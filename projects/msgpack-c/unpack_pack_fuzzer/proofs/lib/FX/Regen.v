(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from FX/Plan.v's check_r walk: the walk that returns the states a plan reaches at its cuts, the rule that rebuilds a recorded template against them, and the rules that carry the main phase's templates (the start state's and the ASan main entry's) to LPS 727298f3. *)
(* Recorded certificate data made again in the build for LPS 727298f3.

   1. [reach]: a plan walked as [Plan.check_r] walks it, returning the state it reaches at each
      [PCut], [PCutDec] and [PEcall] instead of testing it.

   2. [remake]: a recorded template rebuilt against the state a certificate's own run reaches at its
      cut.  Each component the reached state matches under the cut's substitution is kept; where it does
      not, the run's value is taken (a region that does not match takes the run's bound, width and
      background, and the run's granules where the template's do not match).  A template register that
      is a bare template variable (a number at or above 64, the start state's first fresh variable) keeps
      the variable: the cut's substitution binds it to the run's value instead ([rebinds], applied to the
      recorded plan by [rebind_plan] where the plan is checked).  Facts the reached state does not entail
      are dropped; the start state's [STR_END] (below), when the reached state holds it and the template
      does not, is added.

   3. [tx]: the fixed rule for the part after start-up: region 3 (the auxv) := the given region, the start
      fact [FAlign 12 3] replaced by [STR_END] (the first is false at 727298f3: the string area ends at the
      stack's page-aligned top, so its END is 8-aligned and its start is not), and region 1's floor (the
      stack window below sp) raised to the given floor, the start state's.

   4. [txa]: the fixed rule for the ASan main entry's states (below): the heap op's stack window, region 1 and
      the frames and shadow views carved from the released floor moved to the launch's floor, region 3 := the
      given region with its end bound, the string facts.

   SOUNDNESS DOES NOT REST ON ANY OF THIS: every certificate re-runs [check] against the data made here,
   and every computed value is a [Definition] that a lemma re-checks.  A wrong rule can only make a
   certificate fail. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan.

Module Regen.

Inductive hit : Type :=
| HCut (tid : int) (sg : list (int * sv)) (st : sstate)
| HEcall (eid : int) (sg : list (int * sv)) (st : sstate)
| HFail (pc : int)
| HDone.

Section Reach.
Variable segs : list Segment.
Variable rot : Mem.rotab.

Fixpoint reach (C : ctx) (p : plan) (st : sstate) {struct p} : list hit :=
  match p with
  | PFail msg => if PrimInt63.eqb msg DEAD && facts_dead (s_facts st) then [HDone] else [HFail (s_pc st)]
  | PRun stops k =>
      match run_r segs rot (c_itab C) stops st with
      | SStop KStopPc st' | SStop KEcall st' | SStop (KBranch _ _ _ _) st' => reach C k st'
      | SStop _ st' | SOk st' => [HFail (s_pc st')]
      end
  | PCase kT kF =>
      match IMap.find (s_pc st) (c_itab C) with
      | Some (IBranch c rs1 rs2 off) =>
          let a := getr st rs1 in let b := getr st rs2 in
          match take_branch c a b off true st, take_branch c a b off false st with
          | Some stT, Some stF => reach C kT stT ++ reach C kF stF
          | _, _ => [HFail (s_pc st)]
          end
      | _ => [HFail (s_pc st)]
      end
  | PSplit r n ks =>
      let v := getr st r in
      (fix go (ks : list plan) (i : int) : list hit :=
         match ks with
         | [] => []
         | k :: ks' => reach C k (addfact (setr st r (VL (wlit i))) (FEq v (VL (wlit i)))) ++ go ks' (PrimInt63.add i 1%uint63)
         end) ks 0%uint63
  | PSetReg r v k =>
      match decide_eq_t (s_facts st) (getr st r) v with
      | Some true => reach C k (setr st r v)
      | _ => [HFail (s_pc st)]
      end
  | PSubst x u k =>
      let f := vsubst x u in
      reach C k (SS (s_pc st) (rf_map f (s_rf st)) (rf_map f (s_ff st))
                   (match s_resv st with RAddr a => RAddr (f a) | rv => rv end)
                   (IMap.map (region_map f) (s_regs st)) (List.map (fact_map f) (s_facts st))
                   (List.map (op_map f) (s_ops st)) (s_priv st) (s_next st))
  | PName r k =>
      let n := s_next st in
      reach C k (SS (s_pc st) (rf_set (s_rf st) r (VP n wzero)) (s_ff st) (s_resv st) (s_regs st)
                  (FEq (VP n wzero) (getr st r) :: s_facts st) (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63))
  | PSetHi rk v k =>
      match IMap.find rk (s_regs st) with
      | Some r => reach C k (setregs st (IMap.add rk (Region (rg_lo r) v (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)))
      | None => [HFail (s_pc st)]
      end
  | PAssume f k => reach C k (addfact st f)
  | PCall cid ks =>
      match IMap.find cid (c_contracts C) with
      | Some ct =>
          match c_apply ct st with
          | Some sts =>
              (fix go (ks : list plan) (sts : list sstate) : list hit :=
                 match ks, sts with
                 | [], [] => []
                 | k :: ks', st' :: sts' => reach C k st' ++ go ks' sts'
                 | _, _ => [HFail (s_pc st)]
                 end) ks sts
          | None => [HFail (s_pc st)]
          end
      | None => [HFail (s_pc st)]
      end
  | PCut tid sg | PCutDec tid sg => [HCut tid sg st]
  | PEcall eid sg => [HEcall eid sg st]
  | PForget k glo ghi kk =>
      match IMap.find k (s_regs st) with
      | Some r => reach C kk (setregs st (IMap.add k (Mem.region_forget r glo ghi) (s_regs st)))
      | None => [HFail (s_pc st)]
      end
  | PDropFacts keep k =>
      reach C k (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (firstn keep (s_facts st))
                    (s_ops st) (s_priv st) (s_next st))
  end.
End Reach.

(* the first state the run reaches at cut [tid], or at ecall [eid] *)
Fixpoint cut_at (tid : int) (l : list hit) : option (list (int * sv) * sstate) :=
  match l with
  | [] => None
  | HCut t sg st :: l' => if PrimInt63.eqb t tid then Some (sg, st) else cut_at tid l'
  | _ :: l' => cut_at tid l'
  end.
Fixpoint ecall_at (eid : int) (l : list hit) : option (list (int * sv) * sstate) :=
  match l with
  | [] => None
  | HEcall t sg st :: l' => if PrimInt63.eqb t eid then Some (sg, st) else ecall_at eid l'
  | _ :: l' => ecall_at eid l'
  end.

(* ---- rebinding a template variable ---- *)
Definition tvar (v : sv) : option int :=
  match v with VP k o => if weqb o wzero && PrimInt63.leb 64%uint63 k then Some k else None | _ => None end.
Definition rf_rebinds (sg : subst) (T R : rf sv) : list (int * sv) :=
  List.flat_map (fun p => match tvar (fst p) with
                          | Some k => if smatch sg (fst p) (snd p) then [] else [(k, snd p)]
                          | None => [] end) (combine (rf_to_list T) (rf_to_list R)).
Definition sg_upd (d : list (int * sv)) (sg : list (int * sv)) : list (int * sv) :=
  List.map (fun kv => match List.find (fun q => PrimInt63.eqb (fst q) (fst kv)) d with Some q => q | None => kv end) sg.
Fixpoint rebind_plan (t : int) (d : list (int * sv)) (p : plan) : plan :=
  match p with
  | PRun s k => PRun s (rebind_plan t d k)
  | PCase a b => PCase (rebind_plan t d a) (rebind_plan t d b)
  | PSplit r n ks => PSplit r n (List.map (rebind_plan t d) ks)
  | PSetReg r v k => PSetReg r v (rebind_plan t d k)
  | PSubst x u k => PSubst x u (rebind_plan t d k)
  | PName r k => PName r (rebind_plan t d k)
  | PSetHi rk v k => PSetHi rk v (rebind_plan t d k)
  | PAssume f k => PAssume f (rebind_plan t d k)
  | PCall c ks => PCall c (List.map (rebind_plan t d) ks)
  | PCut tid sg => PCut tid (if PrimInt63.eqb tid t then sg_upd d sg else sg)
  | PCutDec tid sg => PCutDec tid (if PrimInt63.eqb tid t then sg_upd d sg else sg)
  | PEcall eid sg => PEcall eid (if PrimInt63.eqb eid t then sg_upd d sg else sg)
  | PForget k glo ghi kk => PForget k glo ghi (rebind_plan t d kk)
  | PDropFacts n k => PDropFacts n (rebind_plan t d k)
  | PFail m => PFail m
  end.

(* the string area (launch variable 12, its length blob 15) ends 8-aligned *)
Definition STR_END : fact :=
  FEq (VAlu ALU_AND (VAlu ALU_ADD (VP 12%uint63 (wp 0%uint63)) (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63)) (VL (wp 7%uint63)))
      (VL (wp 0%uint63)).

(* ---- rebuilding a template against a reached state ---- *)
Definition gran_ok (sg : subst) (tgr : gran) (ogr : option gran) : bool :=
  match ogr with
  | Some gr => if g_dirty tgr then slot_match_sub sg (g_cells tgr) (g_cells gr)
               else negb (g_dirty gr) && slot_match_exact sg (g_cells tgr) (g_cells gr)
  | None => match g_cells tgr with [] => true | _ => false end
  end.
Definition gran_empty (gr : gran) : bool := negb (g_dirty gr) && match g_cells gr with [] => true | _ => false end.
Definition regen_cells (sg : subst) (tc rc : IMap.t gran) : IMap.t gran :=
  let kept := IMap.fold (fun g tgr acc =>
                 if gran_ok sg tgr (IMap.find g rc) then IMap.add g tgr acc
                 else match IMap.find g rc with Some gr => IMap.add g gr acc | None => acc end) tc IMap.empty in
  IMap.fold (fun g gr acc => match IMap.find g tc with
                             | Some _ => acc
                             | None => if gran_empty gr then acc else IMap.add g gr acc
                             end) rc kept.
Definition regen_region (sg : subst) (tr r : region) : region :=
  Region (if kleb (rg_lo r) (rg_lo tr) then rg_lo tr else rg_lo r)
         (if smatch sg (rg_hi tr) (rg_hi r) then rg_hi tr else rg_hi r)
         (rg_w r) (rg_bg r) (regen_cells sg (rg_cells tr) (rg_cells r)).
Definition regen_regs (sg : subst) (TR R : IMap.t region) : IMap.t region :=
  IMap.fold (fun tk tr acc =>
    match svar sg tk with
    | Some k => match IMap.find k R with
                | Some r => IMap.add tk (if region_match sg tk tr k r then tr else regen_region sg tr r) acc
                | None => IMap.add tk tr acc
                end
    | None => IMap.add tk tr acc
    end) TR IMap.empty.
Definition regen_rf (sg : subst) (T R : rf sv) : rf sv :=
  rf_of (VL wzero) (List.map (fun p => if smatch sg (fst p) (snd p) then fst p else snd p) (combine (rf_to_list T) (rf_to_list R))).
Definition regen_st (T st : sstate) (sg : subst) : sstate :=
  SS (s_pc T) (regen_rf sg (s_rf T) (s_rf st)) (regen_rf sg (s_ff T) (s_ff st))
     (if resv_match sg (s_resv T) (s_resv st) then s_resv T else s_resv st)
     (regen_regs sg (s_regs T) (s_regs st))
     (List.filter (fact_entailed (s_facts st) sg) (s_facts T)
      ++ (if has_fact STR_END (s_facts st) && negb (has_fact STR_END (s_facts T)) then [STR_END] else []))
     (if ops_match sg (s_ops T) (s_ops st) then s_ops T else s_ops st)
     (if privs_eqb (s_priv T) (s_priv st) then s_priv T else s_priv st)
     (s_next T).

(* the bindings a cut's substitution changes, and the template rebuilt with them *)
Definition rebinds (T : sstate) (o : option (list (int * sv) * sstate)) : list (int * sv) :=
  match o with Some (sg, st) => rf_rebinds (mk_subst sg) (s_rf T) (s_rf st) | None => [] end.
Definition remake_st (T : sstate) (o : option (list (int * sv) * sstate)) : sstate :=
  match o with Some (sg, st) => regen_st T st (mk_subst (sg_upd (rebinds T o) sg)) | None => T end.
Definition remake (T : template) (o : option (list (int * sv) * sstate)) : template :=
  Tpl (remake_st (t_st T) o) (t_measure T).

Definition with_region (k : int) (r : region) (st : sstate) : sstate :=
  match IMap.find k (s_regs st) with Some _ => setregs st (IMap.add k r (s_regs st)) | None => st end.

(* ---- the part after start-up ---- *)
Definition is_f12 (f : fact) : bool :=
  match f with FAlign k m => PrimInt63.eqb k 12%uint63 && PrimInt63.eqb m 3%uint63 | _ => false end.
Definition fix_f12 (fs : list fact) : list fact := List.map (fun f => if is_f12 f then STR_END else f) fs.
(* the offset key [k] as the w64 [Mem.okey] reads back to [k] *)
Definition wkey (k : int) : w64 := W64 (PrimInt63.leb 4611686018427387904%uint63 k) k.
Definition swap_sv (a b : sv) (v : sv) : sv := if sv_eqb v a then b else v.
(* Region 1 (the stack) starts at the floor [F] where it started below it, and every op argument that named
   the old start as a stack pointer names the new one: the heap op's stack window starts where region 1 does
   ([CtrA.heap_windows]' [stack_window_ok] compares the two). *)
Definition floor1 (F : int) (st : sstate) : sstate :=
  match IMap.find 1%uint63 (s_regs st) with
  | Some r =>
      if kltb (rg_lo r) F then
        SS (s_pc st) (s_rf st) (s_ff st) (s_resv st)
           (IMap.add 1%uint63 (Region F (rg_hi r) (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)) (s_facts st)
           (List.map (op_map (swap_sv (VP 1%uint63 (wkey (rg_lo r))) (VP 1%uint63 (wkey F)))) (s_ops st))
           (s_priv st) (s_next st)
      else st
  | None => st
  end.
Definition tx (R3 : region) (F : int) (st : sstate) : sstate :=
  let st1 := floor1 F (with_region 3%uint63 R3 st) in
  SS (s_pc st1) (s_rf st1) (s_ff st1) (s_resv st1) (s_regs st1) (fix_f12 (s_facts st1)) (s_ops st1) (s_priv st1) (s_next st1).
Definition tx_t (R3 : region) (F : int) (T : template) : template := Tpl (tx R3 F (t_st T)) (t_measure T).
Definition tx_obl (o : obligation) : obligation := (fix_f12 (fst o), snd o).
(* region 1's start in a state: the floor the main phase's templates take from the start state they continue *)
Definition floor_of (st : sstate) : int :=
  match IMap.find 1%uint63 (s_regs st) with Some r => rg_lo r | None => 0%uint63 end.

(* ---- the ASan main entry: the roots of GlueA and the templates of Cert/Asan*, Cert/Both* ---- *)
(* Region 1's start the launch guarantees below sp: -6144513 ([Glue.InitLib.WLO_floor]; the ASan
   start state states the same window, [KWr (SA e_sp0 (-6144513)) (ELit 6144513)]). *)
Definition AFLOOR : int := 9223372036848631295%uint63.
(* An end bound on a launch string the released model gave and LPS 727298f3 does not: the exec name, its
   NUL and an 8-byte slot now sit above the strings, so a string ends at most 9 bytes below 2^47
   ([Glue.InitLib.f_a0_end9] / [f_a1_end9]), not 16. *)
Definition fix_end9 (f : fact) : fact :=
  match f with
  | FULe a (VL w) => if weqb w (wp 140737488355312%uint63) then FULe a (VL (wp 140737488355319%uint63)) else f
  | _ => f
  end.
Definition fix_facts_a (fs : list fact) : list fact := List.map fix_end9 (fix_f12 fs).
(* Region 1 raised to [F] where it started below it. *)
Definition raise1 (F : int) (st : sstate) : sstate :=
  match IMap.find 1%uint63 (s_regs st) with
  | Some r =>
      if kltb (rg_lo r) F then
        SS (s_pc st) (s_rf st) (s_ff st) (s_resv st)
           (IMap.add 1%uint63 (Region F (rg_hi r) (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st))
           (s_facts st) (s_ops st) (s_priv st) (s_next st)
      else st
  | None => st
  end.
(* ---- the fixed rule [txa R3] for the ASan main entry's states ----
   The released templates were recorded with the heap op's K_STACK window, region 1 and the stack frames
   carved from it starting at the released floor [AWLO] (sp0 - 8384512, [Bridge.Op]'s ATOP + 4096).  At
   LPS 727298f3 the launch's floor is [AFLOOR] (sp0 - 6144513, the model's stack bottom), so:
   1. [VP 1 AWLO] (the window's start, and any other value naming it) is [VP 1 AFLOOR] in every value of the
      state, and region 1 starts at AFLOOR where it started below it;
   2. each other region whose start lies in [AWLO, AFLOOR) (a stack frame carved from the old window's
      bottom) starts [FR_D] = AFLOOR - AWLO + 1 higher (a multiple of 16, so the frame keeps its alignment),
      and every [VP k lo] naming its old start names the new one;
   3. each other region whose start lies in [SH_LO, SH_HI) = [AWLO asr 3, (AFLOOR + 7) asr 3) (an ASan shadow
      view of that memory: its start is 1/8 of the address it shadows) starts [SH_D] = FR_D / 8 higher,
      likewise;
   4. region 3 := [R3] (the launch's auxv at one CONFIG_RSEQ value, or the region both values share), the
      auxv's end bound [VP 3 + 160 <= 2^47] (the released 20-word vector) restated at R3's own size, and the
      string facts as [fix_facts_a].
   No window or region the rule writes starts below AFLOOR: the frames start one byte above it and the shadow
   views shadow addresses at or above it.  A run from the raised start carves the same frames: the frame a run
   at 727298f3 carves starts at AWLO + 384 + FR_D, its shadow view at (AWLO + 384) / 8 + SH_D. *)
Definition AWLO : int := 9223372036846391296%uint63.
Fixpoint swap_key (k : int) (a b : w64) (v : sv) : sv :=
  match v with
  | VP k' o => if PrimInt63.eqb k' k && weqb o a then VP k b else v
  | VL _ | VBg _ _ _ _ => v
  | VAlu op x y => VAlu op (swap_key k a b x) (swap_key k a b y)
  | VAluw op x y => VAluw op (swap_key k a b x) (swap_key k a b y)
  | VMd op x y => VMd op (swap_key k a b x) (swap_key k a b y)
  | VMdw op x y => VMdw op (swap_key k a b x) (swap_key k a b y)
  | VExt sx lo n x => VExt sx lo n (swap_key k a b x)
  | VIns lo n x y => VIns lo n (swap_key k a b x) (swap_key k a b y)
  | VBlob sx j off n => VBlob sx j (swap_key k a b off) n
  | VF1 op x => VF1 op (swap_key k a b x)
  end.
(* [VP k a] -> [VP k b] in every value of a state: registers, reservation, regions' bounds and cells, facts, ops *)
Definition swap_st (k : int) (a b : w64) (st : sstate) : sstate :=
  let f := swap_key k a b in
  SS (s_pc st) (rf_map f (s_rf st)) (rf_map f (s_ff st))
     (match s_resv st with RAddr x => RAddr (f x) | rv => rv end)
     (IMap.map (region_map f) (s_regs st)) (List.map (fact_map f) (s_facts st))
     (List.map (op_map f) (s_ops st)) (s_priv st) (s_next st).
(* the regions other than region 1 whose start lies in [lo0, hi0): (key, start) *)
Definition keys_in (lo0 hi0 : int) (R : IMap.t region) : list (int * int) :=
  IMap.fold (fun k r acc => if negb (PrimInt63.eqb k 1%uint63) && kleb lo0 (rg_lo r) && kltb (rg_lo r) hi0
                            then (k, rg_lo r) :: acc else acc) R [].
(* region [k] starting [d] higher (its bound and granules are offsets from its key, unchanged), and every value
   naming its old start naming the new one *)
Definition move1 (d : int) (st : sstate) (kl : int * int) : sstate :=
  let '(k, lo) := kl in
  match IMap.find k (s_regs st) with
  | Some r => swap_st k (wkey lo) (wkey (PrimInt63.add lo d))
                (setregs st (IMap.add k (Region (PrimInt63.add lo d) (rg_hi r) (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)))
  | None => st
  end.
Definition move_in (lo0 hi0 d : int) (st : sstate) : sstate := fold_left (move1 d) (keys_in lo0 hi0 (s_regs st)) st.
Definition FR_D : int := PrimInt63.add (PrimInt63.sub AFLOOR AWLO) 1%uint63.
Definition SH_LO : int := PrimInt63.asr AWLO 3%uint63.
Definition SH_HI : int := PrimInt63.asr (PrimInt63.add AFLOOR 7%uint63) 3%uint63.
Definition SH_D : int := PrimInt63.lsr FR_D 3%uint63.
(* the values the build computes: 2240000, -1048064, -768064, 280000 *)
Lemma rule_consts : (FR_D, SH_LO, SH_HI, SH_D)
  = (2240000%uint63, 9223372036853727744%uint63, 9223372036854007744%uint63, 280000%uint63).
Proof. vm_compute. reflexivity. Qed.
(* the auxv's end bound at region 3's own size ([Glue.InitLib.f_end3] gave it for the released 160 bytes) *)
Definition END3_OLD : fact := FULe (VP 3%uint63 (wp 160%uint63)) (VL (wp 140737488355328%uint63)).
Definition r3_hi (R3 : region) : w64 := match rg_hi R3 with VL h => h | _ => wp 160%uint63 end.
Definition end3_fact (R3 : region) : fact := FULe (VP 3%uint63 (r3_hi R3)) (VL (wp 140737488355328%uint63)).
Definition fix_end3 (R3 : region) (f : fact) : fact := if fact_eqb f END3_OLD then end3_fact R3 else f.
Definition txa (R3 : region) (st : sstate) : sstate :=
  let st1 := raise1 AFLOOR (swap_st 1%uint63 (wkey AWLO) (wkey AFLOOR) st) in
  let st2 := move_in SH_LO SH_HI SH_D (move_in AWLO AFLOOR FR_D st1) in
  let st3 := with_region 3%uint63 R3 st2 in
  SS (s_pc st3) (s_rf st3) (s_ff st3) (s_resv st3) (s_regs st3)
     (List.map (fix_end3 R3) (fix_facts_a (s_facts st3))) (s_ops st3) (s_priv st3) (s_next st3).
Definition txa_t (R3 : region) (T : template) : template := Tpl (txa R3 (t_st T)) (t_measure T).

End Regen.
