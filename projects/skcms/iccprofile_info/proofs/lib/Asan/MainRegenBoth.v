(* SPDX-License-Identifier: MIT *)
(* The main forest's states made again from the computed start-up hand-off state, by this unit's [PlanRegen.collect_hjl] run over each node of a tree; the walk over [mtree] follows [AsanMainTree.mtree_ok], and the per-node collection follows coturn's [Asan/MainCol.v] [mc_loop] over a main tree node; [node_tables_a]/[mtab_a] and the renamed nodes' [node_tables_rn_a]/[mtab_rn_a] collect by [PlanRegen.collect_hjla], each via's arms before its continuation. *)
(* the ASan+UBSan image's copy of MainRegen.v, over that image's tree type and check *)
(* The main forest's recorded states, made again in the build.

   A main tree ([AsanMainTree.mtree]) records, beside its plans, the states its hand-offs and
   joins reach: an [MPre] node's hole table [HT], each [PVia]'s join state and each [PLoop]'s
   invariant.  They are recorded against the start-up hand-off state of an earlier model, whose
   argv/auxv layout facts and accounting bounds the computed one does not have.

   [node_tables C ch p] runs the node's own check of plan [p] at class [C] from state [ch]
   under [collect_hjl] and returns its hand-off, join and loop tables and the last run's result;
   [tb_plan T p] is [p] renumbered by [psh f] with its joins and loop invariants read by
   [pjs f J L] from those tables.  A certificate checks [tb_plan T p] against the hand-off states
   [T] holds, so the tables are definitions, not assumptions: a wrong table only makes a
   certificate red.

   [regen C ch t] rebuilds a tree of leaves, splits and class nodes ([AsanMainTree.mtree_ok]'s
   walk) that way, node by node; an [MPre] node's hole states are the ones its collection
   computes. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO BothAsanPlanImages AsanInit
  AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainHooksBoth AsanMainDefsBoth AsanMainTreeBoth AsanMainCertLibBoth AsanMainItabBoth StartupHSBoth PlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* hand-off, join and loop tables, and the last run's result *)
Definition tables : Type := list (nat * acs) * list (nat * acs) * list (nat * acs) * option cres.
Definition tb_H (T : tables) : list (nat * acs) := fst (fst (fst T)).
Definition tb_J (T : tables) : list (nat * acs) := snd (fst (fst T)).
Definition tb_L (T : tables) : list (nat * acs) := snd (fst T).
Definition tb_last (T : tables) : option cres := snd T.
(* the shape the last run returned, read by a certificate that states its shape *)
Definition tb_shape (T : tables) : shape := match tb_last T with Some (COk s) => s | _ => SNil end.

Section Regen.
  (* the table the checks run under, read by the loop weakening's entailment test *)
  Variable A : atable.
  (* [chk C H cs p]: the tree's check of plan [p] at class [C] from state [cs] (before the class
     facts are added) with hand-off map [H], as [mtree_ok] runs it. *)
  Variable chk : class -> (nat -> option acs) -> acs -> plan -> cres.
  Variable f : nat -> nat.
  Variable fuel : nat.

  (* A node plan that starts by renaming ([PRename m]) is preceded by a forget of the start
     state's facts that name a variable the rename neither moves nor leaves below its targets.
     The recorded start states have no such fact (the rename compacts every variable they use),
     and the computed ones do; left in, it keeps the counter above the renamed variables, and
     the next [PVia] refuses its join bound.  The start state is the node's own, so the indices
     are exact; a forget only weakens. *)
  Definition stray (m : list (nat * nat)) (K : kentry) : bool :=
    let top := fold_left Nat.max (map snd m) 0%nat in
    negb (kvars_all (fun v => orb (existsb (fun q => Nat.eqb (fst q) v) m) (Nat.leb v top)) K).
  Fixpoint stray_ixs (m : list (nat * nat)) (i : nat) (k : list kentry) : list nat :=
    match k with [] => [] | K :: r => if stray m K then i :: stray_ixs m (S i) r else stray_ixs m (S i) r end.
  Definition fix_rename (C : class) (ch : acs) (p : plan) : plan :=
    match p with
    | PRename m k => match stray_ixs m 0 (kn (pay_start ch C)) with [] => p | ixs => PForget ixs p end
    | _ => p
    end.

  Definition node_tables (C : class) (ch : acs) (p : plan) : tables :=
    collect_hjl A fuel (fun H J L => chk C H ch (pjs f J L nodefer (fix_rename C ch (psh f (pdrop_forget p))))) [] [] [] [].
  Definition tb_plan (T : tables) (C : class) (ch : acs) (p : plan) : plan :=
    pjs f (hlookup (tb_J T)) (hlookup (tb_L T)) nodefer (fix_rename C ch (psh f (pdrop_forget p))).
  Definition node_plan (C : class) (ch : acs) (p : plan) : plan := tb_plan (node_tables C ch p) C ch p.
  (* A node whose plan steps onto a recorded numbering takes, in place of that step, the rename
     onto the recorded state [ref] after it that [PlanRegen.rn_step] computes from the state the
     collector reaches at the step: its [PCompact] ([cpt = true]) or its leading [PRename]
     ([cpt = false]).  The rename's own pairs are read off the computed state, so [fix_rename]
     is not applied. *)
  Definition rn_plan (cpt : bool) (ref : acs) (H : nat -> option acs) (p : plan) : plan :=
    if cpt then on_compact (rn_step NX0 ref H) p else on_rename0 (rn_step NX0 ref H) p.
  Definition node_tables_rn (cpt : bool) (ref : acs) (C : class) (ch : acs) (p : plan) : tables :=
    collect_hjl A fuel (fun H J L => chk C H ch (pjs f J L nodefer (rn_plan cpt ref H (psh f (pdrop_forget p))))) [] [] [] [].
  Definition tb_plan_rn (cpt : bool) (ref : acs) (T : tables) (p : plan) : plan :=
    pjs f (hlookup (tb_J T)) (hlookup (tb_L T)) nodefer (rn_plan cpt ref (hlookup (tb_H T)) (psh f (pdrop_forget p))).
  (* [node_tables] by [PlanRegen.collect_hjla]: each via's arms are all merged before its
     continuation is checked from the join; the plan is [tb_plan]'s *)
  Definition node_tables_a (C : class) (ch : acs) (p : plan) : tables :=
    collect_hjla A fuel (fun H J L D => chk C (hk_ext J H) ch (pjs f J L D (fix_rename C ch (psh f (pdrop_forget p))))) [] [] [] [] [].
  (* [node_tables_rn] by [PlanRegen.collect_hjla]; the plan is [tb_plan_rn]'s.  The KWPay nodes
     need it: with each via's join taken from its first arm, via 2's
     continuation in [sec] runs under that arm's side fact of an earlier diamond ([gnew] below the
     fixed region at 2147446784), so its own diamond on the same region has only one side and is
     refused at 340564, and via 1's continuation in [p48]/[p64] runs under a join without the saved
     [s5] word that its epilogue at 334664 loads; with every arm merged first, all three pass. *)
  Definition node_tables_rn_a (cpt : bool) (ref : acs) (C : class) (ch : acs) (p : plan) : tables :=
    collect_hjla A fuel (fun H J L D => chk C (hk_ext J H) ch (pjs f J L D (rn_plan cpt ref H (psh f (pdrop_forget p))))) [] [] [] [] [].

  Fixpoint regen (C : class) (ch : acs) (t : mtree) : mtree :=
    match t with
    | MLeaf L p => MLeaf L (node_plan C ch p)
    | MPre L p HT PT =>
        let T := node_tables C ch p in
        let HT' := map (fun e : nat * (nat * acs) => (fst e, (fst (snd e), hstate (tb_H T) ch (fst e)))) HT in
        MPre L (tb_plan T C ch p) HT'
          ((fix forest (PT : list (nat * mtree)) : list (nat * mtree) :=
              match PT with
              | [] => []
              | (j, t') :: PT' =>
                  (j, match ht_of HT' j with Some s => regen C (snd s) t' | None => t' end) :: forest PT'
              end) PT)
    | MSplit q mid le gt => MSplit q mid (regen (C ++ [(q, QMIN, mid)]) ch le) (regen (C ++ [(q, mid + 1, QMAX)]) ch gt)
    | MCase e mid le gt =>
        let e' := esh f e in
        MCase e' mid (regen C (mcase_lo ch e' mid) le) (regen C (mcase_hi ch e' mid) gt)
    | MClass C' t' => MClass C' (regen C' ch t')
    | MEmpty L => MEmpty L
    end.
End Regen.

(* This image's main check, as [AsanMainTree.mtree_ok] runs it at CONFIG_RSEQ layout [rz], and the
   collector's fuel: one run per hand-off, join and loop update. *)
Definition FUELC : nat := 24.
Definition mchk (rz : Z) (C : class) (H : nat -> option acs) (ch : acs) (p : plan) : cres :=
  APF.check ASEGS ITmD (INFO_BOTH_at rz) NX0 AsanInit.LIMIT (XNm ASEGS (INFO_BOTH_at rz) NX0 RPN.RP_BOTH (iotab_of C))
    (XEm ASEGS (INFO_BOTH_at rz) NX0) (XBm ASEGS (INFO_BOTH_at rz) NX0 (iotab_of C)) H KCm BFUELm FUELm None (pay_start ch C) p.
(* The map a node's plan is renumbered by.  Before the RSEG node's [PCompact] the plans name the
   start-up's variables, which the launch's extra slots moved ([vsh_su]).  [PCompact] renumbers
   every surviving variable densely from the node's base, so after it the variables carry the
   recorded numbers again; the nodes under the RSEG node are renumbered by the identity [vid]. *)
Definition vid (v : nat) : nat := v.
(* The KW chain's first node after [c1_ps_r5bbbbb] starts with an explicit rename onto 31..45,
   which [vsh_su] moves to 35..49, and every later KW variable is counted on from there: after it
   the plans' variables below 622 move by 4 throughout, the rename's own sources (the main phase's
   variables from 622 up) by 5 as [vsh_su] moves them. *)
Definition vkw (v : nat) : nat := if Nat.ltb v 10 then v else if Nat.ltb v 622 then (v + 4)%nat else (v + 5)%nat.
Definition mtab_with (f : nat -> nat) (rz : Z) (C : class) (ch : acs) (p : plan) : tables :=
  node_tables (INFO_BOTH_at rz) (mchk rz) f FUELC C ch p.
Definition mplan_with (f : nat -> nat) (T : tables) (C : class) (ch : acs) (p : plan) : plan := tb_plan f T C ch p.
(* a renamed node's collection runs once more after each table update that drops its hand-offs:
   the step's own state is a hand-off ([HCUT]) *)
Definition mtab_rn (cpt : bool) (ref : acs) (f : nat -> nat) (rz : Z) (C : class) (ch : acs) (p : plan) : tables :=
  node_tables_rn (INFO_BOTH_at rz) (mchk rz) f (FUELC + FUELC) cpt ref C ch p.
Definition mplan_rn (cpt : bool) (ref : acs) (f : nat -> nat) (T : tables) (C : class) (ch : acs) (p : plan) : plan :=
  tb_plan_rn f cpt ref T p.
(* a collection that merges each via's arms first runs once more per arm merged and per via
   settled *)
Definition mtab_a (f : nat -> nat) (rz : Z) (C : class) (ch : acs) (p : plan) : tables :=
  node_tables_a (INFO_BOTH_at rz) (mchk rz) f (FUELC + FUELC + FUELC) C ch p.
(* a renamed node's collection with each via's arms merged first: [mtab_a]'s runs, and once more
   after each table update for the step's own hand-off *)
Definition mtab_rn_a (cpt : bool) (ref : acs) (f : nat -> nat) (rz : Z) (C : class) (ch : acs) (p : plan) : tables :=
  node_tables_rn_a (INFO_BOTH_at rz) (mchk rz) f (FUELC + FUELC + FUELC + FUELC) cpt ref C ch p.
Definition mregen (rz : Z) (C : class) (ch : acs) (t : mtree) : mtree := regen (INFO_BOTH_at rz) (mchk rz) vsh_su FUELC C ch t.
