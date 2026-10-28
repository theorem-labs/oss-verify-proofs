From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV TobjJVA TobjJVAx TobjJVAy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_load__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LoV.

Definition vop : Type := LD.vop.
Definition is_sp := LD.is_sp.
Definition find_sp_cover := LD.find_sp_cover.
Definition find_sp_lo := LD.find_sp_lo.
Definition sOf := LD.sOf.
Definition R_of := LD.R_of.

Definition bad_state : sstate :=
  mkSS 2989 (ss_regs Pre_lo_U) (ss_fregs Pre_lo_U) FcsrFrm0 None [] [] LD.NP false.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => bad_state end.
Definition canon_bnds : list Z := [- LoU.FR; LoU.lno; LoU.dfo; LoU.cxo; LoU.loco; LoU.savo; 0].

Definition canon_bases : list Z :=
[LoU.bofs; LoU.cxo; LoU.alo;
 LoU.lno].

Definition needs_rebase : SymState.sobj -> bool :=
fun o : SymState.sobj =>
match LD.spoff_of o with
| Some c => negb (existsb (Z.eqb c) canon_bases)
| None => false
end.

Definition is_vechdr : SymState.sobj -> bool :=
fun o : SymState.sobj =>
match LD.spoff_of o with
| Some c => (LoU.bofs <? c) && (c <? LoU.bofs + 1304)
| None => false
end.

Definition merge_plan : list SymState.sobj -> nat -> list nat :=
fix merge_plan (os : list SymState.sobj) (i : nat) {struct os} : list nat :=
  match os with
  | [] => []
  | [o1] => []
  | o1 :: (o2 :: _) as r =>
      let rest := merge_plan r (S i) in
      if
       LD.is_sp o1 && LD.is_sp o2 &&
       SymState.sv_eqb (SymState.ob_hi o1) (SymState.ob_lo o2) &&
       (negb (LD.is_lit (SymState.ob_lo o1)) &&
        LD.is_lit (SymState.ob_hi o2) &&
        (LD.lit_of (SymState.ob_hi o2) <=? - LoU.FR)
        || LD.is_lit (SymState.ob_lo o1) &&
           LD.is_lit (SymState.ob_hi o1) &&
           negb
             (existsb (Z.eqb (LD.lit_of (SymState.ob_hi o1)))
                canon_bnds))
      then rest ++ [i]
      else rest
  end.

Definition cur_split_groups : list SymState.sobj -> list (nat * list Z) :=
fun os : list SymState.sobj =>
match
  LD.find_idx
    (fun ob : SymState.sobj =>
     SymState.sv_eqb (SymState.ob_base ob) LoU.cx &&
     SymState.sv_eqb (SymState.ob_lo ob) (SymState.SLit 0) && SymState.sv_eqb (SymState.ob_hi ob) (SymState.SLit 16))
    os
with
| Some i => [(i, [8])]
| None => []
end ++
match
  LD.find_idx
    (fun ob : SymState.sobj =>
     SymState.sv_eqb (SymState.ob_base ob) LoU.bx &&
     SymState.sv_eqb (SymState.ob_lo ob) (SymState.SLit 320) && SymState.sv_eqb (SymState.ob_hi ob) (SymState.SLit 448))
    os
with
| Some i => [(i, [416; 384; 352])]
| None => []
end ++
match
  LD.find_idx
    (fun ob : SymState.sobj =>
     SymState.sv_eqb (SymState.ob_base ob) LoU.bx &&
     SymState.sv_eqb (SymState.ob_lo ob) (SymState.SLit 936) &&
     SymState.sv_eqb (SymState.ob_hi ob) (SymState.SLit 1256))
    os
with
| Some i => [(i, [1224; 1192; 1160; 1128; 1096; 1064; 1032; 1000; 968])]
| None => []
end.

Definition cur_split : list SymState.sobj -> list ObjXform.xform :=
fun os : list SymState.sobj =>
let gs := cur_split_groups os in
let order :=
  LD.sort_by (fun k : nat => - Z.of_nat (fst (nth k gs (0%nat, [])))) (seq 0 (length gs))
  in
flat_map
  (fun k : nat => let (i, mids) := nth k gs (0%nat, []) in map (fun m : Z => ObjXform.XSplit i (SymState.SLit m)) mids)
  order.

Definition mk_ns : SymState.sstate -> list TobjJVAx.nstep :=
fun S : SymState.sstate =>
let os0 := SymState.ss_objs S in
let xs1 :=
  map ObjXform.XRebase (LD.idxs_where needs_rebase os0 0) in
let nuv :=
  map (fun i : nat => TobjJVAx.NU i LoU.bofs)
    (LD.idxs_where is_vechdr os0 0)
  in
match TobjJVAx.run_nsteps S (TobjJVAx.NX xs1 :: nuv) with
| Some S1 =>
    let os := SymState.ss_objs S1 in
    let n := length os in
    let sps := LD.idxs_where LD.is_sp os 0 in
    let others := filter (fun i : nat => negb (existsb (Nat.eqb i) sps)) (seq 0 n) in
    let perm :=
      LD.sort_by
        (fun i : nat =>
         LD.lit_of (SymState.ob_lo (nth i os LoU.O_D)))
        sps ++
      others in
    match ObjXform.apply_xforms S1 [ObjXform.XSelect perm] with
    | Some S2 =>
        let ms := map ObjXform.XMerge (merge_plan (SymState.ss_objs S2) 0) in
        match ObjXform.apply_xforms S2 ms with
        | Some S3 =>
            (TobjJVAx.NX xs1 :: nuv) ++
            [TobjJVAx.NX
               ([ObjXform.XSelect perm] ++ ms ++ cur_split (SymState.ss_objs S3));
             TobjJVAx.NU 0 (- LoU.FR)]
        | None => [TobjJVAx.NX xs1]
        end
    | None => [TobjJVAx.NX xs1]
    end
| None => [TobjJVAx.NX xs1]
end.

Definition renorm_prog : SymState.sstate -> list TobjJVAx.nstep :=
fun S : SymState.sstate =>
mk_ns (Glue3.with_facts (TobjJVAy.gcS S) LoU.base_facts).

Definition renorm : SymState.sstate -> SymState.sstate :=
fun S : SymState.sstate =>
match TobjJVAy.renormK LoU.base_facts (renorm_prog S) S with
| Some X => X
| None => bad_state
end.

Definition contc : SymState.sstate -> SymState.sstate -> bool :=
fun T A : SymState.sstate =>
TobjJVAy.cont_check LoU.base_facts (renorm_prog T) T A.

Definition T_pure : SymState.sstate -> SymState.sstate -> SymFrame.wsub -> SymState.sstate -> SymState.sstate :=
fun (E Pre : SymState.sstate) (extra : SymFrame.wsub) (L : SymState.sstate) =>
renorm
  (SymCFG.add_facts (SymState.ss_facts E)
     (SymSummary.import_post (LD.sOf E Pre extra) (SymState.ss_next Pre) L
        (SymState.ss_next E) (LD.R_of E Pre extra))).

Definition T_cli : positive -> SymState.sstate -> SymState.sstate -> SymFrame.wsub -> SymState.sstate -> SymState.sstate :=
fun (NPc : positive) (E Pre : SymState.sstate) (extra : SymFrame.wsub) (L : SymState.sstate) =>
renorm
  (TobjJV.T_afterN NPc E (LD.sOf E Pre extra)
     (LD.R_of E Pre extra) L).

Definition vop_ns : SymState.sstate -> LD.vop -> list TobjJVAx.nstep :=
fun (S0 : SymState.sstate) (op : LD.vop) =>
let os := SymState.ss_objs S0 in
match op with
| LD.VCarve lo len =>
    match LD.find_sp_cover os lo (lo + len) with
    | Some i =>
        let o := nth i os LoU.O_D in
        let s1 :=
          if LD.lit_of (SymState.ob_lo o) =? lo
          then []
          else [ObjXform.XSplit i (SymState.SLit lo)] in
        let i' := if LD.lit_of (SymState.ob_lo o) =? lo then i else S i in
        let s2 :=
          if LD.lit_of (SymState.ob_hi o) =? lo + len
          then []
          else [ObjXform.XSplit i' (SymState.SLit (lo + len))] in
        [TobjJVAx.NX (s1 ++ s2); TobjJVAx.NU i' lo]
    | None => []
    end
| LD.VUnb lo c =>
    match LD.find_sp_lo os lo with
    | Some i => [TobjJVAx.NU i c]
    | None => []
    end
| LD.VDeep F =>
    match
      LD.find_idx
        (fun o : SymState.sobj =>
         SymState.sv_eqb (SymState.ob_base o) LoU.sp1 &&
         SymState.sv_eqb (SymState.ob_lo o) LD.vDp)
        os
    with
    | Some i => LD.cvFi i F
    | None => []
    end
| LD.VDeep2 F1 F2 =>
    match
      LD.find_idx
        (fun o : SymState.sobj =>
         SymState.sv_eqb (SymState.ob_base o) LoU.sp1 &&
         SymState.sv_eqb (SymState.ob_lo o) LD.vDp)
        os
    with
    | Some i =>
        [TobjJVAx.NX [ObjXform.XSplit i (SymState.SLit (- F1)); ObjXform.XSplit i (SymState.SLit (- (F1 + F2)))];
         TobjJVAx.NU (S i) (- F1); TobjJVAx.NU i (- (F1 + F2))]
    | None => []
    end
| LD.VMerge lo hi =>
    match LD.find_sp_lo os lo with
    | Some i =>
        let n :=
          length
            (filter
               (fun o : SymState.sobj =>
                LD.is_sp o &&
                match SymState.ob_lo o with
                | SymState.SLit a =>
                    match SymState.ob_hi o with
                    | SymState.SLit b =>
                        (lo <=? LD.lit_of (SymState.SLit a)) &&
                        (LD.lit_of (SymState.SLit b) <=? hi)
                    | _ => false
                    end
                | _ => false
                end)
               os)
          in
        [TobjJVAx.NX (repeat (ObjXform.XMerge i) (n - 1))]
    | None => []
    end
| LD.VMergeB o n =>
    match
      LD.find_idx
        (fun ob : SymState.sobj =>
         SymState.sv_eqb (SymState.ob_base ob) LoU.bx &&
         SymState.sv_eqb (SymState.ob_lo ob) (SymState.SLit o))
        os
    with
    | Some i => [TobjJVAx.NX (repeat (ObjXform.XMerge i) (n - 1))]
    | None => []
    end
| LD.VVec o =>
    match
      LD.find_idx
        (fun ob : SymState.sobj =>
         SymState.sv_eqb (SymState.ob_base ob) LoU.bx &&
         SymState.sv_eqb (SymState.ob_lo ob) (SymState.SLit o))
        os
    with
    | Some i => [TobjJVAx.NX [ObjXform.XRebase i]; TobjJVAx.NU i (LoU.bofs + o)]
    | None => []
    end
| LD.VCurM =>
    match
      LD.find_idx
        (fun ob : SymState.sobj =>
         SymState.sv_eqb (SymState.ob_base ob) LoU.cx &&
         SymState.sv_eqb (SymState.ob_lo ob) (SymState.SLit 0))
        os
    with
    | Some i =>
        match
          LD.find_idx
            (fun ob : SymState.sobj =>
             SymState.sv_eqb (SymState.ob_base ob) LoU.cx &&
             SymState.sv_eqb (SymState.ob_lo ob) (SymState.SLit 8))
            os
        with
        | Some j =>
            [TobjJVAx.NX
               [ObjXform.XSelect
                  (i :: j :: filter (fun k : nat => negb (k =? i)%nat && negb (k =? j)%nat) (seq 0 (length os)));
                ObjXform.XMerge 0]]
        | None => []
        end
    | None => []
    end
end.

Definition view_ns : SymState.sstate -> list LD.vop -> list TobjJVAx.nstep :=
fix view_ns (S : SymState.sstate) (ops : list LD.vop) {struct ops} : list TobjJVAx.nstep :=
  match ops with
  | [] => []
  | op :: r =>
      let ns := vop_ns S op in
      match TobjJVAx.run_nsteps S ns with
      | Some S' => ns ++ view_ns S' r
      | None => ns
      end
  end.

Definition view : list LD.vop -> SymState.sstate -> SymState.sstate :=
fun (ops : list LD.vop) (S : SymState.sstate) =>
optS (TobjJVAx.run_nsteps S (view_ns S ops)).

Definition tvfill : list nat -> list (SymState.sv * SymState.sv) -> list (SymState.sv * SymState.sv) :=
fun (slots : list nat) (imp : list (SymState.sv * SymState.sv)) =>
LD.fill LoU.tvL 0 slots imp.

Definition passedL : list nat -> list (SymState.sv * SymState.sv) :=
fun slots : list nat =>
map
  (fun i : nat =>
   nth i LoU.tvL (LD.z0, LD.z0))
  slots.

Definition keptL : list nat -> list (SymState.sv * SymState.sv) :=
fun slots : list nat => LD.drop_slots LoU.tvL 0 slots.

End LoV.
