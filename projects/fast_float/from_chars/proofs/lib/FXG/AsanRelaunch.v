(* SPDX-License-Identifier: MIT *)
(* The recorded states of the ASan main walk, relaunched on the start-up of LPS 727298f3.

   Every state recorded after the start-up (the phase heads PHT2..PHT10, the loop states PHL2..PHL10, the close
   states CTA/CTB, the leaves BLF*, and the body's states in FXD) was recorded on the start-up of LPS f1006fe8.
   At 727298f3 the start-up has two more launch variables (17 = argv[0]'s address, 18 = the group id) and a new
   stack image (the auxv vector, the strings above the random bytes, the 6144000-byte zero window), so the run
   numbers its variables differently and its launch data differ.  [relaunch] makes each recorded state again by
   one fixed rule, the run record's "relaunch D L (ash f S)": rename every variable by [rl_vmap]; rewrite the old
   argv[0] address to the new one; move the zero window (and each piece of it a later walk cut off its top: same
   base, smaller size, same top end; and each piece a join placed by a 0/1 branch variable, written with sp's terms
   or with a variable an equation fact defines: every byte of it below the new window's bottom moves up with the
   bottom, the rest keeps its address) and replace the auxv region by
   the computed state's; take
   the strings pair of the computed state; drop the launch facts D that the computed state no longer has and add
   the launch facts L it has.  D, L, the regions and the strings pair are computed here from the recorded state
   ([PHT1R], main's PHT1) and the state its producer computes at the revision ([PHT1], K0's chain ended at MEnd,
   the producer's own output, string for string).  [rl_vmap] is read off those two states:
   the recorded 1..16 keep their numbers, 17 is the new 19, 84..583 move by 4, 635.. by 6 (the run's counter at
   PHT1 is 2516 against the recorded 2510), and the pattern variables from 13795 (CTA_NB, NB_G) keep theirs.
   Each certificate that names a relaunched state still checks, by computation, that the run's state implies it,
   so a wrong rule can only fail. *)
From Stdlib Require Import ZArith List Bool PrimString.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxEnt FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Import AsanLit AsanLitCodec AsanLitFast AsanPhT1.
Import ListNotations.
Open Scope Z_scope.

(* the variable map *)
Definition rl_vmap (v : positive) : positive :=
  if Pos.leb v 16 then v
  else if Pos.eqb v 17 then 19%positive
  else if Pos.leb v 583 then (v + 4)%positive
  else if Pos.ltb v 13795 then (v + 6)%positive
  else v.
Definition rl_vmapN (n : positive) : positive := if Pos.leb n 13795 then rl_vmap n else n.

(* the regions the start-up made, recorded (R) and computed (N): 47 the zero window, 49 the argv vector,
   50 the auxv vector *)
Definition rl_dflt : region := RG (lconst 0) (lconst 0) RW TEmpty.
Definition RL_WR : region := nth 47 (s_rgs PHT1R_S) rl_dflt.
Definition RL_WN : region := nth 47 (s_rgs PHT1_S) rl_dflt.
Definition RL_AR : region := nth 50 (s_rgs PHT1R_S) rl_dflt.
Definition RL_AN : region := nth 50 (s_rgs PHT1_S) rl_dflt.
Definition RL_WDELTA : Z := l_c (rg_base RL_WN) - l_c (rg_base RL_WR).
Definition rl_cell0 (R : region) : lin := match tget 1%positive (rg_cont R) with Some (BV l _) => l | _ => lconst 0 end.
Definition RL_ARGV0R : lin := rl_cell0 (nth 49 (s_rgs PHT1R_S) rl_dflt).
Definition RL_ARGV0N : lin := rl_cell0 (nth 49 (s_rgs PHT1_S) rl_dflt).

Definition rl_lin (l : lin) : lin :=
  let l1 := LIN (l_c l) (List.map (fun '(x, k) => (rl_vmap x, k)) (l_t l)) in
  if (terms_eqb (l_t l1) (l_t RL_ARGV0R) && Z.leb (l_c RL_ARGV0R) (l_c l1))%bool
  then laddc RL_ARGV0N (l_c l1 - l_c RL_ARGV0R) else l1.
Definition rl_bval (b : bval) : bval := match b with BK z => BK z | BV l j => BV (rl_lin l) j end.
Definition rl_fact (f : fact) : fact :=
  match f with
  | FCond c a b tk => FCond c (rl_lin a) (rl_lin b) tk
  | FRange l lo hi => FRange (rl_lin l) lo hi
  | FMod l k r => FMod (rl_lin l) k r
  | FBits l m v => FBits (rl_lin l) m v
  | FByte x v j => FByte (rl_lin x) (rl_lin v) j
  | FBytes x bs => FBytes (rl_lin x) (List.map (fun '(l, z) => (rl_lin l, z)) bs)
  end.
Definition rl_rekey (d : Z) (t : tree bval) : tree bval :=
  List.fold_left (fun acc '(p, v) => let q := Zpos p - d in if Z.ltb 0 q then tset (Z.to_pos q) v acc else acc)
    (telems t (fun p => p) []) TEmpty.
Definition rl_isW (b z : lin) : bool := (lin_eqb b (rg_base RL_WR) && lin_eqb z (rg_size RL_WR))%bool.
Definition rl_isA (b z : lin) : bool := (lin_eqb b (rg_base RL_AR) && lin_eqb z (rg_size RL_AR))%bool.
(* a piece of the zero window whose top a later walk cut off (the harness's PMCUT): the recorded window's base and
   a smaller constant size; it moves with the window and keeps its top end, so its size shrinks by the move *)
Definition rl_isWc (b z : lin) : bool :=
  (lin_eqb b (rg_base RL_WR) &&
   match is_const z, is_const (rg_size RL_WR) with Some c, Some w => (Z.ltb RL_WDELTA c && Z.ltb c w)%bool | _, _ => false end)%bool.
Definition rl_wcsize (z : lin) : lin := laddc z (- RL_WDELTA).
(* a piece of the zero window that a join placed by a 0/1 branch variable v (the recorded window's base + o0 + k v,
   constant size c; o0 and o0 + k its offsets from the old window's bottom at v = 0 and v = 1): each end of it
   that lies below the new window's bottom moves up with the bottom (RL_WDELTA), the rest keeps its address.  The
   rule applies when both placements lie in the old window, at least one moves, and both give the same new size
   and the same choice of moving the cells with the bottom; it gives the new base, the new size, and whether the
   cells keep their addresses (the piece shrank) *)
Definition RL_W : Z := match is_const (rg_size RL_WR) with Some w => w | None => 0 end.
Definition rl_sb (o : Z) : Z := if Z.ltb o RL_WDELTA then RL_WDELTA else 0.
Definition rl_se (e : Z) : Z := if Z.leb e RL_WDELTA then RL_WDELTA else 0.
Definition rl_bpiece (b z : lin) : option (lin * lin * bool) :=
  let wb := rg_base RL_WR in
  let n := List.length (l_t wb) in
  match is_const z, List.nth_error (l_t b) n with
  | Some c, Some (v, k) =>
      if (Nat.eqb (List.length (l_t b)) (S n) && terms_eqb (List.firstn n (l_t b)) (l_t wb))%bool then
        let o0 := Z.modulo (l_c b - l_c wb) (2 ^ 64) in
        let o1 := Z.modulo (o0 + k) (2 ^ 64) in
        let s0 := rl_sb o0 in let s1 := rl_sb o1 in
        let e0 := rl_se (o0 + c) in let e1 := rl_se (o1 + c) in
        if (Pos.leb 13795 v && Z.leb (o0 + c) RL_W && Z.leb (o1 + c) RL_W &&
            Z.eqb (e0 - s0) (e1 - s1) && Bool.eqb (Z.eqb s0 e0) (Z.eqb s1 e1) && negb (Z.eqb s0 0 && Z.eqb s1 0))%bool
        then Some (LIN (l_c wb + o0 + s0) (l_t wb ++ [(v, Z.modulo ((o1 + s1) - (o0 + s0)) (2 ^ 64))]), lconst (c - s0 + e0),
                   negb (Z.eqb s0 e0))
        else None
      else None
  | _, _ => None
  end.
(* a variable a recorded state defines by an equation fact [FRange (L - x) 0 0] (a join's stand-in for an
   sp-relative address): a piece whose base is that variable plus a constant is the same piece at base L plus the
   constant; it moves as that one does, and keeps its own form *)
Definition rl_eqs (fs : list fact) : list (positive * lin) :=
  List.flat_map (fun f => match f with
    | FRange l lo hi =>
        if (Z.eqb lo 0 && Z.eqb hi 0)%bool then
          match List.filter (fun '(y, k) => (Pos.leb 13795 y && Z.eqb k (2 ^ 64 - 1))%bool) (l_t l) with
          | [(x, _)] => [(x, LIN (l_c l) (List.filter (fun '(y, _) => negb (Pos.eqb y x)) (l_t l)))]
          | _ => []
          end
        else []
    | _ => []
    end) fs.
Definition rl_bpieceE (eqs : list (positive * lin)) (b z : lin) : option (lin * lin * bool) :=
  match rl_bpiece b z with
  | Some r => Some r
  | None =>
      match l_t b with
      | [(x, k1)] =>
          if Z.eqb k1 1 then
            match List.find (fun '(y, _) => Pos.eqb y x) eqs with
            | Some (_, L) =>
                let b' := laddc L (l_c b) in
                match rl_bpiece b' z with Some (bn, zn, rk) => Some (ladd b (lsub bn b'), zn, rk) | None => None end
            | None => None
            end
          else None
      | _ => None
      end
  end.
(* the window's cells the start-up wrote differently (the group id the start-up code keeps near the launch sp):
   at each such byte, a recorded state that still holds the recorded start-up's value gets the computed one *)
Definition rl_ob_eqb (a b : option bval) : bool :=
  match a, b with Some x, Some y => bval_eqb x y | None, None => true | _, _ => false end.
Definition RL_WCR : tree bval := rl_rekey RL_WDELTA (tmap rl_bval (rg_cont RL_WR)).
Definition RL_WCN : tree bval := rg_cont RL_WN.
Definition rl_keys (t : tree bval) : list positive := List.map fst (telems t (fun p => p) []).
Definition RL_WK : list positive := Eval vm_compute in
  List.filter (fun k => negb (rl_ob_eqb (tget k RL_WCR) (tget k RL_WCN))) (rl_keys RL_WCR ++ rl_keys RL_WCN).
Definition rl_wfix (C : tree bval) : tree bval :=
  List.fold_left (fun acc k =>
    if rl_ob_eqb (tget k acc) (tget k RL_WCR)
    then match tget k RL_WCN with Some v => tset k v acc | None => tfilter (fun p => negb (Pos.eqb p k)) acc end
    else acc) RL_WK C.
Definition rl_region (eqs : list (positive * lin)) (R : region) : region :=
  let b := rl_lin (rg_base R) in let z := rl_lin (rg_size R) in
  if rl_isW b z then RG (rg_base RL_WN) (rg_size RL_WN) (rg_kind R) (rl_wfix (rl_rekey RL_WDELTA (tmap rl_bval (rg_cont R))))
  else if rl_isA b z then RL_AN
  else if rl_isWc b z then RG (rg_base RL_WN) (rl_wcsize z) (rg_kind R) (rl_rekey RL_WDELTA (tmap rl_bval (rg_cont R)))
  else match rl_bpieceE eqs b z with
       | Some (b', z', true) => RG b' z' (rg_kind R) (rl_rekey RL_WDELTA (tmap rl_bval (rg_cont R)))
       | Some (b', z', false) => RG b' z' (rg_kind R) (tmap rl_bval (rg_cont R))
       | None => RG b z (rg_kind R) (tmap rl_bval (rg_cont R))
       end.
Definition rl_pair (eqs : list (positive * lin)) (p : lin * lin) : lin * lin :=
  let b := rl_lin (fst p) in let z := rl_lin (snd p) in
  if rl_isW b z then (rg_base RL_WN, rg_size RL_WN) else if rl_isA b z then (rg_base RL_AN, rg_size RL_AN)
  else if rl_isWc b z then (rg_base RL_WN, rl_wcsize z)
  else match rl_bpieceE eqs b z with Some (b', z', _) => (b', z') | None => (b, z) end.

(* the launch facts: on the launch's own variables only *)
Definition rl_lvars (l : lin) : list positive := List.map fst (l_t l).
Definition rl_fvars (f : fact) : list positive :=
  match f with
  | FCond _ a b _ => rl_lvars a ++ rl_lvars b
  | FRange l _ _ | FMod l _ _ | FBits l _ _ => rl_lvars l
  | FByte x v _ => rl_lvars x ++ rl_lvars v
  | FBytes x bs => rl_lvars x ++ List.concat (List.map (fun p => rl_lvars (fst p)) bs)
  end.
Definition rl_launch (f : fact) : bool := forallb (fun v => Pos.ltb v 19) (rl_fvars f).
Definition rl_in (f : fact) (fs : list fact) : bool := existsb (fact_eqb f) fs.
Definition RL_RFACTS : list fact := List.map rl_fact (s_facts PHT1R_S).
Definition RL_D : list fact := Eval vm_compute in
  List.filter (fun f => (rl_launch f && negb (rl_in f (s_facts PHT1_S)))%bool) RL_RFACTS.
Definition RL_L : list fact := Eval vm_compute in
  List.filter (fun f => (rl_launch f && negb (rl_in f RL_RFACTS))%bool) (s_facts PHT1_S).
Definition rl_facts (fs : list fact) : list fact :=
  let fs1 := List.filter (fun f => negb (rl_in f RL_D)) (List.map rl_fact fs) in
  fs1 ++ List.filter (fun f => negb (rl_in f fs1)) RL_L.

Definition rl_rsv (r : rsv) : rsv := match r with RAt l => RAt (rl_lin l) | _ => r end.
Definition rl_st (eqs : list (positive * lin)) (S : sst) : sst :=
  SST (s_pc S) (tmap rl_lin (s_regs S)) (List.map (rl_region eqs) (s_rgs S)) (rl_facts (s_facts S)) (rl_vmapN (s_next S)) (rl_rsv (s_resv S)).
Definition rl_sm (eqs : list (positive * lin)) (M : smodel) : smodel :=
  SM (List.map (fun '(b, z, k) => (rl_lin b, rl_lin z, k)) (sm_maps M)) (List.map (fun '(l, z) => (rl_lin l, z)) (sm_allow M))
     (sm_zr M) (option_map rl_lin (sm_tid M)) (rl_lin (sm_brk M)) (rl_lin (sm_sbrk M)) (rl_lin (sm_sp M))
     (sm_frz PHT1_M) (List.map (rl_pair eqs) (sm_own M)).
Definition rl_fs (F : fstate) : fstate :=
  match F with
  | FSOpen o l => FSOpen (rl_lin o) (rl_lin l)
  | FSOpenLB o b => FSOpenLB (rl_lin o) (rl_lin b)
  | _ => F
  end.
Definition rl_src (s : src) : src := match s with SArgs pre j lj suf => SArgs pre j (rl_lin lj) suf | _ => s end.
Fixpoint rl_shp (sh : shp) : shp :=
  match sh with
  | ShEmit po kc => ShEmit (List.map (fun p => PD (pd_ch p) (rl_src (pd_src p)) (rl_lin (pd_off p))) po) kc
  | ShAlt2 a b => ShAlt2 (rl_shp a) (rl_shp b)
  | ShIf l lo hi a b => ShIf (rl_lin l) lo hi (rl_shp a) (rl_shp b)
  | ShBit l j a b => ShBit (rl_lin l) j (rl_shp a) (rl_shp b)
  end.
Definition rl_ast (eqs : list (positive * lin)) (a : ast) : ast :=
  AST (a_on a) (List.map (rl_region eqs) (a_rgs a)) (List.map rl_fact (a_fcts a)) (List.map (rl_pair eqs) (a_own a)) (rl_pair eqs (a_dep a))
      (rl_lin (a_nl a)) (List.map (rl_pair eqs) (a_live a)) (List.map rl_lin (a_pri a)).

(* a recorded literal, relaunched *)
Definition relaunch (x : est * smodel * fstate * shp * ast) : est * smodel * fstate * shp * ast :=
  match x with (e, M, F, sh, a) =>
    let S0 := dec_st2 e in let eqs := rl_eqs (rl_facts (s_facts S0)) in
    (enc_st (rl_st eqs S0), rl_sm eqs M, rl_fs F, rl_shp sh, rl_ast eqs a) end.
