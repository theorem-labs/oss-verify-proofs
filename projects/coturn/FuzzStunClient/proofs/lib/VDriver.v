(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStep VStepMem VCert VItab VDriverMatch VContract.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record genv := mkGE {
  ge_P0 : vparams ;            (* [comment removed for export] *)
  ge_itab : itab ;
  ge_ctab : pmap contract ;    (* [comment removed for export] *)
  ge_CI : cimg ;
  ge_tp : Z ;                  (* [comment removed for export] *)
  ge_prng : Z ;                (* [comment removed for export] *)
  ge_ranks : bool              (* [comment removed for export] *)
}.

Record denv := mkDE {
  de_G : genv ;
  de_P : vparams ;
  de_done : list vunit ;
  de_U : vunit ;
  de_cuts : pmap (list vcut)   (* [comment removed for export] *)
}.

Definition zkey (z : Z) : positive := Z.to_pos z.

(* [comment removed for export] *)
Definition unit_wcells (G : genv) (U : vunit) : list (Z * Z) :=
  ((if u_errno U then [(ci_errno (ge_CI G), 4)] else []) ++ u_wglobs U)%list.

Definition unit_params (G : genv) (U : vunit) : vparams :=
  let P0 := ge_P0 G in
  mkVP (vp_frame P0) ((- vp_frame P0, u_sp U) :: u_wstack U) (unit_wcells G U) (vp_fcells P0)
       (vp_segs P0) (vp_pristine P0) (vp_rom P0) (vp_nmax P0) (vp_splo P0) (vp_sphi P0).

Fixpoint cuts_by_pc (l : list vcut) (m : pmap (list vcut)) : pmap (list vcut) :=
  match l with
  | [] => m
  | c :: t => let k := zkey (cut_pc c) in
              let old := match pm_get k m with Some l' => l' | None => [] end in
              cuts_by_pc t (pm_set k (old ++ [c])%list m)
  end.

Definition mk_denv (G : genv) (done : list vunit) (U : vunit) : denv :=
  mkDE G (unit_params G U) done U (cuts_by_pc (u_cuts U) pm_empty).

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sres : Type := SN (succs : list vstate) | SF (msg : string).

Inductive res : Type :=
| ROk
| RFail (unit_vid : Z) (origin : string) (A : vstate) (msg : string).

Fixpoint list_Z_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && list_Z_eqb a' b'
  | _, _ => false
  end.

Definition find_cut (D : denv) (pc : Z) (ctx : list Z) : option vcut :=
  if negb (Z.ltb 0 pc) then None else
  match pm_get (zkey pc) (de_cuts D) with
  | None => None
  | Some l => find (fun c => Z.eqb (cut_pc c) pc && list_Z_eqb (cut_ctx c) ctx) l
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition absval_eqb (v : absval) (e : lin) : bool :=
  match v with Some e' => lin_eqb e' e | None => false end.

(* [comment removed for export] *)
Definition sp_offset (A : vstate) : option Z :=
  match get_reg A 2 with
  | Some e => match lt e with
              | [(s, k)] => if Pos.eqb s SP0 && Z.eqb k 1 then Some (lc e) else None
              | _ => None
              end
  | None => None
  end.

Definition sreg_idx : list (Z * Z) :=      (* [comment removed for export] *)
  [(8,0); (9,1); (18,2); (19,3); (20,4); (21,5); (22,6); (23,7); (24,8); (25,9); (26,10); (27,11)].

Definition is_sreg_key (r : positive) : bool :=
  existsb (fun p : Z * Z => Pos.eqb r (zkey (fst p))) sreg_idx.

Definition sregs_intact (A : vstate) : bool :=
  forallb (fun p : Z * Z => absval_eqb (get_reg A (fst p)) (lsym (SREG (snd p)))) sreg_idx.

(* [comment removed for export] *)
Definition ra_is_exit (U : vunit) (v : absval) : bool :=
  match u_root U with
  | Some c => absval_eqb v (lconst c)
  | None => absval_eqb v (lsym RA)
  end.

Fixpoint str_concat (l : list string) : string :=
  match l with [] => "" | [x] => x | x :: t => x ++ " | " ++ str_concat t end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint try_exits (l : list cstate) (A : vstate) (k : nat) (msgs : list string) : option (list string) :=
  match l with
  | [] => Some msgs
  | X :: t =>
      match match_state isv_join no_skip false pm_empty (load_cstate X (vs_pc A) []) A with
      | MOk _ => None
      | MFail m => try_exits t A (Datatypes.S k) (m :: msgs)
      end
  end.

Definition unit_exit (D : denv) (A : vstate) : sres :=
  let U := de_U D in let G := de_G D in
  if negb (absval_eqb (get_reg A 2) (lsymc SP0 (u_sp U))) then SF "exit: sp is not SP0 + sp_off" else
  if negb (sregs_intact A) then SF "exit: some s-register is not its entry symbol" else
  if negb (absval_eqb (get_reg A 3) (lsym GP)) then SF "exit: gp modified" else
  if negb (absval_eqb (get_reg A 4) (lconst (ge_tp G))) then SF "exit: tp modified" else
  if negb (match u_root U with
           | Some _ => match get_reg A 10 with Some e => lin_is_const e && Z.eqb (zm64 (lc e)) 0 | None => false end
           | None => true end) then SF "exit: root unit does not return a0 = 0" else
  match try_exits (u_exits U) A 0 [] with
  | None => SN []
  | Some msgs => SF ("exit: no stored exit state matches: " ++ str_concat msgs)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pop_ctx (P : vparams) (A : vstate) (i : instr) : sres :=
  match vs_ctx A with
  | [] => SF "ret: constant ra with empty inline context"
  | c :: rest =>
      match vstep P A i with
      | VR_next [A'] => if Z.eqb (vs_pc A') c then SN [set_ctx A' rest]
                        else SF "ret: target does not match the innermost inline context"
      | VR_next _ => SF "ret: unexpected successor count"
      | VR_fail m => SF m
      end
  end.

Definition do_ret (D : denv) (A : vstate) (i : instr) : sres :=
  let v := get_reg A 1 in
  if ra_is_exit (de_U D) v then
    match vs_ctx A with
    | [] => unit_exit D A
    | _ => SF "ret to the unit's caller with a non-empty inline context"
    end
  else
    match v with
    | Some e => if lin_is_const e then pop_ctx (de_P D) A i
                else SF "ret: ra is neither the caller's RA nor a constant"
    | None => SF "ret: ra is Top"
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition after_return (D : denv) (A : vstate) (tail : bool) (npc : Z) : sres :=
  if negb tail then SN [set_pc A npc]
  else
    (* [comment removed for export] *)
    let v := get_reg A 1 in
    if ra_is_exit (de_U D) v then
      match vs_ctx A with
      | [] => unit_exit D A
      | _ => SF "tail call returning to the unit's caller with non-empty inline context"
      end
    else match v with
         | Some e => if lin_is_const e then
                       let c := lc e in
                       if negb (Z.eqb (c mod 2) 0 && Z.leb 0 c && Z.ltb c (2 ^ 64)) then SF "tail call: constant ra not an even address" else
                       match vs_ctx A with
                       | c' :: rest => if Z.eqb c' c then SN [set_ctx (set_pc A c) rest]
                                      else SF "tail call: ra does not match the inline context"
                       | [] => SF "tail call: constant ra with empty inline context"
                       end
                     else SF "tail call: ra neither RA nor constant"
         | None => SF "tail call: ra Top"
         end.

Definition do_contract (D : denv) (A : vstate) (c : contract) (rd : Z) (npc : Z) : sres :=
  if negb (Z.eqb rd 0 || Z.eqb rd 1) then SF "contract call: jal with rd not in {x0, ra}" else
  let tail := Z.eqb rd 0 in
  (* [comment removed for export] *)
  let A' := if tail then A else set_reg A 1 (Some (lconst npc)) in
  match sp_offset A' with
  | None => SF "contract call: sp is not SP0 + constant"
  | Some spoff =>
      let K := contract_K c in
      if negb (Z.eqb K 0) && negb (in_ranges (vp_wstack (de_P D)) (spoff - K) K) then SF "contract call: callee frame [sp-K,sp) not inside the unit's stack write set" else
      let ra0 := get_reg A' 1 in
      match contract_apply (de_P D) (ge_CI (de_G D)) c A' spoff with
      | CRDead => SN []
      | CRFail m => SF m
      | CROk A1 v =>
          let A2 := contract_frame c A1 spoff v in
          (* [comment removed for export] *)
          let A3 := set_reg A2 1 ra0 in
          after_return D A3 tail npc
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition osubst (sigma : pmap lin) (e : lin) : option lin :=
  if forallb (fun t : sym * Z => negb (isv_call (fst t)) || pm_mem (fst t) sigma) (lt e)
  then Some (lsubst sigma e) else None.

Definition osubst_v (sigma : pmap lin) (v : absval) : absval :=
  match v with Some e => osubst sigma e | None => None end.

Fixpoint sigma_sregs (A : vstate) (l : list (Z * Z)) (sigma : pmap lin) : pmap lin :=
  match l with
  | [] => sigma
  | (r, i) :: t => sigma_sregs A t (match get_reg A r with
                                    | Some e => pm_set (SREG i) e sigma
                                    | None => sigma
                                    end)
  end.

(* [comment removed for export] *)
Fixpoint sigma_joins (j : positive) (b : positive) (n : nat) (sigma : pmap lin) : pmap lin :=
  match n with
  | O => sigma
  | S n' => sigma_joins (Pos.succ j) (Pos.succ b) n' (pm_set j (lsym b) sigma)
  end.

Definition n_joins (X : cstate) : nat := Pos.to_nat (cs_next X) - Pos.to_nat JOIN0.

Fixpoint kill_ranges (m : cellmap) (l : list (Z * Z)) : cellmap :=
  match l with [] => m | (lo, hi) :: t => kill_ranges (cm_kill m lo hi) t end.

Fixpoint kill_cells (m : cellmap) (l : list (Z * Z)) : cellmap :=
  match l with [] => m | (a, n) :: t => kill_cells (cm_kill m a (a + n)) t end.

Definition nul_survives (spoff : Z) (wst : list (Z * Z)) (f : Z * Z) : bool :=
  Z.leb spoff (fst f) && negb (existsb (fun r : Z * Z => Z.ltb (fst f) (snd r) && Z.leb (fst r) (snd f)) wst).

Definition STACK_BOTTOM : Z := - 2 ^ 64.

(* [comment removed for export] *)
Fixpoint regs_tops (m : pmap lin) (l : list Z) : pmap lin :=
  match l with
  | [] => m
  | r :: t => regs_tops (if Z.eqb r 0 then m else pm_remove (reg_key r) m) t
  end.

Definition reg_upd (m : pmap lin) (r : Z) (v : absval) : pmap lin :=
  match v with Some e => pm_set (reg_key r) e m | None => pm_remove (reg_key r) m end.

(* [comment removed for export] *)
Definition call_base (D : denv) (A : vstate) (V : vunit) (spoff npc : Z) : vstate :=
  let sl := kill_ranges (cm_kill (vs_slots A) STACK_BOTTOM spoff) (u_wstack V) in
  let gl0 := kill_cells (vs_globs A) (u_wglobs V) in
  let gl := if u_errno V then cm_kill gl0 (ci_errno (ge_CI (de_G D))) (ci_errno (ge_CI (de_G D)) + 4) else gl0 in
  let nl := List.filter (nul_survives spoff (u_wstack V)) (vs_nul A) in
  mkVS npc (pm_set (reg_key 1) (lconst npc) (regs_tops (vs_regs A) CALLER_SAVED))
       sl gl (vs_store A) (vs_next A) (vs_conddef A) (vs_moddef A) (vs_valset A) nl (vs_ctx A) (vs_ghosts A).

(* [comment removed for export] *)
Fixpoint add_boxes (S : store) (sigma : pmap lin) (l : list (sym * itv)) : option store :=
  match l with
  | [] => Some S
  | (s, i) :: t =>
      if isv_join s then
        match pm_get s sigma with
        | Some e => match lin_single e with
                    | Some (s', _) => add_boxes (store_set_box S s' i) sigma t
                    | None => add_boxes S sigma t
                    end
        | None => None   (* [comment removed for export] *)
        end
      else
        match osubst sigma (lsym s) with
        | Some e => match add_in_itv S e i with
                    | Some S' => add_boxes S' sigma t
                    | None => None
                    end
        | None => add_boxes S sigma t      (* [comment removed for export] *)
        end
  end.

Fixpoint add_congs (S : store) (sigma : pmap lin) (l : list (sym * (Z * Z))) : option store :=
  match l with
  | [] => Some S
  | (s, (m, r)) :: t =>
      if isv_join s then
        match pm_get s sigma with
        | Some e => match lin_single e with
                    | Some (s', _) => match store_add_cong S s' m r with
                                      | Some S' => add_congs S' sigma t
                                      | None => None
                                      end
                    | None => add_congs S sigma t
                    end
        | None => None
        end
      else add_congs S sigma t
  end.

Fixpoint add_conss (S : store) (sigma : pmap lin) (l : list lin) : option store :=
  match l with
  | [] => Some S
  | c :: t =>
      match osubst sigma c with
      | Some c' => if lin_is_const c' then (if Z.leb (lc c') 0 then add_conss S sigma t else None)
                   else match add_constraint S c' with
                        | Some S' => add_conss S' sigma t
                        | None => None
                        end
      | None => add_conss S sigma t
      end
  end.

Fixpoint set_exit_slots (sl : cellmap) (sigma : pmap lin) (spoff : Z) (l : cellmap) : cellmap :=
  match l with
  | [] => sl
  | (off, (w, v)) :: t =>
      if Z.leb spoff off then
        let sl1 := cm_kill sl off (off + w) in
        set_exit_slots (match osubst_v sigma v with
                        | Some e' => cm_set sl1 off (w, Some e')
                        | None => sl1
                        end) sigma spoff t
      else set_exit_slots sl sigma spoff t
  end.

Fixpoint set_exit_globs (gl : cellmap) (sigma : pmap lin) (l : cellmap) : cellmap :=
  match l with
  | [] => gl
  | (a, (w, v)) :: t => set_exit_globs (cm_set (cm_kill gl a (a + w)) a (w, osubst_v sigma v)) sigma t
  end.

Fixpoint set_exit_valsets (vs : pmap (list Z)) (sigma : pmap lin) (l : list (sym * list Z)) : pmap (list Z) :=
  match l with
  | [] => vs
  | (s, zs) :: t =>
      set_exit_valsets (match sym_image sigma s with
                        | Some s' => if pm_mem s sigma then pm_set s' zs vs else vs
                        | None => vs
                        end) sigma t
  end.

Definition add_exit_nuls (nl : list (Z * Z)) (spoff : Z) (l : list (Z * Z)) : list (Z * Z) :=
  fold_left (fun acc f => if Z.leb spoff (fst f) then (if nul_implied acc f then acc else f :: acc) else acc) l nl.

(* [comment removed for export] *)
Definition apply_exit (B : vstate) (sigma0 : pmap lin) (spoff : Z) (SX : vstate) : option vstate :=
  let nj := (Pos.to_nat (vs_next SX) - Pos.to_nat JOIN0)%nat in
  let b := vs_next B in
  let sigma := sigma_joins JOIN0 b nj sigma0 in
  match add_boxes (vs_store B) sigma (pm_elements (sbox (vs_store SX))) with
  | None => None
  | Some S1 =>
  match add_congs S1 sigma (pm_elements (scong (vs_store SX))) with
  | None => None
  | Some S2 =>
  match add_conss S2 sigma (scons (vs_store SX)) with
  | None => None
  | Some S3 =>
      Some (mkVS (vs_pc B)
                 (reg_upd (reg_upd (vs_regs B) 10 (osubst_v sigma (get_reg SX 10))) 11 (osubst_v sigma (get_reg SX 11)))
                 (set_exit_slots (vs_slots B) sigma spoff (vs_slots SX))
                 (set_exit_globs (vs_globs B) sigma (vs_globs SX))
                 S3
                 (Pos.of_nat (Pos.to_nat b + nj))
                 (vs_conddef B) (vs_moddef B)
                 (set_exit_valsets (vs_valset B) sigma (pm_elements (vs_valset SX)))
                 (add_exit_nuls (vs_nul B) spoff (vs_nul SX))
                 (vs_ctx B) (vs_ghosts B))
  end end end.

Fixpoint apply_exits (B : vstate) (sigma : pmap lin) (spoff npc : Z) (l : list cstate) : list vstate :=
  match l with
  | [] => []
  | X :: t => match apply_exit B sigma spoff (load_cstate X npc []) with
              | Some B' => B' :: apply_exits B sigma spoff npc t
              | None => apply_exits B sigma spoff npc t
              end
  end.

(* [comment removed for export] *)
Definition footprint_ok (D : denv) (V : vunit) (spoff : Z) : bool :=
  let U := de_U D in let P := de_P D in
  Z.leb spoff (u_sp U)
  && Z.eqb (u_sp V) spoff
  && forallb (fun r : Z * Z => in_ranges (vp_wstack P) (fst r) (snd r - fst r)) (u_wstack V)
  && forallb (fun c : Z * Z => in_cells (vp_wcells P) (fst c) (snd c)) (u_wglobs V)
  && (negb (u_errno V) || u_errno U).

(* [comment removed for export] *)
Definition materialize1 (A : vstate) (r : Z) : vstate :=
  match get_reg A r with
  | Some _ => A
  | None => let '(v, A') := afresh A itv_top in set_reg A' r v
  end.

Fixpoint materialize (A : vstate) (l : list (Z * Z)) : vstate :=
  match l with
  | [] => A
  | (r, _) :: t => materialize (materialize1 A r) t
  end.

Definition try_variant (D : denv) (A : vstate) (V : vunit) (spoff npc : Z) : sres :=
  if negb (footprint_ok D V spoff) then SF "call: callee footprint / sp not admissible in this unit" else
  match u_root V with Some _ => SF "call: callee is a root unit" | None =>
  let A0 := set_reg (materialize A sreg_idx) 1 (Some (lconst npc)) in
  let sigma0 := sigma_sregs A0 sreg_idx (pm_set RA (lconst npc) pm_empty) in
  let S := load_cstate (u_pre V) (u_entry V) [] in
  match match_state isv_call is_sreg_key true sigma0 S A0 with
  | MFail m => SF ("call: PRE not matched: " ++ m)
  | MOk sigma =>
      if negb (pm_forallb (fun _ e => lin_below e (vs_next A0)) sigma) then SF "call: internal: sigma range not below the symbol bound" else
      let B := call_base D A0 V spoff npc in
      let succs := apply_exits B sigma spoff npc (u_exits V) in
      if forallb vstate_below_b succs then SN succs else SF "call: internal: symbol hygiene of an instantiated exit"
  end end.

Fixpoint try_variants (D : denv) (A : vstate) (l : list vunit) (spoff npc : Z) (msgs : list string) : sres :=
  match l with
  | [] => SF ("call: no variant applies: " ++ str_concat msgs)
  | V :: t => match try_variant D A V spoff npc with
              | SN succs => SN succs
              | SF m => try_variants D A t spoff npc (m :: msgs)
              end
  end.

(* [comment removed for export] *)
Fixpoint insert_prio (V : vunit) (l : list vunit) : list vunit :=
  match l with
  | [] => [V]
  | W :: t => if Z.ltb (u_prio V) (u_prio W) then V :: l else W :: insert_prio V t
  end.

Fixpoint hinted_variants (calls : list vcall) (pc : Z) (all : list vunit) : list vunit :=
  match calls with
  | [] => []
  | c :: t => if Z.eqb (call_pc c) pc
              then (List.filter (fun V => Z.eqb (u_vid V) (call_vid c)) all ++ hinted_variants t pc all)%list
              else hinted_variants t pc all
  end.

Definition call_variants (D : denv) (pc tgt : Z) : list vunit :=
  let all := fold_right insert_prio [] (List.filter (fun V => Z.eqb (u_entry V) tgt) (de_done D)) in
  (hinted_variants (u_calls (de_U D)) pc all ++ all)%list.

Definition do_call (D : denv) (A : vstate) (tgt npc : Z) (variants : list vunit) : sres :=
  match sp_offset A with
  | None => SF "call: sp is not SP0 + constant"
  | Some spoff => try_variants D A variants spoff npc []
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lift (r : vresult) : sres :=
  match r with VR_next l => SN l | VR_fail m => SF m end.

Definition dstep (D : denv) (A : vstate) : sres :=
  let G := de_G D in
  match itab_get (ge_itab G) (vs_pc A) with
  | None => SF "no decoded instruction at pc"
  | Some i =>
      match i with
      | Jal rd imm =>
          let tgt := wrap64 (vs_pc A + bv_signed imm) in
          let npc := npc_of A in
          match (if Z.ltb 0 tgt then pm_get (zkey tgt) (ge_ctab G) else None) with
          | Some c => do_contract D A c (rz rd) npc
          | None =>
              if Z.eqb (rz rd) 1 then
                match call_variants D (vs_pc A) tgt with
                | [] => (* [comment removed for export] *)
                    match vstep (de_P D) A i with
                    | VR_next [A'] => SN [set_ctx A' (npc :: vs_ctx A')]
                    | VR_next _ => SF "jal: unexpected successor count"
                    | VR_fail m => SF m
                    end
                | vs => do_call D A tgt npc vs
                end
              else if Z.eqb (rz rd) 0 then lift (vstep (de_P D) A i)
              else SF "jal with rd not in {x0, ra}"
          end
      | Jalr rd rs1 imm =>
          if Z.eqb (rz rd) 0 && Z.eqb (rz rs1) 1 && Z.eqb (bv_signed imm) 0 then do_ret D A i
          else lift (vstep (de_P D) A i)
      | _ => lift (vstep (de_P D) A i)
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint try_disjuncts (D : denv) (Rstart : lin) (A : vstate) (c : vcut) (sts : list cstate) (rks : list lin)
         (msgs : list string) : option (list string) :=
  match sts with
  | [] => Some msgs
  | X :: t =>
      let rk := match rks with r :: _ => Some r | [] => None end in
      let rks' := match rks with _ :: r' => r' | [] => [] end in
      let S := load_cstate X (cut_pc c) (cut_ctx c) in
      match match_state isv_join no_skip false pm_empty S A with
      | MOk sigma =>
          if ge_ranks (de_G D) then
            match rk with
            | None => try_disjuncts D Rstart A c t rks' ("cut: disjunct matched but has no rank" :: msgs)
            | Some r =>
                if qge A (lsub Rstart (lsubst sigma r)) 1 then None
                else try_disjuncts D Rstart A c t rks' ("cut: rank does not decrease" :: msgs)
            end
          else None
      | MFail m => try_disjuncts D Rstart A c t rks' (m :: msgs)
      end
  end.

Definition cut_arrival (D : denv) (Rstart : lin) (A : vstate) (c : vcut) : sres :=
  match try_disjuncts D Rstart A c (cut_states c) (cut_ranks c) [] with
  | None => SN []
  | Some msgs => SF ("cut: not included in any disjunct: " ++ str_concat msgs)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint explore (D : denv) (fuel : nat) (origin : string) (Rstart : lin) (work : list (bool * vstate)) : res :=
  match fuel with
  | O => match work with
         | (_, A) :: _ => RFail (u_vid (de_U D)) origin A "out of fuel"
         | [] => ROk
         end
  | S f =>
      match work with
      | [] => ROk
      | (first, A) :: rest =>
          let atcut := if first then None else find_cut D (vs_pc A) (vs_ctx A) in
          match atcut with
          | Some c =>
              match cut_arrival D Rstart A c with
              | SN _ => explore D f origin Rstart rest
              | SF m => RFail (u_vid (de_U D)) origin A m
              end
          | None =>
              match dstep D A with
              | SN succs => explore D f origin Rstart (map (fun A' => (false, A')) succs ++ rest)%list
              | SF m => RFail (u_vid (de_U D)) origin A m
              end
          end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cells_in_window (P : vparams) (l : list (Z * (Z * lin))) : bool :=
  forallb (fun c : Z * (Z * lin) => match c with (off, (w, _)) =>
             Z.leb (- vp_frame P) off && Z.ltb 0 w && Z.leb (off + w) 0 end) l.

Definition globs_in_range (P : vparams) (l : list (Z * (Z * lin))) : bool :=
  forallb (fun c : Z * (Z * lin) => match c with (a, (w, _)) =>
             Z.leb 0 a && Z.ltb 0 w && Z.leb (a + w) (vp_splo P - vp_frame P) end) l.

Definition nuls_in_window (P : vparams) (l : list (Z * Z)) : bool :=
  forallb (fun f : Z * Z => Z.leb (- vp_frame P) (fst f) && Z.leb (fst f) (snd f) && Z.ltb (snd f) 0) l.

Definition cstate_ok (P : vparams) (cs : cstate) : bool :=
  cstate_wf_f cs (* [comment removed for export] *)
  && cells_in_window P (cs_slots cs) && globs_in_range P (cs_globs cs) && nuls_in_window P (cs_nul cs).

(* [comment removed for export] *)
Definition pre_canonical (G : genv) (U : vunit) : bool :=
  let S := load_cstate (u_pre U) (u_entry U) [] in
  ra_is_exit U (get_reg S 1)
  && absval_eqb (get_reg S 2) (lsymc SP0 (u_sp U))
  && sregs_intact S
  && absval_eqb (get_reg S 3) (lsym GP)
  && absval_eqb (get_reg S 4) (lconst (ge_tp G)).

Definition rank_nonneg (c : vcut) : bool :=
  forallb (fun xr : cstate * lin =>
             let S := load_cstate (fst xr) (cut_pc c) (cut_ctx c) in
             qge S (snd xr) 0 && lin_below (snd xr) (cs_next (fst xr)))
          (combine (cut_states c) (cut_ranks c)).

Definition pc_ok (pc : Z) : bool := Z.ltb 0 pc && Z.ltb pc (2 ^ 64).

Definition unit_static_ok (G : genv) (P : vparams) (U : vunit) : option string :=
  if negb (cstate_ok P (u_pre U)) then Some "static: entry state ill-formed" else
  if negb (pre_canonical G U) then Some "static: entry state registers not canonical (ra/sp/s-regs/gp/tp)" else
  if negb (forallb (fun c => pc_ok (cut_pc c) && forallb (cstate_ok P) (cut_states c)) (u_cuts U)) then Some "static: a cut state is ill-formed" else
  if negb (pc_ok (u_entry U)) then Some "static: entry pc out of range" else
  if negb (forallb (cstate_ok P) (u_exits U)) then Some "static: an exit state is ill-formed" else
  if ge_ranks G && negb (forallb (fun c => Nat.eqb (length (cut_ranks c)) (length (cut_states c)) && rank_nonneg c) (u_cuts U))
  then Some "static: missing or possibly negative rank" else
  if negb (forallb (fun r : Z * Z => Z.leb (- vp_frame P) (fst r) && Z.leb (snd r) 0 && Z.leb (u_sp U) (fst r)) (u_wstack U))
  then Some "static: caller-visible write range outside [sp_off, 0)" else
  if negb (forallb (fun c : Z * Z => in_cells (vp_fcells P) (fst c) (snd c)) (vp_wcells P))
  then Some "static: unit writable cells not inside the F-level cells" else
  if Z.ltb 0 (u_sp U) || Z.ltb (u_sp U) (- vp_frame P) then Some "static: sp_off outside the window" else
  None.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RANK_TOP : lin := lconst (2 ^ 200).   (* [comment removed for export] *)

Fixpoint check_cut_states (D : denv) (fuel : nat) (c : vcut) (sts : list cstate) (rks : list lin) (k : nat) : res :=
  match sts with
  | [] => ROk
  | X :: t =>
      let R := match rks with r :: _ => r | [] => RANK_TOP end in
      let rks' := match rks with _ :: r' => r' | [] => [] end in
      let St := load_cstate X (cut_pc c) (cut_ctx c) in
      match explore D fuel "cut" R [(true, St)] with
      | ROk => check_cut_states D fuel c t rks' (Datatypes.S k)
      | r => r
      end
  end.

Fixpoint check_cuts (D : denv) (fuel : nat) (l : list vcut) : res :=
  match l with
  | [] => ROk
  | c :: t => match check_cut_states D fuel c (cut_states c) (cut_ranks c) 0 with
              | ROk => check_cuts D fuel t
              | r => r
              end
  end.

Definition check_unit (G : genv) (done : list vunit) (U : vunit) : res :=
  let D := mk_denv G done U in
  let S0 := load_cstate (u_pre U) (u_entry U) [] in
  match unit_static_ok G (de_P D) U with
  | Some m => RFail (u_vid U) "static" S0 m
  | None =>
      let fuel := N.to_nat (u_fuel U) in
      match explore D fuel "entry" RANK_TOP [(true, S0)] with
      | ROk => check_cuts D fuel (u_cuts U)
      | r => r
      end
  end.

Fixpoint check_units (G : genv) (done : list vunit) (l : list vunit) : res :=
  match l with
  | [] => ROk
  | U :: t => match check_unit G done U with
              | ROk => check_units G (done ++ [U])%list t
              | r => r
              end
  end.

Definition check_cert (G : genv) (C : vcert) : res := check_units G [] C.

(* [comment removed for export] *)
Fixpoint check_report (G : genv) (done : list vunit) (l : list vunit) : list res :=
  match l with
  | [] => []
  | U :: t => check_unit G done U :: check_report G (done ++ [U])%list t
  end.
