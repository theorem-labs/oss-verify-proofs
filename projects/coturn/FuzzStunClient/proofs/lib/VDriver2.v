(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStep VStepMem VCert VItab VDriverMatch VContract VDriver.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VState2 VStepMem2 VCert2 VContract2 VDriverMatch2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record genv2 := mkGE2 {
  ge2_P0 : vparams2 ;          (* [comment removed for export] *)
  ge2_itab : itab ;
  ge2_ctab : pmap contract2 ;  (* [comment removed for export] *)
  ge2_CI : cimg ;
  ge2_tp : Z ;
  ge2_prng : Z ;
  ge2_ranks : bool
}.

Definition genv2_of_v1 (G : genv) : genv2 :=
  mkGE2 (of_p1_tp (ge_P0 G) (ge_tp G)) (ge_itab G) (pm_map CV1 (ge_ctab G)) (ge_CI G) (ge_tp G) (ge_prng G) (ge_ranks G).

Record denv2 := mkDE2 {
  de2_G : genv2 ;
  de2_P : vparams2 ;
  de2_done : list vunit2 ;
  de2_U : vunit2 ;
  de2_cuts : pmap (list vcut2) ;
  de2_vidx : pmap (list vunit2)
}.

Definition unit_wcells2 (G : genv2) (U : vunit2) : list (Z * Z) :=
  ((if u_errno (u1 U) then [(ci_errno (ge2_CI G), 4)] else []) ++ u_wglobs (u1 U))%list.

Definition unit_params2 (G : genv2) (U : vunit2) : vparams2 :=
  let P0 := ge2_P0 G in let Q := p1 P0 in let V := u1 U in
  mkVP2 (mkVP (vp_frame Q) ((- vp_frame Q, u_sp V) :: u_wstack V) (unit_wcells2 G U) (vp_fcells Q)
              (vp_segs Q) (vp_pristine Q) (vp_rom Q) (vp_nmax Q) (vp_splo Q) (vp_sphi Q))
        (vp_shoff P0) (vp_kcells P0) (vp_kruns P0) (vp_fzones P0) (vp_fs P0) (vp_datal P0) (u2_wrgn U) (u2_fdepth U) (vp_tp P0)
        (vp_imgend P0).

Fixpoint cuts_by_pc2 (l : list vcut2) (m : pmap (list vcut2)) : pmap (list vcut2) :=
  match l with
  | [] => m
  | c :: t => let k := zkey (cut2_pc c) in
              let old := match pm_get k m with Some l' => l' | None => [] end in
              cuts_by_pc2 t (pm_set k (old ++ [c])%list m)
  end.

Definition idx_add (V : vunit2) (m : pmap (list vunit2)) : pmap (list vunit2) :=
  let k := zkey (u_entry (u1 V)) in
  pm_set k (V :: match pm_get k m with Some l => l | None => [] end) m.

Definition done_index (done : list vunit2) : pmap (list vunit2) := fold_right idx_add pm_empty done.

Definition mk_denv2 (G : genv2) (done : list vunit2) (U : vunit2) : denv2 :=
  mkDE2 G (unit_params2 G U) done U (cuts_by_pc2 (u2_cuts U) pm_empty) (done_index done).

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sres2 : Type := SN2 (succs : list vstate2) | SF2 (msg : string).

Inductive res2 : Type :=
| R2Ok
| R2Fail (unit_vid : Z) (origin : string) (A : vstate2) (msg : string).

Definition find_cut2 (D : denv2) (pc : Z) (ctx : list Z) : option vcut2 :=
  if negb (Z.ltb 0 pc) then None else
  match pm_get (zkey pc) (de2_cuts D) with
  | None => None
  | Some l => find (fun c => Z.eqb (cut2_pc c) pc && list_Z_eqb (cut2_ctx c) ctx) l
  end.

Definition set_ctx2 (A : vstate2) (c : list Z) : vstate2 := with_v1 A (set_ctx (v1 A) c).

(* [comment removed for export] *)
Definition ra_is_exit2 (U : vunit2) (v : absval) : bool := ra_is_exit (u1 U) v.

(* [comment removed for export] *)
Definition no_local_regions (A : vstate2) : bool :=
  match vs_live A with [] => true | _ => false end
  && forallb (fun r => match vr_kind r with RK_fake _ _ | RK_flag _ => false | _ => true end) (vs_rgn A).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint try_exits2 (P : vparams2) (l : list cstate2) (A : vstate2) (msgs : list string) : option (list string) :=
  match l with
  | [] => Some msgs
  | X :: t =>
      match match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 P X (vs2_pc A) []) A with
      | MOk _ => None
      | MFail m => try_exits2 P t A (m :: msgs)
      end
  end.

Definition unit_exit2 (D : denv2) (A : vstate2) : sres2 :=
  let U := de2_U D in let G := de2_G D in let A1 := v1 A in let V := u1 U in
  if negb (absval_eqb (get_reg A1 2) (lsymc SP0 (u_sp V))) then SF2 "exit: sp is not SP0 + sp_off" else
  if negb (sregs_intact A1) then SF2 "exit: some s-register is not its entry symbol" else
  if negb (absval_eqb (get_reg A1 3) (lsym GP)) then SF2 "exit: gp modified" else
  if negb (absval_eqb (get_reg A1 4) (lconst (ge2_tp G))) then SF2 "exit: tp modified" else
  if negb (match u_root V with
           | Some _ => match get_reg A1 10 with Some e => lin_is_const e && Z.eqb (zm64 (lc e)) 0 | None => false end
           | None => true end) then SF2 "exit: root unit does not return a0 = 0" else
  if negb (no_local_regions A) then SF2 "exit: live fake frames at unit exit" else
  match try_exits2 (de2_P D) (u2_exits U) A [] with
  | None => SN2 []
  | Some msgs => SF2 ("exit: no stored exit state matches: " ++ str_concat msgs)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pop_ctx2 (P : vparams2) (A : vstate2) (i : instr) : sres2 :=
  match vs_ctx (v1 A) with
  | [] => SF2 "ret: constant ra with empty inline context"
  | c :: rest =>
      match vstep2 P A i with
      | VR2_next [A'] => if Z.eqb (vs2_pc A') c then SN2 [set_ctx2 A' rest]
                         else SF2 "ret: target does not match the innermost inline context"
      | VR2_next _ => SF2 "ret: unexpected successor count"
      | VR2_fail m => SF2 m
      end
  end.

Definition do_ret2 (D : denv2) (A : vstate2) (i : instr) : sres2 :=
  let v := get_reg (v1 A) 1 in
  if ra_is_exit2 (de2_U D) v then
    match vs_ctx (v1 A) with
    | [] => unit_exit2 D A
    | _ => SF2 "ret to the unit's caller with a non-empty inline context"
    end
  else
    match v with
    | Some e => if lin_is_const e then pop_ctx2 (de2_P D) A i
                else SF2 "ret: ra is neither the caller's RA nor a constant"
    | None => SF2 "ret: ra is Top"
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition after_return2 (D : denv2) (A : vstate2) (tail : bool) (npc : Z) : sres2 :=
  if negb tail then SN2 [set_pc2 A npc]
  else
    let v := get_reg (v1 A) 1 in
    if ra_is_exit2 (de2_U D) v then
      match vs_ctx (v1 A) with
      | [] => unit_exit2 D A
      | _ => SF2 "tail call returning to the unit's caller with non-empty inline context"
      end
    else match v with
         | Some e => if lin_is_const e then
                       let c := lc e in
                       if negb (Z.eqb (c mod 2) 0 && Z.leb 0 c && Z.ltb c (2 ^ 64)) then SF2 "tail call: constant ra not an even address" else
                       match vs_ctx (v1 A) with
                       | c' :: rest => if Z.eqb c' c then SN2 [set_ctx2 (set_pc2 A c) rest]
                                      else SF2 "tail call: ra does not match the inline context"
                       | [] => SF2 "tail call: constant ra with empty inline context"
                       end
                     else SF2 "tail call: ra neither RA nor constant"
         | None => SF2 "tail call: ra Top"
         end.

(* [comment removed for export] *)
Fixpoint collect_sn2 (l : list sres2) : sres2 :=
  match l with
  | [] => SN2 []
  | SF2 m :: _ => SF2 m
  | SN2 s :: t => match collect_sn2 t with SN2 s' => SN2 (s ++ s')%list | SF2 m => SF2 m end
  end.

Definition do_contract2 (D : denv2) (A : vstate2) (c : contract2) (rd : Z) (npc : Z) : sres2 :=
  if negb (Z.eqb rd 0 || Z.eqb rd 1) then SF2 "contract call: jal with rd not in {x0, ra}" else
  let tail := Z.eqb rd 0 in
  let A' := clear_memo (if tail then A else set_reg2 A 1 (Some (lconst npc))) in
  match sp_offset (v1 A') with
  | None => SF2 "contract call: sp is not SP0 + constant"
  | Some spoff =>
      let K := contract2_K c in
      if negb (Z.eqb K 0) && negb (in_ranges (vp_wstack (p1 (de2_P D))) (spoff - K) K) then SF2 "contract call: callee frame [sp-K,sp) not inside the unit's stack write set" else
      let ra0 := get_reg (v1 A') 1 in
      match contract_apply2 (de2_P D) (ge2_CI (de2_G D)) c A' spoff with
      | CR2Dead => SN2 []
      | CR2Fail m => SF2 m
      | CR2OkN [] => SF2 "contract: no outcome"
      | CR2OkN l =>
          collect_sn2 (map (fun av : vstate2 * absval =>
                              let A2 := contract_frame2 c (fst av) spoff (snd av) in
                              let A3 := set_reg2 A2 1 ra0 in
                              after_return2 D A3 tail npc) l)
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition osubst2 (sigma : pmap lin) (e : lin) : option lin :=
  if forallb (fun t : sym * Z => negb (isv_call2 (fst t)) || pm_mem (fst t) sigma) (lt e)
  then Some (lsubst sigma e) else None.

Definition osubst2_v (sigma : pmap lin) (v : absval) : absval :=
  match v with Some e => osubst2 sigma e | None => None end.

Definition n_joins2 (X : cstate2) : nat := Pos.to_nat (cs_next (c1 X)) - Pos.to_nat FIRST_FRESH2.

Fixpoint add_boxes2 (S : store) (sigma : pmap lin) (l : list (sym * itv)) : option store :=
  match l with
  | [] => Some S
  | (s, i) :: t =>
      if isv_join2 s then
        match pm_get s sigma with
        | Some e => match lin_single e with
                    | Some (s', _) => add_boxes2 (store_set_box S s' i) sigma t
                    | None => add_boxes2 S sigma t
                    end
        | None => None
        end
      else
        match osubst2 sigma (lsym s) with
        | Some e => match add_in_itv S e i with
                    | Some S' => add_boxes2 S' sigma t
                    | None => None
                    end
        | None => add_boxes2 S sigma t
        end
  end.

Fixpoint add_congs2 (S : store) (sigma : pmap lin) (l : list (sym * (Z * Z))) : option store :=
  match l with
  | [] => Some S
  | (s, (m, r)) :: t =>
      if isv_join2 s then
        match pm_get s sigma with
        | Some e => match lin_single e with
                    | Some (s', _) => match store_add_cong S s' m r with
                                      | Some S' => add_congs2 S' sigma t
                                      | None => None
                                      end
                    | None => add_congs2 S sigma t
                    end
        | None => None
        end
      else add_congs2 S sigma t
  end.

Fixpoint add_conss2 (S : store) (sigma : pmap lin) (l : list lin) : option store :=
  match l with
  | [] => Some S
  | c :: t =>
      match osubst2 sigma c with
      | Some c' => if lin_is_const c' then (if Z.leb (lc c') 0 then add_conss2 S sigma t else None)
                   else match add_constraint S c' with
                        | Some S' => add_conss2 S' sigma t
                        | None => None
                        end
      | None => add_conss2 S sigma t
      end
  end.

Fixpoint cm_skip (rp s : cellmap) (o : Z) : cellmap * cellmap :=
  match s with
  | [] => (rp, [])
  | (k, (w, v)) :: t => if Z.leb (k + w) o then cm_skip ((k, (w, v)) :: rp) t o else (rp, s)
  end.

Fixpoint cm_kill_s (m : cellmap) (lo hi : Z) : cellmap :=
  match m with
  | [] => []
  | (k, (w, v)) :: t =>
      if Z.leb hi k then m
      else if Z.ltb lo (k + w) then cm_kill_s t lo hi else (k, (w, v)) :: cm_kill_s t lo hi
  end.

Fixpoint set_exit_slots2_t (rp s : cellmap) (sigma : pmap lin) (spoff : Z) (l : cellmap) : cellmap :=
  match l with
  | [] => rev_append rp s
  | (off, (w, v)) :: t =>
      if Z.leb spoff off then
        let '(rp1, s1) := cm_skip rp s off in
        let s2 := cm_kill_s s1 off (off + w) in
        set_exit_slots2_t rp1 (match osubst2_v sigma v with
                               | Some e' => cm_set s2 off (w, Some e')
                               | None => s2
                               end) sigma spoff t
      else set_exit_slots2_t rp s sigma spoff t
  end.

Definition set_exit_slots2 (sl : cellmap) (sigma : pmap lin) (spoff : Z) (l : cellmap) : cellmap :=
  set_exit_slots2_t [] sl sigma spoff l.

Fixpoint set_exit_globs2 (gl : cellmap) (sigma : pmap lin) (l : cellmap) : cellmap :=
  match l with
  | [] => gl
  | (a, (w, v)) :: t => set_exit_globs2 (cm_set (cm_kill gl a (a + w)) a (w, osubst2_v sigma v)) sigma t
  end.

(* [comment removed for export] *)
Fixpoint set_exit_rcells (cl : cellmap) (sigma : pmap lin) (c : Z) (l : cellmap) : cellmap :=
  match l with
  | [] => cl
  | (off, (w, v)) :: t =>
      let cl1 := cm_kill cl (off + c) (off + c + w) in
      set_exit_rcells (match osubst2_v sigma v with
                       | Some e' => cm_set cl1 (off + c) (w, Some e')
                       | None => cl1
                       end) sigma c t
  end.

(* [comment removed for export] *)
Fixpoint sh_cut_s (m : cellmap) (lo hi : Z) : cellmap :=
  match m with
  | [] => []
  | (k, (w, v)) :: t =>
      if Z.leb hi k then m
      else if Z.ltb lo (k + w) then
        let keep_l := if Z.ltb k lo then match v with Some e => if lin_is_const e then [(k, (lo - k, v))] else [] | None => [] end else [] in
        let keep_r := if Z.ltb hi (k + w) then match v with Some e => if lin_is_const e then [(hi, (k + w - hi, v))] else [] | None => [] end else [] in
        (keep_l ++ keep_r ++ sh_cut_s t lo hi)%list
      else (k, (w, v)) :: sh_cut_s t lo hi
  end.

Fixpoint set_exit_shcells_t (rp s : cellmap) (l : cellmap) : cellmap :=
  match l with
  | [] => rev_append rp s
  | (off, (w, v)) :: t =>
      let '(rp1, s1) := cm_skip rp s off in
      let s2 := sh_cut_s s1 off (off + w) in
      set_exit_shcells_t rp1 (match v with
                              | Some e => if lin_is_const e then cm_set s2 off (w, Some e) else s2
                              | None => s2
                              end) t
  end.

Definition set_exit_shcells (cl : cellmap) (l : cellmap) : cellmap := set_exit_shcells_t [] cl l.

(* [comment removed for export] *)
Fixpoint set_exit_divdefs (dd : pmap (lin * Z)) (sigma : pmap lin) (l : list (sym * (lin * Z))) : pmap (lin * Z) :=
  match l with
  | [] => dd
  | (q, (x, m)) :: t =>
      set_exit_divdefs (if isv_join2 q then
                          match sym_image sigma q, osubst2 sigma x with
                          | Some q', Some x' => pm_set q' (x', m) dd
                          | _, _ => dd
                          end
                        else dd) sigma t
  end.

(* [comment removed for export] *)
Definition rgn_kill (r : vregion) (lo hi : Z) : vregion :=
  mkVR (vr_base r) (vr_disp r) (vr_kind r) (vr_lo r) (vr_hi r) (vr_w r)
       (cm_kill (vr_cells r) lo hi)
       (List.filter (fun f : Z * Z => Z.ltb (snd f) lo || Z.leb hi (fst f)) (vr_nul r))
       (vr_b8 r).

Fixpoint rgn_kill_ranges (r : vregion) (l : list (Z * Z)) : vregion :=
  match l with [] => r | (lo, hi) :: t => rgn_kill_ranges (rgn_kill r lo hi) t end.

(* [comment removed for export] *)
Definition rgn_cut (r : vregion) (lo hi : Z) : vregion :=
  mkVR (vr_base r) (vr_disp r) (vr_kind r) (vr_lo r) (vr_hi r) (vr_w r)
       (sh_cut (vr_cells r) lo hi)
       (List.filter (fun f : Z * Z => Z.ltb (snd f) lo || Z.leb hi (fst f)) (vr_nul r))
       (vr_b8 r).

(* [comment removed for export] *)
Definition wb_fits (xr pr : vregion) (c : Z) : bool :=
  Z.eqb (vr_disp xr) (vr_disp pr) && Z.leb (vr_lo pr) (vr_lo xr + c) && Z.leb (vr_hi xr + c) (vr_hi pr)
  && Bool.eqb (is_shadow xr) (is_shadow pr) && match vr_kind pr with RK_shadow s => negb (Pos.eqb s DATA) | _ => true end
  && forallb (fun k : Z * cell => Z.leb (vr_lo xr) (fst k) && Z.ltb 0 (fst (snd k)) && Z.leb (fst k + fst (snd k)) (vr_hi xr)) (vr_cells xr).

(* [comment removed for export] *)
Fixpoint write_back_args (A : vstate2) (rg : list vregion) (sigma : pmap lin) (l : list vregion) : option (list vregion) :=
  match l with
  | [] => Some rg
  | xr :: t =>
      match vr_kind xr with
      | RK_arg =>
          match resolve_base isv_call2 A sigma (vr_base xr) with
          | Some (b', c) =>
              match rgn_get rg b' with
              | Some pr =>
                  match vr_kind pr with
                  | RK_fake _ _ | RK_arg =>
                      if wb_fits xr pr c
                      then write_back_args A (rgn_upd rg (set_cells pr (set_exit_rcells (vr_cells pr) sigma c (vr_cells xr)))) sigma t
                      else None
                  | _ => None
                  end
              | None => None
              end
          | None => None
          end
      | RK_shadow s =>
          if Pos.eqb s SP0 then
            (* [comment removed for export] *)
            match rgn_shadow_of rg SP0 with
            | Some pr => if wb_fits xr pr 0
                         then write_back_args A (rgn_upd rg (set_cells pr (set_exit_shcells (vr_cells pr) (vr_cells xr)))) sigma t
                         else None
            | None => write_back_args A rg sigma t
            end
          else write_back_args A rg sigma t   (* [comment removed for export] *)
      | RK_fs => write_back_args A rg sigma t
      | _ => None                                            (* [comment removed for export] *)
      end
  end.

(* [comment removed for export] *)
Fixpoint kill_wrgn (A : vstate2) (sigma : pmap lin) (rg : list vregion) (l : list (Z * (Z * Z))) : option (list vregion) :=
  match l with
  | [] => Some rg
  | (i, (lo, hi)) :: t =>
      match resolve_base isv_call2 A sigma (ASYM2 i) with
      | Some (b', c) =>
          match rgn_get rg b' with
          | Some pr =>
              (* [comment removed for export] *)
              let rg1 := match vr_kind pr with RK_arg => havoc_other_args rg b' | _ => rg end in
              kill_wrgn A sigma (rgn_upd rg1 (rgn_kill pr (lo + c) (hi + c))) t
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition kill_fs_cells (rg : list vregion) : list vregion :=
  map (fun r => match vr_kind r with RK_fs => set_rnul (set_cells r []) [] | _ => r end) rg.

(* [comment removed for export] *)
Definition kill_shadow_sp (fr : Z) (V1u : vunit) (spoff : Z) (rg : list vregion) : list vregion :=
  map (fun r => match vr_kind r with
                | RK_shadow s => if Pos.eqb s SP0 then rgn_cut r ((- fr) / 8) ((spoff + 7) / 8) else r
                | _ => r end) rg.

(* [comment removed for export] *)
Definition call_base2v (CI : cimg) (A1 : vstate) (V1u : vunit) (spoff npc : Z) : vstate :=
  let sl := kill_ranges (cm_kill (vs_slots A1) STACK_BOTTOM spoff) (u_wstack V1u) in
  let gl0 := kill_cells (vs_globs A1) (u_wglobs V1u) in
  let gl := if u_errno V1u then cm_kill gl0 (ci_errno CI) (ci_errno CI + 4) else gl0 in
  let nl := List.filter (nul_survives spoff (u_wstack V1u)) (vs_nul A1) in
  mkVS npc (pm_set (reg_key 1) (lconst npc) (regs_tops (vs_regs A1) CALLER_SAVED))
       sl gl (vs_store A1) (vs_next A1) (vs_conddef A1) (vs_moddef A1) (vs_valset A1) nl (vs_ctx A1) (vs_ghosts A1).

Definition call_base2 (D : denv2) (A : vstate2) (V : vunit2) (sigma : pmap lin) (spoff npc : Z) : option vstate2 :=
  match kill_wrgn A sigma (kill_shadow_sp (vp_frame (p1 (de2_P D))) (u1 V) spoff (kill_fs_cells (vs_rgn A))) (u2_wrgn V) with
  | Some rg => Some (mkVS2 (call_base2v (ge2_CI (de2_G D)) (v1 A) (u1 V) spoff npc) rg (vs_live A) (vs_divdef A) [])
  | None => None
  end.

(* [comment removed for export] *)
Definition apply_exit2v (B1 : vstate) (sigma0 : pmap lin) (spoff : Z) (X1 : vstate) : option (vstate * pmap lin) :=
  let nj := (Pos.to_nat (vs_next X1) - Pos.to_nat FIRST_FRESH2)%nat in
  let b := vs_next B1 in
  let sigma := sigma_joins FIRST_FRESH2 b nj sigma0 in
  match add_boxes2 (vs_store B1) sigma (pm_elements (sbox (vs_store X1))) with
  | None => None
  | Some S1 =>
  match add_congs2 S1 sigma (pm_elements (scong (vs_store X1))) with
  | None => None
  | Some S2 =>
  match add_conss2 S2 sigma (scons (vs_store X1)) with
  | None => None
  | Some S3 =>
      Some (mkVS (vs_pc B1)
                 (reg_upd (reg_upd (vs_regs B1) 10 (osubst2_v sigma (get_reg X1 10))) 11 (osubst2_v sigma (get_reg X1 11)))
                 (set_exit_slots2 (vs_slots B1) sigma spoff (vs_slots X1))
                 (set_exit_globs2 (vs_globs B1) sigma (vs_globs X1))
                 S3
                 (Pos.of_nat (Pos.to_nat b + nj))
                 (vs_conddef B1) (vs_moddef B1)
                 (set_exit_valsets (vs_valset B1) sigma (pm_elements (vs_valset X1)))
                 (add_exit_nuls (vs_nul B1) spoff (vs_nul X1))
                 (vs_ctx B1) (vs_ghosts B1), sigma)
  end end end.

(* [comment removed for export] *)
Definition apply_exit2w (B : vstate2) (B1' : vstate) (sigma : pmap lin) (SX : vstate2) : option vstate2 :=
  match write_back_args B (vs_rgn B) sigma (vs_rgn SX) with
  | None => None
  | Some rg => Some (mkVS2 B1' rg (vs_live B) (set_exit_divdefs (vs_divdef B) sigma (pm_elements (vs_divdef SX))) [])
  end.

Definition apply_exit2 (B : vstate2) (sigma0 : pmap lin) (spoff : Z) (SX : vstate2) : option vstate2 :=
  match apply_exit2v (v1 B) sigma0 spoff (v1 SX) with
  | None => None
  | Some (B1', sigma) => apply_exit2w B B1' sigma SX
  end.

(* [comment removed for export] *)
Fixpoint apply_exits2 (P : vparams2) (B : vstate2) (sigma : pmap lin) (spoff npc : Z) (l : list cstate2) : option (list vstate2) :=
  match l with
  | [] => Some []
  | X :: t =>
      let SX := load_cstate2 P X npc [] in
      match apply_exit2v (v1 B) sigma spoff (v1 SX) with
      | None => apply_exits2 P B sigma spoff npc t
      | Some (B1', sigma') =>
          match apply_exit2w B B1' sigma' SX, apply_exits2 P B sigma spoff npc t with
          | Some B', Some r => Some (B' :: r)
          | _, _ => None
          end
      end
  end.

(* [comment removed for export] *)
Definition wrgn_admissible (D : denv2) (A : vstate2) (sigma : pmap lin) (w : Z * (Z * Z)) : bool :=
  match w with (i, (lo, hi)) =>
  match resolve_base isv_call2 A sigma (ASYM2 i) with
  | Some (b', c) =>
      match rgn_get (vs_rgn A) b' with
      | Some pr => Z.eqb (vr_disp pr) 0 &&
                   match vr_kind pr with
                   | RK_fake _ _ => in_ranges (vr_w pr) (lo + c) (hi - lo)
                   | RK_arg => in_ranges (vr_w pr) (lo + c) (hi - lo)     (* [comment removed for export] *)
                   | _ => false
                   end
      | None => false
      end
  | None => false
  end end.

Definition footprint_ok2 (D : denv2) (A : vstate2) (sigma : pmap lin) (V : vunit2) (spoff : Z) : bool :=
  let U := u1 (de2_U D) in let P := p1 (de2_P D) in let W := u1 V in
  Z.leb spoff (u_sp U)
  && Z.eqb (u_sp W) spoff
  && forallb (fun r : Z * Z => in_ranges (vp_wstack P) (fst r) (snd r - fst r)) (u_wstack W)
  && forallb (fun c : Z * Z => in_cells (vp_wcells P) (fst c) (snd c)) (u_wglobs W)
  && (negb (u_errno W) || u_errno U)
  && forallb (wrgn_admissible D A sigma) (u2_wrgn V).

Definition materialize2 (A : vstate2) : vstate2 := with_v1 A (materialize (v1 A) sreg_idx).

(* [comment removed for export] *)
Definition drop_divdefs (l : list sym) (S : vstate2) : vstate2 :=
  mkVS2 (v1 S) (vs_rgn S) (vs_live S) (fold_right (fun q m => pm_remove q m) (vs_divdef S) l) (vs_memo S).

(* [comment removed for export] *)
Fixpoint prebind_args (A0 : vstate2) (pre_rgn : list srgn) (pre_dd : list (sym * (lin * Z))) (sigma : pmap lin)
  : option (pmap lin * list sym) :=
  match pre_rgn with
  | [] => Some (sigma, [])
  | sr :: t =>
      match sr_kind sr with
      | SK_arg =>
          let b := sr_base sr in
          let i := Z.pos b - 19 in
          if negb (Z.leb 0 i && Z.ltb i 8) then None else
          match get_reg (v1 A0) (10 + i) with
          | None => None
          | Some e =>
              let sigma1 := match pm_get b sigma with Some _ => sigma | None => pm_set b e sigma end in
              (* [comment removed for export] *)
              let b8 := ASYM8 i in
              let need8 := existsb (fun d : sym * (lin * Z) => Pos.eqb (fst d) b8) pre_dd in
              let ok8 := forallb (fun d : sym * (lin * Z) => negb (Pos.eqb (fst d) b8)
                                                             || (lin_eqb (fst (snd d)) (lsym b) && Z.eqb (snd (snd d)) 8)) pre_dd in
              if negb need8 then
                match prebind_args A0 t pre_dd sigma1 with Some (s, sk) => Some (s, sk) | None => None end
              else if negb ok8 then None else
                match pm_get b8 sigma1 with
                | Some _ => None                                   (* [comment removed for export] *)
                | None =>
                match resolve_base isv_call2 A0 sigma1 b with
                | Some (bc, c) =>
                    match comp A0 bc, base_res8 A0 bc with
                    | Some bc8, Some rc =>
                        let e8 := laddc (lsym bc8) ((c + rc) / 8) in
                        match prebind_args A0 t pre_dd (pm_set b8 e8 sigma1) with
                        | Some (s, sk) => Some (s, b8 :: sk)
                        | None => None
                        end
                    | _, _ => None
                    end
                | None => None
                end end
          end
      | _ => prebind_args A0 t pre_dd sigma
      end
  end.

Definition try_variant2 (D : denv2) (A : vstate2) (V : vunit2) (spoff npc : Z) : sres2 :=
  let P := de2_P D in
  match u_root (u1 V) with Some _ => SF2 "call: callee is a root unit" | None =>
  let A0 := set_reg2 (materialize2 A) 1 (Some (lconst npc)) in
  let sigma00 := sigma_sregs (v1 A0) sreg_idx (pm_set RA (lconst npc) pm_empty) in
  match prebind_args A0 (cs_rgn (u2_pre V)) (cs_divdef (u2_pre V)) sigma00 with
  | None => SF2 "call: argument regions / companions not resolvable in the caller state"
  | Some (sigma0, skip8) =>
  let S := drop_divdefs skip8 (load_cstate2 P (u2_pre V) (u_entry (u1 V)) []) in
  match match_state2 isv_call2 is_sreg_key true MM_call sigma0 S A0 with
  | MFail m => SF2 ("call: PRE not matched: " ++ m)
  | MOk sigma =>
      if negb (footprint_ok2 D A0 sigma V spoff) then SF2 "call: callee footprint / sp not admissible in this unit" else
      if negb (Z.leb (vp_fdepth P + Z.of_nat (length (fakes_of (vs_rgn A0)))) (u2_fdepth V)) then SF2 "call: callee live-frame budget (fdepth) too small" else
      if negb (pm_forallb (fun _ e => lin_below e (vs2_next A0)) sigma) then SF2 "call: internal: sigma range not below the symbol bound" else
      match call_base2 D A0 V sigma spoff npc with
      | None => SF2 "call: internal: caller regions for the callee footprint"
      | Some B =>
          match apply_exits2 P B sigma spoff npc (u2_exits V) with
          | None => SF2 "call: an exit of the callee cannot be instantiated in this caller state"
          | Some succs =>
          if forallb (fun B' => vstate_below_b (v1 B') && globs_in_fcells P B') succs then SN2 succs else SF2 "call: internal: symbol hygiene / global cells of an instantiated exit"
          end
      end
  end end end.

Fixpoint try_variants2 (D : denv2) (A : vstate2) (l : list vunit2) (spoff npc : Z) (msgs : list string) : sres2 :=
  match l with
  | [] => SF2 ("call: no variant applies: " ++ str_concat msgs)
  | V :: t => match try_variant2 D A V spoff npc with
              | SN2 succs => SN2 succs
              | SF2 m => try_variants2 D A t spoff npc (m :: msgs)
              end
  end.

Fixpoint insert_prio2 (V : vunit2) (l : list vunit2) : list vunit2 :=
  match l with
  | [] => [V]
  | W :: t => if Z.ltb (u_prio (u1 V)) (u_prio (u1 W)) then V :: l else W :: insert_prio2 V t
  end.

Fixpoint hinted_variants2 (calls : list vcall) (pc : Z) (all : list vunit2) : list vunit2 :=
  match calls with
  | [] => []
  | c :: t => if Z.eqb (call_pc c) pc
              then (List.filter (fun V => Z.eqb (u_vid (u1 V)) (call_vid c)) all ++ hinted_variants2 t pc all)%list
              else hinted_variants2 t pc all
  end.

Definition call_variants2 (D : denv2) (pc tgt : Z) : list vunit2 :=
  let cands := List.filter (fun V => Z.eqb (u_entry (u1 V)) tgt)
                 (match pm_get (zkey tgt) (de2_vidx D) with Some l => l | None => [] end) in
  match hinted_variants2 (u_calls (u1 (de2_U D))) pc cands with
  | [] => fold_right insert_prio2 [] cands
  | hv => hv
  end.

Definition do_call2 (D : denv2) (A : vstate2) (tgt npc : Z) (variants : list vunit2) : sres2 :=
  match sp_offset (v1 A) with
  | None => SF2 "call: sp is not SP0 + constant"
  | Some spoff => try_variants2 D A variants spoff npc []
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lift2 (r : vresult2) : sres2 :=
  match r with VR2_next l => SN2 l | VR2_fail m => SF2 m end.

Definition dstep2 (D : denv2) (A : vstate2) : sres2 :=
  let G := de2_G D in let A1 := v1 A in
  match itab_get (ge2_itab G) (vs_pc A1) with
  | None => SF2 "no decoded instruction at pc"
  | Some i =>
      match i with
      | Jal rd imm =>
          let tgt := wrap64 (vs_pc A1 + bv_signed imm) in
          let npc := npc_of A1 in
          match (if Z.ltb 0 tgt then pm_get (zkey tgt) (ge2_ctab G) else None) with
          | Some c => do_contract2 D A c (rz rd) npc
          | None =>
              if Z.eqb (rz rd) 1 then
                match call_variants2 D (vs_pc A1) tgt with
                | [] =>
                    match vstep2 (de2_P D) A i with
                    | VR2_next [A'] => SN2 [set_ctx2 A' (npc :: vs_ctx (v1 A'))]
                    | VR2_next _ => SF2 "jal: unexpected successor count"
                    | VR2_fail m => SF2 m
                    end
                | vs => do_call2 D A tgt npc vs
                end
              else if Z.eqb (rz rd) 0 then lift2 (vstep2 (de2_P D) A i)
              else SF2 "jal with rd not in {x0, ra}"
          end
      | Jalr rd rs1 imm =>
          if Z.eqb (rz rd) 0 && Z.eqb (rz rs1) 1 && Z.eqb (bv_signed imm) 0 then do_ret2 D A i
          else lift2 (vstep2 (de2_P D) A i)
      | _ => lift2 (vstep2 (de2_P D) A i)
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint check_defer_bound (isv : sym -> bool) (sigma : pmap lin) (l : list (lin * lin)) : bool :=
  match l with
  | [] => true
  | (e, e') :: t =>
      (match unbound_vars isv sigma e with
       | [] => lin_eqb (lsubst sigma e) e'
       | _ => true
       end) && check_defer_bound isv sigma t
  end.

(* [comment removed for export] *)
Fixpoint cm_from (pm : cellmap) (k : Z) : cellmap :=
  match pm with
  | [] => []
  | (k', c) :: t => if Z.ltb k' k then cm_from t k else pm
  end.

(* [comment removed for export] *)
Fixpoint prematch_cells (isv : sym -> bool) (l : list (Z * (Z * lin))) (prev : Z) (pm0 pm : cellmap) (acc : macc)
  : option macc :=
  match l with
  | [] => Some acc
  | (k, (w, e)) :: t =>
      let pm1 := cm_from (if Z.ltb k prev then pm0 else pm) k in
      match pm1 with
      | (k', (w', Some e')) :: _ =>
          if Z.eqb k' k && Z.eqb w w' then prematch_cells isv t k pm0 pm1 (match_loc isv acc e e') else None
      | _ => None
      end
  end.

Definition const_regs_ok (l : list (Z * lin)) (A : vstate) : bool :=
  forallb_l (fun re : Z * lin =>
               if lin_is_const (snd re) then
                 match pm_get (Z.to_pos (fst re)) (vs_regs A) with Some e' => lin_eqb (snd re) e' | None => false end
               else true) l.

Definition prematch2 (X : cstate2) (A : vstate2) : bool :=
  if negb (const_regs_ok (cs_regs (c1 X)) (v1 A)) then false else
  let regsS := pm_elements (pm_of_list (map (fun re : Z * lin => (Z.to_pos (fst re), snd re)) (cs_regs (c1 X)))) in
  match match_regs isv_join2 no_skip regsS (v1 A) (pm_empty, []) with
  | inr _ => false
  | inl acc1 =>
      (* [comment removed for export] *)
      if negb (check_defer_bound isv_join2 (fst acc1) (snd acc1)) then false else
      match prematch_cells isv_join2 (cs_slots (c1 X)) 0 (vs_slots (v1 A)) (vs_slots (v1 A)) acc1 with
      | None => false
      | Some acc2 =>
          match prematch_cells isv_join2 (cs_globs (c1 X)) 0 (vs_globs (v1 A)) (vs_globs (v1 A)) acc2 with
          | None => false
          | Some (sigma, defer) => check_defer_bound isv_join2 sigma defer
          end
      end
  end.

Fixpoint try_disjuncts2 (D : denv2) (Rstart : lin) (A : vstate2) (c : vcut2) (sts : list cstate2) (rks : list lin)
         (msgs : list string) : option (list string) :=
  match sts with
  | [] => Some msgs
  | X :: t =>
      let rk := match rks with r :: _ => Some r | [] => None end in
      let rks' := match rks with _ :: r' => r' | [] => [] end in
      if negb (prematch2 X A) then try_disjuncts2 D Rstart A c t rks' ("registers differ" :: msgs) else
      let S := load_cstate2 (de2_P D) X (cut2_pc c) (cut2_ctx c) in
      match match_state2 isv_join2 no_skip false MM_cut pm_empty S A with
      | MOk sigma =>
          if ge2_ranks (de2_G D) then
            match rk with
            | None => try_disjuncts2 D Rstart A c t rks' ("cut: disjunct matched but has no rank" :: msgs)
            | Some r =>
                if qge (v1 A) (lsub Rstart (lsubst sigma r)) 1 then None
                else try_disjuncts2 D Rstart A c t rks' ("cut: rank does not decrease" :: msgs)
            end
          else None
      | MFail m => try_disjuncts2 D Rstart A c t rks' (m :: msgs)
      end
  end.

Definition cut_arrival2 (D : denv2) (Rstart : lin) (A : vstate2) (c : vcut2) : sres2 :=
  match try_disjuncts2 D Rstart A c (cut2_states c) (cut2_ranks c) [] with
  | None => SN2 []
  | Some msgs => SF2 ("cut: not included in any disjunct: " ++ str_concat msgs)
  end.

Fixpoint pick2 (sts : list cstate2) (rks : list lin) (i : Z) : option (cstate2 * lin) :=
  match sts, rks with
  | X :: t, r :: rt => if Z.eqb i 0 then Some (X, r) else pick2 t rt (Z.pred i)
  | _, _ => None
  end.

Definition try_hint2 (D : denv2) (Rstart : lin) (A : vstate2) (c : vcut2) (h : Z) : bool :=
  match pick2 (cut2_states c) (cut2_ranks c) h with
  | Some (X, r) =>
      match match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 (de2_P D) X (cut2_pc c) (cut2_ctx c)) A with
      | MOk sigma => if ge2_ranks (de2_G D) then qge (v1 A) (lsub Rstart (lsubst sigma r)) 1 else false
      | MFail _ => false
      end
  | None => false
  end.

Definition cut_arrival2h (D : denv2) (Rstart : lin) (A : vstate2) (c : vcut2) (tape : list Z) : sres2 :=
  match tape with
  | h :: _ => if try_hint2 D Rstart A c h then SN2 [] else cut_arrival2 D Rstart A c
  | [] => cut_arrival2 D Rstart A c
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint explore2 (D : denv2) (fuel : nat) (origin : string) (Rstart : lin) (work : list (bool * vstate2)) (tape : list Z) : res2 :=
  match fuel with
  | O => match work with
         | (_, A) :: _ => R2Fail (u_vid (u1 (de2_U D))) origin A "out of fuel"
         | [] => R2Ok
         end
  | S f =>
      match work with
      | [] => R2Ok
      | (first, A) :: rest =>
          let atcut := if first then None else find_cut2 D (vs2_pc A) (vs_ctx (v1 A)) in
          match atcut with
          | Some c =>
              match cut_arrival2h D Rstart A c tape with
              | SN2 _ => explore2 D f origin Rstart rest (tl tape)
              | SF2 m => R2Fail (u_vid (u1 (de2_U D))) origin A m
              end
          | None =>
              match dstep2 D A with
              | SN2 succs => explore2 D f origin Rstart (map (fun A' => (false, A')) succs ++ rest)%list tape
              | SF2 m => R2Fail (u_vid (u1 (de2_U D))) origin A m
              end
          end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition globs_fcells_ok (P : vparams2) (cs : cstate2) : bool :=
  negb (has_asan P)
  || forallb (fun c : Z * (Z * lin) => match c with (a, (w, _)) => in_cells (vp_fcells (p1 P)) a w end) (cs_globs (c1 cs)).

Fixpoint ranges_eqb (a b : list (Z * Z)) : bool :=
  match a, b with
  | [], [] => true
  | (x1, y1) :: a', (x2, y2) :: b' => Z.eqb x1 x2 && Z.eqb y1 y2 && ranges_eqb a' b'
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition shadow_disp_ok (P : vparams2) (cs : cstate2) : bool :=
  forallb (fun s => match sr_kind s with
                    | SK_shadow o => Z.eqb (sr_disp s) (vp_shoff P)
                                     && (negb (Pos.eqb o SP0)
                                         || (Pos.eqb (sr_base s) SP8 && Z.eqb (sr_lo s) (- (vp_frame (p1 P) / 8) - 8) && Z.eqb (sr_hi s) 1
                                             && ranges_eqb (sr_w s) (shadow_w (vp_wstack (p1 P)))))
                    | _ => true end) (cs_rgn cs).

Definition cstate2_ok (P : vparams2) (cs : cstate2) : bool :=
  cstate_ok (p1 P) (c1 cs) && cstate2_wf_b cs && (globs_fcells_ok P cs && shadow_disp_ok P cs).

(* [comment removed for export] *)
Definition wrgn_ok (U : vunit2) (cs : cstate2) : bool :=
  forallb (fun sr => match sr_kind sr with
                     | SK_arg => let i := Z.pos (sr_base sr) - 19 in
                                 forallb (fun r : Z * Z => existsb (fun w : Z * (Z * Z) => match w with (j, (lo, hi)) =>
                                            Z.eqb j i && Z.leb lo (fst r) && Z.leb (snd r) hi end) (u2_wrgn U)) (sr_w sr)
                     | _ => true
                     end) (cs_rgn cs).

Definition mod8_ok (P : vparams2) (U : vunit2) : bool :=
  negb (has_asan P)
  || (Z.eqb (u_sp (u1 U) mod 8) 0 && Z.eqb (vp_frame (p1 P) mod 8) 0).

Definition pre_canonical2 (G : genv2) (P : vparams2) (U : vunit2) : bool :=
  let S := v1 (load_cstate2 P (u2_pre U) (u_entry (u1 U)) []) in
  ra_is_exit (u1 U) (get_reg S 1)
  && absval_eqb (get_reg S 2) (lsymc SP0 (u_sp (u1 U)))
  && sregs_intact S
  && absval_eqb (get_reg S 3) (lsym GP)
  && absval_eqb (get_reg S 4) (lconst (ge2_tp G)).

Definition rank_nonneg2 (P : vparams2) (c : vcut2) : bool :=
  forallb (fun xr : cstate2 * lin =>
             let S := load_cstate2 P (fst xr) (cut2_pc c) (cut2_ctx c) in
             qge (v1 S) (snd xr) 0 && lin_below (snd xr) (cs_next (c1 (fst xr))))
          (combine (cut2_states c) (cut2_ranks c)).

Definition unit_static_ok2 (G : genv2) (P : vparams2) (U : vunit2) : option string :=
  let V := u1 U in
  if negb (cstate2_ok P (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)) then Some "static: entry state ill-formed" else
  if negb (pre_canonical2 G P U) then Some "static: entry state registers not canonical (ra/sp/s-regs/gp/tp)" else
  if negb (forallb (fun c => pc_ok (cut2_pc c) && forallb (fun cs => cstate2_ok P cs && wrgn_ok U cs) (cut2_states c)) (u2_cuts U)) then Some "static: a cut state is ill-formed" else
  if negb (pc_ok (u_entry V)) then Some "static: entry pc out of range" else
  if negb (forallb (fun cs => cstate2_ok P cs && cstate2_iface_b cs && wrgn_ok U cs) (u2_exits U)) then Some "static: an exit state is ill-formed" else
  if ge2_ranks G && negb (forallb (fun c => Nat.eqb (length (cut2_ranks c)) (length (cut2_states c)) && rank_nonneg2 P c) (u2_cuts U))
  then Some "static: missing or possibly negative rank" else
  if negb (forallb (fun r : Z * Z => Z.leb (- vp_frame (p1 P)) (fst r) && Z.leb (snd r) 0 && Z.leb (u_sp V) (fst r)) (u_wstack V))
  then Some "static: caller-visible write range outside [sp_off, 0)" else
  if negb (forallb (fun c : Z * Z => in_cells (vp_fcells (p1 P)) (fst c) (snd c)) (vp_wcells (p1 P)))
  then Some "static: unit writable cells not inside the F-level cells" else
  if Z.ltb 0 (u_sp V) || Z.ltb (u_sp V) (- vp_frame (p1 P)) then Some "static: sp_off outside the window" else
  if negb (mod8_ok P U) then Some "static: stack bounds not granule-aligned" else
  if negb (forallb (fun w : Z * (Z * Z) => Z.leb 0 (fst w) && Z.ltb (fst w) 8 && Z.leb (fst (snd w)) (snd (snd w))) (u2_wrgn U))
  then Some "static: malformed arg write range" else
  if negb (match u_root V with Some _ => match u2_wrgn U with [] => forallb (fun sr => negb (match sr_kind sr with SK_arg => true | _ => false end)) (cs_rgn (u2_pre U)) | _ => false end | None => true end)
  then Some "static: root unit with argument regions" else
  None.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint check_cut_states2 (D : denv2) (fuel : nat) (c : vcut2) (sts : list cstate2) (rks : list lin) (tps : list (list Z)) : res2 :=
  match sts with
  | [] => R2Ok
  | X :: t =>
      let R := match rks with r :: _ => r | [] => RANK_TOP end in
      let rks' := match rks with _ :: r' => r' | [] => [] end in
      let T := match tps with p :: _ => p | [] => [] end in
      let tps' := match tps with _ :: p' => p' | [] => [] end in
      let St := load_cstate2 (de2_P D) X (cut2_pc c) (cut2_ctx c) in
      match explore2 D fuel "cut" R [(true, St)] T with
      | R2Ok => check_cut_states2 D fuel c t rks' tps'
      | r => r
      end
  end.

Fixpoint check_cuts2 (D : denv2) (fuel : nat) (l : list vcut2) : res2 :=
  match l with
  | [] => R2Ok
  | c :: t => match check_cut_states2 D fuel c (cut2_states c) (cut2_ranks c) (cut2_tapes c) with
              | R2Ok => check_cuts2 D fuel t
              | r => r
              end
  end.

Definition check_unit2 (G : genv2) (done : list vunit2) (U : vunit2) : res2 :=
  let D := mk_denv2 G done U in
  let S0 := load_cstate2 (de2_P D) (u2_pre U) (u_entry (u1 U)) [] in
  match unit_static_ok2 G (de2_P D) U with
  | Some m => R2Fail (u_vid (u1 U)) "static" S0 m
  | None =>
      let fuel := N.to_nat (u_fuel (u1 U)) in
      match explore2 D fuel "entry" RANK_TOP [(true, S0)] (u2_tape U) with
      | R2Ok => check_cuts2 D fuel (u2_cuts U)
      | r => r
      end
  end.

Fixpoint check_units2 (G : genv2) (done : list vunit2) (l : list vunit2) : res2 :=
  match l with
  | [] => R2Ok
  | U :: t => match check_unit2 G done U with
              | R2Ok => check_units2 G (done ++ [U])%list t
              | r => r
              end
  end.

Definition check_cert2 (G : genv2) (C : vcert2) : res2 := check_units2 G [] C.

Fixpoint check_report2 (G : genv2) (done : list vunit2) (l : list vunit2) : list res2 :=
  match l with
  | [] => []
  | U :: t => check_unit2 G done U :: check_report2 G (done ++ [U])%list t
  end.

(* [comment removed for export] *)
Fixpoint check_chunks2 (G : genv2) (done : list vunit2) (chunks : list (list vunit2)) : Prop :=
  match chunks with
  | [] => True
  | c :: t => check_units2 G done c = R2Ok /\ check_chunks2 G (done ++ c)%list t
  end.

Fixpoint check_chunks2b (G : genv2) (done : list vunit2) (chunks : list (list vunit2)) : bool :=
  match chunks with
  | [] => true
  | c :: t => match check_units2 G done c with
              | R2Ok => check_chunks2b G (done ++ c)%list t
              | _ => false
              end
  end.

Lemma check_chunks2b_sound (G : genv2) : forall chunks done,
  check_chunks2b G done chunks = true -> check_chunks2 G done chunks.
Proof.
  induction chunks as [|c t IH]; intros done H; cbn [check_chunks2b check_chunks2] in H |- *; [exact I|].
  destruct (check_units2 G done c); [|discriminate]. split; [reflexivity|]. exact (IH _ H).
Qed.

(* [comment removed for export] *)
Definition report_chunk2 (G : genv2) (chunks : list (list vunit2)) (i : nat) : list res2 :=
  check_report2 G (List.concat (firstn i chunks)) (nth i chunks []).
