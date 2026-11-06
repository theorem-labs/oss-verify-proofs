(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStep VStepMem VState2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive vresult2 : Type := VR2_next (succs : list vstate2) | VR2_fail (msg : string).

Definition one2 (A : vstate2) : vresult2 := VR2_next [A].

Definition lift1 (A : vstate2) (r : vresult) : vresult2 :=
  match r with
  | VR_next l => VR2_next (map (with_v1 A) l)
  | VR_fail m => VR2_fail m
  end.

(* [comment removed for export] *)
Definition lift1c (A : vstate2) (r : vresult) : vresult2 :=
  match r with
  | VR_next l => VR2_next (map (with_v1c A) l)
  | VR_fail m => VR2_fail m
  end.

Definition finish2 (A : vstate2) (rd : Z) (v : absval) : vstate2 := with_v1 A (finish (v1 A) rd v).

(* [comment removed for export] *)
Definition afresh2 (A : vstate2) (b : itv) : absval * vstate2 :=
  let '(v, A1) := afresh (v1 A) b in (v, with_v1 A A1).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition base_syms (A : vstate2) (addr : lin) : list sym :=
  List.filter (is_base A) (lsyms addr).

(* [comment removed for export] *)
Definition has_base (A : vstate2) (e : lin) : bool :=
  existsb (fun s => match comp A s with Some _ => true | None => is_base A s end) (lsyms e).

Inductive cres2 : Type :=
| C2Rgn (r : vregion) (off : lin) (lo hi : Z)     (* [comment removed for export] *)
| C2Dead
| C2Fail (msg : string).

(* [comment removed for export] *)
Definition classify_rgn (A : vstate2) (r : vregion) (addr : lin) (n : Z) (is_store : bool) : cres2 :=
  let A1 := v1 A in
  let off := laddc (lsub addr (lsym (vr_base r))) (- vr_disp r) in
  match vr_kind r with
  | RK_shadow s =>
      if Pos.eqb s DATA then
        (* [comment removed for export] *)
        (if is_store then C2Fail "store into the Data shadow"
         else if negb (Z.eqb n 1) then C2Fail "Data shadow: access wider than 1 byte"
         else if (if (if qge A1 (lscale 8 off) (-16) then qle A1 (lsub (lscale 8 off) (lsym SIZE)) 15 else false) then qge A1 (lsym SIZE) 1 else false) then
                match bnd A1 off with
                | (Some lo, Some hi) => C2Rgn r off lo hi
                | _ => C2Rgn r off 0 0   (* [comment removed for export] *)
                end
         else if bnd_dead A1 off then C2Dead else C2Fail "Data shadow: offset outside the readable margin")
      else
        if negb (qge A1 off (vr_lo r)) then (if bnd_dead A1 off then C2Dead else C2Fail "region access below its extent")
        else if negb (qle A1 (laddc off n) (vr_hi r)) then (if bnd_dead A1 off then C2Dead else C2Fail "region access above its extent")
        else match bnd A1 off with
             | (Some lo, Some hi) =>
                 if itv_empty (Some lo, Some hi) then C2Dead
                 else if is_store && negb (in_ranges (vr_w r) lo (hi - lo + n)) then C2Fail "store outside the region's writable ranges"
                 else C2Rgn r off lo hi
             | _ => C2Fail "region offset unbounded"
             end
  | _ =>
      if negb (qge A1 off (vr_lo r)) then (if bnd_dead A1 off then C2Dead else C2Fail "region access below its extent")
      else if negb (qle A1 (laddc off n) (vr_hi r)) then (if bnd_dead A1 off then C2Dead else C2Fail "region access above its extent")
      else match bnd A1 off with
           | (Some lo, Some hi) =>
               if itv_empty (Some lo, Some hi) then C2Dead
               else if is_store && negb (in_ranges (vr_w r) lo (hi - lo + n)) then C2Fail "store outside the region's writable ranges"
               else C2Rgn r off lo hi
           | _ => C2Fail "region offset unbounded"
           end
  end.

Definition classify2 (A : vstate2) (addr : lin) (n : Z) (is_store : bool) : option cres2 :=
  match base_syms A addr with
  | [] => None                                          (* [comment removed for export] *)
  | [B] =>
      if negb (Z.eqb (lcoef addr B) 1) then Some (C2Fail "region base with coefficient <> 1")
      else if negb (Z.eqb (lcoef addr SP0) 0 && Z.eqb (lcoef addr DATA) 0) then Some (C2Fail "mixed SP0/DATA/region address")
      else match rgn_get (vs_rgn A) B with
           | Some r => Some (classify_rgn A r addr n is_store)
           | None => Some (C2Fail "internal: base symbol without region")
           end
  | _ => Some (C2Fail "address mentions two region bases")
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sh_cover (m : cellmap) (o : Z) : option (Z * (Z * absval)) :=
  find (fun e : Z * cell => match e with (k, (w, _)) => Z.leb k o && Z.ltb o (k + w) end)
       (cm_overlapping m o (o + 1)).

(* [comment removed for export] *)
Fixpoint sh_cut (m : cellmap) (lo hi : Z) : cellmap :=
  match m with
  | [] => []
  | (k, (w, v)) :: t =>
      if (if Z.ltb k hi then Z.ltb lo (k + w) else false) then   (* [comment removed for export] *)
        let keep_l := if Z.ltb k lo then match v with Some e => if lin_is_const e then [(k, (lo - k, v))] else [] | None => [] end else [] in
        let keep_r := if Z.ltb hi (k + w) then match v with Some e => if lin_is_const e then [(hi, (k + w - hi, v))] else [] | None => [] end else [] in
        (keep_l ++ keep_r ++ sh_cut t lo hi)%list
      else (k, (w, v)) :: sh_cut t lo hi
  end.

(* [comment removed for export] *)
Definition sh_same (v : absval) (e : lin) : bool :=
  match v with Some e' => if lin_is_const e' then Z.eqb (lc e') (lc e) else false | None => false end.

Definition sh_ins_r (t : cellmap) (k w : Z) (e : lin) : cellmap :=
  match t with
  | (k2, (w2, v2)) :: t2 => if (if Z.eqb k2 (k + w) then sh_same v2 e else false) then (k, (w + w2, Some e)) :: t2
                            else (k, (w, Some e)) :: t
  | [] => [(k, (w, Some e))]
  end.

Fixpoint sh_ins (m : cellmap) (o w : Z) (e : lin) : cellmap :=
  match m with
  | [] => [(o, (w, Some e))]
  | (k, (w', v')) :: t =>
      if Z.ltb k o then
        if (if Z.eqb (k + w') o then sh_same v' e else false) then sh_ins_r t k (w' + w) e
        else (k, (w', v')) :: sh_ins t o w e
      else sh_ins_r m o w e
  end.

(* [comment removed for export] *)
Definition sh_write (m : cellmap) (o w : Z) (v : absval) : cellmap :=
  let m1 := sh_cut m o (o + w) in
  match v with
  | Some e => if lin_is_const e then sh_ins m1 o w e else cm_set m1 o (w, Some e)
  | None => m1
  end.

(* [comment removed for export] *)
Fixpoint sh_run_cover (pm : cellmap) (pos stop b : Z) (fuel : nat) : bool :=
  if Z.leb stop pos then true else
  match fuel with
     | O => false
     | S f =>
         match sh_cover pm pos with
         | Some (k', (w', Some e')) =>
             if (if (if lin_is_const e' then Z.eqb (lc e') b else false) then Z.ltb pos (k' + w') else false)
             then sh_run_cover pm (k' + w') stop b f else false
         | _ => false
         end
     end.

Lemma sh_run_cover_andb pm pos stop b fuel : sh_run_cover pm pos stop b fuel =
  (Z.leb stop pos
   || match fuel with
      | O => false
      | S f =>
          match sh_cover pm pos with
          | Some (k', (w', Some e')) =>
              lin_is_const e' && Z.eqb (lc e') b && Z.ltb pos (k' + w') && sh_run_cover pm (k' + w') stop b f
          | _ => false
          end
      end).
Proof. destruct fuel; reflexivity. Qed.

(* [comment removed for export] *)
Definition sh_uniform (pm : cellmap) (lo hi : Z) : option Z :=
  match sh_cover pm lo with
  | Some (_, (_, Some e)) =>
      if (if lin_is_const e then sh_run_cover pm lo (hi + 1) (lc e) (S (List.length pm)) else false) then Some (lc e) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition sh_load (A1 : vstate) (r : vregion) (o : Z) (signed : bool) : absval * vstate :=
  match sh_cover (vr_cells r) o with
  | Some (k, (w, Some e)) =>
      if lin_is_const e then (Some (lconst (sign_adjust signed 1 (Z.land (lc e) 255))), A1)
      else if Z.eqb w 1 then areinterp A1 e 1 signed
      else fresh_loaded A1 1 signed
  | _ => fresh_loaded A1 1 signed
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive dsres : Type := DS_one (v : absval) (A1 : vstate) | DS_two (A0 A1 : vstate) (v1_ : absval) | DS_fail (msg : string).

(* [comment removed for export] *)
Definition data_shadow_load (A1 : vstate) (g : lin) (signed : bool) : dsres :=
  let g8 := lscale 8 g in
  if (if qge A1 g8 0 then qle A1 (lsub (laddc g8 8) (lsym SIZE)) 0 else false) then DS_one (Some (lconst 0)) A1
  else if (if qge A1 g8 0 then qle A1 (lsub (laddc g8 1) (lsym SIZE)) 0 else false) then
    (* [comment removed for export] *)
    let '(vj, Aj) := afresh A1 (Some 1, Some 7) in
    match vj with
    | Some ej =>
        let e := lsub (ladd g8 ej) (lsym SIZE) in          (* [comment removed for export] *)
        let '(ok1, Aj1) := aassume Aj e in
        let '(ok2, Aj2) := aassume Aj1 (lneg e) in
        if ok1 && ok2 then DS_two A1 Aj2 vj
        else DS_one (Some (lconst 0)) A1                    (* [comment removed for export] *)
    | None => DS_fail "internal: afresh returned Top"
    end
  else if (if (if qge A1 g8 (-16) then qle A1 (laddc g8 1) 0 else false) then true else (if qge A1 (lsub g8 (lsym SIZE)) 0 then qle A1 (lsub g8 (lsym SIZE)) 15 else false)) then
    let '(v, A2) := fresh_loaded A1 1 signed in DS_one v A2
  else DS_fail "Data shadow: granule not decidable (inside/last/margin)".

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition load_cells (A1 : vstate) (m : cellmap) (off : lin) (lo hi n : Z) (signed : bool) : absval * vstate :=
  if Z.eqb lo hi then
    match cm_get m lo with
    | Some (w, Some v) =>
        if Z.eqb w n then areinterp A1 v n signed
        else if Z.ltb n w then atruncate A1 v n signed
        else fresh_loaded A1 n signed
    | _ =>
        match const_cover m lo n with
        | Some v => (Some (lconst (sign_adjust signed n v)), A1)
        | None => fresh_loaded A1 n signed
        end
    end
  else fresh_loaded A1 n signed.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition install_ok (m : cellmap) (lo hi n : Z) : bool :=
  Z.eqb lo hi && Z.ltb n 8 && match cm_overlapping m lo (lo + n) with [] => true | _ => false end.

Definition load_install (A1 : vstate) (m : cellmap) (lo n : Z) (signed : bool) : option (absval * vstate * cellmap) :=
  let '(vu, A2) := afresh A1 (urange n) in
  match vu with
  | Some u => let '(v, A3) := areinterp A2 u n signed in Some (v, A3, cm_set m lo (n, Some u))
  | None => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fork_skip (A1 : vstate) (q : sym) (v : Z) : bool :=
  match pm_get q (scong (vs_store A1)) with
  | Some (m, r) => negb (Z.eqb m 0) && negb (Z.eqb ((v - r) mod m) 0)
  | None => false
  end.

Fixpoint shfork_states (A : vstate2) (r : vregion) (q : sym) (c : Z) (signed : bool) (rd : Z) (v : Z) (k : nat)
  : option (list vstate2) :=
  match k with
  | O => Some []
  | S k' =>
      if fork_skip (v1 A) q v then shfork_states A r q c signed rd (v + 1) k' else
      match sh_cover (vr_cells r) (c + v), shfork_states A r q c signed rd (v + 1) k' with
      | Some (_, (_, Some e)), Some rest =>
          if lin_is_const e then
            Some (finish2 (with_v1 A (asetbox (v1 A) q (Some v, Some v))) rd
                          (Some (lconst (sign_adjust signed 1 (Z.land (lc e) 255)))) :: rest)
          else None
      | _, _ => None
      end
  end.

Definition x_load_rgn (P : vparams2) (A : vstate2) (r : vregion) (off : lin) (lo hi n : Z) (signed : bool) (rd : Z) : vresult2 :=
  match vr_kind r with
  | RK_shadow s =>
      if Pos.eqb s DATA then
        if negb (asan_mode P && Z.leb 8 (vp_datal P)) then VR2_fail "Data shadow rule needs an ASan image with 8-aligned Data" else
        match data_shadow_load (v1 A) off signed with
        | DS_one v A1 => one2 (finish2 (with_v1 A A1) rd v)
        | DS_two A0 A1 vj => VR2_next [finish2 (with_v1 A A0) rd (Some (lconst 0)); finish2 (with_v1 A A1) rd vj]
        | DS_fail m => VR2_fail m
        end
      else if negb (Z.eqb n 1) then VR2_fail "shadow region: access wider than 1 byte"
      else if Z.eqb lo hi then
        match sh_cover (vr_cells r) lo with
        | None => VR2_fail "shadow region: load of an unknown shadow byte"
        | Some _ => let '(v, A1) := sh_load (v1 A) r lo signed in one2 (finish2 (with_v1 A A1) rd v)
        end
      else
        (* [comment removed for export] *)
        match sh_uniform (vr_cells r) lo hi with
        | Some b => one2 (finish2 A rd (Some (lconst (sign_adjust signed 1 (Z.land b 255)))))
        | None =>
        (* [comment removed for export] *)
        match lin_single off with
        | Some (q, 1) =>
            if Pos.leb q LAST_FIXED2 || Z.ltb 15 (hi - lo) then VR2_fail "shadow region: ranged offset load" else
            match shfork_states A r q (lc off) signed rd (lo - lc off) (S (Z.to_nat (hi - lo))) with
            | Some l => VR2_next l
            | None => VR2_fail "shadow region: some granule of the offset range is unknown"
            end
        | _ => VR2_fail "shadow region: ranged offset load"
        end end
  | RK_flag _ => VR2_fail "load from a fake-frame flag cell"
  | RK_fs => let '(v, A1) := load_cells (v1 A) (vr_cells r) off lo hi n signed in one2 (finish2 (with_v1 A A1) rd v)
  | _ => (* [comment removed for export] *)
      match (if install_ok (vr_cells r) lo hi n then load_install (v1 A) (vr_cells r) lo n signed else None) with
      | Some (v, A3, m') => one2 (finish2 (with_v1 (set_rgn A (rgn_upd (vs_rgn A) (set_cells r m'))) A3) rd v)
      | None => let '(v, A1) := load_cells (v1 A) (vr_cells r) off lo hi n signed in one2 (finish2 (with_v1 A A1) rd v)
      end
  end.

(* [comment removed for export] *)
Definition kbyte_get (P : vparams2) (a n : Z) : option Z :=
  match kcell_get (vp_kcells P) a n with
  | Some v => Some v
  | None => if Z.eqb n 1 then match krun_get (vp_kruns P) a with Some b => Some (Z.land b 255) | None => None end else None
  end.

(* [comment removed for export] *)
Definition free_single (A : vstate2) (addr : lin) : option (sym * Z) :=
  match lt addr with
  | [(q, 1)] => if Pos.leb q LAST_FIXED2 || has_base A (lsym q) then None else Some (q, lc addr)
  | _ => None
  end.

Fixpoint kfork_states (P : vparams2) (A : vstate2) (q : sym) (c : Z) (signed : bool) (rd : Z) (v : Z) (k : nat)
  : option (list vstate2) :=
  match k with
  | O => Some []
  | S k' =>
      if fork_skip (v1 A) q v then kfork_states P A q c signed rd (v + 1) k' else
      match kbyte_get P (c + v) 1, kfork_states P A q c signed rd (v + 1) k' with
      | Some b, Some rest =>
          Some (finish2 (with_v1 A (asetbox (v1 A) q (Some v, Some v))) rd (Some (lconst (sign_adjust signed 1 b))) :: rest)
      | _, _ => None
      end
  end.

Definition kfork (P : vparams2) (A : vstate2) (addr : lin) (signed : bool) (rd : Z) : option vresult2 :=
  if negb (match base_syms A addr with [] => true | _ => false end) then None else
  match free_single A addr with
  | None => None
  | Some (q, c) =>
      match lp_bounds (vs_store (v1 A)) (lsym q) with
      | (Some lo, Some hi) =>
          if Z.ltb hi lo || Z.ltb 15 (hi - lo) then None else
          match kfork_states P A q c signed rd lo (S (Z.to_nat (hi - lo))) with
          | Some l => Some (VR2_next l)
          | None => None
          end
      | _ => None
      end
  end.

(* [comment removed for export] *)
Fixpoint memo_lookup (A1 : vstate) (l : list (lin * (Z * lin))) (addr : lin) (n : Z) : option lin :=
  match l with
  | [] => None
  | (a', (n', v)) :: t =>
      let d := anorm A1 (lsub addr a') in
      if Z.eqb n' n && lin_is_const d && Z.eqb (lc d) 0 then Some v else memo_lookup A1 t addr n
  end.

Definition memo_push (l : list (lin * (Z * lin))) (e : lin * (Z * lin)) : list (lin * (Z * lin)) :=
  let l' := (l ++ [e])%list in
  if Nat.ltb 8 (List.length l') then List.tl l' else l'.

(* [comment removed for export] *)
Definition x_load_stack (P : vparams2) (A : vstate2) (addr : lin) (off : lin) (lo hi n : Z) (signed : bool) (rd : Z) : vresult2 :=
  let A1 := v1 A in
  if Z.ltb n 8 && negb (Z.eqb lo hi) then
    match memo_lookup A1 (vs_memo A) addr n with
    | Some v => let '(v', A2) := areinterp A1 v n signed in one2 (finish2 (with_v1 A A2) rd v')
    | None =>
        let '(v, A2) := load_val (p1 P) A1 (RStack off lo hi) addr n false in
        match v with
        | Some ve =>
            let '(v', A3) := areinterp A2 ve n signed in
            one2 (finish2 (set_memo (with_v1 A A3) (memo_push (vs_memo A) (addr, (n, ve)))) rd v')
        | None => one2 (finish2 (with_v1 A A2) rd None)
        end
    end
  else
    match (if install_ok (vs_slots A1) lo hi n then load_install A1 (vs_slots A1) lo n signed else None) with
    | Some (v, A3, m') => one2 (finish2 (with_v1 A (set_slots A3 m')) rd v)
    | None => let '(v, A2) := load_val (p1 P) A1 (RStack off lo hi) addr n signed in one2 (finish2 (with_v1 A A2) rd v)
    end.

Definition x_load2 (P : vparams2) (A : vstate2) (sz : msize) (signed : bool) (rd rs1 : Z) (imm : Z) : vresult2 :=
  let n := msize_z sz in
  match sz, signed with
  | SZ8, false => VR2_fail "ld: unexpected unsigned form"
  | _, _ =>
  if Z.eqb rd 0 then lift1 A (x_load (p1 P) (v1 A) sz signed rd rs1 imm) else
  match addr_of (v1 A) rs1 imm with
  | None => VR2_fail "load via Top address"
  | Some addr =>
      match (if lin_is_const addr then kbyte_get P (lc addr) n else None) with
      | Some v => one2 (finish2 A rd (Some (lconst (sign_adjust signed n v))))
      | None =>
          match (if Z.eqb n 1 && asan_mode P then kfork P A addr signed rd else None) with
          | Some r => r
          | None =>
          match classify2 A addr n false with
          | None =>
              (* [comment removed for export] *)
              if asan_mode P then
                match classify (p1 P) (v1 A) addr n false with
                | COk (RStack off lo hi) => x_load_stack P A addr off lo hi n signed rd
                | CDead => VR2_next []
                | CFail m => VR2_fail m
                | COk r => let '(v, A1) := load_val (p1 P) (v1 A) r addr n signed in one2 (finish2 (with_v1 A A1) rd v)
                end
              else lift1 A (x_load (p1 P) (v1 A) sz signed rd rs1 imm)
          | Some (C2Fail m) => VR2_fail m
          | Some C2Dead => VR2_next []
          | Some (C2Rgn r off lo hi) => x_load_rgn P A r off lo hi n signed rd
          end end
      end
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition havoc_other_args (l : list vregion) (b : sym) : list vregion :=
  map (fun r => match vr_kind r with
                | RK_arg => if Pos.eqb (vr_base r) b then r else set_rnul (set_cells r []) []
                | _ => r
                end) l.

(* [comment removed for export] *)
Definition rgn_kill_nul (A1 : vstate) (r : vregion) (lo hi : Z) (v : absval) : vregion :=
  match vr_nul r with
  | [] => r
  | _ => if is_zero_val A1 v then r
         else set_rnul r (List.filter (fun f : Z * Z => Z.ltb (snd f) lo || Z.ltb hi (fst f)) (vr_nul r))
  end.
Definition rgn_add_nul (r : vregion) (lo hi : Z) : vregion := set_rnul r (nul_min ((lo, hi) :: vr_nul r)).

(* [comment removed for export] *)
Definition release_frame (A : vstate2) (ff : sym) : vstate2 :=
  let l := List.filter (fun r => negb (Pos.eqb (vr_base r) ff)
                                  && negb (match vr_kind r with
                                           | RK_shadow s => Pos.eqb s ff
                                           | RK_flag o => Pos.eqb o ff
                                           | _ => false end)) (vs_rgn A) in
  mkVS2 (v1 A) l (List.filter (fun s => negb (Pos.eqb s ff)) (vs_live A)) (vs_divdef A) [].

Definition store_rgn (A : vstate2) (r : vregion) (off : lin) (lo hi n : Z) (v : absval) : vresult2 :=
  let A1 := v1 A in
  match vr_kind r with
  | RK_flag owner =>
      if Z.eqb n 1 && Z.eqb lo 0 && Z.eqb hi 0 && is_zero_byte A1 v
      then one2 (set_pc2 (release_frame A owner) (npc_of A1))
      else VR2_fail "store to a fake-frame flag cell other than the releasing `sb zero`"
  | RK_shadow _ =>
      match v with
      | Some e =>
          if negb (lin_is_const e) then VR2_fail "shadow store of a non-constant value" else
          (* [comment removed for export] *)
          let b0 := Z.land (lc e) 255 in
          if negb (forallb (fun j => Z.eqb (Z.land (Z.shiftr (lc e) (8 * j)) 255) b0) (zrange 0 (Z.to_nat n)))
          then VR2_fail "shadow store: bytes of the constant differ" else
          (* [comment removed for export] *)
          if Z.eqb lo hi then
            one2 (set_pc2 (clear_memo (set_rgn A (rgn_upd (vs_rgn A) (set_rnul (set_cells r (sh_write (vr_cells r) lo n (Some (lconst b0)))) [])))) (npc_of A1))
          else
            one2 (set_pc2 (clear_memo (set_rgn A (rgn_upd (vs_rgn A) (set_rnul (set_cells r (sh_cut (vr_cells r) lo (hi + n))) [])))) (npc_of A1))
      | None => VR2_fail "shadow store of Top"
      end
  | _ =>
      let cells :=
        if Z.eqb lo hi then
          let m := cm_kill (vr_cells r) lo (lo + n) in
          match v with Some e => cm_set m lo (n, Some e) | None => m end
        else cm_kill (vr_cells r) lo (hi + n) in
      let r1 := rgn_kill_nul A1 (set_cells r cells) lo (hi + n - 1) v in
      let r2 := if Z.eqb n 1 && is_zero_byte A1 v then rgn_add_nul r1 lo hi else r1 in
      let l1 := rgn_upd (vs_rgn A) r2 in
      let l2 := match vr_kind r with RK_arg => havoc_other_args l1 (vr_base r) | _ => l1 end in
      one2 (set_pc2 (clear_memo (set_rgn A l2)) (npc_of A1))
  end.

Definition x_store2 (P : vparams2) (A : vstate2) (sz : msize) (rs1 rs2 : Z) (imm : Z) : vresult2 :=
  let n := msize_z sz in
  match addr_of (v1 A) rs1 imm with
  | None => VR2_fail "store via Top address"
  | Some addr =>
      match classify2 A addr n true with
      | None => lift1c A (x_store (p1 P) (v1 A) sz rs1 rs2 imm)
      | Some (C2Fail m) => VR2_fail m
      | Some C2Dead => VR2_next []
      | Some (C2Rgn r off lo hi) => store_rgn A r off lo hi n (get_reg (v1 A) rs2)
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition base_res8 (A : vstate2) (B : sym) : option Z :=
  match pm_get B (scong (vs_store (v1 A))) with
  | Some (m, r) => if negb (Z.eqb m 0) && Z.eqb (m mod 8) 0 then Some (r mod 8) else None
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint divdef_find (l : list (positive * (lin * Z))) (x : lin) (m : Z) : option sym :=
  match l with
  | [] => None
  | (q, (x', m')) :: t => if Z.eqb m' m && lin_eqb x' x then Some q else divdef_find t x m
  end.

(* [comment removed for export] *)
Definition fdivm (A : vstate2) (x : lin) (m : Z) : option (lin * vstate2) :=
  if lin_is_const x then Some (lconst (Z.div (lc x) m), A)
  else if Z.eqb m 8 && ldivisible x 8 then Some (lshiftr x 3, A)
  else match divdef_find (pm_elements (vs_divdef A)) x m with
       | Some q => Some (lsym q, A)
       | None =>
           let A1 := v1 A in
           let b := lp_bounds (vs_store A1) x in
           let bq := (match fst b with Some lo => Some (Z.div lo m) | None => None end,
                      match snd b with Some hi => Some (Z.div hi m) | None => None end) in
           let q := vs_next A1 in
           let A2 := set_next (set_store A1 (store_set_box (vs_store A1) q bq)) (Pos.succ q) in
           (* [comment removed for export] *)
           let '(ok1, A3) := aassume A2 (lsub (lterm m q) x) in
           let '(ok2, A4) := aassume A3 (laddc (lsub x (lterm m q)) (- (m - 1))) in
           if ok1 && ok2 then Some (lsym q, mkVS2 A4 (vs_rgn A) (vs_live A) (pm_set q (x, m) (vs_divdef A)) (vs_memo A))
           else None
       end.

Definition fdiv8 (A : vstate2) (x : lin) : option (lin * vstate2) := fdivm A x 8.

(* [comment removed for export] *)
Definition split_base (A : vstate2) (e : lin) : option (sym * sym * lin) :=
  match List.filter (fun s => match comp A s with Some _ => true | None => false end) (lsyms e) with
  | [B] => if Z.eqb (lcoef e B) 1 then
             match comp A B with
             | Some B8 => Some (B, B8, lsub e (lsym B))
             | None => None
             end
           else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition x_srl3 (A : vstate2) (rd rs1 : Z) : option vresult2 :=
  match get_reg2 A rs1 with
  | None => None
  | Some ea =>
      match split_base A ea with
      | Some (B, B8, e) =>
          match base_res8 A B with
          | None => None
          | Some rB =>
              if negb (inU (v1 A) ea) then None else
              match fdiv8 A (anorm (v1 A) (laddc e rB)) with
              | Some (q, A1) => Some (one2 (finish2 A1 rd (Some (anorm (v1 A1) (ladd (lsym B8) q)))))
              | None => Some (VR2_fail "srl3: floor division infeasible")
              end
          end
      | None =>
          if has_base A ea || lin_is_const ea || negb (inU (v1 A) ea) then None else
          match lp_bounds (vs_store (v1 A)) ea with
          | (Some lo, Some hi) =>
              if Z.ltb (2 ^ 20) (hi - lo) then None else
              match fdiv8 A (anorm (v1 A) ea) with
              | Some (q, A1) => Some (one2 (finish2 A1 rd (Some q)))
              | None => Some (VR2_fail "srl3: floor division infeasible")
              end
          | _ => None
          end
      end
  end.

(* [comment removed for export] *)
Definition x_and7 (A : vstate2) (rd rs1 : Z) : option vresult2 :=
  match get_reg2 A rs1 with
  | None => None
  | Some ea =>
      match split_base A ea with
      | None => None
      | Some (B, B8, e) =>
          match base_res8 A B with
          | None => None
          | Some rB =>
              let x := anorm (v1 A) (laddc e rB) in
              if lin_is_const x then None else
              let '(m, _) := lin_cong (scong (vs_store (v1 A))) x in
              if negb (Z.eqb m 0) && Z.eqb (m mod 8) 0 then None else
              if negb (inU (v1 A) ea) then None else
              match fdiv8 A x with
              | Some (q, A1) => Some (one2 (finish2 A1 rd (Some (anorm (v1 A1) (lsub x (lscale 8 q))))))
              | None => Some (VR2_fail "and7: floor division infeasible")
              end
          end
      end
  end.

(* [comment removed for export] *)
Definition magic_ok (c k d lo : Z) (n : nat) : bool :=
  forallb (fun v => Z.eqb (Z.shiftr (c * v) k) (Z.div v d)) (zrange lo n).

Definition x_srl_magic (A : vstate2) (rd rs1 : Z) (k : Z) : option vresult2 :=
  match get_reg2 A rs1 with
  | None => None
  | Some ea =>
      if negb (Z.eqb (lc ea) 0) || has_base A ea || negb (inU (v1 A) ea) then None else
      match lin_single ea with
      | None => None
      | Some (x, c) =>
          if Z.leb c 1 then None else
          match lp_bounds (vs_store (v1 A)) (lsym x) with
          | (Some lo, Some hi) =>
              if Z.ltb lo 0 || Z.ltb 4096 (hi - lo) || Z.leb (2 ^ 40) hi || Z.ltb hi lo then None else
              let d := Z.div (2 ^ k + Z.div c 2) c in
              if Z.leb d 1 then None else   (* [comment removed for export] *)
              if negb (magic_ok c k d lo (S (Z.to_nat (hi - lo)))) then None else
              match fdivm A (lsym x) d with
              | Some (q, A1) => Some (one2 (finish2 A1 rd (Some q)))
              | None => Some (VR2_fail "srl magic: floor division infeasible")
              end
          | _ => None
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint terms_divm (l : list term) (m : Z) : list term :=
  match l with
  | [] => []
  | (s, c) :: t => if Z.eqb (Z.div c m) 0 then terms_divm t m else (s, Z.div c m) :: terms_divm t m
  end.

Definition split (A1 : vstate) (m : Z) (e : lin) : option (lin * lin) :=
  let qa := lnorm 0 (terms_divm (lt e) m) in
  if lin_is_const qa then None else
  let R := anorm A1 (lsub e (lscale m qa)) in
  match lp_bounds (vs_store A1) R with
  | (Some lo, Some hi) =>
      let j := Z.div lo m in
      if Z.eqb j (Z.div hi m) then Some (anorm A1 (laddc qa j), anorm A1 (laddc R (- (j * m)))) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition x_srl_split (A : vstate2) (rd rs1 : Z) (k : Z) : option vresult2 :=
  let A1 := v1 A in
  match get_reg2 A rs1 with
  | None => None
  | Some ea =>
      if lin_is_const ea || Z.leb k 0 || Z.leb 64 k then None else
      match (if inU A1 ea then split A1 (2 ^ k) ea else None) with
      | Some (q, _) => Some (one2 (finish2 A rd (Some q)))
      | None =>
          if negb (ldivisible ea (2 ^ k)) then None else
          let q := lshiftr ea k in
          let m' := 2 ^ (64 - k) in
          if lin_is_const q then None else
          let b := lp_bounds (vs_store A1) q in
          if itv_empty b then None else
          let window := match b with
                        | (Some lo, Some hi) => Z.eqb (fdiv lo m') (fdiv hi m')
                        | _ => false
                        end in
          if window then None else
          match split A1 m' q with
          | Some (_, r) => Some (one2 (finish2 A rd (Some r)))
          | None => None
          end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition globs_in_fcells (P : vparams2) (A : vstate2) : bool :=
  negb (asan_mode P)
  || forallb (fun c : Z * cell => match c with (a, (w, _)) => in_cells (vp_fcells (p1 P)) a w end) (vs_globs (v1 A)).

Definition check_globs (P : vparams2) (r : vresult2) : vresult2 :=
  match r with
  | VR2_next l => if forallb (globs_in_fcells P) l then r else VR2_fail "a global cell outside the F-level cells"
  | VR2_fail m => r
  end.

Definition vstep2_raw (P : vparams2) (A : vstate2) (i : instr) : vresult2 :=
  if negb (asan_mode P) then
    match i with
    | Load sz sg rd rs1 imm => x_load2 P A sz sg (rz rd) (rz rs1) (bvs imm)
    | Store sz rs1 rs2 imm => x_store2 P A sz (rz rs1) (rz rs2) (bvs imm)
    | _ => lift1 A (vstep (p1 P) (v1 A) i)
    end
  else
  match i with
  | Load sz sg rd rs1 imm => x_load2 P A sz sg (rz rd) (rz rs1) (bvs imm)
  | Store sz rs1 rs2 imm => x_store2 P A sz (rz rs1) (rz rs2) (bvs imm)
  | ShiftImm ALU_SRL rd rs1 sh =>
      if Z.eqb (rz rd) 0 then lift1 A (vstep (p1 P) (v1 A) i) else
      match (if Z.eqb (bv_unsigned sh) 3 then x_srl3 A (rz rd) (rz rs1) else None) with
      | Some r => r
      | None =>
          match x_srl_magic A (rz rd) (rz rs1) (bv_unsigned sh) with
          | Some r => r
          | None =>
              match x_srl_split A (rz rd) (rz rs1) (bv_unsigned sh) with
              | Some r => r
              | None => lift1 A (vstep (p1 P) (v1 A) i)
              end
          end
      end
  | OpImm ALU_AND rd rs1 imm =>
      if negb (Z.eqb (rz rd) 0) && Z.eqb (bvs imm) 7 then
        match x_and7 A (rz rd) (rz rs1) with
        | Some r => r
        | None => lift1 A (vstep (p1 P) (v1 A) i)
        end
      else lift1 A (vstep (p1 P) (v1 A) i)
  | _ => lift1 A (vstep (p1 P) (v1 A) i)
  end.

Definition vstep2 (P : vparams2) (A : vstate2) (i : instr) : vresult2 := check_globs P (vstep2_raw P A i).
