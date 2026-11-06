(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStepMem VCert VDriverMatch VState2 VStepMem2 VCert2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive mmode : Type := MM_cut | MM_call.

(* [comment removed for export] *)
Definition isv_join2 (s : sym) : bool := Pos.leb FIRST_FRESH2 s.
Definition isv_call2 (s : sym) : bool :=
  negb (Pos.eqb s SP0 || Pos.eqb s DATA || Pos.eqb s SIZE || Pos.eqb s TP || Pos.eqb s GP
        || Pos.eqb s SP8 || Pos.eqb s DATA8 || Pos.eqb s FSB || Pos.eqb s FS8).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bind_sym (isv : sym -> bool) (sigma : pmap lin) (s s' : sym) : option (pmap lin) :=
  match pm_get s sigma with
  | Some e => if lin_eqb e (lsym s') then Some sigma else None
  | None => if isv s then Some (pm_set s (lsym s') sigma)
            else if Pos.eqb s s' then Some sigma else None
  end.

(* [comment removed for export] *)
Definition bind_lin (isv : sym -> bool) (sigma : pmap lin) (s : sym) (e : lin) : option (pmap lin) :=
  match pm_get s sigma with
  | Some e' => if lin_eqb e' e then Some sigma else None
  | None => if isv s then Some (pm_set s e sigma)
            else if lin_eqb e (lsym s) then Some sigma else None
  end.

Definition bind_osym (isv : sym -> bool) (sigma : pmap lin) (s s' : option sym) : option (pmap lin) :=
  match s, s' with
  | Some x, Some y => bind_sym isv sigma x y
  | None, _ => Some sigma
  | Some _, None => None
  end.

(* [comment removed for export] *)
Definition resolve_base (isv : sym -> bool) (A : vstate2) (sigma : pmap lin) (b : sym) : option (sym * Z) :=
  match pm_get b sigma with
  | Some e =>
      match List.filter (fun t : sym * Z => negb (Z.eqb (snd t) 0)) (lt e) with
      | [(b', k)] => if Z.eqb k 1 && is_base A b' then Some (b', lc e) else None
      | _ => None
      end
  | None => if negb (isv b) && is_base A b then Some (b, 0) else None
  end.

(* [comment removed for export] *)
Definition bsym_image (isv : sym -> bool) (sigma : pmap lin) (s : sym) : option sym :=
  match pm_get s sigma with
  | Some e => match lin_single e with
              | Some (s', k) => if Z.eqb k 1 && Z.eqb (lc e) 0 then Some s' else None
              | None => None
              end
  | None => if isv s then None else Some s
  end.

(* [comment removed for export] *)
Definition shift_cells (c : Z) (l : cellmap) : cellmap := map (fun e : Z * cell => (fst e + c, snd e)) l.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sh_drop (pm : cellmap) (pos : Z) : cellmap :=
  match pm with
  | [] => []
  | (k, (w, v)) :: t => if Z.leb (k + w) pos then sh_drop t pos else pm
  end.

(* [comment removed for export] *)
Fixpoint sh_run_cover2 (pm : cellmap) (pos stop b : Z) (fuel : nat) : option cellmap :=
  if Z.leb stop pos then Some pm else
  match fuel with
  | O => None
  | S f =>
      match sh_drop pm pos with
      | (k', (w', Some e')) :: t =>
          if lin_is_const e' && Z.eqb (lc e') b && Z.leb k' pos
          then sh_run_cover2 ((k', (w', Some e')) :: t) (k' + w') stop b f
          else None
      | _ => None
      end
  end.

Fixpoint match_sh_cells (isv : sym -> bool) (n : nat) (c : Z) (l : cellmap) (pm : cellmap) (acc : macc) : macc + string :=
  match l with
  | [] => inl acc
  | (k, (w, None)) :: t => match_sh_cells isv n c t pm acc
  | (k, (w, Some e)) :: t =>
      if lin_is_const e then
        match sh_run_cover2 pm (k + c) (k + c + w) (lc e) n with
        | Some pm' => match_sh_cells isv n c t pm' acc
        | None => inr "match: shadow run not covered by equal path runs"
        end
      else
        match sh_drop pm (k + c) with
        | (k', (w', Some e')) :: t' =>
            if Z.eqb k' (k + c) && Z.eqb w w' && Z.eqb w 1 then match_sh_cells isv n c t ((k', (w', Some e')) :: t') (match_loc isv acc e e')
            else inr "match: symbolic shadow cell width/position mismatch"
        | _ => inr "match: symbolic shadow cell absent in path state"
        end
  end.

(* [comment removed for export] *)
Definition sh_fast (pm : cellmap) (pend : option Z) (pos w b : Z) : option cellmap :=
  match pm with
  | (kp, (wp, _)) :: pm1 =>
      match pm1 with
      | (k', (w', Some e')) :: _ =>
          if lin_is_const e' then
            if Z.eqb (lc e') b then
              if Z.ltb 0 w then
                if Z.leb (match pend with Some x => x | None => kp + wp end) pos then
                  if Z.eqb k' pos then (if Z.eqb w' w then Some pm1 else None) else None
                else None
              else None
            else None
          else None
      | _ => None
      end
  | [] => None
  end.

Fixpoint match_sh_cells_h (isv : sym -> bool) (n : nat) (c : Z) (l : cellmap) (pm : cellmap) (pend : option Z) (acc : macc)
  : macc + string :=
  match l with
  | [] => inl acc
  | (k, (w, None)) :: t => match_sh_cells_h isv n c t pm pend acc
  | (k, (w, Some e)) :: t =>
      if lin_is_const e then
        let pos := k + c in
        let stop := pos + w in
        match sh_fast pm pend pos w (lc e) with
        | Some pm1 => match_sh_cells_h isv n c t pm1 (Some stop) acc
        | None =>
            match sh_run_cover2 pm pos stop (lc e) n with
            | Some pm' => match_sh_cells_h isv n c t pm' None acc
            | None => inr "match: shadow run not covered by equal path runs"
            end
        end
      else
        match sh_drop pm (k + c) with
        | (k', (w', Some e')) :: t' =>
            if Z.eqb k' (k + c) && Z.eqb w w' && Z.eqb w 1 then match_sh_cells_h isv n c t ((k', (w', Some e')) :: t') None (match_loc_f isv acc e e')
            else inr "match: symbolic shadow cell width/position mismatch"
        | _ => inr "match: symbolic shadow cell absent in path state"
        end
  end.

(* [comment removed for export] *)
Definition sh_inv (pend : option Z) (pm : cellmap) : Prop :=
  forall x, pend = Some x -> exists kp wp v t, pm = (kp, (wp, v)) :: t /\ kp + wp = x.

Lemma sh_fast_spec pm pend pos w b pm1 f :
  sh_fast pm pend pos w b = Some pm1 -> sh_inv pend pm ->
  sh_run_cover2 pm pos (pos + w) b (S f) = Some pm1 /\ sh_inv (Some (pos + w)) pm1.
Proof.
  unfold sh_fast. destruct pm as [|[kp [wp vp]] pm0]; [discriminate|].
  destruct pm0 as [|[k' [w' [e'|]]] t1]; try discriminate.
  destruct (lin_is_const e') eqn:EC; [|discriminate]. destruct (Z.eqb_spec (lc e') b) as [Eb|]; [|discriminate].
  destruct (Z.ltb_spec 0 w) as [Hw|]; [|discriminate].
  destruct (Z.leb_spec (match pend with Some x => x | None => kp + wp end) pos) as [Hpe|]; [|discriminate].
  destruct (Z.eqb_spec k' pos) as [Ek|]; [|discriminate]. destruct (Z.eqb_spec w' w) as [Ew|]; [|discriminate].
  intros X Inv. injection X as <-. subst k' w'.
  assert (Hend : kp + wp <= pos).
  { destruct pend as [x|]; [|exact Hpe]. destruct (Inv x eq_refl) as (kp0 & wp0 & v0 & t0 & Hc & Hx).
    injection Hc as -> -> _ _. lia. }
  split.
  - cbn [sh_run_cover2]. destruct (Z.leb_spec (pos + w) pos); [lia|].
    cbn [sh_drop]. destruct (Z.leb_spec (kp + wp) pos); [|lia]. destruct (Z.leb_spec (pos + w) pos); [lia|].
    rewrite EC, Eb, Z.eqb_refl, Z.leb_refl. cbn [andb].
    destruct f as [|f']; cbn [sh_run_cover2]; rewrite Z.leb_refl; reflexivity.
  - intros x Hx. injection Hx as <-. exists pos, w, (Some e'), t1. split; reflexivity.
Qed.

Lemma match_sh_cells_h_eq isv n c : n <> O -> forall l pm pend acc,
  sh_inv pend pm ->
  match_sh_cells_h isv n c l pm pend acc = match_sh_cells isv n c l pm acc.
Proof.
  intros Hn. destruct n as [|f]; [congruence|].
  assert (InvN : forall m, sh_inv None m) by (intros m x X; discriminate).
  induction l as [|[k [w [e|]]] t IH]; intros pm pend acc Inv; cbn [match_sh_cells_h match_sh_cells]; [reflexivity| |now apply IH].
  destruct (lin_is_const e).
  - cbv zeta. destruct (sh_fast pm pend (k + c) w (lc e)) as [pm1|] eqn:F.
    + destruct (sh_fast_spec _ _ _ _ _ _ f F Inv) as (HR & Inv1). rewrite HR. apply IH. exact Inv1.
    + destruct (sh_run_cover2 pm (k + c) (k + c + w) (lc e) (S f)) as [pm'|]; [|reflexivity]. apply IH. apply InvN.
  - destruct (sh_drop pm (k + c)) as [|[k' [w' [e'|]]] t']; try reflexivity.
    destruct (Z.eqb k' (k + c) && Z.eqb w w' && Z.eqb w 1); [|reflexivity]. rewrite match_loc_f_eq. apply IH. apply InvN.
Qed.

Definition ranges_incl (a b : list (Z * Z)) (c : Z) : bool :=
  forallb (fun r : Z * Z => in_ranges b (fst r + c) (snd r - fst r)) a.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint fakes_of (l : list vregion) : list vregion :=
  match l with
  | [] => []
  | r :: t => match vr_kind r with RK_fake _ _ => r :: fakes_of t | _ => fakes_of t end
  end.

(* [comment removed for export] *)
Definition rnul_incl (ns np : list (Z * Z)) (c : Z) : bool :=
  forallb (fun f : Z * Z => nul_implied np (fst f + c, snd f + c)) ns.

(* [comment removed for export] *)
Definition match_region_cells (isv : sym -> bool) (cs : bool) (exact : bool) (P : vstate2) (sr pr : vregion) (c : Z) (acc : macc)
  : macc + string :=
  if negb (Z.eqb (vr_disp sr) (vr_disp pr)) then inr "match: region displacement differs" else
  if negb (if exact then Z.eqb c 0 && Z.eqb (vr_lo sr) (vr_lo pr) && Z.eqb (vr_hi sr) (vr_hi pr)
           else Z.leb (vr_lo pr) (vr_lo sr + c) && Z.leb (vr_hi sr + c) (vr_hi pr))
  then inr "match: stored region extent does not agree with the path region" else
  if negb (ranges_incl (vr_w sr) (vr_w pr) c) then inr "match: stored region claims more write permission than the path region" else
  if negb (rnul_incl (vr_nul sr) (vr_nul pr) c) then inr "match: a region NUL fact of the stored state is not implied" else
  if is_shadow sr then match_sh_cells_h isv (S (List.length (vr_cells pr))) c (vr_cells sr) (vr_cells pr) None acc
  else match_cells_h isv cs (v1 P) (shift_cells c (vr_cells sr)) (vr_cells pr) (vr_cells pr) None acc.
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint match_fakes (isv : sym -> bool) (cs : bool) (P : vstate2) (ls lp : list vregion) (acc : macc) : macc + string :=
  match ls, lp with
  | [], [] => inl acc
  | sr :: ls', pr :: lp' =>
      match vr_kind sr, vr_kind pr with
      | RK_fake cid fl, RK_fake cid' fl' =>
          if negb (Z.eqb cid cid') then inr "match: fake frame class differs" else
          match bind_sym isv (fst acc) (vr_base sr) (vr_base pr) with
          | None => inr "match: fake frame base not bindable"
          | Some s1 =>
          match bind_sym isv s1 fl fl' with
          | None => inr "match: fake frame flag symbol not bindable"
          | Some s2 =>
          match bind_osym isv s2 (vr_b8 sr) (vr_b8 pr) with
          | None => inr "match: fake frame companion not bindable"
          | Some s3 =>
              match match_region_cells isv cs true P sr pr 0 (s3, snd acc) with
              | inl acc' => match_fakes isv cs P ls' lp' acc'
              | inr m => inr m
              end
          end end end
      | _, _ => inr "match: internal (fakes_of)"
      end
  | _, _ => inr "match: number of live fake frames differs"
  end.

(* [comment removed for export] *)
Fixpoint match_others (isv : sym -> bool) (cs : bool) (mode : mmode) (P : vstate2) (ls : list vregion) (acc : macc) : macc + string :=
  match ls with
  | [] => inl acc
  | sr :: ls' =>
      let next acc' := match_others isv cs mode P ls' acc' in
      match vr_kind sr with
      | RK_fake _ _ => next acc                              (* [comment removed for export] *)
      | RK_fs =>
          match rgn_get (vs_rgn P) FSB with
          | Some pr => match vr_kind pr with
                       | RK_fs => match match_region_cells isv cs true P sr pr 0 acc with
                                  | inl acc' => next acc'
                                  | inr m => inr m
                                  end
                       | _ => inr "match: FSB is not the fs-hints region in path state"
                       end
          | None => inr "match: fs-hints region absent in path state"
          end
      | RK_arg =>
          match resolve_base isv P (fst acc) (vr_base sr) with
          | None => inr "match: arg region base unresolved in path state"
          | Some (b', c) =>
              match rgn_get (vs_rgn P) b' with
              | None => inr "match: internal (arg base region)"
              | Some pr =>
                  match vr_kind pr, mode with
                  | RK_arg, _ | RK_fake _ _, MM_call =>
                      match match_region_cells isv cs false P sr pr c acc with
                      | inl acc' => next acc'
                      | inr m => inr m
                      end
                  | _, _ => inr "match: arg region points into a non-frame region"
                  end
              end
          end
      | RK_flag owner =>
          (* [comment removed for export] *)
          match bsym_image isv (fst acc) owner, bsym_image isv (fst acc) (vr_base sr) with
          | Some owner', Some b' =>
              match rgn_get (vs_rgn P) b' with
              | Some pr => match vr_kind pr with
                           | RK_flag o' => if Pos.eqb o' owner' then
                                             match match_region_cells isv cs true P sr pr 0 acc with
                                             | inl acc' => next acc'
                                             | inr m => inr m
                                             end
                                           else inr "match: flag region owner differs"
                           | _ => inr "match: flag base is not a flag region in path state"
                           end
              | None => inr "match: flag region absent in path state"
              end
          | _, _ => inr "match: flag region symbols unbound"
          end
      | RK_shadow of_ =>
          match (if Pos.eqb of_ SP0 || Pos.eqb of_ DATA then Some (of_, 0)
                 else match resolve_base isv P (fst acc) of_ with
                      | Some (of', c) => if Pos.eqb of' SP0 || Pos.eqb of' DATA || Pos.eqb of' FSB then None else Some (of', c)
                      | None => None
                      end) with
          | None => inr "match: shadow region's app base unresolved"
          | Some (of', c) =>
              if negb (Bool.eqb (Pos.eqb of' DATA) (Pos.eqb of_ DATA)) then inr "match: Data shadow matched against a non-Data shadow" else
              if negb (Z.eqb (c mod 8) 0) then inr "match: shadow of a non-granule-aligned sub-region" else
              match rgn_shadow_of (vs_rgn P) of' with
              | None => inr "match: shadow region absent in path state"
              | Some pr =>
                  match mode with
                  | MM_cut =>
                      (* [comment removed for export] *)
                      match bind_sym isv (fst acc) (vr_base sr) (vr_base pr) with
                      | None => inr "match: shadow base not bindable"
                      | Some s1 =>
                          if negb (Z.eqb c 0) then inr "match: shifted shadow regions at a cut" else
                          match match_region_cells isv cs (negb (Pos.eqb of' SP0)) P sr pr 0 (s1, snd acc) with
                          | inl acc' => next acc'
                          | inr m => inr m
                          end
                      end
                  | MM_call =>
                      (* [comment removed for export] *)
                      match bind_lin isv (fst acc) (vr_base sr) (laddc (lsym (vr_base pr)) (c / 8)) with
                      | None => inr "match: shadow base not bindable to the caller shadow base + shift"
                      | Some s1 =>
                          match match_region_cells isv cs (Pos.eqb of_ DATA) P sr pr (c / 8) (s1, snd acc) with
                          | inl acc' => next acc'
                          | inr m => inr m
                          end
                      end
                  end
              end
          end
      end
  end.

Definition match_regions (isv : sym -> bool) (cs : bool) (mode : mmode) (S P : vstate2) (acc : macc) : macc + string :=
  let fs := fakes_of (vs_rgn S) in
  let fp := fakes_of (vs_rgn P) in
  if negb (bases_distinct (map vr_base fp)) then inr "match: internal: duplicate fake frames in the path state" else
  match (match mode with
         | MM_cut => match_fakes isv cs P fs fp acc
         | MM_call => match fs with [] => inl acc | _ => inr "match: callee PRE with fake frames" end
         end) with
  | inr m => inr m
  | inl acc1 => match_others isv cs mode P (vs_rgn S) acc1
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition match_divdefs (sigma : pmap lin) (S P : vstate2) : bool :=
  forallb (fun qd : positive * (lin * Z) =>
             match qd with (q, (x, m)) =>
             match sym_image sigma q with
             | Some q' => match pm_get q' (vs_divdef P) with
                          | Some (x', m') => Z.eqb m m' && lin_eqb (lsubst sigma x) x'
                          | None => false
                          end
             | None => false
             end end) (pm_elements (vs_divdef S)).

Fixpoint match_live (isv : sym -> bool) (sigma : pmap lin) (ls lp : list sym) : bool :=
  match ls, lp with
  | [], [] => true
  | s :: ls', p :: lp' => match bsym_image isv sigma s with Some s' => Pos.eqb s' p && match_live isv sigma ls' lp' | None => false end
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition match_state_g (isv : sym -> bool) (skip : positive -> bool) (cs : bool) (sigma0 : pmap lin) (S P : vstate) : mres :=
  match_state isv skip cs sigma0 S P.

Lemma match_state_g_eq isv skip cs sigma0 S P : match_state_g isv skip cs sigma0 S P = match_state isv skip cs sigma0 S P.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition con_weaker_in (e : lin) (pc : list lin) : bool :=
  existsb_l (fun p => if terms_eqb (lt e) (lt p) then Z.leb (lc e) (lc p) else false) pc.

Definition cons_entailed_f (SP : store) (sigma : pmap lin) (cs : list lin) : bool :=
  forallb_l (fun c => let e := lsubst sigma c in if con_weaker_in e (scons SP) then true else check_nonpos SP e) cs.

Definition drop_cons (St : store) : store := mkStore (sbox St) [] (scong St).

Definition match_state_f (isv : sym -> bool) (skip : positive -> bool) (cs : bool) (sigma0 : pmap lin) (S P : vstate) : mres :=
  match match_state_g isv skip cs sigma0 (set_store S (drop_cons (vs_store S))) P with
  | MFail m => MFail m
  | MOk sigma =>
      if cons_entailed_f (vs_store P) sigma (scons (vs_store S)) then MOk sigma
      else MFail "match: store facts of the stored state not entailed"
  end.

Definition match_state2 (isv : sym -> bool) (skip : positive -> bool) (cs : bool) (mode : mmode)
           (sigma0 : pmap lin) (S P : vstate2) : mres :=
  match match_regions isv cs mode S P (sigma0, []) with
  | inr m => MFail m
  | inl (sigma1, defer1) =>
      match match_state_f isv skip cs sigma1 (v1 S) (v1 P) with
      | MFail m => MFail m
      | MOk sigma =>
          if negb (check_defer_f sigma defer1) then MFail "match: a region cell's lin does not match under sigma"
          else if negb (match_divdefs sigma S P) then MFail "match: divdef not matched"
          else if negb (match mode with MM_cut => match_live isv sigma (vs_live S) (vs_live P) | MM_call => true end)
               then MFail "match: live fake-frame lists differ"
          else MOk sigma
      end
  end.
