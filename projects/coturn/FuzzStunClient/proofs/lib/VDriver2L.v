(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStep VStepMem VCert VItab VDriverMatch VContract VDriver.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VState2 VStepMem2 VCert2 VContract2 VDriverMatch2 VDriver2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* [comment removed for export] *)
Definition lcut : Type := (vcut2 * list vstate2)%type.

Definition preload_cut (P : vparams2) (c : vcut2) : lcut :=
  (c, map (fun X => load_cstate2 P X (cut2_pc c) (cut2_ctx c)) (cut2_states c)).

Definition preload (P : vparams2) (l : list vcut2) : list lcut := map (preload_cut P) l.

Fixpoint lcuts_by_pc2 (l : list lcut) (m : pmap (list lcut)) : pmap (list lcut) :=
  match l with
  | [] => m
  | cl :: t => let k := zkey (cut2_pc (fst cl)) in
               let old := match pm_get k m with Some l' => l' | None => [] end in
               lcuts_by_pc2 t (pm_set k (old ++ [cl])%list m)
  end.

Definition find_cut2_l (LT : pmap (list lcut)) (pc : Z) (ctx : list Z) : option lcut :=
  if negb (Z.ltb 0 pc) then None else
  match pm_get (zkey pc) LT with
  | None => None
  | Some l => find (fun cl : lcut => Z.eqb (cut2_pc (fst cl)) pc && list_Z_eqb (cut2_ctx (fst cl)) ctx) l
  end.

Fixpoint pick3 (ls : list vstate2) (rks : list lin) (i : Z) : option (vstate2 * lin) :=
  match ls, rks with
  | St :: t, r :: rt => if Z.eqb i 0 then Some (St, r) else pick3 t rt (Z.pred i)
  | _, _ => None
  end.

Definition try_hint2_l (D : denv2) (Rstart : lin) (A : vstate2) (cl : lcut) (h : Z) : bool :=
  match pick3 (snd cl) (cut2_ranks (fst cl)) h with
  | Some (St, r) =>
      match match_state2 isv_join2 no_skip false MM_cut pm_empty St A with
      | MOk sigma => if ge2_ranks (de2_G D) then qge (v1 A) (lsub Rstart (lsubst sigma r)) 1 else false
      | MFail _ => false
      end
  | None => false
  end.

Definition cut_arrival2h_l (D : denv2) (Rstart : lin) (A : vstate2) (cl : lcut) (tape : list Z) : sres2 :=
  match tape with
  | h :: _ => if try_hint2_l D Rstart A cl h then SN2 [] else cut_arrival2 D Rstart A (fst cl)
  | [] => cut_arrival2 D Rstart A (fst cl)
  end.

Fixpoint explore2_l (D : denv2) (LT : pmap (list lcut)) (fuel : nat) (origin : string) (Rstart : lin)
         (work : list (bool * vstate2)) (tape : list Z) : res2 :=
  match fuel with
  | O => match work with
         | (_, A) :: _ => R2Fail (u_vid (u1 (de2_U D))) origin A "out of fuel"
         | [] => R2Ok
         end
  | S f =>
      match work with
      | [] => R2Ok
      | (first, A) :: rest =>
          let atcut := if first then None else find_cut2_l LT (vs2_pc A) (vs_ctx (v1 A)) in
          match atcut with
          | Some cl =>
              match cut_arrival2h_l D Rstart A cl tape with
              | SN2 _ => explore2_l D LT f origin Rstart rest (tl tape)
              | SF2 m => R2Fail (u_vid (u1 (de2_U D))) origin A m
              end
          | None =>
              match dstep2 D A with
              | SN2 succs => explore2_l D LT f origin Rstart (map (fun A' => (false, A')) succs ++ rest)%list tape
              | SF2 m => R2Fail (u_vid (u1 (de2_U D))) origin A m
              end
          end
      end
  end.

Definition rank_nonneg2_l (cl : lcut) : bool :=
  forallb (fun sxr : vstate2 * (cstate2 * lin) =>
             qge (v1 (fst sxr)) (snd (snd sxr)) 0 && lin_below (snd (snd sxr)) (cs_next (c1 (fst (snd sxr)))))
          (combine (snd cl) (combine (cut2_states (fst cl)) (cut2_ranks (fst cl)))).

Definition unit_static_ok2_l (G : genv2) (P : vparams2) (U : vunit2) (lc : list lcut) : option string :=
  let V := u1 U in
  if negb (cstate2_ok P (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)) then Some "static: entry state ill-formed" else
  if negb (pre_canonical2 G P U) then Some "static: entry state registers not canonical (ra/sp/s-regs/gp/tp)" else
  if negb (forallb (fun c => pc_ok (cut2_pc c) && forallb (fun cs => cstate2_ok P cs && wrgn_ok U cs) (cut2_states c)) (u2_cuts U)) then Some "static: a cut state is ill-formed" else
  if negb (pc_ok (u_entry V)) then Some "static: entry pc out of range" else
  if negb (forallb (fun cs => cstate2_ok P cs && cstate2_iface_b cs && wrgn_ok U cs) (u2_exits U)) then Some "static: an exit state is ill-formed" else
  if ge2_ranks G && negb (forallb (fun cl : lcut => Nat.eqb (length (cut2_ranks (fst cl))) (length (cut2_states (fst cl))) && rank_nonneg2_l cl) lc)
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

Fixpoint check_cut_states2_l (D : denv2) (LT : pmap (list lcut)) (fuel : nat) (lsts : list vstate2) (rks : list lin)
         (tps : list (list Z)) : res2 :=
  match lsts with
  | [] => R2Ok
  | St :: t =>
      let R := match rks with r :: _ => r | [] => RANK_TOP end in
      let rks' := match rks with _ :: r' => r' | [] => [] end in
      let T := match tps with p :: _ => p | [] => [] end in
      let tps' := match tps with _ :: p' => p' | [] => [] end in
      match explore2_l D LT fuel "cut" R [(true, St)] T with
      | R2Ok => check_cut_states2_l D LT fuel t rks' tps'
      | r => r
      end
  end.

Fixpoint check_cuts2_l (D : denv2) (LT : pmap (list lcut)) (fuel : nat) (l : list lcut) : res2 :=
  match l with
  | [] => R2Ok
  | cl :: t => match check_cut_states2_l D LT fuel (snd cl) (cut2_ranks (fst cl)) (cut2_tapes (fst cl)) with
               | R2Ok => check_cuts2_l D LT fuel t
               | r => r
               end
  end.

Definition check_unit2_l (G : genv2) (done : list vunit2) (U : vunit2) : res2 :=
  let D := mk_denv2 G done U in
  let lc := preload (de2_P D) (u2_cuts U) in
  let LT := lcuts_by_pc2 lc pm_empty in
  let S0 := load_cstate2 (de2_P D) (u2_pre U) (u_entry (u1 U)) [] in
  match unit_static_ok2_l G (de2_P D) U lc with
  | Some m => R2Fail (u_vid (u1 U)) "static" S0 m
  | None =>
      let fuel := N.to_nat (u_fuel (u1 U)) in
      match explore2_l D LT fuel "entry" RANK_TOP [(true, S0)] (u2_tape U) with
      | R2Ok => check_cuts2_l D LT fuel lc
      | r => r
      end
  end.

Fixpoint check_units2_l (G : genv2) (done : list vunit2) (l : list vunit2) : res2 :=
  match l with
  | [] => R2Ok
  | U :: t => match check_unit2_l G done U with
              | R2Ok => check_units2_l G (done ++ [U])%list t
              | r => r
              end
  end.

Fixpoint check_chunks2b_l (G : genv2) (done : list vunit2) (chunks : list (list vunit2)) : bool :=
  match chunks with
  | [] => true
  | c :: t => match check_units2_l G done c with
              | R2Ok => check_chunks2b_l G (done ++ c)%list t
              | _ => false
              end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Eq.
  Variable P : vparams2.
  Let f := preload_cut P.

  Lemma fst_preload_cut c : fst (f c) = c.
  Proof. reflexivity. Qed.

  Lemma lcuts_rel : forall (l : list vcut2) (m : pmap (list vcut2)) (ml : pmap (list lcut)),
    (forall k, pm_get k ml = option_map (map f) (pm_get k m)) ->
    forall k, pm_get k (lcuts_by_pc2 (preload P l) ml) = option_map (map f) (pm_get k (cuts_by_pc2 l m)).
  Proof.
    induction l as [|c t IH]; intros m ml R k; cbn [preload map lcuts_by_pc2 cuts_by_pc2]; [apply R|].
    apply IH. intros k0. cbn [fst preload_cut]. fold f.
    rewrite !pm_get_set. destruct (Pos.eqb k0 (zkey (cut2_pc c))); [|apply R].
    cbn [option_map]. rewrite (R (zkey (cut2_pc c))).
    destruct (pm_get (zkey (cut2_pc c)) m) as [old|]; cbn [option_map]; rewrite ?map_app; reflexivity.
  Qed.

  Lemma find_map_fst (p : vcut2 -> bool) (l : list vcut2) :
    find (fun cl : lcut => p (fst cl)) (map f l) = option_map f (find p l).
  Proof.
    induction l as [|c t IH]; cbn [map find]; [reflexivity|]. cbn [fst f preload_cut].
    destruct (p c); [reflexivity|exact IH].
  Qed.

  Lemma pick3_map (c : vcut2) : forall (sts : list cstate2) (rks : list lin) (i : Z),
    pick3 (map (fun X => load_cstate2 P X (cut2_pc c) (cut2_ctx c)) sts) rks i
    = option_map (fun xr : cstate2 * lin => (load_cstate2 P (fst xr) (cut2_pc c) (cut2_ctx c), snd xr)) (pick2 sts rks i).
  Proof.
    induction sts as [|X t IH]; intros rks i; cbn [map pick3 pick2]; [reflexivity|].
    destruct rks as [|r rt]; [reflexivity|]. destruct (Z.eqb i 0); [reflexivity|apply IH].
  Qed.
End Eq.

Lemma try_hint2_l_eq D Rstart A c h :
  try_hint2_l D Rstart A (preload_cut (de2_P D) c) h = try_hint2 D Rstart A c h.
Proof.
  unfold try_hint2_l, try_hint2. cbn [fst snd preload_cut]. rewrite pick3_map.
  destruct (pick2 (cut2_states c) (cut2_ranks c) h) as [[X r]|]; reflexivity.
Qed.

Lemma cut_arrival2h_l_eq D Rstart A c tape :
  cut_arrival2h_l D Rstart A (preload_cut (de2_P D) c) tape = cut_arrival2h D Rstart A c tape.
Proof.
  unfold cut_arrival2h_l, cut_arrival2h. destruct tape as [|h t]; [reflexivity|].
  rewrite try_hint2_l_eq. reflexivity.
Qed.

Definition lt_rel (D : denv2) (LT : pmap (list lcut)) : Prop :=
  forall k, pm_get k LT = option_map (map (preload_cut (de2_P D))) (pm_get k (de2_cuts D)).

Lemma find_cut2_l_eq D LT pc ctx : lt_rel D LT ->
  find_cut2_l LT pc ctx = option_map (preload_cut (de2_P D)) (find_cut2 D pc ctx).
Proof.
  intros R. unfold find_cut2_l, find_cut2. destruct (negb (Z.ltb 0 pc)); [reflexivity|].
  rewrite (R (zkey pc)). destruct (pm_get (zkey pc) (de2_cuts D)) as [l|]; cbn [option_map]; [|reflexivity].
  exact (find_map_fst (de2_P D) (fun c => Z.eqb (cut2_pc c) pc && list_Z_eqb (cut2_ctx c) ctx) l).
Qed.

Lemma explore2_l_eq D LT : lt_rel D LT -> forall fuel origin Rstart work tape,
  explore2_l D LT fuel origin Rstart work tape = explore2 D fuel origin Rstart work tape.
Proof.
  intros R. induction fuel as [|fu IH]; intros origin Rstart work tape; cbn [explore2_l explore2]; [reflexivity|].
  destruct work as [|[first A] rest]; [reflexivity|].
  destruct first.
  - destruct (dstep2 D A); [apply IH|reflexivity].
  - rewrite (find_cut2_l_eq D LT _ _ R). destruct (find_cut2 D (vs2_pc A) (vs_ctx (v1 A))) as [c|]; cbn [option_map].
    + rewrite cut_arrival2h_l_eq. destruct (cut_arrival2h D Rstart A c tape); [apply IH|reflexivity].
    + destruct (dstep2 D A); [apply IH|reflexivity].
Qed.

Lemma check_cut_states2_l_eq D LT fuel c : lt_rel D LT -> forall sts rks tps,
  check_cut_states2_l D LT fuel (map (fun X => load_cstate2 (de2_P D) X (cut2_pc c) (cut2_ctx c)) sts) rks tps
  = check_cut_states2 D fuel c sts rks tps.
Proof.
  intros R. induction sts as [|X t IH]; intros rks tps; cbn [map check_cut_states2_l check_cut_states2]; [reflexivity|].
  rewrite (explore2_l_eq D LT R).
  destruct (explore2 D fuel "cut" match rks with r :: _ => r | [] => RANK_TOP end
              [(true, load_cstate2 (de2_P D) X (cut2_pc c) (cut2_ctx c))] match tps with p :: _ => p | [] => [] end);
    [apply IH|reflexivity].
Qed.

Lemma check_cuts2_l_eq D LT fuel : lt_rel D LT -> forall l,
  check_cuts2_l D LT fuel (preload (de2_P D) l) = check_cuts2 D fuel l.
Proof.
  intros R. induction l as [|c t IH]; cbn [preload map check_cuts2_l check_cuts2]; [reflexivity|].
  cbn [fst snd preload_cut]. rewrite (check_cut_states2_l_eq D LT fuel c R).
  destruct (check_cut_states2 D fuel c (cut2_states c) (cut2_ranks c) (cut2_tapes c)); [exact IH|reflexivity].
Qed.

Lemma rank_nonneg2_l_eq P c : rank_nonneg2_l (preload_cut P c) = rank_nonneg2 P c.
Proof.
  unfold rank_nonneg2_l, rank_nonneg2. cbn [fst snd preload_cut].
  generalize (cut2_ranks c). induction (cut2_states c) as [|X t IH]; intros rks; [reflexivity|].
  destruct rks as [|r rt]; [reflexivity|]. cbn [map combine forallb fst snd]. rewrite IH. reflexivity.
Qed.

Lemma unit_static_ok2_l_eq G P U : unit_static_ok2_l G P U (preload P (u2_cuts U)) = unit_static_ok2 G P U.
Proof.
  unfold unit_static_ok2_l, unit_static_ok2.
  replace (forallb (fun cl : lcut => Nat.eqb (length (cut2_ranks (fst cl))) (length (cut2_states (fst cl))) && rank_nonneg2_l cl) (preload P (u2_cuts U)))
    with (forallb (fun c => Nat.eqb (length (cut2_ranks c)) (length (cut2_states c)) && rank_nonneg2 P c) (u2_cuts U)); [reflexivity|].
  unfold preload. induction (u2_cuts U) as [|c t IH]; [reflexivity|]. cbn [map forallb].
  rewrite rank_nonneg2_l_eq. cbn [fst preload_cut]. rewrite IH. reflexivity.
Qed.

Lemma check_unit2_l_eq G done U : check_unit2_l G done U = check_unit2 G done U.
Proof.
  unfold check_unit2_l, check_unit2. cbv zeta.
  assert (R : lt_rel (mk_denv2 G done U) (lcuts_by_pc2 (preload (de2_P (mk_denv2 G done U)) (u2_cuts U)) pm_empty)).
  { intros k. unfold mk_denv2 at 3. cbn [de2_cuts].
    apply (lcuts_rel (de2_P (mk_denv2 G done U)) (u2_cuts U) pm_empty pm_empty). intros k0. rewrite !pm_get_empty. reflexivity. }
  rewrite unit_static_ok2_l_eq.
  destruct (unit_static_ok2 G (de2_P (mk_denv2 G done U)) U); [reflexivity|].
  rewrite (explore2_l_eq _ _ R).
  destruct (explore2 (mk_denv2 G done U) (N.to_nat (u_fuel (u1 U))) "entry" RANK_TOP
              [(true, load_cstate2 (de2_P (mk_denv2 G done U)) (u2_pre U) (u_entry (u1 U)) [])] (u2_tape U)); [|reflexivity].
  apply (check_cuts2_l_eq _ _ _ R).
Qed.

Lemma check_units2_l_eq G : forall l done, check_units2_l G done l = check_units2 G done l.
Proof.
  induction l as [|U t IH]; intros done; cbn [check_units2_l check_units2]; [reflexivity|].
  rewrite check_unit2_l_eq. destruct (check_unit2 G done U); [apply IH|reflexivity].
Qed.

Theorem check_chunks2b_l_eq G : forall chunks done, check_chunks2b_l G done chunks = check_chunks2b G done chunks.
Proof.
  induction chunks as [|c t IH]; intros done; cbn [check_chunks2b_l check_chunks2b]; [reflexivity|].
  rewrite check_units2_l_eq. destruct (check_units2 G done c); [apply IH|reflexivity].
Qed.
