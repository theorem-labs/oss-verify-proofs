(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEntM FxChSubst FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart FxChain FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv FxChBlob FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChBlob OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pbases_below (n : positive) (rgs : list region) : bool :=
  forallb (fun R => forallb (fun '(y, _) => Pos.ltb y n) (l_t (rg_base R) ++ l_t (rg_size R))) rgs.
Lemma pos_below_lt : forall p x, In x (pos_below p) -> (x < p)%positive.
Proof.
  intros p x H. unfold pos_below in H.
  assert (Hq : Pos.to_nat (Pos.pred p) = (Pos.to_nat p - 1)%nat \/ (Pos.to_nat p - 1)%nat = O).
  { destruct (Pos.eq_dec p 1) as [->|Hp]; [right; reflexivity|]. left.
    rewrite Pos2Nat.inj_pred; [lia|]. pose proof (Pos2Nat.is_pos p). apply Pos2Nat.inj_lt. cbn.
    assert (Pos.to_nat p <> 1)%nat by (intros He; apply Hp; apply Pos2Nat.inj; exact He). lia. }
  apply (pos_below_go_In _ _ [] x Hq) in H. destruct H as [H|H]; [destruct H|]. apply Pos2Nat.inj_lt. pose proof (Pos2Nat.is_pos x). lia.
Qed.
Lemma pbases_below_eq : forall n rgs, pbases_below n rgs = bases_ins (pos_below n) rgs.
Proof.
  intros n rgs. unfold pbases_below, bases_ins. induction rgs as [|R rs IH]; [reflexivity|]. cbn [forallb]. rewrite IH. f_equal.
  induction (l_t (rg_base R) ++ l_t (rg_size R)) as [|[y k] t IHt]; [reflexivity|]. cbn [forallb]. rewrite IHt. f_equal.
  apply eq_true_iff_eq. rewrite Pos.ltb_lt, existsb_exists. split.
  - intros H. exists y. split; [apply pos_below_In; exact H | apply Pos.eqb_refl].
  - intros (x & Hin & He). apply Pos.eqb_eq in He. subst x. exact (pos_below_lt _ _ Hin).
Qed.

Section PCheck.
Context {N A : Type}.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable t : tree xi.
Variable img : tree Z.
Variable apost : N -> sst -> smodel -> A -> option (sst * smodel * A).
Variable aeqb : A -> A -> bool.
Variable awf : positive -> A -> bool.
Variable asub : tree lin -> A -> A.
Variable agok : smodel -> A -> bool.
Variable alins : A -> list lin.        (* [comment removed for export] *)
Variable aset : A -> list lin -> A.
(* [comment removed for export] *)
Variable subs : list (sst * smodel * A * list (sst * smodel * A)).
(* [comment removed for export] *)
Variable amod : smodel -> smodel -> A -> bool.
Variable LIMW : Z.

(* [comment removed for export] *)
Definition PFS : fstate := FSDone.
Definition PSH : shp := ShEmit [] 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition keep_fact (nb n : positive) (f : fact) : bool :=
  match f with
  | FRange l _ _ => (lwf n l && Nat.leb (List.length (l_t l)) 2)%bool
  | FMod l _ _ => (lwf n l && true)%bool      (* [comment removed for export] *)
  | _ => false
  end.
(* [comment removed for export] *)
Definition fvars_tree (fs : list fact) : tree unit := List.fold_left (fun t f => List.fold_left (fun t x => tset x tt t) (fact_vars f) t) fs TEmpty.
Fixpoint anyb_k {X} (p : X -> bool) (l : list X) : bool := match l with [] => false | x :: r => if p x then true else anyb_k p r end.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition svars_tree (F' : sst) : tree unit :=
  List.fold_left live_rg (s_rgs F') (List.fold_left tadd_lin (tvals_acc (s_regs F') []) (fvars_tree (s_facts F'))).
Definition keep_sel (nb n : positive) (fsF : list fact) (vs : tree unit) (f : fact) : bool :=
  if keep_fact nb n f
  then (if anyb_k (fun x => match tget x vs with Some _ => true | None => false end) (fact_vars f) then negb (anyb_k (fact_eqb f) fsF) else false)
  else false.
Definition use_keep (nb : positive) (S F' : sst) : sst :=
  SST (s_pc F') (s_regs F') (s_rgs F')
      (s_facts F' ++ List.filter (keep_sel nb (s_next S) (s_facts F') (svars_tree F')) (s_facts S)) (s_next F') (s_resv F').

(* [comment removed for export] *)
Definition PSR_KEYS : list positive := [48%positive; 49%positive].
Definition psr_ext (S T : sst) (σ : tree lin) : tree lin :=
  List.fold_left (fun σ k => match tget k (s_regs T) with
                             | Some (LIN 0 [(v, 1)]) => match tget v σ with
                                                        | None => match tget k (s_regs S) with Some l => tset v l σ | None => σ end
                                                        | Some _ => σ end
                             | _ => σ end) PSR_KEYS σ.

Fixpoint pchecku (ch : @mchain N) (S : sst) (M : smodel) (a : A) : option (list (sst * smodel * A)) :=
  match ch with
  | MEnd => Some [(S, M, a)]
  | MSegK depth p ks =>
      if pbases_below (s_next S) (s_rgs S) then
        match checkB t img (s_next S) depth p S with
        | Some Ls => all_some (fun L => if (sm_wf (s_next L) M && Pos.leb (s_next S) (s_next L))%bool then pfindu ks L M a else None) Ls
        | None => None
        end
      else None
  | MCall nk k =>
      match apost nk S M a with
      | Some (S', M', a') =>
          if (Pos.leb (s_next S) (s_next S') && frz_eqb (sm_frz M') (sm_frz M) && awf (s_next S') a')%bool then pchecku k S' M' a' else None
      | None => None
      end
  | MVoid => if fx_contra (s_facts S) then Some [] else None
  | MAlt k1 k2 => if is_mvoid k1 then (if fx_contra1 (s_facts S) then Some [] else pchecku k2 S M a)      (* [comment removed for export] *)
                 else match pchecku k1 S M a with Some f => Some f | None => pchecku k2 S M a end
  | MSep op k => match sep_post segs op S M with Some S' => pchecku k S' M a | None => None end
  | MSplit l c ka kb =>
      if lwf (s_next S) l then
        let r := irange (s_facts S) l in
        match (if Z.leb (fst r) c then pchecku ka (add_fact S (FRange l (fst (irange (s_facts S) l)) (Z.min c (snd (irange (s_facts S) l))))) M a else Some []),
              (if Z.ltb c (snd r) then pchecku kb (add_fact S (FRange l (Z.max (c + 1) (fst (irange (s_facts S) l))) (snd (irange (s_facts S) l)))) M a else Some []) with
        | Some f1, Some f2 => Some (f1 ++ f2)
        | _, _ => None
        end
      else None
  | MSplitB l k r0 ka kb =>
      if (lwf (s_next S) l && Z.leb 0 k && Z.ltb k 64 && (Z.eqb k 0 && Z.eqb r0 0 || match lowb (s_facts S) l k with Some r => Z.eqb r r0 | None => false end))%bool then
        match pchecku ka (add_fact S (FMod l (k + 1) r0)) M a, pchecku kb (add_fact S (FMod l (k + 1) (r0 + 2 ^ k))) M a with
        | Some f1, Some f2 => Some (f1 ++ f2)
        | _, _ => None
        end
      else None
  | MSplitG j c ka kb =>
      match nth_error (sm_maps M) j with
      | Some g =>
          let l := fst (fst g) in
          if lwf (s_next S) l then
            let r := irange (s_facts S) l in
            match (if Z.leb (fst r) c then pchecku ka (add_fact S (FRange l (fst (irange (s_facts S) l)) (Z.min c (snd (irange (s_facts S) l))))) M a else Some []),
                  (if Z.ltb c (snd r) then pchecku kb (add_fact S (FRange l (Z.max (c + 1) (fst (irange (s_facts S) l))) (snd (irange (s_facts S) l)))) M a else Some []) with
            | Some f1, Some f2 => Some (f1 ++ f2)
            | _, _ => None
            end
          else None
      | None => None
      end
  | MSplitR r c ka kb =>
      let l := rget (s_regs S) (Z.to_pos (r + 1)) in
      if lwf (s_next S) l then
        let r := irange (s_facts S) l in
        match (if Z.leb (fst r) c then pchecku ka (add_fact S (FRange l (fst (irange (s_facts S) l)) (Z.min c (snd (irange (s_facts S) l))))) M a else Some []),
              (if Z.ltb c (snd r) then pchecku kb (add_fact S (FRange l (Z.max (c + 1) (fst (irange (s_facts S) l))) (snd (irange (s_facts S) l)))) M a else Some []) with
        | Some f1, Some f2 => Some (f1 ++ f2)
        | _, _ => None
        end
      else None
  | MConcR k => pchecku k (concr S) M a
  | MGc nk xs k => pchecku k (gc_post nk xs S M PFS PSH) M a
  | MJoin body jpc k =>
      match pchecku body S M a with
      | Some fb =>
          let J := List.filter (fun '(F, _, _) => Z.eqb (s_pc F) jpc) fb in
          let O := List.filter (fun '(F, _, _) => negb (Z.eqb (s_pc F) jpc)) fb in
          match J with
          | [] => Some O
          | (F0, M0, a0) :: Jr =>
              let n0 := max_next (List.map (fun '(F, _, _) => F) Jr) (s_next F0) in
              let P := fst (gen2 F0 (List.map (fun '(F, _, _) => F) Jr)) in
              if (forallb (fun '(F, MF, aF) => ent_ok n0 F P MF && Pos.leb (s_next F) n0 && sm_eqb MF M0 && aeqb aF a0) J &&
                  Pos.leb (s_next S) n0 && awf n0 a0)%bool
              then match pchecku k P M0 a0 with Some fk => Some (fk ++ O) | None => None end
              else None
          end
      | None => None
      end
  | MJoinL body jpc k =>
      match pchecku body S M a with
      | Some fb =>
          let J := List.filter (fun '(F, _, _) => Z.eqb (s_pc F) jpc) fb in
          let O := List.filter (fun '(F, _, _) => negb (Z.eqb (s_pc F) jpc)) fb in
          match J with
          | [] => Some O
          | (F0, M0, a0) :: Jr =>
              let n0 := max_next (List.map (fun '(F, _, _) => F) Jr) (s_next F0) in
              match genL (List.map (fun '(F, MF, _) => (F, MF)) J) with
              | Some (P, MP) =>
                  if (forallb (fun '(F, MF, aF) => let σ := matchL F MF P MP in
                                 entails F P σ && fixed_below σ n0 && Pos.leb (s_next F) n0 &&
                                 sm_eqbm σ MP MF && aeqb (asub σ a0) aF) J &&
                      state_wf P && sm_wf (s_next P) MP && Pos.leb n0 (s_next P) && agok MP a0 &&
                      Pos.leb (s_next S) n0 && awf n0 a0)%bool
                  then match pchecku k P MP a0 with Some fk => Some (fk ++ O) | None => None end
                  else None
              | None => None
              end
          end
      | None => None
      end
  | MJoinG gen body jpc k =>    (* [comment removed for export] *)
      match pchecku body S M a with
      | Some fb =>
          let J := List.filter (fun '(F, _, _) => Z.eqb (s_pc F) jpc) fb in
          let O := List.filter (fun '(F, _, _) => negb (Z.eqb (s_pc F) jpc)) fb in
          match J with
          | [] => Some O
          | (F0, M0, a0) :: Jr =>
              let n0 := max_next (List.map (fun '(F, _, _) => F) Jr) (s_next F0) in
              match gen (List.map (fun '(F, MF, _) => (F, MF)) J) (List.map (fun '(_, _, aF) => alins aF) J) with
              | Some (P, MP, als) =>
                  let aP := aset a0 als in
                  if (forallb (fun '(F, MF, aF) => let σ := matchLA F MF (alins aF) P MP (alins aP) in
                                 entails F P σ && fixed_below σ n0 && Pos.leb (s_next F) n0 &&
                                 sm_eqbm σ MP MF && aeqb (asub σ aP) aF) J &&
                      state_wf P && sm_wf (s_next P) MP && Pos.leb n0 (s_next P) && agok MP aP &&
                      Pos.leb (s_next S) n0 && awf (s_next P) aP)%bool
                  then match pchecku k P MP aP with Some fk => Some (fk ++ O) | None => None end
                  else None
              | None => None
              end
          end
      | None => None
      end
  | MWeaken P n0 _ _ k =>      (* [comment removed for export] *)
      if (ent_ok n0 S P M && Pos.leb (s_next S) n0 && awf n0 a)%bool then pchecku k P M a else None
  | MLoopG gen body ks =>
      match pchecku body S M a with
      | Some fb1 =>
          match List.find (fun '(F, _, _) => Z.eqb (s_pc F) (s_pc S)) fb1 with
          | Some (F1, _, _) =>
              match gen S F1 PFS PFS PSH PSH with
              | Some (P, n0, _, _, meas) =>
                  if (ent_ok n0 S P M && Pos.leb (s_next S) n0 && lwf (s_next P) meas && meas_ok (s_facts P) meas && awf n0 a)%bool then
                    match pchecku body P M a with
                    | Some fb => all_some (fun '(F, MF, aF) =>
                                   if Z.eqb (s_pc F) (s_pc P) then
                                     if (ent_ok n0 F P MF && sm_eqb MF M && aeqb aF a && lmeas_dec F (match_st F P) meas)%bool then Some [] else None
                                   else if Pos.leb n0 (s_next F) then pfindu ks F MF aF else None) fb
                    | None => None
                    end
                  else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | MUse j nb k =>      (* [comment removed for export] *)
      match nth_error subs j with
      | Some (T, MT, aT, fins) =>
          let σ := psr_ext S T (matchLA S M (alins a) T MT (alins aT)) in
          if (entails S T σ && state_wf T && sm_wf (s_next T) MT && agok MT aT && sm_eqbm σ MT M && aeqb (asub σ aT) a &&
              Pos.leb nb (s_next T) && Pos.leb nb (s_next S) && fixed_below σ nb && use_bwf σ nb (s_next T) (s_next S) &&
              awf (s_next T) aT)%bool then
            all_some (fun '(F, MF, aF) =>
              let σ' := use_sig σ nb (s_next T) (s_next F) (s_next S) in
              let nx := use_next nb (s_next F) (s_next S) in
              if (Pos.leb (s_next T) (s_next F) && awf nx (asub σ' aF) && marks_ok σ' (sm_maps MF))%bool
              then pchecku k (use_keep nb S (ssubst σ' nx F)) (msubst σ' MF) (asub σ' aF) else None) fins
          else None
      | None => None
      end
  | MAllowW j z k =>      (* [comment removed for export] *)
      let M' := with_allow M (widen_nth j z (sm_allow M)) in
      if (widen_ok LIMW S M j z && amod M M' a)%bool then pchecku k S M' a else None
  | _ => None
  end
with pfindu (ks : @mks N) (L : sst) (M : smodel) (a : A) : option (list (sst * smodel * A)) :=
  match ks with
  | KNil => Some [(L, M, a)]
  | KCons b sys k r => if (Z.eqb b (s_pc L) && (Z.eqb sys 0 || match a7c L with Some c => Z.eqb c sys | None => false end))%bool
                       then pchecku k L M a else pfindu r L M a
  end.
End PCheck.

(* [comment removed for export] *)
Definition pcheck {N A : Type} (segs : list Segment) (t : tree xi) (img : tree Z) (apost : N -> sst -> smodel -> A -> option (sst * smodel * A))
  (aeqb : A -> A -> bool) (awf : positive -> A -> bool) (asub : tree lin -> A -> A) (agok : smodel -> A -> bool) (alins : A -> list lin)
  (aset : A -> list lin -> A) : @mchain N -> sst -> smodel -> A -> option (list (sst * smodel * A)) :=
  pchecku segs t img apost aeqb awf asub agok alins aset [] (fun _ _ _ => false) 0.
Definition pfind {N A : Type} (segs : list Segment) (t : tree xi) (img : tree Z) (apost : N -> sst -> smodel -> A -> option (sst * smodel * A))
  (aeqb : A -> A -> bool) (awf : positive -> A -> bool) (asub : tree lin -> A -> A) (agok : smodel -> A -> bool) (alins : A -> list lin)
  (aset : A -> list lin -> A) : @mks N -> sst -> smodel -> A -> option (list (sst * smodel * A)) :=
  pfindu segs t img apost aeqb awf asub agok alins aset [] (fun _ _ _ => false) 0.
(* [comment removed for export] *)
