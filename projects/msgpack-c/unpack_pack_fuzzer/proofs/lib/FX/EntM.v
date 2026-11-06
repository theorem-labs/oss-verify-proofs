(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import GapsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan.
Open Scope Z_scope.

Module EntM.
Import GapsM.GapsM.

Definition decide_ltu_m (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match decide_ltu_s fs a b with
  | Some r => Some r
  | None => match bnd_ltu fs a b with Some r => Some r | None => decide_ltu_G G fs a b end
  end.
Lemma decide_ltu_m_eq : forall fs a b, decide_ltu_m (gaps fs) fs a b = decide_ltu fs a b.
Proof. reflexivity. Qed.

Definition decide_eq_s_m (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  if sv_eqb a b then Some true else
  match (match a, b with
         | _, VL y => if weqb y wzero then decide_eq0_b fs a else None
         | VL x, _ => if weqb x wzero then decide_eq0_b fs b else None
         | _, _ => None
         end) with
  | Some r => Some r
  | None =>
  match a, b with
  | VL x, VL y => Some (weqb x y)
  | VP k1 o1, VP k2 o2 =>
      if PrimInt63.eqb k1 k2 then Some (weqb o1 o2)
      else if fact_lookup fs (is_FNe a b) then Some false
      else if fact_lookup fs (is_FEq a b) then Some true
      else None
  | _, _ =>
      if fact_lookup fs (is_FNe a b) then Some false
      else if fact_lookup fs (is_FEq a b) then Some true
      else
        match a, b with
        | VP k o, VL y | VL y, VP k o =>
            match find_range fs k with
            | Some (lo, hi) =>
                if nowrap lo hi o then
                  (let vlo := wadd lo o in let vhi := wadd hi o in
                   if wltu y vlo || wltu vhi y then Some false else None)
                else None
            | None => None
            end
        | _, _ =>
            match decide_ltu_m G fs a b with
            | Some true => Some false
            | _ => match decide_ltu_m G fs b a with Some true => Some false | _ => None end
            end
        end
  end
  end.
Lemma decide_eq_s_m_eq : forall fs a b, decide_eq_s_m (gaps fs) fs a b = decide_eq_s fs a b.
Proof. intros. unfold decide_eq_s_m, decide_eq_s. rewrite !decide_ltu_m_eq. reflexivity. Qed.

Definition decide_eq_m (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match decide_eq_s_m G fs a b with
  | Some r => Some r
  | None =>
      match lin_eq_G G fs a b with
      | Some r => Some r
      | None =>
          match decide_ltu_G G fs a b, decide_ltu_G G fs b a with
          | Some true, _ | _, Some true => Some false
          | Some false, Some false => Some true
          | _, _ => None
          end
      end
  end.
Lemma decide_eq_m_eq : forall fs a b, decide_eq_m (gaps fs) fs a b = decide_eq fs a b.
Proof. intros. unfold decide_eq_m, decide_eq. rewrite decide_eq_s_m_eq. reflexivity. Qed.

Definition decide_lts_m (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match a, b with
  | VL x, VL y => Some (wlts x y)
  | _, _ =>
  if nonneg63 fs a && nonneg63 fs b then decide_ltu_m G fs a b else
  match a, b with
  | VP k1 o1, VP k2 o2 =>
      if PrimInt63.eqb k1 k2 && below63 fs k1 o1 && below63 fs k1 o2 then Some (soff_ltb o1 o2)
      else if fact_lookup fs (is_FSLt a b) then Some true
      else if fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b) then Some false
      else None
  | _, _ =>
      if sv_eqb a b then Some false
      else if fact_lookup fs (is_FSLt a b) then Some true
      else if fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b) then Some false
      else None
  end
  end.
Lemma decide_lts_m_eq : forall fs a b, decide_lts_m (gaps fs) fs a b = decide_lts fs a b.
Proof. intros. unfold decide_lts_m, decide_lts. rewrite decide_ltu_m_eq. reflexivity. Qed.

Definition implied_m (G : list gapc) (fs : list fact) (f : fact) : bool :=
  if existsb (fact_eqb f) fs then true else
  match f with
  | FRange k lo hi => match find_range fs k with
                      | Some (lo', hi') => wleu lo lo' && wleu hi' hi
                      | None => false
                      end
  | FAlign k m => PrimInt63.leb m (find_align fs k)
  | FULt a b => match decide_ltu_m G fs a b with Some true => true | _ => false end
  | FULe a b => match decide_ltu_m G fs b a with Some false => true | _ => false end
  | FEq a b => match decide_eq_m G fs a b with Some true => true | _ => false end
  | FNe a b => match decide_eq_m G fs a b with Some false => true | _ => false end
  | FSLt a b => match decide_lts_m G fs a b with Some true => true | _ => false end
  | FSLe a b => match decide_lts_m G fs b a with Some false => true | _ => false end
  end.
Lemma implied_m_eq : forall fs f, implied_m (gaps fs) fs f = implied fs f.
Proof. intros fs f. destruct f; unfold implied_m, implied; rewrite ?decide_ltu_m_eq, ?decide_eq_m_eq, ?decide_lts_m_eq; reflexivity. Qed.

Definition decide_ltu_mx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match decide_ltu_s fs a b with
  | Some r => Some r
  | None => match bnd_ltu_x IX a b with Some r => Some r | None => decide_ltu_Gx IX G fs a b end
  end.
Definition decide_eq_s_mx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  if sv_eqb a b then Some true else
  match (match a, b with
         | _, VL y => if weqb y wzero then decide_eq0_b fs a else None
         | VL x, _ => if weqb x wzero then decide_eq0_b fs b else None
         | _, _ => None
         end) with
  | Some r => Some r
  | None =>
  match a, b with
  | VL x, VL y => Some (weqb x y)
  | VP k1 o1, VP k2 o2 =>
      if PrimInt63.eqb k1 k2 then Some (weqb o1 o2)
      else if fact_lookup fs (is_FNe a b) then Some false
      else if fact_lookup fs (is_FEq a b) then Some true
      else None
  | _, _ =>
      if fact_lookup fs (is_FNe a b) then Some false
      else if fact_lookup fs (is_FEq a b) then Some true
      else
        match a, b with
        | VP k o, VL y | VL y, VP k o =>
            match find_range fs k with
            | Some (lo, hi) =>
                if nowrap lo hi o then
                  (let vlo := wadd lo o in let vhi := wadd hi o in
                   if wltu y vlo || wltu vhi y then Some false else None)
                else None
            | None => None
            end
        | _, _ =>
            match decide_ltu_mx IX G fs a b with
            | Some true => Some false
            | _ => match decide_ltu_mx IX G fs b a with Some true => Some false | _ => None end
            end
        end
  end
  end.
Definition decide_eq_mx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match decide_eq_s_mx IX G fs a b with
  | Some r => Some r
  | None =>
      match lin_eq_Gx IX G fs a b with
      | Some r => Some r
      | None =>
          match decide_ltu_Gx IX G fs a b, decide_ltu_Gx IX G fs b a with
          | Some true, _ | _, Some true => Some false
          | Some false, Some false => Some true
          | _, _ => None
          end
      end
  end.
Definition decide_lts_mx (IX : fidx) (G : list gapc) (fs : list fact) (a b : sv) : option bool :=
  match a, b with
  | VL x, VL y => Some (wlts x y)
  | _, _ =>
  if nonneg63_x IX a && nonneg63_x IX b then decide_ltu_mx IX G fs a b else
  match a, b with
  | VP k1 o1, VP k2 o2 =>
      if PrimInt63.eqb k1 k2 && below63 fs k1 o1 && below63 fs k1 o2 then Some (soff_ltb o1 o2)
      else if fact_lookup fs (is_FSLt a b) then Some true
      else if fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b) then Some false
      else None
  | _, _ =>
      if sv_eqb a b then Some false
      else if fact_lookup fs (is_FSLt a b) then Some true
      else if fact_lookup fs (is_FSLe b a) || fact_lookup fs (is_FEq a b) then Some false
      else None
  end
  end.
Definition implied_mx (IX : fidx) (G : list gapc) (fs : list fact) (f : fact) : bool :=
  if existsb (fact_eqb f) fs then true else
  match f with
  | FRange k lo hi => match find_range fs k with
                      | Some (lo', hi') => wleu lo lo' && wleu hi' hi
                      | None => false
                      end
  | FAlign k m => PrimInt63.leb m (find_align fs k)
  | FULt a b => match decide_ltu_mx IX G fs a b with Some true => true | _ => false end
  | FULe a b => match decide_ltu_mx IX G fs b a with Some false => true | _ => false end
  | FEq a b => match decide_eq_mx IX G fs a b with Some true => true | _ => false end
  | FNe a b => match decide_eq_mx IX G fs a b with Some false => true | _ => false end
  | FSLt a b => match decide_lts_mx IX G fs a b with Some true => true | _ => false end
  | FSLe a b => match decide_lts_mx IX G fs b a with Some false => true | _ => false end
  end.

Section MxEq.
Variable fs : list fact.
Variable IX : fidx.
Hypothesis HIX : ix_ok fs IX.
Lemma decide_ltu_mx_eq : forall G a b, decide_ltu_mx IX G fs a b = decide_ltu_m G fs a b.
Proof. intros. unfold decide_ltu_mx, decide_ltu_m. rewrite (bnd_ltu_x_eq fs IX HIX), (decide_ltu_Gx_eq fs IX HIX). reflexivity. Qed.
Lemma decide_eq_s_mx_eq : forall G a b, decide_eq_s_mx IX G fs a b = decide_eq_s_m G fs a b.
Proof. intros. unfold decide_eq_s_mx, decide_eq_s_m. rewrite !decide_ltu_mx_eq. reflexivity. Qed.
Lemma decide_eq_mx_eq : forall G a b, decide_eq_mx IX G fs a b = decide_eq_m G fs a b.
Proof. intros. unfold decide_eq_mx, decide_eq_m. rewrite decide_eq_s_mx_eq, (lin_eq_Gx_eq fs IX HIX), !(decide_ltu_Gx_eq fs IX HIX). reflexivity. Qed.
Lemma decide_lts_mx_eq : forall G a b, decide_lts_mx IX G fs a b = decide_lts_m G fs a b.
Proof. intros. unfold decide_lts_mx, decide_lts_m. rewrite !(nonneg63_x_eq fs IX HIX), decide_ltu_mx_eq. reflexivity. Qed.
Lemma implied_mx_eq : forall G f, implied_mx IX G fs f = implied_m G fs f.
Proof. intros G f. destruct f; unfold implied_mx, implied_m; rewrite ?decide_ltu_mx_eq, ?decide_eq_mx_eq, ?decide_lts_mx_eq; reflexivity. Qed.
End MxEq.

Definition tier01 (fs : list fact) (f : fact) : bool :=
  if has_fact f fs then true else implied (rel_facts (fact_vs f) fs) f.
Definition tier32 (G : list gapc) (fs : list fact) (f : fact) : bool :=
  if implied_m G fs f then true else implied (rel_facts1 (fact_vs f) fs) f.
Definition tier32x (IX : fidx) (G : list gapc) (fs : list fact) (f : fact) : bool :=
  if implied_mx IX G fs f then true else implied (rel_facts1 (fact_vs f) fs) f.
Lemma tier32x_eq : forall fs IX G f, ix_ok fs IX -> tier32x IX G fs f = tier32 G fs f.
Proof. intros. unfold tier32x, tier32. rewrite (implied_mx_eq fs IX H). reflexivity. Qed.
Lemma tier_split : forall fs f, implied_t fs f = (if tier01 fs f then true else tier32 (gaps fs) fs f).
Proof.
  intros fs f. unfold implied_t, tier01, tier32. rewrite implied_m_eq.
  destruct (has_fact f fs); [reflexivity|]. destruct (implied (rel_facts (fact_vs f) fs) f); [reflexivity|].
  destruct (implied (rel_facts1 (fact_vs f) fs) f), (implied fs f); reflexivity.
Qed.

Definition fe_pass1 (fs : list fact) (sg : subst) (f : fact) (acc : list fact) : option (list fact) :=
  match sapply_fact sg f with
  | Some f' => Some (if tier01 fs f' then acc else f' :: acc)
  | None =>
      match f with
      | FRange k lo hi =>
          match IMap.find k sg with
          | Some u =>
              let g1 := FULe (VL lo) u in let g2 := FULe u (VL hi) in
              let acc1 := if tier01 fs g1 then acc else g1 :: acc in
              Some (if tier01 fs g2 then acc1 else g2 :: acc1)
          | None => None
          end
      | FAlign k m =>
          match IMap.find k sg with
          | Some u => if PrimInt63.leb m 62%uint63 && aligned fs u m then Some acc else None
          | None => None
          end
      | _ => None
      end
  end.
Fixpoint fe_pass1_all (fs : list fact) (sg : subst) (T : list fact) (acc : list fact) : option (list fact) :=
  match T with
  | [] => Some acc
  | f :: T' => match fe_pass1 fs sg f acc with
               | Some acc' => fe_pass1_all fs sg T' acc'
               | None => None
               end
  end.
Fixpoint all_tier32 (G : list gapc) (fs : list fact) (l : list fact) : bool :=
  match l with
  | [] => true
  | f :: l' => if tier32 G fs f then all_tier32 G fs l' else false
  end.
Fixpoint all_tier32x (IX : fidx) (G : list gapc) (fs : list fact) (l : list fact) : bool :=
  match l with
  | [] => true
  | f :: l' => if tier32x IX G fs f then all_tier32x IX G fs l' else false
  end.
Lemma all_tier32x_eq : forall fs IX G l, ix_ok fs IX -> all_tier32x IX G fs l = all_tier32 G fs l.
Proof. intros fs IX G l H. induction l as [|f l IH]; cbn; [reflexivity|]. rewrite (tier32x_eq fs IX G f H), IH. reflexivity. Qed.

Fixpoint all_tier23x (fs : list fact) (og : option (fidx * list gapc)) (l : list fact) : bool :=
  match l with
  | [] => true
  | f :: l' =>
      if implied (rel_facts1 (fact_vs f) fs) f then all_tier23x fs og l'
      else let ig := match og with Some ig => ig | None => let IX := mk_ix fs in (IX, gaps_x IX fs) end in
           if implied_mx (fst ig) (snd ig) fs f then all_tier23x fs (Some ig) l' else false
  end.
Lemma all_tier23x_eq : forall fs og l, (og = None \/ og = Some (mk_ix fs, gaps fs)) -> all_tier23x fs og l = all_tier32 (gaps fs) fs l.
Proof.
  intros fs og l. revert og. induction l as [|f l IH]; intros og OG; cbn [all_tier23x all_tier32]; [reflexivity|].
  unfold tier32 at 1. rewrite implied_m_eq.
  destruct (implied (rel_facts1 (fact_vs f) fs) f) eqn:T2.
  - rewrite (IH og OG). destruct (implied fs f); reflexivity.
  - destruct OG as [-> | ->]; cbn [fst snd];
      rewrite ?(gaps_x_eq fs (mk_ix fs) (mk_ix_ok fs)), (implied_mx_eq fs (mk_ix fs) (mk_ix_ok fs)), implied_m_eq;
      destruct (implied fs f); try reflexivity; apply IH; right; reflexivity.
Qed.

Definition facts_entailed_m (fs : list fact) (sg : subst) (T : list fact) : bool :=
  match fe_pass1_all fs sg T [] with
  | None => false
  | Some [] => true
  | Some res => if asan_on fs then (let IX := mk_ix fs in all_tier32x IX (gaps_x IX fs) fs res) else all_tier23x fs None res
  end.
Lemma facts_entailed_m_unfold : forall fs sg T,
  facts_entailed_m fs sg T = match fe_pass1_all fs sg T [] with None => false | Some [] => true | Some res => all_tier32 (gaps fs) fs res end.
Proof.
  intros. unfold facts_entailed_m. destruct (fe_pass1_all fs sg T []) as [[|f res]|]; try reflexivity.
  destruct (asan_on fs).
  - cbv zeta. rewrite (all_tier32x_eq fs (mk_ix fs) _ _ (mk_ix_ok fs)), (gaps_x_eq fs (mk_ix fs) (mk_ix_ok fs)). reflexivity.
  - apply all_tier23x_eq. left; reflexivity.
Qed.

Lemma all_tier32_forallb : forall fs l, all_tier32 (gaps fs) fs l = forallb (tier32 (gaps fs) fs) l.
Proof. induction l as [|f l IH]; cbn; [reflexivity|]. rewrite IH. destruct (tier32 (gaps fs) fs f); reflexivity. Qed.
Lemma fe_pass1_spec : forall fs sg f acc,
  match fe_pass1 fs sg f acc with
  | Some acc' => forallb (tier32 (gaps fs) fs) acc' = fact_entailed fs sg f && forallb (tier32 (gaps fs) fs) acc
  | None => fact_entailed fs sg f = false
  end.
Proof.
  intros fs sg f acc. unfold fe_pass1, fact_entailed.
  destruct (sapply_fact sg f) as [f'|].
  - rewrite (tier_split fs f'). destruct (tier01 fs f'); cbn [forallb]; [reflexivity|]. reflexivity.
  - destruct f; try reflexivity.
    + destruct (IMap.find k sg) as [u|]; [|reflexivity].
      rewrite (tier_split fs (FULe (VL lo) u)), (tier_split fs (FULe u (VL hi))).
      destruct (tier01 fs (FULe (VL lo) u)), (tier01 fs (FULe u (VL hi))); cbn [forallb];
        destruct (tier32 (gaps fs) fs (FULe u (VL hi))), (tier32 (gaps fs) fs (FULe (VL lo) u)); reflexivity.
    + destruct (IMap.find k sg) as [u|]; [|reflexivity].
      destruct (PrimInt63.leb m 62 && aligned fs u m); reflexivity.
Qed.
Lemma fe_pass1_all_spec : forall fs sg T acc,
  match fe_pass1_all fs sg T acc with
  | Some res => forallb (tier32 (gaps fs) fs) res = forallb (fact_entailed fs sg) T && forallb (tier32 (gaps fs) fs) acc
  | None => forallb (fact_entailed fs sg) T = false
  end.
Proof.
  intros fs sg T. induction T as [|f T IH]; intros acc; cbn; [reflexivity|].
  pose proof (fe_pass1_spec fs sg f acc) as S1.
  destruct (fe_pass1 fs sg f acc) as [acc'|].
  - specialize (IH acc'). destruct (fe_pass1_all fs sg T acc') as [res|].
    + rewrite IH, S1. destruct (fact_entailed fs sg f), (forallb (fact_entailed fs sg) T); reflexivity.
    + rewrite IH. destruct (fact_entailed fs sg f); reflexivity.
  - rewrite S1. reflexivity.
Qed.
Lemma facts_entailed_m_eq : forall fs sg T, facts_entailed_m fs sg T = forallb (fact_entailed fs sg) T.
Proof.
  intros fs sg T. rewrite facts_entailed_m_unfold.
  pose proof (fe_pass1_all_spec fs sg T []) as S. cbn [forallb] in S.
  destruct (fe_pass1_all fs sg T []) as [res|]; [|symmetry; exact S].
  rewrite andb_true_r in S. rewrite <- S. destruct res; [reflexivity|]. apply all_tier32_forallb.
Qed.

Definition entails_m (st : sstate) (T : sstate) (sg : subst) : bool :=
  PrimInt63.eqb (s_pc st) (s_pc T)
  && sv_eqb (rf_get (s_rf T) X0) (VL wzero)
  && rf_forallb2 (smatch sg) (s_rf T) (s_rf st)
  && rf_forallb2 (smatch sg) (s_ff T) (s_ff st)
  && resv_match sg (s_resv T) (s_resv st)
  && regions_match sg (s_regs T) (s_regs st)
  && facts_entailed_m (s_facts st) sg (s_facts T)
  && ops_match sg (s_ops T) (s_ops st)
  && privs_eqb (s_priv T) (s_priv st)
  && match svar sg 0%uint63 with Some k => PrimInt63.eqb k 0%uint63 | None => false end.
Lemma entails_m_eq : forall st T sg, entails_m st T sg = entails st T sg.
Proof. intros. unfold entails_m, entails. rewrite facts_entailed_m_eq. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Section Rot.
Variable rot : Mem.rotab.
Fixpoint check_rm (C : ctx) (p : plan) (st : sstate) {struct p} : option (list obligation) :=
  match p with
  | PFail msg => if PrimInt63.eqb msg DEAD && facts_dead (s_facts st) then Some [] else None
  | PRun stops k =>
      match run_r segs rot (c_itab C) stops st with
      | SStop KStopPc st' => check_rm C k st'
      | SStop KEcall st' => check_rm C k st'
      | SStop (KBranch _ _ _ _) st' => check_rm C k st'
      | _ => None
      end
  | PCase kT kF =>
      if PrimInt63.ltb (s_pc st) bit62i then
      match IMap.find (s_pc st) (c_itab C) with
      | Some (IBranch c rs1 rs2 off) =>
          let a := getr st rs1 in let b := getr st rs2 in
          match take_branch c a b off true st, take_branch c a b off false st with
          | Some stT, Some stF =>
              match check_rm C kT stT, check_rm C kF stF with
              | Some o1, Some o2 => Some (o1 ++ o2)
              | _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
      else None
  | PSplit r n ks =>
      let v := getr st r in
      match decide_ltu_t (s_facts st) v (VL (wlit n)) with
      | Some true =>
          if Nat.eqb (length ks) (Z.to_nat (to_Z n)) then
            (fix go (ks : list plan) (i : int) : option (list obligation) :=
               match ks with
               | [] => Some []
               | k :: ks' =>
                   match check_rm C k (addfact (setr st r (VL (wlit i))) (FEq v (VL (wlit i)))), go ks' (PrimInt63.add i 1%uint63) with
                   | Some o1, Some o2 => Some (o1 ++ o2)
                   | _, _ => None
                   end
               end) ks 0%uint63
          else None
      | _ => None
      end
  | PSetReg r v k =>
      match r, decide_eq_t (s_facts st) (getr st r) v with
      | X0, _ => None
      | _, Some true => check_rm C k (setr st r v)
      | _, _ => None
      end
  | PSubst x u k =>
      if negb (PrimInt63.eqb x 0%uint63)
         && match IMap.find x (s_regs st) with Some _ => false | None => true end
         && match decide_eq_t (s_facts st) (VP x wzero) u with Some true => true | _ => false end
      then
        let f := vsubst x u in
        check_rm C k (SS (s_pc st) (rf_map f (s_rf st)) (rf_map f (s_ff st))
                     (match s_resv st with RAddr a => RAddr (f a) | rv => rv end)
                     (IMap.map (region_map f) (s_regs st)) (List.map (fact_map f) (s_facts st))
                     (List.map (op_map f) (s_ops st)) (s_priv st) (s_next st))
      else None
  | PName r k =>
      let n := s_next st in
      match r with
      | X0 => None
      | _ =>
          if st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n bit62i then
            check_rm C k (SS (s_pc st) (rf_set (s_rf st) r (VP n wzero)) (s_ff st) (s_resv st) (s_regs st)
                        (FEq (VP n wzero) (getr st r) :: s_facts st) (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63))
          else None
      end
  | PSetHi rk v k =>
      if PrimInt63.eqb rk 0%uint63 then None else
      match IMap.find rk (s_regs st) with
      | Some r =>
          match decide_eq_t (s_facts st) (rg_hi r) v with
          | Some true => check_rm C k (setregs st (IMap.add rk (Region (rg_lo r) v (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)))
          | _ => None
          end
      | None => None
      end
  | PAssume f k =>
      if implied_t (s_facts st) f then check_rm C k (addfact st f)
      else
      match check_rm C k (addfact st f) with
      | Some o => Some ((s_facts st, f) :: o)
      | None => None
      end
  | PCall cid ks =>
      match IMap.find cid (c_contracts C) with
      | Some ct =>
          if PrimInt63.eqb (s_pc st) (c_pc ct) then
            match c_apply ct st with
            | Some sts =>
                (fix go (ks : list plan) (sts : list sstate) : option (list obligation) :=
                   match ks, sts with
                   | [], [] => Some []
                   | k :: ks', st' :: sts' =>
                       if PrimInt63.leb (s_next st) (s_next st') then
                         match check_rm C k st', go ks' sts' with
                         | Some o1, Some o2 => Some (o1 ++ o2)
                         | _, _ => None
                         end
                       else None
                   | _, _ => None
                   end) ks sts
            | None => None
            end
          else None
      | None => None
      end
  | PCut tid sg =>
      match IMap.find tid (c_cuts C) with
      | Some T => if entails_m st (t_st T) (mk_subst sg) then Some [] else None
      | None => None
      end
  | PCutDec tid sg =>
      match IMap.find tid (c_cuts C) with
      | Some T =>
          let s := mk_subst sg in
          if entails_m st (t_st T) s then
            match sapply s (t_measure T) with
            | Some m => match decide_ltu_t (s_facts st) m (c_mroot C) with
                        | Some true => Some []
                        | _ => None
                        end
            | None => None
            end
          else None
      | None => None
      end
  | PEcall eid sg =>
      match IMap.find (s_pc st) (c_itab C), IMap.find eid (c_ecalls C) with
      | Some IEcall, Some T => if entails_m st T (mk_subst sg) then Some [] else None
      | _, _ => None
      end
  | PForget k glo ghi kk =>
      match IMap.find k (s_regs st) with
      | Some r => check_rm C kk (setregs st (IMap.add k (Mem.region_forget r glo ghi) (s_regs st)))
      | None => None
      end
  | PDropFacts keep k =>
      check_rm C k (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (firstn keep (s_facts st))
                    (s_ops st) (s_priv st) (s_next st))
  end.
End Rot.
End WithSegs.

End EntM.
