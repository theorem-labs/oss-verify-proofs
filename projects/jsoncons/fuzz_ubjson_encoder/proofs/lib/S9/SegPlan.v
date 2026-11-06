(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import DigitFam.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  FPSteps AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module SGP.

Inductive bfact : Type :=
| BRange (id : nat) (from to : expr) (lo hi : Z)
| BSome (id : nat) (from to : expr) (lo hi : Z)
| BBad (id : nat) (s : expr) (ilo ihi : Z) (f : nat)
| BFam (id : nat) (es ee : expr) (f : nat)
| BNe (id : nat) (j : expr) (v : Z).
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.
Variable IT : itab.
Variable x_cpy x_set x_len ro_lo ro_hi : Z.
Variable BFUEL : nat.
Variable A : APC.atable.
Variable nx0 : nat.
Variable BR : list bfact.

Definition bbyte (E : env) (id : nat) (j : Z) : Z := bv_unsigned (nth (Z.to_nat j) (eb E id) (Z_to_bv 8 0)).
Definition blen (E : env) (id : nat) : Z := Z.of_nat (length (eb E id)).

Definition bbody (E : env) (id : nat) (from to : Z) : list Z :=
  map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat (to - from)) (skipn (Z.to_nat from) (eb E id))).
Definition bfact_ok (E : env) (bf : bfact) : Prop :=
  match bf with
  | BRange id from to lo hi =>
      forall j : Z, bv_unsigned (edenot E from) <= j < bv_unsigned (edenot E to) -> (Z.to_nat j < length (eb E id))%nat ->
        lo <= bbyte E id j <= hi
  | BSome id from to lo hi =>
      exists j : Z, bv_unsigned (edenot E from) <= j < bv_unsigned (edenot E to) /\ j < blen E id /\ lo <= bbyte E id j <= hi
  | BBad id s ilo ihi f =>
      exists i : Z, 0 <= i /\ ilo <= i <= ihi /\ bv_unsigned (edenot E s) + i < blen E id
        /\ (forall j : Z, bv_unsigned (edenot E s) <= j < bv_unsigned (edenot E s) + i -> 48 <= bbyte E id j <= 57)
        /\ (bbyte E id (bv_unsigned (edenot E s) + i) < 48 \/ 57 < bbyte E id (bv_unsigned (edenot E s) + i))
        /\ (blen E id - bv_unsigned (edenot E s) <= 38 ->
            DF.pfam_cond f (bbody E id (bv_unsigned (edenot E s)) (bv_unsigned (edenot E s) + i)))
  | BFam id es ee f =>
      bv_unsigned (edenot E es) <= bv_unsigned (edenot E ee) <= blen E id
      /\ DF.pfam_cond f (bbody E id (bv_unsigned (edenot E es)) (bv_unsigned (edenot E ee)))
  | BNe id j v => bv_unsigned (edenot E j) < blen E id -> bbyte E id (bv_unsigned (edenot E j)) <> v
  end.
Definition bfacts_ok (E : env) : Prop := Forall (bfact_ok E) BR.
Definition bfact_vars_lt (n : nat) (bf : bfact) : bool :=
  match bf with
  | BRange _ from to _ _ | BSome _ from to _ _ => (APC.expr_vars_lt n from && APC.expr_vars_lt n to)%bool
  | BBad _ s _ _ _ => APC.expr_vars_lt n s
  | BFam _ es ee _ => (APC.expr_vars_lt n es && APC.expr_vars_lt n ee)%bool
  | BNe _ j _ => APC.expr_vars_lt n j
  end.
Definition bfacts_vars_lt (n : nat) : bool := forallb (bfact_vars_lt n) BR.

Variable XSTEP : list (expr * Z * expr) -> nat -> sym_state -> option sym_state.

Variable XSTEP2 : list (expr * Z * expr) -> nat -> sym_state -> option (sym_state * sym_state).

Inductive splan : Type :=
| PStep (st : SR.sstep) (k : splan)
| PEnd (i : nat)
| PCase (e : expr) (mid : Z) (klo khi : splan)
| PBranch (ktaken knot : splan)
| PFact (K : kentry) (k : splan)
| PAbstract (b : expr) (o : Z) (n : Z) (k : splan)
| PCoalesce (b : expr) (o : Z) (n : expr) (k : splan)
| PFillX (k : splan)
| PCopyX (k : splan)
| PEvalReg (r J : nat) (k : splan)
| PFactRange (e : expr) (J : nat) (lo hi : Z) (k : splan)
| PRefine (v : nat) (lo hi : Z) (k : splan)
| PRespell (r : nat) (e : expr) (k : splan)
| PPin (v : nat) (c : Z) (k : splan)
| PLoadByte (k : splan)
| PLoadByteNe (v : Z) (klo khi : splan)
| PX (id : nat) (k : splan)
| PX2 (id : nat) (ka kb : splan)
| PLoop (J : nat) (N : expr) (inv : sym_state) (body k : splan)
| PNext
| PJoin (j : nat) (js : sym_state) (lo : nat) (karms k : splan)
| PMerge (j : nat).

Inductive loopctx : Type := LC (lc_head : Z) (lc_next : sym_state) (lc_lo lc_hi : nat).
Inductive joinctx : Type := JC (jc_id : nat) (jc_st : sym_state) (jc_b jc_lo : nat).

Fixpoint find_jc (j : nat) (jc : list joinctx) : option joinctx :=
  match jc with
  | [] => None
  | (JC j' js b lo) as c :: r => if Nat.eqb j' j then Some c else find_jc j r
  end.
Lemma find_jc_id : forall j jc j' js b lo, find_jc j jc = Some (JC j' js b lo) -> j' = j.
Proof.
  intros j jc; induction jc as [|[j1 js1 b1 lo1] r IH]; intros j' js b lo H; cbn [find_jc] in H; [discriminate|].
  destruct (Nat.eqb j1 j) eqn:E; [apply Nat.eqb_eq in E; injection H; intros; subst; reflexivity | exact (IH _ _ _ _ H)].
Qed.
Lemma find_jc_In : forall j jc c, find_jc j jc = Some c -> In c jc.
Proof.
  intros j jc; induction jc as [|[j1 js1 b1 lo1] r IH]; intros c H; cbn [find_jc] in H; [discriminate|].
  destruct (Nat.eqb j1 j); [injection H; intros <-; left; reflexivity | right; exact (IH _ H)].
Qed.

Definition acs_of (ss : sym_state) : APC.acs :=
  APC.ACS ss [] 0 0 0 [] [] 0 (ELit 0) APC.FdStd false.

Definition set_kn (ss : sym_state) (k : list kentry) : sym_state :=
  SS (s_pc ss) (s_regs ss) [] k (s_next ss).

Definition region : Type := (expr * Z * expr)%type.
Definition outside (E : env) (F : list region) (a : word) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in
            bv_unsigned a < estart E (SA rb rlo) \/ estart E (SA rb rlo) + elenZ E rlen <= bv_unsigned a) F.
Definition regions_flat (E : env) (F : list region) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in 0 <= estart E (SA rb rlo) /\ estart E (SA rb rlo) + elenZ E rlen <= 2 ^ 64) F.
Definition regions_ok (E : env) (F : list region) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in
            0 <= estart E (SA rb rlo) /\ 0 < elenZ E rlen < 2 ^ 64 /\ estart E (SA rb rlo) + elenZ E rlen <= 2 ^ 64) F.
Lemma regions_ok_flat : forall E F, regions_ok E F -> regions_flat E F.
Proof.
  intros E F H. unfold regions_ok, regions_flat in *. eapply Forall_impl; [|exact H].
  intros [[rb rlo] rlen] X. lia.
Qed.

Definition of_lit_region (r : SR.region) : region := let '(rb, rlo, rlen) := r in (rb, rlo, ELit rlen).
Definition region_vars_lt (n : nat) (r : region) : bool :=
  let '(rb, _, rlen) := r in (APC.expr_vars_lt n rb && APC.expr_vars_lt n rlen)%bool.
Lemma elenZ_litZ : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. reflexivity. Qed.

Definition inst (inv : sym_state) (J : nat) (e : expr) : sym_state :=
  SS (s_pc inv) (map (APC.esubst J e) (s_regs inv)) [] (map (APC.ksubst J e) (s_know inv)) (s_next inv).

Definition body_state (J : nat) (N : expr) (nhi : Z) (inv : sym_state) : sym_state :=
  set_kn inv (KRange (EVar J) 0 (nhi - 1) :: KRange (APC.esub N (EVar J)) 1 nhi :: s_know inv).

Definition piece_of (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KUnk (SA b o) n | KZero (SA b o) n | KFill (SA b o) n _ | KBlob (SA b o) n _ => Some (b, o, n)
  | KWord (SA b o) w _ => Some (b, o, ELit (Z.of_nat w))
  | _ => None
  end.

Fixpoint find_piece (allkn k : list kentry) (tb : expr) (pos : xterms) : option (expr * Z * expr) :=
  match k with
  | [] => None
  | K :: r => match piece_of K with
              | Some (b, o, n) => if (shares_var tb b && lin_ge0 allkn pos [(b, o)] && lin_ge0 allkn [(b, o)] pos)%bool then Some (b, o, n)
                                  else find_piece allkn r tb pos
              | None => find_piece allkn r tb pos
              end
  end.
Fixpoint chain_cover (fuel : nat) (kn : list kentry) (tb : expr) (pos goal : xterms) : bool :=
  match fuel with
  | O => false
  | S f => if lin_ge0 kn pos goal then true
           else match find_piece kn kn tb pos with
                | Some (b, o, n) => chain_cover f kn tb [(b, o); (n, 0)] goal
                | None => false
                end
  end.

Definition kunk_chain (kn : list kentry) (b : expr) (o : Z) (n : expr) : bool :=
  (APC.flat_x kn b o n && APC.off_image_x A kn b o n && Z.leb (APC.img_lo A) (APC.img_hi A)
   && chain_cover (S (length kn)) kn b [(b, o)] [(b, o); (n, 0)])%bool.
Definition coalesce (ss : sym_state) (b : expr) (o : Z) (n : expr) : option sym_state :=
  let kn := s_know ss in
  if (kunk_chain kn b o n && APC.expr_vars_lt (s_next ss) b && APC.expr_vars_lt (s_next ss) n)%bool
  then Some (set_kn ss (KUnk (SA b o) n :: APC.kn_cutout kn b o n))
  else None.

Definition tmpl_chain (kn : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) n => if existsb (fun X => APC.kentry_eqb X K) kn then false   else kunk_chain kn b o n
  | _ => false
  end.

Definition tmpl_rest (kn : list kentry) (tk : list kentry) : list kentry := List.filter (fun K => negb (tmpl_chain kn K)) tk.
Definition entails_h (lo hi : nat) (ss T : sym_state) : bool :=
  (APC.entails_h A lo hi (acs_of ss) (acs_of (set_kn T (tmpl_rest (s_know ss) (s_know T))))
   && APC.kn_vars_lt lo (s_know T))%bool.

Definition is_slot (lo hi : nat) (t : expr) : option nat :=
  match t with EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool then Some v else None | _ => None end.
Definition reg_slot_top (lo hi : nat) (ts : list expr) : nat :=
  fold_right (fun t m => match is_slot lo hi t with Some v => Nat.max (S v) m | None => m end) lo ts.
Fixpoint first_slot_index (lo hi v : nat) (ts : list expr) (i : nat) : option nat :=
  match ts with
  | [] => None
  | t :: r => match is_slot lo hi t with
              | Some v' => if Nat.eqb v v' then Some i else first_slot_index lo hi v r (S i)
              | None => first_slot_index lo hi v r (S i)
              end
  end.
Definition in_rng (kn : list kentry) (e : expr) (l h : Z) : bool :=
  match erange kn e with Some (a, b) => (Z.leb l a && Z.leb b h)%bool | None => false end.
Fixpoint cell_value (kn : list kentry) (a : saddr) (w : nat) : option expr :=
  match kn with
  | [] => None
  | KWord a' w' e :: r => if (saddr_eqb a a' && Nat.eqb w w')%bool then Some e else cell_value r a w
  | _ :: r => cell_value r a w
  end.
Inductive tk_kind := TkBase | TkRegFact (v : nat) (l h : Z) | TkCell (a : saddr) (w : nat) (c : nat) | TkCellFact (c : nat) (l h : Z).
Definition classify (lo hi0 hi : nat) (K : kentry) : tk_kind :=
  match K with
  | KRange (EVar v) l h =>
      if (Nat.leb lo v && Nat.ltb v hi0)%bool then TkRegFact v l h
      else if (Nat.leb hi0 v && Nat.ltb v hi)%bool then TkCellFact v l h else TkBase
  | KWord a w (EVar c) => if (Nat.leb hi0 c && Nat.ltb c hi)%bool then TkCell a w c else TkBase
  | _ => TkBase
  end.
Definition is_base (lo hi0 hi : nat) (K : kentry) : bool := match classify lo hi0 hi K with TkBase => true | _ => false end.
Definition tk_cells (lo hi0 hi : nat) (tk : list kentry) : list (saddr * nat * nat) :=
  flat_map (fun K => match classify lo hi0 hi K with TkCell a w c => [(a, w, c)] | _ => [] end) tk.
Fixpoint find_cslot (c : nat) (cs : list (saddr * nat * nat)) : option (saddr * nat) :=
  match cs with [] => None | (a, w, c') :: r => if Nat.eqb c c' then Some (a, w) else find_cslot c r end.
Fixpoint nodupb (l : list nat) : bool :=
  match l with [] => true | x :: r => (negb (existsb (Nat.eqb x) r) && nodupb r)%bool end.
Definition xentry_ok (lo hi0 hi : nat) (kn : list kentry) (rs ts : list expr) (cs : list (saddr * nat * nat)) (K : kentry) : bool :=
  match classify lo hi0 hi K with
  | TkBase => true
  | TkRegFact v l h =>
      match first_slot_index lo hi v ts 0 with Some i => in_rng kn (nth i rs (ELit 0)) l h | None => false end
  | TkCell a w c =>
      (APC.expr_vars_lt lo (a_base a)
       && match cell_value kn a w with Some e => APC.expr_vars_lt lo e | None => false end)%bool
  | TkCellFact c l h =>
      match find_cslot c cs with
      | Some (a, w) => match cell_value kn a w with Some e => in_rng kn e l h | None => false end
      | None => false
      end
  end.
Definition entails_hx (lo hi : nat) (ss T : sym_state) : bool :=
  let hi0 := reg_slot_top lo hi (s_regs T) in
  let tk := s_know T in let kn := s_know ss in
  let base := List.filter (is_base lo hi0 hi) tk in
  let cs := tk_cells lo hi0 hi tk in
  (entails_h lo hi ss (set_kn T base)
   && Nat.leb hi0 hi
   && APC.sr_vars_lt hi0 (s_regs T)
   && nodupb (map (fun x => snd x) cs)
   && forallb (xentry_ok lo hi0 hi kn (s_regs ss) (s_regs T) cs) tk)%bool.

Definition guard (lc : option loopctx) (jc : list joinctx) (ss : sym_state) : bool :=
  (match lc with Some (LC _ nx lo hi) => Nat.leb nx0 lo && Nat.leb lo hi && Nat.leb hi (s_next ss) && Nat.leb nx0 (s_next nx) | None => true end
   && forallb (fun c => match c with JC _ js b lo => Nat.leb nx0 b && Nat.leb b lo && Nat.leb lo (s_next js) && Nat.leb b (s_next ss) end) jc
   && Nat.leb nx0 (s_next ss))%bool.

Definition end_ok (ps : SR.post_spec) (ss : sym_state) : bool :=
  (Z.eqb (s_pc ss) (SR.ps_pc ps)
   && forallb (fun ie : nat * expr => Nat.ltb 0 (fst ie) && Nat.ltb (fst ie) 32 && expr_eqb (nth (fst ie) (s_regs ss) (ELit 0)) (snd ie)) (SR.ps_regs ps)
   && forallb (fun K => existsb (APC.kentry_eqb K) (s_know ss)) (SR.ps_cells ps))%bool.

Definition case_arms (ss : sym_state) (e : expr) (mid : Z) : option (option sym_state * option sym_state) :=
  if negb (APC.expr_vars_lt (s_next ss) e) then None else
  match erange (s_know ss) e with
  | Some (lo, hi) =>
      if Z.leb hi mid then Some (Some ss, None)
      else if Z.ltb mid lo then Some (None, Some ss)
      else
        let slo := set_kn ss (KRange e lo mid :: s_know ss) in
        let shi := set_kn ss (KRange e (mid + 1) hi :: s_know ss) in
        Some ((if APC.kn_contra (s_know slo) then None else Some slo),
              (if APC.kn_contra (s_know shi) then None else Some shi))
  | None => None
  end.

Definition branch_probe (ss : sym_state) : option expr := APC.branch_probe IT (acs_of ss).

Definition loop_ok (ss : sym_state) (J : nat) (N : expr) (inv : sym_state) : option Z :=
  APC.loop_ok nx0 (acs_of ss) J N (acs_of inv).

Definition via_ok (ss js : sym_state) (lo : nat) : bool :=
  (match s_log js with [] => true | _ => false end
   && Nat.eqb (length (s_regs js)) 32
   && Nat.leb nx0 (s_next ss) && Nat.leb (s_next ss) lo && Nat.leb lo (s_next js))%bool.

Definition abstract (ss : sym_state) (b : expr) (o : Z) (n : Z) : option sym_state :=
  let K := KUnk (SA b o) (ELit n) in
  if (APC.kunk_covered A (s_know ss) K && APC.kn_vars_lt (s_next ss) (s_know ss) && APC.expr_vars_lt (s_next ss) b)%bool
  then Some (set_kn ss (K :: APC.kn_cutout (s_know ss) b o (ELit n)))
  else None.

Definition within1X (kn : list kentry) (b : expr) (k n : Z) (r : region) : bool :=
  let '(rb, rlo, rlen) := r in
  (match rlen with
   | ELit m => (Z.leb 0 m && Z.ltb m two64 && SR.within1 b k n (rb, rlo, m))%bool
   | _ => false
   end || xinside kn b k (ELit n) rb rlo rlen)%bool.
Definition withinX (kn : list kentry) (F : list region) (b : expr) (k n : Z) : bool :=
  (Z.ltb 0 n && Z.ltb n two64 && existsb (within1X kn b k n) F)%bool.
Definition went_withinX (kn : list kentry) (F : list region) (g : SR.went) : bool :=
  match g with
  | SR.WSt (SA b k) wd _ => withinX kn F b k (Z.of_nat wd)
  | SR.WCopy db dk _ _ n => withinX kn F db dk n
  | SR.WFill db dk n _ => withinX kn F db dk n
  end.

Definition withinE (kn : list kentry) (F : list region) (b : expr) (k : Z) (ne : expr) : bool :=
  existsb (fun r : region => let '(rb, rlo, rlen) := r in xinside kn b k ne rb rlo rlen) F.

Definition fillx (F : list region) (ss : sym_state) : option sym_state :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  if negb (Z.eqb (s_pc ss) x_set) then None else
  if negb (SR.closed ss []) then None else
  match SR.ret_lit ss, SR.reg ss 11 with
  | Some ret, ELit c0 =>
      let ne := SR.reg ss 12 in let c8 := (c0 mod two64) mod 256 in
      let dst := SR.reg ss 10 in let '(db, dk) := split_lit dst in
      match xlo fk ne, xhi fk ne, xhi fk dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64
              && APC.flat_x fk db dk ne && APC.kwritable_x fk k db dk ne && withinE fk F db dk ne)%bool
          then let k' := (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: APC.kn_havoc k db dk ne in
               if APC.kn_vars_lt nx k' then Some (SR.after_call ss ret dst k') else None
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.

Inductive cov : Type := CovFill (c : Z) | CovUnk | CovBlob (id : nat).
Definition same_range (fk : list kentry) (sb : expr) (sk : Z) (ne : expr) (b : expr) (o : Z) (n : expr) : bool :=
  (lin_ge0 fk [(sb, sk)] [(b, o)] && lin_ge0 fk [(b, o)] [(sb, sk)] && lin_ge0 fk [(ne, 0)] [(n, 0)] && lin_ge0 fk [(n, 0)] [(ne, 0)])%bool.
Fixpoint src_cover (fk k : list kentry) (sb : expr) (sk : Z) (ne : expr) : option cov :=
  match k with
  | [] => None
  | K :: r =>
      let hit := match K with
                 | KZero (SA b o) n => if xinside fk sb sk ne b o n then Some (CovFill 0) else None
                 | KFill (SA b o) n c => if xinside fk sb sk ne b o n then Some (CovFill c) else None
                 | KUnk (SA b o) n => if xinside fk sb sk ne b o n then Some CovUnk else None
                 | KBlob (SA b o) n id => if xinside fk sb sk ne b o n
                                          then Some (if same_range fk sb sk ne b o n then CovBlob id else CovUnk) else None
                 | _ => None
                 end in
      match hit with Some x => Some x | None => src_cover fk r sb sk ne end
  end.

Definition src_cover2 (fk k : list kentry) (sb : expr) (sk : Z) (ne : expr) : option cov :=
  match src_cover fk k sb sk ne with
  | Some c => Some c
  | None => match ne with
            | ELit n => if APC.kunk_covered A k (KUnk (SA sb sk) (ELit n)) then Some CovUnk else None
            | _ => None
            end
  end.

Definition copyx (F : list region) (ss : sym_state) : option sym_state :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  if negb (Z.eqb (s_pc ss) x_cpy) then None else
  if negb (SR.closed ss []) then None else
  match SR.ret_lit ss with
  | Some ret =>
      let ne := SR.reg ss 12 in let dst := SR.reg ss 10 in let src := SR.reg ss 11 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo fk ne, xhi fk ne, xhi fk dst, xhi fk src, src_cover2 fk k sb sk ne with
      | Some nlo, Some nhi, Some dhi, Some shi, Some cov =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64
              && APC.flat_x fk db dk ne && APC.flat_x fk sb sk ne && APC.kwritable_x fk k db dk ne
              && ranges_apart_x fk db dk ne sb sk ne && withinE fk F db dk ne)%bool
          then let kd := match cov with
                         | CovFill c => if Z.eqb (c mod 256) 0 then KZero (SA db dk) ne else KFill (SA db dk) ne (c mod 256)
                         | CovUnk => KUnk (SA db dk) ne
                         | CovBlob id => KBlob (SA db dk) ne id
                         end in
               let k' := kd :: APC.kn_havoc k db dk ne in
               if APC.kn_vars_lt nx k' then Some (SR.after_call ss ret dst k') else None
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Definition EVAL_MAX : Z := 8192.
Definition Ez : env := Env (fun _ => Z_to_bv 64 0) (fun _ => []).
Fixpoint noblob (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => noblob a && noblob b
  | EExt _ _ _ a => noblob a
  | EBlob _ _ _ _ => false
  end%bool.
Definition eval_at (J : nat) (e : expr) (v : Z) : option Z :=
  let e' := APC.esubst J (ELit v) e in
  if (APC.expr_vars_lt 0 e' && noblob e')%bool then Some (bv_unsigned (edenot Ez e')) else None.
Fixpoint eval_all (fuel : nat) (J : nat) (e : expr) (v : Z) (c : Z) : bool :=
  match fuel with
  | O => true
  | S f => match eval_at J e v with Some c' => Z.eqb c' c && eval_all f J e (v + 1) c | None => false end
  end%bool.
Definition evalreg (ss : sym_state) (r J : nat) : option sym_state :=
  if negb (Nat.ltb 0 r && Nat.ltb r 32)%bool then None else
  let e := SR.reg ss r in

  match (match erange (s_know ss) e with Some (c, c') => if Z.eqb c c' then Some c else None | None => None end) with
  | Some c => Some (SS (s_pc ss) (sr_upd (s_regs ss) r (ELit c)) [] (s_know ss) (s_next ss))
  | None =>

  match erange (s_know ss) (EVar J) with
  | Some (lo, hi) =>
      if negb (Z.leb lo hi && Z.leb (hi - lo) EVAL_MAX)%bool then None else
      match eval_at J e lo with
      | Some c => if eval_all (Z.to_nat (hi - lo + 1)) J e lo c
                  then Some (SS (s_pc ss) (sr_upd (s_regs ss) r (ELit c)) [] (s_know ss) (s_next ss))
                  else None
      | None => None
      end
  | None => None
  end end.

Fixpoint eval_all_in (fuel : nat) (J : nat) (e : expr) (v : Z) (lo hi : Z) : bool :=
  match fuel with
  | O => true
  | S f => match eval_at J e v with Some c => Z.leb lo c && Z.leb c hi && eval_all_in f J e (v + 1) lo hi | None => false end
  end%bool.
Definition factrange (ss : sym_state) (e : expr) (J : nat) (lo hi : Z) : option sym_state :=
  if negb (APC.expr_vars_lt (s_next ss) e) then None else
  match erange (s_know ss) (EVar J) with
  | Some (jlo, jhi) =>
      if negb (Z.leb jlo jhi && Z.leb (jhi - jlo) EVAL_MAX)%bool then None else
      if eval_all_in (Z.to_nat (jhi - jlo + 1)) J e jlo lo hi
      then Some (set_kn ss (KRange e lo hi :: s_know ss))
      else None
  | None => None
  end.

Definition pin (ss : sym_state) (v : nat) (c : Z) : option sym_state :=
  if negb (Nat.ltb v (s_next ss)) then None else
  match erange (s_know ss) (EVar v) with
  | Some (l, h) => if (Z.eqb l c && Z.eqb h c)%bool then Some (inst ss v (ELit c)) else None
  | None => None
  end.

Definition respell (ss : sym_state) (r : nat) (e : expr) : option sym_state :=
  if negb (Nat.ltb 0 r && Nat.ltb r 32 && APC.expr_vars_lt (s_next ss) e)%bool then None else
  match erange (s_know ss) (APC.esub (SR.reg ss r) e) with
  | Some (0, 0) => Some (SS (s_pc ss) (sr_upd (s_regs ss) r e) [] (s_know ss) (s_next ss))
  | _ => None
  end.

Definition two63 : Z := 9223372036854775808.
Definition refute1 (kn' : list kentry) (e : expr) (a b : Z) : bool :=
  (match e with
   | EAlu ALU_SLT x (ELit 0) =>
       match erange kn' x with
       | Some (xl, xh) => (Z.leb two63 xl && negb (Z.leb a 1 && Z.leb 1 b)) || (Z.ltb xh two63 && negb (Z.leb a 0 && Z.leb 0 b))
       | None => false
       end
   | _ => false
   end
   || match erange kn' e with Some (el, eh) => Z.ltb eh a || Z.ltb b el | None => false end)%bool.
Definition kn_remove (K : kentry) (kn : list kentry) : list kentry := List.filter (fun X => negb (APC.kentry_eqb X K)) kn.
Definition refuted (kn : list kentry) (v : nat) (p q : Z) : bool :=
  existsb (fun K => match K with
                    | KRange e a b => refute1 (KRange (EVar v) p q :: kn_remove K kn) e a b
                    | _ => false
                    end) kn.
Definition refine (ss : sym_state) (v : nat) (lo hi : Z) : option sym_state :=
  if negb (Nat.ltb v (s_next ss)) then None else
  let kn := s_know ss in
  let cur := match erange kn (EVar v) with Some r => r | None => (0, two64 - 1) end in
  let cl := Z.max (fst cur) 0 in let ch := Z.min (snd cur) (two64 - 1) in
  if negb (Z.leb cl lo && Z.leb lo hi && Z.leb hi ch)%bool then None else
  if negb ((Z.eqb lo cl || refuted kn v cl (lo - 1)) && (Z.eqb hi ch || refuted kn v (hi + 1) ch))%bool then None else
  Some (set_kn ss (KRange (EVar v) lo hi :: kn)).

Fixpoint find_blob_cover (fk k : list kentry) (rb : expr) (rk : Z) : option (expr * Z * nat) :=
  match k with
  | [] => None
  | KBlob (SA kb kk) len id :: r => if xinside fk rb rk (ELit 1) kb kk len then Some (kb, kk, id) else find_blob_cover fk r rb rk
  | _ :: r => find_blob_cover fk r rb rk
  end.
Fixpoint find_bfact (fk : list kentry) (brs : list bfact) (id : nat) (rb : expr) (rk : Z) (kb : expr) (kk : Z)
  : option (Z * Z) :=
  match brs with
  | [] => None
  | BRange id' from to lo hi :: r =>
      if (Nat.eqb id' id && lin_ge0 fk [(rb, rk)] [(kb, kk); (from, 0)] && lin_ge0 fk [(kb, kk); (to, 0)] [(rb, rk + 1)]
          && Z.leb 0 lo && Z.leb hi 255)%bool
      then Some (lo, hi) else find_bfact fk r id rb rk kb kk
  | _ :: r => find_bfact fk r id rb rk kb kk
  end.
Definition lbu_of (i : instr) : option (reg * reg * bv 12) :=
  match i with Load SZ1 false rd rs imm => Some (rd, rs, imm) | _ => None end.
Lemma lbu_of_sound : forall i rd rs imm, lbu_of i = Some (rd, rs, imm) -> i = Load SZ1 false rd rs imm.
Proof.
  intros i rd rs imm H. destruct i; cbn [lbu_of] in H; try discriminate.
  match goal with [ m : msize, sg : bool |- _ ] => destruct m; try discriminate; destruct sg; try discriminate end.
  injection H as <- <- <-. reflexivity.
Qed.

Definition lb_range (fk : list kentry) (id : nat) (rb : expr) (rk : Z) (kb : expr) (kk : Z) : Z * Z :=
  match find_bfact fk BR id rb rk kb kk with Some r => r | None => (0, 255) end.
Definition loadbyte (ss : sym_state) : option sym_state :=
  match itab_lookup IT (s_pc ss) with
  | Some i =>
      match lbu_of i with
      | Some (rd, rs, imm) =>
      if bv_eqb rd 0 then None else
      if negb (SR.closed ss []) then None else
      let kn := s_know ss in let fk := facts_of kn in let nx := s_next ss in
      let a := to_saddr (sr_get (s_regs ss) rs) (bv_signed imm) in
      let rb := a_base a in let rk := a_off a in
      match find_blob_cover fk kn rb rk with
      | Some (kb, kk, id) =>
          let '(lo, hi) := lb_range fk id rb rk kb kk in
          Some (SS (s_pc ss + 4) (sr_upd (s_regs ss) (ridx rd) (EVar nx)) [] (KRange (EVar nx) lo hi :: kn) (S nx))
      | None => None
      end
      | None => None
      end
  | None => None
  end.

Fixpoint find_bne (fk : list kentry) (brs : list bfact) (id : nat) (rb : expr) (rk : Z) (kb : expr) (kk : Z) (v : Z) : bool :=
  match brs with
  | [] => false
  | BNe id' j v' :: r =>
      if (Nat.eqb id' id && Z.eqb v' v && lin_ge0 fk [(rb, rk)] [(kb, kk); (j, 0)] && lin_ge0 fk [(kb, kk); (j, 0)] [(rb, rk)])%bool
      then true else find_bne fk r id rb rk kb kk v
  | _ :: r => find_bne fk r id rb rk kb kk v
  end.
Definition loadbyte_ne (v : Z) (ss : sym_state) : option (option sym_state * option sym_state) :=
  match itab_lookup IT (s_pc ss) with
  | Some i =>
      match lbu_of i with
      | Some (rd, rs, imm) =>
      if bv_eqb rd 0 then None else
      if negb (SR.closed ss []) then None else
      let kn := s_know ss in let fk := facts_of kn in let nx := s_next ss in
      let a := to_saddr (sr_get (s_regs ss) rs) (bv_signed imm) in
      let rb := a_base a in let rk := a_off a in
      match find_blob_cover fk kn rb rk with
      | Some (kb, kk, id) =>
          let '(lo, hi) := lb_range fk id rb rk kb kk in
          if find_bne fk BR id rb rk kb kk v then
            Some ((if Z.leb lo (v - 1) then Some (SS (s_pc ss + 4) (sr_upd (s_regs ss) (ridx rd) (EVar nx)) [] (KRange (EVar nx) lo (v - 1) :: kn) (S nx)) else None),
                  (if Z.leb (v + 1) hi then Some (SS (s_pc ss + 4) (sr_upd (s_regs ss) (ridx rd) (EVar nx)) [] (KRange (EVar nx) (v + 1) hi :: kn) (S nx)) else None))
          else None
      | None => None
      end
      | None => None
      end
  | None => None
  end.

Section Check.
Variable F : list region.
Variable PSS : list SR.post_spec.

Definition step1 (st : SR.sstep) (ss : sym_state) : option sym_state :=
  match SR.seg_step segs IT x_cpy x_set x_len ro_lo ro_hi BFUEL st ss [] with
  | Some (ss', w') => if forallb (went_withinX (s_know ss') F) w' then Some ss' else None
  | None => None
  end.

Fixpoint check (lc : option loopctx) (jc : list joinctx) (p : splan) (ss : sym_state) {struct p} : bool :=
  guard lc jc ss &&
  match p with
  | PStep st k => match step1 st ss with Some ss' => check lc jc k ss' | None => false end
  | PEnd i => match nth_error PSS i with Some ps => end_ok ps ss | None => false end
  | PCase e mid klo khi =>
      match case_arms ss e mid with
      | Some (alo, ahi) =>
          match alo with Some s1 => check lc jc klo s1 | None => true end
          && match ahi with Some s2 => check lc jc khi s2 | None => true end
      | None => false
      end
  | PBranch kt kf =>
      match branch_probe ss with
      | Some e =>
          match case_arms ss e 0 with
          | Some (af, at_) =>
              match af with Some s1 => check lc jc kf s1 | None => true end
              && match at_ with Some s2 => check lc jc kt s2 | None => true end
          | None => false
          end
      | None => false
      end
  | PFact K k =>
      (APC.fact_ok (s_know ss) K && APC.kentry_vars_lt (s_next ss) K) && check lc jc k (set_kn ss (K :: s_know ss))
  | PAbstract b o n k => match abstract ss b o n with Some ss' => check lc jc k ss' | None => false end
  | PCoalesce b o n k => match coalesce ss b o n with Some ss' => check lc jc k ss' | None => false end
  | PFillX k => match fillx F ss with Some ss' => check lc jc k ss' | None => false end
  | PCopyX k => match copyx F ss with Some ss' => check lc jc k ss' | None => false end
  | PEvalReg r J k => match evalreg ss r J with Some ss' => check lc jc k ss' | None => false end
  | PFactRange e J lo hi k => match factrange ss e J lo hi with Some ss' => check lc jc k ss' | None => false end
  | PRefine v lo hi k => match refine ss v lo hi with Some ss' => check lc jc k ss' | None => false end
  | PRespell r e k => match respell ss r e with Some ss' => check lc jc k ss' | None => false end
  | PPin v c k => match pin ss v c with Some ss' => check lc jc k ss' | None => false end
  | PLoadByte k => match loadbyte ss with Some ss' => check lc jc k ss' | None => false end
  | PLoadByteNe v klo khi =>
      match loadbyte_ne v ss with
      | Some (alo, ahi) =>
          match alo with Some s1 => check lc jc klo s1 | None => true end
          && match ahi with Some s2 => check lc jc khi s2 | None => true end
      | None => false
      end
  | PX id k => match XSTEP F id ss with Some ss' => Nat.leb (s_next ss) (s_next ss') && check lc jc k ss' | None => false end
  | PX2 id ka kb => match XSTEP2 F id ss with
                  | Some (sa, sb) => Nat.leb (s_next ss) (s_next sa) && Nat.leb (s_next ss) (s_next sb) && check lc jc ka sa && check lc jc kb sb
                  | None => false end
  | PLoop J N inv body k =>
      match loop_ok ss J N inv with
      | Some nhi =>
          let lo := S J in let hi := s_next inv in
          Z.eqb (s_pc inv) (s_pc ss)
          && entails_hx lo hi ss (inst inv J (ELit 0))
          && check (Some (LC (s_pc ss) (inst inv J (APC.eaddz (EVar J) 1)) lo hi)) jc body (body_state J N nhi inv)
          && check lc jc k (inst inv J N)
      | None => false
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) => Z.eqb (s_pc ss) h && Nat.eqb (length (s_regs nx)) 32 && entails_hx lo hi ss nx
      | None => false
      end
  | PJoin j js lo karms k =>
      via_ok ss js lo && check lc (JC j js (s_next ss) lo :: jc) karms ss && check lc jc k js
  | PMerge j =>
      match find_jc j jc with
      | Some (JC j' js b lo) => Nat.eqb j j' && Z.eqb (s_pc ss) (s_pc js) && Nat.eqb (length (s_regs js)) 32 && entails_hx lo (s_next js) ss js
      | None => false
      end
  end%bool.

Inductive dres : Type := DOk | DFail (path : list nat) (code : nat) (ss : sym_state).
Definition dand (a : dres) (b : unit -> dres) : dres := match a with DOk => b tt | f => f end.
Fixpoint check_dbg (path : list nat) (lc : option loopctx) (jc : list joinctx) (p : splan) (ss : sym_state) {struct p} : dres :=
  if negb (guard lc jc ss) then DFail path 0 ss else
  match p with
  | PStep st k => match step1 st ss with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 1 ss end
  | PEnd i => match nth_error PSS i with Some ps => if end_ok ps ss then DOk else DFail path 2 ss | None => DFail path 2 ss end
  | PCase e mid klo khi =>
      match case_arms ss e mid with
      | Some (alo, ahi) =>
          dand (match alo with Some s1 => check_dbg (0%nat :: path) lc jc klo s1 | None => DOk end)
               (fun _ => match ahi with Some s2 => check_dbg (1%nat :: path) lc jc khi s2 | None => DOk end)
      | None => DFail path 3 ss
      end
  | PBranch kt kf =>
      match branch_probe ss with
      | Some e =>
          match case_arms ss e 0 with
          | Some (af, at_) =>
              dand (match af with Some s1 => check_dbg (1%nat :: path) lc jc kf s1 | None => DOk end)
                   (fun _ => match at_ with Some s2 => check_dbg (0%nat :: path) lc jc kt s2 | None => DOk end)
          | None => DFail path 4 ss
          end
      | None => DFail path 4 ss
      end
  | PFact K k => if (APC.fact_ok (s_know ss) K && APC.kentry_vars_lt (s_next ss) K)%bool
                 then check_dbg (0%nat :: path) lc jc k (set_kn ss (K :: s_know ss)) else DFail path 5 ss
  | PAbstract b o n k => match abstract ss b o n with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PCoalesce b o n k => match coalesce ss b o n with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PFillX k => match fillx F ss with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PCopyX k => match copyx F ss with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PEvalReg r J k => match evalreg ss r J with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PFactRange e J lo hi k => match factrange ss e J lo hi with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PRefine v lo hi k => match refine ss v lo hi with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PRespell r e k => match respell ss r e with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PPin v c k => match pin ss v c with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PLoadByte k => match loadbyte ss with Some ss' => check_dbg (0%nat :: path) lc jc k ss' | None => DFail path 6 ss end
  | PLoadByteNe v klo khi =>
      match loadbyte_ne v ss with
      | Some (alo, ahi) =>
          dand (match alo with Some s1 => check_dbg (0%nat :: path) lc jc klo s1 | None => DOk end)
               (fun _ => match ahi with Some s2 => check_dbg (1%nat :: path) lc jc khi s2 | None => DOk end)
      | None => DFail path 6 ss
      end
  | PX id k => match XSTEP F id ss with Some ss' => if Nat.leb (s_next ss) (s_next ss') then check_dbg (0%nat :: path) lc jc k ss' else DFail path 6 ss | None => DFail path 6 ss end
  | PX2 id ka kb => match XSTEP2 F id ss with
                  | Some (sa, sb) => if (Nat.leb (s_next ss) (s_next sa) && Nat.leb (s_next ss) (s_next sb))%bool then
                                      match check_dbg (0%nat :: path) lc jc ka sa with DOk => check_dbg (1%nat :: path) lc jc kb sb | d => d end
                                    else DFail path 6 ss
                  | None => DFail path 6 ss end
  | PLoop J N inv body k =>
      match loop_ok ss J N inv with
      | Some nhi =>
          let lo := S J in let hi := s_next inv in
          if negb (Z.eqb (s_pc inv) (s_pc ss) && entails_hx lo hi ss (inst inv J (ELit 0)))%bool then DFail path 8 ss else
          dand (check_dbg (0%nat :: path) (Some (LC (s_pc ss) (inst inv J (APC.eaddz (EVar J) 1)) lo hi)) jc body (body_state J N nhi inv))
               (fun _ => check_dbg (1%nat :: path) lc jc k (inst inv J N))
      | None => DFail path 7 ss
      end
  | PNext =>
      match lc with
      | Some (LC h nx lo hi) => if (Z.eqb (s_pc ss) h && Nat.eqb (length (s_regs nx)) 32 && entails_hx lo hi ss nx)%bool then DOk else DFail path 9 ss
      | None => DFail path 9 ss
      end
  | PJoin j js lo karms k =>
      if negb (via_ok ss js lo) then DFail path 11 ss else
      dand (check_dbg (0%nat :: path) lc (JC j js (s_next ss) lo :: jc) karms ss)
           (fun _ => check_dbg (1%nat :: path) lc jc k js)
  | PMerge j =>
      match find_jc j jc with
      | Some (JC j' js b lo) => if (Nat.eqb j j' && Z.eqb (s_pc ss) (s_pc js) && Nat.eqb (length (s_regs js)) 32 && entails_hx lo (s_next js) ss js)%bool then DOk else DFail path 10 ss
      | None => DFail path 10 ss
      end
  end.
End Check.

Section Sound.
Hypothesis IT_ok : itab_sound segs IT.
Hypothesis COPY : forall fx : FPState, @APSX.copy_spec fx segs x_cpy.
Hypothesis FILL : forall fx : FPState, @APSX.fill_spec fx segs x_set two64.
Hypothesis STRLEN : SR.strlen_step_stmt segs x_len ro_lo ro_hi.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

Variable F : list region.
Hypothesis Fvars : forallb (region_vars_lt nx0) F = true.
Hypothesis BRvars : bfacts_vars_lt nx0 = true.
Variable PSS : list SR.post_spec.
Variable M0 : word -> option byte.

Lemma step_req_all : forall st, SR.step_req segs x_len ro_lo ro_hi st.
Proof. intros st. destruct st; cbn; first [exact I | exact STRLEN]. Qed.

Record INV2 (E : env) (ss : sym_state) (R : bvmap 5 word) (Mc : word -> option byte) : Prop := MKINV2 {
  i_regs : regs_ok E (s_regs ss) R;
  i_know : know_ok segs E Mc (s_know ss);
  i_frame : forall a : word, outside E F a -> Mc a = M0 a;
  i_grows : mem_grows M0 Mc;
  i_flat : regions_ok E F;
  i_nx : (nx0 <= s_next ss)%nat;
  i_bf : bfacts_ok E }.

Lemma bfacts_agree : forall E E', env_agree nx0 E E' -> bfacts_ok E -> bfacts_ok E'.
Proof.
  intros E E' Hag H. unfold bfacts_ok in *. unfold bfacts_vars_lt in BRvars.
  rewrite forallb_forall in BRvars. apply Forall_forall. intros bf Hin.
  pose proof (proj1 (Forall_forall _ _) H bf Hin) as X. pose proof (BRvars bf Hin) as V.
  destruct Hag as [Hv Heb].
  destruct bf as [id from to lo hi|id from to lo hi|id es ilo ihi fb|id es ee f|id ej v]; cbn [bfact_ok bfact_vars_lt] in *; unfold bbyte, blen, bbody in *;
    rewrite <- Heb.
  - apply andb_prop in V as [V1 V2].
    rewrite <- (SR.edenot_agree_AP nx0 E E' from (conj Hv Heb) V1), <- (SR.edenot_agree_AP nx0 E E' to (conj Hv Heb) V2). exact X.
  - apply andb_prop in V as [V1 V2].
    rewrite <- (SR.edenot_agree_AP nx0 E E' from (conj Hv Heb) V1), <- (SR.edenot_agree_AP nx0 E E' to (conj Hv Heb) V2). exact X.
  - rewrite <- (SR.edenot_agree_AP nx0 E E' es (conj Hv Heb) V). exact X.
  - apply andb_prop in V as [V1 V2].
    rewrite <- (SR.edenot_agree_AP nx0 E E' es (conj Hv Heb) V1), <- (SR.edenot_agree_AP nx0 E E' ee (conj Hv Heb) V2). exact X.
  - rewrite <- (SR.edenot_agree_AP nx0 E E' ej (conj Hv Heb) V). exact X.
Qed.

Lemma env_agree_sym : forall b E E', env_agree b E E' -> env_agree b E' E.
Proof. intros b E E' [H1 H2]. split; [intros n Hn; symmetry; apply H1; exact Hn | symmetry; exact H2]. Qed.

Lemma estart_F_agree : forall E E' rb rlo rlen,
  env_agree nx0 E E' -> In (rb, rlo, rlen) F ->
  estart E (SA rb rlo) = estart E' (SA rb rlo) /\ elenZ E rlen = elenZ E' rlen.
Proof.
  intros E E' rb rlo rlen Hag Hin. pose proof (proj1 (forallb_forall _ _) Fvars _ Hin) as Hv. cbn beta iota in Hv.
  apply andb_prop in Hv as [Hv Hl].
  unfold estart, elenZ. cbn [a_base a_off]. rewrite (SR.edenot_agree_AP nx0 E E' rb Hag Hv), (SR.edenot_agree_AP nx0 E E' rlen Hag Hl).
  split; reflexivity.
Qed.

Lemma outside_agree : forall E E' a, env_agree nx0 E E' -> outside E' F a -> outside E F a.
Proof.
  intros E E' a Hag H. unfold outside in *. rewrite Forall_forall in *. intros [[rb rlo] rlen] Hin.
  specialize (H _ Hin). cbn beta iota in H |- *. destruct (estart_F_agree E E' rb rlo rlen Hag Hin) as [-> ->]. exact H.
Qed.

Lemma regions_ok_agree : forall E E', env_agree nx0 E E' -> regions_ok E F -> regions_ok E' F.
Proof.
  intros E E' Hag H. unfold regions_ok in *. rewrite Forall_forall in *. intros [[rb rlo] rlen] Hin.
  specialize (H _ Hin). cbn beta iota in H |- *. destruct (estart_F_agree E E' rb rlo rlen Hag Hin) as [<- <-]. exact H.
Qed.

Definition XSTEP_ok : Prop :=
  forallb (region_vars_lt nx0) F = true ->
  bfacts_vars_lt nx0 = true ->
  forall (fx : FPState) (id : nat) ss ss' E R Mc,
    XSTEP F id ss = Some ss' -> INV2 E ss R Mc ->
    exists (fx' : FPState) E' R' Mc',
      env_agree (s_next ss) E E' /\ INV2 E' ss' R' Mc'
      /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                     (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) Mc' (seg_rom segs)).
Hypothesis XSOK : XSTEP_ok.

Definition XSTEP2_ok : Prop :=
  forallb (region_vars_lt nx0) F = true ->
  bfacts_vars_lt nx0 = true ->
  forall (fx : FPState) (id : nat) ss ssa ssb E R Mc,
    XSTEP2 F id ss = Some (ssa, ssb) -> INV2 E ss R Mc ->
    exists (fx' : FPState) E' R' Mc' ss',
      (ss' = ssa \/ ss' = ssb) /\ env_agree (s_next ss) E E' /\ INV2 E' ss' R' Mc'
      /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                     (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) Mc' (seg_rom segs)).
Hypothesis XSOK2 : XSTEP2_ok.

Lemma INV2_reenv : forall b E E' ss ss' R R' Mc,
  INV2 E ss R Mc -> env_agree b E E' -> (nx0 <= b)%nat ->
  regs_ok E' (s_regs ss') R' -> know_ok segs E' Mc (s_know ss') -> (nx0 <= s_next ss')%nat ->
  INV2 E' ss' R' Mc.
Proof.
  intros b E E' ss ss' R R' Mc HI Hag Hb HR HK Hnx.
  pose proof (APS.env_agree_le nx0 b E E' Hag Hb) as Hag0.
  constructor; [exact HR | exact HK | | exact (i_grows _ _ _ _ HI) | | exact Hnx | exact (bfacts_agree E E' Hag0 (i_bf _ _ _ _ HI))].
  - intros a Ha. apply (i_frame _ _ _ _ HI). eapply outside_agree; [exact Hag0 | exact Ha].
  - eapply regions_ok_agree; [exact Hag0 | exact (i_flat _ _ _ _ HI)].
Qed.

Lemma INV2_mem : forall E ss R Mc Mc',
  INV2 E ss R Mc -> know_ok segs E Mc' (s_know ss) ->
  (forall a : word, outside E F a -> Mc' a = Mc a) -> mem_grows Mc Mc' ->
  INV2 E ss R Mc'.
Proof.
  intros E ss R Mc Mc' HI HK Hfr Hgr.
  constructor; [exact (i_regs _ _ _ _ HI) | exact HK | | | exact (i_flat _ _ _ _ HI) | exact (i_nx _ _ _ _ HI) | exact (i_bf _ _ _ _ HI)].
  - intros a Ha. rewrite (Hfr a Ha). exact (i_frame _ _ _ _ HI a Ha).
  - eapply mem_grows_trans; [exact (i_grows _ _ _ _ HI) | exact Hgr].
Qed.

Lemma wden_grows : forall E M w, mem_grows M (SR.wden segs E M w).
Proof.
  intros E M w. induction w as [|g r IH]; cbn [SR.wden]; [apply mem_grows_refl|].
  destruct g as [a0 wd v|db dk sb sk n|db dk n c].
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
  - destruct (rdn segs (SR.wden segs E M r) _ _); [eapply mem_grows_trans; [exact IH | apply wbytes_grows] | exact IH].
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

Definition inF (E : env) (lo n : Z) : Prop :=
  exists rb rlo rlen, In (rb, rlo, rlen) F /\ estart E (SA rb rlo) <= lo /\ lo + n <= estart E (SA rb rlo) + elenZ E rlen.
Definition gin (E : env) (g : SR.went) : Prop :=
  match g with
  | SR.WSt (SA b k) wd _ => 0 < Z.of_nat wd /\ inF E (estart E (SA b k)) (Z.of_nat wd)
  | SR.WCopy db dk _ _ n => 0 < n /\ inF E (estart E (SA db dk)) n
  | SR.WFill db dk n _ => 0 < n /\ inF E (estart E (SA db dk)) n
  end.

Lemma within1X_sound : forall E M kn b k n r,
  know_ok segs E M kn -> regions_ok E F -> 0 <= n < 2 ^ 64 -> In r F -> within1X kn b k n r = true ->
  inF E (estart E (SA b k)) n.
Proof.
  intros E M kn b k n [[rb rlo] rlen] HK HF Hn Hin H. unfold within1X in H.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as HR. cbn beta iota in HR.
  apply orb_prop in H as [H|H].
  - exists rb, rlo, rlen. split; [exact Hin|]. destruct rlen as [m| | | | | | |]; try discriminate H.
    apply andb_true_iff in H as [Hm H]. apply andb_true_iff in Hm as [Hm0 Hm64]. apply Z.leb_le in Hm0. apply Z.ltb_lt in Hm64. unfold two64 in Hm64.
    rewrite (elenZ_litZ E m) in HR by lia. rewrite (elenZ_litZ E m) by lia. unfold SR.within1 in H.
    apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H H1]. apply andb_true_iff in H as [Hb H0].
    apply expr_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. subst rb. unfold estart in *. cbn [a_base a_off] in *. lia.
  - exists rb, rlo, rlen. split; [exact Hin|].
    pose proof (xinside_sound segs E M kn b k (ELit n) rb rlo rlen HK H) as [X1 X2].
    rewrite (elenZ_litZ E n) in X2 by lia. lia.
Qed.

Lemma withinX_sound : forall E M kn b k n,
  know_ok segs E M kn -> regions_ok E F -> withinX kn F b k n = true -> 0 < n /\ inF E (estart E (SA b k)) n.
Proof.
  intros E M kn b k n HK HF H. unfold withinX in H.
  apply andb_prop in H as [H Hex]. apply andb_prop in H as [H0 H64]. apply Z.ltb_lt in H0. apply Z.ltb_lt in H64. unfold two64 in H64.
  split; [exact H0|]. apply existsb_exists in Hex as (r & Hin & Hr). eapply within1X_sound; try eassumption. lia.
Qed.

Lemma went_withinX_sound : forall E M kn w,
  know_ok segs E M kn -> regions_ok E F -> forallb (went_withinX kn F) w = true -> Forall (gin E) w.
Proof.
  intros E M kn w HK HF H. apply Forall_forall. intros g Hg. pose proof (proj1 (forallb_forall _ _) H g Hg) as Hw.
  destruct g as [[b k] wd v|db dk sb sk n|db dk n c]; cbn [went_withinX gin] in *.
  - exact (withinX_sound E M kn b k _ HK HF Hw).
  - exact (withinX_sound E M kn db dk n HK HF Hw).
  - exact (withinX_sound E M kn db dk n HK HF Hw).
Qed.

Lemma wden_frame_sem : forall E M w (a : word),
  Forall (gin E) w -> regions_flat E F -> outside E F a -> SR.wden segs E M w a = M a.
Proof.
  intros E M w a Hw HF Ha. induction w as [|g r IH]; [reflexivity|].
  apply Forall_cons_iff in Hw as [Hg Hr]. specialize (IH Hr).
  assert (REG : forall lo n, inF E lo n -> 0 < n ->
            0 <= lo /\ lo + n <= 2 ^ 64 /\ 0 < n /\ (bv_unsigned a < lo \/ lo + n <= bv_unsigned a)).
  { intros lo n (rb & rlo & rlen & Hin & H1 & H2) Hn.
    pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hfl. pose proof (proj1 (Forall_forall _ _) Ha _ Hin) as Hout.
    cbn beta iota in Hfl, Hout. lia. }
  destruct g as [[b k] wd v|db dk sb sk n|db dk n c]; cbn [SR.wden gin] in *.
  - destruct Hg as [Hn Hg]. destruct (REG _ _ Hg Hn) as (R0 & R1 & RP & R2).
    rewrite wbytes_out; [exact IH | |]; rewrite length_N_to_le_bytes, APSX.adenot_SA, u64_of_Z by lia; lia.
  - destruct Hg as [Hn Hg]. destruct (REG _ _ Hg Hn) as (R0 & R1 & RP & R2).
    destruct (rdn segs (SR.wden segs E M r) (adenot E (SA sb sk)) (Z.to_nat n)) as [bs|] eqn:Hrd; [|exact IH].
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlbs.
    rewrite wbytes_out; [exact IH | |]; rewrite Hlbs, APSX.adenot_SA, Z2Nat.id, u64_of_Z by lia; lia.
  - destruct Hg as [Hn Hg]. destruct (REG _ _ Hg Hn) as (R0 & R1 & RP & R2).
    rewrite wbytes_out; [exact IH | |]; rewrite repeat_length, APSX.adenot_SA, Z2Nat.id, u64_of_Z by lia; lia.
Qed.

Lemma step1_sound : forall (fx : FPState) st ss ss' E R Mc,
  step1 F st ss = Some ss' -> INV2 E ss R Mc ->
  exists (fx' : FPState) E' R' Mc',
    env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV2 E' ss' R' Mc'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) Mc' (seg_rom segs)).
Proof.
  intros fx st ss ss' E R Mc H HI. unfold step1 in H.
  destruct (SR.seg_step segs IT x_cpy x_set x_len ro_lo ro_hi BFUEL st ss []) as [[ss1 w']|] eqn:Hs; [|discriminate].
  destruct (forallb (went_withinX (s_know ss1) F) w') eqn:Hw; [|discriminate]. injection H as <-.
  destruct (SR.seg_step_sound segs IT x_cpy x_set x_len ro_lo ro_hi BFUEL IT_ok COPY FILL fx st ss [] ss1 w' E R Mc
              (step_req_all st) Hs) as (fx' & E' & R' & Hag & Hle & [HR' HK'] & Hms).
  { split; [exact (i_regs _ _ _ _ HI) | cbn [SR.wden]; exact (i_know _ _ _ _ HI)]. }
  exists fx', E', R', (SR.wden segs E' Mc w').
  split; [exact Hag|]. split; [exact Hle|]. split.
  - pose proof (APS.env_agree_le nx0 (s_next ss) E E' Hag (i_nx _ _ _ _ HI)) as Hag0.
    pose proof (regions_ok_agree E E' Hag0 (i_flat _ _ _ _ HI)) as Hfl'.
    constructor; [exact HR' | exact HK' | | | exact Hfl' | pose proof (i_nx _ _ _ _ HI); lia | exact (bfacts_agree E E' Hag0 (i_bf _ _ _ _ HI))].
    + intros a Ha. rewrite (wden_frame_sem E' Mc w' a (went_withinX_sound E' _ (s_know ss1) w' HK' Hfl' Hw) (regions_ok_flat E' F Hfl') Ha).
      apply (i_frame _ _ _ _ HI). eapply outside_agree; [exact Hag0 | exact Ha].
    + eapply mem_grows_trans; [exact (i_grows _ _ _ _ HI) | apply wden_grows].
  - cbn [SR.wden] in Hms. exact Hms.
Qed.

Lemma withinE_sound : forall E M kn b k ne,
  know_ok segs E M kn -> regions_ok E F -> withinE kn F b k ne = true -> inF E (estart E (SA b k)) (elenZ E ne).
Proof.
  intros E M kn b k ne HK HF H. unfold withinE in H. apply existsb_exists in H as ([[rb rlo] rlen] & Hin & Hx).
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as HR. cbn beta iota in HR.
  pose proof (xinside_sound segs E M kn b k ne rb rlo rlen HK Hx) as [X1 X2].
  exists rb, rlo, rlen. split; [exact Hin|]. lia.
Qed.

Lemma fillx_sound : forall (fx : FPState) ss ss' E R Mc,
  fillx F ss = Some ss' -> INV2 E ss R Mc ->
  exists (fx' : FPState) E' R' Mc',
    env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV2 E' ss' R' Mc'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) Mc' (seg_rom segs)).
Proof.
  intros fx ss ss' E R Mc H HI. pose proof (i_regs _ _ _ _ HI) as HR. pose proof (i_know _ _ _ _ HI) as HK.
  unfold fillx in H.
  destruct (Z.eqb (s_pc ss) x_set) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (SR.closed ss []) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (SR.ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (SR.reg ss 11) as [c0| | | | | | |] eqn:H11; try discriminate.
  destruct (split_lit (SR.reg ss 10)) as [db dk] eqn:Hsd.
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hin. rename X0 into Hwr. rename X1 into Hfd. rename X2 into Hdhi'. rename X3 into Hn40.
  apply Z.leb_le in Hc. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hdhi'. unfold two64 in Hdhi'.
  set (ne := SR.reg ss 12) in *. set (c8 := ((c0 mod two64) mod 256)%Z) in *.
  set (k := s_know ss) in *. set (fk := facts_of k) in *.
  pose proof (facts_of_ok segs E Mc k HK) as HKf. fold fk in HKf.
  set (nv := elenZ E ne).
  pose proof (xlo_sound segs E Mc fk ne nlo HKf Hnlo) as Xlo. pose proof (xhi_sound segs E Mc fk ne nhi HKf Hnhi) as Xhi.
  fold nv in Xlo, Xhi. change (bv_unsigned (edenot E ne)) with nv in Xlo, Xhi.
  destruct (APSX.w_flat_x_sound segs E Mc fk db dk ne HKf Hfd) as (Dlo & Dhi & Dpos).
  destruct (APSX.kwritable_x_sound segs E Mc fk k db dk ne HKf HK Hwr) as (Wst & _ & _).
  change (bv_unsigned (edenot E ne)) with nv in Dhi, Dpos. fold nv in Wst.
  set (D := estart E (SA db dk)) in *.

  destruct (SR.ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (SR.reg_sound10 E ss R HR) as R10. pose proof (SR.reg_sound11 E ss R HR) as R11.
  pose proof (SR.reg_sound12 E ss R HR) as R12. fold ne in R12. rewrite H11 in R11. cbn [edenot] in R11.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in R10. change (bv_unsigned (edenot E db) + dk)%Z with D in R10.
  pose proof (xhi_sound segs E Mc fk (SR.reg ss 10) dhi HKf Hdhi) as XD.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in XD. change (bv_unsigned (edenot E db) + dk)%Z with D in XD.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Dpos; lia).
  rewrite u64_of_Z in XD by exact HD64.
  assert (R12' : getr R 12%bv = Z_to_bv 64 nv) by (rewrite R12; symmetry; apply Z_to_bv_bv_unsigned).
  assert (A1 : 0 <= nv) by (clear - Hc Xlo; lia).
  assert (A2 : bv_unsigned (Z_to_bv 64 D) + nv < 2 ^ 64) by (rewrite (u64_of_Z D HD64); clear - XD Hdhi' Xhi; lia).
  assert (A4 : store_ok segs Mc (Z_to_bv 64 D) (Z.to_nat nv) = true) by (apply Wst; clear - A1; lia).
  assert (A5 : bv_unsigned (Z_to_bv 64 c0) < two64) by (unfold two64; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 c0)) as X; exact (proj2 X)).
  destruct (FILL fx Mc (Z_to_bv 64 D) (Z_to_bv 64 c0) nv R (Z_to_bv 64 ret) A1 A2 A4 A5 Hrok R1 R10 R11 R12')
    as (regs' & Hms & Hkept & Ha0).
  assert (Hc8 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c0)) = Z_to_bv 8 c8).
  { subst c8. rewrite APSX.Z_to_bv8_mod. f_equal; try (rewrite Z_to_bv_unsigned; reflexivity). }
  rewrite Hc8 in Hms.
  set (nx := s_next ss) in *.
  exists fx, (APSX.ext_call E nx regs'), regs', (wbytes Mc (Z_to_bv 64 D) (repeat (Z_to_bv 8 c8) (Z.to_nat nv))).
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|]. split; [cbn [SR.after_call s_next]; lia|].
  assert (Fdst : APC.expr_vars_lt nx (SR.reg ss 10) = true) by (unfold SR.reg; apply SR.nth_sr_vars_lt; [exact Fsr0 | lia]).
  assert (Fne : APC.expr_vars_lt nx ne = true) by (unfold ne, SR.reg; apply SR.nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb.
  set (M' := wbytes Mc (Z_to_bv 64 D) (repeat (Z_to_bv 8 c8) (Z.to_nat nv))).
  assert (FILLED : forall i, 0 <= i < nv -> M' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c8)).
  { intros i Hi. subst M'. rewrite <- (u64_of_Z D HD64) at 2. apply APSX.wbytes_fill_at; [rewrite (u64_of_Z D HD64); clear - Dhi; lia | exact Hi]. }
  assert (OUT : forall x : word, bv_unsigned x < D \/ D + nv <= bv_unsigned x -> M' x = Mc x).
  { intros x Hx. subst M'. apply wbytes_out; rewrite ?repeat_length, ?Z2Nat.id, ?u64_of_Z by lia; clear - Hx A1 HD64 Dhi; lia. }
  pose proof (APS.env_agree_le nx0 nx E _ Hag (i_nx _ _ _ _ HI)) as Hag0.
  split.
  -
    assert (ED : estart (APSX.ext_call E nx regs') (SA db dk) = D).
    { unfold estart. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP nx E _ db Hag Fdb). reflexivity. }
    assert (EN : elenZ (APSX.ext_call E nx regs') ne = nv).
    { unfold elenZ. rewrite <- (SR.edenot_agree_AP nx E _ ne Hag Fne). reflexivity. }
    constructor.
    + cbn [SR.after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (SR.reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0.
      rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd). reflexivity.
    + cbn [SR.after_call s_know].
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      constructor.
      * destruct (Z.eqb c8 0) eqn:Hz; cbn [kentry_ok]; unfold flat; fold nv; change (estart E (SA db dk)) with D.
        -- apply Z.eqb_eq in Hz. split; [clear - HD64 Dhi A1; lia|]. intros i Hi. rewrite (FILLED i Hi), Hz. reflexivity.
        -- split; [clear - HD64 Dhi A1; lia|]. intros i Hi. exact (FILLED i Hi).
      * eapply APSX.w_know_ok_havoc; [exact HK | | apply wbytes_grows]. intros x Hx. apply OUT. exact Hx.
    + intros a Ha. cbn [SR.after_call s_know] in *. rewrite OUT.
      * apply (i_frame _ _ _ _ HI). eapply outside_agree; [exact Hag0 | exact Ha].
      * destruct (withinE_sound E Mc fk db dk ne HKf (i_flat _ _ _ _ HI) Hin) as (rb & rlo & rlen & Hrin & H1 & H2).
        fold nv D in H1, H2.
        pose proof (proj1 (Forall_forall _ _) (outside_agree E _ a Hag0 Ha) _ Hrin) as Hout. cbn beta iota in Hout. lia.
    + eapply mem_grows_trans; [exact (i_grows _ _ _ _ HI) | apply wbytes_grows].
    + eapply regions_ok_agree; [exact Hag0 | exact (i_flat _ _ _ _ HI)].
    + cbn [SR.after_call s_next]. pose proof (i_nx _ _ _ _ HI). lia.
    + exact (bfacts_agree E _ Hag0 (i_bf _ _ _ _ HI)).
  - cbn [SR.after_call s_pc]. rewrite Hpc. exact Hms.
Qed.

Lemma same_range_sound : forall E M fk sb sk ne b o n,
  know_ok segs E M fk -> same_range fk sb sk ne b o n = true ->
  estart E (SA sb sk) = estart E (SA b o) /\ elenZ E ne = elenZ E n.
Proof.
  intros E M fk sb sk ne b o n HK H. unfold same_range in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  pose proof (lin_ge0_sound segs E M fk _ _ HK H1) as X1. pose proof (lin_ge0_sound segs E M fk _ _ HK H2) as X2.
  pose proof (lin_ge0_sound segs E M fk _ _ HK H3) as X3. pose proof (lin_ge0_sound segs E M fk _ _ HK H4) as X4.
  cbn [xt_den] in X1, X2, X3, X4. unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

Lemma src_cover_sound : forall E M fk k sb sk ne cv,
  know_ok segs E M fk -> know_ok segs E M k -> src_cover fk k sb sk ne = Some cv ->
  (forall i, 0 <= i < elenZ E ne ->
    exists b : byte, M (Z_to_bv 64 (estart E (SA sb sk) + i)) = Some b
                     /\ match cv with
                        | CovFill c => b = Z_to_bv 8 c
                        | CovUnk => True
                        | CovBlob id => b = nth (Z.to_nat i) (eb E id) (Z_to_bv 8 0)
                        end)
  /\ match cv with CovBlob id => Z.of_nat (length (eb E id)) = elenZ E ne | _ => True end.
Proof.
  intros E M fk k sb sk ne cv HKf HK. induction k as [|K r IH]; intros H; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hr]. cbn [src_cover] in H.
  match type of H with (match ?h with Some x => Some x | None => _ end = _) => destruct h as [x|] eqn:Hhit end;
    [injection H as <- | exact (IH Hr H)].
  clear IH.
  assert (INS : forall b o n, xinside fk sb sk ne b o n = true ->
            forall i, 0 <= i < elenZ E ne -> 0 <= estart E (SA sb sk) + i - estart E (SA b o) < elenZ E n).
  { intros b o n Hx i Hi. pose proof (xinside_sound segs E M fk sb sk ne b o n HKf Hx) as [X1 X2]. lia. }
  destruct K as [[kb kk] w v|[kb kk] l|[kb kk] l bk| | | |[? ?] ?|[? ?] ? [? ?] ?|[kb kk] l fc|[kb kk] l]; try discriminate;
    cbn [kentry_ok] in HKK.
  - destruct (xinside fk sb sk ne kb kk l) eqn:Hx; [|discriminate]. injection Hhit as <-.
    destruct HKK as [Hfl Hall]. split; [|exact I]. intros i Hi. specialize (Hall _ (INS _ _ _ Hx i Hi)).
    replace (estart E (SA kb kk) + (estart E (SA sb sk) + i - estart E (SA kb kk))) with (estart E (SA sb sk) + i) in Hall by lia.
    eexists. split; [exact Hall | reflexivity].
  - destruct (xinside fk sb sk ne kb kk l) eqn:Hx; [|discriminate]. injection Hhit as <-.
    destruct HKK as (Hfl & Hlen & Hall).
    destruct (same_range fk sb sk ne kb kk l) eqn:Hsr.
    + destruct (same_range_sound E M fk sb sk ne kb kk l HKf Hsr) as [Es En].
      split; [| rewrite En; exact Hlen]. intros i Hi. specialize (Hall i ltac:(rewrite <- En; exact Hi)).
      rewrite <- Es in Hall. eexists. split; [exact Hall | reflexivity].
    + split; [|exact I]. intros i Hi. specialize (Hall _ (INS _ _ _ Hx i Hi)).
      replace (estart E (SA kb kk) + (estart E (SA sb sk) + i - estart E (SA kb kk))) with (estart E (SA sb sk) + i) in Hall by lia.
      eexists. split; [exact Hall | exact I].
  - destruct (xinside fk sb sk ne kb kk l) eqn:Hx; [|discriminate]. injection Hhit as <-.
    destruct HKK as [Hfl Hall]. split; [|exact I]. intros i Hi. specialize (Hall _ (INS _ _ _ Hx i Hi)).
    replace (estart E (SA kb kk) + (estart E (SA sb sk) + i - estart E (SA kb kk))) with (estart E (SA sb sk) + i) in Hall by lia.
    eexists. split; [exact Hall | reflexivity].
  - destruct (xinside fk sb sk ne kb kk l) eqn:Hx; [|discriminate]. injection Hhit as <-.
    destruct HKK as [Hfl Hall]. split; [|exact I]. intros i Hi. specialize (Hall _ (INS _ _ _ Hx i Hi)).
    replace (estart E (SA kb kk) + (estart E (SA sb sk) + i - estart E (SA kb kk))) with (estart E (SA sb sk) + i) in Hall by lia.
    destruct (M (Z_to_bv 64 (estart E (SA sb sk) + i))) as [b|] eqn:HM; [|exfalso; exact (Hall eq_refl)].
    exists b. split; [reflexivity | exact I].
Qed.

Lemma src_cover2_sound : forall E M fk k sb sk ne cv,
  know_ok segs E M fk -> know_ok segs E M k -> src_cover2 fk k sb sk ne = Some cv ->
  (forall i, 0 <= i < elenZ E ne ->
    exists b : byte, M (Z_to_bv 64 (estart E (SA sb sk) + i)) = Some b
                     /\ match cv with
                        | CovFill c => b = Z_to_bv 8 c
                        | CovUnk => True
                        | CovBlob id => b = nth (Z.to_nat i) (eb E id) (Z_to_bv 8 0)
                        end)
  /\ match cv with CovBlob id => Z.of_nat (length (eb E id)) = elenZ E ne | _ => True end.
Proof.
  intros E M fk k sb sk ne cv HKf HK H. unfold src_cover2 in H.
  destruct (src_cover fk k sb sk ne) as [c|] eqn:Hc.
  { assert (Ecv : c = cv) by congruence. subst c. exact (src_cover_sound E M fk k sb sk ne cv HKf HK Hc). }
  destruct ne as [n| | | | | | |]; try discriminate.
  destruct (APC.kunk_covered A k (KUnk (SA sb sk) (ELit n))) eqn:Hcov; [|discriminate]. injection H as <-.
  pose proof (APS.kunk_covered_sound segs A SEGS_in_hull HULL_ok E M k _ HK Hcov) as HKU. cbn [kentry_ok] in HKU.
  destruct HKU as [Hfl Hall]. split; [|exact I]. intros i Hi.
  destruct (M (Z_to_bv 64 (estart E (SA sb sk) + i))) as [b|] eqn:HM; [|exfalso; exact (Hall i Hi HM)].
  exists b. split; [reflexivity | exact I].
Qed.

Lemma copyx_sound : forall (fx : FPState) ss ss' E R Mc,
  copyx F ss = Some ss' -> INV2 E ss R Mc ->
  exists (fx' : FPState) E' R' Mc',
    env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV2 E' ss' R' Mc'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) Mc' (seg_rom segs)).
Proof.
  intros fx ss ss' E R Mc H HI. pose proof (i_regs _ _ _ _ HI) as HR. pose proof (i_know _ _ _ _ HI) as HK.
  unfold copyx in H.
  destruct (Z.eqb (s_pc ss) x_cpy) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (SR.closed ss []) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (SR.ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (SR.reg ss 10)) as [db dk] eqn:Hsd. destruct (split_lit (SR.reg ss 11)) as [sb sk] eqn:Hss.
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 11)) as [shi|] eqn:Hshi; [|discriminate].
  destruct (src_cover2 (facts_of (s_know ss)) (s_know ss) sb sk (SR.reg ss 12)) as [cov|] eqn:Hcov; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hin. rename X0 into Hap. rename X1 into Hwr. rename X2 into Hfs. rename X3 into Hfd.
  rename X4 into Hshi'. rename X5 into Hdhi'. rename X6 into Hn40.
  apply Z.leb_le in Hc. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hdhi'. apply Z.ltb_lt in Hshi'. unfold two64 in Hdhi', Hshi'.
  set (ne := SR.reg ss 12) in *.
  set (k := s_know ss) in *. set (fk := facts_of k) in *.
  pose proof (facts_of_ok segs E Mc k HK) as HKf. fold fk in HKf.
  set (nv := elenZ E ne).
  pose proof (xlo_sound segs E Mc fk ne nlo HKf Hnlo) as Xlo. pose proof (xhi_sound segs E Mc fk ne nhi HKf Hnhi) as Xhi.
  change (bv_unsigned (edenot E ne)) with nv in Xlo, Xhi.
  destruct (APSX.w_flat_x_sound segs E Mc fk db dk ne HKf Hfd) as (Dlo & Dhi & Dpos).
  destruct (APSX.w_flat_x_sound segs E Mc fk sb sk ne HKf Hfs) as (Slo & Shi & _).
  destruct (APSX.kwritable_x_sound segs E Mc fk k db dk ne HKf HK Hwr) as (Wst & _ & _).
  pose proof (ranges_apart_x_sound segs E Mc fk db dk ne sb sk ne HKf Hap) as Hapart.
  change (bv_unsigned (edenot E ne)) with nv in Dhi, Dpos, Shi. fold nv in Wst, Hapart.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.

  destruct (src_cover2_sound E Mc fk k sb sk ne cov HKf HK Hcov) as [SRC BLEN]. fold nv S in SRC. fold nv in BLEN.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Dpos; lia).
  assert (HS64 : 0 <= S < 2 ^ 64) by (clear - Slo Shi Dpos; lia).
  destruct (rdn_defined segs Mc (Z.to_nat nv) (Z_to_bv 64 S)) as (bs & Hrd & Hlbs).
  { rewrite u64_of_Z by exact HS64. clear - Shi Dpos; lia. }
  { intros j Hj. rewrite u64_of_Z by exact HS64. destruct (SRC (Z.of_nat j) ltac:(lia)) as (b & Hb & _).
    unfold rd1. rewrite Hb. discriminate. }
  assert (BS : forall j, (j < Z.to_nat nv)%nat ->
            exists b, nth j bs (Z_to_bv 8 0) = b /\ match cov with CovFill c => b = Z_to_bv 8 c | CovUnk => True
                                                               | CovBlob id => b = nth j (eb E id) (Z_to_bv 8 0) end).
  { intros j Hj. destruct (SRC (Z.of_nat j) ltac:(lia)) as (b & Hb & Hbc). exists b.
    split; [| destruct cov; [exact Hbc | exact I | rewrite Nat2Z.id in Hbc; exact Hbc]].
    pose proof (APSX.rdn_nth segs Mc (Z.to_nat nv) (Z_to_bv 64 S) bs j ltac:(rewrite u64_of_Z by exact HS64; clear - Shi Dpos; lia) Hrd Hj) as X.
    rewrite u64_of_Z in X by exact HS64.
    rewrite (rdn_one segs Mc (Z_to_bv 64 (S + Z.of_nat j)) b) in X by (rewrite Hb; reflexivity).
    injection X as ->. reflexivity. }

  destruct (SR.ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (SR.reg_sound10 E ss R HR) as R10. pose proof (SR.reg_sound11 E ss R HR) as R11.
  pose proof (SR.reg_sound12 E ss R HR) as R12. fold ne in R12.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in R10. change (bv_unsigned (edenot E db) + dk)%Z with D in R10.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 11) sb sk Hss) in R11. change (bv_unsigned (edenot E sb) + sk)%Z with S in R11.
  pose proof (xhi_sound segs E Mc fk (SR.reg ss 10) dhi HKf Hdhi) as XD. pose proof (xhi_sound segs E Mc fk (SR.reg ss 11) shi HKf Hshi) as XS.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in XD. change (bv_unsigned (edenot E db) + dk)%Z with D in XD.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 11) sb sk Hss) in XS. change (bv_unsigned (edenot E sb) + sk)%Z with S in XS.
  rewrite u64_of_Z in XD by exact HD64. rewrite u64_of_Z in XS by exact HS64.
  assert (R12' : getr R 12%bv = Z_to_bv 64 nv) by (rewrite R12; symmetry; apply Z_to_bv_bv_unsigned).
  assert (A1 : 0 <= nv) by (clear - Hc Xlo; lia).
  assert (A3 : rdn segs Mc (Z_to_bv 64 S) (length bs) = Some bs) by (rewrite Hlbs; exact Hrd).
  assert (A4 : store_ok segs Mc (Z_to_bv 64 D) (length bs) = true) by (rewrite Hlbs; apply Wst; clear - A1; lia).
  assert (A5 : bv_unsigned (Z_to_bv 64 D) + nv <= bv_unsigned (Z_to_bv 64 S) \/ bv_unsigned (Z_to_bv 64 S) + nv <= bv_unsigned (Z_to_bv 64 D))
    by (rewrite (u64_of_Z D HD64), (u64_of_Z S HS64); exact Hapart).
  assert (A6 : bv_unsigned (Z_to_bv 64 S) + nv < 2 ^ 64) by (rewrite (u64_of_Z S HS64); clear - XS Hshi' Xhi; lia).
  assert (A7 : bv_unsigned (Z_to_bv 64 D) + nv < 2 ^ 64) by (rewrite (u64_of_Z D HD64); clear - XD Hdhi' Xhi; lia).
  destruct (COPY fx Mc (Z_to_bv 64 D) (Z_to_bv 64 S) nv bs R (Z_to_bv 64 ret) A1 Hlbs A3 A4 A5 A6 A7 Hrok R1 R10 R11 R12')
    as (regs' & Hms & Hkept & Ha0).
  set (nx := s_next ss) in *.
  set (M' := wbytes Mc (Z_to_bv 64 D) bs).
  exists fx, (APSX.ext_call E nx regs'), regs', M'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|]. split; [cbn [SR.after_call s_next]; lia|].
  assert (Fdst : APC.expr_vars_lt nx (SR.reg ss 10) = true) by (unfold SR.reg; apply SR.nth_sr_vars_lt; [exact Fsr0 | lia]).
  assert (Fne : APC.expr_vars_lt nx ne = true) by (unfold ne, SR.reg; apply SR.nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb.
  assert (WROTE : forall i, 0 <= i < nv -> M' (Z_to_bv 64 (D + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
  { intros i Hi. subst M'. rewrite <- (u64_of_Z D HD64) at 2. replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia.
    apply wbytes_nth; [rewrite (u64_of_Z D HD64), Hlbs; clear - Dhi A1; lia | rewrite Hlbs; lia]. }
  assert (OUT : forall x : word, bv_unsigned x < D \/ D + nv <= bv_unsigned x -> M' x = Mc x).
  { intros x Hx. subst M'. apply wbytes_out; rewrite ?Hlbs, ?Z2Nat.id, ?u64_of_Z by lia; clear - Hx A1 HD64 Dhi; lia. }
  pose proof (APS.env_agree_le nx0 nx E _ Hag (i_nx _ _ _ _ HI)) as Hag0.
  split.
  - assert (ED : estart (APSX.ext_call E nx regs') (SA db dk) = D).
    { unfold estart. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP nx E _ db Hag Fdb). reflexivity. }
    assert (EN : elenZ (APSX.ext_call E nx regs') ne = nv).
    { unfold elenZ. rewrite <- (SR.edenot_agree_AP nx E _ ne Hag Fne). reflexivity. }
    constructor.
    + cbn [SR.after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (SR.reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0.
      rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd). reflexivity.
    + cbn [SR.after_call s_know].
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      constructor.
      *
        destruct cov as [c| |id].
        -- assert (BYTES : forall i, 0 <= i < nv -> M' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 (c mod 256))).
           { intros i Hi. rewrite (WROTE i Hi). destruct (BS (Z.to_nat i) ltac:(lia)) as (b & Hb & ->%eq_sym) || idtac.
             destruct (BS (Z.to_nat i) ltac:(lia)) as (b & Hb & Hbc). rewrite Hb, Hbc. rewrite <- APSX.Z_to_bv8_mod. reflexivity. }
           destruct (Z.eqb (c mod 256) 0) eqn:Hz; cbn [kentry_ok]; unfold flat; fold nv; change (estart E (SA db dk)) with D.
           ++ apply Z.eqb_eq in Hz. split; [clear - HD64 Dhi A1; lia|]. intros i Hi. rewrite (BYTES i Hi), Hz. reflexivity.
           ++ split; [clear - HD64 Dhi A1; lia|]. intros i Hi. exact (BYTES i Hi).
        -- cbn [kentry_ok]. unfold flat. fold nv. change (estart E (SA db dk)) with D.
           split; [clear - HD64 Dhi A1; lia|]. intros i Hi. rewrite (WROTE i Hi). discriminate.
        -- cbn [kentry_ok]. unfold flat. fold nv. change (estart E (SA db dk)) with D.
           split; [clear - HD64 Dhi A1; lia|]. split; [exact BLEN|].
           intros i Hi. rewrite (WROTE i Hi). destruct (BS (Z.to_nat i) ltac:(lia)) as (b & Hb & Hbc). rewrite Hb, Hbc. reflexivity.
      * eapply APSX.w_know_ok_havoc; [exact HK | | apply wbytes_grows]. intros x Hx. apply OUT. exact Hx.
    + intros a Ha. cbn [SR.after_call s_know] in *. rewrite OUT.
      * apply (i_frame _ _ _ _ HI). eapply outside_agree; [exact Hag0 | exact Ha].
      * destruct (withinE_sound E Mc fk db dk ne HKf (i_flat _ _ _ _ HI) Hin) as (rb & rlo & rlen & Hrin & H1 & H2).
        fold nv D in H1, H2.
        pose proof (proj1 (Forall_forall _ _) (outside_agree E _ a Hag0 Ha) _ Hrin) as Hout. cbn beta iota in Hout. lia.
    + eapply mem_grows_trans; [exact (i_grows _ _ _ _ HI) | apply wbytes_grows].
    + eapply regions_ok_agree; [exact Hag0 | exact (i_flat _ _ _ _ HI)].
    + cbn [SR.after_call s_next]. pose proof (i_nx _ _ _ _ HI). lia.
    + exact (bfacts_agree E _ Hag0 (i_bf _ _ _ _ HI)).
  - cbn [SR.after_call s_pc]. rewrite Hpc. exact Hms.
Qed.

Lemma edenot_closed_noblob : forall e E E',
  APC.expr_vars_lt 0 e = true -> noblob e = true -> edenot E e = edenot E' e.
Proof.
  induction e; intros E E' Hv Hb; cbn [APC.expr_vars_lt noblob edenot] in *; try reflexivity;
    try (apply andb_prop in Hv as [Hv1 Hv2]; apply andb_prop in Hb as [Hb1 Hb2]; rewrite (IHe1 E E' Hv1 Hb1), (IHe2 E E' Hv2 Hb2); reflexivity).
  - apply Nat.ltb_lt in Hv. lia.
  - rewrite (IHe E E' Hv Hb). reflexivity.
  - discriminate.
Qed.

Lemma eval_at_sound : forall E J e v c,
  eval_at J e v = Some c -> bv_unsigned (edenot (APS.upd E J (Z_to_bv 64 v)) e) = c.
Proof.
  intros E J e v c H. unfold eval_at in H.
  destruct (APC.expr_vars_lt 0 (APC.esubst J (ELit v) e) && noblob (APC.esubst J (ELit v) e))%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hv Hb].
  rewrite (edenot_closed_noblob _ Ez E Hv Hb). rewrite APS.esubst_denot. reflexivity.
Qed.

Lemma eval_all_sound : forall fuel E J e v0 c v,
  eval_all fuel J e v0 c = true -> v0 <= v < v0 + Z.of_nat fuel ->
  bv_unsigned (edenot (APS.upd E J (Z_to_bv 64 v)) e) = c.
Proof.
  induction fuel as [|f IH]; intros E J e v0 c v H Hv; [lia|].
  cbn [eval_all] in H. destruct (eval_at J e v0) as [c'|] eqn:He; [|discriminate].
  apply andb_prop in H as [Hc Hr]. apply Z.eqb_eq in Hc. subst c'.
  destruct (Z.eq_dec v v0) as [->|Hne]; [exact (eval_at_sound E J e v0 c He)|].
  eapply IH; [exact Hr | lia].
Qed.

Lemma evalreg_sound : forall E ss R Mc r J ss',
  INV2 E ss R Mc -> evalreg ss r J = Some ss' ->
  INV2 E ss' R Mc /\ s_pc ss' = s_pc ss /\ s_next ss' = s_next ss.
Proof.
  intros E ss R Mc r J ss' HI H. unfold evalreg in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32)%bool eqn:Hr; [|discriminate]. cbn [negb] in H.
  apply andb_prop in Hr as [Hr0 Hr32]. apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32.
  assert (PINNED : forall c, edenot E (SR.reg ss r) = Z_to_bv 64 c ->
            INV2 E (SS (s_pc ss) (sr_upd (s_regs ss) r (ELit c)) [] (s_know ss) (s_next ss)) R Mc).
  { intros c VAL.
    constructor; cbn [s_regs s_know s_next]; try (exact (i_know _ _ _ _ HI)); try (exact (i_frame _ _ _ _ HI));
      try (exact (i_grows _ _ _ _ HI)); try (exact (i_flat _ _ _ _ HI)); try (exact (i_nx _ _ _ _ HI)); try (exact (i_bf _ _ _ _ HI)).
    intros x. pose proof ((i_regs _ _ _ _ HI) x) as HX. unfold sr_get in *.
    destruct (bv_eqb x 0) eqn:Hx0; [exact HX|].
    rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx x) r) as [Hxr|Hxr]; [|exact HX].
    cbn [edenot]. rewrite HX. unfold SR.reg in VAL. rewrite <- Hxr in VAL. exact VAL. }
  destruct (match erange (s_know ss) (SR.reg ss r) with Some (c, c') => if Z.eqb c c' then Some c else None | None => None end) as [pc|] eqn:Hpin.
  { injection H as <-. split; [|split; reflexivity]. apply PINNED.
    destruct (erange (s_know ss) (SR.reg ss r)) as [[pc1 pc2]|] eqn:Her2; [|discriminate].
    destruct (Z.eqb_spec pc1 pc2) as [Hpp|Hpp]; [|discriminate]. injection Hpin as <-.
    pose proof (erange_sound segs E Mc (s_know ss) (SR.reg ss r) pc1 pc2 (i_know _ _ _ _ HI) Her2) as [P1 P2].
    rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (SR.reg ss r))). f_equal. lia. }
  destruct (erange (s_know ss) (EVar J)) as [[lo hi]|] eqn:Her; [|discriminate].
  destruct (Z.leb lo hi && Z.leb (hi - lo) EVAL_MAX)%bool eqn:Hb; [|discriminate]. cbn [negb] in H.
  destruct (eval_at J (SR.reg ss r) lo) as [c|] eqn:He; [|discriminate].
  destruct (eval_all (Z.to_nat (hi - lo + 1)) J (SR.reg ss r) lo c) eqn:Hall; [|discriminate]. injection H as <-.
  apply andb_prop in Hb as [Hlh _]. apply Z.leb_le in Hlh.
  split; [|split; reflexivity].
  pose proof (erange_sound segs E Mc (s_know ss) (EVar J) lo hi (i_know _ _ _ _ HI) Her) as [L1 L2]. cbn [edenot] in L1, L2.
  assert (VAL : edenot E (SR.reg ss r) = Z_to_bv 64 c).
  { pose proof (eval_all_sound _ E J (SR.reg ss r) lo c (bv_unsigned (ev E J)) Hall ltac:(lia)) as X.
    rewrite Z_to_bv_bv_unsigned, APS.upd_same in X. rewrite <- X. symmetry. apply Z_to_bv_bv_unsigned. }
  constructor; cbn [s_regs s_know s_next]; try (exact (i_know _ _ _ _ HI)); try (exact (i_frame _ _ _ _ HI));
    try (exact (i_grows _ _ _ _ HI)); try (exact (i_flat _ _ _ _ HI)); try (exact (i_nx _ _ _ _ HI)); try (exact (i_bf _ _ _ _ HI)).
  intros x. pose proof ((i_regs _ _ _ _ HI) x) as HX. unfold sr_get in *.
  destruct (bv_eqb x 0) eqn:Hx0; [exact HX|].
  rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx x) r) as [Hxr|Hxr]; [|exact HX].
  cbn [edenot]. rewrite HX. unfold SR.reg in VAL. rewrite <- Hxr in VAL. exact VAL.
Qed.

Lemma respell_sound : forall E ss R Mc r e ss',
  INV2 E ss R Mc -> respell ss r e = Some ss' ->
  INV2 E ss' R Mc /\ s_pc ss' = s_pc ss /\ s_next ss' = s_next ss.
Proof.
  intros E ss R Mc r e ss' HI H. unfold respell in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && APC.expr_vars_lt (s_next ss) e)%bool eqn:Hc; [|discriminate]. cbn [negb] in H.
  destruct (erange (s_know ss) (APC.esub (SR.reg ss r) e)) as [[lo hi]|] eqn:Her; [|discriminate].
  destruct lo; try discriminate. destruct hi; try discriminate. injection H as <-.
  pose proof (erange_sound segs E Mc (s_know ss) _ 0 0 (i_know _ _ _ _ HI) Her) as [D1 D2].
  assert (VAL : edenot E (SR.reg ss r) = edenot E e).
  { unfold APC.esub in D1, D2. rewrite mkAlu_denot, alu_sub in D1, D2.
    pose proof (u64_range (edenot E (SR.reg ss r))) as U1. pose proof (u64_range (edenot E e)) as U2.
    unfold v_sub in D1, D2. rewrite Z_to_bv_unsigned in D1, D2.
    apply bv_eq.
    assert (X : bv_wrap 64 (bv_unsigned (edenot E (SR.reg ss r)) - bv_unsigned (edenot E e)) = 0) by lia.
    unfold bv_wrap in X. change (bv_modulus 64) with (2 ^ 64) in X.
    assert (Y : (bv_unsigned (edenot E (SR.reg ss r)) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0) by exact X.
    apply Z.mod_divide in Y; [|lia]. destruct Y as [q Hq]. assert (q = 0) by nia. subst q. lia. }
  split; [|split; reflexivity].
  constructor; cbn [s_regs s_know s_next]; try (exact (i_know _ _ _ _ HI)); try (exact (i_frame _ _ _ _ HI));
    try (exact (i_grows _ _ _ _ HI)); try (exact (i_flat _ _ _ _ HI)); try (exact (i_nx _ _ _ _ HI)); try (exact (i_bf _ _ _ _ HI)).
  intros x. pose proof ((i_regs _ _ _ _ HI) x) as HX. unfold sr_get in *.
  destruct (bv_eqb x 0) eqn:Hx0; [exact HX|].
  rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx x) r) as [Hxr|Hxr]; [|exact HX].
  rewrite HX. unfold SR.reg in VAL. rewrite <- Hxr in VAL. exact VAL.
Qed.

Lemma eval_all_in_sound : forall fuel E J e v0 lo hi v,
  eval_all_in fuel J e v0 lo hi = true -> v0 <= v < v0 + Z.of_nat fuel ->
  lo <= bv_unsigned (edenot (APS.upd E J (Z_to_bv 64 v)) e) <= hi.
Proof.
  induction fuel as [|f IH]; intros E J e v0 lo hi v H Hv; [lia|].
  cbn [eval_all_in] in H. destruct (eval_at J e v0) as [c'|] eqn:He; [|discriminate].
  apply andb_prop in H as [Hc Hr]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct (Z.eq_dec v v0) as [->|Hne]; [rewrite (eval_at_sound E J e v0 c' He); lia|].
  eapply IH; [exact Hr | lia].
Qed.

Lemma factrange_sound : forall E ss R Mc e J lo hi ss',
  INV2 E ss R Mc -> factrange ss e J lo hi = Some ss' ->
  INV2 E ss' R Mc /\ s_pc ss' = s_pc ss /\ s_next ss' = s_next ss /\ s_regs ss' = s_regs ss
  /\ (APC.kn_vars_lt (s_next ss) (s_know ss) = true -> APC.kn_vars_lt (s_next ss') (s_know ss') = true).
Proof.
  intros E ss R Mc e J lo hi ss' HI H. unfold factrange in H.
  destruct (APC.expr_vars_lt (s_next ss) e) eqn:Hve; [|discriminate]. cbn [negb] in H.
  destruct (erange (s_know ss) (EVar J)) as [[jlo jhi]|] eqn:Her; [|discriminate].
  destruct (Z.leb jlo jhi && Z.leb (jhi - jlo) EVAL_MAX)%bool eqn:Hb; [|discriminate]. cbn [negb] in H.
  destruct (eval_all_in (Z.to_nat (jhi - jlo + 1)) J e jlo lo hi) eqn:Hall; [|discriminate]. injection H as <-.
  apply andb_prop in Hb as [Hlh _]. apply Z.leb_le in Hlh.
  pose proof (erange_sound segs E Mc (s_know ss) (EVar J) jlo jhi (i_know _ _ _ _ HI) Her) as [L1 L2]. cbn [edenot] in L1, L2.
  assert (VAL : lo <= bv_unsigned (edenot E e) <= hi).
  { pose proof (eval_all_in_sound _ E J e jlo lo hi (bv_unsigned (ev E J)) Hall ltac:(lia)) as X.
    rewrite Z_to_bv_bv_unsigned, APS.upd_same in X. exact X. }
  split; [| split; [reflexivity | split; [reflexivity | split; [reflexivity|]]]].
  - constructor; cbn [s_regs s_know s_next set_kn]; try (exact (i_regs _ _ _ _ HI)); try (exact (i_frame _ _ _ _ HI));
      try (exact (i_grows _ _ _ _ HI)); try (exact (i_flat _ _ _ _ HI)); try (exact (i_nx _ _ _ _ HI)); try (exact (i_bf _ _ _ _ HI)).
    constructor; [| exact (i_know _ _ _ _ HI)]. cbn [kentry_ok]. exact VAL.
  - intros Hkv. cbn [s_know s_next set_kn APC.kn_vars_lt forallb]. unfold APC.kn_vars_lt in Hkv |- *. cbn [forallb APC.kentry_vars_lt].
    rewrite Hve, Hkv. reflexivity.
Qed.

Lemma kn_remove_ok : forall E M K kn, know_ok segs E M kn -> know_ok segs E M (kn_remove K kn).
Proof. intros E M K kn H. unfold kn_remove. apply Forall_forall. intros X HX. apply filter_In in HX as [HX _]. exact (proj1 (Forall_forall _ _) H X HX). Qed.

Lemma refute1_sound : forall E M kn' e a b,
  know_ok segs E M kn' -> refute1 kn' e a b = true -> a <= bv_unsigned (edenot E e) <= b -> False.
Proof.
  intros E M kn' e a b HK H Hab. unfold refute1 in H. apply orb_prop in H as [H|H].
  - destruct e as [| |op x y| | | | |]; try discriminate. destruct op; try discriminate. destruct y as [z| | | | | | |]; try discriminate.
    destruct z; try discriminate.
    destruct (erange kn' x) as [[xl xh]|] eqn:Hx; [|discriminate].
    pose proof (erange_sound segs E M kn' x xl xh HK Hx) as [L1 L2].
    cbn [edenot] in Hab. rewrite u_slt64 in Hab.
    replace (bv_signed (Z_to_bv 64 0)) with 0 in Hab by reflexivity.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply negb_true_iff in H2.
    + apply Z.leb_le in H1. rewrite (bv_signed_hi (edenot E x)) in Hab by (unfold two63 in H1; lia).
      pose proof (u64_range (edenot E x)) as U.
      destruct (bv_unsigned (edenot E x) - 2 ^ 64 <? 0) eqn:C; [|apply Z.ltb_ge in C; lia].
      apply andb_false_iff in H2 as [H2|H2]; apply Z.leb_gt in H2; lia.
    + apply Z.ltb_lt in H1. rewrite (bv_signed_small (edenot E x)) in Hab by (unfold two63 in H1; lia).
      pose proof (u64_range (edenot E x)) as U.
      destruct (bv_unsigned (edenot E x) <? 0) eqn:C; [apply Z.ltb_lt in C; lia|].
      apply andb_false_iff in H2 as [H2|H2]; apply Z.leb_gt in H2; lia.
  - destruct (erange kn' e) as [[el eh]|] eqn:He; [|discriminate].
    pose proof (erange_sound segs E M kn' e el eh HK He) as [L1 L2].
    apply orb_prop in H as [H|H]; apply Z.ltb_lt in H; lia.
Qed.

Lemma refuted_sound : forall E M kn v p q,
  know_ok segs E M kn -> refuted kn v p q = true -> p <= bv_unsigned (ev E v) <= q -> False.
Proof.
  intros E M kn v p q HK H Hpq. unfold refuted in H. apply existsb_exists in H as (K & Hin & HKr).
  destruct K as [| | | | |e a b| | | |]; try discriminate.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as Hab. cbn [kentry_ok] in Hab.
  eapply (refute1_sound E M (KRange (EVar v) p q :: kn_remove (KRange e a b) kn) e a b); [|exact HKr|exact Hab].
  constructor; [cbn [kentry_ok edenot]; exact Hpq | apply kn_remove_ok; exact HK].
Qed.

Lemma refine_sound : forall E ss R Mc v lo hi ss',
  INV2 E ss R Mc -> refine ss v lo hi = Some ss' ->
  INV2 E ss' R Mc /\ s_pc ss' = s_pc ss /\ s_next ss' = s_next ss /\ s_regs ss' = s_regs ss
  /\ (APC.kn_vars_lt (s_next ss) (s_know ss) = true -> APC.kn_vars_lt (s_next ss') (s_know ss') = true).
Proof.
  intros E ss R Mc v lo hi ss' HI H. unfold refine in H.
  destruct (Nat.ltb v (s_next ss)) eqn:Hv; [|discriminate]. cbn [negb] in H. apply Nat.ltb_lt in Hv.
  set (cur := match erange (s_know ss) (EVar v) with Some r => r | None => (0, two64 - 1) end) in H.
  assert (CUR : fst cur <= bv_unsigned (ev E v) <= snd cur \/ (0 <= bv_unsigned (ev E v) /\ bv_unsigned (ev E v) <= two64 - 1 /\ fst cur <= bv_unsigned (ev E v) <= snd cur)).
  { subst cur. destruct (erange (s_know ss) (EVar v)) as [[a b]|] eqn:Her.
    - left. pose proof (erange_sound segs E Mc (s_know ss) (EVar v) a b (i_know _ _ _ _ HI) Her) as X. cbn [edenot fst snd] in X |- *. exact X.
    - right. pose proof (u64_range (ev E v)) as U. cbn [fst snd]. unfold two64. lia. }
  pose proof (u64_range (ev E v)) as U.
  assert (CUR' : Z.max (fst cur) 0 <= bv_unsigned (ev E v) <= Z.min (snd cur) (two64 - 1)) by (unfold two64 in *; lia).
  clearbody cur.
  destruct (Z.leb (Z.max (fst cur) 0) lo && Z.leb lo hi && Z.leb hi (Z.min (snd cur) (two64 - 1)))%bool eqn:Hb; [|discriminate]. cbn [negb] in H.
  match type of H with (if negb ?c then _ else _) = _ => destruct c eqn:Hr end; [|discriminate]. cbn [negb] in H. injection H as <-.
  apply andb_prop in Hr as [Hlo Hhi].
  assert (VAL : lo <= bv_unsigned (ev E v) <= hi).
  { split.
    - apply orb_prop in Hlo as [Hlo|Hlo]; [apply Z.eqb_eq in Hlo; lia|].
      destruct (Z_lt_le_dec (bv_unsigned (ev E v)) lo) as [Hlt|Hge]; [|lia].
      exfalso. eapply (refuted_sound E Mc (s_know ss) v); [exact (i_know _ _ _ _ HI) | exact Hlo | lia].
    - apply orb_prop in Hhi as [Hhi|Hhi]; [apply Z.eqb_eq in Hhi; lia|].
      destruct (Z_lt_le_dec hi (bv_unsigned (ev E v))) as [Hlt|Hge]; [|lia].
      exfalso. eapply (refuted_sound E Mc (s_know ss) v); [exact (i_know _ _ _ _ HI) | exact Hhi | lia]. }
  split; [| split; [reflexivity | split; [reflexivity | split; [reflexivity|]]]].
  - constructor; cbn [s_regs s_know s_next set_kn]; try (exact (i_regs _ _ _ _ HI)); try (exact (i_frame _ _ _ _ HI));
      try (exact (i_grows _ _ _ _ HI)); try (exact (i_flat _ _ _ _ HI)); try (exact (i_nx _ _ _ _ HI)); try (exact (i_bf _ _ _ _ HI)).
    constructor; [| exact (i_know _ _ _ _ HI)]. cbn [kentry_ok edenot]. exact VAL.
  - intros Hkv. cbn [s_know s_next set_kn APC.kn_vars_lt forallb]. unfold APC.kn_vars_lt in Hkv |- *. cbn [forallb APC.kentry_vars_lt APC.expr_vars_lt].
    rewrite Hkv. rewrite (proj2 (Nat.ltb_lt _ _) Hv). reflexivity.
Qed.

Lemma find_blob_cover_sound : forall fk k rb rk kb kk id,
  find_blob_cover fk k rb rk = Some (kb, kk, id) ->
  exists len, In (KBlob (SA kb kk) len id) k /\ xinside fk rb rk (ELit 1) kb kk len = true.
Proof.
  intros fk k rb rk kb kk id. induction k as [|K r IH]; cbn [find_blob_cover]; intros H; [discriminate|].
  assert (REST : find_blob_cover fk r rb rk = Some (kb, kk, id) ->
                 exists len, In (KBlob (SA kb kk) len id) (K :: r) /\ xinside fk rb rk (ELit 1) kb kk len = true).
  { intros H'. destruct (IH H') as (len & Hin & Hx). exists len. split; [right; exact Hin | exact Hx]. }
  destruct K as [[? ?] ? ?|[? ?] ?|[b o] len id'| | | |[? ?] ?|[? ?] ? [? ?] ?|[? ?] ? ?|[? ?] ?]; try exact (REST H).
  destruct (xinside fk rb rk (ELit 1) b o len) eqn:Hx; [|exact (REST H)].
  injection H as <- <- <-. exists len. split; [left; reflexivity | exact Hx].
Qed.

Lemma find_bfact_sound : forall fk brs id rb rk kb kk lo hi,
  find_bfact fk brs id rb rk kb kk = Some (lo, hi) ->
  exists from to, In (BRange id from to lo hi) brs
    /\ lin_ge0 fk [(rb, rk)] [(kb, kk); (from, 0)] = true /\ lin_ge0 fk [(kb, kk); (to, 0)] [(rb, rk + 1)] = true
    /\ 0 <= lo /\ hi <= 255.
Proof.
  intros fk brs id rb rk kb kk lo hi. induction brs as [|bf r IH]; cbn [find_bfact]; intros H; [discriminate|].
  destruct bf as [id' from to lo' hi'|? ? ? ? ?|? ? ? ? ?|? ? ? ?|? ? ?];
    [| destruct (IH H) as (f' & t' & Hin & X); exists f', t'; split; [right; exact Hin | exact X]
     | destruct (IH H) as (f' & t' & Hin & X); exists f', t'; split; [right; exact Hin | exact X]
     | destruct (IH H) as (f' & t' & Hin & X); exists f', t'; split; [right; exact Hin | exact X]
     | destruct (IH H) as (f' & t' & Hin & X); exists f', t'; split; [right; exact Hin | exact X]].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end.
  - injection H as <- <-. repeat (apply andb_prop in Hc as [Hc ?X]).
    apply Nat.eqb_eq in Hc. subst id'. apply Z.leb_le in X. apply Z.leb_le in X0.
    exists from, to. split; [left; reflexivity|]. split; [exact X2|]. split; [exact X1|]. lia.
  - destruct (IH H) as (from' & to' & Hin & X). exists from', to'. split; [right; exact Hin | exact X].
Qed.

Lemma lb_range_sound : forall E Mc fk id rb rk kb kk lo hi,
  lb_range fk id rb rk kb kk = (lo, hi) ->
  Forall (kentry_ok segs E Mc) fk -> bfacts_ok E ->
  forall j, j = estart E (SA rb rk) - estart E (SA kb kk) -> 0 <= j -> j < blen E id ->
  lo <= bbyte E id j <= hi /\ 0 <= lo /\ hi <= 255.
Proof.
  intros E Mc fk id rb rk kb kk lo hi H HKf HBF j Hj Hj0 Hjl. unfold lb_range in H.
  pose proof (bv_unsigned_in_range _ (nth (Z.to_nat j) (eb E id) (Z_to_bv 8 0))) as U. change (bv_modulus 8) with 256 in U.
  destruct (find_bfact fk BR id rb rk kb kk) as [[lo' hi']|] eqn:Hbf.
  - injection H as -> ->.
    destruct (find_bfact_sound fk BR id rb rk kb kk lo hi Hbf) as (from & to & Hbin & L1 & L2 & Hlo & Hhi).
    pose proof (lin_ge0_sound segs E Mc fk _ _ HKf L1) as Y1. pose proof (lin_ge0_sound segs E Mc fk _ _ HKf L2) as Y2.
    cbn [xt_den] in Y1, Y2. unfold estart in Hj. cbn [a_base a_off] in Hj.
    pose proof (proj1 (Forall_forall _ _) HBF _ Hbin) as BF. cbn [bfact_ok] in BF.
    split; [| lia]. apply BF; [lia |]. unfold blen in Hjl. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
  - injection H as <- <-. unfold bbyte. lia.
Qed.

Lemma loadbyte_sound : forall (fx : FPState) ss ss' E R Mc,
  loadbyte ss = Some ss' -> INV2 E ss R Mc ->
  exists E' R', env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV2 E' ss' R' Mc
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                   (@mkst fx R' (Z_to_bv 64 (s_pc ss')) Mc (seg_rom segs)).
Proof.
  intros fx ss ss' E R Mc H HI. pose proof (i_regs _ _ _ _ HI) as HR. pose proof (i_know _ _ _ _ HI) as HK.
  unfold loadbyte in H.
  destruct (itab_lookup IT (s_pc ss)) as [i|] eqn:Hit; [|discriminate].
  pose proof (IT_ok _ _ Hit) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz. injection Hen as ->.
  destruct (lbu_of i) as [[[rd rs] imm]|] eqn:Hl; [|discriminate]. apply lbu_of_sound in Hl. subst i.
  destruct (bv_eqb rd 0) eqn:Hrd0; [discriminate|].
  destruct (SR.closed ss []) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  match type of H with (match find_blob_cover ?fk ?kn ?rb ?rk with _ => _ end) = _ =>
    destruct (find_blob_cover fk kn rb rk) as [[[kb kk] id]|] eqn:Hcov; [|discriminate];
    set (RB := rb) in *; set (RK := rk) in * end.
  match type of H with (let '(lo, hi) := lb_range ?fk ?id ?rb ?rk ?kb ?kk in _) = _ =>
    destruct (lb_range fk id rb rk kb kk) as [lo hi] eqn:Hbf end.
  injection H as <-.
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (nx := s_next ss) in *.
  pose proof (facts_of_ok segs E Mc k HK) as HKf. fold fk in HKf.
  destruct (find_blob_cover_sound fk k RB RK kb kk id Hcov) as (len & Hin & Hx).
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKB. cbn [kentry_ok] in HKB. destruct HKB as (Hfl & Hlen & Hall).
  destruct (xinside_sound segs E Mc fk RB RK (ELit 1) kb kk len HKf Hx) as [X1 X2]. rewrite elenZ_lit in X2. rewrite Z.mod_small in X2 by lia.
  set (S := estart E (SA RB RK)) in *. set (B := estart E (SA kb kk)) in *.
  assert (ES : S = bv_unsigned (edenot E RB) + RK) by reflexivity.
  assert (EB : B = bv_unsigned (edenot E kb) + kk) by reflexivity.
  set (j := S - B).
  assert (Hj : 0 <= j < elenZ E len) by (subst j; lia).
  pose proof (Hall j Hj) as HM. replace (B + j) with S in HM by lia.
  set (b := nth (Z.to_nat j) (eb E id) (Z_to_bv 8 0)) in *.
  destruct Hfl as (F1 & F2 & F3 & F4).
  assert (HS64 : 0 <= S < 2 ^ 64) by lia.

  assert (RANGE : lo <= bv_unsigned b <= hi).
  { destruct (lb_range_sound E Mc fk id RB RK kb kk lo hi Hbf HKf (i_bf _ _ _ _ HI) j ltac:(reflexivity) ltac:(lia)
               ltac:(unfold blen; rewrite Hlen; lia)) as (R1 & _ & _). exact R1. }

  assert (ADDR : v_addi (getr R rs) (bv_signed imm) = Z_to_bv 64 S).
  { rewrite (HR rs). rewrite <- to_saddr_denot. fold RB RK.
    rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (to_saddr (sr_get (s_regs ss) rs) (bv_signed imm)))).
    f_equal. change (adenot E (to_saddr (sr_get (s_regs ss) rs) (bv_signed imm))) with (adenot E (SA RB RK)).
    apply (flat_u E (SA RB RK) 1). unfold flat. fold S. lia. }
  assert (RDN : rdn segs Mc (v_addi (getr R rs) (bv_signed imm)) 1%nat = Some [b]).
  { rewrite ADDR. apply rdn_one. rewrite HM. reflexivity. }
  pose proof (PropExec.step_lbu segs R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs) w rd rs imm b Hf Hec Hd RDN) as STEP.
  rewrite Hrd0 in STEP.
  set (v := Z_to_bv 64 (bv_unsigned b)) in *.
  exists (APS.upd E nx v), (regupd R rd v).
  pose proof (APS.upd_agree E nx v) as Hag.
  pose proof (APS.env_agree_le nx0 nx E _ Hag (i_nx _ _ _ _ HI)) as Hag0.
  split; [exact Hag|]. split; [cbn [s_next]; lia|]. split.
  - constructor; cbn [s_regs s_know s_next s_pc].
    +
      intros x. pose proof (regs_ok_upd E (s_regs ss) R rd v (EVar nx) HR) as RU. rewrite Hrd0 in RU.
      assert (HRU : regs_ok (APS.upd E nx v) (sr_upd (s_regs ss) (ridx rd) (EVar nx)) (regupd R rd v)).
      { intros y. unfold sr_get. destruct (bv_eqb y 0) eqn:Hy0.
        - assert (y = 0%bv) by (apply bv_eq; unfold bv_eqb in Hy0; lia). subst y.
          unfold getr. rewrite Hy0. reflexivity.
        - rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx y) (ridx rd)) as [Hyr|Hyr].
          + apply ridx_inj in Hyr. subst y. cbn [edenot]. rewrite APS.upd_at.
            rewrite getr_same; [reflexivity|]. intro Hc. subst rd. rewrite bv_eqb_refl in Hrd0. discriminate.
          + assert (Hyr' : y <> rd) by (intro Hc; subst; exact (Hyr eq_refl)).
            rewrite getr_other by exact Hyr'. rewrite (HR y). unfold sr_get. rewrite Hy0.
            first [apply (SR.edenot_agree_AP nx E _ _ Hag) | symmetry; apply (SR.edenot_agree_AP nx E _ _ Hag)]. apply SR.nth_sr_vars_lt; [exact Fsr0 | ].
            apply ridx_range. }
      exact (HRU x).
    +
      constructor.
      * cbn [kentry_ok edenot]. rewrite APS.upd_at. subst v. rewrite u64_of_Z; [exact RANGE | pose proof (u8_range b); lia].
      * eapply APS.know_ok_agree'; [exact Hag | exact Fkn0 | exact HK].
    + intros a0 Ha. apply (i_frame _ _ _ _ HI). eapply outside_agree; [exact Hag0 | exact Ha].
    + exact (i_grows _ _ _ _ HI).
    + eapply regions_ok_agree; [exact Hag0 | exact (i_flat _ _ _ _ HI)].
    + pose proof (i_nx _ _ _ _ HI). lia.
    + exact (bfacts_agree _ _ Hag0 (i_bf _ _ _ _ HI)).
  - cbn [s_pc]. eapply mst_step; [reflexivity | exact STEP | ].
    replace (v_addi (Z_to_bv 64 (s_pc ss)) 4) with (Z_to_bv 64 (s_pc ss + 4)); [apply mst_refl|].
    unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma piece_defined : forall E M K b o n,
  kentry_ok segs E M K -> piece_of K = Some (b, o, n) ->
  forall x : Z, estart E (SA b o) <= x < estart E (SA b o) + elenZ E n -> APS.in_hull A x = false ->
    0 <= x < 2 ^ 64 /\ M (Z_to_bv 64 x) <> None.
Proof.
  intros E M K b o n HK HP x Hx Hh.
  assert (ZF : forall (P : option byte -> Prop),
            flat E (SA b o) (elenZ E n) /\ (forall i, 0 <= i < elenZ E n -> P (M (Z_to_bv 64 (estart E (SA b o) + i)))) ->
            (forall y, P y -> y <> None) -> 0 <= x < 2 ^ 64 /\ M (Z_to_bv 64 x) <> None).
  { intros P [Hfl Hall] HPn. destruct Hfl as (F1 & F2 & F3 & F4). split; [lia|].
    replace x with (estart E (SA b o) + (x - estart E (SA b o))) by lia. apply HPn. apply Hall. lia. }
  destruct K as [[kb kk] w v|[kb kk] l|[kb kk] l bk| | | |[? ?] ?|[? ?] ? [? ?] ?|[kb kk] l fc|[kb kk] l]; cbn [piece_of] in HP; try discriminate;
    injection HP as <- <- <-; cbn [kentry_ok] in HK.
  -
    destruct HK as (Hw & Hfl & Hrd). pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite elenZ_lit in Hx. rewrite Z.mod_small in Hx by lia. split; [lia|].
    pose proof (APS.rdn_bytes_some segs A SEGS_in_hull M _ w _ Hrd (Z_to_bv 64 x)) as X.
    rewrite Hu in X. rewrite (u64_of_Z x) in X by lia. apply X; [lia | exact Hh].
  - eapply (ZF (fun y => y = Some (Z_to_bv 8 0))); [exact HK | intros y ->; discriminate].
  - destruct HK as (Hfl & Hlen & Hall).
    eapply (ZF (fun y => exists b0, y = Some b0)); [split; [exact Hfl | intros i Hi; eexists; apply Hall; exact Hi] | intros y [b0 ->]; discriminate].
  - eapply (ZF (fun y => y = Some (Z_to_bv 8 fc))); [exact HK | intros y ->; discriminate].
  - eapply (ZF (fun y => y <> None)); [exact HK | intros y Hy; exact Hy].
Qed.

Lemma find_piece_sound : forall E M allkn k tb pos b o n,
  know_ok segs E M allkn -> know_ok segs E M k -> find_piece allkn k tb pos = Some (b, o, n) ->
  xt_den E pos = estart E (SA b o)
  /\ forall x : Z, estart E (SA b o) <= x < estart E (SA b o) + elenZ E n -> APS.in_hull A x = false ->
       0 <= x < 2 ^ 64 /\ M (Z_to_bv 64 x) <> None.
Proof.
  intros E M allkn k tb pos b o n HA HK. induction k as [|K r IH]; intros H; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hr]. cbn [find_piece] in H.
  destruct (piece_of K) as [[[kb ko] kn']|] eqn:HP; [|exact (IH Hr H)].
  destruct (shares_var tb kb && lin_ge0 allkn pos [(kb, ko)] && lin_ge0 allkn [(kb, ko)] pos)%bool eqn:Hc; [|exact (IH Hr H)].
  injection H as <- <- <-. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [_ H1].
  pose proof (lin_ge0_sound segs E M allkn _ _ HA H1) as L1. pose proof (lin_ge0_sound segs E M allkn _ _ HA H2) as L2.
  cbn [xt_den] in L1, L2. split; [unfold estart; cbn [a_base a_off]; lia|].
  exact (piece_defined E M K kb ko kn' HKK HP).
Qed.

Lemma chain_cover_sound : forall fuel E M kn tb pos goal (lo : Z),
  know_ok segs E M kn -> chain_cover fuel kn tb pos goal = true ->
  (forall x : Z, lo <= x < xt_den E pos -> APS.in_hull A x = false -> 0 <= x < 2 ^ 64 /\ M (Z_to_bv 64 x) <> None) ->
  forall x : Z, lo <= x < xt_den E goal -> APS.in_hull A x = false -> 0 <= x < 2 ^ 64 /\ M (Z_to_bv 64 x) <> None.
Proof.
  induction fuel as [|f IH]; intros E M kn tb pos goal lo HK H Hcov x Hx Hh; [discriminate|].
  cbn [chain_cover] in H. destruct (lin_ge0 kn pos goal) eqn:Hge.
  - pose proof (lin_ge0_sound segs E M kn _ _ HK Hge) as L. apply Hcov; [lia | exact Hh].
  - destruct (find_piece kn kn tb pos) as [[[b o] n]|] eqn:Hf; [|discriminate].
    destruct (find_piece_sound E M kn kn tb pos b o n HK HK Hf) as [Hpos Hpiece].
    eapply (IH E M kn tb _ goal lo HK H); [|exact Hx | exact Hh].
    intros y Hy Hhy. cbn [xt_den] in Hy. cbn [edenot] in Hy.
    destruct (Z.lt_ge_cases y (xt_den E pos)) as [Hlt|Hge2].
    + apply Hcov; [lia | exact Hhy].
    + apply Hpiece; [|exact Hhy]. unfold elenZ, estart in *. cbn [a_base a_off] in *. lia.
Qed.

Lemma kunk_chain_sound : forall E M kn b o n,
  know_ok segs E M kn -> kunk_chain kn b o n = true -> kentry_ok segs E M (KUnk (SA b o) n).
Proof.
  intros E M kn b o n HK H. unfold kunk_chain in H.
  apply andb_prop in H as [H Hcc]. apply andb_prop in H as [H Hhull]. apply andb_prop in H as [Hfl Hoff]. apply Z.leb_le in Hhull.
  destruct (APSX.w_flat_x_sound segs E M kn b o n HK Hfl) as (F1 & F2 & F3).
  pose proof (ranges_apart_x_sound segs E M kn _ _ _ _ _ _ HK Hoff) as AP0.
  rewrite (elenZ_lit E (APC.img_hi A - APC.img_lo A)) in AP0. rewrite Z.mod_small in AP0 by (pose proof HULL_ok as HU; unfold APS.hull_ok, APC.KHI in HU; lia).
  unfold estart in AP0 at 2 3. cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
  cbn [kentry_ok]. split; [unfold flat, elenZ in *; lia|].
  intros i Hi.
  assert (Hh : APS.in_hull A (estart E (SA b o) + i) = false).
  { unfold APS.in_hull. apply andb_false_iff. unfold elenZ in *.
    destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
  refine (proj2 (chain_cover_sound _ E M kn b [(b, o)] [(b, o); (n, 0)] (estart E (SA b o)) HK Hcc _ _ _ Hh)).
  - intros x Hx. cbn [xt_den] in Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. lia.
  - cbn [xt_den]. unfold estart, elenZ in *. cbn [a_base a_off] in *. lia.
Qed.

Lemma tmpl_chain_sound : forall E M kn K, know_ok segs E M kn -> tmpl_chain kn K = true -> kentry_ok segs E M K.
Proof.
  intros E M kn K HK H. destruct K as [| | | | | | | | |[b o] n]; try discriminate. cbn [tmpl_chain] in H.
  destruct (existsb _ kn); [discriminate|]. exact (kunk_chain_sound E M kn b o n HK H).
Qed.

Lemma kentry_ok_agree1 : forall b E E' M K,
  env_agree b E E' -> APC.kentry_vars_lt b K = true -> kentry_ok segs E M K -> kentry_ok segs E' M K.
Proof.
  intros b E E' M K Hag Hv HK.
  assert (X : know_ok segs E' M [K]); [|exact (proj1 (proj1 (Forall_cons_iff _ _ _) X))].
  eapply APS.know_ok_agree'; [exact Hag | cbn [APC.kn_vars_lt AP.kn_vars_lt]; rewrite Hv; reflexivity | constructor; [exact HK | constructor]].
Qed.

Lemma entails_h_sound2 : forall lo hi E ss T R Mc,
  INV2 E ss R Mc -> entails_h lo hi ss T = true -> (nx0 <= lo)%nat -> length (s_regs T) = 32%nat ->
  (nx0 <= s_next T)%nat ->
  exists E', env_agree lo E E' /\ (forall n, (hi <= n)%nat -> ev E' n = ev E n) /\ INV2 E' T R Mc
             /\ s_pc T = s_pc ss.
Proof.
  intros lo hi E ss T R Mc HI H Hlo Hlen HnxT. unfold entails_h in H. apply andb_prop in H as [H HkvT]. unfold APC.entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc. cbn [APC.pc APC.a_ss acs_of set_kn s_pc] in Hpc.
  match goal with Hr : APC.regs_match_h _ _ _ _ _ = true |- _ => rename Hr into Hregs; cbn [APC.a_ss acs_of set_kn s_regs] in Hregs end.
  match goal with Hk : APC.kn_incl_h _ _ (APC.kn (acs_of _)) = true |- _ => rename Hk into Hkn; cbn [APC.kn APC.a_ss acs_of set_kn s_know] in Hkn end.
  match goal with Hk : APC.kn_vars_lt lo (APC.kn (acs_of _)) = true |- _ => rename Hk into Hkv; cbn [APC.kn APC.a_ss acs_of set_kn s_know] in Hkv end.
  set (E' := APS.henv lo hi E (s_regs ss) (s_regs T)).
  exists E'. split; [apply APS.henv_agree|]. split; [intros; apply APS.henv_high; assumption|].
  split; [|symmetry; exact Hpc].
  eapply (INV2_reenv lo); [exact HI | apply APS.henv_agree | exact Hlo | | | exact HnxT].
  - apply APS.regs_match_h_sound; [exact Hregs | exact Hlen | exact (i_regs _ _ _ _ HI)].
  -
    pose proof (APS.kn_incl_h_sound segs A SEGS_in_hull HULL_ok E Mc (s_know ss) _ (i_know _ _ _ _ HI) Hkn) as HKrest.
    apply Forall_forall. intros K Hin.
    pose proof (proj1 (forallb_forall _ _) ltac:(rewrite <- APS.kn_vars_lt_eq in HkvT || exact HkvT; exact HkvT) K Hin) as HvK || idtac.
    assert (HvK' : APC.kentry_vars_lt lo K = true).
    { clear - HkvT Hin. induction (s_know T) as [|K0 r IH]; [destruct Hin|].
      cbn [APC.kn_vars_lt] in HkvT. apply andb_prop in HkvT as [H0 Hr]. destruct Hin as [<-|Hin]; [exact H0 | exact (IH Hr Hin)]. }
    destruct (tmpl_chain (s_know ss) K) eqn:Htc.
    + eapply kentry_ok_agree1; [apply APS.henv_agree | exact HvK' |].
      eapply tmpl_chain_sound; [exact (i_know _ _ _ _ HI) | exact Htc].
    + eapply kentry_ok_agree1; [apply APS.henv_agree | exact HvK' |].
      apply (proj1 (Forall_forall _ _) HKrest K). unfold tmpl_rest. apply filter_In. split; [exact Hin | rewrite Htc; reflexivity].
Qed.

Lemma entails_h_sound2' : forall lo hi E ss T R Mc,
  INV2 E ss R Mc -> entails_h lo hi ss T = true -> (nx0 <= lo)%nat -> length (s_regs T) = 32%nat ->
  (nx0 <= s_next T)%nat ->
  let E' := APS.henv lo hi E (s_regs ss) (s_regs T) in
  env_agree lo E E' /\ (forall n, (hi <= n)%nat -> ev E' n = ev E n) /\ INV2 E' T R Mc /\ s_pc T = s_pc ss
  /\ APC.regs_match_h lo hi [] (s_regs ss) (s_regs T) = true.
Proof.
  intros lo hi E ss T R Mc HI H Hlo Hlen HnxT. cbv zeta.
  assert (Hregs : APC.regs_match_h lo hi [] (s_regs ss) (s_regs T) = true).
  { unfold entails_h in H. apply andb_prop in H as [H _]. unfold APC.entails_h in H.
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
    match goal with Hr : APC.regs_match_h _ _ _ _ _ = true |- _ => cbn [APC.a_ss acs_of set_kn s_regs] in Hr; exact Hr end. }
  unfold entails_h in H. apply andb_prop in H as [H HkvT]. unfold APC.entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc. cbn [APC.pc APC.a_ss acs_of set_kn s_pc] in Hpc.
  match goal with Hk : APC.kn_incl_h _ _ (APC.kn (acs_of _)) = true |- _ => rename Hk into Hkn; cbn [APC.kn APC.a_ss acs_of set_kn s_know] in Hkn end.
  match goal with Hk : APC.kn_vars_lt lo (APC.kn (acs_of _)) = true |- _ => rename Hk into Hkv; cbn [APC.kn APC.a_ss acs_of set_kn s_know] in Hkv end.
  set (E' := APS.henv lo hi E (s_regs ss) (s_regs T)).
  split; [apply APS.henv_agree|]. split; [intros; apply APS.henv_high; assumption|].
  split; [|split; [symmetry; exact Hpc | exact Hregs]].
  eapply (INV2_reenv lo); [exact HI | apply APS.henv_agree | exact Hlo | | | exact HnxT].
  - apply APS.regs_match_h_sound; [exact Hregs | exact Hlen | exact (i_regs _ _ _ _ HI)].
  - pose proof (APS.kn_incl_h_sound segs A SEGS_in_hull HULL_ok E Mc (s_know ss) _ (i_know _ _ _ _ HI) Hkn) as HKrest.
    apply Forall_forall. intros K Hin.
    assert (HvK' : APC.kentry_vars_lt lo K = true).
    { clear - HkvT Hin. induction (s_know T) as [|K0 r IH]; [destruct Hin|].
      cbn [APC.kn_vars_lt] in HkvT. apply andb_prop in HkvT as [H0 Hr]. destruct Hin as [<-|Hin]; [exact H0 | exact (IH Hr Hin)]. }
    destruct (tmpl_chain (s_know ss) K) eqn:Htc.
    + eapply kentry_ok_agree1; [apply APS.henv_agree | exact HvK' |].
      eapply tmpl_chain_sound; [exact (i_know _ _ _ _ HI) | exact Htc].
    + eapply kentry_ok_agree1; [apply APS.henv_agree | exact HvK' |].
      apply (proj1 (Forall_forall _ _) HKrest K). unfold tmpl_rest. apply filter_In. split; [exact Hin | rewrite Htc; reflexivity].
Qed.

Lemma kn_vars_lt_In : forall b k K, APC.kn_vars_lt b k = true -> In K k -> APC.kentry_vars_lt b K = true.
Proof.
  intros b k K. induction k as [|K0 r IH]; intros H Hin; [destruct Hin|].
  cbn [APC.kn_vars_lt] in H. apply andb_prop in H as [H0 Hr]. destruct Hin as [<-|Hin]; [exact H0 | exact (IH Hr Hin)].
Qed.
Definition cell_env (kn : list kentry) (Eb : env) (E1 : env) (cs : list (saddr * nat * nat)) : env :=
  fold_right (fun x E2 => match x with (a, w, c) =>
                match cell_value kn a w with Some e => APS.upd E2 c (edenot Eb e) | None => E2 end end) E1 cs.

Lemma cell_env_eb : forall kn Eb E1 cs, eb (cell_env kn Eb E1 cs) = eb E1.
Proof. intros kn Eb E1 cs. induction cs as [|[[a w] c] r IH]; cbn [cell_env fold_right]; [reflexivity|].
  fold (cell_env kn Eb E1 r). destruct (cell_value kn a w); [cbn [APS.upd eb]; exact IH | exact IH]. Qed.

Lemma cell_env_other : forall kn Eb E1 cs n,
  ~ In n (map (fun x => snd x) cs) -> ev (cell_env kn Eb E1 cs) n = ev E1 n.
Proof.
  intros kn Eb E1 cs n. induction cs as [|[[a w] c] r IH]; intros Hn; [reflexivity|].
  assert (Hr : ~ In n (map (fun x => snd x) r)) by (intros X; apply Hn; cbn [map snd]; right; exact X).
  assert (Hc : n <> c) by (intros X; apply Hn; cbn [map snd]; left; symmetry; exact X).
  cbn [cell_env fold_right]. fold (cell_env kn Eb E1 r). destruct (cell_value kn a w); [|apply IH; exact Hr].
  cbn [APS.upd ev]. destruct (Nat.eqb_spec n c); [lia | apply IH; exact Hr].
Qed.

Lemma nodupb_sound : forall l, nodupb l = true -> List.NoDup l.
Proof.
  induction l as [|x r IH]; cbn [nodupb]; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|exact (IH H2)].
  intros Hin. apply negb_true_iff in H1.
  assert (X : existsb (Nat.eqb x) r = true) by (apply existsb_exists; exists x; split; [exact Hin | apply Nat.eqb_refl]).
  rewrite X in H1. discriminate.
Qed.

Lemma cell_env_at : forall kn Eb E1 cs a w c e,
  List.NoDup (map (fun x => snd x) cs) -> In (a, w, c) cs -> cell_value kn a w = Some e ->
  ev (cell_env kn Eb E1 cs) c = edenot Eb e.
Proof.
  intros kn Eb E1 cs a w c e Hnd. induction cs as [|[[a' w'] c'] r IH]; intros Hin Hcv; [destruct Hin|].
  cbn [cell_env fold_right]. fold (cell_env kn Eb E1 r). cbn [map snd] in Hnd.
  pose proof (proj1 (List.NoDup_cons_iff _ _) Hnd) as [Hnotin Hnd'].
  destruct Hin as [Heq|Hin].
  - injection Heq as -> -> ->. rewrite Hcv. apply APS.upd_at.
  - assert (Hc : c <> c').
    { intros ->. apply Hnotin. apply in_map_iff. exists (a, w, c'). split; [reflexivity | exact Hin]. }
    destruct (cell_value kn a' w'); [cbn [APS.upd ev]; destruct (Nat.eqb_spec c c'); [lia|] |]; apply IH; assumption.
Qed.

Lemma cell_value_sound : forall kn a w e, cell_value kn a w = Some e -> In (KWord a w e) kn.
Proof.
  intros kn a w e. induction kn as [|K r IH]; cbn [cell_value]; intros H; [discriminate|].
  destruct K as [a' w' e'| | | | | | | | |]; try (right; exact (IH H)).
  destruct (saddr_eqb a a' && Nat.eqb w w')%bool eqn:Hc.
  - apply andb_prop in Hc as [H1 H2]. apply saddr_eqb_eq in H1. apply Nat.eqb_eq in H2. injection H as <-. subst. left. reflexivity.
  - right. exact (IH H).
Qed.

Lemma first_slot_index_sound : forall lo hi v ts i0 i,
  first_slot_index lo hi v ts i0 = Some i ->
  exists k, i = (i0 + k)%nat /\ (k < length ts)%nat /\ APS.is_havoc lo hi (nth k ts (ELit 0)) = Some v
    /\ forall k', (k' < k)%nat -> APS.is_havoc lo hi (nth k' ts (ELit 0)) <> Some v.
Proof.
  intros lo hi v ts. induction ts as [|t r IH]; cbn [first_slot_index]; intros i0 i H; [discriminate|].
  assert (HV : forall t0, is_slot lo hi t0 = APS.is_havoc lo hi t0) by (intros t0; destruct t0; reflexivity).
  assert (REST : first_slot_index lo hi v r (S i0) = Some i -> is_slot lo hi t <> Some v ->
            exists k, i = (i0 + k)%nat /\ (k < S (length r))%nat /\ APS.is_havoc lo hi (nth k (t :: r) (ELit 0)) = Some v
              /\ forall k', (k' < k)%nat -> APS.is_havoc lo hi (nth k' (t :: r) (ELit 0)) <> Some v).
  { intros H' Ht. destruct (IH (S i0) i H') as (k & Hi & Hk & Hv & Hb). exists (S k). split; [lia|]. split; [cbn [length]; lia|].
    split; [exact Hv|]. intros k' Hk'. destruct k' as [|k']; [cbn [nth]; rewrite <- HV; exact Ht | cbn [nth]; apply Hb; lia]. }
  destruct (is_slot lo hi t) as [v'|] eqn:Hs.
  - destruct (Nat.eqb_spec v v') as [<-|Hne].
    + injection H as <-. exists 0%nat. split; [lia|]. split; [cbn [length]; lia|]. split; [cbn [nth]; rewrite <- HV; exact Hs|]. intros k' Hk'. lia.
    + apply REST; [exact H | intros X; injection X as X; exact (Hne (eq_sym X))].
  - apply REST; [exact H | discriminate].
Qed.

Lemma in_rng_sound : forall E M kn e l h, know_ok segs E M kn -> in_rng kn e l h = true -> l <= bv_unsigned (edenot E e) <= h.
Proof.
  intros E M kn e l h HK H. unfold in_rng in H. destruct (erange kn e) as [[a b]|] eqn:He; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (erange_sound segs E M kn e a b HK He). lia.
Qed.

Lemma reg_slot_top_ge : forall lo hi ts, (lo <= reg_slot_top lo hi ts)%nat.
Proof. intros lo hi ts. unfold reg_slot_top. induction ts as [|t r IH]; cbn [fold_right]; [lia|]. destruct (is_slot lo hi t); lia. Qed.

Lemma reg_slot_top_bound : forall lo hi ts k v,
  APS.is_havoc lo hi (nth k ts (ELit 0)) = Some v -> (k < length ts)%nat -> (v < reg_slot_top lo hi ts)%nat.
Proof.
  intros lo hi ts. unfold reg_slot_top. induction ts as [|t r IH]; intros k v Hv Hk; cbn [length] in Hk; [lia|].
  cbn [fold_right]. assert (HV : is_slot lo hi t = APS.is_havoc lo hi t) by (destruct t; reflexivity).
  destruct k as [|k]; cbn [nth] in Hv.
  - rewrite HV, Hv. lia.
  - pose proof (IH k v Hv ltac:(lia)). destruct (is_slot lo hi t); lia.
Qed.

Lemma find_cslot_sound : forall c cs a w, find_cslot c cs = Some (a, w) -> In (a, w, c) cs.
Proof.
  intros c cs a w. induction cs as [|[[a' w'] c'] r IH]; cbn [find_cslot]; intros H; [discriminate|].
  destruct (Nat.eqb_spec c c') as [<-|Hne]; [injection H as <- <-; left; reflexivity | right; exact (IH H)].
Qed.

Lemma tk_cells_spec : forall lo hi0 hi tk a w c,
  In (a, w, c) (tk_cells lo hi0 hi tk) -> In (KWord a w (EVar c)) tk /\ (hi0 <= c < hi)%nat.
Proof.
  intros lo hi0 hi tk a w c H. unfold tk_cells in H. apply in_flat_map in H as (K & HK & Hin).
  destruct K as [a' w' v'| | | | | | | | |]; cbn [classify] in Hin; try (destruct Hin; fail); try contradiction.
  - destruct v' as [|c'| | | | | |]; try contradiction. destruct (Nat.leb hi0 c' && Nat.ltb c' hi)%bool eqn:Hc; [|contradiction].
    destruct Hin as [Heq|[]]. injection Heq as <- <- <-. apply andb_prop in Hc as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2.
    split; [exact HK | lia].
  - destruct e as [|c'| | | | | |]; try contradiction. destruct (Nat.leb lo c' && Nat.ltb c' hi0)%bool; [contradiction|].
    destruct (Nat.leb hi0 c' && Nat.ltb c' hi)%bool; contradiction.
Qed.

Lemma entails_hx_sound2 : forall lo hi E ss T R Mc,
  INV2 E ss R Mc -> entails_hx lo hi ss T = true -> (nx0 <= lo)%nat -> length (s_regs T) = 32%nat ->
  (nx0 <= s_next T)%nat ->
  exists E', env_agree lo E E' /\ (forall n, (hi <= n)%nat -> ev E' n = ev E n) /\ INV2 E' T R Mc
             /\ s_pc T = s_pc ss.
Proof.
  intros lo hi E ss T R Mc HI H Hlo Hlen HnxT. unfold entails_hx in H.
  set (hi0 := reg_slot_top lo hi (s_regs T)) in H.
  set (base := List.filter (is_base lo hi0 hi) (s_know T)) in H.
  set (cs := tk_cells lo hi0 hi (s_know T)) in H.
  apply andb_prop in H as [H Hx]. apply andb_prop in H as [H Hnd]. apply andb_prop in H as [H Hsr]. apply andb_prop in H as [Hb Hhi0].
  apply Nat.leb_le in Hhi0. pose proof (reg_slot_top_ge lo hi (s_regs T)) as Hlohi0. fold hi0 in Hlohi0.
  destruct (entails_h_sound2' lo hi E ss (set_kn T base) R Mc HI Hb Hlo Hlen HnxT) as (Hag & Hhigh & HIb & Hpc & Hregs).
  cbn [set_kn s_regs s_pc s_next s_know] in Hag, Hhigh, HIb, Hpc, Hregs.
  set (E' := APS.henv lo hi E (s_regs ss) (s_regs T)) in *.
  destruct (APS.regs_match_h_char lo hi [] (s_regs ss) (s_regs T) Hregs) as [Hleneq _].
  set (E'' := cell_env (s_know ss) E E' cs).
  pose proof (nodupb_sound _ Hnd) as HND.
  assert (AG2 : env_agree hi0 E' E'').
  { split; [|symmetry; apply cell_env_eb]. intros n Hn. symmetry. apply cell_env_other.
    intros Hin. apply in_map_iff in Hin as ([[a w] c] & Hc & Hin). cbn [snd] in Hc. subst c.
    destruct (tk_cells_spec lo hi0 hi (s_know T) a w n Hin) as [_ Hr]. lia. }
  pose proof (HK := i_know _ _ _ _ HI).
  exists E''. split; [|split; [|split; [|exact Hpc]]].
  - eapply APS.env_agree_trans; [exact Hag | eapply APS.env_agree_le; [exact AG2 | exact Hlohi0]].
  - intros n Hn. unfold E''. rewrite cell_env_other; [apply Hhigh; exact Hn|].
    intros Hin. apply in_map_iff in Hin as ([[a w] c] & Hc & Hin). cbn [snd] in Hc. subst c.
    destruct (tk_cells_spec lo hi0 hi (s_know T) a w n Hin) as [_ Hr]. lia.
  - eapply (INV2_reenv hi0 E' E''); [exact HIb | exact AG2 | lia | | | exact HnxT].
    + cbn [s_regs]. eapply APS.regs_ok_agree'; [exact AG2 | exact Hsr | exact (i_regs _ _ _ _ HIb)].
    + cbn [s_know]. apply Forall_forall. intros K HinK.
      pose proof (proj1 (forallb_forall _ _) Hx K HinK) as HxK. unfold xentry_ok in HxK.
      destruct (classify lo hi0 hi K) as [|v l h|a w c|c l h] eqn:Hcl.
      *
        assert (Hinb : In K base) by (unfold base; apply filter_In; split; [exact HinK | unfold is_base; rewrite Hcl; reflexivity]).
        pose proof (proj1 (Forall_forall _ _) (i_know _ _ _ _ HIb) K Hinb) as HKb. cbn [s_know set_kn] in HKb.
        assert (HvK : APC.kentry_vars_lt lo K = true).
        { unfold entails_h in Hb. apply andb_prop in Hb as [_ Hkv]. cbn [s_know set_kn] in Hkv. exact (kn_vars_lt_In lo base K Hkv Hinb). }
        eapply kentry_ok_agree1; [eapply APS.env_agree_le; [exact AG2 | exact Hlohi0] | exact HvK | exact HKb].
      *
        destruct K as [a' w' ev'| | | | |ev' l' h'| | | |]; cbn [classify] in Hcl; try discriminate;
          [destruct ev' as [|c'| | | | | |]; try discriminate; destruct (Nat.leb hi0 c' && Nat.ltb c' hi)%bool; discriminate|].
        destruct ev' as [|v'| | | | | |]; try discriminate.
        destruct (Nat.leb lo v' && Nat.ltb v' hi0)%bool eqn:Hv1; [injection Hcl as E1 E2 E3; subst v' l' h' | destruct (Nat.leb hi0 v' && Nat.ltb v' hi)%bool; discriminate].
        destruct (first_slot_index lo hi v (s_regs T) 0) as [i|] eqn:Hfi; [|discriminate].
        destruct (first_slot_index_sound lo hi v (s_regs T) 0 i Hfi) as (k & Hik & Hk & Hhv & Hbefore). cbn [Nat.add] in Hik. subst i.
        pose proof (APS.henv_havoc lo hi E (s_regs ss) (s_regs T) k v Hleneq Hk Hhv Hbefore) as EV. fold E' in EV.
        cbn [kentry_ok edenot].
        assert (EV2 : ev E'' v = ev E' v).
        { unfold E''. apply cell_env_other. intros Hin. apply in_map_iff in Hin as ([[a w] c] & Hc & Hin). cbn [snd] in Hc. subst c.
          destruct (tk_cells_spec lo hi0 hi (s_know T) a w v Hin) as [_ Hr].
          apply andb_prop in Hv1 as [_ Hv2]. apply Nat.ltb_lt in Hv2. lia. }
        rewrite EV2, EV. exact (in_rng_sound E Mc (s_know ss) _ l h HK HxK).
      *
        destruct K as [a' w' ev'| | | | |ev' l' h'| | | |]; cbn [classify] in Hcl; try discriminate;
          [|destruct ev' as [|c'| | | | | |]; try discriminate; destruct (Nat.leb lo c' && Nat.ltb c' hi0)%bool; [discriminate|];
            destruct (Nat.leb hi0 c' && Nat.ltb c' hi)%bool; discriminate].
        destruct ev' as [|c'| | | | | |]; try discriminate.
        destruct (Nat.leb hi0 c' && Nat.ltb c' hi)%bool eqn:Hc1; [|discriminate]. injection Hcl as E1 E2 E3; subst a' w' c'.
        apply andb_prop in HxK as [Hva Hcv]. destruct (cell_value (s_know ss) a w) as [e|] eqn:Hce; [|discriminate].
        pose proof (cell_value_sound _ _ _ _ Hce) as Hine.
        pose proof (proj1 (Forall_forall _ _) HK _ Hine) as HKe.
        assert (HKe'' : kentry_ok segs E'' Mc (KWord a w e)).
        { eapply (kentry_ok_agree1 lo E E''); [| | exact HKe].
          - eapply APS.env_agree_trans; [exact Hag | eapply APS.env_agree_le; [exact AG2 | exact Hlohi0]].
          - destruct a as [ab ao]. cbn [APC.kentry_vars_lt APC.saddr_vars_lt a_base] in Hva |- *.
            unfold APC.saddr_vars_lt. cbn [a_base]. rewrite Hva, Hcv. reflexivity. }
        assert (Hinc : In (a, w, c) cs).
        { unfold cs, tk_cells. apply in_flat_map. exists (KWord a w (EVar c)). split; [exact HinK|]. cbn [classify]. rewrite Hc1. left. reflexivity. }
        pose proof (cell_env_at (s_know ss) E E' cs a w c e HND Hinc Hce) as EVc. fold E'' in EVc.
        cbn [kentry_ok] in HKe'' |- *. destruct HKe'' as (W8 & FL & RD). split; [exact W8|]. split; [exact FL|].
        rewrite RD. cbn [edenot]. rewrite EVc.
        rewrite (APS.edenot_agree' lo E E'' e); [reflexivity | | exact Hcv].
        eapply APS.env_agree_trans; [exact Hag | eapply APS.env_agree_le; [exact AG2 | exact Hlohi0]].
      *
        destruct K as [a' w' ev'| | | | |ev' l' h'| | | |]; cbn [classify] in Hcl; try discriminate;
          [destruct ev' as [|c'| | | | | |]; try discriminate; destruct (Nat.leb hi0 c' && Nat.ltb c' hi)%bool; discriminate|].
        destruct ev' as [|c'| | | | | |]; try discriminate.
        destruct (Nat.leb lo c' && Nat.ltb c' hi0)%bool; [discriminate|]. destruct (Nat.leb hi0 c' && Nat.ltb c' hi)%bool eqn:Hc1; [|discriminate].
        injection Hcl as E1 E2 E3; subst c' l' h'.
        destruct (find_cslot c cs) as [[a w]|] eqn:Hfc; [|discriminate].
        destruct (cell_value (s_know ss) a w) as [e|] eqn:Hce; [|discriminate].
        pose proof (find_cslot_sound _ _ _ _ Hfc) as Hinc.
        pose proof (cell_env_at (s_know ss) E E' cs a w c e HND Hinc Hce) as EVc. fold E'' in EVc.
        cbn [kentry_ok edenot]. rewrite EVc. exact (in_rng_sound E Mc (s_know ss) _ l h HK HxK).
Qed.

Lemma INV2_inst : forall E J e inv R Mc, (nx0 <= J)%nat ->
  INV2 E (inst inv J e) R Mc <-> INV2 (APS.upd E J (edenot E e)) inv R Mc.
Proof.
  intros E J e inv R Mc HJ.
  pose proof (APS.env_agree_le nx0 J E (APS.upd E J (edenot E e)) (APS.upd_agree E J _) HJ) as Hag0.
  split; intros HI.
  - constructor; cbn [inst s_regs s_know s_next] in *.
    + apply (proj1 (APS.regs_ok_inst E J e (s_regs inv) R)). exact (i_regs _ _ _ _ HI).
    + apply (proj1 (APS.know_ok_ksubst segs E J e Mc (s_know inv))). exact (i_know _ _ _ _ HI).
    + intros a Ha. apply (i_frame _ _ _ _ HI). cbn [s_know inst]. eapply outside_agree; [exact Hag0 | exact Ha].
    + exact (i_grows _ _ _ _ HI).
    + eapply regions_ok_agree; [exact Hag0 | exact (i_flat _ _ _ _ HI)].
    + exact (i_nx _ _ _ _ HI).
    + exact (bfacts_agree _ _ Hag0 (i_bf _ _ _ _ HI)).
  - constructor; cbn [inst s_regs s_know s_next] in *.
    + apply (proj2 (APS.regs_ok_inst E J e (s_regs inv) R)). exact (i_regs _ _ _ _ HI).
    + apply (proj2 (APS.know_ok_ksubst segs E J e Mc (s_know inv))). exact (i_know _ _ _ _ HI).
    + intros a Ha. apply (i_frame _ _ _ _ HI). eapply outside_agree; [apply env_agree_sym; exact Hag0 | exact Ha].
    + exact (i_grows _ _ _ _ HI).
    + eapply regions_ok_agree; [apply env_agree_sym; exact Hag0 | exact (i_flat _ _ _ _ HI)].
    + exact (i_nx _ _ _ _ HI).
    + exact (bfacts_agree _ _ (env_agree_sym _ _ _ Hag0) (i_bf _ _ _ _ HI)).
Qed.

Lemma pin_sound : forall E ss R Mc v c ss',
  INV2 E ss R Mc -> pin ss v c = Some ss' ->
  INV2 E ss' R Mc /\ s_pc ss' = s_pc ss /\ s_next ss' = s_next ss.
Proof.
  intros E ss R Mc v c ss' HI H. unfold pin in H.
  destruct (Nat.ltb v (s_next ss)) eqn:Hv; [|discriminate]. cbn [negb] in H. apply Nat.ltb_lt in Hv.
  destruct (erange (s_know ss) (EVar v)) as [[l h]|] eqn:Her; [|discriminate].
  destruct (Z.eqb l c && Z.eqb h c)%bool eqn:Hlh; [|discriminate]. injection H as <-.
  apply andb_prop in Hlh as [Hl Hh]. apply Z.eqb_eq in Hl. apply Z.eqb_eq in Hh. subst l h.
  pose proof (erange_sound segs E Mc (s_know ss) (EVar v) c c (i_know _ _ _ _ HI) Her) as [L1 L2]. cbn [edenot] in L1, L2.
  assert (EVv : ev E v = edenot E (ELit c)).
  { cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned 64 (ev E v)). f_equal. lia. }
  split; [|split; reflexivity].
  assert (UE : APS.upd E v (edenot E (ELit c)) = E) by (rewrite <- EVv; apply APS.upd_same).
  constructor; cbn [inst s_regs s_know s_next]; try (exact (i_frame _ _ _ _ HI)); try (exact (i_grows _ _ _ _ HI));
    try (exact (i_flat _ _ _ _ HI)); try (exact (i_nx _ _ _ _ HI)); try (exact (i_bf _ _ _ _ HI)).
  - apply (proj2 (APS.regs_ok_inst E v (ELit c) (s_regs ss) R)). rewrite UE. exact (i_regs _ _ _ _ HI).
  - apply (proj2 (APS.know_ok_ksubst segs E v (ELit c) Mc (s_know ss))). rewrite UE. exact (i_know _ _ _ _ HI).
Qed.

Lemma find_bne_sound : forall fk brs id rb rk kb kk v,
  find_bne fk brs id rb rk kb kk v = true ->
  exists j, In (BNe id j v) brs
    /\ lin_ge0 fk [(rb, rk)] [(kb, kk); (j, 0)] = true /\ lin_ge0 fk [(kb, kk); (j, 0)] [(rb, rk)] = true.
Proof.
  intros fk brs id rb rk kb kk v. induction brs as [|bf r IH]; cbn [find_bne]; intros H; [discriminate|].
  assert (REST : find_bne fk r id rb rk kb kk v = true ->
            exists j, In (BNe id j v) (bf :: r) /\ lin_ge0 fk [(rb, rk)] [(kb, kk); (j, 0)] = true /\ lin_ge0 fk [(kb, kk); (j, 0)] [(rb, rk)] = true).
  { intros H'. destruct (IH H') as (j & Hin & X). exists j. split; [right; exact Hin | exact X]. }
  destruct bf as [? ? ? ? ?|? ? ? ? ?|? ? ? ? ?|? ? ? ?|id' j v']; try exact (REST H).
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|exact (REST H)].
  repeat (apply andb_prop in Hc as [Hc ?X]). apply Nat.eqb_eq in Hc. apply Z.eqb_eq in X1. subst id' v'.
  exists j. split; [left; reflexivity|]. split; [exact X0 | exact X].
Qed.

Lemma loadbyte_ne_sound : forall (fx : FPState) v ss alo ahi E R Mc,
  loadbyte_ne v ss = Some (alo, ahi) -> INV2 E ss R Mc ->
  exists ss' E' R', (alo = Some ss' \/ ahi = Some ss')
    /\ env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV2 E' ss' R' Mc
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                   (@mkst fx R' (Z_to_bv 64 (s_pc ss')) Mc (seg_rom segs)).
Proof.
  intros fx v ss alo ahi E R Mc H HI. pose proof (i_regs _ _ _ _ HI) as HR. pose proof (i_know _ _ _ _ HI) as HK.
  unfold loadbyte_ne in H.
  destruct (itab_lookup IT (s_pc ss)) as [i|] eqn:Hit; [|discriminate].
  pose proof (IT_ok _ _ Hit) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz. injection Hen as ->.
  destruct (lbu_of i) as [[[rd rs] imm]|] eqn:Hl; [|discriminate]. apply lbu_of_sound in Hl. subst i.
  destruct (bv_eqb rd 0) eqn:Hrd0; [discriminate|].
  destruct (SR.closed ss []) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  match type of H with (match find_blob_cover ?fk ?kn ?rb ?rk with _ => _ end) = _ =>
    destruct (find_blob_cover fk kn rb rk) as [[[kb kk] id]|] eqn:Hcov; [|discriminate];
    set (RB := rb) in *; set (RK := rk) in * end.
  match type of H with (let '(lo, hi) := lb_range ?fk ?id ?rb ?rk ?kb ?kk in _) = _ =>
    destruct (lb_range fk id rb rk kb kk) as [lo hi] eqn:Hbf end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hne; [|discriminate] end.
  injection H as Halo Hahi.
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (nx := s_next ss) in *.
  pose proof (facts_of_ok segs E Mc k HK) as HKf. fold fk in HKf.
  destruct (find_blob_cover_sound fk k RB RK kb kk id Hcov) as (len & Hin & Hx).
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKB. cbn [kentry_ok] in HKB. destruct HKB as (Hfl & Hlen & Hall).
  destruct (xinside_sound segs E Mc fk RB RK (ELit 1) kb kk len HKf Hx) as [X1 X2]. rewrite elenZ_lit in X2. rewrite Z.mod_small in X2 by lia.
  set (S := estart E (SA RB RK)) in *. set (B := estart E (SA kb kk)) in *.
  assert (ES : S = bv_unsigned (edenot E RB) + RK) by reflexivity.
  assert (EB : B = bv_unsigned (edenot E kb) + kk) by reflexivity.
  set (j := S - B).
  assert (Hj : 0 <= j < elenZ E len) by (subst j; lia).
  pose proof (Hall j Hj) as HM. replace (B + j) with S in HM by lia.
  set (b := nth (Z.to_nat j) (eb E id) (Z_to_bv 8 0)) in *.
  destruct Hfl as (F1 & F2 & F3 & F4).
  assert (HS64 : 0 <= S < 2 ^ 64) by lia.

  assert (RANGE : lo <= bv_unsigned b <= hi).
  { destruct (lb_range_sound E Mc fk id RB RK kb kk lo hi Hbf HKf (i_bf _ _ _ _ HI) j ltac:(reflexivity) ltac:(lia)
               ltac:(unfold blen; rewrite Hlen; lia)) as (R1 & _ & _). exact R1. }
  assert (HNE : bv_unsigned b <> v).
  { destruct (find_bne_sound fk BR id RB RK kb kk v Hne) as (ej & Hbin & L1 & L2).
    pose proof (lin_ge0_sound segs E Mc fk _ _ HKf L1) as Y1. pose proof (lin_ge0_sound segs E Mc fk _ _ HKf L2) as Y2.
    cbn [xt_den] in Y1, Y2.
    assert (Hej : bv_unsigned (edenot E ej) = j) by (subst j S B; unfold estart; cbn [a_base a_off]; lia).
    pose proof (proj1 (Forall_forall _ _) (i_bf _ _ _ _ HI) _ Hbin) as BF. cbn [bfact_ok] in BF. rewrite Hej in BF.
    unfold bbyte in BF. apply BF. unfold blen. rewrite Hlen. lia. }

  assert (ADDR : v_addi (getr R rs) (bv_signed imm) = Z_to_bv 64 S).
  { rewrite (HR rs). rewrite <- to_saddr_denot. fold RB RK.
    rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (to_saddr (sr_get (s_regs ss) rs) (bv_signed imm)))).
    f_equal. change (adenot E (to_saddr (sr_get (s_regs ss) rs) (bv_signed imm))) with (adenot E (SA RB RK)).
    apply (flat_u E (SA RB RK) 1). unfold flat. fold S. lia. }
  assert (RDN : rdn segs Mc (v_addi (getr R rs) (bv_signed imm)) 1%nat = Some [b]).
  { rewrite ADDR. apply rdn_one. rewrite HM. reflexivity. }
  pose proof (PropExec.step_lbu segs R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs) w rd rs imm b Hf Hec Hd RDN) as STEP.
  rewrite Hrd0 in STEP.
  set (bv := Z_to_bv 64 (bv_unsigned b)) in *.

  assert (ARM : exists lo' hi', lo' <= bv_unsigned b <= hi'
            /\ let s' := SS (s_pc ss + 4) (sr_upd (s_regs ss) (ridx rd) (EVar nx)) [] (KRange (EVar nx) lo' hi' :: k) (Datatypes.S nx) in
               (alo = Some s' \/ ahi = Some s')).
  { destruct (Z_lt_le_dec (bv_unsigned b) v) as [Hlt|Hge].
    - exists lo, (v - 1). split; [lia|]. left. rewrite <- Halo. destruct (Z.leb_spec lo (v - 1)); [reflexivity | lia].
    - exists (v + 1), hi. split; [lia|]. right. rewrite <- Hahi. destruct (Z.leb_spec (v + 1) hi); [reflexivity | lia]. }
  destruct ARM as (lo' & hi' & RANGE' & Hor).
  exists (SS (s_pc ss + 4) (sr_upd (s_regs ss) (ridx rd) (EVar nx)) [] (KRange (EVar nx) lo' hi' :: k) (Datatypes.S nx)), (APS.upd E nx bv), (regupd R rd bv).
  split; [exact Hor|].
  pose proof (APS.upd_agree E nx bv) as Hag.
  pose proof (APS.env_agree_le nx0 nx E _ Hag (i_nx _ _ _ _ HI)) as Hag0.
  split; [exact Hag|]. split; [cbn [s_next]; lia|]. split.
  - constructor; cbn [s_regs s_know s_next s_pc].
    +
      intros x.
      assert (HRU : regs_ok (APS.upd E nx bv) (sr_upd (s_regs ss) (ridx rd) (EVar nx)) (regupd R rd bv)).
      { intros y. unfold sr_get. destruct (bv_eqb y 0) eqn:Hy0.
        - assert (y = 0%bv) by (apply bv_eq; unfold bv_eqb in Hy0; lia). subst y.
          unfold getr. rewrite Hy0. reflexivity.
        - rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx y) (ridx rd)) as [Hyr|Hyr].
          + apply ridx_inj in Hyr. subst y. cbn [edenot]. rewrite APS.upd_at.
            rewrite getr_same; [reflexivity|]. intro Hc. subst rd. rewrite bv_eqb_refl in Hrd0. discriminate.
          + assert (Hyr' : y <> rd) by (intro Hc; subst; exact (Hyr eq_refl)).
            rewrite getr_other by exact Hyr'. rewrite (HR y). unfold sr_get. rewrite Hy0.
            first [apply (SR.edenot_agree_AP nx E _ _ Hag) | symmetry; apply (SR.edenot_agree_AP nx E _ _ Hag)]. apply SR.nth_sr_vars_lt; [exact Fsr0 | ].
            apply ridx_range. }
      exact (HRU x).
    +
      constructor.
      * cbn [kentry_ok edenot]. rewrite APS.upd_at. subst bv. rewrite u64_of_Z; [exact RANGE' | pose proof (u8_range b); lia].
      * eapply APS.know_ok_agree'; [exact Hag | exact Fkn0 | exact HK].
    + intros a0 Ha. apply (i_frame _ _ _ _ HI). eapply outside_agree; [exact Hag0 | exact Ha].
    + exact (i_grows _ _ _ _ HI).
    + eapply regions_ok_agree; [exact Hag0 | exact (i_flat _ _ _ _ HI)].
    + pose proof (i_nx _ _ _ _ HI). lia.
    + exact (bfacts_agree _ _ Hag0 (i_bf _ _ _ _ HI)).
  - cbn [s_pc]. eapply mst_step; [reflexivity | exact STEP | ].
    replace (v_addi (Z_to_bv 64 (s_pc ss)) 4) with (Z_to_bv 64 (s_pc ss + 4)); [apply mst_refl|].
    unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma set_kn_INV2 : forall E ss R Mc k, INV2 E ss R Mc -> know_ok segs E Mc k -> INV2 E (set_kn ss k) R Mc.
Proof.
  intros E ss R Mc k HI HK. constructor; cbn [set_kn s_regs s_know s_next];
    [exact (i_regs _ _ _ _ HI) | exact HK | exact (i_frame _ _ _ _ HI) | exact (i_grows _ _ _ _ HI) | exact (i_flat _ _ _ _ HI) | exact (i_nx _ _ _ _ HI)
    | exact (i_bf _ _ _ _ HI)].
Qed.

Lemma case_arms_sound : forall E ss R Mc e mid alo ahi,
  INV2 E ss R Mc -> case_arms ss e mid = Some (alo, ahi) ->
  exists s', (alo = Some s' \/ ahi = Some s') /\ INV2 E s' R Mc /\ s_pc s' = s_pc ss /\ s_next s' = s_next ss /\ s_regs s' = s_regs ss.
Proof.
  intros E ss R Mc e mid alo ahi HI H. unfold case_arms in H.
  destruct (APC.expr_vars_lt (s_next ss) e); [|discriminate]. cbn [negb] in H.
  destruct (erange (s_know ss) e) as [[lo hi]|] eqn:Hr; [|discriminate].
  pose proof (erange_sound segs E Mc (s_know ss) e lo hi (i_know _ _ _ _ HI) Hr) as [Hlo Hhi].
  set (v := bv_unsigned (edenot E e)) in *.
  destruct (Z.leb hi mid) eqn:H1.
  { injection H as <- <-. exists ss. split; [left; reflexivity|]. split; [exact HI|]. repeat split; reflexivity. }
  destruct (Z.ltb mid lo) eqn:H2.
  { injection H as <- <-. exists ss. split; [right; reflexivity|]. split; [exact HI|]. repeat split; reflexivity. }
  apply Z.leb_gt in H1. apply Z.ltb_ge in H2. cbv zeta in H. injection H as <- <-.
  destruct (Z.leb_spec v mid) as [Hle|Hgt].
  - set (s1 := set_kn ss (KRange e lo mid :: s_know ss)).
    assert (HI1 : INV2 E s1 R Mc).
    { apply set_kn_INV2; [exact HI|]. constructor; [cbn [kentry_ok]; fold v; lia | exact (i_know _ _ _ _ HI)]. }
    destruct (APC.kn_contra (KRange e lo mid :: s_know ss)) eqn:Hc.
    + exfalso. exact (APS.kn_contra_sound segs E Mc (s_know s1) (i_know _ _ _ _ HI1) Hc).
    + exists s1. split; [left; reflexivity|]. split; [exact HI1|]. repeat split; reflexivity.
  - set (s2 := set_kn ss (KRange e (mid + 1) hi :: s_know ss)).
    assert (HI2 : INV2 E s2 R Mc).
    { apply set_kn_INV2; [exact HI|]. constructor; [cbn [kentry_ok]; fold v; lia | exact (i_know _ _ _ _ HI)]. }
    destruct (APC.kn_contra (KRange e (mid + 1) hi :: s_know ss)) eqn:Hc.
    + exfalso. exact (APS.kn_contra_sound segs E Mc (s_know s2) (i_know _ _ _ _ HI2) Hc).
    + exists s2. split; [right; reflexivity|]. split; [exact HI2|]. repeat split; reflexivity.
Qed.

Lemma fact_sound : forall E ss R Mc K,
  INV2 E ss R Mc -> APC.fact_ok (s_know ss) K = true -> INV2 E (set_kn ss (K :: s_know ss)) R Mc.
Proof.
  intros E ss R Mc K HI H. apply set_kn_INV2; [exact HI|]. constructor; [|exact (i_know _ _ _ _ HI)].
  eapply APS.fact_ok_sound; [exact (i_know _ _ _ _ HI) | exact H].
Qed.

Lemma abstract_sound : forall E ss R Mc b o n ss',
  INV2 E ss R Mc -> abstract ss b o n = Some ss' ->
  INV2 E ss' R Mc /\ s_pc ss' = s_pc ss /\ s_next ss' = s_next ss /\ s_regs ss' = s_regs ss.
Proof.
  intros E ss R Mc b o n ss' HI H. unfold abstract in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hcov _].
  split; [|repeat split; reflexivity].
  apply set_kn_INV2; [exact HI|]. constructor.
  - eapply (APS.kunk_covered_sound segs A SEGS_in_hull HULL_ok); [exact (i_know _ _ _ _ HI) | exact Hcov].
  - eapply APS.know_ok_cutout; [exact (i_know _ _ _ _ HI) | intros; reflexivity].
Qed.

Lemma coalesce_sound : forall E ss R Mc b o n ss',
  INV2 E ss R Mc -> coalesce ss b o n = Some ss' ->
  INV2 E ss' R Mc /\ s_pc ss' = s_pc ss /\ s_next ss' = s_next ss /\ s_regs ss' = s_regs ss.
Proof.
  intros E ss R Mc b o n ss' HI H. unfold coalesce in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. injection H as <-.
  split; [|repeat split; reflexivity].
  apply set_kn_INV2; [exact HI|]. constructor.
  - eapply kunk_chain_sound; [exact (i_know _ _ _ _ HI) | exact Hc].
  - eapply APS.know_ok_cutout; [exact (i_know _ _ _ _ HI) | intros; reflexivity].
Qed.

Lemma guard_facts : forall lc jc ss, guard lc jc ss = true ->
  (forall h nx lo hi, lc = Some (LC h nx lo hi) -> (nx0 <= lo /\ lo <= hi /\ hi <= s_next ss /\ nx0 <= s_next nx)%nat)
  /\ (forall j js b lo, find_jc j jc = Some (JC j js b lo) -> (nx0 <= b /\ b <= lo /\ lo <= s_next js /\ b <= s_next ss)%nat)
  /\ (nx0 <= s_next ss)%nat.
Proof.
  intros lc jc ss H. unfold guard in H. apply andb_prop in H as [H Hn]. apply andb_prop in H as [Hl Hj]. apply Nat.leb_le in Hn.
  split; [|split; [|exact Hn]].
  - intros h nx lo hi ->. repeat (apply andb_prop in Hl as [Hl ?X]). apply Nat.leb_le in Hl. apply Nat.leb_le in X. apply Nat.leb_le in X0. apply Nat.leb_le in X1. lia.
  - intros j js b lo Hf. apply find_jc_In in Hf. rewrite forallb_forall in Hj. specialize (Hj _ Hf). cbn beta iota in Hj.
    repeat (apply andb_prop in Hj as [Hj ?X]). apply Nat.leb_le in Hj. apply Nat.leb_le in X. apply Nat.leb_le in X0. apply Nat.leb_le in X1. lia.
Qed.

Inductive outcome : Type := OEnd (i : nat) | ONext | OMerge (j : nat).

Definition RES (lc : option loopctx) (jc : list joinctx) (E : env) (b : nat)
           (E' : env) (R' : bvmap 5 word) (Mc' : word -> option byte) (pc' : Z) (o : outcome) : Prop :=
  match o with
  | OEnd i => exists ps ssf, nth_error PSS i = Some ps /\ end_ok ps ssf = true /\ pc' = s_pc ssf
                /\ env_agree b E E' /\ INV2 E' ssf R' Mc'
  | ONext => exists h nx lo hi, lc = Some (LC h nx lo hi) /\ pc' = h /\ env_agree lo E E' /\ INV2 E' nx R' Mc'
  | OMerge j => exists js bj lo, find_jc j jc = Some (JC j js bj lo) /\ pc' = s_pc js /\ env_agree bj E E' /\ INV2 E' js R' Mc'
  end.

Lemma RES_up : forall lc lc' jc jc' E E1 b b1 E' R' Mc' pc' o,
  RES lc' jc' E1 b1 E' R' Mc' pc' o -> env_agree b E E1 -> (b <= b1)%nat ->
  (forall h nx lo hi, o = ONext -> lc' = Some (LC h nx lo hi) -> lc = lc' /\ (lo <= b)%nat) ->
  (forall j js bj lo, o = OMerge j -> find_jc j jc' = Some (JC j js bj lo) -> find_jc j jc = Some (JC j js bj lo) /\ (bj <= b)%nat) ->
  RES lc jc E b E' R' Mc' pc' o.
Proof.
  intros lc lc' jc jc' E E1 b b1 E' R' Mc' pc' o H Hag Hle HL HJ. destruct o as [i| |j]; cbn [RES] in *.
  - destruct H as (ps & ssf & H1 & H2 & H3 & Hag' & HI). exists ps, ssf. repeat (split; [assumption|]).
    split; [|exact HI]. eapply APS.env_agree_trans; [exact Hag | eapply APS.env_agree_le; [exact Hag' | exact Hle]].
  - destruct H as (h & nx & lo & hi & H1 & H2 & Hag' & HI). destruct (HL h nx lo hi eq_refl H1) as [-> Hlo].
    exists h, nx, lo, hi. repeat (split; [assumption|]).
    split; [|exact HI]. eapply APS.env_agree_trans; [eapply APS.env_agree_le; [exact Hag | exact Hlo] | exact Hag'].
  - destruct H as (js & bj & lo & H1 & H2 & Hag' & HI). destruct (HJ j js bj lo eq_refl H1) as [Hf Hbj].
    exists js, bj, lo. split; [exact Hf|]. split; [exact H2|].
    split; [|exact HI]. eapply APS.env_agree_trans; [eapply APS.env_agree_le; [exact Hag | exact Hbj] | exact Hag'].
Qed.

Lemma body_state_INV2 : forall E inv R Mc J N nhi (j Nv : Z),
  INV2 E inv R Mc -> ev E J = Z_to_bv 64 j -> bv_unsigned (edenot E N) = Nv ->
  0 <= j < Nv -> Nv <= nhi -> nhi < two64 ->
  INV2 E (body_state J N nhi inv) R Mc.
Proof.
  intros E inv R Mc J N nhi j Nv HI HJ HN Hj Hnhi Hlt. unfold two64 in Hlt.
  apply set_kn_INV2; [exact HI|].
  constructor; [|constructor; [|exact (i_know _ _ _ _ HI)]]; cbn [kentry_ok edenot].
  - rewrite HJ, u64_of_Z by lia. lia.
  - unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite HN, HJ. rewrite u64_of_Z by lia.
    rewrite Z.mod_small by lia. lia.
Qed.

Theorem check_sound : forall p lc jc ss,
  check F PSS lc jc p ss = true ->
  forall (fx : FPState) E R Mc, INV2 E ss R Mc ->
  exists (fx' : FPState) E' R' Mc' pc' o,
    msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 pc') Mc' (seg_rom segs))
    /\ RES lc jc E (s_next ss) E' R' Mc' pc' o.
Proof.
  induction p as [st k IHk|i|e mid klo IHlo khi IHhi|kt IHt kf IHf|K k IHk|b o n k IHk|cb co cn k IHk|k IHk|k IHk|er eJ k IHk|fe fJ flo fhi k IHk|rv rlo rhi k IHk|sr se k IHk|pv pc_ k IHk|k IHk|nv klo IHlo khi IHhi|id k IHk|id2 ka IHka kb IHkb|J N inv body IHbody k IHk| |j js lo karms IHarms k IHk|j];
    intros lc jc ss Hc fx E R Mc HI; cbn [check] in Hc; apply andb_prop in Hc as [Hg Hc];
    destruct (guard_facts lc jc ss Hg) as (GL & GJ & Gn).
  -
    destruct (step1 F st ss) as [ss1|] eqn:Hs; [|discriminate].
    destruct (step1_sound fx st ss ss1 E R Mc Hs HI) as (fx1 & E1 & R1 & Mc1 & Hag & Hle & HI1 & Hms).
    destruct (IHk lc jc ss1 Hc fx1 E1 R1 Mc1 HI1) as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR).
    exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    eapply RES_up; [exact HR | exact Hag | exact Hle
                   | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                   | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
  -
    destruct (nth_error PSS i) as [ps|] eqn:Hps; [|discriminate].
    exists fx, E, R, Mc, (s_pc ss), (OEnd i). split; [apply mst_refl|]. cbn [RES].
    exists ps, ss. split; [exact Hps|]. split; [exact Hc|]. split; [reflexivity|]. split; [apply APS.env_agree_refl | exact HI].
  -
    destruct (case_arms ss e mid) as [[alo ahi]|] eqn:Ha; [|discriminate]. apply andb_prop in Hc as [Hclo Hchi].
    destruct (case_arms_sound E ss R Mc e mid alo ahi HI Ha) as (s' & Hor & HI' & Hpc & Hnx & _).
    rewrite <- Hpc, <- Hnx.
    destruct Hor as [-> | ->]; [exact (IHlo lc jc s' Hclo fx E R Mc HI') | exact (IHhi lc jc s' Hchi fx E R Mc HI')].
  -
    destruct (branch_probe ss) as [e|] eqn:Hb; [|discriminate].
    destruct (case_arms ss e 0) as [[af at_]|] eqn:Ha; [|discriminate]. apply andb_prop in Hc as [Hcf Hct].
    destruct (case_arms_sound E ss R Mc e 0 af at_ HI Ha) as (s' & Hor & HI' & Hpc & Hnx & _).
    rewrite <- Hpc, <- Hnx.
    destruct Hor as [-> | ->]; [exact (IHf lc jc s' Hcf fx E R Mc HI') | exact (IHt lc jc s' Hct fx E R Mc HI')].
  -
    apply andb_prop in Hc as [Hf Hc]. apply andb_prop in Hf as [Hf _].
    exact (IHk lc jc _ Hc fx E R Mc (fact_sound E ss R Mc K HI Hf)).
  -
    destruct (abstract ss b o n) as [ss1|] eqn:Ha; [|discriminate].
    destruct (abstract_sound E ss R Mc b o n ss1 HI Ha) as (HI1 & Hpc & Hnx & _). rewrite <- Hpc, <- Hnx.
    exact (IHk lc jc ss1 Hc fx E R Mc HI1).
  -
    destruct (coalesce ss cb co cn) as [ss1|] eqn:Ha; [|discriminate].
    destruct (coalesce_sound E ss R Mc cb co cn ss1 HI Ha) as (HI1 & Hpc & Hnx & _). rewrite <- Hpc, <- Hnx.
    exact (IHk lc jc ss1 Hc fx E R Mc HI1).
  -
    destruct (fillx F ss) as [ss1|] eqn:Hs; [|discriminate].
    destruct (fillx_sound fx ss ss1 E R Mc Hs HI) as (fx1 & E1 & R1 & Mc1 & Hag & Hle & HI1 & Hms).
    destruct (IHk lc jc ss1 Hc fx1 E1 R1 Mc1 HI1) as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR).
    exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    eapply RES_up; [exact HR | exact Hag | exact Hle
                   | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                   | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
  -
    destruct (copyx F ss) as [ss1|] eqn:Hs; [|discriminate].
    destruct (copyx_sound fx ss ss1 E R Mc Hs HI) as (fx1 & E1 & R1 & Mc1 & Hag & Hle & HI1 & Hms).
    destruct (IHk lc jc ss1 Hc fx1 E1 R1 Mc1 HI1) as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR).
    exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    eapply RES_up; [exact HR | exact Hag | exact Hle
                   | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                   | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
  -
    destruct (evalreg ss er eJ) as [ss1|] eqn:Ha; [|discriminate].
    destruct (evalreg_sound E ss R Mc er eJ ss1 HI Ha) as (HI1 & Hpc & Hnx). rewrite <- Hpc, <- Hnx.
    exact (IHk lc jc ss1 Hc fx E R Mc HI1).
  -
    destruct (factrange ss fe fJ flo fhi) as [ss1|] eqn:Ha; [|discriminate].
    destruct (factrange_sound E ss R Mc fe fJ flo fhi ss1 HI Ha) as (HI1 & Hpc & Hnx & _ & _). rewrite <- Hpc, <- Hnx.
    exact (IHk lc jc ss1 Hc fx E R Mc HI1).
  -
    destruct (refine ss rv rlo rhi) as [ss1|] eqn:Ha; [|discriminate].
    destruct (refine_sound E ss R Mc rv rlo rhi ss1 HI Ha) as (HI1 & Hpc & Hnx & _ & _). rewrite <- Hpc, <- Hnx.
    exact (IHk lc jc ss1 Hc fx E R Mc HI1).
  -
    destruct (respell ss sr se) as [ss1|] eqn:Ha; [|discriminate].
    destruct (respell_sound E ss R Mc sr se ss1 HI Ha) as (HI1 & Hpc & Hnx). rewrite <- Hpc, <- Hnx.
    exact (IHk lc jc ss1 Hc fx E R Mc HI1).
  -
    destruct (pin ss pv pc_) as [ss1|] eqn:Ha; [|discriminate].
    destruct (pin_sound E ss R Mc pv pc_ ss1 HI Ha) as (HI1 & Hpc & Hnx). rewrite <- Hpc, <- Hnx.
    exact (IHk lc jc ss1 Hc fx E R Mc HI1).
  -
    destruct (loadbyte ss) as [ss1|] eqn:Hs; [|discriminate].
    destruct (loadbyte_sound fx ss ss1 E R Mc Hs HI) as (E1 & R1 & Hag & Hle & HI1 & Hms).
    destruct (IHk lc jc ss1 Hc fx E1 R1 Mc HI1) as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR).
    exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    eapply RES_up; [exact HR | exact Hag | exact Hle
                   | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                   | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
  -
    destruct (loadbyte_ne nv ss) as [[alo ahi]|] eqn:Hs; [|discriminate]. apply andb_prop in Hc as [Hclo Hchi].
    destruct (loadbyte_ne_sound fx nv ss alo ahi E R Mc Hs HI) as (s1 & E1 & R1 & Hor & Hag & Hle & HI1 & Hms).
    assert (STEP : exists (fx' : FPState) E' R' Mc' pc' o,
              msteps segs (@mkst fx R1 (Z_to_bv 64 (s_pc s1)) Mc (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 pc') Mc' (seg_rom segs))
              /\ RES lc jc E1 (s_next s1) E' R' Mc' pc' o).
    { destruct Hor as [-> | ->]; [exact (IHlo lc jc s1 Hclo fx E1 R1 Mc HI1) | exact (IHhi lc jc s1 Hchi fx E1 R1 Mc HI1)]. }
    destruct STEP as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR).
    exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    eapply RES_up; [exact HR | exact Hag | exact Hle
                   | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                   | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
  -
    destruct (XSTEP F id ss) as [ss1|] eqn:Hs; [|discriminate].
    apply andb_prop in Hc as [Hle Hc]. apply Nat.leb_le in Hle.
    destruct (XSOK Fvars BRvars fx id ss ss1 E R Mc Hs HI) as (fx1 & E1 & R1 & Mc1 & Hag & HI1 & Hms).
    destruct (IHk lc jc ss1 Hc fx1 E1 R1 Mc1 HI1) as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR).
    exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    eapply RES_up; [exact HR | exact Hag | exact Hle
                   | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                   | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
  -
    destruct (XSTEP2 F id2 ss) as [[sa sb]|] eqn:Hs; [|discriminate].
    apply andb_prop in Hc as [Hc Hcb]. apply andb_prop in Hc as [Hc Hca]. apply andb_prop in Hc as [Hlea Hleb].
    apply Nat.leb_le in Hlea. apply Nat.leb_le in Hleb.
    destruct (XSOK2 Fvars BRvars fx id2 ss sa sb E R Mc Hs HI) as (fx1 & E1 & R1 & Mc1 & ss1 & Hwhich & Hag & HI1 & Hms).
    assert (X : exists (fx' : FPState) E' R' Mc' pc' o,
              msteps segs (@mkst fx1 R1 (Z_to_bv 64 (s_pc ss1)) Mc1 (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 pc') Mc' (seg_rom segs))
              /\ RES lc jc E1 (s_next ss1) E' R' Mc' pc' o).
    { destruct Hwhich as [-> | ->]; [exact (IHka lc jc sa Hca fx1 E1 R1 Mc1 HI1) | exact (IHkb lc jc sb Hcb fx1 E1 R1 Mc1 HI1)]. }
    assert (Hle : (s_next ss <= s_next ss1)%nat) by (destruct Hwhich as [-> | ->]; assumption).
    destruct X as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR).
    exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    eapply RES_up; [exact HR | exact Hag | exact Hle
                   | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                   | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
  -
    destruct (loop_ok ss J N inv) as [nhi|] eqn:Hlo; [|discriminate].
    apply andb_prop in Hc as [Hc Hk]. apply andb_prop in Hc as [Hc Hbody]. apply andb_prop in Hc as [Hpc Hent].
    apply Z.eqb_eq in Hpc.
    destruct (APS.loop_ok_facts nx0 (acs_of ss) J N (acs_of inv) nhi Hlo) as (Ffr & FJ & FJh & Flog & Flen & FvN & FxN & Fnhi).
    unfold AP.nxt, AP.kn in FJ, FJh, FvN, FxN. cbv beta delta [AP.a_ss APC.a_ss acs_of] iota in FJ, FJh, Flog, Flen, FvN, FxN.
    pose proof (xhi_sound segs E Mc (s_know ss) N nhi (i_know _ _ _ _ HI) FxN) as HNv.
    set (Nv := bv_unsigned (edenot E N)) in *. pose proof (u64_range (edenot E N)) as RN. fold Nv in RN. unfold two64 in Fnhi.
    set (h := s_pc ss) in *. set (hi := s_next inv) in *.

    assert (Q : forall (m : nat) (j : Z) (fxj : FPState) Ej Rj Mcj,
               j = Nv - Z.of_nat m -> 0 <= j -> env_agree (s_next ss) E Ej ->
               INV2 Ej (inst inv J (ELit j)) Rj Mcj ->
               exists (fx' : FPState) E' R' Mc' pc' o,
                 msteps segs (@mkst fxj Rj (Z_to_bv 64 h) Mcj (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 pc') Mc' (seg_rom segs))
                 /\ RES lc jc E (s_next ss) E' R' Mc' pc' o).
    { induction m as [|m IHm]; intros j fxj Ej Rj Mcj Hj Hj0 Hag HIj.
      -
        assert (HNe : edenot Ej N = edenot Ej (ELit j)).
        { cbn [edenot]. rewrite <- (APS.edenot_agree' (s_next ss) E Ej N Hag FvN). apply bv_eq. rewrite u64_of_Z by lia.
          subst Nv. cbn [Z.of_nat] in Hj. lia. }
        assert (HIN : INV2 Ej (inst inv J N) Rj Mcj).
        { apply (proj2 (INV2_inst Ej J N inv Rj Mcj ltac:(lia))). rewrite HNe.
          apply (proj1 (INV2_inst Ej J (ELit j) inv Rj Mcj ltac:(lia))). exact HIj. }
        destruct (IHk lc jc (inst inv J N) Hk fxj Ej Rj Mcj HIN) as (fx' & E' & R' & Mc' & pc' & o & Hms & HR).
        exists fx', E', R', Mc', pc', o. split; [cbn [s_pc inst] in Hms; rewrite Hpc in Hms; exact Hms|].
        eapply RES_up; [exact HR | exact Hag | cbn [s_next inst]; lia
                       | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                       | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
      -
        set (E'' := APS.upd Ej J (Z_to_bv 64 j)).
        assert (Hjlt : j < Nv) by lia.
        assert (HIinv : INV2 E'' inv Rj Mcj).
        { unfold E''. replace (Z_to_bv 64 j) with (edenot Ej (ELit j)) by reflexivity.
          apply (proj1 (INV2_inst Ej J (ELit j) inv Rj Mcj ltac:(lia))). exact HIj. }
        assert (Hag'' : env_agree (s_next ss) E E'').
        { eapply APS.env_agree_trans; [exact Hag|]. eapply APS.env_agree_le; [apply APS.upd_agree | exact FJ]. }
        assert (HNE'' : bv_unsigned (edenot E'' N) = Nv) by (subst Nv; f_equal; symmetry; eapply (APS.edenot_agree' (s_next ss)); [exact Hag'' | exact FvN]).
        assert (HJ'' : ev E'' J = Z_to_bv 64 j) by (unfold E''; apply APS.upd_at).
        pose proof (body_state_INV2 E'' inv Rj Mcj J N nhi j Nv HIinv HJ'' HNE'' ltac:(lia) HNv ltac:(unfold two64; lia)) as HIb.
        destruct (IHbody (Some (LC h (inst inv J (APC.eaddz (EVar J) 1)) (S J) hi)) jc (body_state J N nhi inv) Hbody fxj E'' Rj Mcj HIb)
          as (fx1 & E1 & R1 & Mc1 & pc1 & o1 & Hms1 & HR1).
        cbn [s_pc body_state set_kn] in Hms1. rewrite Hpc in Hms1.
        destruct o1 as [i1| |j1].
        +
          exists fx1, E1, R1, Mc1, pc1, (OEnd i1). split; [exact Hms1|].
          eapply RES_up; [exact HR1 | exact Hag'' | cbn [s_next body_state set_kn]; lia
                         | intros * Y _; discriminate Y | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
        +
          cbn [RES] in HR1. destruct HR1 as (h' & nx & lo' & hi' & Hlc & Hpc1 & Hag1 & HI1).
          injection Hlc as <- <- <- <-.
          assert (HJ1 : ev E1 J = Z_to_bv 64 j) by (rewrite <- HJ''; symmetry; apply (proj1 Hag1); lia).
          assert (Hnext : edenot E1 (APC.eaddz (EVar J) 1) = Z_to_bv 64 (j + 1)).
          { unfold APC.eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite HJ1. apply bv_eq. rewrite u_add64, !u64_of_Z by lia.
            rewrite Z.mod_small by lia. reflexivity. }
          set (E4 := APS.upd E1 J (Z_to_bv 64 (j + 1))).
          assert (HI4 : INV2 E4 (inst inv J (ELit (j + 1))) R1 Mc1).
          { apply (proj2 (INV2_inst E4 J (ELit (j + 1)) inv R1 Mc1 ltac:(lia))).
            unfold E4. cbn [edenot]. rewrite APS.upd_upd. rewrite <- Hnext.
            apply (proj1 (INV2_inst E1 J (APC.eaddz (EVar J) 1) inv R1 Mc1 ltac:(lia))). exact HI1. }
          assert (Hag4 : env_agree (s_next ss) E E4).
          { eapply APS.env_agree_trans; [exact Hag''|]. eapply APS.env_agree_trans; [eapply APS.env_agree_le; [exact Hag1 | lia]|].
            eapply APS.env_agree_le; [apply APS.upd_agree | exact FJ]. }
          destruct (IHm (j + 1) fx1 E4 R1 Mc1 ltac:(lia) ltac:(lia) Hag4 HI4) as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR).
          exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms1 | rewrite Hpc1; exact Hms2] | exact HR].
        +
          exists fx1, E1, R1, Mc1, pc1, (OMerge j1). split; [exact Hms1|].
          eapply RES_up; [exact HR1 | exact Hag'' | cbn [s_next body_state set_kn]; lia
                         | intros * Y _; discriminate Y | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]]. }

    destruct (entails_hx_sound2 (S J) hi E ss (inst inv J (ELit 0)) R Mc HI Hent ltac:(lia)
                ltac:(cbn [inst s_regs]; rewrite length_map; exact Flen) ltac:(cbn [inst s_next]; lia))
      as (E1 & Hag1 & _ & HI1 & _).
    destruct (Q (Z.to_nat Nv) 0 fx E1 R Mc ltac:(lia) ltac:(lia) ltac:(eapply APS.env_agree_le; [exact Hag1 | lia]) HI1)
      as (fx' & E' & R' & Mc' & pc' & o & Hms & HR).
    exists fx', E', R', Mc', pc', o. split; [exact Hms | exact HR].
  -
    destruct lc as [[h nx lo hi]|]; [|discriminate].
    apply andb_prop in Hc as [Hc Hent]. apply andb_prop in Hc as [Hpc Hlen]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hlen.
    destruct (GL h nx lo hi eq_refl) as (G1 & G2 & G3 & G4).
    destruct (entails_hx_sound2 lo hi E ss nx R Mc HI Hent G1 Hlen G4) as (E' & Hag & _ & HI' & Hpc').
    exists fx, E', R, Mc, (s_pc ss), ONext. split; [apply mst_refl|]. cbn [RES].
    exists h, nx, lo, hi. split; [reflexivity|]. split; [exact Hpc|]. split; [exact Hag | exact HI'].
  -
    apply andb_prop in Hc as [Hc Hk]. apply andb_prop in Hc as [Hvia Harms].
    unfold via_ok in Hvia. repeat (apply andb_prop in Hvia as [Hvia ?X]).
    apply Nat.leb_le in X. apply Nat.leb_le in X0. apply Nat.leb_le in X1. apply Nat.eqb_eq in X2.
    destruct (IHarms lc (JC j js (s_next ss) lo :: jc) ss Harms fx E R Mc HI) as (fx1 & E1 & R1 & Mc1 & pc1 & o1 & Hms1 & HR1).
    destruct o1 as [i1| |j1].
    +
      exists fx1, E1, R1, Mc1, pc1, (OEnd i1). split; [exact Hms1 | exact HR1].
    +
      exists fx1, E1, R1, Mc1, pc1, ONext. split; [exact Hms1 | exact HR1].
    +
      cbn [RES] in HR1. destruct HR1 as (js' & bj & lo' & Hjc & Hpc1 & Hag1 & HI1).
      cbn [find_jc] in Hjc. destruct (Nat.eqb j j1) eqn:Ejj.
      * injection Hjc as <- <- <- <-.
        destruct (IHk lc jc js Hk fx1 E1 R1 Mc1 HI1) as (fx' & E' & R' & Mc' & pc' & o & Hms2 & HR2).
        exists fx', E', R', Mc', pc', o. split; [eapply msteps_trans; [exact Hms1 | rewrite Hpc1; exact Hms2]|].
        eapply RES_up; [exact HR2 | exact Hag1 | lia
                       | intros * _ Y; split; [reflexivity | edestruct GL; [exact Y|]; lia]
                       | intros * _ Y; split; [exact Y | edestruct GJ; [exact Y|]; lia]].
      * exists fx1, E1, R1, Mc1, pc1, (OMerge j1). split; [exact Hms1|]. cbn [RES].
        exists js', bj, lo'. split; [exact Hjc|]. split; [exact Hpc1|]. split; [|exact HI1].
        eapply APS.env_agree_le; [exact Hag1 | edestruct GJ; [exact Hjc|]; lia].
  -
    destruct (find_jc j jc) as [[j' js bj lo]|] eqn:Hf; [|discriminate].
    apply andb_prop in Hc as [Hc Hent]. apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hj Hpc].
    apply Nat.eqb_eq in Hj. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hlen. subst j'.
    destruct (GJ j js bj lo Hf) as (G1 & G2 & G3 & G4).
    destruct (entails_hx_sound2 lo (s_next js) E ss js R Mc HI Hent ltac:(lia) Hlen ltac:(lia)) as (E' & Hag & _ & HI' & Hpc').
    exists fx, E', R, Mc, (s_pc ss), (OMerge j). split; [apply mst_refl|]. cbn [RES].
    exists js, bj, lo. split; [exact Hf|]. split; [exact Hpc|]. split; [eapply APS.env_agree_le; [exact Hag | exact G2] | exact HI'].
Qed.

Lemma end_ok_sound : forall ps ss E R Mc,
  end_ok ps ss = true -> INV2 E ss R Mc ->
  s_pc ss = SR.ps_pc ps
  /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E e)
  /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok segs E Mc K).
Proof.
  intros ps ss E R Mc H HI. unfold end_ok in H.
  apply andb_prop in H as [H Hcells]. apply andb_prop in H as [Hpc Hregs]. apply Z.eqb_eq in Hpc.
  split; [exact Hpc|]. split.
  - intros i e Hin. rewrite forallb_forall in Hregs. specialize (Hregs (i, e) Hin). cbn [fst snd] in Hregs.
    apply andb_prop in Hregs as [Hi He]. apply andb_prop in Hi as [H0 H32]. apply Nat.ltb_lt in H0. apply Nat.ltb_lt in H32.
    apply expr_eqb_eq in He. split; [lia|]. rewrite <- He. rewrite ((i_regs _ _ _ _ HI) (Z_to_bv 5 (Z.of_nat i))). unfold sr_get.
    replace (bv_eqb (Z_to_bv 5 (Z.of_nat i)) 0) with false.
    2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
        rewrite Z.mod_small by lia. change (bv_unsigned (0%bv : bv 5)) with 0%Z. lia. }
    rewrite APS.ridx_lit by lia. reflexivity.
  - intros K Hin. rewrite forallb_forall in Hcells. specialize (Hcells K Hin). apply existsb_exists in Hcells as (K' & Hin' & Heq).
    apply APS.kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) (i_know _ _ _ _ HI) K Hin').
Qed.

End Sound.

Definition segs_in_hull_b (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside : forall sgs lo hi x,
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool sgs = true ->
  (x < lo \/ hi <= x) -> find_segment sgs x 1 = None.
Proof.
  induction sgs as [|sg l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base sg)) x && Z.leb (x + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma in_hull_of_b : segs_in_hull_b (APC.img_lo A) (APC.img_hi A) = true ->
  forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Proof.
  intros Hb a H. apply (find_segment1_none_outside segs (APC.img_lo A) (APC.img_hi A)); [exact Hb|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Definition region_flat_chkX (kn : list kentry) (r : region) : bool :=
  let '(rb, rlo, rlen) := r in
  match rlen with
  | ELit m => (Z.ltb 0 m && Z.ltb m two64 && (SR.region_flat_chk kn (rb, rlo, m) || APC.flat_x kn rb rlo (ELit m)))%bool
  | _ =>
      (APC.flat_x kn rb rlo rlen && match xhi (facts_of kn) rlen with Some h => Z.ltb h two64 | None => false end)%bool
  end.

Lemma region_flat_chkX_sound : forall E M kn r,
  know_ok segs E M kn -> region_flat_chkX kn r = true ->
  let '(rb, rlo, rlen) := r in 0 <= estart E (SA rb rlo) /\ 0 < elenZ E rlen < 2 ^ 64 /\ estart E (SA rb rlo) + elenZ E rlen <= 2 ^ 64.
Proof.
  intros E M kn [[rb rlo] rlen] HK H. unfold region_flat_chkX in H.
  assert (GEN : (APC.flat_x kn rb rlo rlen && match xhi (facts_of kn) rlen with Some h => Z.ltb h two64 | None => false end)%bool = true ->
                0 <= estart E (SA rb rlo) /\ 0 < elenZ E rlen < 2 ^ 64 /\ estart E (SA rb rlo) + elenZ E rlen <= 2 ^ 64).
  { intros G. apply andb_prop in G as [Gf Gh].
    destruct (APSX.w_flat_x_sound segs E M kn rb rlo rlen HK Gf) as (A1 & A2 & A3). unfold elenZ.
    assert (HB : bv_unsigned (edenot E rlen) < two64) by (unfold two64; pose proof (bv_unsigned_in_range 64 (edenot E rlen)) as X; exact (proj2 X)).
    unfold two64 in HB. lia. }
  destruct rlen as [m| | | | | | |]; try (exact (GEN H)).
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H64]. apply Z.ltb_lt in H0. apply Z.ltb_lt in H64. unfold two64 in H64.
  rewrite (elenZ_litZ E m) by lia.
  apply orb_prop in Hf as [Hf|Hf].
  - exact (SR.region_flat_chk_sound segs E M kn (rb, rlo, m) HK Hf).
  - destruct (APSX.w_flat_x_sound segs E M kn rb rlo (ELit m) HK Hf) as (A1 & A2 & A3).
    cbn [edenot] in A2. rewrite u64_of_Z in A2 by lia. lia.
Qed.

Definition cert_ok (F : list region) (PSS : list SR.post_spec) (p : splan) (pc0 : Z) (sr0 : list expr) (kn0 : list kentry) : bool :=
  (forallb (region_flat_chkX kn0) F
   && forallb (region_vars_lt nx0) F
   && bfacts_vars_lt nx0
   && check F PSS None [] p (SS pc0 sr0 [] kn0 nx0))%bool.

Theorem plan_entry_sound :
  itab_sound segs IT ->
  (forall fx : FPState, @APSX.copy_spec fx segs x_cpy) ->
  (forall fx : FPState, @APSX.fill_spec fx segs x_set two64) ->
  SR.strlen_step_stmt segs x_len ro_lo ro_hi ->
  (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None) ->
  APS.hull_ok A ->
  forall F PSS p pc0 sr0 kn0 (fx : FPState) E R M,
  cert_ok F PSS p pc0 sr0 kn0 = true ->
  (forall M0, XSTEP_ok F M0) ->
  (forall M0, XSTEP2_ok F M0) ->
  regs_ok E sr0 R -> know_ok segs E M kn0 -> bfacts_ok E ->
  exists (fx' : FPState) E' R' M' i ps,
       nth_error PSS i = Some ps
    /\ env_agree nx0 E E'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom segs))
    /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ regions_ok E' F
    /\ (forall a : word, outside E' F a -> M' a = M a)
    /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok segs E' M' K)
    /\ mem_grows M M'.
Proof.
  intros IT_ok COPY FILL STRLEN SIH HOK F PSS p pc0 sr0 kn0 fx E R M Hc HXS HXS2 HR HK HBF.
  unfold cert_ok in Hc. apply andb_prop in Hc as [Hc Hchk]. apply andb_prop in Hc as [Hc Hbv]. apply andb_prop in Hc as [Hflat Hvars].
  assert (HI : INV2 F M   E (SS pc0 sr0 [] kn0 nx0) R M).
  { constructor; cbn [s_regs s_know s_next]; [exact HR | exact HK | intros; reflexivity | apply mem_grows_refl | | lia | exact HBF].
    unfold regions_ok. apply Forall_forall. intros r Hin. rewrite forallb_forall in Hflat.
    exact (region_flat_chkX_sound E M kn0 r HK (Hflat r Hin)). }
  destruct (check_sound IT_ok COPY FILL STRLEN SIH HOK F Hvars Hbv PSS M (HXS M) (HXS2 M) p None [] _ Hchk fx E R M HI)
    as (fx' & E' & R' & M' & pc' & o & Hms & HR').
  destruct o as [i| |j]; cbn [RES] in HR'.
  - destruct HR' as (ps & ssf & Hps & Hend & Hpc & Hag & HI'). cbn [s_next] in Hag.
    destruct (end_ok_sound F M ps ssf E' R' M' Hend HI') as (Hpc2 & Hregs & Hcells).
    exists fx', E', R', M', i, ps. split; [exact Hps|]. split; [exact Hag|].
    split; [rewrite <- Hpc2, <- Hpc; exact Hms|]. split; [exact Hregs|].
    split; [replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; reflexivity); apply getr_zero|].
    split; [exact (i_flat _ _ _ _ _ _ HI')|]. split; [exact (i_frame _ _ _ _ _ _ HI')|].
    split; [exact Hcells | exact (i_grows _ _ _ _ _ _ HI')].
  - destruct HR' as (h & nx & lo & hi & X & _). discriminate X.
  - destruct HR' as (js & bj & lo & X & _). discriminate X.
Qed.

End WithSegs.

Lemma outside_lit : forall E (FL : list SR.region) a,
  Forall (fun r : SR.region => let '(_, _, n) := r in 0 <= n < 2 ^ 64) FL ->
  SR.outside E FL a <-> outside E (map of_lit_region FL) a.
Proof.
  intros E FL a HB. unfold SR.outside, outside. rewrite Forall_map. split; intros H.
  - apply Forall_forall. intros [[rb rlo] rlen] Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as X.
    pose proof (proj1 (Forall_forall _ _) HB _ Hin) as B. cbn beta iota in X, B |- *. unfold of_lit_region. rewrite (elenZ_litZ E rlen) by lia. exact X.
  - apply Forall_forall. intros [[rb rlo] rlen] Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as X.
    pose proof (proj1 (Forall_forall _ _) HB _ Hin) as B. cbn beta iota in X, B |- *. unfold of_lit_region in X. rewrite (elenZ_litZ E rlen) in X by lia. exact X.
Qed.
Lemma regions_ok_lit : forall E (FL : list SR.region),
  Forall (fun r : SR.region => let '(_, _, n) := r in 0 <= n < 2 ^ 64) FL ->
  regions_ok E (map of_lit_region FL) <-> SR.regions_ok E FL.
Proof.
  intros E FL HB. unfold SR.regions_ok, regions_ok. rewrite Forall_map. split; intros H.
  - apply Forall_forall. intros [[rb rlo] rlen] Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as X.
    pose proof (proj1 (Forall_forall _ _) HB _ Hin) as B. cbn beta iota in X, B |- *. unfold of_lit_region in X. rewrite (elenZ_litZ E rlen) in X by lia. exact X.
  - apply Forall_forall. intros [[rb rlo] rlen] Hin. pose proof (proj1 (Forall_forall _ _) H _ Hin) as X.
    pose proof (proj1 (Forall_forall _ _) HB _ Hin) as B. cbn beta iota in X, B |- *. unfold of_lit_region. rewrite (elenZ_litZ E rlen) by lia. exact X.
Qed.

Definition xstep_none (F : list region) (id : nat) (ss : sym_state) : option sym_state := None.
Definition xstep2_none (F : list region) (id : nat) (ss : sym_state) : option (sym_state * sym_state) := None.
Lemma xstep2_none_ok : forall segs nx0 BR F M0, XSTEP2_ok segs nx0 BR xstep2_none F M0.
Proof. intros segs nx0 BR F M0 _ _ fx id ss ssa ssb E R Mc H _. discriminate H. Qed.
Lemma xstep_none_ok : forall segs nx0 BR F M0, XSTEP_ok segs nx0 BR xstep_none F M0.
Proof. intros segs nx0 BR F M0 _ _ fx id ss ss' E R Mc H. discriminate H. Qed.
End SGP.
