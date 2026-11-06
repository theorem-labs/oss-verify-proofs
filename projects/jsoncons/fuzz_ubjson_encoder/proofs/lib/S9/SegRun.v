(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  FPSteps AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SR.
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.
Variable IT : itab.
Variable x_cpy : Z.
Variable x_set : Z.
Variable x_len : Z.
Variable ro_lo ro_hi : Z.

Inductive went : Type :=
| WSt (a : saddr) (wd : nat) (v : expr)
| WCopy (db : expr) (dk : Z) (sb : expr) (sk : Z) (n : Z)
| WFill (db : expr) (dk : Z) (n : Z) (c : Z).

Fixpoint wden (E : env) (M : word -> option byte) (w : list went) : word -> option byte :=
  match w with
  | [] => M
  | WSt a wd v :: r => wbytes (wden E M r) (adenot E a) (word_to_le_bytes wd (edenot E v))
  | WCopy db dk sb sk n :: r =>
      let m := wden E M r in
      match rdn segs m (adenot E (SA sb sk)) (Z.to_nat n) with
      | Some bs => wbytes m (adenot E (SA db dk)) bs
      | None => m
      end
  | WFill db dk n c :: r => wbytes (wden E M r) (adenot E (SA db dk)) (repeat (Z_to_bv 8 c) (Z.to_nat n))
  end.

Fixpoint wlog (log : list sentry) : list went :=
  match log with [] => [] | SE a wd v :: r => WSt a wd v :: wlog r end.

Lemma wden_wlog : forall E M log w, wden E M (wlog log ++ w) = mem_denot E (wden E M w) log.
Proof.
  intros E M log w. induction log as [|[a wd v] r IH]; cbn [wlog app wden mem_denot]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Definition went_vars_lt (b : nat) (g : went) : bool :=
  match g with
  | WSt a _ v => APC.expr_vars_lt b (a_base a) && APC.expr_vars_lt b v
  | WCopy db _ sb _ _ => APC.expr_vars_lt b db && APC.expr_vars_lt b sb
  | WFill db _ _ _ => APC.expr_vars_lt b db
  end%bool.
Definition wl_vars_lt (b : nat) (w : list went) : bool := forallb (went_vars_lt b) w.

Lemma edenot_agree_AP : forall b E E' e, env_agree b E E' -> APC.expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e Hag H. apply (edenot_agree b); [exact Hag|].
  induction e; cbn in *; try reflexivity; try exact H;
    try (apply andb_true_iff in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity).
Qed.

Lemma wden_agree : forall b E E' M w, env_agree b E E' -> wl_vars_lt b w = true -> wden E M w = wden E' M w.
Proof.
  intros b E E' M w Hag. induction w as [|g r IH]; intros H; [reflexivity|].
  cbn [wl_vars_lt forallb] in H. apply andb_true_iff in H as [Hg Hr].
  destruct g as [[ab ak] wd v|db dk sb sk n|db dk n c]; cbn [wden went_vars_lt a_base] in *;
    rewrite (IH Hr).
  - apply andb_true_iff in Hg as [H1 H2]. unfold adenot. cbn [a_base a_off].
    rewrite (edenot_agree_AP b E E' ab Hag H1), (edenot_agree_AP b E E' v Hag H2). reflexivity.
  - apply andb_true_iff in Hg as [H1 H2]. unfold adenot. cbn [a_base a_off].
    rewrite (edenot_agree_AP b E E' db Hag H1), (edenot_agree_AP b E E' sb Hag H2). reflexivity.
  - unfold adenot. cbn [a_base a_off]. rewrite (edenot_agree_AP b E E' db Hag Hg). reflexivity.
Qed.

Lemma wl_vars_lt_mono : forall b b' w, (b <= b')%nat -> wl_vars_lt b w = true -> wl_vars_lt b' w = true.
Proof.
  intros b b' w Hle H. unfold wl_vars_lt in *. rewrite forallb_forall in *. intros g Hg. specialize (H g Hg).
  assert (MONO : forall e, APC.expr_vars_lt b e = true -> APC.expr_vars_lt b' e = true).
  { intros e. induction e; cbn; intros He; try reflexivity; try exact He;
      try (apply andb_true_iff in He as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
      try (apply IHe; exact He).
    apply Nat.ltb_lt in He. apply Nat.ltb_lt. lia. }
  destruct g; cbn [went_vars_lt] in *;
    repeat (apply andb_true_iff in H as [?H1 H]); rewrite ?andb_true_iff; auto.
Qed.

Inductive sstep : Type :=
| SBlock (stops : list Z)
| SCopy
| SFill
| SFsdSeq (n : nat)
| SFldSeq (n : nat)
| SStrlen (k : Z)
| SExpect (pc : Z)
| SDiamond (joinpc : Z)
| SEvalReg (r : nat).

Variable BFUEL : nat.

Definition closed (ss : sym_state) (w : list went) : bool :=
  (APC.sr_vars_lt (s_next ss) (s_regs ss) && APC.kn_vars_lt (s_next ss) (s_know ss) && wl_vars_lt (s_next ss) w
   && match s_log ss with [] => true | _ => false end)%bool.

Definition reg (ss : sym_state) (n : nat) : expr := nth n (s_regs ss) (ELit 0).
Definition ret_lit (ss : sym_state) : option Z :=
  match reg ss 1 with
  | ELit r => if (Z.eqb (r mod 2) 0 && Z.ltb r two64 && Z.leb 0 r)%bool then Some r else None
  | _ => None
  end.

Definition after_call (ss : sym_state) (ret : Z) (rv : expr) (k' : list kentry) : sym_state :=
  let nx := s_next ss in
  SS ret (sr_upd (APC.sr_fresh (s_regs ss) APC.caller_saved nx) 10 rv) [] k' (nx + APC.NCS)%nat.

Definition step_block (stops : list Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let ss' := sym_execTX segs IT 0%nat BFUEL true stops ss in
  match carry (s_log ss') (s_know ss') [] with
  | (kn', [], _) => Some (SS (s_pc ss') (s_regs ss') [] kn' (s_next ss'), wlog (s_log ss') ++ w)
  | _ => None
  end.

Fixpoint kimg_precut (k : list kentry) (db : expr) (dk n : Z) : list kentry :=
  match k with
  | [] => []
  | KImg lo hi :: r =>
      match db with
      | ELit 0 =>
          (if Z.ltb lo (Z.min dk hi) then [KImg lo (Z.min dk hi)] else [])
          ++ (if Z.ltb (Z.max lo (dk + n)) hi then [KImg (Z.max lo (dk + n)) hi] else [])
          ++ kimg_precut r db dk n
      | _ => KImg lo hi :: kimg_precut r db dk n
      end
  | K :: r => K :: kimg_precut r db dk n
  end.

Definition step_copy (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in
  if negb (Z.eqb (s_pc ss) x_cpy) then None else
  match ret_lit ss, reg ss 12 with
  | Some ret, ELit n0 =>
      let n := n0 mod two64 in
      let dst := reg ss 10 in let src := reg ss 11 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xhi fk dst, xhi fk src with
      | Some dhi, Some shi =>
      if (Z.ltb 0 n && Z.leb n 2048 && Z.ltb (dhi + n) two64 && Z.ltb (shi + n) two64
          && APC.flat_x fk db dk (ELit n) && APC.flat_x fk sb sk (ELit n)
          && APC.kwritable_x fk k db dk (ELit n) && ranges_apart_x fk db dk (ELit n) sb sk (ELit n))%bool
      then match APC.copy_facts segs (Z.to_nat n) k sb sk db dk n with
           | Some kc =>
               let k' := kc ++ APC.kn_havoc (kimg_precut k db dk n) db dk (ELit n) in
               if APC.kn_vars_lt (s_next ss) k' then Some (after_call ss ret dst k', WCopy db dk sb sk n :: w) else None
           | None => None
           end
      else None
      | _, _ => None
      end
  | _, _ => None
  end.

Definition step_fill (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in
  if negb (Z.eqb (s_pc ss) x_set) then None else
  match ret_lit ss, reg ss 11, reg ss 12 with
  | Some ret, ELit c0, ELit n0 =>
      let n := n0 mod two64 in let c8 := (c0 mod two64) mod 256 in
      let dst := reg ss 10 in let '(db, dk) := split_lit dst in
      match xhi fk dst with
      | Some dhi =>
      if (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.ltb (dhi + n) two64
          && APC.flat_x fk db dk (ELit n) && APC.kwritable_x fk k db dk (ELit n))%bool
      then let k' := (if Z.eqb c8 0 then KZero (SA db dk) (ELit n) else KFill (SA db dk) (ELit n) c8)
                      :: APC.kn_havoc (kimg_precut k db dk n) db dk (ELit n) in
           if APC.kn_vars_lt (s_next ss) k' then Some (after_call ss ret dst k', WFill db dk n c8 :: w) else None
      else None
      | None => None
      end
  | _, _, _ => None
  end.

Fixpoint fsd_targets (p : Z) (n : nat) (ss : sym_state) : option (list (expr * Z)) :=
  match n with
  | O => Some []
  | S n' =>
      match itab_lookup IT p with
      | Some (FStore FMT_D rs1 _ imm) =>
          match fsd_targets (p + 4) n' ss with
          | Some r => Some (split_lit (mkAlu ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm))) :: r)
          | None => None
          end
      | _ => None
      end
  end.
Fixpoint consecutive (b : expr) (k : Z) (l : list (expr * Z)) : bool :=
  match l with [] => true | (b', k') :: r => expr_eqb b' b && Z.eqb k' k && consecutive b (k + 8) r end%bool.
Fixpoint kslots (db : expr) (dk : Z) (vs : list expr) : list kentry :=
  match vs with [] => [] | v :: r => KWord (SA db dk) 8 v :: kslots db (dk + 8) r end.
Fixpoint wslots_went (db : expr) (dk : Z) (vs : list expr) (acc : list went) : list went :=
  match vs with [] => acc | v :: r => wslots_went db (dk + 8) r (WSt (SA db dk) 8 v :: acc) end.
Definition step_fsdseq (n : nat) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  match fsd_targets (s_pc ss) n ss with
  | Some ((db, dk) :: rest) =>
      let len := 8 * Z.of_nat n in
      match xhi fk (mkAlu ALU_ADD db (ELit dk)) with
      | Some dhi =>
      if (consecutive db (dk + 8) rest && Z.ltb (dhi + len) two64
          && APC.flat_x fk db dk (ELit len) && APC.kwritable_x fk k db dk (ELit len) && APC.expr_vars_lt nx db)%bool
      then let vs := map (fun j => EVar (nx + j)%nat) (seq 0 n) in
           let kh := APC.kn_havoc (kimg_precut k db dk len) db dk (ELit len) in
           let k' := kslots db dk vs ++ kh in
           if (APC.kn_vars_lt (nx + n) k' && APC.kn_vars_lt nx kh)%bool
           then Some (SS (s_pc ss + 4 * Z.of_nat n) (s_regs ss) [] k' (nx + n)%nat, wslots_went db dk vs w)
           else None
      else None
      | None => None
      end
  | _ => None
  end.

Fixpoint fld_sources_ok (p : Z) (n : nat) (ss : sym_state) : bool :=
  match n with
  | O => true
  | S n' =>
      match itab_lookup IT p with
      | Some (FLoad FMT_D _ rs1 imm) =>
          let a := to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm) in
          kn_readable segs (facts_of (s_know ss)) (s_know ss) (a_base a) (a_off a) 8 && fld_sources_ok (p + 4) n' ss
      | _ => false
      end
  end%bool.
Definition step_fldseq (n : nat) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  if fld_sources_ok (s_pc ss) n ss
  then Some (SS (s_pc ss + 4 * Z.of_nat n) (s_regs ss) [] (s_know ss) (s_next ss), w)
  else None.

Fixpoint bytes_nonzero (fk k : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match know_lookup segs k b off 1 false [] [] with
            | LHit (ELit z) [] _ => negb (Z.eqb (z mod 256) 0) && bytes_nonzero fk k b (off + 1) n'
            | _ => false
            end
  end%bool.
Definition byte_zero (k : list kentry) (b : expr) (off : Z) : bool :=
  match know_lookup segs k b off 1 false [] [] with LHit (ELit z) [] _ => Z.eqb (z mod 256) 0 | _ => false end.
Fixpoint words_readable (fk k : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => kn_readable segs fk k b off 1 && words_readable fk k b (off + 1) n'
  end%bool.
Definition ro_covered (k : list kentry) : bool :=
  existsb (fun K => match K with KImg lo hi => (Z.leb lo ro_lo && Z.leb ro_hi hi)%bool | _ => false end) k.
Definition step_strlen (kz : Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  if negb (Z.eqb (s_pc ss) x_len) then None else
  match ret_lit ss with
  | Some ret =>
      let sp := reg ss 10 in let '(sb, sk) := split_lit sp in
      match xhi fk sp, ealign k sb with
      | Some shi, al =>

          let hi := (sk + kz) - (sk + kz) mod 8 + 8 in
          if (Z.leb 0 kz && Z.ltb (shi + (hi - sk)) two64 && Z.leb 3 al
              && bytes_nonzero fk k sb sk (Z.to_nat kz) && byte_zero k sb (sk + kz)
              && words_readable fk k sb (sk + kz + 1) (Z.to_nat (hi - (sk + kz + 1)))
              && APC.flat_x fk sb sk (ELit (hi - sk))
              && ro_covered k)%bool
          then Some (SS ret (sr_upd (APC.sr_fresh (s_regs ss) [11; 12; 13; 14; 15; 16]%nat nx) 10 (ELit kz)) [] k (nx + 6)%nat, w)
          else None
      | None, _ => None
      end
  | None => None
  end.

Definition EVMAX : Z := 8192.

Fixpoint evars (e : expr) (acc : option (list nat)) : option (list nat) :=
  match acc with
  | None => None
  | Some l =>
      match e with
      | ELit _ => acc
      | EVar n => Some (if existsb (Nat.eqb n) l then l else n :: l)
      | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars b (evars a acc)
      | EExt _ _ _ a => evars a acc
      | EBlob _ _ _ _ => None
      end
  end.

Fixpoint efold (x : nat) (k : Z) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar n => if Nat.eqb n x then ELit k else e
  | EAlu op a b => mkAlu op (efold x k a) (efold x k b)
  | EAluw op a b => mkAluw op (efold x k a) (efold x k b)
  | EMd op a b => mkMd op (efold x k a) (efold x k b)
  | EMdw op a b => mkMdw op (efold x k a) (efold x k b)
  | EExt sx lo n a => if Nat.leb n 8 then mkExt sx lo n (efold x k a) else EExt sx lo n (efold x k a)
  | EBlob _ _ _ _ => e
  end.
Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.
Definition eval_range (k : list kentry) (e : expr) : option Z :=
  match evars e (Some []) with
  | Some [x] =>
      match erange k (EVar x) with
      | Some (lo, hi) =>
          if (Z.leb lo hi && Z.leb (hi - lo) EVMAX)%bool then
            match efold x lo e with
            | ELit c => if forallb (fun v => expr_eqb (efold x v e) (ELit c)) (zseq lo (Z.to_nat (hi - lo + 1))) then Some c else None
            | _ => None
            end
          else None
      | None => None
      end
  | _ => None
  end.
Definition step_evalreg (r : nat) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  if (Nat.ltb 0 r && Nat.ltb r 32)%bool then
    match eval_range (s_know ss) (reg ss r) with
    | Some c => Some (SS (s_pc ss) (sr_upd (s_regs ss) r (ELit c)) [] (s_know ss) (s_next ss), w)
    | None => None
    end
  else None.

Definition acs_of (ss : sym_state) : APC.acs := APC.ACS ss [] 0 0 0 [] [] 0 (ELit 0) APC.FdStd false.
Fixpoint join_regs (i : nat) (ra rb : list expr) (nx : nat) : list expr * nat :=
  match ra, rb with
  | a :: ra', b :: rb' =>
      if expr_eqb a b then let '(r, n) := join_regs (S i) ra' rb' nx in (a :: r, n)
      else let '(r, n) := join_regs (S i) ra' rb' (S nx) in (EVar nx :: r, n)
  | _, _ => ([], nx)
  end.
Definition arm_ok (joinpc : Z) (nx : nat) (sa : sym_state) : bool :=
  (Z.eqb (s_pc sa) joinpc && match s_log sa with [] => true | _ => false end && Nat.eqb (s_next sa) nx
   && APC.sr_vars_lt nx (s_regs sa) && Nat.eqb (length (s_regs sa)) 32
   && match s_regs sa with ELit 0 :: _ => true | _ => false end)%bool.
Definition step_diamond (joinpc : Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let nx := s_next ss in
  match APC.branch_probe IT (acs_of ss) with
  | Some e =>
      match erange k e with
      | Some (lo, hi) =>
          let sa := sym_execTX segs IT 0%nat BFUEL true [joinpc] (SS (s_pc ss) (s_regs ss) [] (KRange e lo 0 :: k) nx) in
          let sb := sym_execTX segs IT 0%nat BFUEL true [joinpc] (SS (s_pc ss) (s_regs ss) [] (KRange e 1 hi :: k) nx) in
          if (AxSymRun3.expr_vars_lt nx e && arm_ok joinpc nx sa && arm_ok joinpc nx sb)%bool then
            let '(rj, nx') := join_regs 0 (s_regs sa) (s_regs sb) nx in
            Some (SS joinpc rj [] k nx', w)
          else None
      | None => None
      end
  | None => None
  end.

Definition seg_step (st : sstep) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  if negb (closed ss w) then None else
  match st with
  | SBlock stops => step_block stops ss w
  | SCopy => step_copy ss w
  | SFill => step_fill ss w
  | SFsdSeq n => step_fsdseq n ss w
  | SFldSeq n => step_fldseq n ss w
  | SStrlen kz => step_strlen kz ss w
  | SExpect pc => if Z.eqb (s_pc ss) pc then Some (ss, w) else None
  | SDiamond jp => step_diamond jp ss w
  | SEvalReg r => step_evalreg r ss w
  end.

Fixpoint seg_run (steps : list sstep) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  match steps with
  | [] => if closed ss w then Some (ss, w) else None
  | st :: rest => match seg_step st ss w with Some (ss', w') => seg_run rest ss' w' | None => None end
  end.

Fixpoint seg_run_dbg (i : nat) (steps : list sstep) (ss : sym_state) (w : list went) : nat * bool * sym_state * nat :=
  match steps with
  | [] => (i, closed ss w, ss, length w)
  | st :: rest => match seg_step st ss w with
                  | Some (ss', w') => seg_run_dbg (S i) rest ss' w'
                  | None => (i, false, ss, length w)
                  end
  end.

Hypothesis IT_ok : itab_sound segs IT.

Hypothesis COPY : forall fx : FPState, @APSX.copy_spec fx segs x_cpy.
Hypothesis FILL : forall fx : FPState, @APSX.fill_spec fx segs x_set two64.

Definition strlen_spec (entry : Z) : Prop :=
  forall (fx : FPState) (mem : word -> option byte) (s : word) (buf : list byte) (K : Z)
         (rom : word -> option byte) (regs : bvmap 5 word) (ret : word),
    rdn segs mem s (length buf) = Some buf ->
    (bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 ->
    0 <= K ->
    bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0) ->
    (forall i, ro_lo <= i < ro_hi -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s ->
    exists regs',
      msteps segs (@mkst fx regs (Z_to_bv 64 entry) mem rom) (@mkst fx regs' ret mem rom)
      /\ (forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
            getr regs' r = getr regs r)
      /\ getr regs' 10%bv = Z_to_bv 64 K.

Lemma pow64_pos : (0 < 2 ^ 64)%Z.
Proof. reflexivity. Qed.

Definition INV (E : env) (ss : sym_state) (w : list went) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  regs_ok E (s_regs ss) R /\ know_ok segs E (wden E M w) (s_know ss).

Lemma closed_parts : forall ss w, closed ss w = true ->
  AxSymRun3.sr_vars_lt (s_next ss) (s_regs ss) = true /\ AxSymRun3.kn_vars_lt (s_next ss) (s_know ss) = true
  /\ wl_vars_lt (s_next ss) w = true /\ s_log ss = [].
Proof.
  intros ss w H. unfold closed in H.
  apply andb_true_iff in H as [H Hl]. apply andb_true_iff in H as [H Hw]. apply andb_true_iff in H as [Hs Hk].
  rewrite APS.sr_vars_lt_eq in Hs. rewrite APS.kn_vars_lt_eq in Hk.
  repeat split; try assumption. destruct (s_log ss); [reflexivity | discriminate].
Qed.

Definition STEP_POST (fx : FPState) (ss : sym_state) (w : list went) (ss' : sym_state) (w' : list went)
           (E : env) (R : bvmap 5 word) (M rom : word -> option byte) : Prop :=
  exists (fx' : FPState) E' R', env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV E' ss' w' R' M /\
    msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) (wden E M w) rom)
                (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) (wden E' M w') rom).

Lemma some_pair_inj : forall {A B} (a c : A) (b d : B), Some (a, b) = Some (c, d) -> a = c /\ b = d.
Proof. intros A B a c b d H. injection H as -> ->. split; reflexivity. Qed.
Lemma step_block_sound : forall (fx : FPState) stops ss w ss' w' E R M rom,
  closed ss w = true -> step_block stops ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M rom.
Proof.
  intros fx stops ss w ss' w' E R M rom Hcl H [HR HK].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_block in H.
  destruct ss as [p sr log k nx rsv]. cbn [s_pc s_regs s_log s_know s_next] in *. subst log.
  set (ss1 := sym_execTX segs IT 0%nat BFUEL true stops (SSR p sr [] k nx rsv)) in H.
  destruct (carry (s_log ss1) (s_know ss1) []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection H as <- <-.
  assert (Hx : sym_execTX segs IT 0%nat BFUEL true stops (SS p sr [] k nx) = ss1).
  { subst ss1. unfold sym_execTX. reflexivity. }
  pose proof (@runTX_sound fx segs IT 0%nat BFUEL stops p sr k nx E (wden E M w) rom R IT_ok HR HK Fsr Fkn) as X.
  cbn zeta in X. rewrite Hx in X. destruct X as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms & _).
  exists fx, E', R'. split; [exact Hag|]. split; [exact Hle|].
  assert (Hw : wden E' M w = wden E M w) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  split.
  - split; cbn [s_regs s_know]; [exact HR'|].
    rewrite wden_wlog, Hw. eapply carry_after; [exact Hc | exact Hlf | exact HK' | constructor].
  - cbn [s_pc]. rewrite wden_wlog, Hw. exact Hms.
Qed.

Lemma reg_sound1 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 1%bv = edenot E (reg ss 1).
Proof. intros E ss R HR. exact (HR 1%bv). Qed.
Lemma reg_sound10 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 10%bv = edenot E (reg ss 10).
Proof. intros E ss R HR. exact (HR 10%bv). Qed.
Lemma reg_sound11 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 11%bv = edenot E (reg ss 11).
Proof. intros E ss R HR. exact (HR 11%bv). Qed.
Lemma reg_sound12 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 12%bv = edenot E (reg ss 12).
Proof. intros E ss R HR. exact (HR 12%bv). Qed.

Lemma ret_lit_sound : forall E ss R r, regs_ok E (s_regs ss) R -> ret_lit ss = Some r ->
  getr R 1%bv = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ 0 <= r < two64.
Proof.
  intros E ss R r HR H. unfold ret_lit in H.
  destruct (reg ss 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (reg_sound1 E ss R HR) as R1. rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_of_Z by (unfold two64 in Hlt; lia). exact He.
Qed.

Lemma nth_sr_vars_lt : forall b sr r, APC.sr_vars_lt b sr = true -> (r < 32)%nat -> APC.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [APC.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma kimg_precut_ok : forall E M k db dk n, know_ok segs E M k -> know_ok segs E M (kimg_precut k db dk n).
Proof.
  intros E M k db dk n H. induction k as [|K r IH]; [constructor|].
  apply Forall_cons_iff in H as [HK Hr]. specialize (IH Hr). cbn [kimg_precut].
  assert (PIECE : forall lo hi lo' hi', kentry_ok segs E M (KImg lo hi) -> lo <= lo' -> hi' <= hi ->
                   kentry_ok segs E M (KImg lo' hi')).
  { intros lo hi lo' hi' X Hlo Hhi. cbn [kentry_ok] in *. destruct X as (X0 & X1 & X2).
    split; [lia|]. split; [lia|]. intros i Hi. apply X2. lia. }
  destruct K as [| | |lo hi| | | | | |]; try (constructor; assumption).
  destruct db as [z| | | | | | |]; [destruct z|..]; try (constructor; assumption).
  apply Forall_app. split; [|apply Forall_app; split; [|exact IH]].
  - destruct (Z.ltb lo (Z.min dk hi)) eqn:C; [|constructor]. apply Z.ltb_lt in C.
    constructor; [|constructor]. eapply PIECE; [exact HK | lia | lia].
  - destruct (Z.ltb (Z.max lo (dk + n)) hi) eqn:C; [|constructor]. apply Z.ltb_lt in C.
    constructor; [|constructor]. eapply PIECE; [exact HK | lia | lia].
Qed.

Lemma step_copy_sound : forall (fx : FPState) ss w ss' w' E R M,
  closed ss w = true -> step_copy ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_copy in H.
  destruct (Z.eqb (s_pc ss) x_cpy) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg ss 12) as [n0| | | | | | |] eqn:H12; try discriminate.
  destruct (split_lit (reg ss 10)) as [db dk] eqn:Hsd. destruct (split_lit (reg ss 11)) as [sb sk] eqn:Hss.
  destruct (xhi (facts_of (s_know ss)) (reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (reg ss 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (APC.copy_facts segs (Z.to_nat (n0 mod two64)) (s_know ss) sb sk db dk (n0 mod two64)) as [kc|] eqn:Hcf; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <- <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hap. rename X0 into Hwr. rename X1 into Hfs. rename X2 into Hfd. rename X3 into Hshi'. rename X4 into Hdhi'. rename X5 into Hn2048.
  apply Z.ltb_lt in Hc. apply Z.leb_le in Hn2048. apply Z.ltb_lt in Hdhi'. apply Z.ltb_lt in Hshi'.
  set (n := (n0 mod two64)%Z) in *. set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *.
  assert (Hn64 : 0 <= n < two64) by (subst n; unfold two64; apply Z.mod_pos_bound; lia).
  assert (Hndef : n = (n0 mod two64)%Z) by reflexivity. clearbody n. unfold two64 in Hn64, Hdhi', Hshi'.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; unfold two64 in Hn64; lia).
  destruct (APSX.w_flat_x_sound segs E m fk db dk (ELit n) HKf Hfd) as (Dlo & Dhi & _).
  destruct (APSX.w_flat_x_sound segs E m fk sb sk (ELit n) HKf Hfs) as (Slo & Shi & _).
  destruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit n) HKf HK Hwr) as (Wst & _ & _).
  pose proof (ranges_apart_x_sound segs E m fk db dk (ELit n) sb sk (ELit n) HKf Hap) as Hapart.
  change (bv_unsigned (edenot E (ELit n))) with (elenZ E (ELit n)) in Dhi, Shi.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  destruct (APSX.copy_facts_sound segs E m k sb db (Z.to_nat n) sk dk n kc HK Hcf ltac:(lia) ltac:(lia) Slo Shi Dlo Dhi)
    as (bs & Hlbs & Hrd & Hkc).

  destruct (ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (reg_sound10 E ss R HR) as R10. pose proof (reg_sound11 E ss R HR) as R11.
  pose proof (reg_sound12 E ss R HR) as R12. rewrite H12 in R12. cbn [edenot] in R12.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in R10. rewrite (APSX.w_split_lit_denot E (reg ss 11) sb sk Hss) in R11.
  change (bv_unsigned (edenot E db) + dk)%Z with D in R10. change (bv_unsigned (edenot E sb) + sk)%Z with S in R11.
  pose proof (xhi_sound segs E m fk (reg ss 10) dhi HKf Hdhi) as XD. pose proof (xhi_sound segs E m fk (reg ss 11) shi HKf Hshi) as XS.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in XD. rewrite (APSX.w_split_lit_denot E (reg ss 11) sb sk Hss) in XS.
  change (bv_unsigned (edenot E db) + dk)%Z with D in XD. change (bv_unsigned (edenot E sb) + sk)%Z with S in XS.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hc; lia).
  assert (HS64 : 0 <= S < 2 ^ 64) by (clear - Slo Shi Hc; lia).
  rewrite u64_of_Z in XD by exact HD64. rewrite u64_of_Z in XS by exact HS64.
  assert (R12' : getr R 12%bv = Z_to_bv 64 n).
  { rewrite R12. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Hndef. unfold two64, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_mod by (pose proof pow64_pos; lia). reflexivity. }

  assert (A1 : 0 <= n) by (clear - Hc; lia).
  assert (A3 : rdn segs m (Z_to_bv 64 S) (length bs) = Some bs) by (rewrite Hlbs; exact Hrd).
  assert (A4 : store_ok segs m (Z_to_bv 64 D) (length bs) = true) by (rewrite Hlbs; apply Wst; clear - Hc; lia).
  assert (A5 : bv_unsigned (Z_to_bv 64 D) + n <= bv_unsigned (Z_to_bv 64 S) \/ bv_unsigned (Z_to_bv 64 S) + n <= bv_unsigned (Z_to_bv 64 D))
    by (rewrite (u64_of_Z D HD64), (u64_of_Z S HS64); exact Hapart).
  assert (A6 : bv_unsigned (Z_to_bv 64 S) + n < 2 ^ 64) by (rewrite (u64_of_Z S HS64); clear - XS Hshi'; lia).
  assert (A7 : bv_unsigned (Z_to_bv 64 D) + n < 2 ^ 64) by (rewrite (u64_of_Z D HD64); clear - XD Hdhi'; lia).
  destruct (COPY fx m (Z_to_bv 64 D) (Z_to_bv 64 S) n bs R (Z_to_bv 64 ret) A1 Hlbs A3 A4 A5 A6 A7 Hrok R1 R10 R11 R12')
    as (regs' & Hms & Hkept & Ha0).

  set (nx := s_next ss) in *.
  exists fx, (APSX.ext_call E nx regs'), regs'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|]. split; [cbn [after_call s_next]; lia|].
  assert (Hw : wden (APSX.ext_call E nx regs') M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (Fdst : APC.expr_vars_lt nx (reg ss 10) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  assert (Fsrc : APC.expr_vars_lt nx (reg ss 11) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb. pose proof (APSX.split_lit_vars _ _ _ _ Hss Fsrc) as Fsb.
  assert (ED : adenot (APSX.ext_call E nx regs') (SA db dk) = Z_to_bv 64 D).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ db Hag Fdb). reflexivity. }
  assert (ES : adenot (APSX.ext_call E nx regs') (SA sb sk) = Z_to_bv 64 S).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ sb Hag Fsb). reflexivity. }
  assert (MEM : wden (APSX.ext_call E nx regs') M (WCopy db dk sb sk n :: w) = wbytes m (Z_to_bv 64 D) bs).
  { cbn [wden]. rewrite Hw, ES, ED. fold S in Hrd. rewrite Hrd. reflexivity. }
  split.
  - split.
    + cbn [after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0. rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd). reflexivity.
    + cbn [after_call s_know]. rewrite MEM.
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      apply Forall_app. split.
      * apply Hkc. rewrite <- Hlbs. apply rdn_wbytes_hit. rewrite u64_of_Z by lia. rewrite Hlbs. lia.
      * eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wbytes_grows].
        intros x Hx. rewrite Hlen in Hx. apply wbytes_out; rewrite ?Hlbs, ?u64_of_Z by lia; lia.
  - cbn [after_call s_pc]. rewrite MEM. rewrite Hpc. exact Hms.
Qed.

Lemma step_fill_sound : forall (fx : FPState) ss w ss' w' E R M,
  closed ss w = true -> step_fill ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_fill in H.
  destruct (Z.eqb (s_pc ss) x_set) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg ss 11) as [c0| | | | | | |] eqn:H11; try discriminate.
  destruct (reg ss 12) as [n0| | | | | | |] eqn:H12; try discriminate.
  destruct (split_lit (reg ss 10)) as [db dk] eqn:Hsd.
  destruct (xhi (facts_of (s_know ss)) (reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <- <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hwr. rename X0 into Hfd. rename X1 into Hdhi'. rename X2 into Hn40.
  apply Z.ltb_lt in Hc. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hdhi'.
  set (n := (n0 mod two64)%Z) in *. set (c8 := ((c0 mod two64) mod 256)%Z) in *.
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *.
  assert (Hn64 : 0 <= n < two64) by (subst n; unfold two64; apply Z.mod_pos_bound; lia).
  assert (Hndef : n = (n0 mod two64)%Z) by reflexivity. clearbody n. unfold two64 in Hn64, Hdhi'.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  destruct (APSX.w_flat_x_sound segs E m fk db dk (ELit n) HKf Hfd) as (Dlo & Dhi & _).
  destruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit n) HKf HK Hwr) as (Wst & _ & _).
  change (bv_unsigned (edenot E (ELit n))) with (elenZ E (ELit n)) in Dhi.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *.

  destruct (ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (reg_sound10 E ss R HR) as R10. pose proof (reg_sound11 E ss R HR) as R11.
  pose proof (reg_sound12 E ss R HR) as R12. rewrite H12 in R12. cbn [edenot] in R12. rewrite H11 in R11. cbn [edenot] in R11.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in R10. change (bv_unsigned (edenot E db) + dk)%Z with D in R10.
  pose proof (xhi_sound segs E m fk (reg ss 10) dhi HKf Hdhi) as XD.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in XD. change (bv_unsigned (edenot E db) + dk)%Z with D in XD.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hc; lia).
  rewrite u64_of_Z in XD by exact HD64.
  assert (R12' : getr R 12%bv = Z_to_bv 64 n).
  { rewrite R12. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Hndef. unfold two64, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_mod by (pose proof pow64_pos; lia). reflexivity. }
  assert (A1 : 0 <= n) by (clear - Hc; lia).
  assert (A2 : bv_unsigned (Z_to_bv 64 D) + n < 2 ^ 64) by (rewrite (u64_of_Z D HD64); clear - XD Hdhi'; lia).
  assert (A4 : store_ok segs m (Z_to_bv 64 D) (Z.to_nat n) = true) by (apply Wst; clear - Hc; lia).
  assert (A5 : bv_unsigned (Z_to_bv 64 c0) < two64) by (unfold two64; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 c0)) as X; exact (proj2 X)).
  destruct (FILL fx m (Z_to_bv 64 D) (Z_to_bv 64 c0) n R (Z_to_bv 64 ret) A1 A2 A4 A5 Hrok R1 R10 R11 R12')
    as (regs' & Hms & Hkept & Ha0).
  assert (Hc8 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c0)) = Z_to_bv 8 c8).
  { subst c8. rewrite APSX.Z_to_bv8_mod. f_equal; try (rewrite Z_to_bv_unsigned; reflexivity). }
  rewrite Hc8 in Hms.
  set (nx := s_next ss) in *.
  exists fx, (APSX.ext_call E nx regs'), regs'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|]. split; [cbn [after_call s_next]; lia|].
  assert (Hw : wden (APSX.ext_call E nx regs') M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (Fdst : APC.expr_vars_lt nx (reg ss 10) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb.
  assert (ED : adenot (APSX.ext_call E nx regs') (SA db dk) = Z_to_bv 64 D).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ db Hag Fdb). reflexivity. }
  set (M' := wbytes m (Z_to_bv 64 D) (repeat (Z_to_bv 8 c8) (Z.to_nat n))).
  assert (MEM : wden (APSX.ext_call E nx regs') M (WFill db dk n c8 :: w) = M').
  { cbn [wden]. rewrite Hw, ED. reflexivity. }
  assert (FILLED : forall i, 0 <= i < n -> M' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c8)).
  { intros i Hi. subst M'. rewrite <- (u64_of_Z D HD64) at 2. apply APSX.wbytes_fill_at; [rewrite (u64_of_Z D HD64); clear - A2 XD Hdhi'; lia | exact Hi]. }
  split.
  - split.
    + cbn [after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0. rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd). reflexivity.
    + cbn [after_call s_know]. rewrite MEM.
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      constructor.
      * destruct (Z.eqb c8 0) eqn:Hz; cbn [kentry_ok]; unfold flat, elenZ; cbn [a_base a_off edenot]; rewrite (u64_of_Z n) by lia;
          change (estart E (SA db dk)) with D.
        -- apply Z.eqb_eq in Hz. split; [clear - HD64 Dhi Hc; lia|]. intros i Hi. rewrite (FILLED i Hi), Hz. reflexivity.
        -- split; [clear - HD64 Dhi Hc; lia|]. intros i Hi. exact (FILLED i Hi).
      * eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wbytes_grows].
        intros x Hx. rewrite Hlen in Hx. subst M'. apply wbytes_out; rewrite ?repeat_length, ?Z2Nat.id, ?u64_of_Z by lia; clear - Hx Hc HD64 Dhi; lia.
  - cbn [after_call s_pc]. rewrite MEM. rewrite Hpc. exact Hms.
Qed.

Fixpoint wslots (m : word -> option byte) (a : Z) (vs : list word) : word -> option byte :=
  match vs with [] => m | v :: r => wslots (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)) (a + 8) r end.

Lemma wden_wslots_went : forall E M db dk vs acc,
  wden E M (wslots_went db dk vs acc) = wslots (wden E M acc) (estart E (SA db dk)) (map (edenot E) vs).
Proof.
  intros E M db dk vs. revert dk. induction vs as [|v r IH]; intros dk acc; cbn [wslots_went wslots map]; [reflexivity|].
  rewrite IH. cbn [wden]. rewrite APSX.adenot_SA.
  replace (estart E (SA db (dk + 8))) with (estart E (SA db dk) + 8)%Z by (unfold estart; cbn [a_base a_off]; lia).
  reflexivity.
Qed.

Lemma wslots_out : forall vs m a (x : word),
  0 <= a -> a + 8 * Z.of_nat (length vs) <= 2 ^ 64 ->
  (bv_unsigned x < a \/ a + 8 * Z.of_nat (length vs) <= bv_unsigned x) -> wslots m a vs x = m x.
Proof.
  induction vs as [|v r IH]; intros m a x Ha Hnw Hx; cbn [wslots length] in *; [reflexivity|].
  rewrite IH by lia. apply wbytes_out; rewrite length_N_to_le_bytes, (u64_of_Z a) by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma wslots_grows : forall vs m a, mem_grows m (wslots m a vs).
Proof.
  induction vs as [|v r IH]; intros m a; cbn [wslots]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [apply wbytes_grows | apply IH].
Qed.

Lemma wslots_slot : forall vs m a i,
  0 <= a -> a + 8 * Z.of_nat (length vs) <= 2 ^ 64 -> (i < length vs)%nat ->
  rdn segs (wslots m a vs) (Z_to_bv 64 (a + 8 * Z.of_nat i)) 8%nat = Some (word_to_le_bytes 8 (nth i vs (Z_to_bv 64 0))).
Proof.
  induction vs as [|v r IH]; intros m a i Ha Hnw Hi; cbn [wslots length nth] in *; [lia|].
  destruct i as [|i].
  - rewrite Z.mul_0_r, Z.add_0_r.
    rewrite <- (rdn_wbytes_hit8 segs m (Z_to_bv 64 a) v) by (rewrite u64_of_Z by lia; lia).
    apply rdn_ext; [rewrite u64_of_Z by lia; cbn; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia.
    apply wslots_out; cbn in Hx; lia.
  - replace (a + 8 * Z.of_nat (S i))%Z with ((a + 8) + 8 * Z.of_nat i)%Z by lia. apply IH; lia.
Qed.

Lemma ridx_bv5 : forall r : bv 5, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
  intros r. unfold ridx. rewrite Z2Nat.id by (pose proof (bv_unsigned_in_range _ r); lia). apply Z_to_bv_bv_unsigned.
Qed.
Lemma ridx_of_nat : forall i, (i < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat i)) = i.
Proof.
  intros i Hi. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma itab_fact : forall p i, itab_lookup IT p = Some i ->
  exists w, fetch_word segs (Z_to_bv 64 p) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z).
Proof.
  intros p i Hl. pose proof (IT_ok _ _ Hl) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word segs (Z_to_bv 64 p)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz. injection Hen as ->.
  exists w. split; [reflexivity|]. split; [exact Hec | exact Hd].
Qed.

Lemma fsd_run : forall (fx : FPState) n p ss tl E R (m : word -> option byte) (D : Z),
  fsd_targets p n ss = Some tl ->
  regs_ok E (s_regs ss) R ->
  (forall j bk, nth_error tl j = Some bk -> estart E (SA (fst bk) (snd bk)) = D + 8 * Z.of_nat j) ->
  0 <= D -> D + 8 * Z.of_nat n < 2 ^ 64 ->
  store_ok segs m (Z_to_bv 64 D) (Z.to_nat (8 * Z.of_nat n)) = true ->
  exists vals, length vals = n /\
    msteps segs (@mkst fx R (Z_to_bv 64 p) m (seg_rom segs))
                (@mkst fx R (Z_to_bv 64 (p + 4 * Z.of_nat n)) (wslots m D vals) (seg_rom segs)).
Proof.
  intros fx n. induction n as [|n IH]; intros p ss tl E R m D Htl HR Hest HD0 HDn Hst.
  - exists []. split; [reflexivity|]. cbn [wslots]. rewrite Z.mul_0_r, Z.add_0_r. apply mst_refl.
  - cbn [fsd_targets] in Htl.
    destruct (itab_lookup IT p) as [i|] eqn:Hl; [|discriminate].
    destruct i; try discriminate. destruct fmt; try discriminate.
    destruct (fsd_targets (p + 4) n ss) as [r|] eqn:Hr; [|discriminate]. injection Htl as <-.
    destruct (itab_fact p _ Hl) as (w & Hf & Hec & Hd).
    pose proof (Hest 0%nat _ eq_refl) as E0. cbn [fst snd] in E0. rewrite Z.mul_0_r, Z.add_0_r in E0.
    set (v := reg_get (@fp_regs fx) rs2).
    assert (Ha : v_addi (getr R rs1) (bv_signed imm) = Z_to_bv 64 D).
    { rewrite (HR rs1). rewrite <- E0.
      destruct (split_lit (mkAlu ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm)))) as [b0 k0] eqn:Hsp.
      cbn [fst snd]. unfold estart. cbn [a_base a_off].
      pose proof (APSX.w_split_lit_denot E _ b0 k0 Hsp) as X. rewrite <- X. rewrite mkAlu_denot. cbn [edenot].
      rewrite alu_add. unfold v_addi, v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
      rewrite Zplus_mod_idemp_r. reflexivity. }
    assert (Hst8 : store_ok segs m (Z_to_bv 64 D) 8%nat = true).
    { eapply (store_ok_sub segs m (Z_to_bv 64 D) (Z_to_bv 64 D) (Z.to_nat (8 * Z.of_nat (S n))) 8%nat); try exact Hst;
        rewrite ?u64_of_Z, ?Z2Nat.id by lia; lia. }
    pose proof (fp_step_fsd fx segs R (Z_to_bv 64 p) m (seg_rom segs) w rs1 rs2 imm (Z_to_bv 64 D) Hf Hec Hd Ha Hst8) as STEP.
    destruct (IH (p + 4) ss r E R (wbytes m (Z_to_bv 64 D) (word_to_le_bytes 8 v)) (D + 8) Hr HR) as (vals & Hlen & Hms).
    + intros j bk Hj. replace (D + 8 + 8 * Z.of_nat j)%Z with (D + 8 * Z.of_nat (S j))%Z by lia. apply Hest. cbn. exact Hj.
    + lia. + lia.
    + eapply store_ok_mono; [apply wbytes_grows|].
      eapply (store_ok_sub segs m (Z_to_bv 64 D) (Z_to_bv 64 (D + 8)) (Z.to_nat (8 * Z.of_nat (S n))) (Z.to_nat (8 * Z.of_nat n))); try exact Hst;
        rewrite ?u64_of_Z, ?Z2Nat.id by lia; lia.
    + exists (v :: vals). split; [cbn; lia|].
      eapply mst_step; [reflexivity | exact STEP |].
      replace (v_addi (Z_to_bv 64 p) 4) with (Z_to_bv 64 (p + 4)).
      2:{ unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus].
          change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. rewrite Zplus_mod_idemp_l. reflexivity. }
      replace (p + 4 * Z.of_nat (S n))%Z with (p + 4 + 4 * Z.of_nat n)%Z by lia.
      cbn [wslots]. exact Hms.
Qed.

Lemma consecutive_nth : forall l b k j bk, consecutive b k l = true -> nth_error l j = Some bk ->
  fst bk = b /\ snd bk = (k + 8 * Z.of_nat j)%Z.
Proof.
  induction l as [|[b' k'] r IH]; intros b k j bk H Hj; [destruct j; discriminate|].
  cbn [consecutive] in H. apply andb_true_iff in H as [H Hr]. apply andb_true_iff in H as [Hb Hk].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. subst b' k'.
  destruct j as [|j]; cbn [nth_error] in Hj.
  - injection Hj as <-. cbn [fst snd]. split; [reflexivity | lia].
  - destruct (IH b (k + 8)%Z j bk Hr Hj) as [A B]. split; [exact A | lia].
Qed.

Lemma fsd_targets_length : forall p n ss tl, fsd_targets p n ss = Some tl -> length tl = n.
Proof.
  intros p n. revert p. induction n as [|n IH]; intros p ss tl H; cbn [fsd_targets] in H.
  - injection H as <-. reflexivity.
  - destruct (itab_lookup IT p) as [i|]; [|discriminate]. destruct i; try discriminate. destruct fmt; try discriminate.
    destruct (fsd_targets (p + 4) n ss) as [r|] eqn:Hr; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH. exact Hr.
Qed.

Lemma step_fsdseq_sound : forall (fx : FPState) n ss w ss' w' E R M,
  closed ss w = true -> step_fsdseq n ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx n ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  cbv beta zeta delta [step_fsdseq] in H.
  destruct (fsd_targets (s_pc ss) n ss) as [[|[db dk] rest]|] eqn:Htl; try discriminate.
  destruct (xhi (facts_of (s_know ss)) (mkAlu ALU_ADD db (ELit dk))) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  apply some_pair_inj in H as [<- <-].
  apply andb_true_iff in Hc as [Hc Fdb]. apply andb_true_iff in Hc as [Hc Hwr]. apply andb_true_iff in Hc as [Hc Hfd]. apply andb_true_iff in Hc as [Hcons Hdhi'].
  apply Z.ltb_lt in Hdhi'. unfold two64 in Hdhi'. apply andb_true_iff in Hkv as [Hkv Hkvh].
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *. set (nx := s_next ss) in *.
  set (len := (8 * Z.of_nat n)%Z) in *.
  pose proof (fsd_targets_length _ _ _ _ Htl) as Hn. cbn [length] in Hn.
  assert (Hnpos : (1 <= n)%nat) by lia.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen64 : 0 < len < 2 ^ 64).
  { subst len. split; [lia|].
    pose proof (xhi_sound segs E m fk _ dhi HKf Hdhi) as X. pose proof (u64_range (edenot E (mkAlu ALU_ADD db (ELit dk)))). lia. }
  assert (Hlen : elenZ E (ELit len) = len) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  destruct (APSX.w_flat_x_sound segs E m fk db dk (ELit len) HKf Hfd) as (Dlo & Dhi & _).
  destruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit len) HKf HK Hwr) as (Wst & _ & _).
  change (bv_unsigned (edenot E (ELit len))) with (elenZ E (ELit len)) in Dhi. rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *.
  pose proof (xhi_sound segs E m fk _ dhi HKf Hdhi) as XD.
  rewrite mkAlu_denot in XD. cbn [edenot] in XD. rewrite alu_add in XD. unfold v_add in XD.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hlen64; lia).
  assert (XD' : D <= dhi).
  { unfold D, estart in *. cbn [a_base a_off] in *.
    replace (Z_to_bv 64 (bv_unsigned (edenot E db) + bv_unsigned (Z_to_bv 64 dk)))
      with (Z_to_bv 64 (bv_unsigned (edenot E db) + dk)) in XD.
    2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity. }
    rewrite u64_of_Z in XD by exact HD64. exact XD. }

  assert (EST : forall j bk, nth_error ((db, dk) :: rest) j = Some bk -> estart E (SA (fst bk) (snd bk)) = D + 8 * Z.of_nat j).
  { intros [|j] bk Hj.
    - cbn in Hj. injection Hj as <-. cbn [fst snd]. lia.
    - cbn [nth_error] in Hj. destruct (consecutive_nth _ _ _ _ _ Hcons Hj) as [A B].
      destruct bk as [b' k']. cbn [fst snd] in *. subst b' k'. unfold D, estart. cbn [a_base a_off]. lia. }
  destruct (fsd_run fx n (s_pc ss) ss _ E R m D Htl HR EST ltac:(lia) ltac:(clear - XD' Hdhi' HD64; lia)
              ltac:(apply Wst; subst len; rewrite Z2Nat.id by lia; lia)) as (vals & Hvl & Hms).

  set (E' := APS.ext_list E nx vals).
  pose proof (APS.ext_list_agree E nx vals) as Hag. fold E' in Hag.
  exists fx, E', R. split; [exact Hag|]. split; [cbn [s_next]; lia|].
  assert (Hw : wden E' M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (ED : estart E' (SA db dk) = D).
  { unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E E' db Hag Fdb). reflexivity. }
  assert (VALS : map (edenot E') (map (fun j => EVar (nx + j)%nat) (seq 0 n)) = vals).
  { rewrite map_map. rewrite <- (map_id vals). rewrite <- Hvl.
    transitivity (map (fun j => nth j vals (Z_to_bv 64 0)) (seq 0 (length vals))).
    - apply map_ext_in. intros j Hj. apply in_seq in Hj. cbn [edenot]. unfold E'. apply APS.ext_list_at. lia.
    - rewrite map_id. clear. induction vals as [|v r IH]; [reflexivity|].
      cbn [length]. rewrite <- cons_seq. cbn [map nth]. f_equal.
      rewrite <- seq_shift, map_map. cbn [nth]. exact IH. }
  assert (MEM : wden E' M (wslots_went db dk (map (fun j => EVar (nx + j)%nat) (seq 0 n)) w) = wslots m D vals).
  { rewrite wden_wslots_went, Hw, ED, VALS. reflexivity. }
  split.
  - split.
    + cbn [s_regs]. eapply APS.regs_ok_agree'; [exact Hag | exact Fsr0 | exact HR].
    + cbn [s_know]. rewrite MEM. apply Forall_app. split.
      * assert (SL : forall vs dk0 i0, (i0 + length vs = n)%nat -> estart E' (SA db dk0) = D + 8 * Z.of_nat i0 ->
                     (forall j, (j < length vs)%nat -> edenot E' (nth j vs (ELit 0)) = nth (i0 + j) vals (Z_to_bv 64 0)) ->
                     know_ok segs E' (wslots m D vals) (kslots db dk0 vs)).
        { induction vs as [|v r IH]; intros dk0 i0 Hl He Hv; cbn [kslots]; [constructor|].
          cbn [length] in Hl. constructor.
          - cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite He; clear - HD64 Hl XD' Hdhi'; lia|].
            rewrite APSX.adenot_SA, He. pose proof (Hv 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. rewrite H0, Nat.add_0_r.
            apply wslots_slot; [lia | rewrite Hvl; clear - HD64 XD' Hdhi'; lia | rewrite Hvl; lia].
          - apply (IH (dk0 + 8) (S i0)); [lia | unfold estart in *; cbn [a_base a_off] in *; lia |].
            intros j Hj. replace (S i0 + j)%nat with (i0 + S j)%nat by lia. apply (Hv (S j)). cbn [length]. lia. }
        apply (SL _ dk 0%nat).
        -- rewrite length_map, length_seq. reflexivity.
        -- rewrite ED. lia.
        -- intros j Hj. cbn [Nat.add]. rewrite <- VALS.
           change (Z_to_bv 64 0) with (edenot E' (ELit 0)). rewrite map_nth. reflexivity.
      * eapply APS.know_ok_agree'; [exact Hag | exact Hkvh |].
        eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wslots_grows].
        intros x Hx. rewrite Hlen in Hx. apply wslots_out; rewrite ?Hvl; clear - Hx HD64 XD' Hdhi'; subst len; lia.
  - cbn [s_pc]. rewrite MEM. exact Hms.
Qed.

Lemma fld_run : forall n (fx : FPState) p ss E R (m : word -> option byte) allkn,
  fld_sources_ok p n ss = true ->
  regs_ok E (s_regs ss) R -> know_ok segs E m allkn -> allkn = s_know ss ->
  exists fx' : FPState,
    msteps segs (@mkst fx R (Z_to_bv 64 p) m (seg_rom segs))
                (@mkst fx' R (Z_to_bv 64 (p + 4 * Z.of_nat n)) m (seg_rom segs)).
Proof.
  induction n as [|n IH]; intros fx p ss E R m allkn H HR HK Hak.
  - exists fx. rewrite Z.mul_0_r, Z.add_0_r. apply mst_refl.
  - cbn [fld_sources_ok] in H.
    destruct (itab_lookup IT p) as [i|] eqn:Hl; [|discriminate].
    destruct i; try discriminate. destruct fmt; try discriminate.
    apply andb_true_iff in H as [Hrd Hrest].
    destruct (itab_fact p _ Hl) as (w & Hf & Hec & Hd).
    subst allkn.
    destruct (kn_readable_sound segs E m (facts_of (s_know ss)) m (s_know ss) _ _ 8 (facts_of_ok segs E m _ HK) HK
                ltac:(lia) ltac:(lia) Hrd) as (Hfl & bs & Hbs & Hlbs).
    assert (Ha : v_addi (getr R rs1) (bv_signed imm) = adenot E (to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm))).
    { rewrite (HR rs1). rewrite to_saddr_denot. reflexivity. }
    pose proof (fp_step_fld fx segs R (Z_to_bv 64 p) m (seg_rom segs) w rd rs1 imm _ bs Hf Hec Hd Ha Hbs) as STEP.
    destruct (IH (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
                 (p + 4) ss E R m (s_know ss) Hrest HR HK eq_refl) as (fx' & Hms).
    exists fx'. eapply mst_step; [reflexivity | exact STEP |].
    replace (v_addi (Z_to_bv 64 p) 4) with (Z_to_bv 64 (p + 4)).
    2:{ unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus].
        change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. rewrite Zplus_mod_idemp_l. reflexivity. }
    replace (p + 4 * Z.of_nat (S n))%Z with (p + 4 + 4 * Z.of_nat n)%Z by lia. exact Hms.
Qed.

Lemma step_fldseq_sound : forall (fx : FPState) n ss w ss' w' E R M,
  closed ss w = true -> step_fldseq n ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx n ss w ss' w' E R M Hcl H [HR HK]. unfold step_fldseq in H.
  destruct (fld_sources_ok (s_pc ss) n ss) eqn:Hs; [|discriminate]. apply some_pair_inj in H as [<- <-].
  destruct (fld_run n fx (s_pc ss) ss E R (wden E M w) (s_know ss) Hs HR HK eq_refl) as (fx' & Hms).
  exists fx', E, R. split; [apply APS.env_agree_refl|]. split; [cbn [s_next]; lia|].
  split; [split; [exact HR | exact HK]|]. cbn [s_pc]. exact Hms.
Qed.

Definition strlen_step_stmt : Prop := forall (fx : FPState) kz ss w ss' w' E R M,
  closed ss w = true -> step_strlen kz ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).

Lemma efold_denot : forall E x k e, edenot E (efold x k e) = edenot (APS.upd E x (Z_to_bv 64 k)) e.
Proof.
  intros E x k e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n];
    cbn [efold edenot]; try reflexivity.
  - unfold APS.upd. cbn [ev]. destruct (Nat.eqb n x); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - destruct (Nat.leb n 8) eqn:Hn.
    + apply Nat.leb_le in Hn. rewrite mkExt_denot by exact Hn. rewrite IHa. reflexivity.
    + cbn [edenot]. rewrite IHa. reflexivity.
Qed.

Lemma evars_mono : forall e acc l, evars e acc = Some l -> exists l0, acc = Some l0 /\ incl l0 l.
Proof.
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n]; intros acc l H;
    destruct acc as [l0|]; cbn [evars] in H; try discriminate;
    try (destruct (IHb _ _ H) as (l1 & H1 & S1); destruct (IHa _ _ H1) as (l2 & H2 & S2); injection H2 as <-;
         exists l0; split; [reflexivity | eapply incl_tran; [exact S2 | exact S1]]).
  - injection H as <-. exists l0. split; [reflexivity | apply incl_refl].
  - injection H as <-. exists l0. split; [reflexivity|]. intros m Hm. destruct (existsb (Nat.eqb n) l0); [exact Hm | right; exact Hm].
  - exact (IHa _ _ H).
Qed.

Lemma evars_agree : forall e acc l E E',
  evars e acc = Some l -> (forall n, In n l -> ev E n = ev E' n) -> eb E = eb E' -> edenot E e = edenot E' e.
Proof.
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n]; intros acc l E E' H Hv Hb;
    destruct acc as [l0|]; cbn [evars edenot] in *; try discriminate; try reflexivity;
    try (destruct (evars_mono b _ _ H) as (l1 & H1 & S1);
         rewrite (IHa _ _ E E' H1), (IHb _ _ E E' H); [reflexivity | exact Hv | exact Hb | intros m Hm; apply Hv; apply S1; exact Hm | exact Hb]).
  - injection H as <-. apply Hv. destruct (existsb (Nat.eqb n) l0) eqn:Hx.
    + apply existsb_exists in Hx as (m & Hm & He). apply Nat.eqb_eq in He. subst m. exact Hm.
    + left. reflexivity.
  - first [rewrite (IHa _ _ E E' H Hv Hb); reflexivity | rewrite Hb; reflexivity].
Qed.

Lemma zseq_In : forall lo n v, lo <= v < lo + Z.of_nat n -> In v (zseq lo n).
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo v Hv; [lia|]. cbn [zseq].
  destruct (Z.eq_dec v lo) as [->|Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.

Lemma eval_range_sound : forall E M k e c,
  know_ok segs E M k -> eval_range k e = Some c -> edenot E e = Z_to_bv 64 c.
Proof.
  intros E M k e c HK H. unfold eval_range in H.
  destruct (evars e (Some [])) as [[|x [|]]|] eqn:Hev; try discriminate.
  destruct (erange k (EVar x)) as [[lo hi]|] eqn:Her; [|discriminate].
  destruct (Z.leb lo hi && Z.leb (hi - lo) EVMAX)%bool eqn:Hb; [|discriminate].
  apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  destruct (efold x lo e) as [c0| | | | | | |] eqn:Hf; try discriminate.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hall; [|discriminate] end.
  injection H as <-.
  pose proof (erange_sound segs E M k (EVar x) lo hi HK Her) as Hx. cbn [edenot] in Hx.
  set (v := bv_unsigned (ev E x)) in *.
  assert (Hin : In v (zseq lo (Z.to_nat (hi - lo + 1)))).
  { apply zseq_In. rewrite Z2Nat.id by lia. clear - Hx Hb1. lia. }
  rewrite forallb_forall in Hall. specialize (Hall v Hin).
  apply expr_eqb_eq in Hall.
  transitivity (edenot (APS.upd E x (Z_to_bv 64 v)) e).
  - eapply evars_agree; [exact Hev | | reflexivity]. intros n Hn. destruct Hn as [<-|[]].
    unfold APS.upd. cbn [ev]. rewrite Nat.eqb_refl. subst v. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite <- efold_denot, Hall. reflexivity.
Qed.

Lemma step_evalreg_sound : forall (fx : FPState) r ss w ss' w' E R M,
  closed ss w = true -> step_evalreg r ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx r ss w ss' w' E R M Hcl H [HR HK]. unfold step_evalreg in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32)%bool eqn:Hr; [|discriminate].
  apply andb_true_iff in Hr as [Hr0 Hr32]. apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32.
  destruct (eval_range (s_know ss) (reg ss r)) as [c|] eqn:Hev; [|discriminate]. injection H as <- <-.
  exists fx, E, R. split; [apply APS.env_agree_refl|]. split; [cbn [s_next]; lia|]. split.
  - split; [|cbn [s_know]; exact HK]. cbn [s_regs].
    pose proof (eval_range_sound E _ (s_know ss) (reg ss r) c HK Hev) as Hc.
    intros r'. unfold sr_get. destruct (bv_eqb r' 0) eqn:Hr'0.
    + specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR. exact HR.
    + rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') r) eqn:Hi.
      * apply Nat.eqb_eq in Hi. specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR.
        rewrite HR. unfold reg in Hc. rewrite <- Hi in Hc. rewrite Hc. reflexivity.
      * specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR. exact HR.
  - cbn [s_pc]. apply mst_refl.
Qed.

Lemma join_regs_sound : forall ra rb i nx rj nx' E (G : nat -> word) (side : bool),
  join_regs i ra rb nx = (rj, nx') -> length rb = length ra ->
  (forall j, (j < length ra)%nat -> G (i + j)%nat = edenot E (nth j (if side then ra else rb) (ELit 0))) ->
  (forall j, (j < length ra)%nat -> APC.expr_vars_lt nx (nth j ra (ELit 0)) = true /\ APC.expr_vars_lt nx (nth j rb (ELit 0)) = true) ->
  exists E', env_agree nx E E' /\ (nx <= nx')%nat /\ length rj = length ra
    /\ (forall j, (j < length ra)%nat -> G (i + j)%nat = edenot E' (nth j rj (ELit 0))).
Proof.
  induction ra as [|a ra IH]; intros rb i nx rj nx' E G side H Hlen HG Hv.
  - cbn [join_regs] in H. injection H as <- <-. exists E. split; [apply APS.env_agree_refl|]. split; [lia|]. split; [reflexivity|].
    intros j Hj. cbn in Hj. lia.
  - destruct rb as [|b rb]; [discriminate|]. cbn [length] in Hlen. injection Hlen as Hlen. cbn [join_regs] in H.
    assert (HG' : forall j, (j < length ra)%nat -> G (S i + j)%nat = edenot E (nth j (if side then ra else rb) (ELit 0))).
    { intros j Hj. replace (S i + j)%nat with (i + S j)%nat by lia. rewrite (HG (S j)) by (cbn; lia). destruct side; reflexivity. }
    assert (Hv' : forall j, (j < length ra)%nat -> APC.expr_vars_lt nx (nth j ra (ELit 0)) = true /\ APC.expr_vars_lt nx (nth j rb (ELit 0)) = true).
    { intros j Hj. exact (Hv (S j) ltac:(cbn; lia)). }
    destruct (Hv 0%nat ltac:(cbn; lia)) as [Hva Hvb]. cbn [nth] in Hva, Hvb.
    pose proof (HG 0%nat ltac:(cbn; lia)) as HG0. rewrite Nat.add_0_r in HG0. cbn [nth] in HG0.
    destruct (expr_eqb a b) eqn:Hab.
    + destruct (join_regs (S i) ra rb nx) as [r n] eqn:Hr. injection H as <- <-.
      destruct (IH rb (S i) nx r n E G side Hr Hlen HG' Hv') as (E' & Hag & Hle & Hlr & HR).
      exists E'. split; [exact Hag|]. split; [exact Hle|]. split; [cbn; lia|].
      intros [|j] Hj; cbn [nth].
      * rewrite Nat.add_0_r. rewrite HG0. apply expr_eqb_eq in Hab. subst b.
        destruct side; (eapply edenot_agree_AP; [exact Hag | first [exact Hva | exact Hvb]]).
      * replace (i + S j)%nat with (S i + j)%nat by lia. apply HR. cbn in Hj. lia.
    + destruct (join_regs (S i) ra rb (S nx)) as [r n] eqn:Hr. injection H as <- <-.
      set (E1 := APS.upd E nx (G i)).
      assert (Hag1 : env_agree nx E E1).
      { split; [|reflexivity]. intros m Hm. unfold E1, APS.upd. cbn [ev]. destruct (Nat.eqb m nx) eqn:He; [apply Nat.eqb_eq in He; lia | reflexivity]. }
      assert (HG1 : forall j, (j < length ra)%nat -> G (S i + j)%nat = edenot E1 (nth j (if side then ra else rb) (ELit 0))).
      { intros j Hj. rewrite (HG' j Hj). destruct (Hv' j Hj) as [X Y].
        destruct side; (eapply edenot_agree_AP; [exact Hag1 | first [exact X | exact Y]]). }
      assert (Hv1 : forall j, (j < length ra)%nat -> APC.expr_vars_lt (S nx) (nth j ra (ELit 0)) = true /\ APC.expr_vars_lt (S nx) (nth j rb (ELit 0)) = true).
      { intros j Hj. destruct (Hv' j Hj) as [X Y]. split; (eapply APS.expr_vars_lt_mono; [eassumption | lia]). }
      destruct (IH rb (S i) (S nx) r n E1 G side Hr Hlen HG1 Hv1) as (E' & Hag & Hle & Hlr & HR).
      exists E'. split.
      { eapply APS.env_agree_trans; [exact Hag1 | eapply APS.env_agree_le; [exact Hag | lia]]. }
      split; [lia|]. split; [cbn; lia|].
      intros [|j] Hj; cbn [nth].
      * rewrite Nat.add_0_r. cbn [edenot]. destruct Hag as [Hagv _]. rewrite <- (Hagv nx) by lia. unfold E1, APS.upd. cbn [ev]. rewrite Nat.eqb_refl. reflexivity.
      * replace (i + S j)%nat with (S i + j)%nat by lia. apply HR. cbn in Hj. lia.
Qed.

Lemma arm_ok_parts : forall joinpc nx sa, arm_ok joinpc nx sa = true ->
  s_pc sa = joinpc /\ s_log sa = [] /\ s_next sa = nx /\ APC.sr_vars_lt nx (s_regs sa) = true /\ length (s_regs sa) = 32%nat
  /\ nth 0 (s_regs sa) (ELit 0) = ELit 0.
Proof.
  intros joinpc nx sa H. unfold arm_ok in H.
  apply andb_true_iff in H as [H Hr0]. apply andb_true_iff in H as [H Hlen]. apply andb_true_iff in H as [H Hvars].
  apply andb_true_iff in H as [H Hnx]. apply andb_true_iff in H as [Hpc Hlog].
  apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hnx. apply Nat.eqb_eq in Hlen.
  destruct (s_log sa); [|discriminate].
  split; [exact Hpc|]. split; [reflexivity|]. split; [exact Hnx|]. split; [exact Hvars|]. split; [exact Hlen|].
  destruct (s_regs sa) as [|[z| | | | | | |] t]; try discriminate. destruct z; try discriminate. reflexivity.
Qed.

Lemma step_diamond_sound : forall (fx : FPState) jp ss w ss' w' E R M,
  closed ss w = true -> step_diamond jp ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx jp ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_diamond in H.
  destruct (APC.branch_probe IT (acs_of ss)) as [e|] eqn:Hbp; [|discriminate].
  destruct (erange (s_know ss) e) as [[lo hi]|] eqn:Her; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hok; [|discriminate] end.
  apply andb_true_iff in Hok as [Hok Hokb]. apply andb_true_iff in Hok as [Hve Hoka].
  set (sa := sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] (KRange e lo 0 :: s_know ss) (s_next ss))) in *.
  set (sb := sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] (KRange e 1 hi :: s_know ss) (s_next ss))) in *.
  destruct (join_regs 0 (s_regs sa) (s_regs sb) (s_next ss)) as [rj nx'] eqn:Hjoin. injection H as <- <-.
  destruct (arm_ok_parts _ _ _ Hoka) as (PCa & LOGa & NXa & Va & La & Z0a).
  destruct (arm_ok_parts _ _ _ Hokb) as (PCb & LOGb & NXb & Vb & Lb & Z0b).
  set (m := wden E M w) in *.
  pose proof (erange_sound segs E m (s_know ss) e lo hi HK Her) as Hrange.

  assert (ARM : exists (side : bool) (sx : sym_state), (sx = (if side then sa else sb))
            /\ know_ok segs E m ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss)).
  { destruct (Z_le_gt_dec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exists true, sa. split; [reflexivity|]. constructor; [cbn [kentry_ok]; lia | exact HK].
    - exists false, sb. split; [reflexivity|]. constructor; [cbn [kentry_ok]; lia | exact HK]. }
  destruct ARM as (side & sx & Hsx & HKx).
  assert (Fknx : AxSymRun3.kn_vars_lt (s_next ss) ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss) = true).
  { destruct side; cbn [AxSymRun3.kn_vars_lt AxSymRun3.kentry_vars_lt]; rewrite Hve, Fkn; reflexivity. }
  pose proof (@runTX_sound fx segs IT 0%nat BFUEL [jp] (s_pc ss) (s_regs ss) _ (s_next ss) E m (seg_rom segs) R IT_ok HR HKx Fsr Fknx) as X.
  cbn zeta in X.
  replace (sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss) (s_next ss)))
    with sx in X by (subst sx; destruct side; reflexivity).
  destruct X as (E1 & R1 & Hag1 & Hle1 & HR1 & Hlf1 & HK1 & Hms1 & _).
  assert (PCx : s_pc sx = jp) by (subst sx; destruct side; assumption).
  assert (LOGx : s_log sx = []) by (subst sx; destruct side; assumption).
  assert (NXx : s_next sx = s_next ss) by (subst sx; destruct side; assumption).
  rewrite LOGx in Hms1. cbn [mem_denot] in Hms1. rewrite PCx in Hms1.

  set (G := fun n : nat => getr R1 (Z_to_bv 5 (Z.of_nat n))).
  assert (HG : forall j, (j < length (s_regs sa))%nat -> G (0 + j)%nat = edenot E1 (nth j (if side then s_regs sa else s_regs sb) (ELit 0))).
  { intros j Hj. unfold G. cbn [Nat.add]. rewrite (HR1 (Z_to_bv 5 (Z.of_nat j))). unfold sr_get.
    rewrite La in Hj.
    destruct (Nat.eq_dec j 0) as [->|Hj0].
    - replace (bv_eqb (Z_to_bv 5 (Z.of_nat 0)) 0) with true by reflexivity. cbn [edenot].
      replace (nth 0 (if side then s_regs sa else s_regs sb) (ELit 0)) with (ELit 0) by (destruct side; symmetry; assumption). reflexivity.
    - replace (bv_eqb (Z_to_bv 5 (Z.of_nat j)) 0) with false.
      2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
          rewrite Z.mod_small by lia. change (bv_unsigned (0%bv : bv 5)) with 0%Z. lia. }
      rewrite ridx_of_nat by lia. subst sx. destruct side; reflexivity. }
  assert (Hv : forall j, (j < length (s_regs sa))%nat -> APC.expr_vars_lt (s_next ss) (nth j (s_regs sa) (ELit 0)) = true
                                                  /\ APC.expr_vars_lt (s_next ss) (nth j (s_regs sb) (ELit 0)) = true).
  { intros j Hj. rewrite La in Hj. split; (apply nth_sr_vars_lt; [assumption | lia]). }
  assert (Hlen : length (s_regs sb) = length (s_regs sa)) by (rewrite La, Lb; reflexivity).
  destruct (join_regs_sound (s_regs sa) (s_regs sb) 0 (s_next ss) rj nx' E1 G side Hjoin Hlen HG Hv) as (E' & Hag' & Hle' & Hlr & HRj).
  exists fx, E', R1.
  split; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag']|]. split; [cbn [s_next]; lia|].
  assert (Hw : wden E' M w = m) by (symmetry; eapply wden_agree; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag'] | exact Fw]).
  split.
  - split; cbn [s_regs s_know].
    + intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
      * unfold bv_eqb in Hr0. apply Z.eqb_eq in Hr0. replace r with (Z_to_bv 5 (Z.of_nat 0)) by (apply bv_eq; rewrite Hr0; reflexivity).
        pose proof (HG 0%nat ltac:(rewrite La; lia)) as X. unfold G in X. cbn [Nat.add] in X. rewrite X.
        replace (nth 0 (if side then s_regs sa else s_regs sb) (ELit 0)) with (ELit 0) by (destruct side; symmetry; assumption). reflexivity.
      * assert (Hr : (ridx r < 32)%nat) by (unfold ridx; pose proof (bv_unsigned_in_range _ r); change (bv_modulus 5) with 32%Z in *; lia).
        pose proof (HRj (ridx r) ltac:(rewrite La; exact Hr)) as X. unfold G in X. cbn [Nat.add] in X. rewrite ridx_bv5 in X. exact (X).
    + rewrite Hw. eapply APS.know_ok_agree'; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag'] | exact Fkn0 | exact HK].
  - cbn [s_pc]. rewrite Hw. exact Hms1.
Qed.

Definition step_req (st : sstep) : Prop := match st with SStrlen _ => strlen_step_stmt | _ => True end.
Definition no_strlen (steps : list sstep) : bool :=
  forallb (fun st => match st with SStrlen _ => false | _ => true end) steps.
Lemma no_strlen_req : forall steps, no_strlen steps = true -> Forall step_req steps.
Proof.
  intros steps H. unfold no_strlen in H. rewrite forallb_forall in H. apply Forall_forall. intros st Hin.
  specialize (H st Hin). destruct st; cbn; try exact I. discriminate.
Qed.

Lemma seg_step_sound : forall (fx : FPState) st ss w ss' w' E R M,
  step_req st ->
  seg_step st ss w = Some (ss', w') -> INV E ss w R M -> STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx st ss w ss' w' E R M Hreq H HI. unfold seg_step in H.
  destruct (closed ss w) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  destruct st as [stops| | |n|n|kz|p|jp|r].
  - eapply step_block_sound; eassumption.
  - eapply step_copy_sound; eassumption.
  - eapply step_fill_sound; eassumption.
  - eapply step_fsdseq_sound; eassumption.
  - eapply step_fldseq_sound; eassumption.
  - eapply Hreq; eassumption.
  - destruct (Z.eqb (s_pc ss) p); [|discriminate]. injection H as <- <-.
    exists fx, E, R. split; [apply APS.env_agree_refl|]. split; [lia|]. split; [exact HI | apply mst_refl].
  - eapply step_diamond_sound; eassumption.
  - eapply step_evalreg_sound; eassumption.
Qed.

Theorem seg_run_sound : forall (fx : FPState) steps ss w ss' w' E R M,
  Forall step_req steps ->
  seg_run steps ss w = Some (ss', w') -> INV E ss w R M ->
  exists (fx' : FPState) E' R', env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV E' ss' w' R' M
    /\ closed ss' w' = true
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) (wden E M w) (seg_rom segs))
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) (wden E' M w') (seg_rom segs)).
Proof.
  intros fx steps. revert fx. induction steps as [|st rest IH]; intros fx ss w ss' w' E R M Hreq H HI; cbn [seg_run] in H.
  - destruct (closed ss w) eqn:Hcl; [|discriminate]. injection H as <- <-.
    exists fx, E, R. split; [apply APS.env_agree_refl|]. split; [lia|]. split; [exact HI|]. split; [exact Hcl | apply mst_refl].
  - apply Forall_cons_iff in Hreq as [Hreq1 Hreqr].
    destruct (seg_step st ss w) as [[ss1 w1]|] eqn:Hs; [|discriminate].
    destruct (seg_step_sound fx st ss w ss1 w1 E R M Hreq1 Hs HI) as (fx1 & E1 & R1 & Hag1 & Hle1 & HI1 & Hms1).
    destruct (IH fx1 ss1 w1 ss' w' E1 R1 M Hreqr H HI1) as (fx2 & E2 & R2 & Hag2 & Hle2 & HI2 & Hcl2 & Hms2).
    exists fx2, E2, R2. split; [eapply APS.env_agree_trans; [exact Hag1 | eapply APS.env_agree_le; [exact Hag2 | exact Hle1]]|].
    split; [lia|]. split; [exact HI2|]. split; [exact Hcl2|].
    eapply msteps_trans; [exact Hms1 | exact Hms2].
Qed.

Corollary seg_run_entry : forall (fx : FPState) steps pc kn nx ss' w' R M,
  Forall step_req steps ->
  seg_run steps (SS pc sr_id [] kn nx) [] = Some (ss', w') ->
  know_ok segs (EnvR R) M kn ->
  exists (fx' : FPState) E' R', env_agree nx (EnvR R) E' /\ regs_ok E' (s_regs ss') R' /\ know_ok segs E' (wden E' M w') (s_know ss')
    /\ closed ss' w' = true
    /\ msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) (wden E' M w') (seg_rom segs)).
Proof.
  intros fx steps pc kn nx ss' w' R M Hreq H HK.
  destruct (seg_run_sound fx steps (SS pc sr_id [] kn nx) [] ss' w' (EnvR R) R M Hreq H) as (fx' & E' & R' & Hag & _ & [HR' HK'] & Hcl & Hms).
  - split; [apply EnvR_regs_ok | cbn [wden]; exact HK].
  - exists fx', E', R'. cbn [s_next s_pc wden] in *. split; [exact Hag|]. split; [exact HR'|]. split; [exact HK'|]. split; [exact Hcl | exact Hms].
Qed.

Definition region : Type := (expr * Z * Z)%type.
Definition within1 (b : expr) (k len : Z) (r : region) : bool :=
  let '(rb, rlo, rlen) := r in (expr_eqb b rb && Z.ltb 0 len && Z.leb rlo k && Z.leb (k + len) (rlo + rlen))%bool.
Definition went_within (F : list region) (g : went) : bool :=
  match g with
  | WSt (SA b k) wd _ => existsb (within1 b k (Z.of_nat wd)) F
  | WCopy db dk _ _ n => Z.leb 0 n && existsb (within1 db dk n) F
  | WFill db dk n _ => Z.leb 0 n && existsb (within1 db dk n) F
  end%bool.
Definition regions_flat (E : env) (F : list region) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in 0 <= estart E (SA rb rlo) /\ estart E (SA rb rlo) + rlen <= 2 ^ 64) F.
Definition outside (E : env) (F : list region) (a : word) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in
            bv_unsigned a < estart E (SA rb rlo) \/ estart E (SA rb rlo) + rlen <= bv_unsigned a) F.

Lemma within1_sound : forall E b k len rb rlo rlen (a : word),
  within1 b k len (rb, rlo, rlen) = true ->
  (bv_unsigned a < estart E (SA rb rlo) \/ estart E (SA rb rlo) + rlen <= bv_unsigned a) ->
  bv_unsigned a < estart E (SA b k) \/ estart E (SA b k) + len <= bv_unsigned a.
Proof.
  intros E b k len rb rlo rlen a H Ha. unfold within1 in H.
  apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H H1]. apply andb_true_iff in H as [Hb H0].
  apply expr_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. subst rb.
  unfold estart in *. cbn [a_base a_off] in *. lia.
Qed.

Lemma wden_frame : forall E M w F (a : word),
  forallb (went_within F) w = true -> regions_flat E F -> outside E F a ->
  wden E M w a = M a.
Proof.
  intros E M w F a Hw HF Ha. induction w as [|g r IH]; [reflexivity|].
  cbn [forallb] in Hw. apply andb_true_iff in Hw as [Hg Hr]. specialize (IH Hr).
  assert (REG : forall b k len, existsb (within1 b k len) F = true -> 0 <= len ->
            0 <= estart E (SA b k) /\ estart E (SA b k) + len <= 2 ^ 64 /\ 0 < len
            /\ (bv_unsigned a < estart E (SA b k) \/ estart E (SA b k) + len <= bv_unsigned a)).
  { intros b k len Hex Hlen. apply existsb_exists in Hex as ([[rb rlo] rlen] & Hin & Hw1).
    pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hfl. pose proof (proj1 (Forall_forall _ _) Ha _ Hin) as Hout.
    cbn beta iota in Hfl, Hout.
    pose proof (within1_sound E b k len rb rlo rlen a Hw1 Hout) as X.
    unfold within1 in Hw1. apply andb_true_iff in Hw1 as [Hw1 H2]. apply andb_true_iff in Hw1 as [Hw1 H1]. apply andb_true_iff in Hw1 as [Hb H0].
    apply expr_eqb_eq in Hb. apply Z.ltb_lt in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. subst rb.
    unfold estart in *. cbn [a_base a_off] in *. lia. }
  destruct g as [[b k] wd v|db dk sb sk n|db dk n c]; cbn [wden went_within] in *.
  - destruct (REG b k (Z.of_nat wd) Hg ltac:(lia)) as (R0 & R1 & RP & R2).
    rewrite wbytes_out; [exact IH | |]; rewrite length_N_to_le_bytes, APSX.adenot_SA, u64_of_Z by lia; lia.
  - apply andb_true_iff in Hg as [Hn Hg]. apply Z.leb_le in Hn.
    destruct (REG db dk n Hg Hn) as (R0 & R1 & RP & R2).
    destruct (rdn segs (wden E M r) (adenot E (SA sb sk)) (Z.to_nat n)) as [bs|] eqn:Hrd; [|exact IH].
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlbs.
    rewrite wbytes_out; [exact IH | |]; rewrite Hlbs, APSX.adenot_SA, Z2Nat.id, u64_of_Z by lia; lia.
  - apply andb_true_iff in Hg as [Hn Hg]. apply Z.leb_le in Hn.
    destruct (REG db dk n Hg Hn) as (R0 & R1 & RP & R2).
    rewrite wbytes_out; [exact IH | |]; rewrite repeat_length, APSX.adenot_SA, Z2Nat.id, u64_of_Z by lia; lia.
Qed.

Fixpoint kn_word (kn : list kentry) (b : expr) (k : Z) (w : nat) : option expr :=
  match kn with
  | [] => None
  | KWord (SA b' k') w' v :: r => if (expr_eqb b' b && Z.eqb k' k && Nat.eqb w' w)%bool then Some v else kn_word r b k w
  | _ :: r => kn_word r b k w
  end.
Lemma kn_word_sound : forall E M kn b k w v,
  know_ok segs E M kn -> kn_word kn b k w = Some v ->
  rdn segs M (adenot E (SA b k)) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros E M kn b k w v HK H. induction kn as [|K r IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hr]. cbn [kn_word] in H.
  destruct K as [[b' k'] w' v'| | | | | | | | |]; try exact (IH Hr H).
  destruct (expr_eqb b' b && Z.eqb k' k && Nat.eqb w' w)%bool eqn:Hc; [|exact (IH Hr H)].
  injection H as <-. apply andb_true_iff in Hc as [Hc Hw]. apply andb_true_iff in Hc as [Hb Hk].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. apply Nat.eqb_eq in Hw. subst b' k' w'.
  cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hrd). exact Hrd.
Qed.

Record post_spec : Type := PS {
  ps_pc : Z;
  ps_regs : list (nat * expr);
  ps_regions : list region;
  ps_cells : list kentry
}.

Definition region_flat_chk (kn : list kentry) (r : region) : bool :=
  let '(rb, rlo, rlen) := r in
  match rb with
  | ELit 0 => (Z.leb 0 rlo && Z.ltb 0 rlen && Z.ltb (rlo + rlen) two64)%bool
  | _ => (Z.ltb 0 rlen && existsb (fun K => match K with
                         | KWr (SA b lo) (ELit len) => (expr_eqb b rb && Z.leb lo rlo && Z.leb (rlo + rlen) (lo + len) && Z.ltb len two64 && Z.leb 0 len)%bool
                         | _ => false end) kn)%bool
  end.
Definition post_ok (ps : post_spec) (ss : sym_state) (w : list went) : bool :=
  (Z.eqb (s_pc ss) (ps_pc ps)
   && forallb (fun ie : nat * expr => expr_eqb (nth (fst ie) (s_regs ss) (ELit 0)) (snd ie)) (ps_regs ps)
   && forallb (went_within (ps_regions ps)) w
   && forallb (region_flat_chk (s_know ss)) (ps_regions ps)
   && forallb (fun K => existsb (APC.kentry_eqb K) (s_know ss)) (ps_cells ps))%bool.

Definition run_post_ok (steps : list sstep) (ss0 : sym_state) (ps : post_spec) : bool :=
  match seg_run steps ss0 [] with Some (ss, w) => post_ok ps ss w | None => false end.

Lemma kn_word_entry : forall E M kn b k w v,
  know_ok segs E M kn -> kn_word kn b k w = Some v -> kentry_ok segs E M (KWord (SA b k) w v).
Proof.
  intros E M kn b k w v HK H. induction kn as [|K r IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hr]. cbn [kn_word] in H.
  destruct K as [[b' k'] w' v'| | | | | | | | |]; try exact (IH Hr H).
  destruct (expr_eqb b' b && Z.eqb k' k && Nat.eqb w' w)%bool eqn:Hc; [|exact (IH Hr H)].
  injection H as <-. apply andb_true_iff in Hc as [Hc Hw]. apply andb_true_iff in Hc as [Hb Hk].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. apply Nat.eqb_eq in Hw. subst b' k' w'. exact HKK.
Qed.

Lemma region_flat_chk_sound : forall E M kn r,
  know_ok segs E M kn -> region_flat_chk kn r = true ->
  let '(rb, rlo, rlen) := r in 0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64.
Proof.
  intros E M kn [[rb rlo] rlen] HK H. unfold region_flat_chk in H.
  assert (GEN : (Z.ltb 0 rlen && existsb (fun K => match K with
                         | KWr (SA b lo) (ELit len) => (expr_eqb b rb && Z.leb lo rlo && Z.leb (rlo + rlen) (lo + len) && Z.ltb len two64 && Z.leb 0 len)%bool
                         | _ => false end) kn)%bool = true ->
                0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64).
  { intros G. apply andb_true_iff in G as [G0 G]. apply Z.ltb_lt in G0.
    apply existsb_exists in G as (K & Hin & HKc).
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
    destruct K as [| | | | | |[b lo] [len| | | | | | |]| | |]; try discriminate.
    apply andb_true_iff in HKc as [HKc H0]. apply andb_true_iff in HKc as [HKc Hlt].
    apply andb_true_iff in HKc as [HKc H2]. apply andb_true_iff in HKc as [Hb H1].
    apply expr_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0. subst b.
    cbn [kentry_ok] in HKK. destruct HKK as [Hfl _]. unfold flat, elenZ in Hfl. cbn [edenot] in Hfl.
    rewrite u64_of_Z in Hfl by (unfold two64 in Hlt; lia). unfold two64 in Hlt.
    unfold estart in *. cbn [a_base a_off] in *. pose proof (bv_unsigned_in_range _ (edenot E rb)). lia. }
  destruct rb as [z| | | | | | |]; try (apply GEN; exact H).
  destruct z; try (apply GEN; exact H).
  apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  unfold estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

Definition regions_ok (E : env) (F : list region) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in
            0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64) F.
Lemma regions_ok_flat : forall E F, regions_ok E F -> regions_flat E F.
Proof.
  intros E F H. unfold regions_ok, regions_flat in *. eapply Forall_impl; [|exact H].
  intros [[rb rlo] rlen] X. lia.
Qed.

Theorem run_post_sound : forall (fx : FPState) steps pc0 sr0 kn0 nx0 ps E R M,
  Forall step_req steps ->
  run_post_ok steps (SS pc0 sr0 [] kn0 nx0) ps = true ->
  regs_ok E sr0 R -> know_ok segs E M kn0 ->
  exists (fx' : FPState) E' R' M' ,
       env_agree nx0 E E'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (ps_pc ps)) M' (seg_rom segs))
    /\ (forall i e, In (i, e) (ps_regs ps) -> (0 < i < 32)%nat -> getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ regions_ok E' (ps_regions ps)
    /\ (forall a : word, outside E' (ps_regions ps) a -> M' a = M a)
    /\ know_ok segs E' M' (ps_cells ps)
    /\ mem_grows M M'.
Proof.
  intros fx steps pc0 sr0 kn0 nx0 ps E R M Hreq H HR HK. unfold run_post_ok in H.
  destruct (seg_run steps (SS pc0 sr0 [] kn0 nx0) []) as [[ss w]|] eqn:Hrun; [|discriminate].
  destruct (seg_run_sound fx steps (SS pc0 sr0 [] kn0 nx0) [] ss w E R M Hreq Hrun) as (fx' & E' & R' & Hag & _ & [HR' HK'] & Hcl & Hms).
  { split; [exact HR | cbn [wden]; exact HK]. }
  unfold post_ok in H. apply andb_true_iff in H as [H Hcells]. apply andb_true_iff in H as [H Hflat].
  apply andb_true_iff in H as [H Hw]. apply andb_true_iff in H as [Hpc Hregs].
  apply Z.eqb_eq in Hpc.
  exists fx', E', R', (wden E' M w). cbn [s_next s_pc wden] in *.
  assert (ROK : regions_ok E' (ps_regions ps)).
  { unfold regions_ok. apply Forall_forall. intros r Hin. rewrite forallb_forall in Hflat.
    exact (region_flat_chk_sound E' (wden E' M w) (s_know ss) r HK' (Hflat r Hin)). }
  split; [exact Hag|]. split; [rewrite <- Hpc; exact Hms|]. split; [|split; [|split; [exact ROK|split; [|split]]]].
  2:{ rewrite (HR' (Z_to_bv 5 0)). reflexivity. }
  - intros i e Hin Hi. rewrite forallb_forall in Hregs. specialize (Hregs (i, e) Hin). cbn [fst snd] in Hregs.
    apply expr_eqb_eq in Hregs. rewrite <- Hregs. rewrite (HR' (Z_to_bv 5 (Z.of_nat i))). unfold sr_get.
    replace (bv_eqb (Z_to_bv 5 (Z.of_nat i)) 0) with false.
    2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
        rewrite Z.mod_small by lia. change (bv_unsigned (0%bv : bv 5)) with 0%Z. lia. }
    rewrite ridx_of_nat by lia. reflexivity.
  - intros a Ha. eapply wden_frame; [exact Hw | apply regions_ok_flat; exact ROK | exact Ha].
  - unfold know_ok. apply Forall_forall. intros K Hin. rewrite forallb_forall in Hcells. specialize (Hcells K Hin).
    apply existsb_exists in Hcells as (K' & Hin' & Heq). apply APS.kentry_eqb_eq in Heq. subst K'.
    exact (proj1 (Forall_forall _ _) HK' K Hin').
  - clear. induction w as [|g r IH]; cbn [wden]; [apply mem_grows_refl|].
    destruct g as [a0 wd v|db dk sb sk n|db dk n c].
    + eapply mem_grows_trans; [exact IH | apply wbytes_grows].
    + destruct (rdn segs (wden E' M r) _ _); [eapply mem_grows_trans; [exact IH | apply wbytes_grows] | exact IH].
    + eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

End WithSegs.
End SR.
