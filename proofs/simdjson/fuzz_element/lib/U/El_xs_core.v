(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Exec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec CatSim AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_xs_stepG El_xs_soundG El_xs_full.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Section Mach.
Variable segs : list Segment.

Lemma write_to_mem_keeps : forall bs m a x, m x <> None -> write_to_mem m a bs x <> None.
Proof.
  induction bs as [|b rest IH]; intros m a x H; cbn [write_to_mem]; [exact H|].
  apply IH. destruct (bv_eqb x a); [discriminate| exact H].
Qed.
Definition ovl_mono (m m' : word -> option byte) : Prop := forall x, m x <> None -> m' x <> None.

Lemma interp_mem_inv : forall t m,
  mem_inv segs m ->
  match interp_eff_accesses segs t m with
  | MachineOk r => mem_inv segs (snd (access_value _ r)) /\ wmono segs m (snd (access_value _ r)) /\ ovl_mono m (snd (access_value _ r))
  | _ => True
  end.
Proof.
  induction t; intros m Hm; cbn [interp_eff_accesses access_value snd]; auto.
  - split; [exact Hm | split; [apply wmono_refl| intros x Hx; exact Hx]].
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| exact I].
    specialize (H (bv_extract 0 n (le_bytes_to_word bs)) m Hm).
    destruct (interp_eff_accesses segs (k _) m) as [r| |]; cbn in *; try exact H; exact I.
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hs; [| exact I].
    assert (Hm' : mem_inv segs (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    { apply mem_inv_store; [exact Hm|]. rewrite length_Z_to_le_bytes. exact Hs. }
    specialize (IHt _ Hm').
    destruct (interp_eff_accesses segs t _) as [r| |]; cbn in *; try exact I.
    destruct IHt as (H1 & H2 & H3). split; [exact H1|]. split.
    + eapply wmono_trans; [| exact H2]. apply wmono_write. apply wmono_refl.
    + intros x Hx. apply H3. apply write_to_mem_keeps. exact Hx.
Qed.

Lemma step_mem_inv : forall ms ms',
  RiscvSemantics.step segs ms = MachineOk ms' -> mem_inv segs (ms_mem ms) ->
  mem_inv segs (ms_mem ms') /\ wmono segs (ms_mem ms) (ms_mem ms') /\ ovl_mono (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' Hs Hm.
  assert (D : forall w, decode_exec_accesses segs ms w = MachineOk (mkAccessReport _ ms' (accessed_ranges _ (mkAccessReport _ ms' []))) \/
                    (exists rs, decode_exec_accesses segs ms w = MachineOk (mkAccessReport _ ms' rs)) ->
                    mem_inv segs (ms_mem ms') /\ wmono segs (ms_mem ms) (ms_mem ms') /\ ovl_mono (ms_mem ms) (ms_mem ms')).
  { intros w [Hd|[rs Hd]]; revert Hd; unfold decode_exec_accesses;
      (destruct (is_ecall w); [intros Hd; injection Hd as <-; cbn; split; [exact Hm| split; [apply wmono_refl| intros x Hx; exact Hx]] |]);
      (destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate]);
      destruct ms as [R F pc svc rv fc m ro]; cbn in Hm |- *;
      pose proof (interp_mem_inv (exec (Z_to_bv 64 isz) i (Core R F pc fc rv)) m Hm) as K;
      (destruct (interp_eff_accesses segs (exec _ i (Core R F pc fc rv)) m) as [[[c m1] rs1]| |]; try discriminate);
      intros Hd; injection Hd as <- _; cbn in *; exact K. }
  unfold RiscvSemantics.step, drop_access_report, RiscvSemantics.step_accesses, ms_pc in Hs.
  destruct (fetch_word segs (ms_pc_val ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [[x rs]| |] eqn:Hd; try discriminate. injection Hs as <-. apply (D w). right. exists rs. exact Hd. }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [[x rs]| |] eqn:Hd; try discriminate. injection Hs as <-. apply (D w). right. exists rs. exact Hd. }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [[x rs]| |] eqn:Hd; try discriminate. injection Hs as <-. apply (D w). right. exists rs. exact Hd. }
  unfold fetch_failure in Hs. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Lemma msteps_mem_inv : forall ms ms',
  Exec.msteps segs ms ms' -> mem_inv segs (ms_mem ms) ->
  mem_inv segs (ms_mem ms') /\ wmono segs (ms_mem ms) (ms_mem ms') /\ ovl_mono (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [_ Hs] _ IH]; intros Hm.
  - split; [exact Hm | split; [apply wmono_refl| intros x Hx; exact Hx]].
  - destruct (step_mem_inv _ _ Hs Hm) as (H1 & H2 & H2'). destruct (IH H1) as (H3 & H4 & H4').
    split; [exact H3|]. split; [eapply wmono_trans; eauto|]. intros x Hx. apply H4', H2', Hx.
Qed.

Lemma msteps_lib_of_as : forall ms ms', CatSim.msteps segs ms ms' -> Exec.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms| ms ms1 ms2 Hsvc Hstep _ IH].
  - apply Exec.msteps_refl.
  - eapply Exec.msteps_cons; [split; [exact Hsvc| exact Hstep]| exact IH].
Qed.
End Mach.

Section Core.
Variable segs : list Segment.
Variable t : itab.
Hypothesis Ht : itab_sound segs t.
Let rom := seg_rom segs.

Definition FPB : nat := 64.
Definition fp_ok (E : env) (F : bvmap 5 word) : Prop :=
  forall i : nat, (i < 32)%nat -> ev E (FPB + i)%nat = reg_get F (Z_to_bv 5 (Z.of_nat i)).

Definition wrange : Type := (expr * Z * Z)%type.
Fixpoint in_W (W : list wrange) (b : expr) (lo hi : Z) : bool :=
  match W with
  | [] => false
  | (wb, wlo, whi) :: W' => ((expr_eqb b wb && Z.leb wlo lo && Z.leb hi whi) || in_W W' b lo hi)%bool
  end.
Definition se_inW (W : list wrange) (e : sentry) : bool :=
  in_W W (a_base (e_addr e)) (a_off (e_addr e)) (a_off (e_addr e) + Z.of_nat (e_width e)).
Definition log_inW (W : list wrange) (log : list sentry) : bool := forallb (se_inW W) log.
Definition wf_W (W : list wrange) : bool := forallb (fun w => evars_lt FPB (fst (fst w))) W.
Definition Wd (E : env) (W : list wrange) (x : word) : Prop :=
  exists wb wlo whi, In (wb, wlo, whi) W /\ bv_unsigned (edenot E wb) + wlo <= bv_unsigned x < bv_unsigned (edenot E wb) + whi.

Definition CI (fc : bv 32) (E : env) (W RW : list wrange) (m0 base : word -> option byte) (ss : sym_state) (ms : machine_state) : Prop :=
  exists (R F : bvmap 5 word),
    ms = MS R F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom
    /\ regs_ok E (s_regs ss) R /\ log_flat E (s_log ss) /\ know_ok segs E base (s_know ss)
    /\ fullR R /\ fp_ok E F
    /\ mem_inv segs (ms_mem ms) /\ wmono segs m0 (ms_mem ms)
    /\ (forall x, ~ Wd E W x -> base x = m0 x)
    /\ log_inW W (s_log ss) = true
    /\ (forall x, Wd E RW x -> ms_mem ms x <> None /\ seg_rom segs x = None).

Definition CIX (fc : bv 32) (E : env) (W RW : list wrange) (m0 base : word -> option byte) (ss : sym_state) (ms : machine_state) : Prop :=
  (FPB + 32 <= s_next ss)%nat /\ forall E', eagree (s_next ss) E E' -> CI fc E' W RW m0 base ss ms.

Definition KCAP : nat := 4096.

Definition node_run (W : list wrange) (fuel : nat) (stops : list Z) (ss : sym_state) : option sym_state :=
  let ss1 := sym_execTX segs t KCAP fuel true stops ss in
  if log_inW W (s_log ss1) then Some ss1 else None.

Definition node_flush (ss : sym_state) : option sym_state :=
  match carry (s_log ss) (s_know ss) [] with
  | (kn', [], _) => Some (SSR (s_pc ss) (s_regs ss) [] kn' (s_next ss) None)
  | _ => None
  end.

Definition CLOB : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint havoc_regs (sr : list expr) (rs : list nat) (nx : nat) : list expr :=
  match rs with [] => sr | r :: rs' => havoc_regs (sr_upd sr r (EVar nx)) rs' (S nx) end.

Fixpoint kwr_find (kn : list kentry) (b : expr) (k n : Z) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) (ELit len) :: rest => ((expr_eqb b kb && Z.leb kk k && Z.leb (k + n) (kk + len) && Z.leb 0 len && Z.ltb len two64) || kwr_find rest b k n)%bool
  | _ :: rest => kwr_find rest b k n
  end.

Definition range_flat (fk : list kentry) (b : expr) (k n : Z) : bool :=
  match base_range fk b with
  | Some (lo, hi) => (Z.leb 0 (lo + k) && Z.leb 0 n && Z.leb (hi + k + n) two64)%bool
  | None => false
  end.

Definition kkeep (fk : list kentry) (b : expr) (k n : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ => ranges_apart_x fk kb kk (elen w) b k (ELit n)
  | KZero (SA kb kk) len => ranges_apart_x fk kb kk len b k (ELit n)
  | KFill (SA kb kk) len _ => ranges_apart_x fk kb kk len b k (ELit n)
  | KUnk (SA kb kk) len => ranges_apart_x fk kb kk len b k (ELit n)
  | KBlob (SA kb kk) len _ => ranges_apart_x fk kb kk len b k (ELit n)
  | KImg lo hi => (match base_range fk b with
                   | Some (blo, bhi) => (Z.leb hi (blo + k) || Z.leb (bhi + k + n) lo)%bool
                   | None => false
                   end || (Z.leb 0 lo && Z.ltb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_x fk (ELit 0) lo (ELit (hi - lo)) b k (ELit n)))%bool
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ | KWr _ _ => true
  end.
Definition retZ (ra : Z) : Z := ra - ra mod 2.

Definition call_gate (W RW : list wrange) (PC : Z) (ss : sym_state) : option (Z * expr * Z * Z) :=
  let regs := s_regs ss in let fk := facts_of (s_know ss) in
  match s_log ss, sr_get regs (Z_to_bv 5 1), sr_get regs (Z_to_bv 5 12) with
  | [], ELit ra, ELit n =>
      let '(db, dk) := split_lit (sr_get regs (Z_to_bv 5 10)) in
      if (Z.eqb (s_pc ss) PC && Z.leb 0 ra && Z.ltb ra two64 && Z.eqb (ra mod 4) 0 && Z.ltb 0 n && Z.leb n 4096
          && range_flat fk db dk n && kwr_find (s_know ss) db dk n && in_W W db dk (dk + n) && in_W RW db dk (dk + n))%bool
      then Some (ra, db, dk, n) else None
  | _, _, _ => None
  end.

Fixpoint kzeros8 (b : expr) (k : Z) (cnt : nat) : list kentry :=
  match cnt with O => [] | S c => KWord (SA b k) 8 (ELit 0) :: kzeros8 b (k + 8) c end.
Fixpoint kzeros1 (b : expr) (k : Z) (cnt : nat) : list kentry :=
  match cnt with O => [] | S c => KWord (SA b k) 1 (ELit 0) :: kzeros1 b (k + 1) c end.
Definition kzeros (b : expr) (k n : Z) : list kentry :=
  kzeros8 b k (Z.to_nat (n / 8)) ++ kzeros1 b (k + 8 * (n / 8)) (Z.to_nat (n mod 8)).

Definition node_set (W RW : list wrange) (PC : Z) (ss : sym_state) : option sym_state :=
  match call_gate W RW PC ss, sr_get (s_regs ss) (Z_to_bv 5 11) with
  | Some (ra, db, dk, n), ELit 0 =>
      let fk := facts_of (s_know ss) in
      Some (SSR (retZ ra) (havoc_regs (s_regs ss) CLOB (s_next ss)) []
               (kzeros db dk n ++ List.filter (kkeep fk db dk n) (s_know ss)) (s_next ss + 14)%nat None)
  | _, _ => None
  end.

Fixpoint read_words (ss : sym_state) (fk : list kentry) (sb : expr) (sk : Z) (cnt : nat) : option (list expr) :=
  match cnt with
  | O => Some []
  | S c => match sym_read segs ss fk scr_nil (SA sb sk) 8 false with
           | Some (v, [], _, nx) => if Nat.eqb nx (s_next ss) then
                                      match read_words ss fk sb (sk + 8) c with Some vs => Some (v :: vs) | None => None end
                                    else None
           | _ => None
           end
  end.
Fixpoint kwords8 (b : expr) (k : Z) (vs : list expr) : list kentry :=
  match vs with [] => [] | v :: vs' => KWord (SA b k) 8 v :: kwords8 b (k + 8) vs' end.

Definition node_cpy (W RW : list wrange) (PC : Z) (ss : sym_state) : option sym_state :=
  match call_gate W RW PC ss with
  | Some (ra, db, dk, n) =>
      let fk := facts_of (s_know ss) in
      let '(sb, sk) := split_lit (sr_get (s_regs ss) (Z_to_bv 5 11)) in
      if (Z.eqb (n mod 8) 0 && range_flat fk sb sk n && ranges_apart_x fk db dk (ELit n) sb sk (ELit n))%bool then
        match read_words ss fk sb sk (Z.to_nat (n / 8)) with
        | Some vs => Some (SSR (retZ ra) (havoc_regs (s_regs ss) CLOB (s_next ss)) []
                              (kwords8 db dk vs ++ List.filter (kkeep fk db dk n) (s_know ss)) (s_next ss + 14)%nat None)
        | None => None
        end
      else None
  | None => None
  end.

Fixpoint kfp (b : expr) (k : Z) (i cnt : nat) : list kentry :=
  match cnt with O => [] | S c => KWord (SA b k) 8 (EVar (FPB + i)%nat) :: kfp b (k + 8) (S i) c end.
Definition node_fsd (W RW : list wrange) (PC : Z) (ss : sym_state) : option sym_state :=
  let regs := s_regs ss in let fk := facts_of (s_know ss) in
  let '(db, dk) := split_lit (sr_get regs (Z_to_bv 5 10)) in
  match s_log ss with
  | [] => if (Z.eqb (s_pc ss) PC && range_flat fk db dk 512 && kwr_find (s_know ss) db (dk + 256) 256 && in_W W db (dk + 256) (dk + 512) && in_W RW db (dk + 256) (dk + 512))%bool
          then Some (SSR (PC + 128) regs [] (kfp db (dk + 256) 0 32 ++ List.filter (kkeep fk db (dk + 256) 256) (s_know ss)) (s_next ss) None)
          else None
  | _ => None
  end.

Fixpoint check_fp (ss : sym_state) (fk : list kentry) (b : expr) (k : Z) (i cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match sym_read segs ss fk scr_nil (SA b k) 8 false with
           | Some (EVar j, [], _, nx) => (Nat.eqb j (FPB + i) && Nat.eqb nx (s_next ss) && check_fp ss fk b (k + 8) (S i) c)%bool
           | _ => false
           end
  end.
Definition node_fld (PC : Z) (ss : sym_state) : option sym_state :=
  let regs := s_regs ss in let fk := facts_of (s_know ss) in
  let '(db, dk) := split_lit (sr_get regs (Z_to_bv 5 10)) in
  if (Z.eqb (s_pc ss) PC && range_flat fk db dk 512 && check_fp ss fk db (dk + 256) 0 32)%bool
  then Some (SSR (PC + 128) regs (s_log ss) (s_know ss) (s_next ss) (s_resv ss))
  else None.

Definition kin (b : expr) (lo hi : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ => (expr_eqb kb b && Z.leb lo kk && Z.leb (kk + Z.of_nat w) hi)%bool
  | KZero (SA kb kk) (ELit len) => (expr_eqb kb b && Z.leb lo kk && Z.leb (kk + len) hi)%bool
  | _ => false
  end.
Definition node_drop (b : expr) (lo hi : Z) (ss : sym_state) : option sym_state :=
  match s_log ss with
  | [] => Some (SSR (s_pc ss) (s_regs ss) [] (List.filter (fun K => negb (kin b lo hi K)) (s_know ss)) (s_next ss) None)
  | _ => None
  end.

Section Contracts.
Variables SETPC CPYPC FSDPC FLDPC : Z.

Definition set_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
  rw_cells segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv segs m ->
  evt segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' rom
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SETPC) fc None m rom).

Definition cpy_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte),
  bytes_at segs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  mem_inv segs m ->
  evt segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' rom
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at segs m' (bv_unsigned a1) src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CPYPC) fc None m rom).

Definition fle8 (F : bvmap 5 word) (i : nat) : list byte := word_to_le_bytes 8 (reg_get F (Z_to_bv 5 (Z.of_nat i))).

Definition fsd_contract : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
  fullR R ->
  rw_cells segs m (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 256) [CB 256 junk] ->
  (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 512 <= 2 ^ 64)%Z ->
  mem_inv segs m ->
  evt segs (fun ms' => exists m',
    ms' = MS R F (Z_to_bv 64 (FSDPC + 128)) fc None m' rom
    /\ munch [(bv_unsigned (reg_get R (Z_to_bv 5 10)) + 256, bv_unsigned (reg_get R (Z_to_bv 5 10)) + 512)]%Z m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ (forall i : nat, (i < 32)%nat -> rdn segs m' (Z_to_bv 64 (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 256 + 8 * Z.of_nat i)) 8 = Some (fle8 F i)))
    (MS R F (Z_to_bv 64 FSDPC) fc None m rom).

Definition fld_contract : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  fullR R ->
  (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 512 <= 2 ^ 64)%Z ->
  (forall i : nat, (i < 32)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 256 + 8 * Z.of_nat i)) 8 = Some (fle8 F i)) ->
  evt segs (fun ms' => exists F',
    ms' = MS R F' (Z_to_bv 64 (FLDPC + 128)) fc None m rom
    /\ (forall r : reg, reg_get F' r = reg_get F r))
    (MS R F (Z_to_bv 64 FLDPC) fc None m rom).

Inductive unode : Type :=
| URun (fuel : nat) (stops : list Z)
| UFlush
| USet
| UCpy
| UFsd
| UFld
| UDrop (b : expr) (lo hi : Z).

Definition xnode (W RW : list wrange) (n : unode) (ss : sym_state) : option sym_state :=
  match n with
  | URun fuel stops => node_run W fuel stops ss
  | UFlush => node_flush ss
  | USet => node_set W RW SETPC ss
  | UCpy => node_cpy W RW CPYPC ss
  | UFsd => node_fsd W RW FSDPC ss
  | UFld => node_fld FLDPC ss
  | UDrop b lo hi => node_drop b lo hi ss
  end.

Fixpoint xrun (W RW : list wrange) (plan : list unode) (ss : sym_state) : option sym_state :=
  match plan with
  | [] => Some ss
  | n :: k => match xnode W RW n ss with Some ss1 => xrun W RW k ss1 | None => None end
  end.

Fixpoint itab_of_ranges (rs : list (Z * nat)) (acc : itab) : itab :=
  match rs with
  | [] => acc
  | (lo, n) :: rs' => itab_of_ranges rs' (mk_itab_fuel segs n lo acc)
  end.
Lemma itab_of_ranges_sound : forall rs acc, itab_sound segs acc -> itab_sound segs (itab_of_ranges rs acc).
Proof. induction rs as [|[lo n] rs IH]; intros acc H; cbn; [exact H|]. apply IH. apply mk_itab_fuel_sound. exact H. Qed.

Definition obind (x : option sym_state) (f : sym_state -> option sym_state) : option sym_state :=
  match x with Some y => f y | None => None end.
Definition gc_sp (ss : sym_state) : option sym_state :=
  let '(b, k) := split_lit (sr_get (s_regs ss) (Z_to_bv 5 2)) in node_drop b (k - 1048576) k ss.
Definition STOPS (ENDPC : Z) : list Z := [SETPC; CPYPC; FSDPC; FLDPC; ENDPC].
Fixpoint xauto (W RW : list wrange) (ENDPC : Z) (fuel : nat) (k : nat) (ss : sym_state) : option sym_state :=
  match k with
  | O => None
  | S k' =>
      match node_run W fuel (STOPS ENDPC) ss with
      | None => None
      | Some ss1 =>
          let pc := s_pc ss1 in
          if Z.eqb pc ENDPC then node_flush ss1
          else if Z.eqb pc FLDPC then obind (node_fld FLDPC ss1) (xauto W RW ENDPC fuel k')
          else obind (obind (node_flush ss1) gc_sp) (fun ss3 =>
                 obind (if Z.eqb pc SETPC then node_set W RW SETPC ss3
                        else if Z.eqb pc CPYPC then node_cpy W RW CPYPC ss3
                        else if Z.eqb pc FSDPC then node_fsd W RW FSDPC ss3
                        else None) (xauto W RW ENDPC fuel k'))
      end
  end.

End Contracts.
End Core.
