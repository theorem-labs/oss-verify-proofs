(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Record region : Type := RG { r_s : expr; r_lo : Z; r_hi : Z }.

Record sentry : Type := SE { e_s : expr; e_k : Z; e_w : nat; e_v : expr }.

Record sym_state : Type := SS {
  s_pc   : expr;
  s_regs : list expr;
  s_log  : list sentry;
  s_next : nat;
  s_vb   : bounds;
  s_flat : list region;
  s_dj   : list (region * region);
  s_sok  : list region;
  s_rd   : list (expr * Z * nat * expr)
}.

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

Definition sr_get (sr : list expr) (r : reg) : expr :=
  if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0).

Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : expr) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_next ss) (s_vb ss) (s_flat ss) (s_dj ss) (s_sok ss) (s_rd ss).


Inductive sidecond : Type :=
| SCBr      (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat    (r : region)
| SCDisj    (r1 r2 : region)
| SCStoreOk (r : region)
| SCRead    (s : expr) (k : Z) (n : nat) (v : expr)
| SCJump    (e : expr).

Definition flat_ok (E : venv) (r : region) : Prop :=
  0 <= ed E (r_s r) + r_lo r /\ ed E (r_s r) + r_hi r <= 2 ^ 64.

Definition dj_ok (E : venv) (p : region * region) : Prop :=
  let (r1, r2) := p in
  ed E (r_s r1) + r_hi r1 <= ed E (r_s r2) + r_lo r2
  \/ ed E (r_s r2) + r_hi r2 <= ed E (r_s r1) + r_lo r1.

Definition br_ok (E : venv) (t : bool) (c : branch_cond) (a b : expr) : Prop :=
  match c, t with
  | BC_EQ, true | BC_NE, false => ed E a = ed E b
  | BC_EQ, false | BC_NE, true => ed E a <> ed E b
  | BC_LT, true | BC_LTU, true | BC_GE, false | BC_GEU, false => ed E a < ed E b
  | BC_LT, false | BC_LTU, false | BC_GE, true | BC_GEU, true => ed E b <= ed E a
  end.

Section WithSegs.
Variable segs : list Segment.

Definition sok_ok (base : word -> option byte) (E : venv) (r : region) : Prop :=
  flat_ok E r /\ r_lo r <= r_hi r /\
  RiscvSemantics.store_ok segs base (zw (ed E (r_s r) + r_lo r)) (Z.to_nat (r_hi r - r_lo r)) = true.

Definition sc_denot (base : word -> option byte) (E : venv) (sc : sidecond) : Prop :=
  match sc with
  | SCBr t c a b => br_ok E t c a b
  | SCFlat r => flat_ok E r
  | SCDisj r1 r2 => dj_ok E (r1, r2)
  | SCStoreOk r => sok_ok base E r
  | SCRead s k n v =>
      exists bs, rdn segs base (zw (ed E s + k)) n = Some bs /\ bytes_le_to_Z bs = ed E v
  | SCJump e => zw (Z.land (ed E e) (-2)) = zw (ed E e)
  end.

Definition scs_denot base E (l : list sidecond) : Prop := Forall (sc_denot base E) l.

Fixpoint find_hull (l : list region) (s : expr) : option region :=
  match l with
  | [] => None
  | r :: rest => if expr_eqb (r_s r) s then Some r else find_hull rest s
  end.

Fixpoint replace_hull (l : list region) (r : region) : list region :=
  match l with
  | [] => [r]
  | r' :: rest => if expr_eqb (r_s r') (r_s r) then r :: rest else r' :: replace_hull rest r
  end.

Definition in_region (r : region) (s : expr) (k : Z) (n : Z) : bool :=
  expr_eqb (r_s r) s && (r_lo r <=? k) && (k + n <=? r_hi r).



Definition regs_ok (E : venv) (sr : list expr) (regs : bvmap 5 word) : Prop :=
  forall r : reg, getr regs r = zw (ed E (sr_get sr r)).

Fixpoint mem_denot (E : venv) (base : word -> option byte) (log : list sentry)
  : word -> option byte :=
  match log with
  | [] => base
  | SE s k w v :: rest =>
      wbytes (mem_denot E base rest) (zw (ed E s + k)) (Z_to_le_bytes w (ed E v))
  end.

Definition entry_flat (E : venv) (e : sentry) : Prop :=
  0 <= ed E (e_s e) + e_k e /\ ed E (e_s e) + e_k e + Z.of_nat (e_w e) <= 2 ^ 64.

Definition hull_covers (fl : list region) (s : expr) (k n : Z) : Prop :=
  exists r, find_hull fl s = Some r /\ r_lo r <= k /\ k + n <= r_hi r.

Definition log_hulled (fl : list region) (log : list sentry) : Prop :=
  Forall (fun e => hull_covers fl (e_s e) (e_k e) (Z.of_nat (e_w e))) log.

Definition rd_ok (base : word -> option byte) (E : venv) (c : expr * Z * nat * expr) : Prop :=
  let '(s, k, n, v) := c in
  exists bs, rdn segs base (zw (ed E s + k)) n = Some bs /\ bytes_le_to_Z bs = ed E v.

Definition inv_ok (base : word -> option byte) (E : venv) (ss : sym_state) : Prop :=
  vars_ok E (s_vb ss)
  /\ Forall (flat_ok E) (s_flat ss)
  /\ Forall (dj_ok E) (s_dj ss)
  /\ Forall (sok_ok base E) (s_sok ss)
  /\ Forall (entry_flat E) (s_log ss)
  /\ log_hulled (s_flat ss) (s_log ss)
  /\ Forall (rd_ok base E) (s_rd ss).

Definition st_ok (E : venv) (base rom : word -> option byte)
                 (ss : sym_state) (ms : machine_state) : Prop :=
  exists regs, ms = mkst regs (zw (ed E (s_pc ss))) (mem_denot E base (s_log ss)) rom
          /\ regs_ok E (s_regs ss) regs
          /\ inv_ok base E ss.


Definition note_flat (fl : list region) (s : expr) (k n : Z)
  : list region * region * list sidecond :=
  match find_hull fl s with
  | Some r =>
      if (r_lo r <=? k) && (k + n <=? r_hi r) then (fl, r, [])
      else let r' := RG s (Z.min (r_lo r) k) (Z.max (r_hi r) (k + n)) in
           (replace_hull fl r', r', [SCFlat (RG s k (k + n))])
  | None => let r' := RG s k (k + n) in (r' :: fl, r', [SCFlat r'])
  end.

Fixpoint dj_known (l : list (region * region)) (a b : region) : bool :=
  match l with
  | [] => false
  | (x, y) :: rest =>
      (in_region x (r_s a) (r_lo a) (r_hi a - r_lo a) && in_region y (r_s b) (r_lo b) (r_hi b - r_lo b))
      || (in_region y (r_s a) (r_lo a) (r_hi a - r_lo a) && in_region x (r_s b) (r_lo b) (r_hi b - r_lo b))
      || dj_known rest a b
  end.

Fixpoint may_alias (ma : list (expr * expr)) (s s' : expr) : bool :=
  match ma with
  | [] => false
  | (x, y) :: rest => (expr_eqb x s && expr_eqb y s') || (expr_eqb x s' && expr_eqb y s)
                      || may_alias rest s s'
  end.

Inductive lk_res : Type :=
| LKStuck
| LKHit (delta : Z) (w : nat) (v : expr)
| LKBase.

Fixpoint lookup (ma : list (expr * expr)) (fl : list region)
                (log : list sentry) (s : expr) (k : Z) (n : Z) (ra : region)
                (dj : list (region * region)) (acc : list sidecond)
  : lk_res * list (region * region) * list sidecond :=
  match log with
  | [] => (LKBase, dj, acc)
  | SE s' k' w v :: rest =>
      if expr_eqb s s' then
        if (k' <=? k) && (k + n <=? k' + Z.of_nat w) then (LKHit (k - k') w v, dj, acc)
        else if (k + n <=? k') || (k' + Z.of_nat w <=? k) then lookup ma fl rest s k n ra dj acc
        else (LKStuck, dj, acc)
      else if may_alias ma s s' then (LKStuck, dj, acc)
      else
        match find_hull fl s' with
        | None => (LKStuck, dj, acc)
        | Some rb =>
            if dj_known dj ra rb then lookup ma fl rest s k n ra dj acc
            else lookup ma fl rest s k n ra ((ra, rb) :: dj) (SCDisj ra rb :: acc)
        end
  end.

Fixpoint sok_known (l : list region) (s : expr) (k n : Z) : bool :=
  match l with
  | [] => false
  | r :: rest => in_region r s k n || sok_known rest s k n
  end.

Fixpoint rd_known (l : list (expr * Z * nat * expr)) (s : expr) (k : Z) (n : nat) : option expr :=
  match l with
  | [] => None
  | (s', k', n', v) :: rest =>
      if expr_eqb s s' && Z.eqb k k' && Nat.eqb n n' then Some v else rd_known rest s k n
  end.


Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end%nat.

Record aview : Type := AV { av_part : expr; av_k0 : Z; av_w : nat; av_f : nat; av_idx : expr }.

Record cfg : Type := CFG {
  c_fb    : bounds;
  c_ma    : list (expr * expr);
  c_rets  : list expr;
  c_stops : list Z;
  c_av    : list aview
}.

Fixpoint av_lookup (l : list aview) (s : expr) (k : Z) (n : nat) : option expr :=
  match l with
  | [] => None
  | AV s' k0 w f idx :: rest =>
      if expr_eqb s s' && Nat.eqb n w && Z.eqb ((k - k0) mod Z.of_nat w) 0
      then Some (EApp1 f (mkAdd idx (ELit ((k - k0) / Z.of_nat w))))
      else av_lookup rest s k n
  end.

Definition pick_read (av : list aview) (s : expr) (k : Z) (n : nat) (next : nat)
           (rds : list (option expr)) : expr * bool * list (option expr) :=
  match av_lookup av s k n with
  | Some e => (e, false, rds)
  | None =>
      match rds with
      | Some e :: t => (e, false, t)
      | None :: t => (EVar next, true, t)
      | [] => (EVar next, true, [])
      end
  end.

Lemma pick_read_fresh : forall av s k n next rds rv rds',
  pick_read av s k n next rds = (rv, true, rds') -> rv = EVar next.
Proof.
  intros av s k n next rds rv rds' H. unfold pick_read in H.
  destruct (av_lookup av s k n); [congruence|].
  destruct rds as [|[e|] t]; congruence.
Qed.

Definition lit4 (p : expr) : expr := mkAdd p (ELit 4).

Section Step.
Variable C : cfg.

Definition zbits (sz : msize) : Z :=
  match sz with SZ1 => 8 | SZ2 => 16 | SZ4 => 32 | SZ8 => 64 end.

Definition load_result (vb : bounds) (sz : msize) (sgn : bool) (raw : expr) : expr :=
  match sz, sgn with
  | SZ1, true => mkSx vb (c_fb C) 8 raw
  | SZ2, true => mkSx vb (c_fb C) 16 raw
  | SZ4, true => mkSx vb (c_fb C) 32 raw
  | _, _ => raw
  end.

Definition step (i : instr) (ss : sym_state) (rds : list (option expr))
  : option (sym_state * list sidecond * list (option expr)) :=
  let vb := s_vb ss in
  let fb := c_fb C in
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  let p4 := lit4 p in
  match i with
  | OpImm op rd rs imm =>
      Some (sset ss rd (sem_alu vb fb op (g rs) (ELit (bv_signed imm))) p4, [], rds)
  | ShiftImm op rd rs sh =>
      Some (sset ss rd (sem_alu vb fb op (g rs) (ELit (bv_unsigned sh))) p4, [], rds)
  | Op op rd rs1 rs2 =>
      Some (sset ss rd (sem_alu vb fb op (g rs1) (g rs2)) p4, [], rds)
  | OpImm32 rd rs imm =>
      Some (sset ss rd (sem_aluw vb fb ALU_ADD (g rs) (ELit (bv_signed imm))) p4, [], rds)
  | ShiftImm32 op rd rs sh =>
      Some (sset ss rd (sem_aluw vb fb op (g rs) (ELit (bv_unsigned sh))) p4, [], rds)
  | Op32 op rd rs1 rs2 =>
      Some (sset ss rd (sem_aluw vb fb op (g rs1) (g rs2)) p4, [], rds)
  | Mul op rd rs1 rs2 =>
      Some (sset ss rd (sem_md vb fb op (g rs1) (g rs2)) p4, [], rds)
  | Mul32 op rd rs1 rs2 =>
      Some (sset ss rd (sem_mdw vb fb op (g rs1) (g rs2)) p4, [], rds)
  | Lui rd imm =>
      Some (sset ss rd (ELit (Z.shiftl (bv_signed imm) 12)) p4, [], rds)
  | Auipc rd imm =>
      match p with
      | ELit pz => Some (sset ss rd (ELit (Z.shiftl (bv_signed imm) 12 + pz)) p4, [], rds)
      | _ => None
      end
  | Jal rd imm =>
      Some (sset ss rd p4 (mkAdd p (ELit (bv_signed imm))), [], rds)
  | Jalr rd rs1 imm =>
      let t := mkAdd (g rs1) (ELit (bv_signed imm)) in
      match t with
      | ELit z => Some (sset ss rd p4 (ELit (Z.land z (-2))), [], rds)
      | _ => if existsb (expr_eqb t) (c_rets C)
             then Some (sset ss rd p4 t, [SCJump t], rds)
             else Some (sset ss rd p4 (mkAnd vb fb t (ELit (-2))), [], rds)
      end
  | Load sz sgn rd rs imm =>
      if (match sz, sgn with SZ8, false => true | _, _ => false end) then None else
      let n := msize_bytes sz in
      let '(s, k) := lin (mkAdd (g rs) (ELit (bv_signed imm))) in
      let '(fl1, ra, scf) := note_flat (s_flat ss) s k (Z.of_nat n) in
      match lookup (c_ma C) fl1 (s_log ss) s k (Z.of_nat n) ra (s_dj ss) [] with
      | (LKStuck, _, _) => None
      | (LKHit delta w v, dj1, scd) =>
          let raw := mkZx vb fb (zbits sz) (mkShr vb fb v (8 * delta)) in
          let res := load_result vb sz sgn raw in
          Some (SS p4 (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) res)
                   (s_log ss) (s_next ss) vb fl1 dj1 (s_sok ss) (s_rd ss),
                scf ++ scd, rds)
      | (LKBase, dj1, scd) =>
          match rd_known (s_rd ss) s k n with
          | Some rv =>
              let raw := mkZx vb fb (zbits sz) rv in
              let res := load_result vb sz sgn raw in
              Some (SS p4 (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) res)
                       (s_log ss) (s_next ss) vb fl1 dj1 (s_sok ss) (s_rd ss),
                    scf ++ scd, rds)
          | None =>
          let '(rv, fresh, rds') := pick_read (c_av C) s k n (s_next ss) rds in
          let vb1 := if fresh then (s_next ss, 2 ^ zbits sz) :: vb else vb in
          let raw := mkZx vb1 fb (zbits sz) rv in
          let res := load_result vb1 sz sgn raw in
          Some (SS p4 (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) res)
                   (s_log ss) (if fresh then S (s_next ss) else s_next ss) vb1 fl1 dj1 (s_sok ss)
                   ((s, k, n, rv) :: s_rd ss),
                scf ++ SCRead s k n rv :: scd, rds')
          end
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let '(s, k) := lin (mkAdd (g rs1) (ELit (bv_signed imm))) in
      let '(fl1, ra, scf) := note_flat (s_flat ss) s k (Z.of_nat n) in
      let '(sok1, scs) :=
        if sok_known (s_sok ss) s k (Z.of_nat n) then (s_sok ss, [])
        else (RG s k (k + Z.of_nat n) :: s_sok ss, [SCStoreOk (RG s k (k + Z.of_nat n))]) in
      Some (SS p4 (s_regs ss) (SE s k n (g rs2) :: s_log ss) (s_next ss) vb fl1 (s_dj ss) sok1 (s_rd ss),
            scf ++ scs, rds)
  | _ => None
  end.


Fixpoint run (fuel : nat) (first : bool) (dirs : list bool) (rds : list (option expr))
             (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond :=
  match fuel with
  | O => (ss, acc)
  | S f =>
      match s_pc ss with
      | ELit pz =>
          if negb first && existsb (Z.eqb pz) (c_stops C) then (ss, acc) else
          match fetch_word segs (Z_to_bv 64 pz) with
          | None => (ss, acc)
          | Some w =>
              if is_ecall w then (ss, acc) else
              match decode_any w with
              | None => (ss, acc)
              | Some (i, sz) =>
                  if negb (Z.eqb sz 4) then (ss, acc) else
                  match i with
                  | Branch c rs1 rs2 imm =>
                      match dirs with
                      | [] => (ss, acc)
                      | t :: dirs' =>
                          let a := sr_get (s_regs ss) rs1 in
                          let b := sr_get (s_regs ss) rs2 in
                          let '(a', b') :=
                            match c with
                            | BC_LT | BC_GE => (mkSx (s_vb ss) (c_fb C) 64 a, mkSx (s_vb ss) (c_fb C) 64 b)
                            | _ => (mkZx (s_vb ss) (c_fb C) 64 a, mkZx (s_vb ss) (c_fb C) 64 b)
                            end in
                          run f false dirs' rds
                            (SS (ELit (if t then pz + bv_signed imm else pz + 4))
                                (s_regs ss) (s_log ss) (s_next ss) (s_vb ss)
                                (s_flat ss) (s_dj ss) (s_sok ss) (s_rd ss))
                            (SCBr t c a' b' :: acc)
                      end
                  | _ =>
                      match step i ss rds with
                      | Some (ss', scs, rds') => run f false dirs rds' ss' (scs ++ acc)
                      | None => (ss, acc)
                      end
                  end
              end
          end
      | _ => (ss, acc)
      end
  end.

End Step.
End WithSegs.



Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof.
  intros r r' H. apply bv_eq. unfold ridx in H.
  pose proof (u5_range r). pose proof (u5_range r'). lia.
Qed.

Lemma nth_sr_upd : forall n sr e i,
  nth i (sr_upd sr n e) (ELit 0) = if Nat.eqb i n then e else nth i sr (ELit 0).
Proof.
  induction n as [|n IH]; intros sr e i.
  - destruct sr; destruct i; cbn; try reflexivity; destruct i; reflexivity.
  - destruct sr as [|h t]; destruct i as [|i]; cbn; try reflexivity.
    + rewrite IH. destruct (Nat.eqb i n); [reflexivity|]. destruct i; reflexivity.
    + apply IH.
Qed.

Lemma regs_ok_upd : forall E sr regs rd v e,
  regs_ok E sr regs -> zw (ed E e) = v ->
  regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
            (if bv_eqb rd 0 then regs else regupd regs rd v).
Proof.
  intros E sr regs rd v e Hr Hv.
  destruct (bv_eqb rd 0) eqn:Hrd; [exact Hr|].
  assert (Hne : rd <> 0%bv).
  { intro Hc. subst rd. rewrite bv_eqb_refl in Hrd. discriminate. }
  intro r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r.
      rewrite getr_same by exact Hne. exact (eq_sym Hv).
    + assert (Hrr : r <> rd).
      { intro Hc. subst r. rewrite Nat.eqb_refl in Hi. discriminate. }
      rewrite getr_other by exact Hrr.
      specialize (Hr r). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

Lemma regs_ok_pin : forall E sr regs (r : reg) e,
  regs_ok E sr regs -> getr regs r = zw (ed E e) ->
  regs_ok E (sr_upd sr (ridx r) e) regs.
Proof.
  intros E sr regs r e Hr Hv r'. unfold sr_get. destruct (bv_eqb r' 0) eqn:Hr0.
  - assert (r' = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r'. unfold getr. rewrite Hr0. reflexivity.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
    + specialize (Hr r'). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

Definition sr_id : list expr := map EVar (seq 0 32).
Definition vb_id : bounds := map (fun n => (n, 2 ^ 64)) (seq 0 32).

Definition mkE (regs : bvmap 5 word) (vals : list Z) (F1 : nat -> Z -> Z) (F2 : nat -> Z -> Z -> Z)
  : venv :=
  VEnv (fun n => if Nat.ltb n 32 then bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n)))
                 else nth (n - 32) vals 0) F1 F2.

Lemma ridx_range : forall r : reg, (ridx r < 32)%nat.
Proof. intro r. unfold ridx. pose proof (u5_range r). lia. Qed.

Lemma ridx_roundtrip : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
  intro r. apply bv_eq. unfold ridx. rewrite Z_to_bv_unsigned.
  pose proof (u5_range r). rewrite Z2Nat.id by lia. apply bv_wrap_small.
  change (bv_modulus 5) with 32. lia.
Qed.


Lemma nth_sr_id : forall n, (n < 32)%nat -> nth n sr_id (ELit 0) = EVar n.
Proof.
  intros n Hn. unfold sr_id.
  do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.


Lemma blookup_vb_id : forall n b, blookup vb_id n = Some b -> b = 2 ^ 64 /\ (n < 32)%nat.
Proof.
  intros n b H.
  do 32 (destruct n as [|n]; [cbn in H; split; [congruence|lia] |]).
  cbn in H. discriminate.
Qed.


Section Sound.
Variable segs : list Segment.


Lemma length_Z_to_le_bytes' : forall n z, length (Z_to_le_bytes n z) = n.
Proof. apply length_Z_to_le_bytes. Qed.

Lemma bytes_le_to_Z_of_Z : forall n z,
  bytes_le_to_Z (Z_to_le_bytes n z) = z mod 2 ^ (8 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intro z.
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - cbn [Z_to_le_bytes bytes_le_to_Z]. rewrite IH, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by lia.
    apply Z.bits_inj'. intros i Hi.
    rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (testbit_mod_pow2 z 8 i) by lia.
    rewrite (testbit_mod_pow2 z (8 * Z.of_nat n + 8) i) by lia.
    destruct (Z.ltb_spec i 8).
    + rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
      replace (i <? 8 * Z.of_nat n + 8) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite orb_false_r. reflexivity.
    + rewrite (testbit_mod_pow2 (Z.shiftr z 8) (8 * Z.of_nat n) (i - 8)) by lia.
      rewrite Z.shiftr_spec by lia. replace (i - 8 + 8) with i by lia. cbn [orb].
      destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat n)); destruct (Z.ltb_spec i (8 * Z.of_nat n + 8));
        try reflexivity; lia.
Qed.

Lemma skipn_Z_to_le_bytes : forall d w z, (d <= w)%nat ->
  skipn d (Z_to_le_bytes w z) = Z_to_le_bytes (w - d) (z / 2 ^ (8 * Z.of_nat d)).
Proof.
  induction d as [|d IH]; intros w z Hd.
  - cbn [skipn]. rewrite Nat.sub_0_r. replace (8 * Z.of_nat 0) with 0 by lia.
    rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
  - destruct w as [|w]; [lia|]. cbn [Z_to_le_bytes skipn Nat.sub].
    rewrite IH by lia. f_equal. rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia. f_equal. f_equal. lia.
Qed.

Lemma firstn_Z_to_le_bytes : forall n w z, (n <= w)%nat ->
  firstn n (Z_to_le_bytes w z) = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intros w z Hn; [reflexivity|].
  destruct w as [|w]; [lia|]. cbn [Z_to_le_bytes firstn]. f_equal. apply IH. lia.
Qed.

Lemma Z_to_le_bytes_mod64 : forall (n : nat) z, (n <= 8)%nat ->
  Z_to_le_bytes n (z mod 2 ^ 64) = Z_to_le_bytes n z.
Proof.
  intros n z Hn.
  rewrite <- (Z_to_le_bytes_mod n (z mod 2 ^ 64)), <- (Z_to_le_bytes_mod n z).
  f_equal. apply mod_mod_le. lia.
Qed.

Lemma word_to_le_bytes_zw : forall (n : nat) z, (n <= 8)%nat ->
  word_to_le_bytes n (zw z) = Z_to_le_bytes n z.
Proof.
  intros n z Hn. unfold word_to_le_bytes. rewrite u_zw. apply Z_to_le_bytes_mod64. exact Hn.
Qed.

Lemma subread_value : forall n d w z, (d + n <= w)%nat ->
  bytes_le_to_Z (firstn n (skipn d (Z_to_le_bytes w z)))
  = (z / 2 ^ (8 * Z.of_nat d)) mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n d w z H.
  rewrite skipn_Z_to_le_bytes, firstn_Z_to_le_bytes, bytes_le_to_Z_of_Z by lia.
  reflexivity.
Qed.


Lemma mem_denot_grows : forall E base log, mem_grows base (mem_denot E base log).
Proof.
  intros E base log. induction log as [|[s k w v] rest IH]; cbn [mem_denot].
  - apply mem_grows_refl.
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

Lemma rdn_sub : forall k n (a : word) mem bs m,
  rdn segs mem a n = Some bs -> (k + m <= n)%nat ->
  rdn segs mem (a + nat_to_word k)%bv m = Some (firstn m (skipn k bs)).
Proof.
  induction k as [|k IH]; intros n a mem bs m H Hk.
  - rewrite word_add_0. cbn [skipn]. apply (rdn_firstn segs mem n a bs m H). lia.
  - destruct n as [|n]; [lia|]. cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a + 1)%bv n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-. cbn [skipn].
    replace (a + nat_to_word (S k))%bv with (a + 1 + nat_to_word k)%bv
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    apply (IH n (a + 1)%bv mem rest m Er). lia.
Qed.

Lemma zw_add_nat : forall a (d : nat),
  zw (a + Z.of_nat d) = (zw a + nat_to_word d)%bv.
Proof.
  intros a d. unfold zw, nat_to_word. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma rdn_wbytes_sub : forall m a w z (d n : nat),
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> (d + n <= w)%nat ->
  rdn segs (wbytes m (zw a) (Z_to_le_bytes w z)) (zw (a + Z.of_nat d)) n
  = Some (firstn n (skipn d (Z_to_le_bytes w z))).
Proof.
  intros m a w z d n Ha Hw Hdn.
  destruct w as [|w'].
  { assert (d = 0%nat) by lia. assert (n = 0%nat) by lia. subst. reflexivity. }
  rewrite zw_add_nat.
  eapply rdn_sub; [|exact Hdn].
  pose proof (rdn_wbytes_hit segs (Z_to_le_bytes (S w') z) m (zw a)) as H.
  rewrite length_Z_to_le_bytes' in H. apply H. rewrite u_zw_small by lia. lia.
Qed.


Lemma find_hull_s : forall fl s r, find_hull fl s = Some r -> r_s r = s.
Proof.
  induction fl as [|r' rest IH]; intros s r H; cbn in H; [discriminate|].
  destruct (expr_eqb (r_s r') s) eqn:He.
  - injection H as <-. apply expr_eqb_eq. exact He.
  - exact (IH _ _ H).
Qed.

Lemma find_hull_In : forall fl s r, find_hull fl s = Some r -> In r fl.
Proof.
  induction fl as [|r' rest IH]; intros s r H; cbn in H; [discriminate|].
  destruct (expr_eqb (r_s r') s); [injection H as <-; left; reflexivity | right; exact (IH _ _ H)].
Qed.

Lemma expr_eqb_refl : forall e, expr_eqb e e = true.
Proof.
  assert (A : forall o, aluop_eqb o o = true) by (intros []; reflexivity).
  assert (M : forall o, mulop_eqb o o = true) by (intros []; reflexivity).
  induction e; cbn [expr_eqb]; rewrite ?Z.eqb_refl, ?Nat.eqb_refl, ?A, ?M;
    rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; reflexivity.
Qed.

Lemma find_replace_same : forall fl r, find_hull (replace_hull fl r) (r_s r) = Some r.
Proof.
  induction fl as [|r' rest IH]; intro r; cbn.
  - rewrite expr_eqb_refl. reflexivity.
  - destruct (expr_eqb (r_s r') (r_s r)) eqn:He; cbn.
    + rewrite expr_eqb_refl. reflexivity.
    + rewrite He. apply IH.
Qed.

Lemma find_replace_other : forall fl r s,
  expr_eqb (r_s r) s = false -> find_hull (replace_hull fl r) s = find_hull fl s.
Proof.
  induction fl as [|r' rest IH]; intros r s He; cbn.
  - rewrite He. reflexivity.
  - destruct (expr_eqb (r_s r') (r_s r)) eqn:He'; cbn.
    + rewrite He. apply expr_eqb_eq in He'. rewrite He'. rewrite He. reflexivity.
    + destruct (expr_eqb (r_s r') s); [reflexivity | apply IH; exact He].
Qed.

Lemma Forall_replace : forall (P : region -> Prop) fl r,
  Forall P fl -> P r -> Forall P (replace_hull fl r).
Proof.
  induction fl as [|r' rest IH]; intros r Hfl Hr; cbn.
  - constructor; [exact Hr | constructor].
  - inversion Hfl; subst. destruct (expr_eqb (r_s r') (r_s r)).
    + constructor; assumption.
    + constructor; [assumption | apply IH; assumption].
Qed.

Lemma note_flat_sound : forall base E fl s k n fl1 ra scf,
  note_flat fl s k n = (fl1, ra, scf) ->
  0 <= n ->
  Forall (flat_ok E) fl ->
  scs_denot segs base E scf ->
  Forall (flat_ok E) fl1
  /\ find_hull fl1 s = Some ra /\ r_s ra = s /\ r_lo ra <= k /\ k + n <= r_hi ra
  /\ flat_ok E ra
  /\ (forall s' k' n', hull_covers fl s' k' n' -> hull_covers fl1 s' k' n').
Proof.
  intros base E fl s k n fl1 ra scf Hnf Hn Hfl Hsc. unfold note_flat in Hnf.
  destruct (find_hull fl s) as [r|] eqn:Hf.
  - pose proof (find_hull_s _ _ _ Hf) as Hrs.
    assert (Hr : flat_ok E r).
    { apply find_hull_In in Hf. rewrite Forall_forall in Hfl. exact (Hfl _ Hf). }
    destruct ((r_lo r <=? k) && (k + n <=? r_hi r)) eqn:Hin.
    + injection Hnf as <- <- <-. apply andb_prop in Hin as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2.
      split; [exact Hfl|]. split; [exact Hf|]. split; [exact Hrs|]. split; [exact H1|].
      split; [exact H2|]. split; [exact Hr|]. intros s' k' n' Hc; exact Hc.
    + injection Hnf as <- <- <-.
      pose proof (Forall_inv Hsc) as Hx. cbn [sc_denot] in Hx. unfold flat_ok in Hx. cbn [r_s r_lo r_hi] in Hx.
      unfold flat_ok in Hr. rewrite Hrs in Hr.
      assert (Hr' : flat_ok E (RG s (Z.min (r_lo r) k) (Z.max (r_hi r) (k + n)))).
      { unfold flat_ok; cbn [r_s r_lo r_hi]. lia. }
      split; [apply Forall_replace; [exact Hfl | exact Hr']|].
      split; [exact (find_replace_same fl (RG s _ _))|].
      split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [exact Hr'|].
      intros s' k' n' (r0 & Hf0 & Hlo & Hhi).
      destruct (expr_eqb s s') eqn:Hss.
      * apply expr_eqb_eq in Hss. subst s'. rewrite Hf in Hf0. injection Hf0 as <-.
        exists (RG s (Z.min (r_lo r) k) (Z.max (r_hi r) (k + n))).
        split; [exact (find_replace_same fl (RG s _ _)) | cbn; lia].
      * exists r0. split; [|lia].
        rewrite (find_replace_other fl (RG s _ _) s') by exact Hss. exact Hf0.
  - injection Hnf as <- <- <-.
    pose proof (Forall_inv Hsc) as Hx. cbn [sc_denot] in Hx.
    split; [constructor; [exact Hx | exact Hfl]|].
    split; [cbn; rewrite expr_eqb_refl; reflexivity|].
    split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|]. split; [exact Hx|].
    intros s' k' n' (r0 & Hf0 & Hlo & Hhi). exists r0. split; [|lia].
    cbn. destruct (expr_eqb s s') eqn:Hss; [|exact Hf0].
    apply expr_eqb_eq in Hss. subst. rewrite Hf in Hf0. discriminate.
Qed.


Lemma in_region_sound : forall r s k n,
  in_region r s k n = true -> r_s r = s /\ r_lo r <= k /\ k + n <= r_hi r.
Proof.
  intros r s k n H. unfold in_region in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma dj_known_sound : forall E dj a b,
  Forall (dj_ok E) dj -> dj_known dj a b = true -> r_lo a <= r_hi a -> r_lo b <= r_hi b ->
  dj_ok E (a, b).
Proof.
  intros E dj a b Hdj. induction dj as [|[x y] rest IH]; intros H Ha Hb; cbn [dj_known] in H.
  - discriminate.
  - inversion Hdj as [|p l Hxy Hrest]; subst.
    apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
    + apply andb_prop in H as [H1 H2].
      apply in_region_sound in H1 as (S1 & L1 & U1). apply in_region_sound in H2 as (S2 & L2 & U2).
      unfold dj_ok in Hxy |- *. rewrite <- S1, <- S2. lia.
    + apply andb_prop in H as [H1 H2].
      apply in_region_sound in H1 as (S1 & L1 & U1). apply in_region_sound in H2 as (S2 & L2 & U2).
      unfold dj_ok in Hxy |- *. rewrite <- S1, <- S2. lia.
    + exact (IH Hrest H Ha Hb).
Qed.

Lemma rdn_wbytes_skip : forall m (a a' : Z) (bs : list byte) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  0 <= a' -> a' + Z.of_nat (length bs) <= 2 ^ 64 ->
  (a + Z.of_nat n <= a' \/ a' + Z.of_nat (length bs) <= a) ->
  rdn segs (wbytes m (zw a') bs) (zw a) n = rdn segs m (zw a) n.
Proof.
  intros m a a' bs n Ha Han Ha' Hbs Hd.
  destruct n as [|n']; [reflexivity|].
  destruct bs as [|b bs']; [reflexivity|].
  cbn [length] in Hbs, Hd.
  apply rdn_wbytes_out; rewrite ?u_zw_small; cbn [length]; lia.
Qed.

Lemma lookup_acc : forall ma fl log s k n ra dj acc res dj1 acc1,
  lookup ma fl log s k n ra dj acc = (res, dj1, acc1) ->
  exists pre, acc1 = pre ++ acc.
Proof.
  intros ma fl log. induction log as [|[s' k' w v] rest IH]; intros s k n ra dj acc res dj1 acc1 Hl.
  { cbn in Hl. injection Hl as <- <- <-. exists []. reflexivity. }
  cbn [lookup] in Hl.
  destruct (expr_eqb s s').
  - destruct ((k' <=? k) && (k + n <=? k' + Z.of_nat w)).
    + injection Hl as <- <- <-. exists []. reflexivity.
    + destruct ((k + n <=? k') || (k' + Z.of_nat w <=? k)).
      * exact (IH _ _ _ _ _ _ _ _ _ Hl).
      * injection Hl as <- <- <-. exists []. reflexivity.
  - destruct (may_alias ma s s'). { injection Hl as <- <- <-. exists []. reflexivity. }
    destruct (find_hull fl s') as [rb|]. 2: { injection Hl as <- <- <-. exists []. reflexivity. }
    destruct (dj_known dj ra rb).
    + exact (IH _ _ _ _ _ _ _ _ _ Hl).
    + destruct (IH _ _ _ _ _ _ _ _ _ Hl) as [pre Hpre]. exists (pre ++ [SCDisj ra rb]).
      rewrite <- app_assoc. exact Hpre.
Qed.

Lemma scs_denot_app : forall base E l1 l2,
  scs_denot segs base E (l1 ++ l2) <-> scs_denot segs base E l1 /\ scs_denot segs base E l2.
Proof. intros. unfold scs_denot. apply Forall_app. Qed.

Lemma lookup_sound : forall base E ma fl log s k (n : nat) ra dj acc res dj1 acc1,
  lookup ma fl log s k (Z.of_nat n) ra dj acc = (res, dj1, acc1) ->
  scs_denot segs base E acc1 ->
  Forall (dj_ok E) dj ->
  Forall (flat_ok E) fl ->
  log_hulled fl log ->
  Forall (entry_flat E) log ->
  r_s ra = s -> r_lo ra <= k -> k + Z.of_nat n <= r_hi ra -> flat_ok E ra ->
  Forall (dj_ok E) dj1 /\ scs_denot segs base E acc /\
  match res with
  | LKBase => rdn segs (mem_denot E base log) (zw (ed E s + k)) n
              = rdn segs base (zw (ed E s + k)) n
  | LKHit delta w v =>
      0 <= delta /\ delta + Z.of_nat n <= Z.of_nat w /\
      rdn segs (mem_denot E base log) (zw (ed E s + k)) n
      = Some (firstn n (skipn (Z.to_nat delta) (Z_to_le_bytes w (ed E v))))
  | LKStuck => True
  end.
Proof.
  intros base E ma fl log. induction log as [|[s' k' w v] rest IH];
    intros s k n ra dj acc res dj1 acc1 Hl Hsc Hdj Hfl Hhl Hef Hras Hlo Hhi Hra.
  { cbn in Hl. injection Hl as <- <- <-. split; [exact Hdj|]. split; [exact Hsc|]. reflexivity. }
  pose proof (Forall_inv Hef) as He1. pose proof (Forall_inv_tail Hef) as Hef'.
  pose proof (Forall_inv Hhl) as Hh1. pose proof (Forall_inv_tail Hhl) as Hhl'.
  unfold entry_flat in He1. cbn [e_s e_k e_w] in He1, Hh1.
  assert (Hacc : 0 <= ed E s + k /\ ed E s + k + Z.of_nat n <= 2 ^ 64).
  { unfold flat_ok in Hra. rewrite Hras in Hra. lia. }
  cbn [lookup mem_denot] in Hl |- *.
  destruct (expr_eqb s s') eqn:Hss.
  - pose proof (ed_eqb E _ _ Hss) as Hed.
    destruct ((k' <=? k) && (k + Z.of_nat n <=? k' + Z.of_nat w)) eqn:Hhit.
    + injection Hl as <- <- <-. apply andb_prop in Hhit as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2.
      split; [exact Hdj|]. split; [exact Hsc|]. split; [lia|]. split; [lia|].
      rewrite Hed.
      replace (ed E s' + k) with (ed E s' + k' + Z.of_nat (Z.to_nat (k - k'))) by lia.
      apply rdn_wbytes_sub; lia.
    + destruct ((k + Z.of_nat n <=? k') || (k' + Z.of_nat w <=? k)) eqn:Hdis; [|].
      * assert (Hd : ed E s + k + Z.of_nat n <= ed E s' + k' \/ ed E s' + k' + Z.of_nat w <= ed E s + k).
        { apply orb_prop in Hdis as [Hdis|Hdis]; apply Z.leb_le in Hdis; rewrite Hed; lia. }
        specialize (IH s k n ra dj acc res dj1 acc1 Hl Hsc Hdj Hfl Hhl' Hef' Hras Hlo Hhi Hra)
          as (IH1 & IH2 & IH3).
        split; [exact IH1|]. split; [exact IH2|].
        assert (Hskip : rdn segs (wbytes (mem_denot E base rest) (zw (ed E s' + k')) (Z_to_le_bytes w (ed E v)))
                          (zw (ed E s + k)) n
                        = rdn segs (mem_denot E base rest) (zw (ed E s + k)) n).
        { apply rdn_wbytes_skip; rewrite ?length_Z_to_le_bytes'; lia. }
        rewrite Hskip. exact IH3.
      * injection Hl as <- <- <-. split; [exact Hdj|]. split; [exact Hsc|]. exact I.
  - destruct (may_alias ma s s').
    { injection Hl as <- <- <-. split; [exact Hdj|]. split; [exact Hsc|]. exact I. }
    destruct Hh1 as (rb0 & Hfb & Hblo & Hbhi). rewrite Hfb in Hl.
    assert (Hrbs : r_s rb0 = s') by exact (find_hull_s _ _ _ Hfb).
    assert (Hrbf : flat_ok E rb0).
    { apply find_hull_In in Hfb. rewrite Forall_forall in Hfl. exact (Hfl _ Hfb). }
    assert (Hgo : forall dj' acc',
              lookup ma fl rest s k (Z.of_nat n) ra dj' acc' = (res, dj1, acc1) ->
              Forall (dj_ok E) dj' -> dj_ok E (ra, rb0) ->
              (scs_denot segs base E acc' -> scs_denot segs base E acc) ->
              Forall (dj_ok E) dj1 /\ scs_denot segs base E acc /\
              match res with
              | LKStuck => True
              | LKHit delta w0 v0 =>
                  0 <= delta /\ delta + Z.of_nat n <= Z.of_nat w0 /\
                  rdn segs (wbytes (mem_denot E base rest) (zw (ed E s' + k')) (Z_to_le_bytes w (ed E v)))
                      (zw (ed E s + k)) n
                  = Some (firstn n (skipn (Z.to_nat delta) (Z_to_le_bytes w0 (ed E v0))))
              | LKBase =>
                  rdn segs (wbytes (mem_denot E base rest) (zw (ed E s' + k')) (Z_to_le_bytes w (ed E v)))
                      (zw (ed E s + k)) n
                  = rdn segs base (zw (ed E s + k)) n
              end).
    { intros dj' acc' Hl' Hdj' Hab Hacc'.
      specialize (IH s k n ra dj' acc' res dj1 acc1 Hl' Hsc Hdj' Hfl Hhl' Hef' Hras Hlo Hhi Hra)
        as (IH1 & IH2 & IH3).
      split; [exact IH1|]. split; [exact (Hacc' IH2)|].
      assert (Hskip : rdn segs (wbytes (mem_denot E base rest) (zw (ed E s' + k')) (Z_to_le_bytes w (ed E v)))
                        (zw (ed E s + k)) n
                      = rdn segs (mem_denot E base rest) (zw (ed E s + k)) n).
      { unfold dj_ok in Hab. rewrite Hras, Hrbs in Hab. unfold flat_ok in Hrbf. rewrite Hrbs in Hrbf.
        apply rdn_wbytes_skip; rewrite ?length_Z_to_le_bytes'; lia. }
      rewrite Hskip. exact IH3. }
    destruct (dj_known dj ra rb0) eqn:Hk.
    + apply (Hgo dj acc Hl Hdj); [|intro X; exact X].
      apply (dj_known_sound E dj ra rb0 Hdj Hk); lia.
    + destruct (lookup_acc _ _ _ _ _ _ _ _ _ _ _ _ Hl) as [pre Hpre].
      pose proof Hsc as HscC. rewrite Hpre in HscC. apply scs_denot_app in HscC as [_ Hsc2].
      pose proof (Forall_inv Hsc2) as Hab. cbn [sc_denot] in Hab.
      apply (Hgo ((ra, rb0) :: dj) (SCDisj ra rb0 :: acc) Hl).
      * constructor; [exact Hab | exact Hdj].
      * exact Hab.
      * intro X. exact (Forall_inv_tail X).
Qed.


Lemma v_addi_zw : forall a i, v_addi (zw a) i = zw (a + i).
Proof.
  intros a i. unfold v_addi. rewrite u_zw. apply zw_eqm.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma lit4_zw : forall E p, zw (ed E (lit4 p)) = v_addi (zw (ed E p)) 4.
Proof. intros E p. unfold lit4. rewrite mkAdd_ed, v_addi_zw. reflexivity. Qed.

Lemma lin_addr : forall E g imm s k x,
  lin (mkAdd g (ELit imm)) = (s, k) -> x = zw (ed E g) ->
  zw (ed E s + k) = v_addi x imm.
Proof.
  intros E g imm s k x Hl ->. rewrite v_addi_zw.
  pose proof (lin_ed E (mkAdd g (ELit imm))) as H. rewrite Hl in H. cbn [fst snd] in H.
  rewrite <- H, mkAdd_ed. reflexivity.
Qed.

Lemma zw_land_m2 : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 ->
  zw (Z.land a (-2)) = zw (Z.land b (-2)).
Proof.
  intros a b H. apply zw_eqm. rewrite !land_mod by lia. rewrite H. reflexivity.
Qed.

Lemma v_jalr_zw : forall a i, v_jalr (zw a) i = zw (Z.land (a + i) (-2)).
Proof.
  intros a i. unfold v_jalr, jalr_tgtZ. rewrite u_zw. fold (zw (Z.land (a mod 2 ^ 64 + i) (-2))).
  apply zw_land_m2. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Definition load_res_ok (sz : msize) (sgn : bool) : Prop :=
  match sz, sgn with SZ8, false => False | _, _ => True end.

Lemma load_cases : forall C E regs pc mem rom w sz sgn rd rs (imm : bv 12) bs V vbx raw,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sgn rd rs imm, 4) ->
  load_res_ok sz sgn ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (msize_bytes sz) = Some bs ->
  bytes_le_to_Z bs = V ->
  ed E raw = V -> vars_ok E vbx -> funs_ok E (c_fb C) ->
  exists v', RiscvSemantics.step segs (mkst regs pc mem rom)
             = MachineOk (mkst (if bv_eqb rd 0%bv then regs else regupd regs rd v') (v_addi pc 4) mem rom)
        /\ zw (ed E (load_result C vbx sz sgn raw)) = v'.
Proof.
  intros C E regs pc mem rom w sz sgn rd rs imm bs V vbx raw Hf He Hd Hok Hrd Hbs Hraw Hvb Hfb.
  pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
  pose proof (bytes_le_to_Z_bound bs) as HbV. pose proof (bytes_le_to_Z_nonneg bs) as HbV0.
  rewrite Hlen, Hbs in HbV. rewrite Hbs in HbV0.
  assert (HuV : bv_unsigned (zw V) = V).
  { apply u_zw_small. destruct sz; cbn [msize_bytes Z.of_nat] in HbV; lia. }
  unfold load_result.
  destruct sz; destruct sgn; cbn [msize_bytes] in *; try (exfalso; exact Hok).
  - destruct bs as [|b [|]]; cbn in Hlen; try discriminate.
    rewrite bytes_le_to_Z_1 in Hbs.
    eexists. split; [exact (step_lb segs regs pc mem rom w rd rs imm b Hf He Hd Hrd)|].
    rewrite (mkSx_ed vbx (c_fb C) E Hvb Hfb), Hraw. unfold v_lb.
    change (Z_to_bv 64 (bv_signed b)) with (zw (bv_signed b)). f_equal.
    unfold bv_signed. rewrite Hbs, szwrap8. reflexivity.
  - destruct bs as [|b [|]]; cbn in Hlen; try discriminate.
    rewrite bytes_le_to_Z_1 in Hbs.
    eexists. split; [exact (step_lbu segs regs pc mem rom w rd rs imm b Hf He Hd Hrd)|].
    rewrite Hraw, <- Hbs. reflexivity.
  - eexists. split; [exact (step_lh segs regs pc mem rom w rd rs imm bs (zw V) Hf He Hd Hrd
                                        ltac:(rewrite HuV; exact Hbs))|].
    rewrite (mkSx_ed vbx (c_fb C) E Hvb Hfb), Hraw. unfold v_lh. rewrite HuV, szwrap16. reflexivity.
  - eexists. split; [exact (step_lhu segs regs pc mem rom w rd rs imm bs (zw V) Hf He Hd Hrd
                                        ltac:(rewrite HuV; exact Hbs))|].
    rewrite Hraw. reflexivity.
  - eexists. split; [exact (SymExec.step_lw segs regs pc mem rom w rd rs imm bs (zw V) Hf He Hd Hrd
                                        ltac:(rewrite HuV; exact Hbs))|].
    rewrite (mkSx_ed vbx (c_fb C) E Hvb Hfb), Hraw. unfold v_lw. rewrite HuV, szwrap32. reflexivity.
  - eexists. split; [exact (step_lwu segs regs pc mem rom w rd rs imm bs (zw V) Hf He Hd Hrd
                                        ltac:(rewrite HuV; exact Hbs))|].
    rewrite Hraw. reflexivity.
  - eexists. split; [exact (step_ld segs regs pc mem rom w rd rs imm bs (zw V) Hf He Hd Hrd
                                        ltac:(rewrite HuV; exact Hbs))|].
    rewrite Hraw. reflexivity.
Qed.


Lemma zbits_eq : forall sz, zbits sz = 8 * Z.of_nat (msize_bytes sz).
Proof. intros []; reflexivity. Qed.

Lemma step_sound : forall C E base rom ss ms i ss' scs rds rds' w,
  fetch_word segs (zw (ed E (s_pc ss))) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4) ->
  step C i ss rds = Some (ss', scs, rds') ->
  scs_denot segs base E scs ->
  funs_ok E (c_fb C) ->
  st_ok segs E base rom ss ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok segs E base rom ss' ms'.
Proof.
  intros C E base rom ss ms i ss' scs rds rds' w Hf He Hd Hs Hsc Hfb
    (regs & -> & Hregs & Hinv).
  destruct Hinv as (Hvb & Hfl & Hdj & Hsok & Hef & Hhl & Hrdc).
  set (mem := mem_denot E base (s_log ss)) in *.
  set (pc := zw (ed E (s_pc ss))) in *.
  assert (REG : forall rd e v,
    zw (ed E e) = v ->
    st_ok segs E base rom (sset ss rd e (lit4 (s_pc ss)))
          (mkst (if bv_eqb rd 0%bv then regs else regupd regs rd v) (v_addi pc 4) mem rom)).
  { intros rd e v Hv. exists (if bv_eqb rd 0%bv then regs else regupd regs rd v).
    split; [unfold sset; cbn [s_pc s_log]; rewrite lit4_zw; reflexivity|].
    split; [apply regs_ok_upd; [exact Hregs | exact Hv]|].
    unfold inv_ok, sset; cbn [s_vb s_flat s_dj s_sok s_log s_rd].
    split; [exact Hvb|]. split; [exact Hfl|]. split; [exact Hdj|]. split; [exact Hsok|].
    split; [exact Hef|]. split; [exact Hhl | exact Hrdc]. }
  destruct i; cbn [step] in Hs; try discriminate.
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_lui segs regs pc mem rom w rd imm Hf He Hd)|].
    apply REG. reflexivity.
  - destruct (s_pc ss) as [pz| | | | | | | | | | | | | | | | | | ] eqn:Hpc in Hs; try discriminate.
    injection Hs as <- <- <-.
    eexists. split; [exact (step_auipc segs regs pc mem rom w rd imm Hf He Hd)|].
    rewrite <- Hpc. apply REG. cbn [ed]. unfold v_auipc, pc. rewrite Hpc. cbn [ed].
    rewrite u_zw. apply zw_eqm. rewrite Zplus_mod_idemp_r. reflexivity.
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_jal_link segs regs pc mem rom w rd imm Hf He Hd)|].
    exists (if bv_eqb rd 0%bv then regs else regupd regs rd (v_addi pc 4)).
    split.
    + unfold sset; cbn [s_pc s_log]. unfold btgt. rewrite mkAdd_ed. cbn [ed].
      unfold pc. rewrite !v_addi_zw. reflexivity.
    + split; [apply regs_ok_upd; [exact Hregs | apply lit4_zw]|].
      unfold inv_ok, sset; cbn [s_vb s_flat s_dj s_sok s_log s_rd].
      split; [exact Hvb|]. split; [exact Hfl|]. split; [exact Hdj|]. split; [exact Hsok|].
      split; [exact Hef|]. split; [exact Hhl | exact Hrdc].
  -
    assert (Htgt : v_jalr (getr regs rs1) (bv_signed imm)
                   = zw (Z.land (ed E (mkAdd (sr_get (s_regs ss) rs1) (ELit (bv_signed imm)))) (-2))).
    { rewrite (Hregs rs1), v_jalr_zw, mkAdd_ed. reflexivity. }
    assert (GO : forall (tgt : expr) scs0,
      Some (sset ss rd (lit4 (s_pc ss)) tgt, scs0, rds) = Some (ss', scs, rds') ->
      zw (ed E tgt) = v_jalr (getr regs rs1) (bv_signed imm) ->
      exists ms', RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk ms' /\ st_ok segs E base rom ss' ms').
    { intros tgt scs0 HS Ht. injection HS as <- <- <-.
      eexists. split; [exact (step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd)|].
      exists (if bv_eqb rd 0%bv then regs else regupd regs rd (v_addi pc 4)).
      split; [unfold sset; cbn [s_pc s_log]; rewrite Ht; reflexivity|].
      split; [apply regs_ok_upd; [exact Hregs | apply lit4_zw]|].
      unfold inv_ok, sset; cbn [s_vb s_flat s_dj s_sok s_log s_rd].
      split; [exact Hvb|]. split; [exact Hfl|]. split; [exact Hdj|]. split; [exact Hsok|].
      split; [exact Hef|]. split; [exact Hhl | exact Hrdc]. }
    destruct (mkAdd (sr_get (s_regs ss) rs1) (ELit (bv_signed imm))) eqn:Ht;
      try (destruct (existsb _ (c_rets C));
           [ pose proof Hs as Hs2; injection Hs2 as _ Escs _; rewrite <- Escs in Hsc;
             eapply GO; [exact Hs|]; rewrite Htgt;
             pose proof (Forall_inv Hsc) as HJ; cbn [sc_denot] in HJ; exact (eq_sym HJ)
           | eapply GO; [exact Hs|]; rewrite Htgt, (mkAnd_ed (s_vb ss) (c_fb C) E Hvb Hfb); reflexivity ]).
    eapply GO; [exact Hs|]. rewrite Htgt. reflexivity.
  -
    destruct (match sz, signed with SZ8, false => true | _, _ => false end) eqn:Hgd; [discriminate|].
    assert (Hok : load_res_ok sz signed) by (destruct sz, signed; cbn; try exact I; discriminate).
    destruct (lin (mkAdd (sr_get (s_regs ss) rs1) (ELit (bv_signed imm)))) as [s k] eqn:Hlin.
    destruct (note_flat (s_flat ss) s k (Z.of_nat (msize_bytes sz))) as [[fl1 ra] scf] eqn:Hnf.
    pose proof (lin_addr E _ _ _ _ _ Hlin (Hregs rs1)) as Haddr.
    destruct (lookup (c_ma C) fl1 (s_log ss) s k (Z.of_nat (msize_bytes sz)) ra (s_dj ss) [])
      as [[res dj1] scd] eqn:Hlk.
    assert (Hscf : scs_denot segs base E scf).
    { destruct res; [discriminate| |]; [injection Hs as _ <- _ | ];
      [ apply scs_denot_app in Hsc as [H _]; exact H |].
      destruct (rd_known (s_rd ss) s k (msize_bytes sz));
        [injection Hs as _ <- _; apply scs_denot_app in Hsc as [H _]; exact H|].
      destruct (pick_read (c_av C) s k (msize_bytes sz) (s_next ss) rds) as [[rv0 fr0] rds0];
        cbv beta iota zeta in Hs; injection Hs as _ <- _;
        apply scs_denot_app in Hsc as [H _]; exact H. }
    destruct (note_flat_sound base E (s_flat ss) s k _ fl1 ra scf Hnf ltac:(lia) Hfl Hscf)
      as (Hfl1 & Hfra & Hras & Hralo & Hrahi & Hraf & Hcov).
    assert (Hhl1 : log_hulled fl1 (s_log ss)).
    { unfold log_hulled in *. rewrite Forall_forall in Hhl |- *. intros e Hin. apply Hcov. exact (Hhl e Hin). }
    assert (FIN : forall bs vbx (raw : expr) dj1' scs0 rd1 nx rdsx,
      rdn segs mem (v_addi (getr regs rs1) (bv_signed imm)) (msize_bytes sz) = Some bs ->
      ed E raw = bytes_le_to_Z bs -> vars_ok E vbx -> Forall (dj_ok E) dj1' -> Forall (rd_ok segs base E) rd1 ->
      Some (SS (lit4 (s_pc ss))
               (if bv_eqb rd 0%bv then s_regs ss else sr_upd (s_regs ss) (ridx rd) (load_result C vbx sz signed raw))
               (s_log ss) nx vbx fl1 dj1' (s_sok ss) rd1, scs0, rdsx) = Some (ss', scs, rds') ->
      exists ms', RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk ms' /\ st_ok segs E base rom ss' ms').
    { intros bs vbx raw dj1' scs0 rd1 nx rdsx Hrd Hraw Hvbx Hdj1 Hrd1 HS. injection HS as <- <- <-.
      destruct (load_cases C E regs pc mem rom w sz signed rd rs1 imm bs _ vbx raw
                  Hf He Hd Hok Hrd eq_refl Hraw Hvbx Hfb) as (v' & Hstep & Hv').
      eexists. split; [exact Hstep|].
      exists (if bv_eqb rd 0%bv then regs else regupd regs rd v').
      split; [cbn [s_pc s_log]; rewrite lit4_zw; reflexivity|].
      split; [cbn [s_regs]; apply regs_ok_upd; [exact Hregs | exact Hv']|].
      unfold inv_ok; cbn [s_vb s_flat s_dj s_sok s_log s_rd].
      split; [exact Hvbx|]. split; [exact Hfl1|]. split; [exact Hdj1|]. split; [exact Hsok|].
      split; [exact Hef|]. split; [exact Hhl1 | exact Hrd1]. }
    destruct res as [|delta wd v|]; [discriminate| |].
    +
      assert (Hscd : scs_denot segs base E scd).
      { pose proof Hs as Hs2. injection Hs2 as _ E2 _. rewrite <- E2 in Hsc.
        apply scs_denot_app in Hsc as [_ H]; exact H. }
      destruct (lookup_sound base E _ _ _ _ _ _ _ _ _ _ _ _ Hlk Hscd Hdj Hfl1 Hhl1 Hef Hras Hralo Hrahi Hraf)
        as (Hdj1 & _ & Hd0 & Hdn & Hrd).
      rewrite Haddr in Hrd.
      eapply (FIN _ (s_vb ss) _ dj1 _ (s_rd ss) (s_next ss) _ Hrd); [| exact Hvb | exact Hdj1 | exact Hrdc | exact Hs].
      rewrite (mkZx_ed _ _ E Hvb Hfb), (mkShr_ed _ _ E Hvb Hfb) by lia.
      rewrite subread_value by lia. rewrite Z2Nat.id, zbits_eq by lia. reflexivity.
    +
      destruct (rd_known (s_rd ss) s k (msize_bytes sz)) as [rv|] eqn:Hkn.
      *
        assert (Hscd : scs_denot segs base E scd).
        { pose proof Hs as Hs2. injection Hs2 as _ E2 _. rewrite <- E2 in Hsc.
          apply scs_denot_app in Hsc as [_ H]; exact H. }
        destruct (lookup_sound base E _ _ _ _ _ _ _ _ _ _ _ _ Hlk Hscd Hdj Hfl1 Hhl1 Hef Hras Hralo Hrahi Hraf)
          as (Hdj1 & _ & Hrd).
        assert (Hc : rd_ok segs base E (s, k, msize_bytes sz, rv)).
        { clear -Hrdc Hkn. induction (s_rd ss) as [|[[[s' k'] n'] v'] rest IH]; cbn [rd_known] in Hkn; [discriminate|].
          inversion Hrdc as [|x l Hx Hrest]; subst.
          destruct (expr_eqb s s' && Z.eqb k k' && Nat.eqb (msize_bytes sz) n') eqn:Heq.
          - injection Hkn as <-. apply andb_prop in Heq as [Heq H3]. apply andb_prop in Heq as [H1 H2].
            apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply Nat.eqb_eq in H3. subst. exact Hx.
          - apply IH; assumption. }
        destruct Hc as (bs & Hrdb & Hbs).
        rewrite Hrdb, Haddr in Hrd.
        pose proof (rdn_length _ _ _ _ _ Hrdb) as Hlen.
        pose proof (bytes_le_to_Z_bound bs) as HbV. rewrite Hlen, Hbs, <- zbits_eq in HbV.
        pose proof (bytes_le_to_Z_nonneg bs) as HbV0. rewrite Hbs in HbV0.
        eapply (FIN bs (s_vb ss) _ dj1 _ (s_rd ss) (s_next ss) _ Hrd); [| exact Hvb | exact Hdj1 | exact Hrdc | exact Hs].
        rewrite (mkZx_ed _ _ E Hvb Hfb), Hbs. apply Z.mod_small. lia.
      *
      destruct (pick_read (c_av C) s k (msize_bytes sz) (s_next ss) rds) as [[rv fresh] rds2] eqn:Hpick.
      cbv beta iota zeta in Hs.
      set (vb1 := if fresh then (s_next ss, 2 ^ zbits sz) :: s_vb ss else s_vb ss) in *.
      assert (Hshape : Some (SS (lit4 (s_pc ss))
                 (if bv_eqb rd 0%bv then s_regs ss
                  else sr_upd (s_regs ss) (ridx rd) (load_result C vb1 sz signed (mkZx vb1 (c_fb C) (zbits sz) rv)))
                 (s_log ss) (if fresh then S (s_next ss) else s_next ss) vb1 fl1 dj1 (s_sok ss) ((s, k, msize_bytes sz, rv) :: s_rd ss),
                 scf ++ SCRead s k (msize_bytes sz) rv :: scd, rds2) = Some (ss', scs, rds')
              /\ scs = scf ++ SCRead s k (msize_bytes sz) rv :: scd /\ rds' = rds2).
      { split; [exact Hs|]. injection Hs as _ <- <-. split; reflexivity. }
      destruct Hshape as (Hs' & Escs & ->). rewrite Escs in Hsc.
      apply scs_denot_app in Hsc as [_ Hsc2].
      pose proof (Forall_inv Hsc2) as Hread. pose proof (Forall_inv_tail Hsc2) as Hscd.
      cbn [sc_denot] in Hread. destruct Hread as (bs & Hrdb & Hbs).
      destruct (lookup_sound base E _ _ _ _ _ _ _ _ _ _ _ _ Hlk Hscd Hdj Hfl1 Hhl1 Hef Hras Hralo Hrahi Hraf)
        as (Hdj1 & _ & Hrd).
      rewrite Hrdb, Haddr in Hrd.
      pose proof (rdn_length _ _ _ _ _ Hrdb) as Hlen.
      pose proof (bytes_le_to_Z_bound bs) as HbV. rewrite Hlen, Hbs, <- zbits_eq in HbV.
      pose proof (bytes_le_to_Z_nonneg bs) as HbV0. rewrite Hbs in HbV0.
      assert (Hvb1 : vars_ok E vb1).
      { subst vb1. destruct fresh; [|exact Hvb].
        pose proof (pick_read_fresh _ _ _ _ _ _ _ _ Hpick) as Hrv. subst rv.
        intros n0 b0 Hb; cbn [blookup] in Hb;
          destruct (Nat.eqb (s_next ss) n0) eqn:Hn; [|exact (Hvb n0 b0 Hb)];
          apply Nat.eqb_eq in Hn; subst n0; injection Hb as <-;
          cbn [ed] in HbV, HbV0; lia. }
      eapply (FIN bs vb1 _ dj1 _ ((s, k, msize_bytes sz, rv) :: s_rd ss) (if fresh then S (s_next ss) else s_next ss) _ Hrd);
        [| exact Hvb1 | exact Hdj1 | | rewrite <- Escs in Hs'; exact Hs'].
      -- rewrite (mkZx_ed _ _ E Hvb1 Hfb), Hbs. apply Z.mod_small. lia.
      -- constructor; [|exact Hrdc]. unfold rd_ok. exists bs. split; [|exact Hbs].
         rewrite Haddr. rewrite <- Haddr. exact Hrdb.
  -
    destruct (lin (mkAdd (sr_get (s_regs ss) rs1) (ELit (bv_signed imm)))) as [s k] eqn:Hlin.
    destruct (note_flat (s_flat ss) s k (Z.of_nat (msize_bytes sz))) as [[fl1 ra] scf] eqn:Hnf.
    pose proof (lin_addr E _ _ _ _ _ Hlin (Hregs rs1)) as Haddr.
    set (n := msize_bytes sz) in *.
    set (sok1 := if sok_known (s_sok ss) s k (Z.of_nat n) then s_sok ss else RG s k (k + Z.of_nat n) :: s_sok ss) in *.
    set (scs1 := if sok_known (s_sok ss) s k (Z.of_nat n) then [] else [SCStoreOk (RG s k (k + Z.of_nat n))]) in *.
    assert (Hshape : ss' = SS (lit4 (s_pc ss)) (s_regs ss) (SE s k n (sr_get (s_regs ss) rs2) :: s_log ss)
                              (s_next ss) (s_vb ss) fl1 (s_dj ss) sok1 (s_rd ss)
                     /\ scs = scf ++ scs1 /\ rds' = rds).
    { unfold sok1, scs1. destruct (sok_known (s_sok ss) s k (Z.of_nat n)); injection Hs as <- <- <-;
        repeat split; reflexivity. }
    clear Hs. destruct Hshape as (-> & -> & ->).
    apply scs_denot_app in Hsc as [Hscf Hscs].
    destruct (note_flat_sound base E (s_flat ss) s k _ fl1 ra scf Hnf ltac:(lia) Hfl Hscf)
      as (Hfl1 & Hfra & Hras & Hralo & Hrahi & Hraf & Hcov).
    assert (Hn8 : (1 <= n <= 8)%nat) by (unfold n; destruct sz; cbn; lia).
    assert (Hflat : 0 <= ed E s + k /\ ed E s + k + Z.of_nat n <= 2 ^ 64).
    { unfold flat_ok in Hraf. rewrite Hras in Hraf. lia. }
    assert (Hsok1 : Forall (sok_ok segs base E) sok1
                    /\ RiscvSemantics.store_ok segs base (zw (ed E s + k)) n = true).
    { unfold sok1, scs1 in *. destruct (sok_known (s_sok ss) s k (Z.of_nat n)) eqn:Hkn.
      - split; [exact Hsok|].
        clear -Hsok Hkn Hflat Hn8. induction (s_sok ss) as [|r rest IH]; cbn [sok_known] in Hkn; [discriminate|].
        inversion Hsok as [|r' l Hr Hrest]; subst.
        apply orb_prop in Hkn as [Hin|Hkn]; [|apply IH; assumption].
        apply in_region_sound in Hin as (Hs' & Hlo & Hhi).
        destruct Hr as (Hrf & Hle & Hst). unfold flat_ok in Hrf. rewrite Hs' in Hrf, Hst.
        eapply (store_ok_sub segs base (zw (ed E s + r_lo r)) (zw (ed E s + k)) (Z.to_nat (r_hi r - r_lo r)) n);
          [ rewrite u_zw_small by lia; lia | exact Hst | rewrite !u_zw_small by lia; lia
          | rewrite !u_zw_small by lia; lia ].
      - pose proof (Forall_inv Hscs) as Hst. cbn [sc_denot] in Hst.
        split; [constructor; [exact Hst | exact Hsok]|].
        destruct Hst as (_ & _ & Hst). cbn [r_s r_lo r_hi] in Hst.
        replace (Z.to_nat (k + Z.of_nat n - k)) with n in Hst by lia. exact Hst. }
    destruct Hsok1 as [Hsok1 Hstore].
    assert (Hstore' : RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) n = true).
    { rewrite <- Haddr. eapply store_ok_mono; [apply mem_denot_grows | exact Hstore]. }
    assert (Hmem : wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes n (getr regs rs2))
                   = mem_denot E base (SE s k n (sr_get (s_regs ss) rs2) :: s_log ss)).
    { cbn [mem_denot]. rewrite <- Haddr, (Hregs rs2), word_to_le_bytes_zw by lia. reflexivity. }
    assert (POST : st_ok segs E base rom
              (SS (lit4 (s_pc ss)) (s_regs ss) (SE s k n (sr_get (s_regs ss) rs2) :: s_log ss)
                  (s_next ss) (s_vb ss) fl1 (s_dj ss) sok1 (s_rd ss))
              (mkst regs (v_addi pc 4)
                 (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes n (getr regs rs2))) rom)).
    { exists regs. split; [cbn [s_pc s_log]; rewrite lit4_zw, Hmem; reflexivity|].
      split; [exact Hregs|].
      unfold inv_ok; cbn [s_vb s_flat s_dj s_sok s_log s_rd].
      split; [exact Hvb|]. split; [exact Hfl1|]. split; [exact Hdj|]. split; [exact Hsok1|].
      split; [|split].
      - constructor; [|exact Hef]. unfold entry_flat; cbn [e_s e_k e_w]. exact Hflat.
      - constructor; [|]. { cbn [e_s e_k e_w]. exists ra. split; [exact Hfra | lia]. }
        unfold log_hulled in Hhl. rewrite Forall_forall in Hhl |- *. intros e Hin. apply Hcov. exact (Hhl e Hin).
      - exact Hrdc. }
    unfold n in *.
    destruct sz.
    + eexists. split; [exact (step_sb segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hstore')| exact POST].
    + eexists. split; [exact (step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hstore')| exact POST].
    + eexists. split; [exact (step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hstore')| exact POST].
    + eexists. split; [exact (step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hstore')| exact POST].
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_opimm_gen segs regs pc mem rom w op rd rs1 imm Hf He Hd)|].
    apply REG. rewrite (sem_alu_sound _ _ E Hvb Hfb), <- (Hregs rs1). reflexivity.
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_shiftimm_gen segs regs pc mem rom w op rd rs1 shamt Hf He Hd)|].
    apply REG. rewrite (sem_alu_sound _ _ E Hvb Hfb), <- (Hregs rs1). reflexivity.
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_op_gen segs regs pc mem rom w op rd rs1 rs2 Hf He Hd)|].
    apply REG. rewrite (sem_alu_sound _ _ E Hvb Hfb), <- (Hregs rs1), <- (Hregs rs2). reflexivity.
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_opimm32_gen segs regs pc mem rom w rd rs1 imm Hf He Hd)|].
    apply REG. rewrite (sext32_low32 imm), (Hregs rs1).
    exact (sem_aluw_sound (s_vb ss) (c_fb C) E Hvb Hfb ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm))).
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_shiftimm32_gen segs regs pc mem rom w op rd rs1 shamt Hf He Hd)|].
    apply REG. rewrite (sem_aluw_sound _ _ E Hvb Hfb), <- (Hregs rs1). cbn [ed].
    rewrite (zext32_low32 shamt). reflexivity.
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_op32_gen segs regs pc mem rom w op rd rs1 rs2 Hf He Hd)|].
    apply REG. rewrite (sem_aluw_sound _ _ E Hvb Hfb), <- (Hregs rs1), <- (Hregs rs2). reflexivity.
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_mul_gen segs regs pc mem rom w op rd rs1 rs2 Hf He Hd)|].
    apply REG. rewrite (sem_md_sound _ _ E Hvb Hfb), <- (Hregs rs1), <- (Hregs rs2). reflexivity.
  - injection Hs as <- <- <-.
    eexists. split; [exact (step_mul32_gen segs regs pc mem rom w op rd rs1 rs2 Hf He Hd)|].
    apply REG. rewrite (sem_mdw_sound _ _ E Hvb Hfb), <- (Hregs rs1), <- (Hregs rs2). reflexivity.
Qed.


Lemma run_acc : forall C fuel first dirs rds ss acc,
  exists pre, snd (run segs C fuel first dirs rds ss acc) = pre ++ acc.
Proof.
  intros C fuel. induction fuel as [|f IH]; intros first dirs rds ss acc; [exists []; reflexivity|].
  cbn [run].
  destruct (s_pc ss) as [pz| | | | | | | | | | | | | | | | | | ]; try (exists []; reflexivity).
  destruct (negb first && existsb (Z.eqb pz) (c_stops C)); [exists []; reflexivity|].
  destruct (fetch_word segs (Z_to_bv 64 pz)) as [w|]; [|exists []; reflexivity].
  destruct (is_ecall w); [exists []; reflexivity|].
  destruct (decode_any w) as [[i sz]|]; [|exists []; reflexivity].
  destruct (Z.eqb sz 4); cbn [negb]; [|exists []; reflexivity].
  destruct i;
    try (match goal with
         | |- context [ step C ?ii ss rds ] =>
             destruct (step C ii ss rds) as [[[ss2 scs2] rds2]|];
               [ destruct (IH false dirs rds2 ss2 (scs2 ++ acc)) as [pre Hpre];
                 exists (pre ++ scs2); rewrite <- app_assoc; exact Hpre
               | exists []; reflexivity ]
         end).
  destruct dirs as [|t dirs']; [exists []; reflexivity|].
  match goal with
  | |- exists pre, snd (let '(a', b') := ?ab in _) = _ => destruct ab as [a' b']
  end.
  match goal with
  | |- exists pre, snd (run _ _ _ _ _ _ ?ss2 (?sc :: acc)) = _ =>
      destruct (IH false dirs' rds ss2 (sc :: acc)) as [pre Hpre];
      exists (pre ++ [sc]); rewrite <- app_assoc; exact Hpre
  end.
Qed.

Theorem run_sound : forall C fuel first dirs rds ss acc ss' scs E base rom ms,
  run segs C fuel first dirs rds ss acc = (ss', scs) ->
  scs_denot segs base E scs ->
  funs_ok E (c_fb C) ->
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms'.
Proof.
  intros C fuel. induction fuel as [|f IH]; intros first dirs rds ss acc ss' scs E base rom ms Hex Hsc Hfb Hst.
  { cbn in Hex. injection Hex as <- <-. exists ms. split; [apply mst_refl|exact Hst]. }
  assert (Hstop : (ss, acc) = (ss', scs) -> exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms').
  { intro HX. injection HX as <- <-. exists ms. split; [apply mst_refl|exact Hst]. }
  cbn [run] in Hex.
  destruct (s_pc ss) as [pz| | | | | | | | | | | | | | | | | | ] eqn:Hpc; try exact (Hstop Hex).
  destruct (negb first && existsb (Z.eqb pz) (c_stops C)); [exact (Hstop Hex)|].
  destruct (fetch_word segs (Z_to_bv 64 pz)) as [w|] eqn:Hf; [|exact (Hstop Hex)].
  assert (Hf' : fetch_word segs (zw (ed E (s_pc ss))) = Some w) by (rewrite Hpc; exact Hf).
  destruct (is_ecall w) eqn:He; [exact (Hstop Hex)|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hstop Hex)].
  destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in Hex; [|exact (Hstop Hex)].
  apply Z.eqb_eq in Hsz. subst sz.
  destruct i;
    try (match type of Hex with
         | context [ step C ?ii ss rds ] =>
             destruct (step C ii ss rds) as [[[ss2 scs2] rds2]|] eqn:Hstep;
               [|exact (Hstop Hex)];
             destruct (run_acc C f false dirs rds2 ss2 (scs2 ++ acc)) as [pre Hpre];
             rewrite Hex in Hpre; cbn [snd] in Hpre; subst scs;
             assert (Hsc2 : scs_denot segs base E scs2)
               by (apply scs_denot_app in Hsc as [_ Hsc]; apply scs_denot_app in Hsc as [Hsc _]; exact Hsc);
             destruct (step_sound C E base rom ss ms ii ss2 scs2 rds rds2 w Hf' He Hd Hstep Hsc2 Hfb Hst)
               as (msA & HstepA & HstA);
             destruct (IH false dirs rds2 ss2 (scs2 ++ acc) ss' _ E base rom msA Hex Hsc Hfb HstA)
               as (msB & HmsB & HstB);
             exists msB; split; [| exact HstB];
             eapply mst_step; [ destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact HmsB ]
         end).
  destruct dirs as [|t dirs']; [exact (Hstop Hex)|].
  destruct Hst as (regs & -> & Hregs & Hinv).
  pose proof Hinv as (Hvb & _).
  set (a := sr_get (s_regs ss) rs1) in *. set (b := sr_get (s_regs ss) rs2) in *.
  set (ab' := match c with
              | BC_LT | BC_GE => (mkSx (s_vb ss) (c_fb C) 64 a, mkSx (s_vb ss) (c_fb C) 64 b)
              | _ => (mkZx (s_vb ss) (c_fb C) 64 a, mkZx (s_vb ss) (c_fb C) 64 b)
              end) in *.
  destruct ab' as [a' b'] eqn:Hab.
  set (ss2 := SS (ELit (if t then pz + bv_signed imm else pz + 4)) (s_regs ss) (s_log ss) (s_next ss)
                 (s_vb ss) (s_flat ss) (s_dj ss) (s_sok ss) (s_rd ss)) in *.
  destruct (run_acc C f false dirs' rds ss2 (SCBr t c a' b' :: acc)) as [pre Hpre].
  rewrite Hex in Hpre. cbn [snd] in Hpre. subst scs.
  assert (Hbr : sc_denot segs base E (SCBr t c a' b')).
  { apply scs_denot_app in Hsc as [_ Hsc]. exact (Forall_inv Hsc). }
  cbn [sc_denot] in Hbr.
  assert (Htk : branch_taken c (getr regs rs1) (getr regs rs2) = t).
  { rewrite (Hregs rs1), (Hregs rs2). fold a b.
    destruct c; subst ab'; injection Hab as <- <-; unfold br_ok in Hbr;
      rewrite ?(mkZx_ed _ _ E Hvb Hfb), ?(mkSx_ed _ _ E Hvb Hfb) in Hbr;
      cbn [branch_taken]; unfold bv_eqb, bv_ltu, bv_lts; rewrite ?u_zw, ?s_zw;
      destruct t;
      first [ apply Z.eqb_eq; exact Hbr
            | apply Z.eqb_neq; exact Hbr
            | apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hbr
            | apply Bool.negb_false_iff; apply Z.eqb_eq; exact Hbr
            | apply Z.ltb_lt; exact Hbr
            | apply Z.ltb_ge; exact Hbr
            | apply Bool.negb_true_iff; apply Z.ltb_ge; exact Hbr
            | apply Bool.negb_false_iff; apply Z.ltb_lt; exact Hbr ]. }
  assert (HstA : st_ok segs E base rom ss2
                   (mkst regs (if t then btgt (zw (ed E (s_pc ss))) (bv_signed imm)
                               else v_addi (zw (ed E (s_pc ss))) 4)
                         (mem_denot E base (s_log ss)) rom)).
  { exists regs. split; [| split; [exact Hregs | exact Hinv]].
    subst ss2. cbn [s_pc s_log ed]. rewrite Hpc. cbn [ed]. unfold btgt.
    destruct t; rewrite v_addi_zw; reflexivity. }
  destruct (IH false dirs' rds _ _ ss' _ E base rom _ Hex Hsc Hfb HstA) as (msB & HmsB & HstB).
  exists msB. split; [| exact HstB].
  eapply mst_step; [ reflexivity | | exact HmsB ].
  destruct t.
  - exact (step_branch_tk_gen segs regs _ (mem_denot E base (s_log ss)) rom w c rs1 rs2 imm Hf' He Hd Htk).
  - exact (step_branch_ft_gen segs regs _ (mem_denot E base (s_log ss)) rom w c rs1 rs2 imm Hf' He Hd Htk).
Qed.

Theorem run_ex : forall C fuel first dirs rds ss acc ss' scs E base rom ms,
  run segs C fuel first dirs rds ss acc = (ss', scs) ->
  scs_denot segs base E scs ->
  funs_ok E (c_fb C) ->
  st_ok segs E base rom ss ms ->
  exists R, regs_ok E (s_regs ss') R
         /\ inv_ok segs base E ss'
         /\ msteps segs ms (mkst R (zw (ed E (s_pc ss'))) (mem_denot E base (s_log ss')) rom).
Proof.
  intros C fuel first dirs rds ss acc ss' scs E base rom ms Hex Hsc Hfb Hst.
  destruct (run_sound C fuel first dirs rds ss acc ss' scs E base rom ms Hex Hsc Hfb Hst)
    as (ms' & Hms & (R & Heq & Hregs & Hinv)).
  exists R. split; [exact Hregs|]. split; [exact Hinv|]. rewrite <- Heq. exact Hms.
Qed.

End Sound.
End FXG.
