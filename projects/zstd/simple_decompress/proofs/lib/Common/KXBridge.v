(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition acc_sym (fk : list kentry) (i : instr) (ss : sym_state) : option (list (saddr * nat)) :=
  match i with
  | Load msz _ _ rs1 imm => Some [(to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm), msize_bytes msz)]
  | Store msz rs1 _ imm => Some [(to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm), msize_bytes msz)]
  | Lui _ _ | Auipc _ _ | Jal _ _ | Jalr _ _ _ | Branch _ _ _ _ | OpImm _ _ _ _ | ShiftImm _ _ _ _ | Op _ _ _ _
  | OpImm32 _ _ _ | ShiftImm32 _ _ _ _ | Op32 _ _ _ _ | Mul _ _ _ _ | Mul32 _ _ _ _ => Some []
  | _ => None
  end.

Definition kxout : Type := (sym_state * list sidecond * scripts * list (saddr * nat))%type.

Section Driver.
Variable segs : list Segment.

Fixpoint kx_exec (fuel : nat) (first : bool) (stops : list Z) (scr : scripts) (ss : sym_state)
                 (acc : list sidecond) (accs : list (saddr * nat)) : kxout :=
  match fuel with
  | O => (ss, acc, scr, accs)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (ss, acc, scr, accs) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => (ss, acc, scr, accs)
      | Some w =>
          if is_ecall w then (ss, acc, scr, accs) else
          match decode_any w with
          | None => (ss, acc, scr, accs)
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (ss, acc, scr, accs) else
              match acc_sym (facts_of (s_know ss)) i ss with
              | None => (ss, acc, scr, accs)
              | Some la =>
                  match sym_step segs i ss scr with
                  | SOk ss' scs scr' =>
                      if s_clean ss' then kx_exec f false stops scr' ss' (sc_add scs acc) (la ++ accs)
                      else (ss, acc, scr, accs)
                  | SStop => (ss, acc, scr, accs)
                  end
              end
          end
      end
  end.

End Driver.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition accP (E : env) (RNG : footprint) (an : saddr * nat) : Prop :=
  RNG (bv_unsigned (adenot E (fst an))) (snd an).

Section Sound.
Variable segs : list Segment.
Variables (F : bvmap 5 word) (fc : bv 32).
Local Instance kx_fx : AS.PropExec.FPState := AS.PropExec.mkFP F fc.

Lemma getr_rgetR : forall regs r, AS.PropExec.getr regs r = rgetR regs r.
Proof. intros. unfold AS.PropExec.getr, rgetR. rewrite AS.PropExec.bv_eqb0_is_x0. reflexivity. Qed.

Lemma acc_sym_denot : forall E base ss regs i la,
  know_ok segs E base (s_know ss) -> regs_ok E (s_regs ss) regs ->
  acc_sym (facts_of (s_know ss)) i ss = Some la ->
  acc_of i regs = Some (map (fun an => (adenot E (fst an), snd an)) la).
Proof.
  intros E base ss regs i la Hkn Hr Ha.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk.
  destruct i; cbn [acc_sym] in Ha; try discriminate Ha; injection Ha as <-; cbn [acc_of map fst snd]; try reflexivity.
  - rewrite (to_saddrK_denot segs E base _ _ _ Hfk), <- Hr.
    pose proof (AS.PropExec.b_addsext (AS.PropExec.getr regs rs1) imm) as HH. rewrite (getr_rgetR regs rs1) in HH at 1.
    rewrite <- HH. destruct sz; reflexivity.
  - rewrite (to_saddrK_denot segs E base _ _ _ Hfk), <- Hr.
    pose proof (AS.PropExec.b_addsext (AS.PropExec.getr regs rs1) imm) as HH. rewrite (getr_rgetR regs rs1) in HH at 1.
    rewrite <- HH. destruct sz; reflexivity.
Qed.

Lemma kx_step_sound : forall E base rom RNG ss regs i ss' scs scr scr' w la,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  sym_step segs i ss scr = SOk ss' scs scr' ->
  acc_sym (facts_of (s_know ss)) i ss = Some la ->
  s_resv ss = None -> s_resv ss' = None ->
  scs_denot segs base E scs -> Forall (accP E RNG) la ->
  regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists regs',
    mstepF segs RNG (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom)
                    (MS regs' F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E base (s_log ss')) rom)
    /\ regs_ok E (s_regs ss') regs' /\ rfull regs' /\ log_flat E (s_log ss') /\ know_ok segs E base (s_know ss')
    /\ (mem_inv segs (mem_denot E base (s_log ss)) -> mem_inv segs (mem_denot E base (s_log ss'))).
Proof.
  intros E base rom RNG ss regs i ss' scs scr scr' w la Hf He Hd Hs Ha Hc Hc' Hsc Hacc Hr Hfull Hlf Hkn.
  assert (Hst : st_okR segs E base rom ss (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom)).
  { exists regs. rewrite Hc. split; [reflexivity|]. repeat split; assumption. }
  destruct (sym_step_soundR segs E base rom ss _ i ss' scs scr scr' w Hf He Hd Hs Hsc Hst) as (ms' & Hstep & (regs' & -> & Hr' & Hlf' & Hkn')).
  rewrite Hc' in Hstep. cbn [resv_denot] in Hstep.
  pose proof (acc_sym_denot E base ss regs i la Hkn Hr Ha) as Hao.
  destruct (step_acc_full segs regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom w i _ _ Hf He Hd Hfull Hao Hstep)
    as (Hfull' & Hrep & HMI).
  exists regs'. split; [|repeat split; assumption].
  split; [reflexivity|]. eexists. split; [exact Hrep|].
  clear - Hacc. induction Hacc as [|[a n] l H _ IH]; cbn [map]; constructor; [exact H | exact IH].
Qed.

Lemma kx_exec_sound : forall fuel first stops scr ss acc accs E base rom RNG r accr scrr accsr,
  kx_exec segs fuel first stops scr ss acc accs = (r, accr, scrr, accsr) ->
  s_resv ss = None ->
  s_resv r = None /\
  (scs_denot segs base E accr -> scs_denot segs base E acc) /\
  (Forall (accP E RNG) accsr -> Forall (accP E RNG) accs) /\
  (forall regs, scs_denot segs base E accr -> Forall (accP E RNG) accsr ->
     regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
     exists regs',
       mstepsF segs RNG (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom)
                        (MS regs' F (Z_to_bv 64 (s_pc r)) fc None (mem_denot E base (s_log r)) rom)
       /\ regs_ok E (s_regs r) regs' /\ rfull regs' /\ log_flat E (s_log r) /\ know_ok segs E base (s_know r)
       /\ (mem_inv segs (mem_denot E base (s_log ss)) -> mem_inv segs (mem_denot E base (s_log r)))).
Proof.
  induction fuel as [|f IH]; intros first stops scr ss acc accs E base rom RNG r accr scrr accsr Hex Hc.
  - cbn [kx_exec] in Hex. injection Hex as <- <- <- <-.
    split; [exact Hc|]. split; [auto|]. split; [auto|].
    intros regs _ _ Hr Hfu Hlf Hkn. exists regs. split; [constructor|]. repeat split; auto.
  - assert (Hstop : (ss, acc, scr, accs) = (r, accr, scrr, accsr) ->
       s_resv r = None /\
       (scs_denot segs base E accr -> scs_denot segs base E acc) /\
       (Forall (accP E RNG) accsr -> Forall (accP E RNG) accs) /\
       (forall regs, scs_denot segs base E accr -> Forall (accP E RNG) accsr ->
          regs_ok E (s_regs ss) regs -> rfull regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
          exists regs',
            mstepsF segs RNG (MS regs F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom)
                             (MS regs' F (Z_to_bv 64 (s_pc r)) fc None (mem_denot E base (s_log r)) rom)
            /\ regs_ok E (s_regs r) regs' /\ rfull regs' /\ log_flat E (s_log r) /\ know_ok segs E base (s_know r)
            /\ (mem_inv segs (mem_denot E base (s_log ss)) -> mem_inv segs (mem_denot E base (s_log r))))).
    { intros Hx. injection Hx as <- <- <- <-.
      split; [exact Hc|]. split; [auto|]. split; [auto|].
      intros regs _ _ Hr Hfu Hlf Hkn. exists regs. split; [constructor|]. repeat split; auto. }
    cbn [kx_exec] in Hex.
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact (Hstop Hex)|].
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact (Hstop Hex)].
    destruct (is_ecall w) eqn:He; [exact (Hstop Hex)|].
    destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hstop Hex)].
    destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in Hex; [|exact (Hstop Hex)].
    apply Z.eqb_eq in Hsz. subst sz.
    destruct (acc_sym (facts_of (s_know ss)) i ss) as [la|] eqn:Ha; [|exact (Hstop Hex)].
    destruct (sym_step segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|exact (Hstop Hex)].
    destruct (s_clean ss') eqn:Hcl; [|exact (Hstop Hex)].
    apply s_clean_None in Hcl.
    destruct (IH false stops scr' ss' (sc_add scs acc) (la ++ accs) E base rom RNG r accr scrr accsr Hex Hcl)
      as (Hr0 & Hsc0 & Hac0 & Hrun).
    split; [exact Hr0|].
    split; [intros H; exact (proj2 (sc_add_denot segs base E scs acc (Hsc0 H)))|].
    split; [intros H; apply Hac0 in H; apply Forall_app in H; exact (proj2 H)|].
    intros regs Hscs Haccs Hr Hfu Hlf Hkn.
    pose proof (sc_add_denot segs base E scs acc (Hsc0 Hscs)) as [Hscs1 _].
    pose proof (proj1 (proj1 (Forall_app _ _ _) (Hac0 Haccs))) as Hla.
    destruct (kx_step_sound E base rom RNG ss regs i ss' scs scr scr' w la Hf He Hd Hs Ha Hc Hcl Hscs1 Hla Hr Hfu Hlf Hkn)
      as (regs1 & Hstep & Hr1 & Hfu1 & Hlf1 & Hkn1 & Hmi1).
    destruct (Hrun regs1 Hscs Haccs Hr1 Hfu1 Hlf1 Hkn1) as (regs' & Hsteps & Hr2 & Hfu2 & Hlf2 & Hkn2 & Hmi2).
    exists regs'. split; [econstructor; [exact Hstep | exact Hsteps] |]. repeat split; auto.
Qed.

End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive zexp : Type :=
| ZL (z : Z) | ZA (n : nat) | ZAdd (a b : zexp) | ZSub (a b : zexp) | ZMul (a b : zexp) | ZOpp (a : zexp).

(* [comment removed for export] *)
Fixpoint znth (n : nat) (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | x :: t => match n with O => x | S n' => znth n' t end
  end.
Lemma znth_nth : forall n l, znth n l = nth n l 0%Z.
Proof. induction n as [|n IH]; intros [|x t]; cbn; auto. Qed.

Fixpoint zden (zs : list Z) (e : zexp) : Z :=
  match e with
  | ZL z => z
  | ZA n => znth n zs
  | ZAdd a b => (zden zs a + zden zs b)%Z
  | ZSub a b => (zden zs a - zden zs b)%Z
  | ZMul a b => (zden zs a * zden zs b)%Z
  | ZOpp a => (- zden zs a)%Z
  end.

(* [comment removed for export] *)
Fixpoint zx (e : zexp) : expr :=
  match e with
  | ZL z => ELit z
  | ZA n => EVar n
  | ZAdd a b => mkAlu ALU_ADD (zx a) (zx b)
  | ZSub a b => mkAlu ALU_SUB (zx a) (zx b)
  | ZMul a b => mkMd M_MUL (zx a) (zx b)
  | ZOpp a => mkAlu ALU_SUB (ELit 0) (zx a)
  end.

Fixpoint zwf (nz : nat) (e : zexp) : bool :=
  match e with
  | ZL _ => true
  | ZA n => Nat.ltb n nz
  | ZAdd a b | ZSub a b | ZMul a b => zwf nz a && zwf nz b
  | ZOpp a => zwf nz a
  end.

Definition atoms_ok (zs : list Z) (E : env) : Prop :=
  forall j, (j < length zs)%nat -> ev E j = Z_to_bv 64 (znth j zs).

Lemma Zbv_eq_mod : forall x y : Z, (x mod 2^64 = y mod 2^64)%Z -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma word_eq_Z : forall (w : word) z, (bv_unsigned w = z mod 2^64)%Z -> w = Z_to_bv 64 z.
Proof. intros w z H. apply bv_eq. rewrite Z_to_bv_unsigned. exact H. Qed.

Lemma zx_sound : forall zs E e, atoms_ok zs E -> zwf (length zs) e = true -> edenot E (zx e) = Z_to_bv 64 (zden zs e).
Proof.
  intros zs E e HA. induction e as [z|n|a IHa b IHb|a IHa b IHb|a IHa b IHb|a IHa]; cbn [zx zwf zden]; intros W.
  - reflexivity.
  - cbn [edenot]. apply HA. apply Nat.ltb_lt. exact W.
  - apply andb_prop in W as [Wa Wb]. rewrite mkAlu_denot, (IHa Wa), (IHb Wb). apply word_eq_Z.
    rewrite u_add64, !Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64)%Z. rewrite <- Zplus_mod. reflexivity.
  - apply andb_prop in W as [Wa Wb]. rewrite mkAlu_denot, (IHa Wa), (IHb Wb). apply word_eq_Z.
    rewrite u_sub64, !Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64)%Z. rewrite <- Zminus_mod. reflexivity.
  - apply andb_prop in W as [Wa Wb]. rewrite mkMd_denot, (IHa Wa), (IHb Wb). apply word_eq_Z.
    rewrite u_mul64, !Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64)%Z. rewrite <- Zmult_mod. reflexivity.
  - rewrite mkAlu_denot, (IHa W). cbn [edenot]. apply word_eq_Z.
    rewrite u_sub64, !Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64)%Z.
    rewrite <- Zminus_mod. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nob : nat -> list byte := fun _ => [].
Definition kx_env (xs : list word) : env := Env (fun n => nth n xs w0) nob.

Definition rdspec : Type := (saddr * nat * bool)%type.

Section Vals.
Variable segs : list Segment.
Variable m : word -> option byte.

Definition rdval (a : word) (n : nat) (sx : bool) : word :=
  match rdn segs m a n with
  | Some bs => Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))
  | None => w0
  end.

Fixpoint kx_vals (xs : list word) (reads : list rdspec) : list word :=
  match reads with
  | [] => xs
  | (a, n, sx) :: rest => kx_vals (xs ++ [rdval (adenot (kx_env xs) a) n sx]) rest
  end.

Lemma kx_vals_prefix : forall reads xs j, (j < length xs)%nat -> nth j (kx_vals xs reads) w0 = nth j xs w0.
Proof.
  induction reads as [|[[a n] sx] rest IH]; intros xs j Hj; cbn [kx_vals]; [reflexivity|].
  rewrite IH by (rewrite length_app; cbn; lia). apply app_nth1. exact Hj.
Qed.

Lemma kx_vals_read : forall reads xs k a n sx,
  nth_error reads k = Some (a, n, sx) -> evars_lt (length xs + k) (a_base a) = true ->
  nth (length xs + k) (kx_vals xs reads) w0 = rdval (adenot (kx_env (kx_vals xs reads)) a) n sx.
Proof.
  induction reads as [|[[a0 n0] sx0] rest IH]; intros xs k a n sx Hk Hv; [destruct k; discriminate Hk|].
  cbn [kx_vals]. destruct k as [|k]; cbn [nth_error] in Hk.
  - injection Hk as -> -> ->. rewrite Nat.add_0_r in *.
    rewrite kx_vals_prefix by (rewrite length_app; cbn; lia).
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    f_equal. unfold adenot. f_equal. apply (edenot_evars_lt (length xs)); [|exact Hv].
    split; [|reflexivity]. intros j Hj. cbn [ev kx_env].
    rewrite kx_vals_prefix by (rewrite length_app; cbn; lia). symmetry. apply app_nth1. exact Hj.
  - replace (length xs + S k)%nat with (length (xs ++ [rdval (adenot (kx_env xs) a0) n0 sx0]) + k)%nat
      by (rewrite length_app; cbn; lia).
    apply IH; [exact Hk|]. rewrite length_app. cbn [length]. replace (length xs + 1 + k)%nat with (length xs + S k)%nat by lia. exact Hv.
Qed.

(* [comment removed for export] *)
Definition reads_ok (nz : nat) (reads : list rdspec) (E : env) : Prop :=
  forall k a n sx, nth_error reads k = Some (a, n, sx) -> ev E (nz + k) = rdval (adenot E a) n sx.

Definition kx_env_ok (zs : list Z) (reads : list rdspec) (E : env) : Prop :=
  atoms_ok zs E /\ reads_ok (length zs) reads E.

(* [comment removed for export] *)
Definition rd_chk (nz : nat) (reads : list rdspec) (k : nat) (r : rdspec) : bool :=
  let '(a, n, sx) := r in evars_lt (nz + k) (a_base a).
Fixpoint rds_chk (nz : nat) (k : nat) (reads : list rdspec) : bool :=
  match reads with
  | [] => true
  | (a, n, sx) :: rest => evars_lt (nz + k) (a_base a) && rds_chk nz (S k) rest
  end.

Lemma rds_chk_nth : forall nz reads k0 k a n sx,
  rds_chk nz k0 reads = true -> nth_error reads k = Some (a, n, sx) -> evars_lt (nz + (k0 + k)) (a_base a) = true.
Proof.
  intros nz. induction reads as [|[[a0 n0] sx0] rest IH]; intros k0 k a n sx H Hk; [destruct k; discriminate Hk|].
  cbn [rds_chk] in H. apply andb_prop in H as [H1 H2]. destruct k as [|k]; cbn [nth_error] in Hk.
  - injection Hk as -> -> ->. rewrite Nat.add_0_r. exact H1.
  - replace (k0 + S k)%nat with (S k0 + k)%nat by lia. eapply IH; eassumption.
Qed.

Lemma kx_env_exists : forall zs reads,
  rds_chk (length zs) 0 reads = true ->
  kx_env_ok zs reads (kx_env (kx_vals (map (Z_to_bv 64) zs) reads)).
Proof.
  intros zs reads Hc. split.
  - intros j Hj. cbn [ev kx_env]. rewrite kx_vals_prefix by (rewrite length_map; exact Hj).
    rewrite znth_nth. change w0 with (Z_to_bv 64 0). apply map_nth.
  - intros k a n sx Hk. cbn [ev kx_env].
    pose proof (kx_vals_read reads (map (Z_to_bv 64) zs) k a n sx Hk) as H. rewrite length_map in H.
    apply H. exact (rds_chk_nth _ _ 0%nat k a n sx Hc Hk).
Qed.

(* [comment removed for export] *)

Definition rd_ok (E : env) (a : saddr) (n : nat) : Prop := rdn segs m (adenot E a) n <> None.

(* [comment removed for export] *)
Lemma rdn_AS : forall a n, AS.PropExec.rdn segs m a n = rdn segs m a n.
Proof. reflexivity. Qed.

Definition sc_resid (E : env) (sc : sidecond) : Prop :=
  match sc with
  | SCReadBase a n sx _ => rd_ok E a n
  | _ => sc_denot segs m E sc
  end.

Definition sc_rd_chk (nz : nat) (reads : list rdspec) (sc : sidecond) : bool :=
  match sc with
  | SCReadBase a n sx (EVar j) =>
      Nat.leb nz j &&
      match nth_error reads (j - nz) with
      | Some (a', n', sx') => saddr_eqb a a' && Nat.eqb n n' && Bool.eqb sx sx'
      | None => false
      end
  | SCReadBase _ _ _ _ => false
  | _ => true
  end.

Lemma kx_readbase : forall nz reads E sc,
  reads_ok nz reads E -> sc_rd_chk nz reads sc = true -> sc_resid E sc -> sc_denot segs m E sc.
Proof.
  intros nz reads E sc HR Hc Hres. destruct sc; try exact Hres.
  cbn [sc_rd_chk] in Hc. destruct e; try discriminate Hc.
  apply andb_prop in Hc as [Hle Hc]. apply Nat.leb_le in Hle.
  destruct (nth_error reads (n0 - nz)) as [[[a' n'] sx']|] eqn:Hn; [|discriminate Hc].
  apply andb_prop in Hc as [Hc Hsx]. apply andb_prop in Hc as [Ha Hnn].
  apply saddr_eqb_eq in Ha. apply Nat.eqb_eq in Hnn. apply Bool.eqb_prop in Hsx. subst a' n' sx'.
  pose proof (HR _ _ _ _ Hn) as Hv. replace (nz + (n0 - nz))%nat with n0 in Hv by lia.
  cbn [sc_resid] in Hres. unfold rd_ok in Hres. cbn [sc_denot edenot]. unfold rdval in Hv. rewrite rdn_AS.
  destruct (rdn segs m (adenot E a) n) as [bs|]; [|congruence].
  exists bs. split; [reflexivity|]. symmetry. exact Hv.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tblfact : Type := (saddr * Z * Z * Z * Z * Z * option expr)%type.
(* [comment removed for export] *)

Lemma sa_eta_b : forall a : saddr, SA (a_base a) (a_off a) = a.
Proof. intros [b o]. reflexivity. Qed.
Lemma adenot_estart_b : forall E a, adenot E a = wa (estart E a).
Proof. reflexivity. Qed.

Definition tf_ok (E : env) (tf : tblfact) : Prop :=
  let '(base, size, stride, off, lo, hi, osh) := tf in
  match osh with
  | None =>
      forall i, (0 <= i)%Z -> (stride * i + off < size)%Z ->
        (lo <= bv_unsigned (rdval (wa (estart E base + stride * i + off)) 1 false) <= hi)%Z
  | Some sh =>
      forall i, (0 <= i < 2 ^ (64 - bv_unsigned (edenot E sh) mod 64))%Z ->
        (lo <= bv_unsigned (rdval (wa (estart E base + stride * i + off)) 1 false) <= hi)%Z
  end.

Fixpoint lin_mult (s : Z) (ts : list (Z * expr)) : bool :=
  match ts with [] => true | (k, _) :: r => Z.eqb (k mod s) 0 && lin_mult s r end.

Definition tbl_match (kn0 : list kentry) (tf : tblfact) (a : saddr) : bool :=
  let '(base, size, stride, off, lo, hi, osh) := tf in
  let la := lin_of (a_base a) in let lb := lin_of (a_base base) in
  match osh with
  | None =>
      Z.ltb 0 stride && Z.eqb (2^64 mod stride) 0 && Z.leb 0 off && Z.leb off size && Z.ltb size (2^64) &&
      xinside kn0 (a_base a) (a_off a) (ELit 1) (a_base base) (a_off base + off) (ELit (size - off)) &&
      (lin_mult stride (lsub_e (snd la) (snd lb)) && Z.eqb ((fst la + a_off a - fst lb - a_off base - off) mod stride) 0)
  | Some sh =>
      match lsub_e (snd la) (snd lb) with
      | [(k, EAlu ALU_SRL x s')] => Z.eqb k stride && expr_eqb s' sh && Z.eqb (fst la + a_off a - fst lb - a_off base) off
      | _ => false
      end
  end.

Lemma lin_mult_sound : forall E s ts, (0 < s)%Z -> lin_mult s ts = true -> (tden E ts mod s = 0)%Z.
Proof.
  intros E s ts Hs. induction ts as [|[k e] r IH]; cbn [lin_mult tden]; intro H; [apply Z.mod_0_l; lia|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. specialize (IH H2).
  rewrite Z.add_mod, Z.mul_mod, H1, IH by lia. cbn. rewrite Z.mod_0_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tbl_match_sound : forall E kn0 tf a, know_ok segs E m kn0 -> tf_ok E tf -> tbl_match kn0 tf a = true ->
  let '(_, _, _, _, lo, hi, _) := tf in
  (lo <= bv_unsigned (rdval (adenot E a) 1 false) <= hi)%Z.
Proof.
  intros E kn0 [[[[[[base size] stride] off] lo] hi] osh] a HK HT H. unfold tbl_match in H. cbv zeta in H.
  destruct (lin_of_sound E (a_base a)) as [qa Qa]. destruct (lin_of_sound E (a_base base)) as [qb Qb].
  unfold lden, uE in Qa, Qb.
  pose proof (lsub_e_sound E (snd (lin_of (a_base a))) (snd (lin_of (a_base base)))) as LS.
  rewrite adenot_estart_b.
  destruct osh as [sh|]; cbn [tf_ok] in HT.
  - (* [comment removed for export] *)
    destruct (lsub_e (snd (lin_of (a_base a))) (snd (lin_of (a_base base)))) as [|[k e] [|? ?]]; try discriminate H;
      [| exfalso; destruct e as [| |op ? ?| | | | |]; try discriminate H; destruct op; discriminate H].
    destruct e as [| |op x s'| | | | |]; try discriminate H. destruct op; try discriminate H.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.eqb_eq in H1, H3. apply expr_eqb_eq in H2. subst k s'.
    cbn [tden] in LS. unfold uE in LS. cbn [edenot] in LS. rewrite u_srl64 in LS.
    set (i := (bv_unsigned (edenot E x) / 2 ^ (bv_unsigned (edenot E sh) mod 64))%Z) in *.
    assert (S0 : (0 <= bv_unsigned (edenot E sh) mod 64 < 64)%Z) by (apply Z.mod_pos_bound; lia).
    assert (I0 : (0 <= i < 2 ^ (64 - bv_unsigned (edenot E sh) mod 64))%Z).
    { pose proof (u64_range (edenot E x)) as RX. unfold i.
      assert (P : (0 < 2 ^ (bv_unsigned (edenot E sh) mod 64))%Z) by (apply Z.pow_pos_nonneg; lia).
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [exact P|].
      rewrite <- Z.pow_add_r by lia. replace (bv_unsigned (edenot E sh) mod 64 + (64 - bv_unsigned (edenot E sh) mod 64))%Z with 64%Z by lia. lia. }
    assert (EA : wa (estart E a) = wa (estart E base + stride * i + off)).
    { unfold wa. apply eqm_Z_to_bv. exists (qb - qa)%Z. unfold estart. lia. }
    rewrite EA. exact (HT i I0).
  - (* [comment removed for export] *)
    apply andb_prop in H as [H HL]. apply andb_prop in HL as [HL1 HL2].
    repeat (apply andb_prop in H as [H ?]).
    repeat match goal with X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X | X : Z.leb _ _ = true |- _ => apply Z.leb_le in X
                      | X : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in X end.
    match goal with X : xinside _ _ _ _ _ _ _ = true |- _ => pose proof (xinside_sound segs E m kn0 _ _ _ _ _ _ HK X) as [I1 I2] end.
    rewrite !sa_eta_b in I1, I2.
    assert (EL1 : elenZ E (ELit 1) = 1%Z) by reflexivity.
    assert (ELS : elenZ E (ELit (size - off)) = (size - off)%Z).
    { unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. lia. }
    rewrite EL1, ELS in I2.
    assert (EB : estart E (SA (a_base base) (a_off base + off)) = (estart E base + off)%Z) by (unfold estart; cbn [a_base a_off]; lia).
    rewrite EB in I1, I2.
    pose proof (lin_mult_sound E stride _ ltac:(lia) HL1) as LM. rewrite LS in LM.
    set (D := (estart E a - estart E base)%Z).
    assert (DM : ((D - off) mod stride = 0)%Z).
    { assert (S64 : exists w, (2^64 = w * stride)%Z).
      { exists (2^64 / stride)%Z. match goal with X : (2^64 mod stride = 0)%Z |- _ => pose proof (Z.div_mod (2^64) stride ltac:(lia)) as DV; rewrite X in DV end. lia. }
      destruct S64 as [w W64].
      apply Z.mod_divide in LM; [|lia]. destruct LM as [u LMu].
      apply Z.mod_divide in HL2; [destruct HL2 as [v Xv]|lia].
      apply Z.mod_divide; [lia|]. exists (v + u + (qb - qa) * w)%Z. unfold D, estart. rewrite W64 in Qa, Qb. lia. }
    apply Z.mod_divide in DM; [|lia]. destruct DM as [i Hi].
    replace (estart E a) with (estart E base + stride * i + off)%Z by (unfold D in Hi; lia).
    apply HT; unfold D in *; nia.
Qed.

Definition rk_chk (kn0 : list kentry) (tfs : list tblfact) (nz : nat) (reads : list rdspec) (K : kentry) : bool :=
  match K with
  | KRange (EVar j) lo hi =>
      Nat.leb nz j &&
      match nth_error reads (j - nz) with
      | Some (a, n, false) =>
          (Z.eqb lo 0 && Nat.ltb n 8 && Z.eqb hi (2 ^ (8 * Z.of_nat n) - 1))
          || (Nat.eqb n 1 && existsb (fun tf => let '(_, _, _, _, l, h, _) := tf in Z.eqb lo l && Z.eqb hi h && tbl_match kn0 tf a) tfs)
      | _ => false
      end
  | _ => false
  end.

Lemma rdval_range : forall a n, (n < 8)%nat -> (0 <= bv_unsigned (rdval a n false) <= 2 ^ (8 * Z.of_nat n) - 1)%Z.
Proof.
  intros a n Hn. unfold rdval. destruct (rdn segs m a n) as [bs|] eqn:Hr.
  - pose proof (rdn_length _ _ _ _ _ Hr) as Hl. pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
    cbn [extz]. rewrite Z_to_bv_unsigned.
    assert (P : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
    rewrite bv_wrap_small by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia). lia.
  - change (bv_unsigned w0) with 0%Z. assert (0 < 2 ^ (8 * Z.of_nat n))%Z by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma rk_chk_ok : forall kn0 tfs nz reads E K, reads_ok nz reads E -> know_ok segs E m kn0 -> Forall (tf_ok E) tfs ->
  rk_chk kn0 tfs nz reads K = true -> kentry_ok segs E m K.
Proof.
  intros kn0 tfs nz reads E K HR HK HT Hc. destruct K; try discriminate Hc. cbn [rk_chk] in Hc.
  destruct e; try discriminate Hc.
  apply andb_prop in Hc as [Hle Hrd]. apply Nat.leb_le in Hle.
  destruct (nth_error reads (n - nz)) as [[[a' n'] [|]]|] eqn:Hn; try discriminate Hrd.
  pose proof (HR _ _ _ _ Hn) as Hv. replace (nz + (n - nz))%nat with n in Hv by lia.
  cbn [kentry_ok edenot]. rewrite Hv.
  apply orb_prop in Hrd as [Hrd|Hrd].
  - apply andb_prop in Hrd as [Hrd Hhi]. apply andb_prop in Hrd as [Hlo Hn8].
    apply Z.eqb_eq in Hlo. apply Nat.ltb_lt in Hn8. apply Z.eqb_eq in Hhi. subst lo hi. apply rdval_range. exact Hn8.
  - apply andb_prop in Hrd as [Hn1 Hex]. apply Nat.eqb_eq in Hn1. subst n'.
    apply existsb_exists in Hex as ([[[[[[base size] stride] off] l] h] osh] & Hin & Hm).
    apply andb_prop in Hm as [Hm Hmt]. apply andb_prop in Hm as [El Eh]. apply Z.eqb_eq in El, Eh. subst l h.
    rewrite Forall_forall in HT. pose proof (HT _ Hin) as Htf.
    exact (tbl_match_sound E kn0 _ a' HK Htf Hmt).
Qed.

End Vals.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kx_regs (E : env) (sr : list expr) : bvmap 5 word := mkRf (fun n => edenot E (nth n sr (ELit 0))).

Lemma regs_ok_full_eq : forall E sr R, regs_ok E sr R -> rfull R -> R = kx_regs E sr.
Proof.
  intros E sr R Hr Hfull.
  assert (A : forall k, (1 <= k < 32)%nat -> reg_get R (regn k) = edenot E (nth k sr (ELit 0))).
  { intros k Hk. destruct k as [|k]; [lia|].
    let rec go i :=
      lazymatch i with
      | 32%nat => exfalso; lia
      | _ => destruct k as [|k]; [exact (Hr (regn i)) | go (S i)]
      end in go 1%nat. }
  rewrite (rfull_canon R Hfull). unfold kx_regs, mkRf. rewrite !A by lia. reflexivity.
Qed.

Lemma nth_reg_init : forall zs E rz xs, atoms_ok zs E -> forallb (zwf (length zs)) rz = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  forall k, nth k xs w0 = edenot E (nth k (map zx rz) (ELit 0)).
Proof.
  intros zs E rz xs HA HW H. revert HW. induction H as [|e x rz xs Hx _ IH]; intros HW k.
  - destruct k; reflexivity.
  - cbn [forallb] in HW. apply andb_prop in HW as [W1 W2]. destruct k as [|k]; cbn [nth map].
    + rewrite (zx_sound zs E e HA W1). exact Hx.
    + apply IH. exact W2.
Qed.

Lemma regs_ok_init : forall zs E rz xs, atoms_ok zs E -> forallb (zwf (length zs)) rz = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  regs_ok E (ELit 0 :: map zx rz) (mkRl xs).
Proof.
  intros zs E rz xs HA HW H r. pose proof (nth_reg_init zs E rz xs HA HW H) as N.
  destruct (reg_cases r) as (n & Hn & ->).
  destruct n as [|k]; [reflexivity|].
  let rec go i :=
    lazymatch i with
    | 31%nat => exfalso; lia
    | _ => destruct k as [|k]; [exact (N i) | go (S i)]
    end in go 0%nat.
Qed.

Section BridgeThm.
Variable segs : list Segment.
Variables (F : bvmap 5 word) (fc : bv 32).

Theorem kx_core : forall RNG fuel stops dirs zs rz xs kn0 tfs rk pc m rom ss' scs scr' accs reads,
  kx_exec segs fuel true stops (SCR dirs [] []) (SS pc (ELit 0 :: map zx rz) [] (kn0 ++ rk) (length zs)) [] [] = (ss', scs, scr', accs) ->
  forallb (zwf (length zs)) rz = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  rds_chk (length zs) 0 reads = true ->
  forallb (sc_rd_chk (length zs) reads) scs = true ->
  forallb (rk_chk kn0 tfs (length zs) reads) rk = true ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m kn0) ->
  (forall E, kx_env_ok segs m zs reads E -> Forall (tf_ok segs m E) tfs) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (kn0 ++ rk) -> Forall (sc_resid segs m E) scs) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (kn0 ++ rk) -> Forall (accP E RNG) accs) ->
  exists E, kx_env_ok segs m zs reads E /\ know_ok segs E m (kn0 ++ rk) /\ log_flat E (s_log ss') /\
    (mem_inv segs m -> mem_inv segs (mem_denot E m (s_log ss'))) /\
    mstepsF segs RNG (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom)
                     (MS (kx_regs E (s_regs ss')) F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E m (s_log ss')) rom).
Proof.
  intros RNG fuel stops dirs zs rz xs kn0 tfs rk pc m rom ss' scs scr' accs reads Hex HW Hregs Hrds Hscr Hrk Hkn0 Htf Hscs Haccs.
  pose proof (kx_env_exists segs m zs reads Hrds) as HE.
  set (E := kx_env (kx_vals segs m (map (Z_to_bv 64) zs) reads)) in *.
  assert (Hkn : know_ok segs E m (kn0 ++ rk)).
  { apply Forall_app. split; [exact (Hkn0 E HE)|].
    apply Forall_forall. intros K HK. rewrite forallb_forall in Hrk.
    exact (rk_chk_ok segs m kn0 tfs _ reads E K (proj2 HE) (Hkn0 E HE) (Htf E HE) (Hrk K HK)). }
  assert (Hsc : scs_denot segs m E scs).
  { specialize (Hscs E HE Hkn). rewrite forallb_forall in Hscr. unfold scs_denot.
    rewrite Forall_forall in *. intros sc Hin. exact (kx_readbase segs m _ reads E sc (proj2 HE) (Hscr sc Hin) (Hscs sc Hin)). }
  destruct (kx_exec_sound segs F fc _ _ _ _ _ _ _ E m rom RNG _ _ _ _ Hex eq_refl) as (_ & _ & _ & Hrun).
  destruct (Hrun (mkRl xs) Hsc (Haccs E HE Hkn) (regs_ok_init zs E rz xs (proj1 HE) HW Hregs) (rfull_mkRl xs) I Hkn)
    as (regs' & Hsteps & Hr' & Hfull' & Hlf' & _ & Hmi').
  exists E. split; [exact HE|]. split; [exact Hkn|]. split; [exact Hlf'|]. split; [exact Hmi'|].
  rewrite <- (regs_ok_full_eq E _ regs' Hr' Hfull'). exact Hsteps.
Qed.

Theorem kx_run_evtF : forall RNG (Q : machine_state -> Prop) fuel stops dirs zs rz xs kn0 tfs rk pc m rom ss' scs scr' accs reads,
  kx_exec segs fuel true stops (SCR dirs [] []) (SS pc (ELit 0 :: map zx rz) [] (kn0 ++ rk) (length zs)) [] [] = (ss', scs, scr', accs) ->
  forallb (zwf (length zs)) rz = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  rds_chk (length zs) 0 reads = true ->
  forallb (sc_rd_chk (length zs) reads) scs = true ->
  forallb (rk_chk kn0 tfs (length zs) reads) rk = true ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m kn0) ->
  (forall E, kx_env_ok segs m zs reads E -> Forall (tf_ok segs m E) tfs) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (kn0 ++ rk) -> Forall (sc_resid segs m E) scs) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (kn0 ++ rk) -> Forall (accP E RNG) accs) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (kn0 ++ rk) -> log_flat E (s_log ss') ->
     (mem_inv segs m -> mem_inv segs (mem_denot E m (s_log ss'))) ->
     evtF segs RNG Q (MS (kx_regs E (s_regs ss')) F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E m (s_log ss')) rom)) ->
  evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros RNG Q fuel stops dirs zs rz xs kn0 tfs rk pc m rom ss' scs scr' accs reads Hex HW Hregs Hrds Hscr Hrk Hkn0 Htf Hscs Haccs K.
  destruct (kx_core RNG fuel stops dirs zs rz xs kn0 tfs rk pc m rom ss' scs scr' accs reads Hex HW Hregs Hrds Hscr Hrk Hkn0 Htf Hscs Haccs)
    as (E & HE & Hkn & Hlf & Hmi & Hsteps).
  destruct (K E HE Hkn Hlf Hmi) as (ms' & Hs2 & HQ). exists ms'. split; [eapply mstepsF_trans; eassumption | exact HQ].
Qed.

Theorem kx_run_evt : forall (Q : machine_state -> Prop) fuel stops dirs zs rz xs kn0 tfs rk pc m rom ss' scs scr' accs reads,
  kx_exec segs fuel true stops (SCR dirs [] []) (SS pc (ELit 0 :: map zx rz) [] (kn0 ++ rk) (length zs)) [] [] = (ss', scs, scr', accs) ->
  forallb (zwf (length zs)) rz = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  rds_chk (length zs) 0 reads = true ->
  forallb (sc_rd_chk (length zs) reads) scs = true ->
  forallb (rk_chk kn0 tfs (length zs) reads) rk = true ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m kn0) ->
  (forall E, kx_env_ok segs m zs reads E -> Forall (tf_ok segs m E) tfs) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (kn0 ++ rk) -> Forall (sc_resid segs m E) scs) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (kn0 ++ rk) -> log_flat E (s_log ss') ->
     (mem_inv segs m -> mem_inv segs (mem_denot E m (s_log ss'))) ->
     evt segs Q (MS (kx_regs E (s_regs ss')) F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E m (s_log ss')) rom)) ->
  evt segs Q (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros Q fuel stops dirs zs rz xs kn0 tfs rk pc m rom ss' scs scr' accs reads Hex HW Hregs Hrds Hscr Hrk Hkn0 Htf Hscs K.
  destruct (kx_core (fun _ _ => True) fuel stops dirs zs rz xs kn0 tfs rk pc m rom ss' scs scr' accs reads Hex HW Hregs Hrds Hscr Hrk Hkn0 Htf Hscs)
    as (E & HE & Hkn & Hlf & Hmi & Hsteps).
  { intros E _ _. apply Forall_forall. intros an _. exact I. }
  destruct (K E HE Hkn Hlf Hmi) as (ms' & Hs2 & HQ). exists ms'.
  split; [eapply msteps_trans; [eapply mstepsF_msteps; exact Hsteps | exact Hs2] | exact HQ].
Qed.

End BridgeThm.
