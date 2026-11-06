(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GxSymRun3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SymExec.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2S.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vals_ev (vals : list word) : nat -> word :=
  fun n => nth n vals (Z_to_bv 64 0).

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.

Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KImg _ _ => true
  | KAlign e _ => expr_vars_lt b e
  | KRange e _ _ => expr_vars_lt b e
  | KWr a n => saddr_vars_lt b a && expr_vars_lt b n
  | KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
  | KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
  end.

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.


Definition env_agree (b : nat) (E E' : env) : Prop :=
  (forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.

Lemma edenot_agree : forall b E E' e,
  env_agree b E E' -> expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try reflexivity;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (rewrite IHe by assumption; reflexivity).
  - apply Nat.ltb_lt in H. apply Hv. exact H.
  - rewrite Hb. reflexivity.
Qed.

Lemma adenot_agree : forall b E E' a,
  env_agree b E E' -> saddr_vars_lt b a = true -> adenot E a = adenot E' a.
Proof.
  intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.

Lemma regs_ok_agree : forall b E E' sr regs,
  env_agree b E E' -> sr_vars_lt b sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
  intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
  unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
  { clear HR r. induction sr as [|e t IH]; intros i.
    - destruct i; reflexivity.
    - cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
      destruct i; [exact He | apply IH; exact Ht]. }
  apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.


Lemma flat_agree : forall b E E' a n,
  env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
  intros b E E' a n Ha H. unfold flat, estart.
  rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.


Lemma know_ok_agree : forall segs b E E' base kn,
  env_agree b E E' -> kn_vars_lt b kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
  intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
  - constructor.
  - apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
    constructor; [| apply IH; assumption].
    destruct Ha as [Hv Hb].
    destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2|a n fc|a n]; cbn [kentry_vars_lt kentry_ok] in *;
      [ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
              | rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
              | apply andb_prop in HK as [HK1 HK2]; unfold flat, estart, elenZ in *;
                rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK1), <- (edenot_agree b E E' wn (conj Hv Hb) HK2); exact Hk1
              | apply andb_prop in HK as [HK HK4]; apply andb_prop in HK as [HK HK3]; apply andb_prop in HK as [HK1 HK2];
                unfold estart, elenZ in *;
                rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1), <- (edenot_agree b E E' dn1 (conj Hv Hb) HK2),
                        <- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK3), <- (edenot_agree b E E' dn2 (conj Hv Hb) HK4); exact Hk1
              | | ].
    + apply andb_prop in HK as [H1 H2].
      rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
      destruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
      apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + exact Hk1.
    + (* [comment removed for export] *)
      apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + (* [comment removed for export] *)
      apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma st_ok_entry : forall E base rom pc sr kn nx regs fx,
  regs_ok E sr regs -> know_ok segs E base kn -> fx_ok fx ->
  st_ok segs E base rom (SS pc sr [] kn nx) (@mkst fx regs (Z_to_bv 64 pc) base rom).
Proof.
  intros E base rom pc sr kn nx regs fx HR HK HF. exists regs, fx. cbn [s_pc s_log s_regs s_know mem_denot].
  split; [reflexivity|]. split; [exact HF|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

Theorem run_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs fx,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> know_ok segs E base kn -> fx_ok fx ->
  scs_denot segs base E scs ->
  exists R fx', fx_ok fx'
         /\ regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (@mkst fx regs (Z_to_bv 64 pc) base rom)
                        (@mkst fx' R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs fx Hex HR HK HF Hsc.
  eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

(* [comment removed for export] *)
Lemma eagree_env_agree : forall b E E', eagree b E E' <-> env_agree b E E'.
Proof. intros b E E'. unfold eagree, env_agree. tauto. Qed.

(* [comment removed for export] *)
Lemma st_okX_entry : forall E base rom pc sr kn nx regs fx,
  regs_ok E sr regs -> know_ok segs E base kn -> fx_ok fx ->
  sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
  forall E', eagree nx E E' -> st_ok segs E' base rom (SS pc sr [] kn nx) (@mkst fx regs (Z_to_bv 64 pc) base rom).
Proof.
  intros E base rom pc sr kn nx regs fx HR HK HF Hsr Hkn E' Ha. apply eagree_env_agree in Ha.
  apply st_ok_entry.
  - eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR].
  - eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
  - exact HF.
Qed.

(* [comment removed for export] *)
Theorem runTX_sound : forall t K fuel stops pc sr kn nx E base rom regs fx,
  itab_sound segs t ->
  regs_ok E sr regs -> know_ok segs E base kn -> fx_ok fx ->
  sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
  let ss' := sym_execTX segs t K fuel true stops (SS pc sr [] kn nx) in
  exists E' R fx', env_agree nx E E'
    /\ (nx <= s_next ss')%nat
    /\ fx_ok fx'
    /\ regs_ok E' (s_regs ss') R
    /\ log_flat E' (s_log ss')
    /\ know_ok segs E' base (s_know ss')
    /\ msteps segs (@mkst fx regs (Z_to_bv 64 pc) base rom)
                   (@mkst fx' R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
    /\ (forall E'', env_agree (s_next ss') E' E'' ->
          st_ok segs E'' base rom ss' (@mkst fx' R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof.
  intros t K fuel stops pc sr kn nx E base rom regs fx Ht HR HK HF Hsr Hkn.
  destruct (sym_execTX_ex segs t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht
              (st_okX_entry E base rom pc sr kn nx regs fx HR HK HF Hsr Hkn)) as (E' & R & fx' & Ha & Hle & HF' & HR' & Hlf & HK' & Hms & HALL).
  exists E', R, fx'. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|]. split; [exact HF'|].
  split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hms|].
  intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.

(* [comment removed for export] *)
Theorem runTXF_sound : forall t K fuel stops pc sr kn nx E M rom R fx,
  itab_sound segs t ->
  regs_ok E sr R -> know_ok segs E M kn ->
  sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
  fx_ok fx ->
  let ss' := sym_execTX segs t K fuel true stops (SS pc sr [] kn nx) in
  exists E' R' fx', env_agree nx E E'
    /\ (nx <= s_next ss')%nat
    /\ regs_ok E' (s_regs ss') R'
    /\ log_flat E' (s_log ss')
    /\ know_ok segs E' M (s_know ss')
    /\ fx_ok fx'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 pc) M rom)
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' M (s_log ss')) rom).
Proof.
  intros t K fuel stops pc sr kn nx E M rom R fx Ht HR HK Hsr Hkn HF.
  destruct (runTX_sound t K fuel stops pc sr kn nx E M rom R fx Ht HR HK HF Hsr Hkn)
    as (E' & R' & fx' & Ha & Hle & HF' & HR' & Hlf & HK' & Hms & _).
  exists E', R', fx'. repeat (split; [assumption|]). exact Hms.
Qed.



(* [comment removed for export] *)
Lemma regs_ok_set : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> rd <> 0%bv -> edenot E e = v ->
  regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v).
Proof.
  intros E sr R rd v e HR Hrd He.
  pose proof (regs_ok_upd E sr R rd v e HR He) as H.
  assert (Hb : bv_eqb rd 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
  rewrite Hb in H. exact H.
Qed.

End Run.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk_ok (segs : list Segment) (mem : word -> option byte) (sp : word) (K : Z) : Prop :=
  forall (a : word) (n : nat),
    (bv_unsigned sp - K <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp)%Z ->
    store_ok segs mem a n = true.

Lemma stk_ok_vaddi : forall segs mem sp K off n,
  stk_ok segs mem sp K -> (K <= bv_unsigned sp)%Z ->
  (- K <= off)%Z -> (off + Z.of_nat n <= 0)%Z ->
  store_ok segs mem (v_addi sp off) n = true.
Proof.
  intros segs mem sp K off n Hs HK H1 H2. pose proof (u64_range sp).
  apply Hs; unfold v_addi; rewrite u_small by lia; lia.
Qed.

Lemma stk_ok_lit : forall segs mem sp K z n,
  stk_ok segs mem sp K ->
  (bv_unsigned sp - K <= z)%Z -> (z + Z.of_nat n <= bv_unsigned sp)%Z -> (0 <= z)%Z ->
  store_ok segs mem (Z_to_bv 64 z) n = true.
Proof.
  intros segs mem sp K z n Hs H1 H2 H3. pose proof (u64_range sp).
  apply Hs; rewrite u_small by lia; lia.
Qed.




















(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac split_scs :=
  lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| split_scs]
  end.

(* [comment removed for export] *)
Ltac ground_mod :=
  repeat match goal with
  | |- context [ (?a mod ?b)%Z ] =>
      lazymatch a with
      | context [bv_unsigned _] => fail
      | _ => lazymatch b with
             | context [bv_unsigned _] => fail
             | _ => let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
             end
      end
  end.

Ltac sc_unfold :=
  unfold sc_denot, flat, estart, elenZ, adenot;
  cbn [a_base a_off edenot ev eb vals_ev nth];
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod.

(* [comment removed for export] *)
Ltac lit_u :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned _] => fail
      | _ => rewrite (u_small z) by (cbn; lia)
      end
  end.

(* [comment removed for export] *)
Ltac sc_store :=
  match goal with
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (v_addi _ _) _ = true =>
      apply (stk_ok_vaddi _ _ _ _ _ _ Hs); lia
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (Z_to_bv 64 _) _ = true =>
      apply (stk_ok_lit _ _ _ _ _ _ Hs); lia
  end.

Ltac sc_auto extra :=
  sc_unfold;
  first [ lia
        | sc_store
        | extra
        | match goal with |- _ /\ _ => repeat split; first [lia | sc_store | extra] end
        | idtac ].

(* [comment removed for export] *)
Ltac sym_run_tac segs fuel stops scr nx HR HK R' HR' Hlf Hms extra :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok _ _ ?base ?kn =>
      lazymatch goal with
      | |- context [@mkst ?fx regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; sc_auto extra
              | let fx' := fresh "fx'" in let HF' := fresh "HF'" in
                edestruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs fx
                          (eq_refl _) HR HK ltac:(assumption) Hsc) as (R' & fx' & HF' & HR' & Hlf & Hms);
                clear Hsc ]
          end
      end
    end
  end.
End GxSymRun3.
Require Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GxPlanSound.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
(* [comment removed for export] *)
#[local] Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.
#[local] Existing Instance fx0.  (* [comment removed for export] *)

Module APS.
Import AX2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AX2S.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).

Definition pagedown (z : Z) : Z := z / 4096 * 4096.
Definition pageup (z : Z) : Z := (z + 4095) / 4096 * 4096.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).




Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition in_ivs (z : Z) (l : list (word * word)) : bool :=
  existsb (fun iv => (bv_unsigned (fst iv) <=? z) && (z <? bv_unsigned (fst iv) + bv_unsigned (snd iv)))%bool l.

Definition in_hull (A : atable) (z : Z) : bool := ((img_lo A <=? z) && (z <? img_hi A))%bool.

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Fixpoint sum_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + sum_sizes r end.

Definition cfg_of (SEGS : list Segment) (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom SEGS)) model.

Section Sound.
Variable SEGS : list Segment.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
(* [comment removed for export] *)
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable XC : xhookB.   (* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_ok : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_ok : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Definition shadow_ok : Prop := 0 <= shadow_off A <= 2 ^ 47.
Hypothesis RES_len : res_len_ok.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok.
Hypothesis SHADOW_ok : shadow_ok.

(* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

(* [comment removed for export] *)
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Variable KC : nat.

#[local] Notation CHECK := (AP.check SEGS IT A nx0 LIMIT XN XE XB XC HS KC).

#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Definition piece_den (E : env) (p : spiece) : list byte :=
  match p with SPLit bs => map (Z_to_bv 8) bs | SPBlob k => eb E k end.
Definition Wp (E : env) (fd : Z) (ps : list spiece) : list event :=
  map (WriteEv (Z_to_bv 64 fd)) (flat_map (piece_den E) ps).

(* [comment removed for export] *)
Fixpoint sd (D : TSet) (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmitP fd ps s' => t_emit (Wp E fd ps) (sd D E fs s')
  | SAlt2 a b => t_alt2 (sd D E fs a) (sd D E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd D E fs s1 else sd D E fs s2
  | SHole h => HOLES h E fs
  | SNext => D
  end.

(* [comment removed for export] *)
Definition sh_lo (E : env) (p : expr * expr) : Z := shadow_off A + uE E (fst p) / 8.
Definition sh_hi (E : env) (p : expr * expr) : Z := shadow_off A + (uE E (fst p) + uE E (snd p)) / 8.

(* [comment removed for export] *)
Definition allow1 (E : env) (p : expr * expr) : list (Z * Z) :=
  [(pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))); (pagedown (sh_lo E p), pageup (sh_hi E p))].
Definition allowA (E : env) (cs : acs) : list (Z * Z) := flat_map (allow1 E) (a_vis cs ++ a_ghost cs).

Definition amap_den (E : env) (m : amap) : word * word := (edenot E (am_base m), edenot E (am_len m)).

(* [comment removed for export] *)
Definition in_vis (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs).
Definition in_sh (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool (a_vis cs).
Definition in_allow (E : env) (cs : acs) (z : Z) : bool := (in_vis E cs z || in_sh E cs z)%bool.

(* [comment removed for export] *)
Definition in_ghost (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_ghost cs).

(* [comment removed for export] *)
Definition vis (E : env) (cs : acs) (model : Model) (a : word) : bool :=
  let h := m_vmmaps model in
  let z := bv_unsigned a in
  (in_hull A z
   || (CEIL <=? z)
   || (in_ivs z (vm_maps h) && negb (in_ivs z (vm_noaccess h))
       && (negb (page_in_ranges (page_base a) (m_vm_lazy model)) || in_allow E cs z)))%bool.

Definition hid (E : env) (cs : acs) (model : Model) (a : word) : bool :=
  (argH E a || negb (vis E cs model a))%bool.

(* [comment removed for export] *)
Definition Mr (E : env) (cs : acs) (model : Model) (FULL : word -> option byte) : word -> option byte :=
  mrestrict (hid E cs model) FULL.

Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition CH : nat := Z.to_nat 65536.
Definition chunk (j : nat) (c : list byte) : list byte := firstn CH (skipn (CH * j) c).
Definition flen (c : list byte) : Z := Z.min (Z.of_nat (length c)) (2 ^ 26).
Definition fds3 (e : FdEntry) : list (word * FdEntry) := (Z_to_bv 64 3, e) :: fds_std.
Definition fds_ok (E : env) (f : afd) (model : Model) : Prop :=
  match f with
  | AP.FdStd => m_fds model = fds_std
  | AP.FdDir => m_fds model = fds3 State.FdDir
  | AP.FdFile k len off => exists p c,
        m_fds model = fds3 (State.FdFile p (edenot E off)) /\ fs_lookup (m_fs model) p = Some c
     /\ uE E len = flen c /\ uE E off <= uE E len
     /\ (forall j, (65536 * Z.of_nat j < 2 ^ 26)%Z -> eb E (k + j)%nat = chunk j c)
  end.

(* [comment removed for export] *)
Fixpoint maps_match (E : env) (ms : list amap) (l : list (word * word)) : Prop :=
  match ms with
  | [] => l = []
  | m :: ms' =>
      if is_fog m       (* [comment removed for export] *)
      then maps_match E ms' l
           \/ exists iv l', l = iv :: l' /\ bv_unsigned (snd iv) <= uE E (am_len m) /\ maps_match E ms' l'
      else exists l', l = amap_den E m :: l' /\ maps_match E ms' l'
  end.

(* [comment removed for export] *)
Definition hole_ok (E : env) (ylo : Z) (l : list (word * word)) (m : amap) : Prop :=
  is_hole m = true ->
  (forall iv, In iv l -> bv_unsigned (fst iv) + bv_unsigned (snd iv) <= uE E (am_base m)
                         \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (fst iv))
  /\ (uE E (am_base m) + uE E (am_len m) <= KHI \/ ylo <= uE E (am_base m)).
Lemma holes_mono : forall E y y' l ms,
  Forall (hole_ok E y l) ms -> y' <= y -> Forall (hole_ok E y' l) ms.
Proof.
  intros E y y' l ms H Hy. apply Forall_forall. intros m Hm Hh.
  destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [exact H1 | lia].
Qed.



Record cs_ok (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) : Prop := CS_OK {
  (* [comment removed for export] *)
  co_regs  : regs_ok E (s_regs (a_ss cs)) R;
  co_log   : s_log (a_ss cs) = [];
  co_know  : know_ok SEGS E (Mr E cs model FULL) (kn cs);
  (* [comment removed for export] *)
  co_halt  : m_halted model = None;
  co_fds   : fds_ok E (a_fd cs) model;
  co_fs    : m_fs model = FS0;
  co_tid   : a_tidset cs = false -> m_tid model = None;
  co_res   : vm_reserved (m_vmmaps model) = segments_reserved SEGS;
  co_limit : vm_limit (m_vmmaps model) = LIMIT;
  (* [comment removed for export] *)
  co_maps  : maps_match E (a_maps cs) (vm_maps (m_vmmaps model));
  co_holes : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (a_maps cs);   (* [comment removed for export] *)
  co_seps  : seps (vm_maps (m_vmmaps model));
  co_wf    : model_ivs_wf model;
  co_bounds : Forall (fun iv => 0 < bv_unsigned (snd iv)
                                /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                /\ img_hi A <= bv_unsigned (fst iv)
                                /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL) (vm_maps (m_vmmaps model));
  co_lazyb : Forall (fun iv => img_hi A <= bv_unsigned (fst iv)
                               /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL) (m_vm_lazy model);
  co_nasub : forall z, in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true;
  co_none  : Forall (fun m => am_kind m = KNONE \/ am_kind m = KNONELAZY ->
               In (amap_den E m) (vm_noaccess (m_vmmaps model))) (a_maps cs);
  co_kinds : Forall (fun m => am_kind m = KRWLAZY ->
               forall a : word, bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
                 in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
                 /\ page_in_ranges (page_base a) (m_vm_lazy model) = true) (a_maps cs);
  co_totsz : sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs;
  co_split : exists Y, a_ylo cs <= Y /\ Y mod 4096 = 0 /\ Y <= bv_unsigned (vm_mmap_base (m_vmmaps model))
                       /\ ledger_split (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) kHighMemBeg Y;
  co_brk   : vm_brk (m_vmmaps model) = edenot E (a_brk cs);
  co_sbrk  : bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model));
  (* [comment removed for export] *)
  co_eager : eager_used model <= a_eager cs;
  co_abytes : A_bytes (allowA E cs) <= a_abytes cs;
  co_minv  : MInv (allowA E cs) model;
  (* [comment removed for export] *)
  co_zero  : forall a : word, hid E cs model a = true ->
               in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
               in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
               page_in_ranges (page_base a) (m_vm_lazy model) = true ->
               in_ghost E cs (bv_unsigned a) = false ->
               FULL a = Some (Z_to_bv 8 0);
  co_sinv  : SINV E FULL
}.







(* [comment removed for export] *)
Lemma vis_same : forall E cs model model',
  same_but_materialized model model' -> vis E cs model' = vis E cs model.
Proof.
  intros E cs model model' Hs. pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  apply functional_extensionality. intros a. unfold vis.
  replace (m_vmmaps model') with (m_vmmaps model) by (symmetry; apply Hfr).
  replace (m_vm_lazy model') with (m_vm_lazy model) by (symmetry; apply Hfr). reflexivity.
Qed.

Lemma hid_same : forall E cs model model',
  same_but_materialized model model' -> hid E cs model' = hid E cs model.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_same _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma vis_ext : forall E cs cs' model,
  a_vis cs' = a_vis cs -> vis E cs' model = vis E cs model.
Proof. intros E cs cs' model Ha. apply functional_extensionality. intros a. unfold vis, in_allow, in_vis, in_sh. rewrite Ha. reflexivity. Qed.
Lemma hid_ext : forall E cs cs' model,
  a_vis cs' = a_vis cs -> hid E cs' model = hid E cs model.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_ext _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma cs_ok_frame : forall E cs R FULL model ss' R' FULL' model',
  cs_ok E cs R FULL model ->
  same_but_materialized model model' ->
  MInv (allowA E cs) model' ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
  know_ok SEGS E (Mr E cs model FULL') (s_know ss') ->
  (forall a, hid E cs model a = true -> FULL' a = FULL a) ->
  cs_ok E (with_ss cs ss') R' FULL' model'.
Proof.
  intros E cs R FULL model ss' R' FULL' model' HC Hs Hinv HR HL HK Hhid.
  pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  assert (Evm : m_vmmaps model' = m_vmmaps model) by apply Hfr.
  assert (Elz : m_vm_lazy model' = m_vm_lazy model) by apply Hfr.
  destruct HC. constructor; cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn];
    rewrite ?Evm, ?Elz; try assumption.
  - unfold Mr. rewrite (hid_same _ _ _ _ Hs). exact HK.
  - replace (m_halted model') with (m_halted model) by (symmetry; apply Hfr). assumption.
  - unfold fds_ok in *. replace (m_fds model') with (m_fds model) by (symmetry; apply Hfr).
    replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - intros Ht. replace (m_tid model') with (m_tid model) by (symmetry; apply Hfr). auto.
  - unfold model_ivs_wf in *. rewrite Evm, Elz. assumption.
  - replace (eager_used model') with (eager_used model) by (symmetry; apply Hfr). assumption.
  - intros a Hh. rewrite (hid_same _ _ _ _ Hs) in Hh. rewrite (Hhid a Hh). auto.
  - eapply SINV_frame; [|eassumption]. intros a Ha. apply Hhid. unfold hid. rewrite Ha. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma know_ok_filter : forall E M f k, know_ok SEGS E M k -> know_ok SEGS E M (List.filter f k).
Proof.
  intros E M f k HK. unfold know_ok in *. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin _]. exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

Lemma cs_ok_set_kn : forall E cs R FULL model k',
  cs_ok E cs R FULL model -> know_ok SEGS E (Mr E cs model FULL) k' ->
  cs_ok E (set_kn cs k') R FULL model.
Proof.
  intros E cs R FULL model k' HC HK.
  destruct HC; constructor; cbn [set_kn with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
    try assumption; reflexivity.
Qed.

Lemma cs_gc_ok : forall gb E cs R FULL model, cs_ok E cs R FULL model -> cs_ok E (cs_gc gb cs) R FULL model.
Proof.
  intros gb E cs R FULL model HC. unfold cs_gc. destruct (split_lit (reg cs 2)) as [spb spk].
  apply cs_ok_set_kn; [exact HC|]. apply know_ok_filter. exact (co_know _ _ _ _ _ HC).
Qed.

Lemma mk_itab_ranges_acc_sound : forall rs t, itab_sound SEGS t -> itab_sound SEGS (mk_itab_ranges_acc SEGS rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Ht; cbn [mk_itab_ranges_acc]; [exact Ht|].
  apply IH. apply mk_itab_fuel_sound. exact Ht.
Qed.
Lemma mk_itab_ranges_sound : forall rs, itab_sound SEGS (mk_itab_ranges SEGS rs).
Proof.
  intros rs. unfold mk_itab_ranges. apply mk_itab_ranges_acc_sound.
  intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.

Lemma pc_set_kn : forall cs k, pc (set_kn cs k) = pc cs.
Proof. reflexivity. Qed.
Lemma pc_cs_gc : forall gb cs, pc (cs_gc gb cs) = pc cs.
Proof. intros gb cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.

Lemma drop_ixs_incl : forall ixs i k K, In K (drop_ixs ixs i k) -> In K k.
Proof.
  intros ixs i k. revert i. induction k as [|K' r IH]; intros i K Hin; cbn [drop_ixs] in Hin.
  - exact Hin.
  - destruct (existsb (Nat.eqb i) ixs).
    + right. eapply IH. exact Hin.
    + destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; exact Hin].
Qed.

Lemma forget_sound : forall E cs R FULL model ixs,
  cs_ok E cs R FULL model -> cs_ok E (set_kn cs (drop_ixs ixs 0 (kn cs))) R FULL model.
Proof.
  intros E cs R FULL model ixs HC. apply cs_ok_set_kn; [exact HC|].
  unfold know_ok. apply Forall_forall. intros K Hin. apply drop_ixs_incl in Hin.
  exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ HC) K Hin).
Qed.

(* [comment removed for export] *)
Definition kfoot (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a l => Some (estart E a, elenZ E l)
  | KBlob a l _ => Some (estart E a, elenZ E l)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | KWr a n => Some (estart E a, elenZ E n)
  | KFill a l _ => Some (estart E a, elenZ E l)
  | KUnk a l => Some (estart E a, elenZ E l)
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => None
  end.

Definition kfoot_apart (E : env) (K : kentry) (lo n : Z) : Prop :=
  match kfoot E K with
  | None => True
  | Some (s, l) => (s + l <= lo \/ lo + n <= s)%Z
  end.

Lemma kentry_keep_sem : forall E M M' K lo n,
  kentry_ok SEGS E M K -> kfoot_apart E K lo n ->
  (forall x : word, (bv_unsigned x < lo \/ lo + n <= bv_unsigned x)%Z -> M' x = M x) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' K lo n HK Hap Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (bv_unsigned a + Z.of_nat k <= lo \/ lo + n <= bv_unsigned a)%Z ->
     rdn SEGS M' a k = rdn SEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hout. lia. }
  unfold kfoot_apart, kfoot in Hap.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok] in *;
    try exact HK.
  7: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  6: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia | rewrite (flat_u E _ _ Hfl); lia].
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    rewrite Hout; [apply HC; lia|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.

Lemma elenZ_lit : forall E z, (0 <= z < 2 ^ 64)%Z -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

Lemma kentry_apart_b_sem : forall E M allkn K ub uk un,
  know_ok SEGS E M allkn -> kentry_apart_b allkn ub uk un K = true ->
  kfoot_apart E K (estart E (SA ub uk)) (elenZ E un).
Proof.
  intros E M allkn K ub uk un Hall Hb. unfold kfoot_apart, kfoot.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_apart_b] in Hb;
    try exact I; try discriminate.
  7: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  6: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb) as Hd.
    rewrite (elenZ_lit E (Z.of_nat w)) in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [H0 Hl].
    apply Z.leb_le in H0. apply Z.leb_le in Hl. apply Z.ltb_lt in Hlt. unfold two64 in Hlt.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hap) as Hd.
    rewrite (elenZ_lit E (ihi - ilo)) in Hd by lia.
    unfold estart in Hd at 2 3. cbn [a_base a_off edenot] in Hd.
    rewrite !u64_lit in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
Qed.

Lemma kentry_apart_keep : forall E M M' allkn K (ub : expr) uk un,
  know_ok SEGS E M allkn -> kentry_ok SEGS E M K ->
  kentry_apart_b allkn ub uk un K = true ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' allkn K ub uk un Hall HK Hb Hout.
  eapply kentry_keep_sem; [exact HK | eapply kentry_apart_b_sem; [exact Hall | exact Hb] | exact Hout].
Qed.


(* [comment removed for export] *)
Lemma kentry_apart_bp_eq : forall allkn ub uk un K,
  kentry_apart_bp allkn (mk_sprep allkn ub uk un) ub uk un K = kentry_apart_b allkn ub uk un K.
Proof.
  intros allkn ub uk un K. destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kentry_apart_bp kentry_apart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.

Lemma havoc1p_eq : forall k ub uk un K,
  havoc1p k (mk_sprep k ub uk un) ub uk un K = havoc1 k ub uk un K.
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq. reflexivity. Qed.


(* [comment removed for export] *)
Lemma know_ok_havoc : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok SEGS E M' (kn_havoc k b o n).
Proof.
  intros E M M' k b o n HK Hout Hg. unfold kn_havoc, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite havoc1p_eq. unfold havoc1.
  destruct (kwr_b K ||| kentry_apart_b k b o n K)%bool eqn:Hf.
  - apply Forall_one. apply orb_prop in Hf as [Hw|Ha].
    + destruct K as [| | | | | |[wb wk] wn| | |[qb qk] qn]; try discriminate.
      * destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
        intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
      * (* [comment removed for export] *)
        destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
        intros i Hi. apply Hg. apply Hs. exact Hi.
    + eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | | | |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pw_kind (mk : saddr -> expr -> kentry) (P : (word -> option byte) -> word -> Prop) : Prop :=
  forall E M a n,
    kentry_ok SEGS E M (mk a n)
    <-> (flat E a (elenZ E n) /\ forall i, (0 <= i < elenZ E n)%Z -> P M (Z_to_bv 64 (estart E a + i))).


Lemma pw_kind_wr : pw_kind KWr (fun M x => wview SEGS M x <> None).
Proof.
  intros E M a n. cbn [kentry_ok]. split; intros [Hfl H]; split; try exact Hfl.
  - intros i Hi. pose proof (H i 1%nat ltac:(lia) ltac:(cbn; lia)) as S1. cbn [store_ok] in S1.
    destruct (wview SEGS M (Z_to_bv 64 (estart E a + i))); [discriminate | discriminate].
  - intros d m Hd Hdm. pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
    assert (Hm : 1 <= Z.of_nat m) by (subst m; rewrite Nat2Z.inj_succ; lia).
    assert (Hu : bv_unsigned (Z_to_bv 64 (estart E a + d)) = estart E a + d) by (apply u_small; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. replace x with (Z_to_bv 64 (estart E a + (bv_unsigned x - estart E a))).
    + apply H. lia.
    + apply bv_eq. rewrite u_small; [lia|]. pose proof (u64_range x). lia.
Qed.

(* [comment removed for export] *)
Lemma kcut_pw_sound : forall mk P E M0 M M' allkn wb wk wn kb kk len,
  pw_kind mk P ->
  know_ok SEGS E M0 allkn ->
  kentry_ok SEGS E M (mk (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     P M x -> P M' x) ->
  Forall (kentry_ok SEGS E M') (kcut mk allkn wb wk wn kb kk len).
Proof.
  intros mk P E M0 M M' allkn wb wk wn kb kk len Hkind Hall HK Hout.
  apply (proj1 (Hkind E M _ _)) in HK. destruct HK as [Hfl Hz].
  unfold kcut.
  set (ws := mkAlu ALU_ADD wb (ELit wk)). set (ks := mkAlu ALU_ADD kb (ELit kk)).
  assert (Uws : eqm (bv_unsigned (edenot E ws)) (estart E (SA wb wk))).
  { subst ws. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
    eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
  assert (Uks : eqm (bv_unsigned (edenot E ks)) (estart E (SA kb kk))).
  { subst ks. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
    eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
  pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
  apply Forall_app; split.
  - (* [comment removed for export] *)
    destruct (lin_ge0 allkn [(kb, kk)] [(wb, wk)]); [constructor|].
    destruct (lin_ge0 allkn [(wb, wk)] [(kb, kk)]) eqn:H1; [|constructor].
    destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk)]) eqn:H2; [|constructor].
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
    constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)).
    assert (HL : elenZ E (mkAlu ALU_SUB ws ks) = (estart E (SA wb wk) - estart E (SA kb kk))%Z).
    { unfold elenZ. rewrite mkAlu_denot.
      assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E ws) (edenot E ks))) (estart E (SA wb wk) - estart E (SA kb kk))) as [q Hq].
      { eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add; [exact Uws|]. destruct Uks as [q Hq]. exists (-q)%Z. lia. }
      pose proof (u64_range (alu64 ALU_SUB (edenot E ws) (edenot E ks))) as R.
      pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    rewrite HL. split.
    + unfold flat in *. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
    + intros i Hi. apply Hout; [|apply Hz]; unfold estart, elenZ in *; cbn [a_base a_off] in *; [|lia].
      left. rewrite u_small; lia.
  - (* [comment removed for export] *)
    destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]) eqn:H1; [|constructor].
    destruct (lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(kb, kk)]) eqn:H2; [|constructor].
    destruct (lin_ge0 allkn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]) eqn:H3; [|constructor].
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H3) as C0. cbn [xt_den edenot] in C0.
    rewrite u_lit0 in C0. unfold two64 in C0.
    cbv zeta.
    set (we := mkAlu ALU_ADD ws wn).
    assert (Uwe : eqm (bv_unsigned (edenot E we)) (estart E (SA wb wk) + elenZ E wn)).
    { subst we. rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uws|apply eqm_refl]. }
    destruct (split_lit we) as [hb ho] eqn:Hsp.
    lazymatch goal with |- Forall _ [mk ?ha0 _] => set (ha := ha0) end.
    assert (Hst : estart E ha = (estart E (SA wb wk) + elenZ E wn)%Z).
    { subst ha.
      destruct (lin_ge0 allkn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool eqn:Hh.
      - apply andb_prop in Hh as [Hh1 Hh2].
        pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh1) as C1. cbn [xt_den] in C1.
        pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh2) as C2. cbn [xt_den] in C2.
        unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
      - unfold estart at 1; cbn [a_base a_off]. rewrite Z.add_0_r.
        destruct Uwe as [q Hq]. pose proof (u64_range (edenot E we)).
        pose proof (u64_range (edenot E len)) as RL.
        unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    assert (HL : elenZ E (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)
                 = (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))%Z).
    { unfold elenZ at 1. rewrite mkAlu_denot.
      assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we)))
                  (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))) as [q Hq].
      { eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add.
        - rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uks|apply eqm_refl].
        - destruct Uwe as [q Hq]. exists (-q)%Z. lia. }
      pose proof (u64_range (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we))) as R.
      pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)). rewrite HL.
    split.
    + unfold flat. rewrite Hst. pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia.
    + intros i Hi. rewrite Hst.
      apply Hout.
      * right. pose proof (u64_range (edenot E len)) as RL.
        rewrite u_small; unfold flat, estart, elenZ in *; cbn [a_base a_off] in *; lia.
      * replace (estart E (SA wb wk) + elenZ E wn + i)%Z
          with (estart E (SA kb kk) + (estart E (SA wb wk) + elenZ E wn - estart E (SA kb kk) + i))%Z by lia.
        apply Hz. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
Qed.

Lemma kwr_cut_sound : forall E M0 M M' allkn wb wk wn kb kk len,
  know_ok SEGS E M0 allkn ->
  kentry_ok SEGS E M (KWr (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     M' x = M x) ->
  Forall (kentry_ok SEGS E M') (kwr_cut allkn wb wk wn kb kk len).
Proof.
  intros. eapply (kcut_pw_sound KWr _ E M0 M M'); [apply pw_kind_wr | eassumption | eassumption |].
  intros x Hx HP. unfold wview in *. rewrite (H1 x Hx). exact HP.
Qed.

Lemma cutout1p_eq : forall k ub uk un K,
  cutout1p k (mk_sprep k ub uk un) ub uk un K = cutout1 k ub uk un K.
Proof. intros. unfold cutout1p, cutout1. rewrite kentry_apart_bp_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_ok_cutout : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  know_ok SEGS E M' (kn_cutout k b o n).
Proof.
  intros E M M' k b o n HK Hout. unfold kn_cutout, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite cutout1p_eq. unfold cutout1.
  destruct (kentry_apart_b k b o n K) eqn:Hf.
  - apply Forall_one. eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | |[kb kk] len| |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kwr_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

Lemma droprange_sound : forall E cs R FULL model b n,
  cs_ok E cs R FULL model -> cs_ok E (node_droprange cs b n) R FULL model.
Proof.
  intros E cs R FULL model b n HC. unfold node_droprange. destruct (split_lit b) as [bb bk].
  apply cs_ok_set_kn; [exact HC|]. eapply know_ok_havoc; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity | apply mem_grows_refl].
Qed.

Lemma bump_sound : forall E cs R FULL model m cs',
  cs_ok E cs R FULL model -> node_bump cs m = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model m cs' HC H. unfold node_bump in H. destruct (Nat.leb (nxt cs) m); [|discriminate]. injection H as <-.
  split; [|reflexivity].
  destruct HC; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
    try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mkind_eqb_eq : forall a b, mkind_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; first [reflexivity | discriminate]. Qed.
Lemma kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.
Lemma amap_eqb_eq : forall x y, amap_eqb x y = true -> x = y.
Proof.
  intros [b l k] [b' l' k'] H. unfold amap_eqb in H. cbn [am_base am_len am_kind] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply mkind_eqb_eq in H3. congruence.
Qed.
Lemma pair_eqb_eq : forall x y, pair_eqb x y = true -> x = y.
Proof.
  intros [a b] [a' b'] H. unfold pair_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. congruence.
Qed.
Lemma afd_eqb_eq : forall x y, afd_eqb x y = true -> x = y.
Proof.
  intros [|k l o|] [|k' l' o'|] H; cbn [afd_eqb] in H; try discriminate; try reflexivity.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. apply expr_eqb_eq in H3. congruence.
Qed.
Lemma list_eqb_eq : forall {T} (eqb : T -> T -> bool), (forall x y, eqb x y = true -> x = y) ->
  forall x y, list_eqb eqb x y = true -> x = y.
Proof.
  intros T eqb Heq x. induction x as [|a x IH]; intros [|b y] H; cbn [list_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Heq _ _ H1), (IH _ H2). reflexivity.
Qed.















Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma flat_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> flat_x k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k b off n HK H. unfold flat_x in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  destruct (xlo k n) as [nl|] eqn:Hnl; [|discriminate]. destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hn. unfold two64 in H2.
  pose proof (base_range_sound SEGS E M k b lo hi HK Hb). pose proof (xlo_sound SEGS E M k n nl HK Hnl). pose proof (xhi_sound SEGS E M k n nh HK Hnh).
  unfold estart. cbn [a_base a_off]. lia.
Qed.

Lemma u_of_split : forall E e b k, split_lit e = (b, k) ->
  0 <= estart E (SA b k) < 2 ^ 64 -> bv_unsigned (edenot E e) = estart E (SA b k).
Proof.
  intros E e b k Hs Hr. rewrite (split_lit_denot E e b k Hs). unfold estart in *. cbn [a_base a_off] in *.
  apply u64_lit. lia.
Qed.










Lemma aluop_eqb_refl' : forall o, aluop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma mulop_eqb_refl' : forall o, mulop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma expr_eqb_refl' : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?aluop_eqb_refl', ?mulop_eqb_refl', ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.







(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ext1 (E : env) (v : nat) (a : word) : env :=
  Env (fun n => if Nat.eqb n v then a else ev E n) (eb E).

Lemma ext1_agree : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.
Lemma ext1_at : forall E v a, ev (ext1 E v a) v = a.
Proof. intros. cbn [ext1 ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.
Lemma env_agree_refl : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.
Lemma env_agree_trans : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.

(* [comment removed for export] *)
Lemma expr_vars_lt_eq : forall b e, AP.expr_vars_lt b e = GxSymRun3.expr_vars_lt b e.
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.
Lemma kentry_vars_lt_eq : forall b K, AP.kentry_vars_lt b K = GxSymRun3.kentry_vars_lt b K.
Proof.
  intros b K. destruct K as [[? ?] | [? ?] | [? ?] | | | | [? ?] | [? ?] ? [? ?] ?| [? ?] ? ?| [? ?] ?];
    cbn -[AP.expr_vars_lt GxSymRun3.expr_vars_lt]; unfold AP.saddr_vars_lt, GxSymRun3.saddr_vars_lt; cbn [a_base];
    rewrite ?expr_vars_lt_eq; reflexivity.
Qed.
Lemma kn_vars_lt_eq : forall b k, AP.kn_vars_lt b k = GxSymRun3.kn_vars_lt b k.
Proof. intros b k. induction k; cbn [AP.kn_vars_lt GxSymRun3.kn_vars_lt]; [reflexivity|]. rewrite kentry_vars_lt_eq, IHk. reflexivity. Qed.
Lemma sr_vars_lt_eq : forall b sr, AP.sr_vars_lt b sr = GxSymRun3.sr_vars_lt b sr.
Proof. intros b sr. induction sr; cbn [AP.sr_vars_lt GxSymRun3.sr_vars_lt]; [reflexivity|]. rewrite expr_vars_lt_eq, IHsr. reflexivity. Qed.

Lemma edenot_agree' : forall b E E' e, env_agree b E E' -> AP.expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof. intros. eapply edenot_agree; [eassumption | rewrite <- expr_vars_lt_eq; assumption]. Qed.
Lemma know_ok_agree' : forall b E E' M k, env_agree b E E' -> AP.kn_vars_lt b k = true -> know_ok SEGS E M k -> know_ok SEGS E' M k.
Proof. intros. eapply know_ok_agree; [eassumption | rewrite <- kn_vars_lt_eq; eassumption | assumption]. Qed.
Lemma regs_ok_agree' : forall b E E' sr R, env_agree b E E' -> AP.sr_vars_lt b sr = true -> regs_ok E sr R -> regs_ok E' sr R.
Proof. intros. eapply regs_ok_agree; [eassumption | rewrite <- sr_vars_lt_eq; eassumption | assumption]. Qed.

(* [comment removed for export] *)

Lemma sd_agree : forall D E E' fs s,
  env_agree nx0 E E' -> shape_vars_lt nx0 s = true -> sd D E fs s = sd D E' fs s.
Proof.
  intros D E E' fs s Hag. induction s; cbn [shape_vars_lt sd]; intros H; try reflexivity.
  - rewrite IHs by exact H. unfold Wp. replace (flat_map (piece_den E') ps) with (flat_map (piece_den E) ps); [reflexivity|].
    apply flat_map_ext. intros [bs|k]; cbn [piece_den]; [reflexivity|]. destruct Hag as [_ Heb]. rewrite Heb. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    rewrite IHs1, IHs2 by assumption. rewrite (edenot_agree' nx0 E E' e Hag H1). reflexivity.
  - apply HOLES_agree. exact Hag.
Qed.

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.
Lemma sd_has_nil : forall D E fs s, D [] -> sd D E fs s [].
Proof.
  intros D E fs s HD. induction s; cbn [sd].
  - reflexivity.
  - apply t_exit_has_nil.
  - apply t_emit_has_nil.
  - left. exact IHs1.
  - destruct (_ <=? _)%Z; assumption.
  - apply HOLES_nil.
  - exact HD.
Qed.
Lemma t_alt2_nil_l : forall T : TSet, T [] -> t_eq (t_alt2 t_nil T) T.
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [->|H]; assumption | intros H; right; exact H]. Qed.
Lemma t_alt2_nil_r : forall T : TSet, T [] -> t_eq (t_alt2 T t_nil) T.
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [H| ->]; assumption | intros H; left; exact H]. Qed.

Lemma t_eq_refl' : forall T : TSet, t_eq T T.
Proof. intros T tr. tauto. Qed.
Lemma sd_salt2 : forall D E fs a b, D [] ->
  t_eq (t_alt2 (sd D E fs a) (sd D E fs b)) (sd D E fs (salt2 a b)).
Proof.
  intros D E fs a b HD.
  assert (Ha : sd D E fs a []) by (apply sd_has_nil; exact HD).
  assert (Hb : sd D E fs b []) by (apply sd_has_nil; exact HD).
  unfold salt2. destruct a; destruct b; cbn [sd] in *;
    first [ apply t_alt2_nil_l; assumption | apply t_alt2_nil_r; assumption | apply t_eq_refl' ].
Qed.
Lemma salt2_vars : forall b x y, shape_vars_lt b x = true -> shape_vars_lt b y = true -> shape_vars_lt b (salt2 x y) = true.
Proof.
  intros b x y Hx Hy. unfold salt2.
  destruct x; destruct y; cbn [shape_vars_lt] in *; rewrite ?Hx, ?Hy; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node1_stmt (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) T.

Definition always (cs : acs) : bool := true.

(* [comment removed for export] *)
Definition sys_stmt (y : snode) : Prop := node1_stmt (is_ecall_at SEGS) (node_sys A nx0 y).
(* [comment removed for export] *)
Definition x_stmt (x : xnode) : Prop := forall args, node1_stmt always (node_x SEGS A nx0 x args).

(* [comment removed for export] *)
Definition join_stmt : Prop := forall b off n, node1_stmt always (fun cs => node_join SEGS cs b off n).

(* [comment removed for export] *)
Definition brk2_stmt : Prop :=
  forall cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_brk2 A LIMIT cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).

(* [comment removed for export] *)
Definition exit_stmt : Prop :=
  forall cs code E R FULL model,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_exit (Z_to_bv 64 code) (m_fs model)).

(* [comment removed for export] *)
Definition ext_stmt : Prop := forall id args, node1_stmt always (XN id args).
(* [comment removed for export] *)
Definition ext2_stmt : Prop :=
  forall id args cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> XB id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).
(* [comment removed for export] *)
Definition mm2_stmt (node : acs -> option (acs * acs)) : Prop :=
  forall cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).

Definition mm3_stmt (node : acs -> option (acs * acs * list acs)) : Prop :=
  forall cs csa csb cscs E R FULL model TA TB TC,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    (forall csc E' R' FULL' model', In csc cscs ->
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csc R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csc) FULL' model') TC) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA (t_alt2 TB TC)).

(* [comment removed for export] *)
Definition emit_stmt : Prop :=
  forall id args cs fd ps cs' E R FULL model T,
    cs_ok E cs R FULL model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_emit (Wp E fd ps) T).

(* [comment removed for export] *)
Definition holes_stmt : Prop :=
  forall h ch, HS h = Some ch ->
  forall E R FULL model, cs_ok E ch R FULL model ->
    srealizes SEGS (cfg R (pc ch) FULL model) (HOLES h E (m_fs model)).

(* [comment removed for export] *)
Hypothesis node_sys_sound : forall y, sys_stmt y.
Hypothesis node_brk2_sound : brk2_stmt.
Hypothesis node_mmap2_sound : mm2_stmt (node_mmap2 A nx0 LIMIT).
Hypothesis node_mmapin_sound : forall hole : bool, mm3_stmt (node_mmapin A LIMIT hole).   (* [comment removed for export] *)
Hypothesis node_mprotect2_sound : mm2_stmt (node_mprotect2 A LIMIT).
Hypothesis node_exit_sound : exit_stmt.
Hypothesis node_x_sound : forall x, x_stmt x.
Hypothesis node_join_sound : join_stmt.
Hypothesis node_ext_sound : ext_stmt.
Hypothesis node_emit_sound : emit_stmt.
Hypothesis node_ext2_sound : ext2_stmt.
Hypothesis HS_sound : holes_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma split_sound : forall cs e mid lo hi E R FULL model,
  cs_ok E cs R FULL model -> erange (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> cs_ok E (set_kn cs (KRange e lo mid :: kn cs)) R FULL model)
  /\ (mid < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) R FULL model).
Proof.
  intros cs e mid lo hi E R FULL model HC Hr.
  pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
  split; intros Hm; apply cs_ok_set_kn; [exact HC| |exact HC|];
    (constructor; [cbn [kentry_ok]; lia | exact (co_know _ _ _ _ _ HC)]).
Qed.

Lemma kn_contra_sound : forall E M k, know_ok SEGS E M k -> kn_contra k = true -> False.
Proof.
  intros E M k HK H. rewrite kn_contra_eq in H. unfold kn_contra_ref in H. apply existsb_exists in H as (K & Hin & HKb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | | | |e lo hi| | | |]; try discriminate. cbn [kentry_ok] in HKK.
  destruct (Z.ltb hi lo) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|].
  assert (GEN : forall c ts, lin_of e = (c, ts) ->
            match lin_range (erange k) c ts with
            | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
            | None => false end = true -> False).
  { intros c ts Hle Hm.
    destruct (lin_range (erange k) c ts) as [[a b]|] eqn:Hlr; [|discriminate].
    apply andb_prop in Hm as [Hm Hd]. apply andb_prop in Hm as [Ha Hb].
    apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. unfold two64 in Hb.
    pose proof (lin_range_sound E (erange k) (fun a lo hi Ha => erange_sound SEGS E M k a lo hi HK Ha) _ _ _ _ Hlr) as Hbd.
    pose proof (lin_of_sound E e) as [q Hq]. unfold lden, AX2S.uE in Hq. rewrite Hle in Hq. cbn [fst snd] in Hq.
    pose proof (u64_range (edenot E e)).
    assert (q = 0)%Z by nia. subst q.
    apply orb_prop in Hd as [Hd|Hd]; apply Z.ltb_lt in Hd; lia. }
  destruct e; try discriminate;
    try (destruct (lin_of _) as [c [|t1 ts]] eqn:Hle; try discriminate; exact (GEN _ _ eq_refl HKb)).
  (* [comment removed for export] *)
  cbn [edenot] in HKK. rewrite u_lit64, <- zlit64_eq in HKK. apply orb_prop in HKb as [Hb|Hb]; apply Z.ltb_lt in Hb; lia.
Qed.

Lemma estart_SA : forall E b k, estart E (SA b k) = bv_unsigned (edenot E b) + k.
Proof. reflexivity. Qed.

Lemma xlo1_sound : forall E M k e lo, know_ok SEGS E M k -> xlo1 k e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof.
  intros E M k e lo HK H. unfold xlo1 in H.
  assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some lo -> lo <= bv_unsigned (edenot E e)).
  { intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
  destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
  (destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
   destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
   [..| (* [comment removed for export] *) destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
   try discriminate; injection H as <-; lia).
Qed.

Lemma xhi1_sound : forall E M k e hi, know_ok SEGS E M k -> xhi1 k e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold xhi1 in H.
  assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some hi -> bv_unsigned (edenot E e) <= hi).
  { intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
  destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
  (destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
   destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
   [..| (* [comment removed for export] *) destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
   try discriminate; injection H as <-; lia).
Qed.

(* [comment removed for export] *)
Lemma deand_sound : forall E e e' s, deand e = (e', s) ->
  0 <= s /\ exists rho, 0 <= rho <= s /\ bv_unsigned (edenot E e) = (bv_unsigned (edenot E e') - rho) mod 2 ^ 64.
Proof.
  (* [comment removed for export] *)
  repeat match goal with H : _ |- _ => clear H end.
  intros E e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
    intros e' s Hd;
    try (cbn [deand] in Hd; injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
  cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
  destruct op;
    try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
  - (* [comment removed for export] *)
    destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
    destruct (IHa a' s1 eq_refl) as [Hs1 [ra [Hra Ea]]]. destruct (IHb b' s2 eq_refl) as [Hs2 [rb [Hrb Eb]]].
    split; [lia|]. exists (ra + rb). split; [lia|].
    cbn [edenot]. rewrite !u_add64, Ea, Eb. unfold two64.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof (u64_range (edenot E a')). pose proof (u64_range (edenot E b')).
    set (A1 := bv_unsigned (edenot E a')) in *. set (B1 := bv_unsigned (edenot E b')) in *.
    nia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - (* [comment removed for export] *)
    destruct b as [m| | | | | | |];
      try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
           rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
    cbv zeta in Hd.
    set (m' := m mod two64) in Hd. set (j := Z.log2 (two64 - m')) in Hd.
    destruct (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool eqn:Ht;
      [|injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
         rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity].
    apply andb_prop in Ht as [Hm Hj]. apply Z.eqb_eq in Hm. apply Z.leb_le in Hj.
    assert (Hj0 : 0 <= j) by (unfold j; apply Z.log2_nonneg).
    destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-.
    destruct (IHa a' s0 eq_refl) as [Hs0 [ra [Hra Ea]]].
    assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    split; [lia|].
    set (X := bv_unsigned (edenot E a)) in *.
    pose proof (u64_range (edenot E a)) as HX. fold X in HX.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hr : 0 <= X mod 2 ^ j < 2 ^ j) by (apply Z.mod_pos_bound; lia).
    assert (Hr2 : X mod 2 ^ j <= X) by (apply Z.mod_le; lia).
    exists (ra + X mod 2 ^ j). split; [lia|].
    cbn [edenot]. rewrite u_and64, u_lit64. fold X. fold m'.
    assert (Hm' : 0 <= m' < two64) by (unfold m'; apply Z.mod_pos_bound; unfold two64; lia).
    replace m' with (2 ^ 64 - 2 ^ j) by (unfold two64 in *; lia).
    rewrite land_highmask by lia.
    pose proof (u64_range (edenot E a')) as HA'. set (A' := bv_unsigned (edenot E a')) in *.
    set (r := X mod 2 ^ j) in *. clearbody r.
    rewrite Ea. rewrite Ea in HX. nia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma deand_vars : forall bnd e e' s, deand e = (e', s) -> AP.expr_vars_lt bnd e = true -> AP.expr_vars_lt bnd e' = true.
Proof.
  intros bnd e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
    intros e' s Hd Hv; try (cbn [deand] in Hd; injection Hd as <- <-; exact Hv).
  cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
  pose proof Hv as Hv0.
  cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hva Hvb].
  destruct op; try (injection Hd as <- <-; exact Hv0).
  - destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
    cbn [AP.expr_vars_lt]. rewrite (IHa a' s1 eq_refl Hva), (IHb b' s2 eq_refl Hvb). reflexivity.
  - destruct b as [m| | | | | | |]; try (injection Hd as <- <-; exact Hv0).
    cbv zeta in Hd.
    destruct (Z.eqb _ _ && Z.leb _ 48)%bool; [|injection Hd as <- <-; exact Hv0].
    destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-. exact (IHa a' s0 eq_refl Hva).
Qed.

Lemma xb2_sound : forall E M k e lo hi, know_ok SEGS E M k -> xb2 k e = Some (lo, hi) ->
  lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e lo hi HK H. unfold xb2 in H.
  set (plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end) in H.
  assert (HP : forall lo hi, plain = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi).
  { intros l h Hp. unfold plain in Hp.
    destruct (xlo1 k e) as [l1|] eqn:H1; [|discriminate]. destruct (xhi1 k e) as [h1|] eqn:H2; [|discriminate].
    injection Hp as <- <-. split; [eapply xlo1_sound; eassumption | eapply xhi1_sound; eassumption]. }
  destruct (deand e) as [e' s] eqn:Hd.
  destruct (deand_sound E e e' s Hd) as [Hs [rho [Hrho Ee]]].
  destruct (Z.eqb s 0); [exact (HP lo hi H)|].
  destruct (xlo1 k e') as [lo'|] eqn:H1; [|exact (HP lo hi H)].
  destruct (xhi1 k e') as [hi'|] eqn:H2; [|exact (HP lo hi H)].
  destruct (Z.leb s lo') eqn:Hsl; [|exact (HP lo hi H)]. apply Z.leb_le in Hsl.
  pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (xhi1_sound E M k e' hi' HK H2) as L2.
  pose proof (u64_range (edenot E e')) as R'.
  assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
  destruct plain as [[l0 h0]|].
  - specialize (HP l0 h0 eq_refl). injection H as <- <-. lia.
  - injection H as <- <-. lia.
Qed.

Lemma xlo2_sound : forall E M k e lo, know_ok SEGS E M k -> xlo2 k e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof.
  intros E M k e lo HK H. unfold xlo2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj1 (xb2_sound E M k e l h HK Hb)).
Qed.

Lemma xhi2_sound : forall E M k e hi, know_ok SEGS E M k -> xhi2 k e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold xhi2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj2 (xb2_sound E M k e l h HK Hb)).
Qed.
(* [comment removed for export] *)
Lemma brange_sound : forall E M k e lo hi, know_ok SEGS E M k -> brange k e = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e lo hi HK H. unfold brange in H.
  destruct (erange k e) as [[l h]|] eqn:Hr.
  - injection H as <- <-. exact (erange_sound SEGS E M k e l h HK Hr).
  - destruct (xlo k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi k e) as [h|] eqn:Hh; [|discriminate].
    injection H as <- <-. split; [exact (xlo_sound SEGS E M k e l HK Hl) | exact (xhi_sound SEGS E M k e h HK Hh)].
Qed.


(* [comment removed for export] *)
Lemma residue_fact_sound : forall E E' M M' k e ne,
  know_ok SEGS E M k ->
  edenot E' ne = edenot E e ->
  (forall e' s, deand e = (e', s) -> edenot E' e' = edenot E e') ->
  know_ok SEGS E' M' (residue_fact k e ne).
Proof.
  intros E E' M M' k e ne HK Hne Hag. unfold residue_fact.
  destruct (deand e) as [e' s] eqn:Hd. destruct (Z.ltb 0 s) eqn:Hs; [|constructor].
  destruct (xlo1 k e') as [lo'|] eqn:H1; [|constructor]. destruct (xhi1 k e') as [hi'|] eqn:H2; [|constructor].
  destruct (Z.leb s lo') eqn:Hsl; [|constructor]. apply Z.leb_le in Hsl.
  constructor; [|constructor]. cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot, u_sub64, Hne, (Hag e' s eq_refl).
  destruct (deand_sound E e e' s Hd) as [Hs0 [rho [Hrho Ee]]].
  pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (u64_range (edenot E e')) as R'.
  assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
  rewrite Hue. replace (bv_unsigned (edenot E e') - (bv_unsigned (edenot E e') - rho)) with rho by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma disj_by_end_sound : forall E M k b1 k1 n1 b2 k2,
  know_ok SEGS E M k -> disj_by_end k b1 k1 n1 b2 k2 = true ->
  estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2).
Proof.
  intros E M k b1 k1 n1 b2 k2 HK H. unfold disj_by_end in H.
  destruct (xhi k b1) as [hb|] eqn:H1; [|discriminate]. destruct (xhi k n1) as [hn|] eqn:H2; [|discriminate].
  destruct (xhi2 k (eadd b1 n1)) as [he|] eqn:H3; [|discriminate]. destruct (xlo k b2) as [lb2|] eqn:H4; [|discriminate].
  apply andb_prop in H as [Hw Hle]. apply Z.ltb_lt in Hw. apply Z.leb_le in Hle.
  pose proof (xhi_sound SEGS E M k b1 hb HK H1) as B1. pose proof (xhi_sound SEGS E M k n1 hn HK H2) as B2.
  pose proof (xhi2_sound E M k (eadd b1 n1) he HK H3) as B3. pose proof (xlo_sound SEGS E M k b2 lb2 HK H4) as B4.
  unfold eadd in B3. rewrite mkAlu_denot, u_add64 in B3.
  pose proof (u64_range (edenot E b1)) as R1. pose proof (u64_range (edenot E n1)) as R2. unfold two64 in *.
  rewrite Z.mod_small in B3 by lia.
  unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.
Lemma disj_x_sound : forall E M k b1 k1 n1 b2 k2 n2,
  know_ok SEGS E M k -> disj_x k b1 k1 n1 b2 k2 n2 = true ->
  estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) \/ estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1).
Proof.
  intros E M k b1 k1 n1 b2 k2 n2 HK H. unfold disj_x in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - exact (ranges_apart_x_sound SEGS E M k b1 k1 n1 b2 k2 n2 HK H).
  - left. exact (disj_by_end_sound E M k b1 k1 n1 b2 k2 HK H).
  - right. exact (disj_by_end_sound E M k b2 k2 n2 b1 k1 HK H).
Qed.

Lemma fact_ok_sound : forall E M k K, know_ok SEGS E M k -> fact_ok k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. destruct K as [| | | |e m|e lo hi| |[b1 k1] n1 [b2 k2] n2| |]; try discriminate; cbn [fact_ok] in H.
  - (* [comment removed for export] *) apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. cbn [kentry_ok]. split; [exact H1|].
    destruct (ealign_sound SEGS E M k e HK) as [Hr Hd].
    rewrite H2. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hd]. apply pow2_divide_le. split; [apply Z.log2_nonneg | exact H3].
  - (* [comment removed for export] *) apply orb_prop in H as [H|H].
    + destruct (xlo2 k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi2 k e) as [h|] eqn:Hh; [|discriminate].
      apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      pose proof (xlo2_sound E M k e l HK Hl). pose proof (xhi2_sound E M k e h HK Hh). cbn [kentry_ok]. lia.
    + apply andb_prop in H as [H1 H2].
      pose proof (lin_ge0d_sound 2 SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0d_sound 2 SEGS E M k _ _ HK H2) as A2.
      cbn [xt_den edenot] in A1, A2. rewrite u_small in A1, A2 by (pose proof two64_pos; lia). cbn [kentry_ok]. lia.
  - (* [comment removed for export] *) cbn [kentry_ok]. exact (disj_x_sound E M k b1 k1 n1 b2 k2 n2 HK H).
Qed.

Lemma fact_sound : forall E cs R FULL model K,
  cs_ok E cs R FULL model -> fact_ok (kn cs) K = true -> cs_ok E (add_kn cs [K]) R FULL model.
Proof.
  intros E cs R FULL model K HC H. unfold add_kn. apply cs_ok_set_kn; [exact HC|].
  constructor; [eapply fact_ok_sound; [exact (co_know _ _ _ _ _ HC) | exact H] | exact (co_know _ _ _ _ _ HC)].
Qed.


(* [comment removed for export] *)
Lemma entails_sound : forall E cs ch R FULL model,
  cs_ok E cs R FULL model -> entails cs ch = true -> cs_ok E ch R FULL model /\ pc ch = pc cs.
Proof.
  intros E cs ch R FULL model HC H. unfold entails in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc. split; [|symmetry; exact Hpc].
  match goal with Hl : match s_log (a_ss ch) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss ch)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hr : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hr; rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : forallb _ (kn ch) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  assert (HA : allowA E ch = allowA E cs) by (unfold allowA; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E ch model = hid E cs model) by (apply hid_ext; symmetry; exact Hallow).
  destruct HC; constructor; rewrite <- ?Hregs, <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hbrk, <- ?Hfd, <- ?Htid, ?HA; try assumption.
  - unfold Mr. rewrite HH. unfold know_ok. apply Forall_forall. intros K Hin.
    pose proof (proj1 (forallb_forall _ _) Hkn K Hin) as HK. apply existsb_exists in HK as [K' [Hin' Heq]].
    apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) co_know0 K Hin').
  - eapply holes_mono; [exact co_holes0 | lia].
  - lia.
  - destruct co_split0 as [Y HY]. exists Y. split; [lia | apply HY].
  - lia.
  - lia.
  - intros a. rewrite HH. replace (in_ghost E ch) with (in_ghost E cs) by (unfold in_ghost; rewrite Hghost; reflexivity). exact (co_zero0 a).
Qed.


(* [comment removed for export] *)
Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma reg_sound : forall E cs R FULL model n,
  cs_ok E cs R FULL model -> (0 < n < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof.
  intros E cs R FULL model n HC Hn. rewrite (co_regs _ _ _ _ _ HC). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

Lemma lit_of_sound : forall E e z, lit_of e = Some z -> edenot E e = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E e z H. destruct e; try discriminate. cbn [lit_of] in H. injection H as <-.
  split; [| unfold two64; apply Z.mod_pos_bound; lia].
  cbn [edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma reg_lit_sound : forall E cs R FULL model n z,
  cs_ok E cs R FULL model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E cs R FULL model n z HC Hn H. unfold reg_lit in H.
  destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs R FULL model n HC Hn), He. auto.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_respell : forall E sr R n e,
  regs_ok E sr R -> (0 < n < 32)%nat -> edenot E e = edenot E (nth n sr (ELit 0)) ->
  regs_ok E (sr_upd sr n e) R.
Proof.
  intros E sr R n e HR Hn He.
  replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_pin; [exact HR|].
  rewrite (HR (Z_to_bv 5 (Z.of_nat n))). unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_lit by lia. symmetry. exact He.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_set_n : forall E sr R n e v,
  regs_ok E sr R -> (0 < n < 32)%nat -> edenot E e = v ->
  regs_ok E (sr_upd sr n e) (regupd R (Z_to_bv 5 (Z.of_nat n)) v).
Proof.
  intros E sr R n e v HR Hn He.
  replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_set; [exact HR | | exact He].
  intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
  change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
  replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
  AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ AP.kn_vars_lt (nxt cs) (kn cs) = true
  /\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
  /\ AP.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof.
  intros cs H. unfold fresh_ok in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X. repeat split; try assumption.
  unfold pairs_vars_lt in *. rewrite forallb_app. apply andb_true_intro. split; assumption.
Qed.

Lemma allowA_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true -> allowA E' cs = allowA E cs.
Proof.
  intros b E E' cs Hag H. unfold allowA. rewrite !flat_map_concat_map. f_equal. apply map_ext_in. intros p Hin.
  pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
  unfold allow1, sh_lo, sh_hi, uE. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

Lemma in_allow_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs) = true -> in_allow E' cs = in_allow E cs.
Proof.
  intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. unfold pairs_vars_lt in H.
  induction (a_vis cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
  apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
  unfold sh_lo, sh_hi, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  pose proof (IH Hl) as E1. apply (f_equal negb) in E1. rewrite !negb_orb in E1.
  apply (f_equal negb) in E1. rewrite !negb_andb, !negb_involutive in E1.
  destruct (existsb _ l), (existsb _ l), (existsb _ l), (existsb _ l); cbn in E1 |- *; rewrite ?orb_true_r, ?orb_false_r; try reflexivity; try discriminate.
Qed.

Lemma in_ghost_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  in_ghost E' cs = in_ghost E cs.
Proof.
  intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_ghost.
  unfold pairs_vars_lt in H. rewrite forallb_app in H. apply andb_prop in H as [_ H].
  induction (a_ghost cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
  apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
  unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2), (IH Hl). reflexivity.
Qed.

Lemma hid_agree : forall b E E' cs model, env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  hid E' cs model = hid E cs model.
Proof.
  intros b E E' cs model Hag Hle H. apply functional_extensionality. intros a. unfold hid, vis.
  assert (H' : pairs_vars_lt b (a_vis cs) = true).
  { unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [H _]. exact H. }
  rewrite (in_allow_agree b E E' cs Hag H'). rewrite (argH_agree E E' a) by (eapply env_agree_le; eassumption). reflexivity.
Qed.


Lemma maps_match_agree : forall b E E' ms l, env_agree b E E' -> maps_vars_lt b ms = true ->
  maps_match E ms l -> maps_match E' ms l.
Proof.
  intros b E E' ms. induction ms as [|m ms IH]; intros l Hag H HM; cbn [maps_match] in *; [exact HM|].
  cbn [maps_vars_lt forallb] in H. apply andb_prop in H as [Hm Hr]. apply andb_prop in Hm as [H1 H2].
  unfold uE, amap_den in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  destruct (is_fog m).
  - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hag Hr HM) | right].
    exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hag Hr HM)].
  - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hag Hr HM)].
Qed.

(* [comment removed for export] *)
Lemma holes_agree : forall b E E' y l ms,
  env_agree b E E' -> maps_vars_lt b ms = true -> Forall (hole_ok E y l) ms -> Forall (hole_ok E' y l) ms.
Proof.
  intros b E E' y l ms Hag Hv H. apply Forall_forall. intros m Hin Hh.
  pose proof (proj1 (forallb_forall _ _) Hv m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  unfold hole_ok, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  exact (proj1 (Forall_forall _ _) H m Hin Hh).
Qed.

Lemma fds_ok_agree : forall b E E' f model,
  env_agree b E E' -> fd_vars_lt b f = true -> fds_ok E f model -> fds_ok E' f model.
Proof.
  intros b E E' f model Hag Hv H. destruct f as [|k len off|]; try exact H.
  cbn [fd_vars_lt] in Hv. apply andb_prop in Hv as [Hl Ho].
  destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
  unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag Hl), <- (edenot_agree' b E E' _ Hag Ho).
  destruct Hag as [_ Heb]. rewrite <- Heb. repeat split; assumption.
Qed.

Lemma cs_ok_agree : forall E E' cs R FULL model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true ->
  cs_ok E cs R FULL model -> cs_ok E' cs R FULL model.
Proof.
  intros E E' cs R FULL model Hag Hf HC.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
  pose proof (allowA_agree (nxt cs) E E' cs Hag Fallow) as HA.
  destruct HC; constructor; rewrite ?HA; try assumption.
  - eapply regs_ok_agree'; eassumption.
  - unfold Mr. rewrite HH. eapply know_ok_agree'; eassumption.
  - eapply fds_ok_agree; eassumption.
  - eapply maps_match_agree; [exact Hag | exact Fmaps | assumption].
  - eapply holes_agree; [exact Hag | exact Fmaps | assumption].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    unfold amap_den. rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2).
    exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2) in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite <- (edenot_agree' (nxt cs) E E' _ Hag Fbrk). assumption.
  - intros a. rewrite HH, (in_ghost_agree (nxt cs) E E' cs Hag Fallow). exact (co_zero0 a).
  - eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | assumption].
Qed.


Lemma fresh_ok_mono : forall gb cs, (nx0 <= gb)%nat -> fresh_ok gb cs = true -> fresh_ok nx0 cs = true.
Proof.
  intros gb cs Hle H. unfold fresh_ok in *.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X.
  repeat (apply andb_true_intro; split); try assumption. apply Nat.leb_le. lia.
Qed.

(* [comment removed for export] *)
Lemma u_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply u64_lit. assumption. Qed.

Lemma nth_sr_vars_lt : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.



(* [comment removed for export] *)
Lemma listZ_eqb_eq : forall x y, listZ_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn [listZ_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH y H2), H1. reflexivity.
Qed.
Lemma spieces_eqb_eq : forall x y, spieces_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn [spieces_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (IH y H2). f_equal.
  destruct a as [l|k], b as [l'|k']; cbn [spiece_eqb] in H1; try discriminate.
  - apply listZ_eqb_eq in H1. congruence.
  - apply Nat.eqb_eq in H1. congruence.
Qed.
Lemma shape_eqb_eq : forall x y, shape_eqb x y = true -> x = y.
Proof.
  induction x; intros y H; destruct y; cbn [shape_eqb] in H; try discriminate;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end; try reflexivity.
  - apply Z.eqb_eq in H. congruence.
  - apply Z.eqb_eq in H. apply spieces_eqb_eq in X0. rewrite (IHx _ X). congruence.
  - rewrite (IHx1 _ H), (IHx2 _ X). reflexivity.
  - apply expr_eqb_eq in H. apply Z.eqb_eq in X1. rewrite (IHx1 _ X0), (IHx2 _ X). congruence.
  - apply Nat.eqb_eq in H. congruence.
Qed.

Lemma find_disj_sound : forall E M k b1 b2 c1 o1 n1 c2 o2 n2,
  know_ok SEGS E M k -> find_disj k b1 b2 = Some (c1, o1, n1, c2, o2, n2) ->
  estart E (SA c1 o1) + elenZ E n1 <= estart E (SA c2 o2) \/ estart E (SA c2 o2) + elenZ E n2 <= estart E (SA c1 o1).
Proof.
  intros E M k b1 b2 c1 o1 n1 c2 o2 n2 HK. induction k as [|K k IH]; intros H; [discriminate|].
  inversion HK as [|K' k' HKK HK']; subst.
  cbn [find_disj] in H.
  destruct K as [| | | | | | |[d1 p1] m1 [d2 p2] m2| |]; try exact (IH HK' H).
  destruct (expr_eqb d1 b1 && expr_eqb d2 b2)%bool.
  - injection H as <- <- <- <- <- <-. exact HKK.
  - destruct (expr_eqb d1 b2 && expr_eqb d2 b1)%bool; [|exact (IH HK' H)].
    injection H as <- <- <- <- <- <-. cbn [kentry_ok] in HKK. lia.
Qed.

Lemma disj_side_fact_sound : forall E M k cA oA nA cB oB K,
  know_ok SEGS E M k -> disj_side_fact k cA oA nA cB oB = Some K ->
  0 <= estart E (SA cA oA) -> estart E (SA cB oB) < 2 ^ 64 ->
  estart E (SA cA oA) + elenZ E nA <= estart E (SA cB oB) ->
  kentry_ok SEGS E M K.
Proof.
  intros E M k cA oA nA cB oB K HK H HA HB Hle. unfold disj_side_fact in H.
  destruct (xlo2 k nA) as [n|] eqn:Hn; [|discriminate].
  destruct (base_range k cB) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  destruct (Z.leb 0 n && Z.leb n (bhi + oB))%bool eqn:Ht; [|discriminate]. injection H as <-.
  apply andb_prop in Ht as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  pose proof (xlo2_sound E M k nA n HK Hn) as Ln. pose proof (base_range_sound SEGS E M k cB blo bhi HK Hbr) as [_ Bh].
  pose proof (u64_range (edenot E nA)) as RnA.
  cbn [kentry_ok]. unfold esub, eaddz. rewrite !mkAlu_denot, u_sub64, !u_add64. cbn [edenot]. rewrite !u_lit64.
  unfold estart, elenZ in *; cbn [a_base a_off] in *.
  pose proof (u64_range (edenot E cA)) as RA. pose proof (u64_range (edenot E cB)) as RB. unfold two64.
  set (uA := bv_unsigned (edenot E cA)) in *. set (uB := bv_unsigned (edenot E cB)) in *. set (uN := bv_unsigned (edenot E nA)) in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E1 : (uB + oB mod 2 ^ 64) mod 2 ^ 64 = uB + oB).
  { rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  assert (E2 : (uA + oA mod 2 ^ 64) mod 2 ^ 64 = uA + oA).
  { rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  rewrite E1, E2. rewrite Z.mod_small by lia. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma casedisj_sound : forall cs b1 b2 csa csb E R FULL model,
  cs_ok E cs R FULL model -> node_casedisj cs b1 b2 = Some (csa, csb) ->
  (cs_ok E csa R FULL model /\ pc csa = pc cs) \/ (cs_ok E csb R FULL model /\ pc csb = pc cs).
Proof.
  intros cs b1 b2 csa csb E R FULL model HC H. unfold node_casedisj in H.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (find_disj (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
  destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|cbn in H; discriminate].
  destruct (disj_side_fact (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
  destruct (disj_side_fact (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate].
  injection H as <- <-.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
  unfold elenZ in *.
  destruct (find_disj_sound E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as [Hd|Hd].
  - left. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hd].
  - right. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hd].
Qed.



(* [comment removed for export] *)
Lemma expr_vars_lt_mono : forall b b' e, AP.expr_vars_lt b e = true -> (b <= b')%nat -> AP.expr_vars_lt b' e = true.
Proof.
  intros b b' e H Hle. induction e; cbn [AP.expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity); try (apply IHe; exact H).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
Lemma sr_vars_lt_mono : forall b b' sr, AP.sr_vars_lt b sr = true -> (b <= b')%nat -> AP.sr_vars_lt b' sr = true.
Proof.
  intros b b' sr H Hle. induction sr; cbn [AP.sr_vars_lt] in *; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (expr_vars_lt_mono _ _ _ H1 Hle), (IHsr H2). reflexivity.
Qed.
Lemma sr_vars_lt_upd : forall b sr n e, AP.sr_vars_lt b sr = true -> AP.expr_vars_lt b e = true -> AP.sr_vars_lt b (sr_upd sr n e) = true.
Proof.
  intros b sr n e. revert sr. induction n as [|n IH]; intros sr Hsr He.
  - destruct sr; cbn [sr_upd AP.sr_vars_lt]; cbn [AP.sr_vars_lt] in Hsr; rewrite He; [reflexivity|].
    apply andb_prop in Hsr as [_ H2]. rewrite H2. reflexivity.
  - destruct sr; cbn [sr_upd AP.sr_vars_lt]; cbn [AP.sr_vars_lt] in Hsr.
    + rewrite IH by (reflexivity || exact He). reflexivity.
    + apply andb_prop in Hsr as [H1 H2]. rewrite H1, (IH _ H2 He). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint ext_list (E : env) (nx : nat) (vals : list word) : env :=
  match vals with
  | [] => E
  | v :: rest => ext_list (ext1 E nx v) (Datatypes.S nx) rest
  end.

Lemma ext_list_agree : forall E nx vals, env_agree nx E (ext_list E nx vals).
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx; cbn [ext_list].
  - apply env_agree_refl.
  - eapply env_agree_trans; [apply ext1_agree|]. eapply env_agree_le; [apply IH | lia].
Qed.

Lemma ext_list_at : forall E nx vals i, (i < length vals)%nat -> ev (ext_list E nx vals) (nx + i) = nth i vals (Z_to_bv 64 0).
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx i Hi; cbn [length] in Hi; [lia|].
  cbn [ext_list]. destruct i as [|i].
  - rewrite Nat.add_0_r. pose proof (ext_list_agree (ext1 E nx v) (Datatypes.S nx) rest) as [Hag _].
    rewrite <- Hag by lia. cbn [nth]. apply ext1_at.
  - replace (nx + Datatypes.S i)%nat with (Datatypes.S nx + i)%nat by lia. cbn [nth]. apply IH. lia.
Qed.

Lemma regs_ok_sr_fresh : forall E sr R rs nx,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> Forall (fun r => 0 < r < 32)%nat rs ->
  regs_ok (ext_list E nx (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)) (sr_fresh sr rs nx) R.
Proof.
  intros E sr R rs. revert E sr. induction rs as [|r rest IH]; intros E sr nx HR Hsr Hrs; cbn [sr_fresh map ext_list].
  - exact HR.
  - apply Forall_cons_iff in Hrs as [Hr Hrest].
    apply IH.
    + apply regs_ok_respell.
      * eapply regs_ok_agree'; [apply ext1_agree | exact Hsr | exact HR].
      * exact Hr.
      * cbn [edenot]. rewrite ext1_at.
        pose proof (regs_ok_agree' nx E (ext1 E nx (getr R (Z_to_bv 5 (Z.of_nat r)))) sr R (ext1_agree _ _ _) Hsr HR) as HR'.
        etransitivity; [exact (HR' (Z_to_bv 5 (Z.of_nat r)))|]. unfold sr_get.
        assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat r)) 0%bv = false).
        { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
          change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
          replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
        rewrite Hnz, ridx_lit by lia. reflexivity.
    + apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
    + exact Hrest.
Qed.

Lemma havoc_sound : forall E cs R FULL model rs cs',
  cs_ok E cs R FULL model -> node_havoc nx0 cs rs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model rs cs' HC H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hf Hrs].
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_list E (nxt cs) (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  destruct HC'; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; [|reflexivity].
  apply regs_ok_sr_fresh; [exact (co_regs _ _ _ _ _ HC) | exact Fsr |].
  apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
  apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
Fixpoint kn_bigexprs (K : nat) (k : list kentry) : list expr :=
  match k with
  | [] => []
  | KWord a w v :: r => if bigb K v then v :: kn_bigexprs K r else kn_bigexprs K r
  | _ :: r => kn_bigexprs K r
  end.

Lemma kentry_vars_lt_mono : forall b b' K, AP.kentry_vars_lt b K = true -> (b <= b')%nat -> AP.kentry_vars_lt b' K = true.
Proof.
  intros b b' K H Hle.
  assert (E1 : forall e, AP.expr_vars_lt b e = true -> AP.expr_vars_lt b' e = true) by (intros; eapply expr_vars_lt_mono; eassumption).
  assert (A1 : forall a, AP.saddr_vars_lt b a = true -> AP.saddr_vars_lt b' a = true) by (intros [? ?]; unfold AP.saddr_vars_lt; apply E1).
  destruct K; cbn [AP.kentry_vars_lt] in *;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end;
    repeat match goal with
    | Y : AP.expr_vars_lt b ?e = true |- _ => rewrite (E1 e Y); clear Y
    | Y : AP.saddr_vars_lt b ?a = true |- _ => rewrite (A1 a Y); clear Y
    end; reflexivity.
Qed.
Lemma kn_vars_lt_mono' : forall b b' k, AP.kn_vars_lt b k = true -> (b <= b')%nat -> AP.kn_vars_lt b' k = true.
Proof.
  intros b b' k H Hle. induction k as [|K k IH]; [reflexivity|]. cbn [AP.kn_vars_lt] in *. apply andb_prop in H as [H1 H2].
  rewrite (kentry_vars_lt_mono b b' K H1 Hle), (IH H2). reflexivity.
Qed.


Lemma kn_bigsubst_sound : forall K k nx E2 M,
  know_ok SEGS E2 M k -> AP.kn_vars_lt nx k = true ->
  (forall i, (i < length (kn_bigexprs K k))%nat -> ev E2 (nx + i) = edenot E2 (nth i (kn_bigexprs K k) (ELit 0))) ->
  know_ok SEGS E2 M (fst (kn_bigsubst K k nx)).
Proof.
  intros K k. induction k as [|x r IH]; intros nx E2 M HK Hv Hvals; [constructor|].
  inversion HK as [|x' r' Hx Hr]; subst. cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [Hvx Hvr].
  cbn [kn_bigsubst]. cbn [kn_bigexprs] in Hvals.
  assert (DFLT : (forall i, (i < length (kn_bigexprs K r))%nat -> ev E2 (nx + i) = edenot E2 (nth i (kn_bigexprs K r) (ELit 0))) ->
                 know_ok SEGS E2 M (fst (let '(r', c) := kn_bigsubst K r nx in (x :: r', c)))).
  { intros Hvals'. pose proof (IH nx E2 M Hr Hvr Hvals') as IH'. destruct (kn_bigsubst K r nx) as [r' c]. cbn [fst] in *. constructor; [exact Hx | apply IH']. }
  destruct x as [a w v| | | | | | | | |]; try (apply DFLT; exact Hvals).
  destruct (bigb K v) eqn:Hb; [|apply DFLT; exact Hvals]. clear DFLT.
  pose proof (IH (Datatypes.S nx) E2 M Hr ltac:(eapply kn_vars_lt_mono'; [exact Hvr | lia])) as IH'.
  destruct (kn_bigsubst K r (Datatypes.S nx)) as [r' c] eqn:Hs. cbn [fst]. constructor.
  - cbn [kentry_ok] in Hx |- *. destruct Hx as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    rewrite H3. f_equal. f_equal. cbn [edenot]. symmetry. replace nx with (nx + 0)%nat by lia. rewrite (Hvals 0%nat ltac:(cbn; lia)). reflexivity.
  - apply IH'. intros i Hi. replace (Datatypes.S nx + i)%nat with (nx + Datatypes.S i)%nat by lia. rewrite (Hvals (Datatypes.S i) ltac:(cbn; lia)). reflexivity.
Qed.

Lemma node_havoc_nxt : forall cs rs cs1, node_havoc nx0 cs rs = Some cs1 -> nxt cs1 = (nxt cs + length rs)%nat /\ pc cs1 = pc cs.
Proof.
  intros cs rs cs1 H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r : nat => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool; [|discriminate].
  injection H as <-. split; reflexivity.
Qed.

Lemma havocbig_sound : forall E cs R FULL model K cs',
  cs_ok E cs R FULL model -> node_havocbig nx0 cs K = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model K cs' HC H. unfold node_havocbig in H.
  destruct (node_havoc nx0 cs _) as [cs1|] eqn:Hh; [|discriminate].
  destruct (fresh_ok nx0 cs1) eqn:Hf1; [|discriminate].
  destruct (kn_bigsubst K (kn cs1) (nxt cs1)) as [k' c] eqn:Hs. injection H as <-.
  destruct (havoc_sound E cs R FULL model _ cs1 HC Hh) as (E1 & [Hag0 Hag1] & HC1 & Hpc1).
  destruct (fresh_ok_parts cs1 Hf1) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (vals := map (edenot E1) (kn_bigexprs K (kn cs1))).
  set (E2 := ext_list E1 (nxt cs1) vals).
  assert (Hag2 : env_agree (nxt cs1) E1 E2) by apply ext_list_agree.
  assert (Hnx : (nxt cs <= nxt cs1)%nat).
  { destruct (node_havoc_nxt cs _ cs1 Hh) as [-> _]. lia. }
  exists E2. split; [|split; [|rewrite <- Hpc1; reflexivity]].
  { split; (eapply env_agree_trans; [|eapply env_agree_le; [exact Hag2 | lia]]); assumption. }
  pose proof (cs_ok_agree E1 E2 cs1 R FULL model Hag2 Hf1 HC1) as HC2.
  replace (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nxt cs1 + c))) with (set_kn (bump cs1 c) k') by reflexivity.
  apply cs_ok_set_kn.
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - replace k' with (fst (kn_bigsubst K (kn cs1) (nxt cs1))) by (rewrite Hs; reflexivity).
    unfold Mr. change (hid E2 (bump cs1 c) model) with (hid E2 cs1 model).
    apply kn_bigsubst_sound; [exact (co_know _ _ _ _ _ HC2) | rewrite kn_vars_lt_eq; rewrite <- kn_vars_lt_eq; exact Fkn |].
    intros i Hi. unfold E2. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hi).
    unfold vals. change (Z_to_bv 64 0) with (edenot E1 (ELit 0)). rewrite map_nth.
    eapply (edenot_agree' (nxt cs1)); [apply ext_list_agree|].
    (* [comment removed for export] *)
    clear - Fkn Hi. revert i Hi. generalize (kn cs1) Fkn. intros k Hk.
    induction k as [|x r IH]; intros i Hi; [cbn in Hi; lia|].
    cbn [AP.kn_vars_lt] in Hk. apply andb_prop in Hk as [Hx Hr]. cbn [kn_bigexprs] in Hi |- *.
    destruct x as [a w v| | | | | | | | |]; try (apply IH; assumption).
    destruct (bigb K v); [|apply IH; assumption].
    destruct i as [|i]; cbn [nth]; [cbn [AP.kentry_vars_lt] in Hx; apply andb_prop in Hx as [_ Hx]; exact Hx | apply IH; [exact Hr | cbn [length] in Hi; lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition upd (E : env) (J : nat) (w : word) : env := Env (fun n => if Nat.eqb n J then w else ev E n) (eb E).

Lemma esubst_denot : forall E J e x, edenot E (esubst J e x) = edenot (upd E J (edenot E e)) x.
Proof.
  intros E J e x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [esubst edenot]; try reflexivity.
  - cbn [upd ev]. destruct (Nat.eqb n J); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma upd_agree : forall E J w, env_agree J E (upd E J w).
Proof. intros E J w. split; [|reflexivity]. intros n Hn. cbn [upd ev]. destruct (Nat.eqb_spec n J); [lia|reflexivity]. Qed.
Lemma upd_at : forall E J w, ev (upd E J w) J = w.
Proof. intros. cbn [upd ev]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_upd : forall E J w w', upd (upd E J w) J w' = upd E J w'.
Proof. intros [f g] J w w'. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb n J); reflexivity. Qed.

Lemma estart_asubst : forall E J e a, estart E (asubst J e a) = estart (upd E J (edenot E e)) a.
Proof. intros E J e [b o]. unfold asubst, estart. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.
Lemma adenot_asubst : forall E J e a, adenot E (asubst J e a) = adenot (upd E J (edenot E e)) a.
Proof. intros E J e [b o]. unfold asubst, adenot. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.

Lemma kentry_ok_ksubst : forall E J e M K,
  kentry_ok SEGS E M (ksubst J e K) <-> kentry_ok SEGS (upd E J (edenot E e)) M K.
Proof.
  intros E J e M K. set (E' := upd E J (edenot E e)).
  destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubst kentry_ok];
    unfold flat, elenZ; rewrite ?estart_asubst, ?adenot_asubst, ?esubst_denot; fold E'; tauto.
Qed.

Lemma know_ok_ksubst : forall E J e M k,
  know_ok SEGS E M (map (ksubst J e) k) <-> know_ok SEGS (upd E J (edenot E e)) M k.
Proof.
  intros E J e M k. unfold know_ok. induction k as [|K k IH]; [split; intros; constructor|].
  cbn [map]. split; intros H; inversion H; subst; constructor; try (apply IH; assumption);
    apply (kentry_ok_ksubst E J e M K); assumption.
Qed.

(* [comment removed for export] *)
Lemma inst_allowA : forall E J e inv, allowA E (inst inv J e) = allowA (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. unfold allowA, inst. cbn [a_vis a_ghost]. rewrite <- map_app, flat_map_concat_map, flat_map_concat_map, map_map.
  f_equal. apply map_ext. intros [b n]. unfold allow1, psubst, sh_lo, sh_hi, uE. cbn [fst snd]. rewrite !esubst_denot. reflexivity.
Qed.

Lemma existsb_map' : forall {X Y} (f : Y -> bool) (g : X -> Y) l, existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. intros X Y f g l. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma inst_in_allow : forall E J e inv, in_allow E (inst inv J e) = in_allow (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh, inst. cbn [a_vis].
  rewrite !existsb_map'. f_equal; f_equal; apply functional_extensionality; intros [b n];
    unfold psubst, sh_lo, sh_hi, uE; cbn [fst snd]; rewrite !esubst_denot; reflexivity.
Qed.

Lemma inst_in_ghost : forall E J e inv, in_ghost E (inst inv J e) = in_ghost (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. apply functional_extensionality. intros z. unfold in_ghost, inst. cbn [a_ghost].
  induction (a_ghost inv) as [|[b n] l IH]; [reflexivity|]. cbn [map existsb fst snd psubst].
  unfold uE in *. cbn [fst snd]. rewrite !esubst_denot, IH. reflexivity.
Qed.

Lemma inst_hid : forall E J e inv model, (nx0 <= J)%nat ->
  hid E (inst inv J e) model = hid (upd E J (edenot E e)) inv model.
Proof.
  intros E J e inv model HJ. apply functional_extensionality. intros a. unfold hid, vis.
  rewrite inst_in_allow. rewrite (argH_agree E (upd E J (edenot E e)) a); [|eapply env_agree_le; [apply upd_agree | exact HJ]].
  unfold inst. cbn [a_maps]. reflexivity.
Qed.

Lemma inst_maps : forall E J e inv, map (amap_den E) (a_maps (inst inv J e)) = map (amap_den (upd E J (edenot E e))) (a_maps inv).
Proof.
  intros. unfold inst. cbn [a_maps]. rewrite map_map. apply map_ext. intros m. unfold amap_den, msubst. cbn [am_base am_len].
  rewrite !esubst_denot. reflexivity.
Qed.

Lemma maps_match_msubst : forall E J e ms l,
  maps_match E (map (msubst J e) ms) l <-> maps_match (upd E J (edenot E e)) ms l.
Proof.
  intros E J e ms. induction ms as [|m ms IH]; intros l; cbn [maps_match map]; [tauto|].
  unfold is_fog, msubst, uE, amap_den. cbn [am_kind am_base am_len]. rewrite !esubst_denot.
  destruct (is_tok_kind (am_kind m)).
  - split; (intros [HM|(iv & l' & -> & Hsz & HM)]; [left; apply IH; exact HM | right; exists iv, l'; split; [reflexivity|]; split; [exact Hsz | apply IH; exact HM]]).
  - split; (intros (l' & -> & HM); exists l'; split; [reflexivity | apply IH; exact HM]).
Qed.
(* [comment removed for export] *)
Lemma holes_msubst : forall E J e y l ms,
  Forall (hole_ok E y l) (map (msubst J e) ms) <-> Forall (hole_ok (upd E J (edenot E e)) y l) ms.
Proof.
  intros E J e y l ms. induction ms as [|m ms IH]; cbn [map].
  - split; intros; constructor.
  - rewrite !Forall_cons_iff, IH.
    assert (X : hole_ok E y l (msubst J e m) <-> hole_ok (upd E J (edenot E e)) y l m).
    { unfold hole_ok, is_hole, msubst, uE. cbn [am_kind am_base am_len]. rewrite !esubst_denot. tauto. }
    rewrite X. tauto.
Qed.


Lemma regs_ok_inst : forall E J e sr R,
  regs_ok E (map (esubst J e) sr) R <-> regs_ok (upd E J (edenot E e)) sr R.
Proof.
  intros E J e sr R. unfold regs_ok, sr_get.
  assert (G : forall r, edenot E (if bv_eqb r 0 then ELit 0 else nth (ridx r) (map (esubst J e) sr) (ELit 0))
                     = edenot (upd E J (edenot E e)) (if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0))).
  { intros r. destruct (bv_eqb r 0); [reflexivity|].
    replace (ELit 0) with (esubst J e (ELit 0)) at 1 by reflexivity. rewrite map_nth. apply esubst_denot. }
  split; intros H r; [rewrite <- G | rewrite G]; apply H.
Qed.

Lemma fds_ok_inst : forall E J e f model, fds_ok E (fsubst J e f) model <-> fds_ok (upd E J (edenot E e)) f model.
Proof.
  intros E J e f model. destruct f as [|k l o|]; cbn [fsubst fds_ok]; try tauto.
  unfold uE. rewrite !esubst_denot. cbn [eb upd]. tauto.
Qed.

Lemma cs_ok_inst : forall E J e inv R FULL model, (nx0 <= J)%nat -> s_log (a_ss inv) = [] ->
  cs_ok E (inst inv J e) R FULL model <-> cs_ok (upd E J (edenot E e)) inv R FULL model.
Proof.
  intros E J e inv R FULL model HJ Hlog.
  pose proof (inst_hid E J e inv model HJ) as HH. pose proof (inst_allowA E J e inv) as HA. pose proof (inst_maps E J e inv) as HM.
  pose proof (inst_in_ghost E J e inv) as HG.
  assert (AG : env_agree nx0 E (upd E J (edenot E e))) by (eapply env_agree_le; [apply upd_agree | exact HJ]).
  split; intros HC; destruct HC; constructor;
    cbn [inst a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset mk_ss] in *;
    rewrite <- ?HA, <- ?HM; try assumption.
  - apply regs_ok_inst. assumption.
  - unfold Mr. rewrite <- HH. apply know_ok_ksubst. exact co_know0.
  - apply fds_ok_inst. assumption.
  - apply (proj1 (maps_match_msubst E J e _ _)). assumption.
  - apply (proj1 (holes_msubst E J e _ _ _)). assumption.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (Forall_forall _ _) co_none0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk) as X.
    unfold amap_den, msubst in X |- *. cbn [am_base am_len am_kind] in X. rewrite !esubst_denot in X. exact X.
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (Forall_forall _ _) co_kinds0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk a) as X.
    unfold msubst in X. cbn [am_base am_len] in X. rewrite !esubst_denot in X. exact (X Ha).
  - rewrite <- esubst_denot. assumption.
  - intros a. unfold Mr in *. rewrite <- HH. first [rewrite HG | rewrite <- HG]. exact (co_zero0 a).
  - eapply SINV_agree; [exact AG | assumption].
  - apply regs_ok_inst. assumption.
  - reflexivity.
  - unfold Mr in *. rewrite HH. apply know_ok_ksubst. assumption.
  - apply fds_ok_inst. assumption.
  - apply (proj2 (maps_match_msubst E J e _ _)). assumption.
  - apply (proj2 (holes_msubst E J e _ _ _)). assumption.
  - apply Forall_forall. intros m' Hin Hk. apply in_map_iff in Hin as [m [<- Hin]].
    pose proof (proj1 (Forall_forall _ _) co_none0 m Hin Hk) as X.
    unfold amap_den, msubst. cbn [am_base am_len am_kind]. rewrite !esubst_denot. exact X.
  - apply Forall_forall. intros m' Hin Hk a Ha. apply in_map_iff in Hin as [m [<- Hin]].
    unfold msubst in Ha, Hk. cbn [am_base am_len am_kind] in Ha, Hk. rewrite !esubst_denot in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite esubst_denot. assumption.
  - rewrite HA. assumption.
  - rewrite HA. assumption.
  - intros a. unfold Mr in *. rewrite HH. first [rewrite <- HG | rewrite HG]. exact (co_zero0 a).
  - eapply SINV_agree; [|eassumption]. destruct AG as [AG1 AG2]. split; [intros n Hn; symmetry; apply AG1; exact Hn | symmetry; exact AG2].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kentry_eqb_h_sound : forall E M k X K,
  know_ok SEGS E M k -> kentry_ok SEGS E M X -> kentry_eqb_h X K = true -> kflat_h k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k X K HK HX Heq Hfl. unfold kentry_eqb_h in Heq. apply orb_prop in Heq as [Heq|Heq].
  { apply kentry_eqb_eq in Heq. subst. exact HX. }
  assert (SAD : forall b o b' o' n ne, saddr_eqb_h (SA b o) (SA b' o') = true -> flat E (SA b o) n ->
            flat_x k b' o' ne = true -> estart E (SA b' o') = estart E (SA b o)).
  { intros b o b' o' n ne Hs Hf Hf'. unfold saddr_eqb_h in Hs. cbn [a_base a_off] in *.
    apply orb_prop in Hs as [Hs|Hs]; [apply saddr_eqb_eq in Hs; injection Hs as -> ->; reflexivity|].
    apply expr_eqb_eq in Hs. apply (f_equal (fun x => bv_unsigned (edenot E x))) in Hs.
    unfold eaddz in Hs. rewrite !mkAlu_denot, !u_add64 in Hs. cbn [edenot] in Hs. rewrite !u_lit64 in Hs.
    pose proof (flat_x_sound E M k b' o' ne HK Hf') as (F1 & F2 & F3). pose proof (u64_range (edenot E ne)).
    unfold flat, estart in *; cbn [a_base a_off] in *.
    pose proof (u64_range (edenot E b)). pose proof (u64_range (edenot E b')). unfold two64 in Hs.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (E1 : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b) + o) by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
    assert (E2 : (bv_unsigned (edenot E b') + o' mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b') + o') by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (AD : forall a a', estart E a' = estart E a -> adenot E a' = adenot E a).
  { intros [b o] [b' o'] He. unfold adenot, estart, v_addi in *. cbn [a_base a_off] in *. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite He. reflexivity. }
  destruct X as [[b o] w v|[b o] n|[b o] n kk| | | |[b o] n| |[b o] n c|[b o] n];
    destruct K as [[b' o'] w' v'|[b' o'] n'|[b' o'] n' kk'| | | |[b' o'] n'| |[b' o'] n' c'|[b' o'] n']; try discriminate;
    repeat match type of Heq with (_ && _)%bool = true => apply andb_prop in Heq as [Heq ?X] end;
    cbn [kentry_ok kflat_h] in *.
  - apply Nat.eqb_eq in X0. apply expr_eqb_eq in X. subst w' v'. destruct HX as (H1 & H2 & H3).
    pose proof (SAD b o b' o' _ _ Heq H2 Hfl) as ES.
    split; [exact H1|]. split; [unfold flat in *; rewrite ES; exact H2|]. rewrite (AD _ _ ES). exact H3.
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply Nat.eqb_eq in X. apply expr_eqb_eq in X0. subst n' kk'. destruct HX as (H1 & H2 & H3).
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. split; [exact H2 | exact H3].
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply Z.eqb_eq in X. apply expr_eqb_eq in X0. subst n' c'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
  - apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
    pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_off_hull : forall a : word, in_hull A (bv_unsigned a) = false -> seg_rom SEGS a = None.
Proof.
  intros a Ha. unfold seg_rom.
  rewrite (memory_read1_hidden SEGS (fun x => negb (in_hull A (bv_unsigned x)))); [reflexivity| |].
  - intros x Hx. apply SEGS_in_hull. apply negb_true_iff in Hx. exact Hx.
  - rewrite Ha. reflexivity.
Qed.

Lemma rdn_bytes_some : forall M (a : word) w bs,
  rdn SEGS M a w = Some bs ->
  forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat w)%Z ->
  in_hull A (bv_unsigned x) = false -> M x <> None.
Proof.
  intros M a w. revert a. induction w as [|w IH]; intros a bs Hr x Hx Hh; [lia|].
  cbn [rdn] in Hr.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    destruct (M a) eqn:HMa; [congruence|]. rewrite (seg_rom_off_hull a Hh) in Hr. discriminate.
  - destruct (match M a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
    destruct (rdn SEGS M (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
    pose proof (u64_range x).
    assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    eapply (IH (a + 1)%bv rest Hr2); [rewrite Hu1; lia | exact Hh].
Qed.

Lemma cover1_sound : forall E M k b i e,
  know_ok SEGS E M k -> cover1 k b i = Some e ->
  (i < e)%Z /\ forall j, (i <= j < e)%Z -> in_hull A (uE E b + j) = false ->
     (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None.
Proof.
  intros E M k b i e HK. induction k as [|K r IH]; intros H; [discriminate|].
  inversion HK as [|K' r' HKK Hr]; subst. cbn [cover1] in H.
  match type of H with (match ?h with Some e0 => Some e0 | None => _ end = _) => destruct h as [e1|] eqn:Hhit end;
    [injection H as <- | exact (IH Hr H)].
  clear IH Hr HK.
  assert (ZF : forall kb kk l (P : option byte -> Prop),
            (flat E (SA kb kk) (elenZ E (ELit l)) /\ forall i0, (0 <= i0 < elenZ E (ELit l))%Z -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i0)))) ->
            (forall x, P x -> x <> None) ->
            (if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l)%Z else None) = Some e1 ->
            (i < e1)%Z /\ forall j, (i <= j < e1)%Z -> in_hull A (uE E b + j) = false ->
               (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None).
  { intros kb kk l P [Hfl Hall] HP Hc.
    destruct (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool eqn:Hcnd; [|discriminate].
    injection Hc as <-.
    repeat match type of Hcnd with (_ && _)%bool = true => apply andb_prop in Hcnd as [Hcnd ?X] end.
    apply expr_eqb_eq in Hcnd. subst kb. apply Z.leb_le in X2. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    unfold two64 in X1. rewrite (elenZ_lit E l) in Hfl, Hall by lia.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj Hh. split; [lia|].
    replace (bv_unsigned (edenot E b) + j)%Z with (bv_unsigned (edenot E b) + kk + (j - kk))%Z by lia.
    apply HP. apply Hall. lia. }
  destruct K as [[kb kk] w v|[kb kk] [l| | | | | | |]|[kb kk] [l| | | | | | |] bk| | | | | |[kb kk] [l| | | | | | |] fc|[kb kk] [l| | | | | | |]];
    try discriminate.
  - (* [comment removed for export] *)
    destruct (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool eqn:Hcnd; [|discriminate]. injection Hhit as <-.
    apply andb_prop in Hcnd as [Hcnd X]. apply andb_prop in Hcnd as [Hb X0].
    apply expr_eqb_eq in Hb. subst kb. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    cbn [kentry_ok] in HKK. destruct HKK as (Hw & Hfl & Hrd).
    pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj Hh. split; [lia|].
    apply (rdn_bytes_some M _ w _ Hrd); rewrite ?Hu, ?u64_lit by lia; [lia | exact Hh].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 0))); [exact HKK | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK. destruct HKK as (Hfl & Hlen & Hall).
    eapply (ZF kb kk l (fun x => exists b0, x = Some b0)); [split; [exact Hfl | intros i0 Hi0; eexists; apply Hall; exact Hi0] | intros x [b0 ->]; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 fc))); [exact HKK | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x <> None)); [exact HKK | intros x Hx; exact Hx | exact Hhit].
Qed.

Lemma cover_x_sound : forall fuel E M k b i stop,
  know_ok SEGS E M k -> cover_x fuel k b i stop = true ->
  forall j, (i <= j < stop)%Z -> in_hull A (uE E b + j) = false ->
    (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None.
Proof.
  induction fuel as [|f IH]; intros E M k b i stop HK H j Hj Hh; [discriminate|].
  cbn [cover_x] in H. destruct (Z.leb_spec stop i); [lia|].
  destruct (cover1 k b i) as [e|] eqn:Hc; [|discriminate].
  destruct (Z.ltb_spec i e); [|discriminate].
  destruct (cover1_sound E M k b i e HK Hc) as [_ Hcov].
  destruct (Z.lt_ge_cases j e).
  - apply Hcov; [lia | exact Hh].
  - eapply IH; [exact HK | exact H | lia | exact Hh].
Qed.

Lemma kunk_covered_sound : forall E M k K, know_ok SEGS E M k -> kunk_covered A k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. unfold kunk_covered in H.
  destruct K as [| | | | | | | | |[b o] [n| | | | | | |]]; try discriminate.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H. apply Z.leb_le in X3. apply Z.leb_le in X2.
  pose proof (flat_x_sound E M k b o (ELit n) HK X1) as (F1 & F2 & F3).
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK X0) as AP0.
  cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
  pose proof HULL_ok as HU; unfold hull_ok, KHI in HU.
  rewrite (elenZ_lit E n) in AP0 by lia. rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by lia.
  unfold estart in AP0; cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
  cbn [kentry_ok]. rewrite elenZ_lit by lia. split.
  - unfold flat, estart in *; cbn [a_base a_off] in *. lia.
  - intros i Hi. unfold estart in *; cbn [a_base a_off] in *.
    replace (bv_unsigned (edenot E b) + o + i)%Z with (uE E b + (o + i))%Z by (unfold uE; lia).
    apply (cover_x_sound _ E M k b o (o + n) HK X); [lia|].
    unfold in_hull, uE. apply andb_false_iff.
    destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Lemma respell_ok_sound : forall E M k a e,
  know_ok SEGS E M k -> respell_ok k a e = true -> edenot E a = edenot E e.
Proof.
  intros E M k a e HK H. unfold respell_ok in H.
  destruct (decide_branch k BC_EQ a e) as [[|]|] eqn:Hd.
  - pose proof (decide_branch_sound SEGS E M k BC_EQ a e true HK Hd) as Heq. cbn [branch_taken] in Heq. apply bv_eqb_eq in Heq. exact Heq.
  - destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
    apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
    pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
    cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
    apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
    assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
    apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
  - destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
    apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
    pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
    cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
    apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
    assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
    apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
Qed.

Lemma kn_incl_h_sound : forall E M k tk, know_ok SEGS E M k -> kn_incl_h A k tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k tk HK H. unfold kn_incl_h in H. apply Forall_forall. intros K Hin.
  pose proof (proj1 (forallb_forall _ _) H K Hin) as HK1. unfold kn_incl1_h in HK1.
  destruct (existsb (fun X => kentry_eqb X K) k) eqn:Hex1.
  { apply existsb_exists in Hex1 as [X [HinX Heq]]. apply kentry_eqb_eq in Heq. subst. exact (proj1 (Forall_forall _ _) HK K HinX). }
  (* [comment removed for export] *)
  assert (IMG : kimg_sub_covered k K = true -> kentry_ok SEGS E M K).
  { intros Hc. unfold kimg_sub_covered in Hc. destruct K as [| | |lo hi| | | | | |]; try discriminate.
    apply existsb_exists in Hc as [X [HinX HX]]. destruct X as [| | |lo' hi'| | | | | |]; try discriminate.
    apply andb_prop in HX as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ HinX) as HKX. cbn [kentry_ok] in HKX |- *.
    destruct HKX as (Ha & Hb & Hc). split; [lia|]. split; [lia|]. intros i Hi. apply Hc. lia. }
  (* [comment removed for export] *)
  assert (KWV : kword_val_h k K = true -> kentry_ok SEGS E M K).
  { intros Hc. unfold kword_val_h in Hc. destruct K as [a w v| | | | | | | | |]; try discriminate.
    apply existsb_exists in Hc as [X [HinX HX]]. destruct X as [a' w' v'| | | | | | | | |]; try discriminate.
    apply andb_prop in HX as [HX H3]. apply andb_prop in HX as [H1 H2].
    apply saddr_eqb_eq in H1. apply Nat.eqb_eq in H2. subst a' w'.
    pose proof (proj1 (Forall_forall _ _) HK _ HinX) as HKX.
    pose proof (respell_ok_sound E M k v' v HK H3) as Heq.
    cbn [kentry_ok] in HKX |- *. rewrite <- Heq. exact HKX. }
  destruct (kflat_h k K) eqn:Hfl.
  - destruct (existsb (fun X => kentry_eqb_h X K) k) eqn:Hex.
    + apply existsb_exists in Hex as [X [HinX Heq]].
      eapply kentry_eqb_h_sound; [exact HK | exact (proj1 (Forall_forall _ _) HK X HinX) | exact Heq | exact Hfl].
    + destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|].
      destruct (kword_val_h k K) eqn:Hkw; [exact (KWV eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
  - destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|].
    destruct (kword_val_h k K) eqn:Hkw; [exact (KWV eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
Qed.

(* [comment removed for export] *)
Definition is_havoc (lo hi : nat) (t : expr) : option nat :=
  match t with EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool then Some v else None | _ => None end.

Fixpoint henv (lo hi : nat) (E : env) (rs ts : list expr) : env :=
  match rs, ts with
  | r :: rs', t :: ts' =>
      let E1 := henv lo hi E rs' ts' in
      match is_havoc lo hi t with Some v => upd E1 v (edenot E r) | None => E1 end
  | _, _ => E
  end.

Lemma is_havoc_range : forall lo hi t v, is_havoc lo hi t = Some v -> t = EVar v /\ (lo <= v < hi)%nat.
Proof.
  intros lo hi t v H. destruct t; try discriminate. cbn [is_havoc] in H.
  destruct (Nat.leb lo n && Nat.ltb n hi)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. split; [reflexivity | lia].
Qed.

Lemma henv_agree : forall lo hi E rs ts, env_agree lo E (henv lo hi E rs ts).
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts]; cbn [henv]; try apply env_agree_refl.
  destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH].
  apply is_havoc_range in Hv as [_ Hv]. eapply env_agree_trans; [apply IH|]. eapply env_agree_le; [apply upd_agree | lia].
Qed.

Lemma henv_high : forall lo hi E rs ts n, (hi <= n)%nat -> ev (henv lo hi E rs ts) n = ev E n.
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] n Hn; cbn [henv]; try reflexivity.
  destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH; exact Hn].
  apply is_havoc_range in Hv as [_ Hv]. cbn [upd ev]. destruct (Nat.eqb_spec n v); [lia|]. apply IH. exact Hn.
Qed.

(* [comment removed for export] *)
Lemma regs_match_h_char : forall lo hi seen rs ts, regs_match_h lo hi seen rs ts = true ->
  length rs = length ts /\
  forall i, (i < length ts)%nat ->
    (exists v, is_havoc lo hi (nth i ts (ELit 0)) = Some v /\ ~ In v seen /\
               forall i', (i' < i)%nat -> is_havoc lo hi (nth i' ts (ELit 0)) <> Some v)
    \/ (is_havoc lo hi (nth i ts (ELit 0)) = None /\ nth i ts (ELit 0) = nth i rs (ELit 0) /\ AP.expr_vars_lt lo (nth i ts (ELit 0)) = true).
Proof.
  intros lo hi seen rs. revert seen. induction rs as [|r rs IH]; intros seen [|t ts] H; cbn [regs_match_h length] in H |- *; try discriminate.
  - split; [reflexivity | intros i Hi; lia].
  - assert (STEP : forall seen', regs_match_h lo hi seen' rs ts = true -> (forall v, In v seen -> In v seen') ->
              (forall v, is_havoc lo hi t = Some v -> In v seen') ->
              length rs = length ts /\ forall i, (Datatypes.S i < Datatypes.S (length ts))%nat ->
                (exists v, is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = Some v /\ ~ In v seen /\
                   forall i', (i' < Datatypes.S i)%nat -> is_havoc lo hi (nth i' (t :: ts) (ELit 0)) <> Some v)
                \/ (is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = None /\ nth (Datatypes.S i) (t :: ts) (ELit 0) = nth (Datatypes.S i) (r :: rs) (ELit 0)
                    /\ AP.expr_vars_lt lo (nth (Datatypes.S i) (t :: ts) (ELit 0)) = true)).
    { intros seen' Hm Hsub Ht. destruct (IH seen' ts Hm) as [Hlen Hc]. split; [exact Hlen|].
      intros i Hi. cbn [nth]. destruct (Hc i ltac:(lia)) as [[v (Hv & Hns & Hbefore)]|Hn]; [left|right; exact Hn].
      exists v. split; [exact Hv|]. split; [intros Hin; apply Hns; apply Hsub; exact Hin|].
      intros [|i'] Hi'; cbn [nth].
      - intros Heq. apply Hns. apply Ht. exact Heq.
      - apply Hbefore. lia. }
    destruct (is_havoc lo hi t) as [v|] eqn:Hv.
    + destruct t as [|w| | | | | |]; try discriminate. cbn [is_havoc] in Hv.
      destruct (Nat.leb lo w && Nat.ltb w hi)%bool eqn:Hr; [|discriminate]. injection Hv as Hwv. subst v.
      apply andb_prop in H as [Hnew Hm]. apply negb_true_iff in Hnew.
      assert (Hns : ~ In w seen).
      { intros Hin. enough (existsb (Nat.eqb w) seen = true) by congruence. apply existsb_exists. exists w. split; [exact Hin | apply Nat.eqb_refl]. }
      destruct (STEP (w :: seen) Hm ltac:(intros; right; assumption) ltac:(intros v' Hv'; injection Hv' as <-; left; reflexivity)) as [Hlen Hc].
      split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
      left. exists w. cbn [nth is_havoc]. rewrite Hr. split; [reflexivity|]. split; [exact Hns|]. intros i' Hi'. lia.
    + assert (Hm : (expr_eqb r t && AP.expr_vars_lt lo t && regs_match_h lo hi seen rs ts)%bool = true).
      { destruct t; try exact H. cbn [is_havoc] in Hv. destruct (Nat.leb lo n && Nat.ltb n hi)%bool; [discriminate | exact H]. }
      apply andb_prop in Hm as [Hm1 Hm]. apply andb_prop in Hm1 as [He Hvl]. apply expr_eqb_eq in He. subst t.
      destruct (STEP seen Hm ltac:(intros; assumption) ltac:(intros v' Hv'; discriminate Hv')) as [Hlen Hc].
      split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
      right. cbn [nth]. split; [exact Hv|]. split; [reflexivity | exact Hvl].
Qed.

Lemma henv_havoc : forall lo hi E rs ts i v,
  length rs = length ts -> (i < length ts)%nat ->
  is_havoc lo hi (nth i ts (ELit 0)) = Some v ->
  (forall i', (i' < i)%nat -> is_havoc lo hi (nth i' ts (ELit 0)) <> Some v) ->
  ev (henv lo hi E rs ts) v = edenot E (nth i rs (ELit 0)).
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] i v Hlen Hi Hv Hbefore; cbn [length] in *; try lia.
  cbn [henv]. destruct i as [|i]; cbn [nth] in *.
  - rewrite Hv. apply upd_at.
  - destruct (is_havoc lo hi t) as [v'|] eqn:Ht.
    + cbn [upd ev]. destruct (Nat.eqb_spec v v').
      * subst v'. exfalso. exact (Hbefore 0%nat ltac:(lia) Ht).
      * apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
    + apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
Qed.

Lemma regs_match_h_sound : forall lo hi E rs ts R,
  regs_match_h lo hi [] rs ts = true -> length ts = 32%nat -> regs_ok E rs R -> regs_ok (henv lo hi E rs ts) ts R.
Proof.
  intros lo hi E rs ts R H Hlen HR. destruct (regs_match_h_char lo hi [] rs ts H) as [Hl Hc].
  intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [exact (eq_trans (HR r) ltac:(unfold sr_get; rewrite Hr0; reflexivity))|].
  pose proof (ridx_range r) as Hlt. specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. rewrite HR.
  destruct (Hc (ridx r) ltac:(lia)) as [[v (Hv & _ & Hbefore)]|(Hn & Heq & Hvl)].
  - destruct (is_havoc_range _ _ _ _ Hv) as [Et _]. rewrite Et. cbn [edenot]. symmetry. apply (henv_havoc lo hi E rs ts (ridx r) v Hl ltac:(lia) Hv Hbefore).
  - rewrite Heq in Hvl |- *. eapply (edenot_agree' lo); [apply henv_agree | exact Hvl].
Qed.

(* [comment removed for export] *)
Lemma cs_ok_reenv : forall b E E' cs sr' R FULL model,
  cs_ok E cs R FULL model -> env_agree b E E' -> (nx0 <= b)%nat ->
  AP.kn_vars_lt b (kn cs) = true -> maps_vars_lt b (a_maps cs) = true -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  AP.expr_vars_lt b (a_brk cs) = true -> fd_vars_lt b (a_fd cs) = true ->
  regs_ok E' sr' R ->
  cs_ok E' (set_regs cs sr') R FULL model.
Proof.
  intros b E E' cs sr' R FULL model HC Hag Hb Hkn Hmaps Hallow Hbrk Hfd HR.
  pose proof (hid_agree b E E' cs model Hag Hb Hallow) as HH.
  rewrite <- (hid_ext E' cs (set_regs cs sr') model eq_refl) in HH.
  pose proof (allowA_agree b E E' cs Hag Hallow) as HA.
  assert (HA2 : allowA E' (set_regs cs sr') = allowA E' cs) by reflexivity. rewrite <- HA2 in HA. clear HA2.
  destruct HC; constructor; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset] in *;
    rewrite ?HA; try assumption; try reflexivity.
  - unfold Mr in *. rewrite HH. eapply know_ok_agree'; eassumption.
  - eapply fds_ok_agree; eassumption.
  - eapply maps_match_agree; [exact Hag | exact Hmaps | assumption].
  - eapply holes_agree; [exact Hag | exact Hmaps | assumption].
  - apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
    exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2) in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite <- (edenot_agree' b E E' _ Hag Hbrk). assumption.
  - intros a. rewrite HH. change (in_ghost E' (set_regs cs sr')) with (in_ghost E' cs). rewrite (in_ghost_agree b E E' cs Hag Hallow). exact (co_zero0 a).
  - eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Hb] | assumption].
Qed.

Lemma entails_h_sound : forall lo hi E cs T R FULL model,
  cs_ok E cs R FULL model -> entails_h A lo hi cs T = true -> (nx0 <= lo)%nat -> length (s_regs (a_ss T)) = 32%nat ->
  exists E', env_agree lo E E' /\ (forall n, (hi <= n)%nat -> ev E' n = ev E n) /\ cs_ok E' T R FULL model /\ pc T = pc cs.
Proof.
  intros lo hi E cs T R FULL model HC H Hlo Hlen. unfold entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => rename Hl into HRV; destruct (s_resv (a_ss T)) eqn:HRV'; [discriminate|clear HRV; rename HRV' into HRV] end.
  match goal with Hr : regs_match_h _ _ _ _ _ = true |- _ => rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : kn_incl_h _ _ (kn T) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  set (E' := henv lo hi E (s_regs (a_ss cs)) (s_regs (a_ss T))).
  exists E'. split; [apply henv_agree|]. split; [intros; apply henv_high; assumption|]. split; [|symmetry; exact Hpc].
  (* [comment removed for export] *)
  set (Tc := set_regs T (s_regs (a_ss cs))).
  assert (Evis : a_vis Tc = a_vis cs) by (unfold Tc; cbn [set_regs with_ss a_vis]; symmetry; exact Hallow).
  assert (HA : allowA E Tc = allowA E cs) by (unfold allowA; unfold Tc; cbn [set_regs with_ss a_vis a_ghost]; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E Tc model = hid E cs model) by (apply hid_ext; exact Evis).
  assert (HC1 : cs_ok E Tc R FULL model).
  { destruct HC; constructor; rewrite ?HA;
      try (unfold Tc; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
           rewrite <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hbrk, <- ?Hfd, <- ?Htid; first [assumption | reflexivity | lia]).
    - unfold Mr. rewrite HH. eapply kn_incl_h_sound; [exact co_know0 | exact Hkn].
    - unfold Tc. cbn [set_regs with_ss a_maps a_ylo]. rewrite <- Hmaps. eapply holes_mono; [exact co_holes0 | lia].
    - destruct co_split0 as [Y HY]. exists Y. split; [unfold Tc; cbn [set_regs with_ss a_ylo]; lia | apply HY].
    - intros a. rewrite HH. replace (in_ghost E Tc) with (in_ghost E cs) by (unfold in_ghost, Tc; cbn [set_regs with_ss a_ghost]; rewrite Hghost; reflexivity).
      exact (co_zero0 a). }
  (* [comment removed for export] *)
  assert (ET : T = set_regs Tc (s_regs (a_ss T))).
  { subst Tc. clear - HL HRV. destruct T as [[p sr lg k nx rv] m t y e v g ab br f ti]. cbn in HL, HRV. subst lg rv. reflexivity. }
  rewrite ET at 1. eapply (cs_ok_reenv lo); try eassumption.
  - apply henv_agree.
  - unfold pairs_vars_lt, Tc. cbn [set_regs with_ss a_vis a_ghost]. rewrite forallb_app. apply andb_true_intro; split; assumption.
  - apply regs_match_h_sound; [exact Hregs | exact Hlen | exact (co_regs _ _ _ _ _ HC)].
Qed.

(* [comment removed for export] *)
Lemma diamond_join_sound : forall nx joinpc rs ca cb csj,
  node_diamond_join A nx0 nx joinpc rs ca cb = Some csj ->
  (forall E R FULL model, cs_ok E ca R FULL model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj R FULL model /\ pc csj = pc ca)
  /\ (forall E R FULL model, cs_ok E cb R FULL model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj R FULL model /\ pc csj = pc cb).
Proof.
  intros nx joinpc rs ca cb csj H. unfold node_diamond_join in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  match goal with Hl : Nat.eqb (length ?l) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
  match goal with Hl : Nat.leb nx0 ?v = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hn0 end.
  split; intros E R FULL model HC.
  - match goal with Hea : entails_h A ?lo ?hi ca ?T = true |- _ =>
      destruct (entails_h_sound lo hi E ca T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
  - match goal with Hea : entails_h A ?lo ?hi cb ?T = true |- _ =>
      destruct (entails_h_sound lo hi E cb T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
Qed.

Lemma loop_ok_facts : forall cs J N inv nhi,
  loop_ok nx0 cs J N inv = Some nhi ->
  fresh_ok nx0 cs = true /\ (nxt cs <= J)%nat /\ (J < nxt inv)%nat /\ s_log (a_ss inv) = [] /\
  length (s_regs (a_ss inv)) = 32%nat /\ AP.expr_vars_lt (nxt cs) N = true /\
  xhi (kn cs) N = Some nhi /\ nhi < two64.
Proof.
  intros cs J N inv nhi H. unfold loop_ok in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (xhi (kn cs) N) as [h|] eqn:Hx; [|discriminate]. destruct (Z.ltb h two64) eqn:Hlt; [|discriminate]. injection H as <-.
  apply Z.ltb_lt in Hlt.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  apply Nat.leb_le in X4. apply Nat.ltb_lt in X3.
  destruct (s_log (a_ss inv)); [|discriminate]. apply Nat.eqb_eq in X.
  repeat split; try assumption; reflexivity.
Qed.

Lemma pc_inst : forall inv J e, pc (inst inv J e) = pc inv.
Proof. reflexivity. Qed.
Lemma nxt_inst : forall inv J e, nxt (inst inv J e) = nxt inv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma check_all_ok : forall (chk : acs -> plan -> cres) k css s,
  check_all A chk k css = COk s ->
  (exists cs1, In cs1 css /\ chk cs1 k = COk s /\ True) /\ (forall cs, In cs css -> chk cs k = COk s).
Proof.
  intros chk k css s H. unfold check_all in H. destruct css as [|cs0 rest]; [discriminate|].
  destruct (chk cs0 k) as [s0|] eqn:H0; [|discriminate].
  match type of H with fold_left ?F rest (COk s0) = _ =>
  assert (GEN : forall l acc, fold_left F l acc = COk s ->
                 acc = COk s /\ forall cs, In cs l -> chk cs k = COk s) end.
  { induction l as [|c l IHl]; intros acc Hf; cbn [fold_left] in Hf.
    - split; [exact Hf | intros ? []].
    - destruct acc as [s1|c1 q1 r1].
      + destruct (chk c k) as [s'|] eqn:Hc'; [| apply IHl in Hf as [Hf _]; discriminate].
        destruct (shape_eqb s1 s') eqn:Hse; [| apply IHl in Hf as [Hf _]; discriminate].
        apply IHl in Hf as [E1 Hl]. injection E1 as ->. apply shape_eqb_eq in Hse. subst s'.
        split; [reflexivity|]. intros cs [<-|Hin]; [exact Hc' | apply Hl; exact Hin].
      + apply IHl in Hf as [Hf _]. discriminate. }
  apply GEN in H as [E0 Hrest]. injection E0 as ->.
  split; [exists cs0; split; [left; reflexivity | split; [exact H0 | exact I]]|].
  intros cs [<-|Hin]; [exact H0 | apply Hrest; exact Hin].
Qed.

(* [comment removed for export] *)
Lemma check_next_vars : forall lc cs p w s, AP.check_next A lc cs p w = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros lc cs p w s Hc. unfold AP.check_next in Hc. destruct lc as [[h nx lo hi hx|j' js' sk' b' lo' jx']|]; [|discriminate|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection Hc as <-. reflexivity.
Qed.
Lemma check_merge_vars : forall lc cs p j w s, AP.check_merge A nx0 lc cs p j w = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros lc cs p j w s Hc. unfold AP.check_merge in Hc. destruct lc as [[h nx lo hi hx|j' js' sk' b' lo' jx']|]; [discriminate| |discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Ht; [|discriminate] end.
  injection Hc as <-. apply andb_prop in Ht as [Ht _]. apply andb_prop in Ht as [_ Hsv]. exact Hsv.
Qed.
Lemma check_each_first : forall chk p cs0 css s,
  AP.check_each chk p cs0 css = COk s -> exists cs k, In (cs, k) css /\ chk cs k = COk s.
Proof.
  intros chk p cs0 css s Hc. destruct css as [|[c ck] rest]; [discriminate|]. cbn [AP.check_each] in Hc.
  destruct rest as [|c2 rest2].
  - exists c, ck. split; [left; reflexivity | exact Hc].
  - destruct (chk c ck) as [s1|] eqn:H1; [|discriminate].
    destruct (AP.check_each chk p cs0 (c2 :: rest2)); [|discriminate]. destruct (AP.shape_eqv s1 _); [|discriminate].
    injection Hc as <-. exists c, ck. split; [left; reflexivity | exact H1].
Qed.
Lemma check_loop_vars : forall bfuel fuel lc cs p J N alts w s,
  (forall lc p cs s, CHECK bfuel fuel lc cs p = COk s -> shape_vars_lt nx0 s = true) ->
  AP.check_loop A nx0 (CHECK bfuel fuel) lc cs p J N alts w = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel lc cs p J N alts w s IH Hc. unfold AP.check_loop in Hc.
  destruct (AP.loop_okM nx0 cs J N alts) as [nhi|]; [|discriminate]. destruct alts as [|a0 rest]; [discriminate|]. cbv zeta in Hc.
  match type of Hc with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  match type of Hc with context [AP.check_each ?f ?pp ?c0 ?l] => destruct (AP.check_each f pp c0 l) as [sk|] eqn:Hk; [|discriminate] end.
  cbv zeta in Hc.
  match type of Hc with context [AP.check_bodies ?f ?pp ?c0 ?l] => destruct (AP.check_bodies f pp c0 l) as [sb|]; [|discriminate] end.
  destruct sb; try discriminate.
  destruct (check_each_first _ _ _ _ _ Hk) as (c1 & k1 & _ & Hk1).
  destruct (lc_xmode lc && next_or_holes sk)%bool; injection Hc as <-; [reflexivity | exact (IH _ _ _ _ Hk1)].
Qed.
Lemma check_via_vars : forall bfuel fuel lc cs p j alts lo karms s,
  (forall lc p cs s, CHECK bfuel fuel lc cs p = COk s -> shape_vars_lt nx0 s = true) ->
  AP.check_via nx0 (CHECK bfuel fuel) lc cs p j alts lo karms = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel lc cs p j alts lo karms s IH Hc. unfold AP.check_via in Hc.
  match type of Hc with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  match type of Hc with context [AP.check_each ?f ?pp ?c0 ?l] => destruct (AP.check_each f pp c0 l) as [sk|]; [|discriminate] end.
  exact (IH _ _ _ _ Hc).
Qed.

Lemma check_branch_vars : forall bfuel fuel lc cs p e k1 k2 s,
  (forall lc p cs s, CHECK bfuel fuel lc cs p = COk s -> shape_vars_lt nx0 s = true) ->
  AP.check_branch (CHECK bfuel fuel lc) cs p e k1 k2 = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel lc cs p e k1 k2 s IH Hc. unfold AP.check_branch in Hc.
  destruct (brange (kn cs) e) as [[lo hi]|]; [|discriminate].
  destruct (Z.leb lo 0 && Z.ltb 0 hi)%bool.
  2: { cbn [negb] in Hc. destruct (Z.leb hi 0); [exact (IH _ _ _ s Hc) | exact (IH _ _ _ s Hc)]. }
  cbn [negb] in Hc.
  destruct (kn_contra (kn (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)))); [exact (IH _ _ _ s Hc)|].
  destruct (kn_contra (kn (set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)))); [exact (IH _ _ _ s Hc)|].
  destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
  destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (0+1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
  destruct (AP.shape_eqv s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ _ _ s1 H1).
Qed.

Lemma check_vars : forall bfuel fuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel. induction fuel as [|fuel IH]; intros lc p cs s Hc; [discriminate|].
  cbn [AP.check] in Hc. rewrite ?fact_okM_fe, ?factle_okM_fe in Hc.
  match type of Hc with (if ?g then _ else _) = _ => destruct g; [discriminate|] end.
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lw lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc|nw|mwj mww|bkf bkt|crr crmid crk1 crk2|fve fvv fvlo fvhi fvk|hwh hww|fle flb flhi flk|fse fsc fshi fsk|flr flo flb2 flh2 flk2|frr fro frlo frhi frk|fxr fxph fxe fxb fxhi fxk|gxr gxph gxe gxlo gxhi gxk|cth|mJ mN malts mw|wj walts wlo wka|bpz bpnz|aid aargs ak1 ak2].
  - destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (brange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { destruct (Z.leb hi mid); [exact (IH _ k1 _ s Hc) | exact (IH _ k2 _ s Hc)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. rewrite Hv, (IH _ k1 _ s1 H1), (IH _ k2 _ s2 H2). reflexivity.
  - destruct (brange (kn cs) ce) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (IH _ ck1 _ s Hc) | exact (IH _ ck2 _ s Hc)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))); [exact (IH _ ck2 _ s Hc)|].
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))); [exact (IH _ ck1 _ s Hc)|].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ ck1 _ s1 H1).
  - destruct (node_casedisj cs db1 db2) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ dk1 _ s1 H1).
  - destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (fact_ok (kn cs) K); [|discriminate]. exact (IH _ k _ s Hc).
  - destruct (node_join SEGS cs jb joff jn) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - destruct (node_bump cs bm) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_havoc nx0 cs hrs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_havocbig nx0 cs hbK) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_fresh nx0 cs r logc fb) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_sys A nx0 y cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmap2 A nx0 LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ma) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb mb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. apply salt2_vars; [exact (IH _ ma _ sa H1) | exact (IH _ mb _ sb H2)].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ia) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ib) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A (CHECK bfuel fuel lc) ic cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    destruct (check_all_ok _ _ _ _ H3) as [(cs1 & Hin1 & Hc1 & _) _].
    apply salt2_vars; [exact (IH _ ia _ sa H1) | apply salt2_vars; [exact (IH _ ib _ sb H2) | exact (IH _ ic _ sc Hc1)]].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa qa) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb qb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. apply salt2_vars; [exact (IH _ qa _ sa H1) | exact (IH _ qb _ sb H2)].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_brk2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ka) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. apply salt2_vars; [exact (IH _ ka _ sa H1) | exact (IH _ kb _ sb H2)].
  - destruct (node_x SEGS A nx0 x args cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (XN xid xargs cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (XE eid eargs cs) as [[[fd ps] cs1]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. exact (IH _ k cs1 s1 H1).
  - destruct (XB bid bargs cs) as [[csa csb]|]; [|discriminate].
    destruct (kn_contra (kn csa)); [exact (IH _ kb2 _ s Hc)|].
    destruct (kn_contra (kn csb)); [exact (IH _ kb1 _ s Hc)|].
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv sa sb); [|discriminate]. injection Hc as <-. exact (IH _ kb1 _ sa H1).
  - eapply check_loop_vars; [exact IH | exact Hc].
  - eapply check_next_vars; exact Hc.
  - unfold AP.check_handoff in Hc. destruct (HS h) as [ch|]; [|discriminate].
    destruct (entails cs ch ||| entails_tw A nx0 (nxt ch) [] cs ch)%bool; [|discriminate]. injection Hc as <-.
    destruct lc as [[h0 nx0' lo0 hi0 [|]|j0 js0 sk0 b0 lo0 [|]]|]; reflexivity.
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_exit cs); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (node_spin SEGS cs); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (node_fog cs fi fsz) as [cs1|]; [|discriminate]. exact (IH _ fk cs1 s Hc).
  - destruct (node_fognew cs gi gsz) as [cs1|]; [|discriminate]. exact (IH _ gk cs1 s Hc).
  - destruct (node_ghost LIMIT cs gb gn) as [cs1|]; [|discriminate]. exact (IH _ gk2 cs1 s Hc).
  - destruct (node_unvis A cs ub un) as [cs1|]; [|discriminate]. exact (IH _ uk cs1 s Hc).
  - destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|]; [|discriminate]. exact (IH _ hk cs1 s Hc).
  - destruct (node_intro nx0 cs ilo ihi) as [cs1|]; [|discriminate]. exact (IH _ ik cs1 s Hc).
  - destruct (branch_probe IT cs) as [e|]; [|discriminate].
    destruct (brange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.ltb hi 1 ||| Z.ltb 0 lo)%bool.
    { destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|]; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate]. exact (IH _ dk cs1 s Hc). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|]; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|]; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|]; [|discriminate]. exact (IH _ dk csj s Hc).
  - destruct (node_rename _ cs rnm) as [cs1|]; [|discriminate]. exact (IH _ rnk cs1 s Hc).
  - destruct (node_compact _ cs) as [cs1|]; [|discriminate]. exact (IH _ cpk cs1 s Hc).
  - eapply check_via_vars; [exact IH | exact Hc].
  - eapply check_merge_vars; exact Hc.
  - destruct (node_abstractcell A cs ab an) as [cs1|]; [|discriminate]. exact (IH _ ak cs1 s Hc).
  - destruct (node_havocwords nx0 cs hws) as [cs1|]; [|discriminate]. exact (IH _ hwk cs1 s Hc).
  - destruct (node_respell cs rsr rse) as [cs1|]; [|discriminate]. exact (IH _ rsk cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT true cs) as [[[csa csb] cscs]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa iha) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ihb) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A (CHECK bfuel fuel lc) ihc cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    destruct (check_all_ok _ _ _ _ H3) as [(cs1 & Hin1 & Hc1 & _) _].
    apply salt2_vars; [exact (IH _ iha _ sa H1) | apply salt2_vars; [exact (IH _ ihb _ sb H2) | exact (IH _ ihc _ sc Hc1)]].
  - (* [comment removed for export] *)
    eapply check_next_vars; exact Hc.
  - (* [comment removed for export] *)
    eapply check_merge_vars; exact Hc.
  - (* [comment removed for export] *)
    destruct (branch_probe2 IT cs) as [[e pos]|]; [|discriminate]. cbv zeta in Hc.
    eapply check_branch_vars; [exact IH | exact Hc].
  - (* [comment removed for export] *)
    cbv zeta in Hc.
    destruct (brange (kn cs) (reg cs crr)) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo crmid && Z.ltb crmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi crmid); [exact (IH _ crk1 _ s Hc) | exact (IH _ crk2 _ s Hc)]. }
    cbn [negb] in Hc.
    destruct (kn_contra (kn (set_kn cs (KRange (reg cs crr) lo crmid :: kn cs)))); [exact (IH _ crk2 _ s Hc)|].
    destruct (kn_contra (kn (set_kn cs (KRange (reg cs crr) (crmid + 1) hi :: kn cs)))); [exact (IH _ crk1 _ s Hc)|].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange (reg cs crr) lo crmid :: kn cs)) crk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange (reg cs crr) (crmid+1) hi :: kn cs)) crk2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ crk1 _ s1 H1).
  - (* [comment removed for export] *)
    destruct (factvia_ok (kn cs) fve fvv fvlo fvhi); [|discriminate]. exact (IH _ fvk _ s Hc).
  - (* [comment removed for export] *)
    unfold AP.check_handoff in Hc. destruct (HS hwh) as [ch|]; [|discriminate].
    destruct (entails cs ch ||| entails_tw A nx0 (nxt ch) hww cs ch)%bool; [|discriminate]. injection Hc as <-.
    destruct lc as [[h0 nx0' lo0 hi0 [|]|j0 js0 sk0 b0 lo0 [|]]|]; reflexivity.
  - (* [comment removed for export] *)
    destruct (factle_ok (kn cs) fle flb flhi); [|discriminate]. exact (IH _ flk _ s Hc).
  - (* [comment removed for export] *)
    destruct (factscale_ok (kn cs) fse fsc fshi); [|discriminate]. exact (IH _ fsk _ s Hc).
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (factle_ok (kn cs) (eaddz (reg cs flr) flo) flb2 flh2); [|discriminate]. exact (IH _ flk2 _ s Hc).
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (fact_ok (kn cs) (KRange (eaddz (reg cs frr) fro) frlo frhi)); [|discriminate]. exact (IH _ frk _ s Hc).
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (factle_ok (kn cs) (APC.esubst fxph (reg cs fxr) fxe) (APC.esubst fxph (reg cs fxr) fxb) fxhi); [|discriminate]. exact (IH _ fxk _ s Hc).
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (fact_ok (kn cs) (KRange (APC.esubst gxph (reg cs gxr) gxe) gxlo gxhi)); [|discriminate]. exact (IH _ gxk _ s Hc).
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. destruct (lc_xmode lc); reflexivity.
  - eapply check_loop_vars; [exact IH | exact Hc].
  - eapply check_via_vars; [exact IH | exact Hc].
  - destruct (branch_probe2 IT cs) as [[e pos]|]; [|discriminate]. eapply check_branch_vars; [exact IH | exact Hc].
  - (* [comment removed for export] *)
    destruct (XC aid aargs cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ak1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ak2) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. destruct (shape_eqb sa sb); [exact (IH _ ak1 _ sa H1)|].
    apply salt2_vars; [exact (IH _ ak1 _ sa H1) | exact (IH _ ak2 _ sb H2)].
Qed.



















(* [comment removed for export] *)
Lemma intro_sound : forall E cs R FULL model lo hi cs',
  cs_ok E cs R FULL model -> node_intro nx0 cs lo hi = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model lo hi cs' HC H. unfold node_intro in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 lo)).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : bv_unsigned (edenot E' (EVar v)) = lo).
  { cbn [edenot]. unfold E'. rewrite ext1_at. unfold two64 in H3. apply u_small. lia. }
  set (cs' := with_ss _ _).
  assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
  assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
  destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
    cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  - (* [comment removed for export] *) constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv. lia.
Qed.

(* [comment removed for export] *)
Section Rename.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.

  Lemma mk_fwd_spec_gen : forall m0 t, mk_fwd m0 = Some t -> forall s d, nt_get t s = Some d <-> In (s, d) m0.
  Proof.
    induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_fwd] in H.
    - injection H as <-. unfold nt_get. cbn. split; [destruct s; discriminate | tauto].
    - destruct (mk_fwd rest) as [t0|] eqn:E0; [|discriminate].
      destruct (nt_get t0 s0) eqn:Eg; [discriminate|]. injection H as <-.
      rewrite nt_get_set. specialize (IH t0 eq_refl).
      destruct (Nat.eqb_spec s s0) as [->|NE].
      + split.
        * intros X. injection X as <-. left. reflexivity.
        * intros [X|X]; [congruence|]. apply IH in X. congruence.
      + rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
  Qed.
  Lemma mk_bwd_spec_gen : forall m0 t, mk_bwd m0 = Some t -> forall s d, nt_get t d = Some s <-> In (s, d) m0.
  Proof.
    induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_bwd] in H.
    - injection H as <-. unfold nt_get. cbn. split; [destruct d; discriminate | tauto].
    - destruct (mk_bwd rest) as [t0|] eqn:E0; [|discriminate].
      destruct (nt_get t0 d0) eqn:Eg; [discriminate|]. injection H as <-.
      rewrite nt_get_set. specialize (IH t0 eq_refl).
      destruct (Nat.eqb_spec d d0) as [->|NE].
      + split.
        * intros X. injection X as <-. left. reflexivity.
        * intros [X|X]; [congruence|]. apply IH in X. congruence.
      + rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
  Qed.
  Lemma fw_in : forall s d, nt_get fw s = Some d <-> In (s, d) m.
  Proof. exact (mk_fwd_spec_gen m fw Hfw). Qed.
  Lemma bw_in : forall s d, nt_get bw d = Some s <-> In (s, d) m.
  Proof. exact (mk_bwd_spec_gen m bw Hbw). Qed.

  Definition ren_env (E : env) : env :=
    Env (fun w => match nt_get bw w with Some s => ev E s | None => ev E w end) (eb E).
  Definition ren_ok (v : nat) : bool :=
    match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end.

  Lemma edenot_rename : forall E e, evars_all ren_ok e = true -> edenot (ren_env E) (erename fw e) = edenot E e.
  Proof.
    intros E e. induction e; cbn [evars_all erename edenot]; intros H;
      try reflexivity;
      try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
      try (rewrite (IHe H); reflexivity).
    unfold ren_ok in H. destruct (nt_get fw n) as [d|] eqn:Ef.
    - cbn [edenot ren_env ev]. destruct (nt_get bw d) as [s|] eqn:Eb.
      + apply bw_in in Eb. apply fw_in in Ef. pose proof (proj2 (fw_in _ _) Eb) as Ef'.
        assert (s = n) by (apply bw_in in Eb; apply bw_in in Ef; congruence). subst s. reflexivity.
      + exfalso. apply fw_in in Ef. apply (proj2 (bw_in _ _)) in Ef. congruence.
    - cbn [edenot ren_env ev]. destruct (nt_get bw n) as [s|] eqn:Eb; [discriminate|reflexivity].
  Qed.
End Rename.

Section RenameCS.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.
  Variable gb : nat.
  Hypothesis Hgb : (nx0 <= gb)%nat.
  Hypothesis Hm : forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m = true.

  Let ER := edenot_rename m fw bw Hfw Hbw.

  Lemma ren_agree : forall E, env_agree gb E (ren_env bw E).
  Proof.
    intros E. split; [|reflexivity]. intros n Hn. cbn [ren_env ev].
    destruct (nt_get bw n) as [s|] eqn:Eb; [|reflexivity].
    apply (bw_in m bw Hbw) in Eb. exfalso.
    pose proof (proj1 (forallb_forall _ _) Hm (s, n) Eb) as X. cbn [fst snd] in X.
    apply andb_prop in X as [_ X]. apply Nat.leb_le in X. clear Hgb. lia.
  Qed.

  Lemma uE_rename : forall E e, evars_all (ren_ok fw bw) e = true -> uE (ren_env bw E) (erename fw e) = uE E e.
  Proof. intros. unfold uE. rewrite (ER E e H). reflexivity. Qed.

  Lemma regs_ok_rename : forall E sr R, forallb (evars_all (ren_ok fw bw)) sr = true -> regs_ok E sr R -> regs_ok (ren_env bw E) (map (erename fw) sr) R.
  Proof.
    intros E sr R Hsr HR r. rewrite (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
    revert Hsr. generalize (ridx r) as i. clear HR r.
    induction sr as [|e t IH]; intros i Hsr; [destruct i; reflexivity|].
    cbn [forallb] in Hsr. apply andb_prop in Hsr as [He Ht].
    destruct i as [|i]; cbn [map nth]; [symmetry; exact (ER E e He) | apply IH; exact Ht].
  Qed.

  Lemma eb_ren : forall E, eb (ren_env bw E) = eb E.
  Proof. reflexivity. Qed.

  Lemma kentry_ok_rename : forall E M K, kvars_all (ren_ok fw bw) K = true -> kentry_ok SEGS E M K -> kentry_ok SEGS (ren_env bw E) M (krename fw K).
  Proof.
    intros E M K HK Hk.
    destruct K as [[ab ak] w v|[ab ak] n|[ab ak] n k|lo hi|ae am|re rlo rhi|[ab ak] wn|[b1 k1] dn1 [b2 k2] dn2|[ab ak] n fc|[ab ak] n];
      unfold krename, arename in *; cbn [kvars_all kentry_ok a_base a_off] in *;
      repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H as [? H] end;
      unfold flat, estart, elenZ, adenot in *; cbn [a_base a_off] in *;
      rewrite ?eb_ren; rewrite ?(ER E) by assumption; exact Hk.
  Qed.

  Lemma know_ok_rename : forall E M k, forallb (kvars_all (ren_ok fw bw)) k = true ->
    know_ok SEGS E M k -> know_ok SEGS (ren_env bw E) M (map (krename fw) k).
  Proof.
    intros E M k. induction k as [|K rest IH]; intros Hv Hk; [constructor|].
    cbn [forallb] in Hv. apply andb_prop in Hv as [H1 H2]. apply Forall_cons_iff in Hk as [HK Hr].
    cbn [map]. constructor; [apply kentry_ok_rename; assumption | apply IH; assumption].
  Qed.

  Definition pvars_all (l : list (expr * expr)) : bool :=
    forallb (fun p => evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p)) l.

  Lemma allowA_rename : forall E cs nx,
    pvars_all (a_vis cs) = true -> pvars_all (a_ghost cs) = true ->
    allowA (ren_env bw E) (rename_cs fw cs nx) = allowA E cs.
  Proof.
    intros E cs nx Hv Hg. unfold allowA. cbn [rename_cs a_vis a_ghost]. rewrite <- map_app, !flat_map_concat_map, map_map. f_equal.
    apply map_ext_in. intros p Hin.
    assert (Hp : (evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p))%bool = true).
    { apply in_app_iff in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) Hv p Hin) | exact (proj1 (forallb_forall _ _) Hg p Hin)]. }
    apply andb_prop in Hp as [H1 H2].
    unfold allow1, sh_lo, sh_hi, prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
  Qed.

  Lemma existsb_map : forall (X Y : Type) (f : X -> Y) (P : Y -> bool) l, existsb P (map f l) = existsb (fun x => P (f x)) l.
  Proof. intros X Y f P l. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
  Lemma existsb_ext_in : forall (X : Type) (P Q : X -> bool) l, (forall x, In x l -> P x = Q x) -> existsb P l = existsb Q l.
  Proof. intros X P Q l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.

  Lemma in_allow_rename : forall E cs nx, pvars_all (a_vis cs) = true ->
    in_allow (ren_env bw E) (rename_cs fw cs nx) = in_allow E cs.
  Proof.
    intros E cs nx Hv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. cbn [rename_cs a_vis].
    rewrite !existsb_map. f_equal; apply existsb_ext_in; intros p Hin;
      pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp; apply andb_prop in Hp as [H1 H2];
      unfold sh_lo, sh_hi, prename; cbn [fst snd]; rewrite !(uE_rename E) by assumption; reflexivity.
  Qed.

  Lemma in_ghost_rename : forall E cs nx, pvars_all (a_ghost cs) = true ->
    in_ghost (ren_env bw E) (rename_cs fw cs nx) = in_ghost E cs.
  Proof.
    intros E cs nx Hg. apply functional_extensionality. intros z. unfold in_ghost. cbn [rename_cs a_ghost].
    rewrite existsb_map. apply existsb_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hg p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
  Qed.

  Lemma hid_rename : forall E cs nx model, pvars_all (a_vis cs) = true ->
    hid (ren_env bw E) (rename_cs fw cs nx) model = hid E cs model.
  Proof.
    intros E cs nx model Hv. apply functional_extensionality. intros a. unfold hid, vis.
    rewrite (in_allow_rename E cs nx Hv). rewrite <- (argH_agree E (ren_env bw E) a); [reflexivity|].
    eapply env_agree_le; [apply ren_agree | exact Hgb].
  Qed.

  Lemma maps_match_rename : forall E ms l,
    forallb (fun m0 => evars_all (ren_ok fw bw) (am_base m0) && evars_all (ren_ok fw bw) (am_len m0)) ms = true ->
    maps_match E ms l -> maps_match (ren_env bw E) (map (mrename fw) ms) l.
  Proof.
    intros E ms. induction ms as [|[mb ml mk] ms IH]; intros l H HM; cbn [maps_match map] in *; [exact HM|].
    cbn [forallb am_base am_len] in H. apply andb_prop in H as [Hm0 Hr]. apply andb_prop in Hm0 as [H1 H2].
    unfold mrename, is_fog, amap_den in *. cbn [am_kind am_base am_len] in *.
    rewrite ?(uE_rename E) by assumption. rewrite ?(ER E) by assumption.
    destruct (is_tok_kind mk).
    - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hr HM) | right].
      exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hr HM)].
    - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hr HM)].
  Qed.
  (* [comment removed for export] *)
  Lemma holes_rename : forall E y l ms,
    forallb (fun m0 => evars_all (ren_ok fw bw) (am_base m0) && evars_all (ren_ok fw bw) (am_len m0)) ms = true ->
    Forall (hole_ok E y l) ms -> Forall (hole_ok (ren_env bw E) y l) (map (mrename fw) ms).
  Proof.
    intros E y l ms H HF. apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) H m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
    unfold hole_ok, is_hole, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(uE_rename E) by assumption.
    exact (proj1 (Forall_forall _ _) HF m1 Hin Hk).
  Qed.

  Lemma fds_ok_rename : forall E f model,
    match f with FdFile _ l o => evars_all (ren_ok fw bw) l && evars_all (ren_ok fw bw) o | _ => true end%bool = true ->
    fds_ok E f model -> fds_ok (ren_env bw E) (frename fw f) model.
  Proof.
    intros E f model Hv H. destruct f as [|k len off|]; try exact H.
    apply andb_prop in Hv as [Hl Ho]. cbn [frename].
    destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
    rewrite !(uE_rename E) by assumption. rewrite !(ER E) by assumption. rewrite eb_ren. repeat split; assumption.
  Qed.

  Lemma cs_ok_rename : forall E cs R FULL model nx,
    csvars_all (ren_ok fw bw) cs = true -> s_log (a_ss cs) = [] ->
    cs_ok E cs R FULL model -> cs_ok (ren_env bw E) (rename_cs fw cs nx) R FULL model.
  Proof.
    intros E cs R FULL model nx Hv Hlog HC.
    unfold csvars_all in Hv.
    apply andb_prop in Hv as [Hv Hfd]. apply andb_prop in Hv as [Hv Hbrk]. apply andb_prop in Hv as [Hv Hgh].
    apply andb_prop in Hv as [Hv Hvis]. apply andb_prop in Hv as [Hv Hmaps]. apply andb_prop in Hv as [Hregs Hkn].
    pose proof (hid_rename E cs nx model Hvis) as HH.
    pose proof (allowA_rename E cs nx Hvis Hgh) as HA.
    assert (HMr : Mr (ren_env bw E) (rename_cs fw cs nx) model FULL = Mr E cs model FULL) by (unfold Mr; rewrite HH; reflexivity).
    destruct HC; constructor; cbn [rename_cs a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
      rewrite ?HA, ?HMr; try assumption.
    - apply regs_ok_rename; assumption.
    - reflexivity.
    - apply know_ok_rename; assumption.
    - apply fds_ok_rename; assumption.
    - apply maps_match_rename; assumption.
    - apply holes_rename; assumption.
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold amap_den, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) by assumption.
      exact (proj1 (Forall_forall _ _) co_none0 m1 Hin Hk).
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk a Ha. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) in Ha by assumption.
      exact (proj1 (Forall_forall _ _) co_kinds0 m1 Hin Hk a Ha).
    - rewrite (ER E) by assumption. assumption.
    - intros a. rewrite HH, (in_ghost_rename E cs nx Hgh). exact (co_zero0 a).
    - eapply SINV_agree; [eapply env_agree_le; [apply ren_agree | exact Hgb] | assumption].
  Qed.
End RenameCS.

Lemma rename_sound : forall gb E cs R FULL model m cs',
  (nx0 <= gb)%nat -> cs_ok E cs R FULL model -> node_rename gb cs m = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros gb E cs R FULL model m cs' Hgb HC H. unfold node_rename in H.
  destruct (forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m) eqn:Hm; [|discriminate].
  destruct (mk_fwd m) as [fw|] eqn:Hfw; [|discriminate].
  destruct (mk_bwd m) as [bw|] eqn:Hbw; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. apply andb_prop in Hc as [Hv Hlog].
  exists (ren_env bw E). split; [exact (ren_agree m bw Hbw gb Hm E)|]. split; [|reflexivity].
  match goal with |- cs_ok _ (with_ss _ (mk_ss _ _ _ ?NX)) _ _ _ =>
    change (cs_ok (ren_env bw E) (rename_cs fw cs NX) R FULL model) end.
  apply (cs_ok_rename m fw bw Hfw Hbw gb Hgb Hm); [exact Hv | exact (co_log _ _ _ _ _ HC) | exact HC].
Qed.

Lemma compact_sound : forall gb E cs R FULL model cs',
  (nx0 <= gb)%nat -> cs_ok E cs R FULL model -> node_compact gb cs = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof. intros gb E cs R FULL model cs' Hgb HC H. unfold node_compact in H. eapply rename_sound; eassumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma abstractcell_sound : forall E cs R FULL model b n cs',
  cs_ok E cs R FULL model -> node_abstractcell A cs b n = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model b n cs' HC H. unfold node_abstractcell in H.
  destruct (split_lit b) as [bb bo]. cbv zeta in H.
  destruct (kunk_covered A (kn cs) (KUnk (SA bb bo) (ELit n))) eqn:Hcov; [|discriminate].
  injection H as <-. split; [|apply pc_set_kn].
  apply cs_ok_set_kn; [exact HC|]. constructor.
  - eapply kunk_covered_sound; [exact (co_know _ _ _ _ _ HC) | exact Hcov].
  - eapply know_ok_cutout; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity].
Qed.

Lemma hw_apply_true_incl : forall r a x K, In K (hw_apply r a x true) -> In K r.
Proof.
  induction r as [|X r IH]; intros a x K H; [exact H|]. cbn [hw_apply] in H.
  destruct X as [a' w v| | | | | | | | |]; cbn in H;
    try (destruct H as [H|H]; [left; exact H | right; eapply IH; exact H]).
  destruct (saddr_eqb a' a); [right; eapply IH; exact H|].
  destruct H as [H|H]; [left; exact H | right; eapply IH; exact H].
Qed.

Lemma hw_apply_true_vars : forall r a x b, AP.kn_vars_lt b r = true -> AP.kn_vars_lt b (hw_apply r a x true) = true.
Proof.
  induction r as [|X r IH]; intros a x b H; [reflexivity|]. cbn [AP.kn_vars_lt] in H. apply andb_prop in H as [HX Hr].
  cbn [hw_apply]. destruct X as [a' w v| | | | | | | | |]; cbn [AP.kn_vars_lt]; rewrite ?HX, ?(IH a x b Hr); try reflexivity.
  destruct (saddr_eqb a' a); [exact (IH a x b Hr)|]. cbn [AP.kn_vars_lt]. rewrite HX, (IH a x b Hr). reflexivity.
Qed.

Lemma hw_apply_ok : forall E M k a x,
  know_ok SEGS E M k -> AP.kn_vars_lt x k = true ->
  know_ok SEGS (upd E x (edenot E (hw_val k a))) M (hw_apply k a x false)
  /\ AP.kn_vars_lt (Datatypes.S x) (hw_apply k a x false) = true.
Proof.
  intros E M k a x. induction k as [|X r IH]; intros HK Hv.
  - split; [constructor | reflexivity].
  - apply Forall_cons_iff in HK as [HX Hr]. cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [HvX Hvr].
    assert (AG : forall e, env_agree x E (upd E x e)) by (intros; apply upd_agree).
    assert (KEEP : forall e, kentry_ok SEGS (upd E x e) M X).
    { intros e. apply (@Forall_inv _ (kentry_ok SEGS (upd E x e) M) X []).
      eapply (know_ok_agree' x); [apply AG | | constructor; [exact HX | constructor]].
      cbn [AP.kn_vars_lt]. rewrite HvX. reflexivity. }
    assert (KEEPV : AP.kentry_vars_lt (Datatypes.S x) X = true) by (eapply kentry_vars_lt_mono; [exact HvX | lia]).
    cbn [hw_apply hw_val].
    destruct X as [a' w v| | | | | | | | |];
      try (destruct (IH Hr Hvr) as [IH1 IH2]; split; [constructor; [apply KEEP | exact IH1] | cbn [AP.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity]).
    destruct (saddr_eqb a' a) eqn:Hs.
    + (* [comment removed for export] *)
      split.
      * constructor.
        -- cbn [kentry_ok] in HX |- *. destruct HX as (Hw & Hf & Hrd).
           cbn [AP.kentry_vars_lt AP.saddr_vars_lt] in HvX. apply andb_prop in HvX as [Hva Hvv].
           assert (Ea : adenot (upd E x (edenot E v)) a' = adenot E a').
           { unfold adenot. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
           assert (Es : estart (upd E x (edenot E v)) a' = estart E a').
           { unfold estart. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
           split; [exact Hw|]. split; [unfold flat in *; rewrite ?Es; exact Hf|].
           rewrite Ea. cbn [edenot]. rewrite upd_at. exact Hrd.
        -- eapply (know_ok_agree' x); [apply AG | apply hw_apply_true_vars; exact Hvr |].
           apply Forall_forall. intros K HK'. apply hw_apply_true_incl in HK'. exact (proj1 (Forall_forall _ _) Hr K HK').
      * cbn [AP.kn_vars_lt AP.kentry_vars_lt]. cbn [AP.kentry_vars_lt] in KEEPV. apply andb_prop in KEEPV as [Ka _].
        rewrite Ka. cbn [AP.expr_vars_lt]. replace (Nat.ltb x (Datatypes.S x)) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
        eapply kn_vars_lt_mono'; [apply hw_apply_true_vars; exact Hvr | lia].
    + destruct (IH Hr Hvr) as [IH1 IH2]. split; [constructor; [apply KEEP | exact IH1] | cbn [AP.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity].
Qed.

Lemma hw_go_ok : forall bs E M k x,
  know_ok SEGS E M k -> AP.kn_vars_lt x k = true ->
  exists E', env_agree x E E' /\ know_ok SEGS E' M (hw_go k bs x) /\ AP.kn_vars_lt (x + length bs)%nat (hw_go k bs x) = true.
Proof.
  induction bs as [|b r IH]; intros E M k x HK Hv.
  - exists E. split; [apply env_agree_refl|]. cbn [hw_go length]. rewrite Nat.add_0_r. split; assumption.
  - cbn [hw_go length]. destruct (hw_apply_ok E M k (sa_of b) x HK Hv) as [H1 H2].
    destruct (IH _ M _ (Datatypes.S x) H1 H2) as (E' & Hag & HK' & Hv').
    exists E'. split; [|split; [exact HK' | rewrite <- Nat.add_succ_comm; exact Hv']].
    apply (env_agree_trans _ _ (upd E x (edenot E (hw_val k (sa_of b)))) _); [apply upd_agree | eapply env_agree_le; [exact Hag | lia]].
Qed.

Lemma havocwords_sound : forall E cs R FULL model bs cs',
  cs_ok E cs R FULL model -> node_havocwords nx0 cs bs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model bs cs' HC H. unfold node_havocwords in H.
  destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate]. injection H as <-.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (hw_go_ok bs E (Mr E cs model FULL) (kn cs) (nxt cs) (co_know _ _ _ _ _ HC)) as (E' & Hag & HK' & _).
  { rewrite kn_vars_lt_eq. rewrite <- kn_vars_lt_eq. exact Fkn. }
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC2.
  replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (hw_go (s_know (a_ss cs)) bs (s_next (a_ss cs))) (s_next (a_ss cs) + length bs)))
    with (set_kn (bump cs (length bs)) (hw_go (kn cs) bs (nxt cs))) by reflexivity.
  apply cs_ok_set_kn.
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - unfold Mr. change (hid E' (bump cs (length bs)) model) with (hid E' cs model).
    rewrite (hid_agree (nxt cs) E E' cs model Hag Fle Fallow). exact HK'.
Qed.

(* [comment removed for export] *)
Lemma respell_sound : forall E cs R FULL model r e cs',
  cs_ok E cs R FULL model -> node_respell cs r e = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model r e cs' HC H. unfold node_respell in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && AP.expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
  pose proof (respell_ok_sound E _ (kn cs) (reg cs r) e (co_know _ _ _ _ _ HC) Hok) as Heq.
  split; [|reflexivity].
  destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
  apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
Qed.



End Sound.
End APS.
End GxPlanSound.
Module GxPlanSound2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan GxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

Section Sound2.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Lemma kread_bytes_sound : forall E M k n b off zs,
  know_ok SEGS E M k ->
  kread_bytes SEGS n k b off = Some zs ->
  0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat n <= 2 ^ 64 ->
  exists bs, length bs = n /\ map bv_unsigned bs = zs
             /\ forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (estart E (SA b off) + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros E M k n. induction n as [|n IH]; intros b off zs HK Hr Hlo Hhi.
  - cbn in Hr. injection Hr as <-. exists []. repeat split; try reflexivity. intros j Hj. lia.
  - cbn [kread_bytes] in Hr.
    destruct (kreadZ SEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes SEGS n k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate]. injection Hr as <-.
    unfold kreadZ in Hz.
    pose proof (know_lookup_sound SEGS E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as KL.
    destruct (know_lookup SEGS k b off 1 false [] []) as [v scs nx| |]; try discriminate.
    destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection Hz as <-.
    assert (Hfl : flat E (SA b off) (Z.of_nat 1)) by (unfold flat; change (Z.of_nat 1) with 1; rewrite Nat2Z.inj_succ in Hhi; lia).
    destruct (KL ltac:(constructor) Hfl) as [bs1 (R1 & L1 & V1)].
    destruct bs1 as [|b0 [|? ?]]; try (cbn in L1; lia).
    destruct (IH b (off + 1) rest HK Hrest) as [bs (Lb & Mb & Rb)].
    { unfold estart in *; cbn [a_base a_off] in *. lia. }
    { unfold estart in *; cbn [a_base a_off] in *. rewrite Nat2Z.inj_succ in Hhi. lia. }
    exists (b0 :: bs). split; [cbn; lia|]. split.
    + cbn [map]. rewrite Mb. f_equal.
      cbn [edenot] in V1. apply (f_equal bv_unsigned) in V1. rewrite !u_lit64 in V1.
      unfold extz in V1. cbn [bytes_le_to_Z] in V1. rewrite Z.shiftl_0_l, Z.lor_0_r in V1.
      pose proof (u8_range b0). unfold two64 in *. rewrite Z.mod_small in V1 by lia. exact V1.
    + intros j Hj. destruct j as [|j].
      * cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite <- R1. reflexivity.
      * cbn [nth]. rewrite <- (Rb j) by lia. f_equal. f_equal. unfold estart; cbn [a_base a_off]. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_bytes1 : forall M n (a : word) bs,
  length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  rdn SEGS M a n = Some bs.
Proof.
  intros M n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
  - destruct bs; [reflexivity | cbn in Hlen; lia].
  - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
    pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
    destruct n as [|n'].
    + destruct bs'; [exact H0 | cbn in Hlen; lia].
    + apply rdn_cons1; [exact H0|].
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      apply IH; [lia | rewrite Hu1; lia |].
      intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
      exact (Hpt (S j) ltac:(lia)).
Qed.

End Sound2.
End GxPlanSound2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan GxPlanSound GxPlanSound2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
#[local] Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.

Module GPS.
(* [comment removed for export] *)
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FX : Type := FPState.
Definition mkstF (fx : FX) (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
  @mkst fx regs pc mem rom.


Definition cfgF (SEGS : list Segment) (fx : FX) (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkstF fx R (Z_to_bv 64 p) M (seg_rom SEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).

(* [comment removed for export] *)
Definition blocks_den (E : env) (L : list (expr * expr)) : list (Z * Z) :=
  map (fun p => (uE E (fst p), uE E (snd p))) L.

(* [comment removed for export] *)
Definition MBLK : Z := 2 ^ 20 + 2 ^ 13.   (* [comment removed for export] *)
Fixpoint bcost (E : env) (L : list (expr * expr)) : Z :=
  match L with [] => 0 | p :: r => uE E (snd p) + MBLK + bcost E r end.
Definition bcount (L : list (expr * expr)) : Z := Z.of_nat (length L).

Definition in_blocks (Lc : list (Z * Z)) (z : Z) : Prop :=
  exists b n, In (b, n) Lc /\ b <= z < b + n.
Definition in_wins (W : list (Z * Z)) (z : Z) : Prop :=
  exists lo hi, In (lo, hi) W /\ lo <= z < hi.

(* [comment removed for export] *)
Definition wins_den (E : env) (L : list (expr * expr)) : list (Z * Z) :=
  map (fun p => (uE E (fst p), uE E (fst p) + uE E (snd p))) L.
Definition sptop_den (E : env) (e : expr) : Z :=
  if Z.eqb (uE E e) 0 then 2 ^ 64 else uE E e.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition floor_sem {RC : run_ceil} (E : env) (fl : option expr) (top : expr) (bud : Z) : Prop :=
  match fl with
  | Some f => CEIL_run <= uE E f
  | None => CEIL_run + bud <= sptop_den E top
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition owned {RC : run_ceil} (SWIN PERM : list (Z * Z)) (TOP : Z) (Lc : list (Z * Z)) (a : word) : Prop :=
  in_blocks Lc (bv_unsigned a) \/ in_wins PERM (bv_unsigned a) \/ (CEIL_run <= bv_unsigned a < TOP) \/ in_wins SWIN (bv_unsigned a).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rz_t : Type := config -> TSet -> Prop.

Definition RZ_STEP (SEGS : list Segment) (RZ : rz_t) : Prop :=
  forall ms model ms' T,
    m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
    RiscvSemantics.step SEGS ms = MachineOk ms' -> RZ (mkCfg ms' model) T -> RZ (mkCfg ms model) T.
Definition RZ_MSTEPS (SEGS : list Segment) (RZ : rz_t) : Prop :=
  forall ms ms' model T,
    m_halted model = None -> m_vm_lazy model = [] -> msteps SEGS ms ms' -> RZ (mkCfg ms' model) T -> RZ (mkCfg ms model) T.
Definition RZ_EXIT (SEGS : list Segment) (RZ : rz_t) : Prop :=
  forall ms model x8,
    m_halted model = None -> ms_svc_pending ms = Some x8 -> ExitSim.is_exit_no x8 ->
    RZ (mkCfg ms model) (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Definition RZ_CONSEQ (RZ : rz_t) : Prop :=
  forall c T T', RZ c T -> t_eq T T' -> RZ c T'.





(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
(* [comment removed for export] *)
Context {RC : run_ceil}.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.           (* [comment removed for export] *)
Variable nx0 : nat.            (* [comment removed for export] *)
Variable LIMIT : Z.            (* [comment removed for export] *)
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable XC : xhookB.                                           (* [comment removed for export] *)
Variable KC : nat.

(* [comment removed for export] *)
Variable SWIN : list (Z * Z).
(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).

(* [comment removed for export] *)
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
(* [comment removed for export] *)
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
(* [comment removed for export] *)
Hypothesis AINV_vm : forall Lc B C M mdl mdl',
  AINV Lc B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINV Lc B C M mdl'.
(* [comment removed for export] *)
Hypothesis AINV_mono : forall Lc B C B' C' M mdl,
  AINV Lc B C M mdl -> B <= B' -> C <= C' -> AINV Lc B' C' M mdl.

(* [comment removed for export] *)
Variable FXOK : FX -> Prop.

(* [comment removed for export] *)
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

(* [comment removed for export] *)
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
(* [comment removed for export] *)
Hypothesis HOLES_same : forall h E fs, HOLES h E fs = HOLES 0%nat E fs.

(* [comment removed for export] *)
Variable RZ : rz_t.
Hypothesis RZ_step : RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : RZ_MSTEPS SEGS RZ.
Hypothesis RZ_exit : RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : RZ_CONSEQ RZ.

#[local] Notation cfg := (cfgF SEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record cs_ok (E : env) (cs : acs) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop := CS_OK {
  co_regs  : regs_ok E (s_regs (a_ss cs)) R;
  co_log   : s_log (a_ss cs) = [];
  co_know  : know_ok SEGS E M (kn cs);
  co_halt  : m_halted model = None;
  co_lazy  : m_vm_lazy model = [];
  co_fs    : m_fs model = FS0;
  co_fds   : m_fds model = FDS0;
  co_ainv  : AINV (blocks_den E (a_vis cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) M model;
  co_uinv  : UINV E;
  co_fx    : FXOK fx;
  co_perm  : wins_den E (a_ghost cs) = PERMc;
  co_top   : sptop_den E (a_brk cs) = SPTOPc;
  co_mat   : m_vm_materialized model = [];     (* [comment removed for export] *)
  co_floor : floor_sem E (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs)   (* [comment removed for export] *)
}.
Arguments co_regs {E cs fx R M model} _.
Arguments co_log {E cs fx R M model} _.
Arguments co_know {E cs fx R M model} _.
Arguments co_halt {E cs fx R M model} _.
Arguments co_lazy {E cs fx R M model} _.
Arguments co_fs {E cs fx R M model} _.
Arguments co_fds {E cs fx R M model} _.
Arguments co_ainv {E cs fx R M model} _.
Arguments co_uinv {E cs fx R M model} _.
Arguments co_fx {E cs fx R M model} _.
Arguments co_perm {E cs fx R M model} _.
Arguments co_top {E cs fx R M model} _.
Arguments co_mat {E cs fx R M model} _.
Arguments co_floor {E cs fx R M model} _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RUN_SOUND : Prop :=
  forall t K fuel stops pc sr kn nx E M R fx,
    itab_sound SEGS t -> regs_ok E sr R -> know_ok SEGS E M kn ->
    GxSymRun3.sr_vars_lt nx sr = true -> GxSymRun3.kn_vars_lt nx kn = true -> FXOK fx ->
    let ss' := sym_execTX SEGS t K fuel true stops (SS pc sr [] kn nx) in
    exists E' R' fx', env_agree nx E E'
      /\ (nx <= s_next ss')%nat
      /\ regs_ok E' (s_regs ss') R'
      /\ log_flat E' (s_log ss')
      /\ know_ok SEGS E' M (s_know ss')
      /\ FXOK fx'
      /\ msteps SEGS (mkstF fx R (Z_to_bv 64 pc) M (seg_rom SEGS))
                     (mkstF fx' R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' M (s_log ss')) (seg_rom SEGS)).
Hypothesis RUN_sound : RUN_SOUND.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition piece_den (E : env) (p : spiece) : list byte :=
  match p with SPLit bs => map (Z_to_bv 8) bs | SPBlob k => eb E k end.
Definition Wp (E : env) (fd : Z) (ps : list spiece) : list event :=
  map (WriteEv (Z_to_bv 64 fd)) (flat_map (piece_den E) ps).

Fixpoint sd (D : TSet) (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmitP fd ps s' => t_emit (Wp E fd ps) (sd D E fs s')
  | SAlt2 a b => t_alt2 (sd D E fs a) (sd D E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd D E fs s1 else sd D E fs s2
  | SHole h => HOLES h E fs
  | SNext => D
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node1_stmt (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E fx R M model T,
    cs_ok E cs fx R M model -> pre cs = true -> node cs = Some cs' ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc cs') M' model') T) ->
    RZ (cfg fx R (pc cs) M model) T.

Definition always (cs : acs) : bool := true.

(* [comment removed for export] *)
Definition node1_stmtN (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E fx R M model (T : TSet),
    T [] ->
    cs_ok E cs fx R M model -> pre cs = true -> node cs = Some cs' ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc cs') M' model') T) ->
    RZ (cfg fx R (pc cs) M model) T.
Lemma node1_stmt_N : forall pre node, node1_stmt pre node -> node1_stmtN pre node.
Proof. intros pre node H cs cs' E fx R M model T _ HC Hp Hn Hk. exact (H cs cs' E fx R M model T HC Hp Hn Hk). Qed.

(* [comment removed for export] *)
Definition ext_stmt : Prop := forall id args, node1_stmtN always (XN id args).

(* [comment removed for export] *)
Definition emit_stmt : Prop :=
  forall id args cs fd ps cs' E fx R M model T,
    cs_ok E cs fx R M model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc cs') M' model') T) ->
    RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) T).

(* [comment removed for export] *)
Definition ext2_stmt : Prop :=
  forall id args cs csa csb E fx R M model T,
    cs_ok E cs fx R M model -> XB id args cs = Some (csa, csb) -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc csa) M' model') T) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc csb) M' model') T) ->
    RZ (cfg fx R (pc cs) M model) T.

(* [comment removed for export] *)
Definition alt2x_stmt : Prop :=
  forall id args cs csa csb E fx R M model Ta Tb,
    cs_ok E cs fx R M model -> XC id args cs = Some (csa, csb) -> Ta [] -> Tb [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc csa) M' model') Ta) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
        RZ (cfg fx' R' (pc csb) M' model') Tb) ->
    RZ (cfg fx R (pc cs) M model) (t_alt2 Ta Tb).

(* [comment removed for export] *)
Definition holes_stmt : Prop :=
  forall h ch, HS h = Some ch ->
  forall E fx R M model, cs_ok E ch fx R M model ->
    RZ (cfg fx R (pc ch) M model) (HOLES h E (m_fs model)).

(* [comment removed for export] *)
Fixpoint gplan_ok (p : plan) : bool :=
  let fix lalts_ok (l : list (acs * plan * plan)) : bool :=
    match l with [] => true | (_, b, k) :: r => gplan_ok b && gplan_ok k && lalts_ok r end in
  let fix valts_ok (l : list (acs * plan)) : bool :=
    match l with [] => true | (_, k) :: r => gplan_ok k && valts_ok r end in
  match p with
  | PRun _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k | PBump _ k | PHavoc _ k
  | PHavocBig _ k | PFresh _ _ _ k | PExt _ _ k | PEmit _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k | PFactVia _ _ _ _ k | PFactLe _ _ _ k | PFactScale _ _ _ k
  | PFactLeR _ _ _ _ k | PFactR _ _ _ _ k | PFactLeX _ _ _ _ _ k | PFactX _ _ _ _ _ k => gplan_ok k
  | PSplit _ _ k1 k2 | PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 | PExt2 _ _ k1 k2 | PBranch k1 k2 | PBranchP k1 k2 | PCaseReg _ _ k1 k2
  | PAlt2X _ _ k1 k2 => gplan_ok k1 && gplan_ok k2
  | PLoop _ _ _ _ body k => gplan_ok body && gplan_ok k
  | PLoopM _ _ alts _ => lalts_ok alts
  | PVia _ _ _ karms k => gplan_ok karms && gplan_ok k
  | PViaM _ alts _ karms => gplan_ok karms && valts_ok alts
  | PContra | PNext | PHandoff _ | PExit | PMerge _ | PNextW _ | PMergeW _ _ | PHandoffW _ _ | PContraH _ => true
  | PShDisj _ _ _ _ _ | PSys _ _ | PMmap _ _ | PMmapIn _ _ _ | PMmapInH _ _ _ | PMprotect _ _ | PBrk2 _ _ | PX _ _ _
  | PSpin | PFog _ _ _ | PFogNew _ _ _ | PGhost _ _ _ | PUnvis _ _ _ | PHavocBrk _ _ _ => false
  end%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
(* [comment removed for export] *)
Hypothesis node_ext_sound : ext_stmt.
Hypothesis node_emit_sound : emit_stmt.
Hypothesis node_ext2_sound : ext2_stmt.
Hypothesis node_alt2x_sound : alt2x_stmt.
Hypothesis HS_sound : holes_stmt.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mem_denot_outside : forall E M log (a : word),
  log_flat E log ->
  (forall b w v, In (SE b w v) log -> bv_unsigned a < estart E b \/ estart E b + Z.of_nat w <= bv_unsigned a) ->
  mem_denot E M log a = M a.
Proof.
  intros E M log a. induction log as [|[b w v] rest IH]; intros Hlf Hout; [reflexivity|].
  cbn [mem_denot]. cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hfl & Hlf').
  pose proof (Hout b w v) as Ha. specialize (Ha (or_introl eq_refl)).
  pose proof (flat_u E b (Z.of_nat w) Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  assert (Hlen : length (word_to_le_bytes w (edenot E v)) = w) by apply length_N_to_le_bytes.
  destruct Ha as [Ha|Ha].
  - rewrite wbytes_below; [| rewrite Hlen, Hu; lia | rewrite Hu; lia].
    apply IH; [exact Hlf' | intros b' w' v' Hin; apply (Hout b' w' v'); right; exact Hin].
  - rewrite wbytes_above; [| rewrite Hlen, Hu; lia].
    apply IH; [exact Hlf' | intros b' w' v' Hin; apply (Hout b' w' v'); right; exact Hin].
Qed.

Lemma wbytes_same_or_some : forall m addr bs (a : word),
  wbytes m addr bs a = m a \/ exists b, wbytes m addr bs a = Some b.
Proof.
  intros m addr bs. revert m addr. induction bs as [|b rest IH]; intros m addr a; [left; reflexivity|].
  cbn [wbytes]. destruct (IH (fun x => if bv_eqb x addr then Some b else m x) (addr + 1)%bv a) as [H|H].
  - rewrite H. destruct (bv_eqb a addr); [right; exists b; reflexivity | left; reflexivity].
  - right. exact H.
Qed.

Lemma mem_denot_same_or_some : forall E M log (a : word),
  mem_denot E M log a = M a \/ exists b, mem_denot E M log a = Some b.
Proof.
  intros E M log a. induction log as [|[b w v] rest IH]; [left; reflexivity|]. cbn [mem_denot].
  destruct (wbytes_same_or_some (mem_denot E M rest) (adenot E b) (word_to_le_bytes w (edenot E v)) a) as [H|H].
  - rewrite H. exact IH.
  - right. exact H.
Qed.

Lemma in_blocks_den : forall E live b n z,
  In (b, n) live -> uE E b <= z < uE E b + uE E n -> in_blocks (blocks_den E live) z.
Proof.
  intros E live b n z Hin Hz. exists (uE E b), (uE E n). split; [|exact Hz].
  unfold blocks_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hin].
Qed.

Lemma u_add_off : forall (x : word) (off : Z),
  0 <= bv_unsigned x + off < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_unsigned (Z_to_bv 64 off))) = bv_unsigned x + off.
Proof.
  intros x off H. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.

(* [comment removed for export] *)
Lemma log_flat_In : forall E log b w v, log_flat E log -> In (SE b w v) log -> (w <= 8)%nat /\ flat E b (Z.of_nat w).
Proof.
  intros E log b w v. induction log as [|[b' w' v'] rest IH]; intros Hlf Hin; [destruct Hin|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hf & Hr).
  destruct Hin as [Heq|Hin]; [injection Heq as -> -> ->; split; assumption | exact (IH Hr Hin)].
Qed.

(* [comment removed for export] *)
Lemma in_wins_den : forall E perm b n z,
  In (b, n) perm -> uE E b <= z < uE E b + uE E n -> in_wins (wins_den E perm) z.
Proof.
  intros E perm b n z Hin Hz. exists (uE E b), (uE E b + uE E n). split; [|exact Hz].
  unfold wins_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hin].
Qed.

(* [comment removed for export] *)
Lemma in_floor_sound : forall E M k fl top bud b off n (a : word),
  know_ok SEGS E M k -> in_floor k fl top bud b off n = true ->
  floor_sem E fl top bud ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + elenZ E n ->
  CEIL_run <= bv_unsigned a < sptop_den E top /\ sptop_den E top < 2 ^ 64.
Proof.
  intros E M k fl top bud b off n a HK Hf Hfl Ha. unfold in_floor in Hf.
  destruct (split_lit top) as [tb tk] eqn:Hsp.
  destruct (base_range k tb) as [[tlo thi]|] eqn:Hbr; [|discriminate].
  destruct fl as [f|]; cbn [floor_sem] in Hfl.
  { (* [comment removed for export] *)
    apply andb_prop in Hf as [Hf L2]. apply andb_prop in Hf as [Hf L1]. apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H0 H1].
    apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H3.
    pose proof (base_range_sound SEGS E M k tb tlo thi HK Hbr) as [B1 B2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK L1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK L2) as X2.
    cbn [xt_den] in X1, X2. pose proof (u64_range (edenot E tb)) as Rt. pose proof (u64_range a) as Ra.
    assert (Ht : uE E top = bv_unsigned (edenot E tb) + tk).
    { unfold uE. rewrite (split_lit_denot E top tb tk Hsp). apply u64_lit. unfold two64 in *. lia. }
    rewrite estart_SA in Ha. unfold elenZ in Ha. pose proof GlzConst.ceil_lo as CL.
    assert (Hnz : uE E top <> 0) by (unfold uE in *; lia).
    unfold sptop_den in *. destruct (Z.eqb_spec (uE E top) 0) as [Hz|Hz]; [exfalso; exact (Hnz Hz)|].
    pose proof (u64_range (edenot E top)). unfold uE in *. lia. }
  apply andb_prop in Hf as [Hg Hx]. apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  pose proof (base_range_sound SEGS E M k tb tlo thi HK Hbr) as [B1 B2].
  pose proof (xinside_sound SEGS E M k b off n tb (tk - bud) (ELit bud) HK Hx) as [X1 X2].
  rewrite !estart_SA in X1. rewrite !estart_SA in X2. rewrite (APS.elenZ_lit E bud) in X2 by (unfold CEIL, two64 in *; lia).
  pose proof (u64_range (edenot E tb)) as Rt. pose proof (u64_range a) as Ra.
  assert (Ht : uE E top = bv_unsigned (edenot E tb) + tk).
  { unfold uE. rewrite (split_lit_denot E top tb tk Hsp). apply u64_lit. unfold CEIL, two64 in *. lia. }
  assert (Hnz : uE E top <> 0) by (unfold CEIL in *; lia).
  unfold sptop_den in *. destruct (Z.eqb_spec (uE E top) 0) as [Hz|Hz]; [exfalso; exact (Hnz Hz)|].
  rewrite estart_SA in Ha. pose proof (u64_range (edenot E top)). unfold uE in *. lia.
Qed.

Lemma store_owned_sound : forall E M k live perm fl top bud b off n v (a : word),
  know_ok SEGS E M k -> store_owned k (live ++ perm) fl top bud (SE (SA b off) n v) = true -> (n <= 8)%nat ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> floor_sem E fl top bud ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + Z.of_nat n ->
  owned SWIN PERMc SPTOPc (blocks_den E live) a.
Proof.
  intros E M k live perm fl top bud b off n v a HK Hs Hn8 Hperm Htop Hfl Ha. unfold store_owned in Hs. apply orb_prop in Hs as [Hs|Hs].
  - apply existsb_exists in Hs as [[lb0 ln] [Hin Hx]]. cbn [fst snd] in Hx.
    destruct (split_lit lb0) as [lb lk] eqn:Hsp.
    apply andb_prop in Hx as [Hx Hbr0].
    destruct (base_range k lb) as [[blo bhi]|] eqn:Hbr; [|discriminate]. apply Z.leb_le in Hbr0.
    pose proof (base_range_sound SEGS E M k lb blo bhi HK Hbr) as [Hblo _].
    pose proof (xinside_sound SEGS E M k b off (ELit (Z.of_nat n)) lb lk ln HK Hx) as [X1 X2].
    rewrite APS.elenZ_lit in X2 by lia.
    pose proof (split_lit_denot E lb0 lb lk Hsp) as Hd.
    rewrite !estart_SA in X1. rewrite !estart_SA in X2. rewrite !estart_SA in Ha. unfold elenZ in X2.
    pose proof (u64_range (edenot E lb)). pose proof (u64_range a). pose proof (u64_range (edenot E ln)).
    assert (Hu : uE E lb0 = bv_unsigned (edenot E lb) + lk) by (unfold uE; rewrite Hd; apply u64_lit; lia).
    apply in_app_iff in Hin as [Hin|Hin].
    + left. eapply (in_blocks_den E live lb0 ln); [exact Hin|]. rewrite Hu. unfold uE. lia.
    + right. left. rewrite <- Hperm. eapply (in_wins_den E perm lb0 ln); [exact Hin|]. rewrite Hu. unfold uE. lia.
  - right. right. left. rewrite <- Htop.
    eapply (proj1 (in_floor_sound E M k fl top bud b off (ELit (Z.of_nat n)) a HK Hs Hfl _)). Unshelve.
    rewrite (APS.elenZ_lit E) by (pose proof (u64_range a); lia). exact Ha.
Qed.

Lemma log_owned_sound : forall E M k live perm fl top bud log (a : word),
  know_ok SEGS E M k -> log_owned k (live ++ perm) fl top bud log = true -> log_flat E log ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> floor_sem E fl top bud ->
  mem_denot E M log a <> M a -> owned SWIN PERMc SPTOPc (blocks_den E live) a.
Proof.
  intros E M k live perm fl top bud log a HK Hown Hlf Hperm Htop Hfl Hne.
  destruct (Z_lt_ge_dec 0 1) as [_|X]; [|lia].
  assert (CASE : forall b w v, In (SE b w v) log ->
            (bv_unsigned a < estart E b \/ estart E b + Z.of_nat w <= bv_unsigned a) \/ owned SWIN PERMc SPTOPc (blocks_den E live) a).
  { intros [bb bo] w v Hin. unfold log_owned in Hown.
    pose proof (proj1 (forallb_forall _ _) Hown _ Hin) as Hs.
    destruct (Z_lt_ge_dec (bv_unsigned a) (estart E (SA bb bo))) as [Hlt|Hge]; [left; left; exact Hlt|].
    destruct (Z_lt_ge_dec (bv_unsigned a) (estart E (SA bb bo) + Z.of_nat w)) as [Hlt2|Hge2]; [|left; right; lia].
    right. eapply store_owned_sound; [exact HK | exact Hs | exact (proj1 (log_flat_In E log _ w v Hlf Hin)) | exact Hperm | exact Htop | exact Hfl | lia]. }
  (* [comment removed for export] *)
  assert (ALL : (forall b w v, In (SE b w v) log -> bv_unsigned a < estart E b \/ estart E b + Z.of_nat w <= bv_unsigned a)
                \/ owned SWIN PERMc SPTOPc (blocks_den E live) a).
  { clear Hne. induction log as [|[b w v] rest IH]; [left; intros ? ? ? []|].
    assert (Hlf' : log_flat E rest) by (cbn [log_flat] in Hlf; tauto).
    assert (Hown' : log_owned k (live ++ perm) fl top bud rest = true).
    { unfold log_owned in *. cbn [forallb] in Hown. apply andb_prop in Hown as [_ H]. exact H. }
    destruct (CASE b w v (or_introl eq_refl)) as [Hbw|Ho]; [|right; exact Ho].
    destruct (IH Hown' Hlf') as [Hall|Ho].
    - intros b' w' v' Hin'. apply (CASE b' w' v'). right. exact Hin'.
    - left. intros b' w' v' [Heq|Hin']; [injection Heq as <- <- <-; exact Hbw | apply (Hall b' w' v'); exact Hin'].
    - right. exact Ho. }
  destruct ALL as [Hall|Ho]; [|exact Ho].
  exfalso. apply Hne. apply mem_denot_outside; [exact Hlf | exact Hall].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blocks_den_agree : forall b E E' live,
  env_agree b E E' -> pairs_vars_lt b live = true -> blocks_den E' live = blocks_den E live.
Proof.
  intros b E E' live Hag H. unfold blocks_den. apply map_ext_in. intros p Hin.
  pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
  unfold uE. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

Lemma bcost_agree : forall b E E' live,
  env_agree b E E' -> pairs_vars_lt b live = true -> bcost E' live = bcost E live.
Proof.
  intros b E E' live Hag H. induction live as [|[x n] r IH]; [reflexivity|].
  unfold pairs_vars_lt in H. cbn [forallb fst snd] in H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [_ Hn].
  cbn [bcost snd]. unfold uE at 1 2. rewrite <- (edenot_agree' b E E' _ Hag Hn). rewrite (IH H2). reflexivity.
Qed.

Lemma pairs_vars_lt_app_l : forall b l1 l2, pairs_vars_lt b (l1 ++ l2) = true -> pairs_vars_lt b l1 = true.
Proof. intros b l1 l2 H. unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [H _]. exact H. Qed.
Lemma pairs_vars_lt_app_r : forall b l1 l2, pairs_vars_lt b (l1 ++ l2) = true -> pairs_vars_lt b l2 = true.
Proof. intros b l1 l2 H. unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma wins_den_agree : forall b E E' l,
  env_agree b E E' -> pairs_vars_lt b l = true -> wins_den E' l = wins_den E l.
Proof.
  intros b E E' l Hag H. unfold wins_den. apply map_ext_in. intros p Hin.
  pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
  unfold uE. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

Lemma sptop_den_agree : forall b E E' e,
  env_agree b E E' -> AP.expr_vars_lt b e = true -> sptop_den E' e = sptop_den E e.
Proof.
  intros b E E' e Hag H. unfold sptop_den, uE. rewrite <- (edenot_agree' b E E' _ Hag H). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma floor_sem_agree : forall b E E' ms top bud,
  env_agree b E E' -> AP.expr_vars_lt b top = true -> AP.maps_vars_lt b ms = true ->
  floor_sem E (acs_floor ms) top bud -> floor_sem E' (acs_floor ms) top bud.
Proof.
  intros b E E' ms top bud Hag Htop Hms H. destruct ms as [|[f l kd] r]; cbn [acs_floor floor_sem] in *.
  - rewrite (sptop_den_agree b E E' top Hag Htop). exact H.
  - cbn [AP.maps_vars_lt forallb am_base am_len] in Hms. apply andb_prop in Hms as [Hms _]. apply andb_prop in Hms as [Hf _].
    unfold uE in *. rewrite <- (edenot_agree' b E E' f Hag Hf). exact H.
Qed.

(* [comment removed for export] *)
Lemma floor_sem_xfer : forall E E' ms top top' bud bud',
  (forall f l kd r, ms = AM f l kd :: r -> uE E' f = uE E f) ->
  sptop_den E' top' = sptop_den E top -> bud' <= bud ->
  floor_sem E (acs_floor ms) top bud -> floor_sem E' (acs_floor ms) top' bud'.
Proof.
  intros E E' ms top top' bud bud' Hf Ht Hb H. destruct ms as [|[f l kd] r]; cbn [acs_floor floor_sem] in *.
  - rewrite Ht. lia.
  - rewrite (Hf f l kd r eq_refl). exact H.
Qed.

(* [comment removed for export] *)
Lemma floor_sem_weaken : forall E ms top bud bud',
  bud' <= bud -> floor_sem E (acs_floor ms) top bud -> floor_sem E (acs_floor ms) top bud'.
Proof.
  intros E ms top bud bud' Hle H. destruct ms as [|[f l kd] r]; cbn [acs_floor floor_sem] in *; [lia | exact H].
Qed.

Lemma cs_ok_agree : forall E E' cs fx R M model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true ->
  cs_ok E cs fx R M model -> cs_ok E' cs fx R M model.
Proof.
  intros E E' cs fx R M model Hag Hf HC.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor; try assumption.
  - eapply regs_ok_agree'; eassumption.
  - eapply know_ok_agree'; eassumption.
  - rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (bcost_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)). assumption.
  - eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | assumption].
  - rewrite (wins_den_agree (nxt cs) E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). assumption.
  - rewrite (sptop_den_agree (nxt cs) E E' (a_brk cs) Hag Fbrk). assumption.
  - eapply (floor_sem_agree (nxt cs) E E'); [exact Hag | exact Fbrk | exact Fmaps | assumption].
Qed.

(* [comment removed for export] *)
Lemma cs_ok_frame : forall E cs fx R M model ss' fx' R' M',
  cs_ok E cs fx R M model ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] -> know_ok SEGS E M' (s_know ss') -> FXOK fx' ->
  (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc (blocks_den E (a_vis cs)) a /\ M' a <> None) ->
  cs_ok E (with_ss cs ss') fx' R' M' model.
Proof.
  intros E cs fx R M model ss' fx' R' M' HC HR HL HK HF Hown.
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor; cbn [with_ss a_ss a_vis a_totsz a_eager kn]; try assumption.
  eapply AINV_frame; [exact CA | exact Hown].
Qed.


Lemma cs_ok_set_kn : forall E cs fx R M model k',
  cs_ok E cs fx R M model -> know_ok SEGS E M k' -> cs_ok E (set_kn cs k') fx R M model.
Proof.
  intros E cs fx R M model k' HC HK.
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor; cbn [set_kn with_ss a_ss a_vis a_totsz a_eager kn mk_ss s_regs s_log s_know]; try assumption; reflexivity.
Qed.

Lemma cs_gc_ok : forall gb E cs fx R M model, cs_ok E cs fx R M model -> cs_ok E (cs_gc gb cs) fx R M model.
Proof.
  intros gb E cs fx R M model HC. unfold cs_gc. destruct (split_lit (reg cs 2)) as [spb spk].
  apply cs_ok_set_kn; [exact HC|]. apply know_ok_filter. exact (co_know HC).
Qed.

Lemma cs_ok_bump : forall E cs fx R M model d, cs_ok E cs fx R M model -> cs_ok E (bump cs d) fx R M model.
Proof.
  intros E cs fx R M model d HC.
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_vis a_totsz a_eager]; try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_block_sound : forall gb bfuel stops cs cs' E fx R M model T,
  (nx0 <= gb)%nat ->
  run_block SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs fx R M model ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros gb bfuel stops cs cs' E fx R M model T Hgb Hrb HC Hk.
  rewrite run_block_eq in Hrb. unfold run_block_ref in Hrb.
  destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate].
  pose proof (fresh_ok_mono nx0 gb cs Hgb Hf0) as Hf.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  unfold kn in HK, Fkn. unfold nxt in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  destruct (a_ss cs) as [p sr log k nx rsv] eqn:Hss.
  cbn [s_know s_regs s_pc s_next] in Hrb, HR, HK, Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  set (ss' := sym_execTX SEGS IT KC bfuel true stops (SS p sr [] k nx)) in Hrb.
  destruct (log_owned k (a_vis cs ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (s_log ss')) eqn:Hown; [|discriminate]. cbn [negb] in Hrb.
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection Hrb as <-.
  rewrite sr_vars_lt_eq in Fsr. rewrite kn_vars_lt_eq in Fkn.
  pose proof (RUN_sound IT KC bfuel stops p sr k nx E M R fx IT_ok HR HK Fsr Fkn (co_fx HC)) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (E' & R' & fx' & Hag & Hle & HR' & Hlf & HK' & HF' & Hms).
  assert (Hagc : env_agree (nxt cs) E E') by (unfold nxt; rewrite Hss; exact Hag).
  pose proof (cs_ok_agree E E' cs fx R M model Hagc Hf HC) as HC'.
  unfold cfgF, pc. rewrite Hss. cbn [a_ss s_pc].
  eapply RZ_msteps; [exact (co_halt HC) | exact (co_lazy HC) | exact Hms |].
  assert (HKc : know_ok SEGS E' (mem_denot E' M (s_log ss')) kn').
  { eapply (carry_sound SEGS E' M); [exact Hc | exact Hlf | exact HK' | constructor]. }
  specialize (Hk E' fx' R' (mem_denot E' M (s_log ss')) model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
  eapply cs_ok_frame; [exact HC' | exact HR' | reflexivity | cbn [mk_ss s_know]; exact HKc | exact HF' |].
  intros a Ha. assert (Fallow' : pairs_vars_lt (nxt cs) (a_vis cs) = true) by (unfold nxt; rewrite Hss; exact (pairs_vars_lt_app_l _ _ _ Fallow)).
  split.
  2:{ destruct (mem_denot_same_or_some E' M (s_log ss') a) as [Hs|[b Hb]]; [exfalso; exact (Ha Hs) | rewrite Hb; discriminate]. }
  eapply log_owned_sound; [| exact Hown | exact Hlf | | | | exact Ha].
  - eapply know_ok_agree'; [exact Hag | rewrite kn_vars_lt_eq; exact Fkn | exact HK].
  - rewrite (wins_den_agree nx E E' (a_ghost cs) Hag (pairs_vars_lt_app_r _ _ _ Fallow)). exact (co_perm HC).
  - rewrite (sptop_den_agree nx E E' (a_brk cs) Hag Fbrk). exact (co_top HC).
  - eapply (floor_sem_agree nx E E'); [exact Hag | exact Fbrk | exact Fmaps | exact (co_floor HC)].
Qed.

Lemma run_block_gc_sound : forall gb bfuel stops cs cs' E fx R M model T,
  (nx0 <= gb)%nat ->
  run_block_gc SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs fx R M model ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros gb bfuel stops cs cs' E fx R M model T Hgb H HC Hk. unfold run_block_gc in H.
  destruct (run_block SEGS IT gb KC bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  eapply run_block_sound; [exact Hgb | exact Hrb | exact HC |].
  intros E' fx' R' M' model' Hag HC1 Hfs. rewrite <- (pc_cs_gc gb cs1).
  apply (Hk E' fx' R' M' model'); [exact Hag | apply cs_gc_ok; exact HC1 | exact Hfs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma forget_sound : forall E cs fx R M model ixs,
  cs_ok E cs fx R M model -> cs_ok E (set_kn cs (drop_ixs ixs 0 (kn cs))) fx R M model.
Proof.
  intros E cs fx R M model ixs HC. apply cs_ok_set_kn; [exact HC|].
  unfold know_ok. apply Forall_forall. intros K Hin. apply drop_ixs_incl in Hin.
  exact (proj1 (Forall_forall _ _) (co_know HC) K Hin).
Qed.

Lemma droprange_sound : forall E cs fx R M model b n,
  cs_ok E cs fx R M model -> cs_ok E (node_droprange cs b n) fx R M model.
Proof.
  intros E cs fx R M model b n HC. unfold node_droprange. destruct (split_lit b) as [bb bk].
  apply cs_ok_set_kn; [exact HC|]. eapply know_ok_havoc; [exact (co_know HC) | intros; reflexivity | apply mem_grows_refl].
Qed.

Lemma gckeep_sound : forall E cs fx R M model ws,
  cs_ok E cs fx R M model -> cs_ok E (set_kn cs (kn_keep (kn cs) ws)) fx R M model.
Proof.
  intros E cs fx R M model ws HC. apply cs_ok_set_kn; [exact HC|]. unfold kn_keep. apply know_ok_filter. exact (co_know HC).
Qed.

Lemma bump_sound : forall E cs fx R M model m cs',
  cs_ok E cs fx R M model -> node_bump cs m = Some cs' -> cs_ok E cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model m cs' HC H. unfold node_bump in H. destruct (Nat.leb (nxt cs) m); [|discriminate]. injection H as <-.
  split; [apply cs_ok_bump; exact HC | reflexivity].
Qed.

Lemma split_sound : forall cs e mid lo hi E fx R M model,
  cs_ok E cs fx R M model -> brange (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> cs_ok E (set_kn cs (KRange e lo mid :: kn cs)) fx R M model)
  /\ (mid < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) fx R M model).
Proof.
  intros cs e mid lo hi E fx R M model HC Hr.
  pose proof (APS.brange_sound SEGS E _ (kn cs) e lo hi (co_know HC) Hr) as Hb.
  split; intros Hm; apply cs_ok_set_kn; [exact HC| |exact HC|];
    (constructor; [cbn [kentry_ok]; lia | exact (co_know HC)]).
Qed.

(* [comment removed for export] *)
Lemma probe_lin_facts_sound : forall E M k e (one : bool),
  know_ok SEGS E M k ->
  (if one then 1 <= bv_unsigned (edenot E e) else bv_unsigned (edenot E e) <= 0)%Z ->
  know_ok SEGS E M (probe_lin_facts k e one).
Proof.
  intros E M k e one HK Hv. unfold probe_lin_facts.
  assert (SUBD : forall a b, bv_unsigned (edenot E (esub a b)) = (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) mod 2 ^ 64).
  { intros a b. unfold esub. rewrite mkAlu_denot. apply u_sub64. }
  assert (XH : forall d h0, (bv_unsigned (edenot E d) <= h0)%Z ->
            (bv_unsigned (edenot E d) <= match xhi k d with Some h' => Z.min h' h0 | None => h0 end)%Z).
  { intros d h0 Hd. destruct (xhi k d) as [h'|] eqn:Hh; [|exact Hd]. pose proof (xhi_sound SEGS E M k d h' HK Hh). lia. }
  assert (GEN : forall x0 y0, e = EAlu ALU_SLTU x0 y0 -> let x := conc_expr k x0 in let y := conc_expr k y0 in
    know_ok SEGS E M (if one then match xhi k y, xlo k x with
                                  | Some hy, Some lx => let d := esub y x in
                                      let h := match xhi k d with Some h' => Z.min h' (hy - lx) | None => hy - lx end in
                                      KRange d 1 h :: match xhi k x with Some hx => if (lin_atomic x || Z.ltb (hy - 1) hx)%bool then [KRange x lx (Z.min hx (hy - 1))] else [] | None => [] end
                                                   ++ match xlo k y with Some ly => if (lin_atomic y || Z.ltb ly (lx + 1))%bool then [KRange y (Z.max ly (lx + 1)) hy] else [] | None => [] end
                                  | _, _ => [] end
                      else match xhi k x, xlo k y with
                           | Some hx, Some ly => let d := esub x y in
                               let h := match xhi k d with Some h' => Z.min h' (hx - ly) | None => hx - ly end in
                               KRange d 0 h :: match xlo k x with Some lx => if (lin_atomic x || Z.ltb lx ly)%bool then [KRange x (Z.max lx ly) hx] else [] | None => [] end
                                            ++ match xhi k y with Some hy => if (lin_atomic y || Z.ltb hx hy)%bool then [KRange y ly (Z.min hy hx)] else [] | None => [] end
                           | _, _ => [] end)).
  { intros x0 y0 He. cbv zeta. set (x := conc_expr k x0). set (y := conc_expr k y0). subst e. cbn [edenot] in Hv. rewrite u_sltu64 in Hv.
    rewrite <- (conc_expr_sound SEGS E M k x0 HK) in Hv. rewrite <- (conc_expr_sound SEGS E M k y0 HK) in Hv. fold x in Hv. fold y in Hv.
    pose proof (u64_range (edenot E x)) as Rx. pose proof (u64_range (edenot E y)) as Ry.
    destruct one.
    - destruct (xhi k y) as [hy|] eqn:Hy; [|constructor]. destruct (xlo k x) as [lx|] eqn:Hx; [|constructor].
      pose proof (xhi_sound SEGS E M k y hy HK Hy). pose proof (xlo_sound SEGS E M k x lx HK Hx).
      destruct (Z.ltb_spec (bv_unsigned (edenot E x)) (bv_unsigned (edenot E y))); [|lia].
      cbv zeta. constructor.
      + cbn [kentry_ok].
        assert (Hd : bv_unsigned (edenot E (esub y x)) = bv_unsigned (edenot E y) - bv_unsigned (edenot E x)) by (rewrite SUBD, Z.mod_small by lia; reflexivity).
        split; [rewrite Hd; lia|]. apply XH. rewrite Hd. lia.
      + apply Forall_app. split.
        * destruct (xhi k x) as [hx|] eqn:Hhx; [|constructor]. destruct (lin_atomic x || Z.ltb (hy - 1) hx)%bool; [|constructor]. pose proof (xhi_sound SEGS E M k x hx HK Hhx).
          constructor; [|constructor]. cbn [kentry_ok]. lia.
        * destruct (xlo k y) as [ly|] eqn:Hly; [|constructor]. destruct (lin_atomic y || Z.ltb ly (lx + 1))%bool; [|constructor]. pose proof (xlo_sound SEGS E M k y ly HK Hly).
          constructor; [|constructor]. cbn [kentry_ok]. lia.
    - destruct (xhi k x) as [hx|] eqn:Hx; [|constructor]. destruct (xlo k y) as [ly|] eqn:Hy; [|constructor].
      pose proof (xhi_sound SEGS E M k x hx HK Hx). pose proof (xlo_sound SEGS E M k y ly HK Hy).
      destruct (Z.ltb_spec (bv_unsigned (edenot E x)) (bv_unsigned (edenot E y))); [lia|].
      cbv zeta. constructor.
      + cbn [kentry_ok].
        assert (Hd : bv_unsigned (edenot E (esub x y)) = bv_unsigned (edenot E x) - bv_unsigned (edenot E y)) by (rewrite SUBD, Z.mod_small by lia; reflexivity).
        split; [rewrite Hd; lia|]. apply XH. rewrite Hd. lia.
      + apply Forall_app. split.
        * destruct (xlo k x) as [lx|] eqn:Hlx; [|constructor]. destruct (lin_atomic x || Z.ltb lx ly)%bool; [|constructor]. pose proof (xlo_sound SEGS E M k x lx HK Hlx).
          constructor; [|constructor]. cbn [kentry_ok]. lia.
        * destruct (xhi k y) as [hy|] eqn:Hhy; [|constructor]. destruct (lin_atomic y || Z.ltb hx hy)%bool; [|constructor]. pose proof (xhi_sound SEGS E M k y hy HK Hhy).
          constructor; [|constructor]. cbn [kentry_ok]. lia. }
  destruct e as [| |op x y| | | | |]; try constructor. destruct op; try constructor; try (apply (GEN x y); reflexivity).
  (* [comment removed for export] *)
  destruct x as [| |op2 a b| | | | |]; try (apply (GEN _ y); reflexivity).
  destruct op2; try (apply (GEN _ y); reflexivity).
  destruct y as [z| | | | | | |]; try (apply (GEN _ _); reflexivity).
  destruct (Z.eq_dec z 1) as [->|Hz].
  2: { destruct z as [|p|p]; try (apply (GEN _ _); reflexivity); destruct p as [p|p|]; try (apply (GEN _ _); reflexivity);
       exfalso; apply Hz; reflexivity. }
  destruct one.
  2: { (* [comment removed for export] *)
       destruct b as [c| | | | | | |]; try constructor.
       cbn [edenot] in Hv. rewrite u_sltu64 in Hv. rewrite u_sub64 in Hv. rewrite (u_lit64a c) in Hv.
       change (bv_unsigned (Z_to_bv 64 1)) with 1 in Hv.
       pose proof (u64_range (edenot E a)) as Ra.
       match type of Hv with context [if ?x then _ else _] => destruct x eqn:Hc end; [cbn in Hv; lia|].
       apply Z.ltb_ge in Hc. rewrite Zminus_mod_idemp_r in Hc.
       assert (Hne : bv_unsigned (edenot E a) <> c).
       { intros He. rewrite He, Z.sub_diag, Z.mod_0_l in Hc; lia. }
       assert (GENc : know_ok SEGS E M
                 match xlo k a, xhi k a with
                 | Some l, Some h => if Z.eqb l c then [KRange a (c + 1) h] else if Z.eqb h c then [KRange a l (c - 1)] else []
                 | _, _ => [] end).
       { destruct (xlo k a) as [l|] eqn:Hl; [|constructor]. destruct (xhi k a) as [h|] eqn:Hh; [|constructor].
         pose proof (xlo_sound SEGS E M k a l HK Hl). pose proof (xhi_sound SEGS E M k a h HK Hh).
         destruct (Z.eqb_spec l c); [constructor; [cbn [kentry_ok]; lia | constructor]|].
         destruct (Z.eqb_spec h c); [constructor; [cbn [kentry_ok]; lia | constructor]|]. constructor. }
       destruct c as [|p|p]; try exact GENc.
       (* [comment removed for export] *)
       destruct (xhi k a) as [h|] eqn:Hh; [|constructor].
       constructor; [|constructor]. cbn [kentry_ok]. split; [lia | exact (xhi_sound SEGS E M k a h HK Hh)]. }
  cbn [edenot] in Hv. rewrite u_sltu64 in Hv. rewrite u_sub64 in Hv.
  change (bv_unsigned (Z_to_bv 64 1)) with 1 in Hv.
  pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E b)) as Rb.
  match type of Hv with context [if ?c then _ else _] => destruct c eqn:Hc end; [|cbn in Hv; lia].
  apply Z.ltb_lt in Hc.
  assert (Hm0 : (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) mod 2 ^ 64 = 0) by (pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) (2 ^ 64) ltac:(lia)); lia).
  assert (Heq : bv_unsigned (edenot E a) = bv_unsigned (edenot E b)).
  { destruct (Z.le_gt_cases (bv_unsigned (edenot E b)) (bv_unsigned (edenot E a))).
    - rewrite Z.mod_small in Hm0 by lia. lia.
    - rewrite <- (Z.mod_add _ 1) in Hm0 by lia. rewrite Z.mod_small in Hm0 by lia. lia. }
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; rewrite SUBD, Heq, Z.sub_diag, Z.mod_0_l by lia; lia.
Qed.

Lemma fact_sound : forall E cs fx R M model K,
  cs_ok E cs fx R M model -> fact_ok (kn cs) K = true -> cs_ok E (add_kn cs [K]) fx R M model.
Proof.
  intros E cs fx R M model K HC H. unfold add_kn. apply cs_ok_set_kn; [exact HC|].
  constructor; [eapply fact_ok_sound; [exact (co_know HC) | exact H] | exact (co_know HC)].
Qed.

Lemma factvia_ok_sound : forall E M k e via lo hi,
  know_ok SEGS E M k -> factvia_ok k e via lo hi = true -> kentry_ok SEGS E M (KRange e lo hi).
Proof.
  intros E M k e via lo hi HK H. unfold factvia_ok in H.
  destruct (xlo2 k via) as [l1|] eqn:H1; [|discriminate]. destruct (xhi2 k via) as [h1|] eqn:H2; [|discriminate].
  destruct (xlo2 k (esub e via)) as [l2|] eqn:H3; [|discriminate]. destruct (xhi2 k (esub e via)) as [h2|] eqn:H4; [|discriminate].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.leb_le in H. apply Z.leb_le in X2. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
  pose proof (APS.xlo2_sound SEGS E M k via l1 HK H1) as B1. pose proof (APS.xhi2_sound SEGS E M k via h1 HK H2) as B2.
  pose proof (APS.xlo2_sound SEGS E M k (esub e via) l2 HK H3) as B3. pose proof (APS.xhi2_sound SEGS E M k (esub e via) h2 HK H4) as B4.
  unfold esub in B3, B4. rewrite mkAlu_denot, u_sub64 in B3, B4.
  cbn [kentry_ok]. pose proof (u64_range (edenot E e)) as Re. pose proof (u64_range (edenot E via)) as Rv.
  unfold two64 in *.
  assert (Hm : (bv_unsigned (edenot E e) - bv_unsigned (edenot E via)) mod 2 ^ 64
               = bv_unsigned (edenot E e) - bv_unsigned (edenot E via)
               \/ (bv_unsigned (edenot E e) - bv_unsigned (edenot E via)) mod 2 ^ 64
               = bv_unsigned (edenot E e) - bv_unsigned (edenot E via) + 2 ^ 64).
  { destruct (Z.leb_spec (bv_unsigned (edenot E via)) (bv_unsigned (edenot E e))).
    - left. apply Z.mod_small. lia.
    - right. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
  destruct Hm as [Hm|Hm]; rewrite Hm in B3, B4; lia.
Qed.

Lemma factle_ok_sound : forall E M k e big hi,
  know_ok SEGS E M k -> factle_ok k e big hi = true -> kentry_ok SEGS E M (KRange e 0 hi).
Proof.
  intros E M k e big hi HK H. unfold factle_ok in H. apply andb_prop in H as [Hge Hb].
  destruct (xhi2 k big) as [hb|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hb.
  pose proof (lin_ge0_sound SEGS E M k [(big, 0)] [(e, 0)] HK Hge) as Hle. cbn [xt_den] in Hle.
  pose proof (APS.xhi2_sound SEGS E M k big hb HK Hx) as B. cbn [kentry_ok]. pose proof (u64_range (edenot E e)). lia.
Qed.

Lemma factscale_ok_sound : forall E M k e c hi,
  know_ok SEGS E M k -> factscale_ok k e c hi = true -> kentry_ok SEGS E M (KRange e 0 hi).
Proof.
  intros E M k e c hi HK H. unfold factscale_ok in H.
  destruct (xlo k e) as [l0|] eqn:H0; [|discriminate]. destruct (xhi k e) as [h0|] eqn:H1; [|discriminate].
  destruct (xhi2 k (escale c e)) as [h|] eqn:H2; [|discriminate].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.leb_le in X.
  pose proof (xlo_sound SEGS E M k e l0 HK H0) as B0. pose proof (xhi_sound SEGS E M k e h0 HK H1) as B1.
  pose proof (APS.xhi2_sound SEGS E M k (escale c e) h HK H2) as B2.
  unfold escale in B2. rewrite mkMd_denot, u_mul64 in B2. cbn [edenot] in B2. rewrite u_lit64a in B2.
  cbn [kentry_ok]. pose proof (u64_range (edenot E e)) as Re. unfold two64 in *.
  assert (Hh : 0 <= h) by (pose proof (Z.mod_pos_bound (c mod 2 ^ 64 * bv_unsigned (edenot E e)) (2 ^ 64) ltac:(lia)); lia).
  split; [lia|].
  destruct (Z.eq_dec (bv_unsigned (edenot E e)) 0) as [Hz|Hnz].
  { rewrite Hz. apply (Z.le_trans _ (h / c)); [apply Z.div_pos; lia | exact X0]. }
  rewrite (Z.mod_small c) in B2 by nia. rewrite Z.mod_small in B2 by nia.
  apply (Z.le_trans _ (h / c)); [|exact X0]. apply Z.div_le_lower_bound; [lia|]. lia.
Qed.

Lemma casedisj_sound : forall cs b1 b2 csa csb E fx R M model,
  cs_ok E cs fx R M model -> node_casedisj cs b1 b2 = Some (csa, csb) ->
  (cs_ok E csa fx R M model /\ pc csa = pc cs) \/ (cs_ok E csb fx R M model /\ pc csb = pc cs).
Proof.
  intros cs b1 b2 csa csb E fx R M model HC H. unfold node_casedisj in H.
  pose proof (co_know HC) as HK.
  destruct (find_disj (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
  destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|cbn in H; discriminate].
  destruct (disj_side_fact (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
  destruct (disj_side_fact (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate].
  injection H as <- <-.
  pose proof (flat_x_sound SEGS E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound SEGS E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
  unfold elenZ in *.
  destruct (find_disj_sound SEGS E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as [Hd|Hd].
  - left. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hd].
  - right. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hd].
Qed.

Lemma havoc_sound : forall E cs fx R M model rs cs',
  cs_ok E cs fx R M model -> node_havoc nx0 cs rs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model rs cs' HC H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hf Hrs].
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_list E (nxt cs) (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs fx R M model Hag Hf HC) as HC'.
  destruct HC' as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_vis a_totsz a_eager]; try assumption; [|reflexivity].
  apply regs_ok_sr_fresh; [exact (co_regs HC) | exact Fsr |].
  apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
  apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
Qed.

Lemma havocbig_sound : forall E cs fx R M model K cs',
  cs_ok E cs fx R M model -> node_havocbig nx0 cs K = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model K cs' HC H. unfold node_havocbig in H.
  destruct (node_havoc nx0 cs _) as [cs1|] eqn:Hh; [|discriminate].
  destruct (fresh_ok nx0 cs1) eqn:Hf1; [|discriminate].
  destruct (kn_bigsubst K (kn cs1) (nxt cs1)) as [k' c] eqn:Hs. injection H as <-.
  destruct (havoc_sound E cs fx R M model _ cs1 HC Hh) as (E1 & [Hag0 Hag1] & HC1 & Hpc1).
  destruct (fresh_ok_parts nx0 cs1 Hf1) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (vals := map (edenot E1) (kn_bigexprs K (kn cs1))).
  set (E2 := ext_list E1 (nxt cs1) vals).
  assert (Hag2 : env_agree (nxt cs1) E1 E2) by apply ext_list_agree.
  assert (Hnx : (nxt cs <= nxt cs1)%nat).
  { destruct (node_havoc_nxt nx0 cs _ cs1 Hh) as [-> _]. lia. }
  exists E2. split; [|split; [|rewrite <- Hpc1; reflexivity]].
  { split; (eapply env_agree_trans; [|eapply env_agree_le; [exact Hag2 | lia]]); assumption. }
  pose proof (cs_ok_agree E1 E2 cs1 fx R M model Hag2 Hf1 HC1) as HC2.
  replace (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nxt cs1 + c))) with (set_kn (bump cs1 c) k') by reflexivity.
  apply cs_ok_set_kn; [apply cs_ok_bump; exact HC2|].
  replace k' with (fst (kn_bigsubst K (kn cs1) (nxt cs1))) by (rewrite Hs; reflexivity).
  apply kn_bigsubst_sound; [exact (co_know HC2) | rewrite kn_vars_lt_eq; rewrite <- kn_vars_lt_eq; exact Fkn |].
  intros i Hi. unfold E2. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hi).
  unfold vals. change (Z_to_bv 64 0) with (edenot E1 (ELit 0)). rewrite map_nth.
  eapply (edenot_agree' (nxt cs1)); [apply ext_list_agree|].
  clear - Fkn Hi. revert i Hi. generalize (kn cs1) Fkn. intros k Hk.
  induction k as [|x r IH]; intros i Hi; [cbn in Hi; lia|].
  cbn [AP.kn_vars_lt] in Hk. apply andb_prop in Hk as [Hx Hr]. cbn [kn_bigexprs] in Hi |- *.
  destruct x as [a w v| | | | | | | | |]; try (apply IH; assumption).
  destruct (bigb K v); [|apply IH; assumption].
  destruct i as [|i]; cbn [nth]; [cbn [AP.kentry_vars_lt] in Hx; apply andb_prop in Hx as [_ Hx]; exact Hx | apply IH; [exact Hr | cbn [length] in Hi; lia]].
Qed.

Lemma fresh_sound : forall r logc base cs cs' E fx R M model,
  cs_ok E cs fx R M model -> node_fresh nx0 cs r logc base = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros r logc base cs cs' E fx R M model HC Hn. rewrite node_fresh_eq in Hn. unfold node_fresh_ref in Hn.
  set (b := match base with Some b => b | None => ELit 0 end) in Hn.
  set (e := esub (reg cs r) b) in Hn.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign (kn cs) e)
            && AP.expr_vars_lt (nxt cs) b && AP.expr_vars_lt (nxt cs) e && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hve]. apply andb_prop in Hc as [Hc Hvb].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc H40]. apply andb_prop in Hc as [Hc H0].
  apply andb_prop in Hc as [Hr0 Hr32].
  apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32. apply Z.leb_le in H0. apply Z.leb_le in H40. apply Z.leb_le in Hal.
  destruct (xlo2 (kn cs) e) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi2 (kn cs) e) as [hi|] eqn:Hhi; [|discriminate].
  injection Hn as <-.
  set (c := 2 ^ logc) in *. set (v := nxt cs) in *.
  pose proof (co_know HC) as HK.
  pose proof (xlo2_sound SEGS E _ (kn cs) e lo HK Hlo) as Hlo'.
  pose proof (xhi2_sound SEGS E _ (kn cs) e hi HK Hhi) as Hhi'.
  destruct (ealign_sound SEGS E _ (kn cs) e HK) as [Hea Hdiv].
  assert (Hcpos : 0 < c) by (unfold c; apply Z.pow_pos_nonneg; lia).
  assert (Hc2 : c <= 2 ^ 40) by (unfold c; apply Z.pow_le_mono_r; lia).
  assert (Hcd : (c | bv_unsigned (edenot E e))%Z).
  { eapply Z.divide_trans; [|exact Hdiv]. unfold c. apply pow2_divide_le. lia. }
  destruct Hcd as [q Hq].
  pose proof (u64_range (edenot E e)) as Hue.
  assert (Hq0 : 0 <= q) by nia.
  assert (Hq64 : q < 2 ^ 64) by nia.
  set (a := Z_to_bv 64 q). set (E' := ext1 E v a).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (cs_ok_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  assert (Hev : edenot E' e = edenot E e) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hve]).
  assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hvb]).
  assert (Hrv : edenot E' (reg cs r) = edenot E (reg cs r)).
  { symmetry. eapply (edenot_agree' v); [exact Hag|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
  assert (Hne : edenot E' (escale c (EVar v)) = edenot E e).
  { unfold escale. rewrite mkMd_denot. cbn [edenot]. unfold E'. rewrite ext1_at. unfold a.
    apply bv_eq. rewrite u_mul64. rewrite (u_small c) by lia. rewrite (u_small q) by lia. rewrite Z.mod_small by nia. lia. }
  assert (He_sem : edenot E e = alu64 ALU_SUB (edenot E (reg cs r)) (edenot E b)) by (unfold e, esub; apply mkAlu_denot).
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (HKf : know_ok SEGS E' M
            ((KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e (escale c (EVar v))) 0 0
               :: residue_fact (kn cs) e (escale c (EVar v)))
             ++ kn cs)).
  { apply Forall_app. split; [|exact (co_know HC')].
    constructor; [|constructor].
    - cbn [kentry_ok edenot]. unfold E' at 1 2. rewrite ext1_at. unfold a. rewrite u_small by lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; nia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - cbn [kentry_ok]. unfold esub. rewrite !mkAlu_denot, !Hne, !Hev.
      rewrite !u_sub64. rewrite Z.sub_diag, Z.mod_0_l by lia. lia.
    - eapply (residue_fact_sound SEGS E E' _ _ (kn cs) e); [exact HK | exact Hne |].
      intros e1 s1 Hd1. symmetry. eapply (edenot_agree' v); [exact Hag | exact (deand_vars v e e1 s1 Hd1 Hve)]. }
  destruct HC' as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor; cbn [bump set_reg add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_vis a_totsz a_eager]; try assumption.
  - apply regs_ok_respell; [exact CR | lia |].
    unfold eadd. rewrite mkAlu_denot, Hne, Hbv. fold (reg cs r). rewrite Hrv, He_sem.
    apply bv_eq. rewrite u_add64, u_sub64. pose proof (u64_range (edenot E (reg cs r))). pose proof (u64_range (edenot E b)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E b) + (bv_unsigned (edenot E (reg cs r)) - bv_unsigned (edenot E b))) with (bv_unsigned (edenot E (reg cs r))) by lia.
    rewrite Z.mod_small by lia. reflexivity.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma intro_sound : forall E cs fx R M model lo hi cs',
  cs_ok E cs fx R M model -> node_intro nx0 cs lo hi = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model lo hi cs' HC H. unfold node_intro in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 lo)).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs fx R M model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : bv_unsigned (edenot E' (EVar v)) = lo).
  { cbn [edenot]. unfold E'. rewrite ext1_at. unfold two64 in H3. apply u_small. lia. }
  replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (KRange (EVar v) lo hi :: s_know (a_ss cs)) (S v)))
    with (set_kn (bump cs 1) (KRange (EVar v) lo hi :: kn cs)).
  2:{ unfold set_kn, bump, with_ss, mk_ss, kn. cbn. rewrite Nat.add_1_r. reflexivity. }
  apply cs_ok_set_kn; [apply cs_ok_bump; exact HC'|].
  constructor; [|exact (co_know HC')]. cbn [kentry_ok]. rewrite Hv. lia.
Qed.

Lemma join_sound : forall b off n cs cs' E fx R M model,
  cs_ok E cs fx R M model -> node_join SEGS cs b off n = Some cs' -> cs_ok E cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros b off n cs cs' E fx R M model HC Hn. unfold node_join in Hn.
  destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  pose proof (co_know HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia.
  destruct (kread_bytes_sound SEGS E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
  split; [|reflexivity].
  unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [unfold flat; lia|].
  rewrite (rdn_of_bytes1 SEGS _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n)); [lia | unfold flat; lia].
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n)) by (unfold flat; lia). exact (Rb j Hj).
Qed.

Lemma abstractcell_sound : forall E cs fx R M model b n cs',
  cs_ok E cs fx R M model -> node_abstractcell A cs b n = Some cs' -> cs_ok E cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model b n cs' HC H. unfold node_abstractcell in H.
  destruct (split_lit b) as [bb bo]. cbv zeta in H.
  destruct (kunk_covered A (kn cs) (KUnk (SA bb bo) (ELit n))) eqn:Hcov; [|discriminate].
  injection H as <-. split; [|apply pc_set_kn].
  apply cs_ok_set_kn; [exact HC|]. constructor.
  - eapply kunk_covered_sound; [exact SEGS_in_hull | exact HULL_ok | exact (co_know HC) | exact Hcov].
  - eapply know_ok_cutout; [exact (co_know HC) | intros; reflexivity].
Qed.

Lemma havocwords_sound : forall E cs fx R M model bs cs',
  cs_ok E cs fx R M model -> node_havocwords nx0 cs bs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model bs cs' HC H. unfold node_havocwords in H.
  destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate]. injection H as <-.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (hw_go_ok SEGS bs E M (kn cs) (nxt cs) (co_know HC)) as (E' & Hag & HK' & _).
  { rewrite kn_vars_lt_eq. rewrite <- kn_vars_lt_eq. exact Fkn. }
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs fx R M model Hag Hf HC) as HC2.
  replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (hw_go (s_know (a_ss cs)) bs (s_next (a_ss cs))) (s_next (a_ss cs) + length bs)))
    with (set_kn (bump cs (length bs)) (hw_go (kn cs) bs (nxt cs))) by reflexivity.
  apply cs_ok_set_kn; [apply cs_ok_bump; exact HC2 | exact HK'].
Qed.

Lemma respell_sound : forall E cs fx R M model r e cs',
  cs_ok E cs fx R M model -> node_respell cs r e = Some cs' -> cs_ok E cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros E cs fx R M model r e cs' HC H. unfold node_respell in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && AP.expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
  pose proof (respell_ok_sound SEGS E _ (kn cs) (reg cs r) e (co_know HC) Hok) as Heq.
  split; [|reflexivity].
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_vis a_totsz a_eager]; try assumption; try reflexivity.
  apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma entails_sound : forall E cs ch fx R M model,
  cs_ok E cs fx R M model -> entails cs ch = true -> cs_ok E ch fx R M model /\ pc ch = pc cs.
Proof.
  intros E cs ch fx R M model HC H. unfold entails in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc. split; [|symmetry; exact Hpc].
  match goal with Hl : match s_log (a_ss ch) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss ch)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hr : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hr; rename Hr into Hregs end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hvis end.
  match goal with Hk : forallb _ (kn ch) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hm : list_eqb amap_eqb (a_maps cs) _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL]; constructor; rewrite <- ?Hregs, <- ?Hvis, <- ?Hghost, <- ?Hbrk, <- ?Hmaps; try assumption.
  2:{ (* [comment removed for export] *) eapply floor_sem_weaken; [|exact CFL]. assumption. }
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (forallb_forall _ _) Hkn K Hin) as HK. apply existsb_exists in HK as [K' [Hin' Heq]].
  apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) CK K Hin').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_sound : forall E cs fx R M model n,
  cs_ok E cs fx R M model -> (0 < n < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof.
  intros E cs fx R M model n HC Hn. rewrite (co_regs HC). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

Lemma reg_lit_sound : forall E cs fx R M model n z,
  cs_ok E cs fx R M model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E cs fx R M model n z HC Hn H. unfold reg_lit in H.
  destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs fx R M model n HC Hn), He. auto.
Qed.

Lemma is_ecall_at_sound : forall cs, is_ecall_at SEGS cs = true ->
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true /\ 0 <= pc cs /\ pc cs + 4 < 2 ^ 64.
Proof.
  intros cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|]; [|discriminate].
  exists w. unfold two64 in H4. repeat split; auto.
Qed.

(* [comment removed for export] *)
Definition ependF (fx : FX) (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := @fp_regs fx; ms_pc_val := pc;
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := @fp_csr fx;
     ms_mem := mem; ms_rom := rom |}.

Lemma step_ecallF : forall fx regs pc mem rom w,
  fetch_word SEGS pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step SEGS (mkstF fx regs pc mem rom) = MachineOk (ependF fx regs pc mem rom (getr regs 17)).
Proof.
  intros fx regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses.
  cbn [ms_pc ms_pc_val mkstF mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota. reflexivity.
Qed.

Lemma ms_gpr_ependF0 : forall fx regs pc mem rom x8, ms_gpr (ependF fx regs pc mem rom x8) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs ependF]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.

Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
  bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
  intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply u64_lit. unfold two64 in *.
  pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma node_exit_sound : forall cs code E fx R M model,
  cs_ok E cs fx R M model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
  RZ (cfg fx R (pc cs) M model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros cs code E fx R M model HC Hec Hn.
  destruct (is_ecall_at_sound cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  unfold node_exit in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [c0|] eqn:H10.
  2:{ destruct a7; try discriminate; repeat (destruct p; try discriminate). }
  destruct (reg_lit_sound E cs fx R M model 10 c0 HC ltac:(lia) H10) as [G10 Hc0].
  assert (H94 : (a7 = 94 \/ a7 = 93) /\ code = Z.land c0 255).
  { destruct a7 as [|p|p]; try discriminate;
      repeat (destruct p as [p|p|]; try discriminate); injection Hn as <-; auto. }
  destruct H94 as [Ha7 ->].
  assert (G17 : getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94 \/ getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 93).
  { destruct Ha7 as [-> | ->].
    - left. exact (proj1 (reg_lit_sound E cs fx R M model 17 94 HC ltac:(lia) H17)).
    - right. exact (proj1 (reg_lit_sound E cs fx R M model 17 93 HC ltac:(lia) H17)). }
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E10 in G10. rewrite E17 in G17.
  unfold cfgF. rewrite <- (bv_and_255 c0 Hc0).
  eapply RZ_step; [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply step_ecallF; eassumption |].
  rewrite <- G10. rewrite <- (ms_gpr_ependF0 fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS) (getr R 17)).
  eapply RZ_exit; [exact (co_halt HC) | reflexivity |].
  destruct G17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blocks_den_psubst : forall E J e l,
  blocks_den E (map (psubst J e) l) = blocks_den (upd E J (edenot E e)) l.
Proof.
  intros E J e l. unfold blocks_den. rewrite map_map. apply map_ext. intros [b n]. unfold psubst. cbn [fst snd].
  unfold uE. rewrite !esubst_denot. reflexivity.
Qed.

Lemma wins_den_psubst : forall E J e l,
  wins_den E (map (psubst J e) l) = wins_den (upd E J (edenot E e)) l.
Proof.
  intros E J e l. unfold wins_den. rewrite map_map. apply map_ext. intros [b n]. unfold psubst. cbn [fst snd].
  unfold uE. rewrite !esubst_denot. reflexivity.
Qed.

Lemma sptop_den_esubst : forall E J e x, sptop_den E (esubst J e x) = sptop_den (upd E J (edenot E e)) x.
Proof. intros. unfold sptop_den, uE. rewrite esubst_denot. reflexivity. Qed.
Lemma floor_sem_msubst : forall E J e ms top bud,
  floor_sem E (acs_floor (map (msubst J e) ms)) (esubst J e top) bud <-> floor_sem (upd E J (edenot E e)) (acs_floor ms) top bud.
Proof.
  intros. destruct ms as [|[f l kd] r]; cbn [map msubst acs_floor floor_sem am_base am_len am_kind];
    [rewrite sptop_den_esubst; tauto | unfold uE; rewrite esubst_denot; tauto].
Qed.
Lemma bcost_psubst : forall E J e l, bcost E (map (psubst J e) l) = bcost (upd E J (edenot E e)) l.
Proof.
  intros E J e l. induction l as [|[b n] r IH]; [reflexivity|]. cbn [map bcost psubst fst snd]. unfold uE. rewrite esubst_denot, IH. reflexivity.
Qed.


Lemma cs_ok_inst : forall E J e inv fx R M model, (nx0 <= J)%nat -> s_log (a_ss inv) = [] ->
  cs_ok E (inst inv J e) fx R M model <-> cs_ok (upd E J (edenot E e)) inv fx R M model.
Proof.
  intros E J e inv fx R M model HJ Hlog.
  assert (AG : env_agree nx0 E (upd E J (edenot E e))) by (eapply env_agree_le; [apply upd_agree | exact HJ]).
  pose proof (blocks_den_psubst E J e (a_vis inv)) as HV.
  pose proof (wins_den_psubst E J e (a_ghost inv)) as HG.
  pose proof (sptop_den_esubst E J e (a_brk inv)) as HB.
  pose proof (bcost_psubst E J e (a_vis inv)) as HBC.
  pose proof (floor_sem_msubst E J e (a_maps inv) (a_brk inv) (a_ylo inv)) as HFL.
  assert (AG' : env_agree nx0 (upd E J (edenot E e)) E).
  { destruct AG as [AG1 AG2]. split; [intros n Hn; symmetry; apply AG1; exact Hn | symmetry; exact AG2]. }
  split; intros HC; destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor;
    cbn [inst a_ss s_regs s_log s_know kn a_totsz a_eager a_vis a_ghost a_brk mk_ss] in *; try assumption; try reflexivity;
    unfold bcount in *; rewrite ?length_map in *;
    first [ apply regs_ok_inst; assumption
          | apply (proj1 (regs_ok_inst _ _ _ _ _)); assumption
          | apply know_ok_ksubst; assumption
          | apply (proj1 (know_ok_ksubst _ _ _ _ _ _)); assumption
          | rewrite <- HV, <- HBC; assumption
          | rewrite HV, HBC; assumption
          | rewrite <- HG; assumption
          | rewrite HG; assumption
          | rewrite <- HB; assumption
          | rewrite HB; assumption
          | apply (proj1 HFL); assumption
          | apply (proj2 HFL); assumption
          | eapply UINV_agree; [exact AG | assumption]
          | eapply UINV_agree; [exact AG' | assumption] ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tenv (E : env) (th : list expr) : env :=
  Env (fun n => if Nat.ltb n (length th) then edenot E (nth n th (ELit 0)) else ev E n) (eb E).

Lemma tsubst_denot : forall E th x, edenot E (tsubst th x) = edenot (tenv E th) x.
Proof.
  intros E th x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [tsubst edenot]; try reflexivity.
  - cbn [tenv ev]. destruct (Nat.ltb n (length th)); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.
Lemma estart_atsubst : forall E th a, estart E (atsubst th a) = estart (tenv E th) a.
Proof. intros E th [b o]. unfold atsubst, estart. cbn [a_base a_off]. rewrite tsubst_denot. reflexivity. Qed.
Lemma adenot_atsubst : forall E th a, adenot E (atsubst th a) = adenot (tenv E th) a.
Proof. intros E th [b o]. unfold atsubst, adenot. cbn [a_base a_off]. rewrite tsubst_denot. reflexivity. Qed.
Lemma kentry_ok_ktsubst : forall E th M K,
  kentry_ok SEGS E M (ktsubst th K) <-> kentry_ok SEGS (tenv E th) M K.
Proof.
  intros E th M K. set (E' := tenv E th).
  destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ktsubst kentry_ok];
    unfold flat, elenZ; rewrite ?estart_atsubst, ?adenot_atsubst, ?tsubst_denot; fold E'; tauto.
Qed.
Lemma know_ok_ktsubst : forall E th M k,
  know_ok SEGS E M (map (ktsubst th) k) <-> know_ok SEGS (tenv E th) M k.
Proof.
  intros E th M k. unfold know_ok. induction k as [|K k IH]; [split; intros; constructor|].
  cbn [map]. split; intros H; inversion H; subst; constructor; try (apply IH; assumption);
    apply (kentry_ok_ktsubst E th M K); assumption.
Qed.
Lemma regs_ok_tsubst : forall E th sr R,
  regs_ok E (map (tsubst th) sr) R <-> regs_ok (tenv E th) sr R.
Proof.
  intros E th sr R. unfold regs_ok, sr_get.
  assert (G : forall r, edenot E (if bv_eqb r 0 then ELit 0 else nth (ridx r) (map (tsubst th) sr) (ELit 0))
                     = edenot (tenv E th) (if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0))).
  { intros r. destruct (bv_eqb r 0); [reflexivity|].
    replace (ELit 0) with (tsubst th (ELit 0)) at 1 by reflexivity. rewrite map_nth. apply tsubst_denot. }
  split; intros H r; [rewrite <- G | rewrite G]; apply H.
Qed.
Lemma blocks_den_ptsubst : forall E th l, blocks_den E (map (ptsubst th) l) = blocks_den (tenv E th) l.
Proof.
  intros E th l. unfold blocks_den. rewrite map_map. apply map_ext. intros [b n]. unfold ptsubst. cbn [fst snd].
  unfold uE. rewrite !tsubst_denot. reflexivity.
Qed.
Lemma bcost_ptsubst : forall E th l, bcost E (map (ptsubst th) l) = bcost (tenv E th) l.
Proof.
  intros E th l. induction l as [|[b n] r IH]; [reflexivity|]. cbn [map bcost ptsubst fst snd].
  unfold uE. rewrite tsubst_denot, IH. reflexivity.
Qed.
Lemma bcost_perm : forall E l l', Permutation.Permutation l l' -> bcost E l = bcost E l'.
Proof. intros E l l' HP. induction HP; cbn [bcost]; lia. Qed.
Lemma bcount_perm : forall l l' : list (expr * expr), Permutation.Permutation l l' -> bcount l = bcount l'.
Proof. intros l l' HP. unfold bcount. rewrite (Permutation.Permutation_length HP). reflexivity. Qed.
Lemma wins_den_ptsubst : forall E th l, wins_den E (map (ptsubst th) l) = wins_den (tenv E th) l.
Proof.
  intros E th l. unfold wins_den. rewrite map_map. apply map_ext. intros [b n]. unfold ptsubst. cbn [fst snd].
  unfold uE. rewrite !tsubst_denot. reflexivity.
Qed.
Lemma sptop_den_tsubst : forall E th x, sptop_den E (tsubst th x) = sptop_den (tenv E th) x.
Proof. intros. unfold sptop_den, uE. rewrite tsubst_denot. reflexivity. Qed.


(* [comment removed for export] *)
Lemma th_id_below_agree : forall lo th E, th_id_below lo th = true -> env_agree lo E (tenv E th).
Proof.
  intros lo th E H. unfold th_id_below in H. split; [|reflexivity]. intros n Hn. cbn [tenv ev].
  destruct (Nat.ltb_spec n (length th)) as [Hlt|Hge]; [|reflexivity].
  pose proof (proj1 (forallb_forall _ _) H n ltac:(apply in_seq; lia)) as Hi. cbn beta in Hi.
  destruct (nth_error th n) as [x|] eqn:Hx; [| apply nth_error_None in Hx; lia].
  destruct x as [z|j| | | | | |]; try discriminate. apply Nat.eqb_eq in Hi. subst j.
  rewrite (nth_error_nth _ _ _ Hx). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kpure_entails_sound : forall E M k K,
  know_ok SEGS E M k -> kpure_entails k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. rewrite kpure_entails_eq in H. destruct K as [a w v|a n|a n kb|lo hi|e m|e lo hi|a n|[b1 o1] n1 [b2 o2] n2|a n c|a n]; try discriminate; cbn [kentry_ok kpure_entails_ref] in *.
  - (* [comment removed for export] *)
    apply andb_prop in H as [Hm Hd]. apply Z.ltb_lt in Hm. apply Z.eqb_eq in Hd.
    destruct (ealign_sound SEGS E M k e HK) as [A1 [q Hq]]. split; [lia|].
    apply Z.mod_divide in Hd; [|lia]. destruct Hd as [r Hr]. rewrite Hq, Hr.
    rewrite Z.mul_assoc. apply Z_mod_mult.
  - (* [comment removed for export] *)
    apply orb_prop in H as [H|H].
    + destruct (xlo2 k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi2 k e) as [h|] eqn:Hh; [|discriminate].
      apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
      pose proof (APS.xlo2_sound SEGS E M k e l HK Hl). pose proof (APS.xhi2_sound SEGS E M k e h HK Hh). lia.
    + assert (HH : (krange_lin k e lo hi || (lin_ge0 k [(e, 0)] [(ELit 0, lo)] && lin_ge0 k [(ELit 0, hi)] [(e, 0)])
                    || (lin_ge0d 2 k [(e, 0)] [(ELit 0, lo)] && lin_ge0d 2 k [(ELit 0, hi)] [(e, 0)]))%bool = true) by (destruct e; try discriminate H; exact H).
      clear H. apply orb_prop in HH as [HH|HH]; [apply orb_prop in HH as [HL|HH]|].
      3: { apply andb_prop in HH as [H1 H2].
           pose proof (lin_ge0d_sound 2 SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0d_sound 2 SEGS E M k _ _ HK H2) as A2.
           cbn [xt_den edenot] in A1, A2. rewrite u_small in A1, A2 by (pose proof two64_pos; lia). lia. }
      2: { apply andb_prop in HH as [H1 H2].
           pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
           cbn [xt_den edenot] in A1, A2. rewrite u_small in A1, A2 by (pose proof two64_pos; lia). lia. }
      { (* [comment removed for export] *)
        unfold krange_lin in HL. rewrite !lin_testd12_eq in HL. repeat (apply andb_prop in HL as [HL ?X]).
        apply Z.leb_le in HL. apply Z.ltb_lt in X1.
        assert (LT : forall t, (lin_testd 1 k (fst (lin_of e)) (snd (lin_of e)) t || lin_testd 2 k (fst (lin_of e)) (snd (lin_of e)) t)%bool = true ->
                     exists lo' hi', t lo' hi' = true /\ (lo' <= fst (lin_of e) + tden E (snd (lin_of e)) <= hi')%Z).
        { intros t Ht. apply orb_prop in Ht as [Ht|Ht]; [exact (lin_testd_sound 1 SEGS E M k _ _ _ HK Ht) | exact (lin_testd_sound 2 SEGS E M k _ _ _ HK Ht)]. }
        destruct (LT _ X0) as (l1 & h1 & T1 & B1).
        destruct (LT _ X) as (l2 & h2 & T2 & B2).
        apply Z.leb_le in T1. apply Z.leb_le in T2.
        pose proof (lin_of_sound E e) as [q Hq]. unfold lden, AX2S.uE in Hq.
        pose proof (u64_range (edenot E e)) as Re. unfold two64 in *.
        cbn beta in T1, T2.
        set (V := (fst (lin_of e) + tden E (snd (lin_of e)))%Z) in *.
        change (2 ^ 64)%Z with 18446744073709551616%Z in *.
        assert (Hq0 : q = 0) by (destruct (Z.le_gt_cases 1 q); [nia|]; destruct (Z.le_gt_cases q (-1)); [nia|lia]).
        subst q. lia. }
  - (* [comment removed for export] *)
    exact (APS.disj_x_sound SEGS E M k b1 o1 n1 b2 o2 n2 HK H).
Qed.
Lemma kn_ent_sound : forall E M k tk, know_ok SEGS E M k -> kn_ent A k tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k tk HK H. rewrite kn_ent_eq in H. apply Forall_forall. intros K Hin.
  pose proof (proj1 (forallb_forall _ _) H K Hin) as HK1. apply orb_prop in HK1 as [H1|H1]; [|rewrite <- kpure_entails_eq in H1].
  - assert (H2 : kn_incl_h A k [K] = true) by (unfold kn_incl_h; cbn [forallb]; rewrite H1; reflexivity).
    exact (Forall_inv (kn_incl_h_sound SEGS A SEGS_in_hull HULL_ok E M k [K] HK H2)).
  - exact (kpure_entails_sound E M k K HK H1).
Qed.
(* [comment removed for export] *)
Lemma regs_ent_sound : forall E M k ts cs0 i,
  know_ok SEGS E M k -> regs_ent k i ts cs0 = true ->
  length ts = length cs0 /\ forall n, (i + n <> 0)%nat -> edenot E (nth n ts (ELit 0)) = edenot E (nth n cs0 (ELit 0)).
Proof.
  intros E M k ts. induction ts as [|t ts IH]; intros cs0 i HK H; destruct cs0 as [|c cs0]; try discriminate; cbn [regs_ent] in H.
  - split; [reflexivity|]. intros [|n] _; reflexivity.
  - apply andb_prop in H as [H1 H2]. destruct (IH cs0 (S i) HK H2) as [Hlen Hn]. split; [cbn; lia|].
    intros [|n] Hnz; cbn [nth].
    + apply orb_prop in H1 as [H1|H1]; [apply orb_prop in H1 as [H1|H1]|].
      * apply Nat.eqb_eq in H1. lia.
      * apply expr_eqb_eq in H1. subst. reflexivity.
      * symmetry. exact (respell_ok_sound SEGS E M k c t HK H1).
    + apply Hn. lia.
Qed.

Lemma entails_t_sound : forall lo E cs T th fx R M model,
  cs_ok E cs fx R M model -> entails_t A lo cs T th = true -> (nx0 <= lo)%nat ->
  exists E', env_agree lo E E' /\ cs_ok E' T fx R M model /\ pc T = pc cs.
Proof.
  intros lo E cs T th fx R M model HC H Hlo. unfold entails_t in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => clear Hl end.
  match goal with Hl : th_id_below lo th = true |- _ => rename Hl into Hid end.
  match goal with Hl : regs_ent _ _ _ _ = true |- _ => rename Hl into Hregs end.
  match goal with Hl : kn_ent _ _ _ = true |- _ => rename Hl into Hkn end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_vis T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hvis end.
  match goal with Hl : list_eqb pair_eqb (map (ptsubst th) (a_ghost T)) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hl; rename Hl into Hgh end.
  match goal with Hl : expr_eqb (tsubst th (a_brk T)) _ = true |- _ => apply expr_eqb_eq in Hl; rename Hl into Hbrk end.
  match goal with Hl : Z.leb (a_ylo T) (a_ylo cs) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hylo end.
  match goal with Hl : list_eqb amap_eqb (a_maps cs) (a_maps T) = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hl; rename Hl into Hmaps end.
  match goal with Hl : AP.maps_vars_lt lo (a_maps T) = true |- _ => rename Hl into Hmv end.
  set (E' := tenv E th). exists E'.
  assert (Hag : env_agree lo E E') by (apply th_id_below_agree; exact Hid).
  split; [exact Hag|]. split; [|symmetry; exact Hpc].
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL]; constructor; try assumption.
  - (* [comment removed for export] *)
    apply (proj1 (regs_ok_tsubst E th (s_regs (a_ss T)) R)).
    destruct (regs_ent_sound E M (kn cs) _ _ 0%nat CK Hregs) as [Hlen Hn].
    intros r. rewrite (CR r). unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|]. symmetry. apply Hn.
    intros Hz. cbn in Hz. unfold ridx in Hz. unfold bv_eqb in Hr0. apply Z.eqb_neq in Hr0. apply Hr0.
    change (bv_unsigned r = 0). pose proof (u5_range r). lia.
  - (* [comment removed for export] *)
    apply (proj1 (know_ok_ktsubst E th M (kn T))). eapply kn_ent_sound; [exact CK | exact Hkn].
  - (* [comment removed for export] *)
    unfold E'. rewrite <- blocks_den_ptsubst, <- bcost_ptsubst, Hvis. unfold bcount in *. rewrite <- (length_map (ptsubst th)), Hvis. exact CA.
  - (* [comment removed for export] *) eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Hlo] | exact CU].
  - (* [comment removed for export] *) unfold E'. rewrite <- wins_den_ptsubst, Hgh. exact CP.
  - (* [comment removed for export] *) unfold E'. rewrite <- sptop_den_tsubst, Hbrk. exact CT.
  - (* [comment removed for export] *)
    rewrite <- Hmaps. eapply (floor_sem_xfer E E' (a_maps cs) (a_brk cs) (a_brk T) (a_ylo cs) (a_ylo T)); [| | exact Hylo | exact CFL].
    + intros f l kd r Hm. unfold uE. rewrite <- Hmaps, Hm in Hmv. cbn [AP.maps_vars_lt forallb am_base am_len] in Hmv.
      apply andb_prop in Hmv as [Hmv _]. apply andb_prop in Hmv as [Hf _].
      rewrite <- (edenot_agree' lo E E' f Hag Hf). reflexivity.
    + unfold E'. rewrite <- sptop_den_tsubst, Hbrk. reflexivity.
Qed.

Lemma entails_tw_sound : forall lo hi w E cs T fx R M model,
  cs_ok E cs fx R M model -> entails_tw A lo hi w cs T = true -> (nx0 <= lo)%nat ->
  exists E', env_agree lo E E' /\ cs_ok E' T fx R M model /\ pc T = pc cs.
Proof. intros lo hi w E cs T fx R M model HC H Hlo. rewrite entails_tw_eq in H. apply andb_prop in H as [_ H]. eapply entails_t_sound; eassumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cs_ok_reenv : forall b E E' cs sr' fx R M model,
  cs_ok E cs fx R M model -> env_agree b E E' -> (nx0 <= b)%nat ->
  AP.kn_vars_lt b (kn cs) = true -> pairs_vars_lt b (a_vis cs) = true ->
  pairs_vars_lt b (a_ghost cs) = true -> AP.expr_vars_lt b (a_brk cs) = true -> AP.maps_vars_lt b (a_maps cs) = true ->
  regs_ok E' sr' R ->
  cs_ok E' (set_regs cs sr') fx R M model.
Proof.
  intros b E E' cs sr' fx R M model HC Hag Hb Hkn Hvis Hgh Hbrk Hmv HR.
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT]; constructor;
    cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_totsz a_eager a_vis a_ghost a_brk] in *; try assumption; try reflexivity.
  - eapply know_ok_agree'; eassumption.
  - rewrite (blocks_den_agree b E E' (a_vis cs) Hag Hvis). rewrite (bcost_agree b E E' (a_vis cs) Hag Hvis). assumption.
  - eapply UINV_agree; [eapply env_agree_le; [exact Hag | exact Hb] | assumption].
  - rewrite (wins_den_agree b E E' (a_ghost cs) Hag Hgh). assumption.
  - rewrite (sptop_den_agree b E E' (a_brk cs) Hag Hbrk). assumption.
  - cbn [a_ylo a_maps]. eapply (floor_sem_agree b E E'); [exact Hag | exact Hbrk | exact Hmv | assumption].
Qed.

Lemma entails_h_sound : forall lo hi E cs T fx R M model,
  cs_ok E cs fx R M model -> entails_h A lo hi cs T = true -> (nx0 <= lo)%nat -> length (s_regs (a_ss T)) = 32%nat ->
  exists E', env_agree lo E E' /\ (forall n, (hi <= n)%nat -> ev E' n = ev E n) /\ cs_ok E' T fx R M model /\ pc T = pc cs.
Proof.
  intros lo hi E cs T fx R M model HC H Hlo Hlen. unfold entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => rename Hl into HRV; destruct (s_resv (a_ss T)) eqn:HRV'; [discriminate|clear HRV; rename HRV' into HRV] end.
  match goal with Hr : regs_match_h _ _ _ _ _ = true |- _ => rename Hr into Hregs end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hvis end.
  match goal with Hk : kn_incl_h _ _ (kn T) = true |- _ => rename Hk into Hkn end.
  match goal with Hk : AP.kn_vars_lt lo (kn T) = true |- _ => rename Hk into Hknv end.
  match goal with Hk : pairs_vars_lt lo (a_vis T) = true |- _ => rename Hk into Hvisv end.
  match goal with Hk : pairs_vars_lt lo (a_ghost T) = true |- _ => rename Hk into Hghv end.
  match goal with Hk : AP.expr_vars_lt lo (a_brk T) = true |- _ => rename Hk into Hbrkv end.
  match goal with Hk : AP.maps_vars_lt lo (a_maps T) = true |- _ => rename Hk into Hmapsv end.
  match goal with Ha : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hm : list_eqb amap_eqb (a_maps cs) _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  set (E' := henv lo hi E (s_regs (a_ss cs)) (s_regs (a_ss T))).
  exists E'. split; [apply henv_agree|]. split; [intros; apply henv_high; assumption|]. split; [|symmetry; exact Hpc].
  (* [comment removed for export] *)
  set (Tc := set_regs T (s_regs (a_ss cs))).
  assert (HC1 : cs_ok E Tc fx R M model).
  { destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL]; constructor;
      try (unfold Tc; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_totsz a_eager a_vis a_ghost a_brk a_ylo a_maps];
           rewrite <- ?Hvis, <- ?Hghost, <- ?Hbrk, <- ?Hmaps; first [assumption | reflexivity | lia | eapply floor_sem_weaken; [|exact CFL]; assumption]).
    unfold Tc. cbn [set_regs with_ss a_ss mk_ss s_know kn]. eapply kn_incl_h_sound; [exact SEGS_in_hull | exact HULL_ok | exact CK | exact Hkn]. }
  (* [comment removed for export] *)
  assert (ET : T = set_regs Tc (s_regs (a_ss T))).
  { subst Tc. clear - HL HRV. destruct T as [[p sr lg k nx rv] m t y e v g ab br f ti]. cbn in HL, HRV. subst lg rv. reflexivity. }
  rewrite ET at 1. eapply (cs_ok_reenv lo); try eassumption.
  - apply henv_agree.
  - apply regs_match_h_sound; [exact Hregs | exact Hlen | exact (co_regs HC)].
Qed.

Lemma diamond_join_sound : forall nx joinpc rs ca cb csj,
  node_diamond_join A nx0 nx joinpc rs ca cb = Some csj ->
  (forall E fx R M model, cs_ok E ca fx R M model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj fx R M model /\ pc csj = pc ca)
  /\ (forall E fx R M model, cs_ok E cb fx R M model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj fx R M model /\ pc csj = pc cb).
Proof.
  intros nx joinpc rs ca cb csj H. unfold node_diamond_join in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  match goal with Hl : Nat.eqb (length ?l) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
  match goal with Hl : Nat.leb nx0 ?v = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hn0 end.
  split; intros E fx R M model HC.
  - match goal with Hea : entails_h A ?lo ?hi ca ?T = true |- _ =>
      destruct (entails_h_sound lo hi E ca T fx R M model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
  - match goal with Hea : entails_h A ?lo ?hi cb ?T = true |- _ =>
      destruct (entails_h_sound lo hi E cb T fx R M model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RenameCS.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.
  Variable gb : nat.
  Hypothesis Hgb : (nx0 <= gb)%nat.
  Hypothesis Hm : forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m = true.

  Let ER := edenot_rename m fw bw Hfw Hbw.

  Lemma blocks_den_rename : forall E l,
    pvars_all fw bw l = true -> blocks_den (ren_env bw E) (map (prename fw) l) = blocks_den E l.
  Proof.
    intros E l Hv. unfold blocks_den. rewrite map_map. apply map_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. unfold uE. rewrite !(ER E) by assumption. reflexivity.
  Qed.

  Lemma bcost_rename : forall E l,
    pvars_all fw bw l = true -> bcost (ren_env bw E) (map (prename fw) l) = bcost E l.
  Proof.
    intros E l Hv. induction l as [|[b n] r IH]; [reflexivity|].
    unfold pvars_all in Hv. cbn [forallb fst snd] in Hv. apply andb_prop in Hv as [H12 Hr]. apply andb_prop in H12 as [H1 H2].
    cbn [map bcost prename fst snd]. unfold uE at 1 2. rewrite (ER E) by assumption. rewrite (IH Hr). reflexivity.
  Qed.

  Lemma wins_den_rename : forall E l,
    pvars_all fw bw l = true -> wins_den (ren_env bw E) (map (prename fw) l) = wins_den E l.
  Proof.
    intros E l Hv. unfold wins_den. rewrite map_map. apply map_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. unfold uE. rewrite !(ER E) by assumption. reflexivity.
  Qed.

  Lemma sptop_den_rename : forall E e,
    evars_all (ren_ok fw bw) e = true -> sptop_den (ren_env bw E) (erename fw e) = sptop_den E e.
  Proof. intros E e Hv. unfold sptop_den, uE. rewrite (ER E) by assumption. reflexivity. Qed.

  Lemma floor_sem_rename : forall E ms top bud,
    forallb (fun m => evars_all (ren_ok fw bw) (am_base m) && evars_all (ren_ok fw bw) (am_len m))%bool ms = true ->
    evars_all (ren_ok fw bw) top = true ->
    floor_sem E (acs_floor ms) top bud -> floor_sem (ren_env bw E) (acs_floor (map (mrename fw) ms)) (erename fw top) bud.
  Proof.
    intros E ms top bud Hms Htop H. destruct ms as [|[f l kd] r]; cbn [map mrename acs_floor floor_sem am_base am_len am_kind] in *.
    - rewrite (sptop_den_rename E top Htop). exact H.
    - apply andb_prop in Hms as [Hms _]. apply andb_prop in Hms as [Hf _]. unfold uE in *. rewrite (ER E) by assumption. exact H.
  Qed.

  Lemma cs_ok_rename : forall E cs fx R M model nx,
    csvars_all (ren_ok fw bw) cs = true -> s_log (a_ss cs) = [] ->
    cs_ok E cs fx R M model -> cs_ok (ren_env bw E) (rename_cs fw cs nx) fx R M model.
  Proof.
    intros E cs fx R M model nx Hv Hlog HC.
    unfold csvars_all in Hv.
    apply andb_prop in Hv as [Hv Hfd]. apply andb_prop in Hv as [Hv Hbrk]. apply andb_prop in Hv as [Hv Hgh].
    apply andb_prop in Hv as [Hv Hvis]. apply andb_prop in Hv as [Hv Hmaps]. apply andb_prop in Hv as [Hregs Hkn].
    destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL]; constructor;
      cbn [rename_cs a_ss a_totsz a_eager a_vis a_ghost a_brk a_ylo kn mk_ss s_regs s_log s_know s_pc s_next] in *; try assumption.
    - apply (regs_ok_rename m fw bw Hfw Hbw); assumption.
    - reflexivity.
    - apply (know_ok_rename SEGS m fw bw Hfw Hbw); assumption.
    - rewrite (blocks_den_rename E (a_vis cs) Hvis), (bcost_rename E (a_vis cs) Hvis). unfold bcount in *. rewrite length_map. assumption.
    - eapply UINV_agree; [eapply env_agree_le; [apply (ren_agree m bw Hbw gb Hm) | exact Hgb] | assumption].
    - rewrite (wins_den_rename E (a_ghost cs) Hgh). assumption.
    - rewrite (sptop_den_rename E (a_brk cs) Hbrk). assumption.
    - cbn [a_maps]. apply floor_sem_rename; assumption.
  Qed.
End RenameCS.

Lemma rename_sound : forall gb E cs fx R M model m cs',
  (nx0 <= gb)%nat -> cs_ok E cs fx R M model -> node_rename gb cs m = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof.
  intros gb E cs fx R M model m cs' Hgb HC H. unfold node_rename in H.
  destruct (forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m) eqn:Hm; [|discriminate].
  destruct (mk_fwd m) as [fw|] eqn:Hfw; [|discriminate].
  destruct (mk_bwd m) as [bw|] eqn:Hbw; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. apply andb_prop in Hc as [Hv Hlog].
  exists (ren_env bw E). split; [exact (ren_agree m bw Hbw gb Hm E)|]. split; [|reflexivity].
  match goal with |- cs_ok _ (with_ss _ (mk_ss _ _ _ ?NX)) _ _ _ _ =>
    change (cs_ok (ren_env bw E) (rename_cs fw cs NX) fx R M model) end.
  apply (cs_ok_rename m fw bw Hfw Hbw gb Hgb Hm); [exact Hv | exact (co_log HC) | exact HC].
Qed.

Lemma compact_sound : forall gb E cs fx R M model cs',
  (nx0 <= gb)%nat -> cs_ok E cs fx R M model -> node_compact gb cs = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' fx R M model /\ pc cs' = pc cs.
Proof. intros gb E cs fx R M model cs' Hgb HC H. unfold node_compact in H. eapply rename_sound; eassumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation CHECK := (AP.check SEGS IT A nx0 LIMIT XN XE XB XC HS KC).

Lemma sd_agree : forall D E E' fs s,
  env_agree nx0 E E' -> shape_vars_lt nx0 s = true -> sd D E fs s = sd D E' fs s.
Proof.
  intros D E E' fs s Hag. induction s; cbn [sd shape_vars_lt]; intros Hv; try reflexivity.
  - (* [comment removed for export] *) rewrite IHs by exact Hv. unfold Wp.
    replace (flat_map (piece_den E') ps) with (flat_map (piece_den E) ps); [reflexivity|].
    apply flat_map_ext. intros p. destruct p; cbn [piece_den]; [reflexivity|]. destruct Hag as [_ Heb]. rewrite Heb. reflexivity.
  - apply andb_prop in Hv as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in Hv as [Hv H3]. apply andb_prop in Hv as [H1 H2].
    rewrite (edenot_agree' nx0 E E' e Hag H1), IHs1, IHs2 by assumption. reflexivity.
  - apply HOLES_agree. exact Hag.
Qed.

Lemma sd_has_nil : forall D E fs s, D [] -> sd D E fs s [].
Proof.
  intros D E fs s HD. induction s; cbn [sd].
  - reflexivity.
  - apply t_exit_has_nil.
  - left. apply is_prefix_nil.
  - left. exact IHs1.
  - destruct (bv_unsigned (edenot E e) <=? mid); assumption.
  - apply HOLES_nil.
  - exact HD.
Qed.

Lemma sd_salt2 : forall D E fs a b, D [] ->
  t_eq (t_alt2 (sd D E fs a) (sd D E fs b)) (sd D E fs (salt2 a b)).
Proof.
  intros D E fs a b HD.
  assert (Ha : sd D E fs a []) by (apply sd_has_nil; exact HD).
  assert (Hb : sd D E fs b []) by (apply sd_has_nil; exact HD).
  unfold salt2. destruct a; destruct b; cbn [sd] in *;
    first [ apply t_alt2_nil_l; assumption | apply t_alt2_nil_r; assumption | apply t_eq_refl ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LCOK (lc : option loopctx) (D : TSet) (E : env) (fs : Fs.Fs) : Prop :=
  match lc with
  | None => True
  | Some (LC h nxs lo hi hx) => ((nx0 <= lo)%nat /\ (lo <= hi)%nat /\ (hx = true -> t_eq D (HOLES 0%nat E fs))) /\
              forall nx, In nx nxs -> forall E' fx' R' M' m', env_agree lo E E' -> cs_ok E' nx fx' R' M' m' -> m_fs m' = fs ->
                RZ (cfg fx' R' h M' m') D
  | Some (JC j jss sk b lo jx) => ((nx0 <= b)%nat /\ (b <= lo)%nat /\ (jx = true -> t_eq D (HOLES 0%nat E fs))) /\
              forall js, In js jss -> forall E' fx' R' M' m', env_agree b E E' -> cs_ok E' js fx' R' M' m' -> m_fs m' = fs ->
                RZ (cfg fx' R' (pc js) M' m') (sd D E' fs sk)
  end.

Lemma LCOK_bnd : forall lc D E fs, LCOK lc D E fs -> (nx0 <= match lc with Some c => lc_bnd c | None => nx0 end)%nat.
Proof. intros [[h nx lo hi hx|j js sk b lo jx]|] D E fs HL; cbn [LCOK lc_bnd] in *; [destruct HL as [(H1 & H2 & _) _]; lia | destruct HL as [(H1 & _ & _) _]; lia | lia]. Qed.

Lemma LCOK_raise : forall lc b D E fs, LCOK lc D E fs -> (nx0 <= b)%nat -> LCOK (AP.lc_raise lc b) D E fs.
Proof.
  intros [[h nx lo hi hx|j js sk b0 lo jx]|] b D E fs HL Hb; cbn [LCOK AP.lc_raise] in *.
  - destruct HL as [(H1 & H2 & H3) HL]. split; [split; [exact H1 | split; [lia | exact H3]] | exact HL].
  - exact HL.
  - split; [split; [exact Hb | split; [lia | intros H; discriminate H]]|]. intros nx [].
Qed.


Definition lc_guard (lc : option loopctx) (cs : acs) : bool :=
  match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end.

Lemma LCOK_agree_gb : forall lc D E E' fs,
  LCOK lc D E fs -> env_agree (match lc with Some c => lc_bnd c | None => nx0 end) E E' -> LCOK lc D E' fs.
Proof.
  intros [[h nx lo hi hx|j js sk b lo jx]|] D E E' fs HL Hag; [| |exact I]; cbn [LCOK lc_bnd] in *.
  - destruct HL as [(Hn0 & Hlh & Hx) HL]. split.
    + split; [exact Hn0 | split; [exact Hlh |]].
      intros Hhx. rewrite <- (HOLES_agree 0%nat E E' fs ltac:(eapply env_agree_le; [exact Hag | lia])). exact (Hx Hhx).
    + intros nx1 Hin E2 fx' R' M' m' Hag2; apply (HL nx1 Hin); (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
  - destruct HL as [(Hn0 & Hlh & Hx) HL]; (split; [split; [exact Hn0 | split; [exact Hlh |]]|]).
    + intros Hjx. rewrite <- (HOLES_agree 0%nat E E' fs ltac:(eapply env_agree_le; [exact Hag | lia])). exact (Hx Hjx).
    + intros js1 Hin E2 fx' R' M' m' Hag2; apply (HL js1 Hin); (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
Qed.

Lemma LCOK_agree : forall lc D E E' fs cs,
  LCOK lc D E fs -> lc_guard lc cs = true -> env_agree (nxt cs) E E' -> LCOK lc D E' fs.
Proof.
  intros [c|] D E E' fs cs HL Hg Hag; [|exact I]. eapply LCOK_agree_gb; [exact HL|].
  cbn [lc_guard] in Hg. apply Nat.leb_le in Hg. eapply env_agree_le; [exact Hag | exact Hg].
Qed.

Lemma LCOK_xmode : forall lc D E fs, LCOK lc D E fs -> lc_xmode lc = true -> t_eq D (HOLES 0%nat E fs).
Proof.
  intros [[h0 nx0' lo0 hi0 hx0|j0 js0 sk0 b0 lo0 jx0]|] D E fs HL Hxm; cbn [lc_xmode] in Hxm; try discriminate Hxm;
    cbn [LCOK] in HL; [destruct hx0; [|discriminate Hxm] | destruct jx0; [|discriminate Hxm]];
    destruct HL as [(_ & _ & Hx) _]; exact (Hx eq_refl).
Qed.

Lemma cont_agree : forall bfuel fuel lc k cs cs' s E model D,
  CHECK bfuel fuel lc cs' k = COk s ->
  LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  (forall E fx R M model, cs_ok E cs' fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
     RZ (cfg fx R (pc cs') M model) (sd D E (m_fs model) s)) ->
  forall E' fx' R' M' model',
    env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
    RZ (cfg fx' R' (pc cs') M' model') (sd D E (m_fs model) s).
Proof.
  intros bfuel fuel lc k cs cs' s E model D Hc HL Hg HD IH E' fx' R' M' model' [Hag Hag2] HC' Hfs.
  rewrite (sd_agree D E E' (m_fs model) s Hag (check_vars SEGS IT A nx0 LIMIT HS XN XE XB XC KC _ _ _ _ _ _ Hc)), <- Hfs.
  apply (IH E' fx' R' M' model' HC'); [|exact HD]. rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma sd_holes_only_eq : forall D E fs s, holes_only s = true -> t_eq (sd D E fs s) (HOLES 0%nat E fs).
Proof.
  intros D E fs s. induction s; cbn [holes_only sd]; intros H; try discriminate.
  - apply andb_prop in H as [H1 H2]. destruct (Z.leb _ _); [apply IHs1; exact H1 | apply IHs2; exact H2].
  - rewrite (HOLES_same h). intros tr. tauto.
Qed.
(* [comment removed for export] *)
Lemma shape_eqv_transfer : forall D E fs s1 s2 c,
  AP.shape_eqv s1 s2 = true -> RZ c (sd D E fs s2) -> RZ c (sd D E fs s1).
Proof.
  intros D E fs s1 s2 c H HR. unfold AP.shape_eqv in H. apply orb_prop in H as [H|H].
  - apply shape_eqb_eq in H. subst. exact HR.
  - apply andb_prop in H as [H1 H2]. eapply RZ_conseq; [exact HR|].
    intros tr. pose proof (sd_holes_only_eq D E fs s1 H1 tr). pose proof (sd_holes_only_eq D E fs s2 H2 tr). tauto.
Qed.


(* [comment removed for export] *)
Lemma sd_next_or_holes_D : forall D E fs s,
  next_or_holes s = true -> t_eq D (HOLES 0%nat E fs) -> t_eq (sd D E fs s) D.
Proof.
  intros D E fs s Hs HD. induction s; cbn [next_or_holes sd] in *; try discriminate.
  - apply andb_prop in Hs as [H1 H2]. destruct (Z.leb _ _); [apply IHs1; exact H1 | apply IHs2; exact H2].
  - rewrite (HOLES_same h). intros tr. pose proof (HD tr). tauto.
  - intros tr. tauto.
Qed.

(* [comment removed for export] *)
Lemma check_next_sound : forall lc cs p w s E fx R M model D,
  AP.check_next A lc cs p w = COk s ->
  cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros lc cs p w s E fx R M model D Hc HC HL. unfold AP.check_next in Hc.
  destruct lc as [[h nxs lo hi hx|j' js' sk' b' lo' jx']|]; [|discriminate|discriminate].
  destruct (Z.eqb (pc cs) h && existsbL (fun nx => entails_tw A lo hi w cs nx) nxs)%bool eqn:Ht; [|discriminate]. injection Hc as <-. cbn [sd].
  apply andb_prop in Ht as [Hpc Hex]. apply Z.eqb_eq in Hpc. rewrite existsbL_eq in Hex. apply existsb_exists in Hex as [nx [Hin Hent]].
  cbn [LCOK] in HL. destruct HL as [(Hn0 & Hlh & _) HL].
  destruct (entails_tw_sound lo hi w E cs nx fx R M model HC Hent Hn0) as (E' & Hag & HC' & Hpc').
  rewrite Hpc. exact (HL nx Hin E' fx R M model Hag HC' eq_refl).
Qed.
Lemma check_merge_sound : forall lc cs p j w s E fx R M model D,
  AP.check_merge A nx0 lc cs p j w = COk s ->
  cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros lc cs p j w s E fx R M model D Hc HC HL. unfold AP.check_merge in Hc.
  destruct lc as [[h nx lo hi hx|j' jss sk' b' lo' jx']|]; [discriminate| |discriminate].
  destruct (Nat.eqb j j' && shape_vars_lt nx0 sk' && existsbL (fun js => Z.eqb (pc cs) (pc js) && entails_tw A lo' (nxt js) w cs js) jss)%bool eqn:Ht; [|discriminate].
  injection Hc as <-.
  apply andb_prop in Ht as [Ht Hex]. apply andb_prop in Ht as [_ Hsv]. rewrite existsbL_eq in Hex. apply existsb_exists in Hex as [js [Hin Hje]].
  apply andb_prop in Hje as [Hpc Hent]. apply Z.eqb_eq in Hpc.
  cbn [LCOK] in HL. destruct HL as [(Hn0 & Hbl & _) HJ].
  destruct (entails_tw_sound lo' (nxt js) w E cs js fx R M model HC Hent ltac:(clear -Hn0 Hbl; lia)) as (E' & Hag & HC' & Hpc').
  assert (Hn0l : (nx0 <= lo')%nat) by lia.
  rewrite (sd_agree D E E' (m_fs model) sk' (env_agree_le nx0 lo' E E' Hag Hn0l) Hsv). rewrite Hpc.
  exact (HJ js Hin E' fx R M model (env_agree_le _ _ _ _ Hag Hbl) HC' eq_refl).
Qed.

(* [comment removed for export] *)
Lemma listZ_eqb_refl : forall l, APC.listZ_eqb l l = true.
Proof. induction l; cbn; [reflexivity|]. rewrite Z.eqb_refl, IHl. reflexivity. Qed.
Lemma spieces_eqb_refl : forall l, APC.spieces_eqb l l = true.
Proof.
  induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH.
  destruct a; cbn; [rewrite listZ_eqb_refl | rewrite Nat.eqb_refl]; reflexivity.
Qed.
Lemma shape_eqb_refl : forall s, shape_eqb s s = true.
Proof.
  induction s; cbn [shape_eqb]; try reflexivity.
  - apply Z.eqb_refl.
  - rewrite Z.eqb_refl, spieces_eqb_refl, IHs. reflexivity.
  - rewrite IHs1, IHs2. reflexivity.
  - rewrite APS.expr_eqb_refl', Z.eqb_refl, IHs1, IHs2. reflexivity.
  - apply Nat.eqb_refl.
Qed.
Lemma shape_eqv_refl : forall s, AP.shape_eqv s s = true.
Proof. intros s. unfold AP.shape_eqv. rewrite shape_eqb_refl. reflexivity. Qed.
Lemma shape_eqv_trans : forall a b c, AP.shape_eqv a b = true -> AP.shape_eqv b c = true -> AP.shape_eqv a c = true.
Proof.
  intros a b c H1 H2. unfold AP.shape_eqv in *.
  apply orb_prop in H1 as [H1|H1]; [apply shape_eqb_eq in H1; subst; exact H2|].
  apply andb_prop in H1 as [Ha Hb].
  apply orb_prop in H2 as [H2|H2]; [apply shape_eqb_eq in H2; subst; rewrite Ha, Hb; cbn; apply orb_true_r|].
  apply andb_prop in H2 as [_ Hc]. rewrite Ha, Hc. cbn. apply orb_true_r.
Qed.
Lemma check_each_ok : forall chk p cs0 css s,
  AP.check_each chk p cs0 css = COk s ->
  forall cs k, In (cs, k) css -> exists s', chk cs k = COk s' /\ AP.shape_eqv s s' = true.
Proof.
  intros chk p cs0 css. induction css as [|[c ck] rest IH]; intros s Hc cs k Hin; [discriminate|].
  cbn [AP.check_each] in Hc. destruct rest as [|c2 rest2].
  - destruct Hin as [He|[]]. injection He as <- <-. exists s. split; [exact Hc | apply shape_eqv_refl].
  - destruct (chk c ck) as [s1|] eqn:H1; [|discriminate].
    destruct (AP.check_each chk p cs0 (c2 :: rest2)) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:He; [|discriminate]. injection Hc as <-.
    destruct Hin as [Hx|Hin].
    + injection Hx as <- <-. exists s1. split; [exact H1 | apply shape_eqv_refl].
    + destruct (IH s2 eq_refl cs k Hin) as (s' & Hs' & Hev). exists s'. split; [exact Hs'|].
      eapply shape_eqv_trans; [exact He | exact Hev].
Qed.
Lemma check_bodies_ok : forall chk p cs0 css,
  AP.check_bodies chk p cs0 css = COk SNext -> forall cs b, In (cs, b) css -> chk cs b = COk SNext.
Proof.
  intros chk p cs0 css. induction css as [|[c cb] rest IH]; intros Hc cs b Hin; [destruct Hin|].
  cbn [AP.check_bodies] in Hc. destruct (chk c cb) as [sb|] eqn:H1; [|discriminate].
  destruct sb; try discriminate. destruct Hin as [Hx|Hin]; [injection Hx as <- <-; exact H1 | exact (IH Hc cs b Hin)].
Qed.
Lemma check_bodies_next : forall chk p cs0 css sb, AP.check_bodies chk p cs0 css = COk sb -> sb = SNext.
Proof.
  intros chk p cs0 css. induction css as [|[c cb] rest IH]; intros sb Hc; cbn [AP.check_bodies] in Hc.
  - injection Hc as <-. reflexivity.
  - destruct (chk c cb) as [s1|]; [|discriminate]. destruct s1; try discriminate. exact (IH sb Hc).
Qed.
Lemma loop_okM_facts : forall cs J N alts nhi,
  AP.loop_okM nx0 cs J N alts = Some nhi ->
  forall a, In a alts -> loop_ok nx0 cs J N (AP.la_inv a) = Some nhi /\ pc (AP.la_inv a) = pc cs
                        /\ nxt (AP.la_inv a) = nxt (AP.la_inv (hd a alts)).
Proof.
  intros cs J N alts nhi H a Hin. unfold AP.loop_okM in H. destruct alts as [|a0 rest]; [discriminate|].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hf; [|discriminate] end.
  pose proof (proj1 (forallb_forall _ _) Hf a Hin) as Hi. cbn beta in Hi.
  apply andb_prop in Hi as [Hi Hlk]. apply andb_prop in Hi as [Hpc Hnx]. apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hnx.
  cbn [hd]. split; [|split; [exact Hpc | exact Hnx]].
  destruct (loop_ok nx0 cs J N (AP.la_inv a)) as [n1|] eqn:Hl; [|discriminate].
  (* [comment removed for export] *)
  unfold loop_ok in H, Hl.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  match type of Hl with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  rewrite Hl in H. exact H.
Qed.
(* [comment removed for export] *)
Lemma gplan_ok_lalts : forall alts a, gplan_ok (PLoopM 0 (ELit 0) alts []) = true -> In a alts ->
  gplan_ok (AP.la_body a) = true /\ gplan_ok (AP.la_k a) = true.
Proof.
  intros alts. induction alts as [|[[i b] k] r IH]; intros a H Hin; [destruct Hin|].
  cbn [gplan_ok] in H. fold gplan_ok in H.
  apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hb Hk].
  destruct Hin as [<-|Hin]; [split; [exact Hb | exact Hk]|]. apply IH; [|exact Hin]. cbn [gplan_ok]. fold gplan_ok. exact Hr.
Qed.
Lemma gplan_ok_valts : forall alts ka a, gplan_ok (PViaM 0 alts 0 ka) = true -> In a alts -> gplan_ok (snd a) = true.
Proof.
  intros alts ka. induction alts as [|[j k] r IH]; intros a H Hin; [destruct Hin|].
  cbn [gplan_ok] in H. fold gplan_ok in H.
  apply andb_prop in H as [Hka H]. apply andb_prop in H as [Hk Hr].
  destruct Hin as [<-|Hin]; [exact Hk|]. apply IH; [|exact Hin]. cbn [gplan_ok]. fold gplan_ok. rewrite Hka, Hr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma start_ok_sound : forall E cs N e0 fx R M model,
  cs_ok E cs fx R M model -> AP.start_ok cs N e0 = true ->
  bv_unsigned (edenot E e0) <= bv_unsigned (edenot E N) /\
  (forall E', env_agree (nxt cs) E E' -> edenot E e0 = edenot E' e0).
Proof.
  intros E cs N e0 fx R M model HC H.
  assert (GEN : (AP.expr_vars_lt (nxt cs) e0 && lin_ge0 (kn cs) [(N, 0%Z)] [(e0, 0%Z)])%bool = true ->
            bv_unsigned (edenot E e0) <= bv_unsigned (edenot E N) /\
            (forall E', env_agree (nxt cs) E E' -> edenot E e0 = edenot E' e0)).
  { intros G. apply andb_prop in G as [Gv Gl]. split.
    - pose proof (lin_ge0_sound SEGS E M (kn cs) [(N, 0%Z)] [(e0, 0%Z)] (co_know HC) Gl) as Hle. cbn [xt_den] in Hle. lia.
    - intros E' Hag. exact (edenot_agree' (nxt cs) E E' e0 Hag Gv). }
  unfold AP.start_ok in H. destruct e0 as [z| | | | | | |]; try (exact (GEN H)).
  destruct z as [|p|p]; try (exact (GEN H)).
  split; [| intros E' _; reflexivity]. cbn [edenot]. rewrite u_small by lia. pose proof (u64_range (edenot E N)). lia.
Qed.

(* [comment removed for export] *)
Lemma check_loop_sound : forall fuel bfuel,
  (forall lc p cs s, gplan_ok p = true -> CHECK bfuel fuel lc cs p = COk s ->
     forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
     RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s)) ->
  forall lc cs p lJ lN alts lw s,
  (forall a, In a alts -> gplan_ok (AP.la_body a) = true /\ gplan_ok (AP.la_k a) = true) ->
  AP.check_loop A nx0 (CHECK bfuel fuel) lc cs p lJ lN alts lw = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros fuel bfuel IH lc cs p lJ lN alts lw s Hgalts Hc E fx R M model D HC HL Hg HD.
  unfold AP.check_loop in Hc.
  destruct (AP.loop_okM nx0 cs lJ lN alts) as [nhi|] eqn:HloM; [|discriminate].
  destruct alts as [|a0 rest] eqn:Halts; [discriminate|]. rewrite <- Halts in *.
  assert (Hin0 : In a0 alts) by (rewrite Halts; left; reflexivity).
  set (inv0 := AP.la_inv a0) in *.
  cbv zeta in Hc.
  set (e0 := AP.loop_start lw lJ) in Hc.
  destruct (AP.start_ok cs lN e0 && existsbL (fun a => entails_tw A (Datatypes.S lJ) (nxt inv0) lw cs (inst (AP.la_inv a) lJ e0)) alts)%bool eqn:Hex; [|discriminate].
  apply andb_prop in Hex as [Hst Hex]. rewrite existsbL_eq in Hex.
  destruct (AP.check_each (fun js k => CHECK bfuel fuel (AP.lc_raise lc (nxt js)) js k) p cs (map (fun a => (inst (AP.la_inv a) lJ lN, AP.la_k a)) alts)) as [sk|] eqn:Hk; [|discriminate].
  cbv zeta in Hc.
  match type of Hc with context [AP.check_bodies ?f ?pp ?c0 ?l] =>
    destruct (AP.check_bodies f pp c0 l) as [sb|] eqn:Hbody; [|discriminate] end.
  pose proof (check_bodies_next _ _ _ _ _ Hbody) as ->.
  enough (MAIN : RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) sk)).
  { destruct (lc_xmode lc && next_or_holes sk)%bool eqn:Hxn; injection Hc as <-; [|exact MAIN].
    apply andb_prop in Hxn as [Hxm Hnoh]. cbn [sd].
    pose proof (sd_next_or_holes_D D E (m_fs model) sk Hnoh (LCOK_xmode lc D E (m_fs model) HL Hxm)) as Heq.
    eapply RZ_conseq; [exact MAIN|]. intros tr. pose proof (Heq tr). tauto. }
  clear Hc s. rename sk into s.
  (* [comment removed for export] *)
  assert (FACTS : forall a, In a alts -> loop_ok nx0 cs lJ lN (AP.la_inv a) = Some nhi /\ pc (AP.la_inv a) = pc cs /\ nxt (AP.la_inv a) = nxt inv0).
  { intros a Hin. destruct (loop_okM_facts cs lJ lN alts nhi HloM a Hin) as (H1 & H2 & H3). rewrite Halts in H3. cbn [hd] in H3.
    split; [exact H1 | split; [exact H2 | exact H3]]. }
  destruct (FACTS a0 Hin0) as (Hlo0 & Hpc0 & _).
  destruct (loop_ok_facts nx0 cs lJ lN inv0 nhi Hlo0) as (Ffr & FJ & FJh & Flog & Flen & FvN & FxN & Fnhi).
  destruct (fresh_ok_parts nx0 cs Ffr) as (_ & _ & _ & _ & _ & _ & Fle).
  pose proof (xhi_sound SEGS E _ (kn cs) lN nhi (co_know HC) FxN) as HNv.
  set (Nv := bv_unsigned (edenot E lN)) in *. pose proof (u64_range (edenot E lN)) as RN. fold Nv in RN.
  set (D0 := sd D E (m_fs model) s).
  assert (HD0 : D0 []) by (apply sd_has_nil; exact HD).
  set (h := pc cs) in *.
  pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
  assert (Hg' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
  { destruct lc as [c|]; cbn [lc_guard] in Hg; [apply Nat.leb_le in Hg; exact Hg | lia]. }
  assert (Q : forall m j a E' fx' R' M' m', In a alts -> j = Nv - Z.of_nat m -> 0 <= j -> env_agree (nxt cs) E E' ->
             cs_ok E' (inst (AP.la_inv a) lJ (ELit j)) fx' R' M' m' -> m_fs m' = m_fs model ->
             RZ (cfg fx' R' h M' m') D0).
  { induction m as [|m IHm]; intros j a E' fx' R' M' m' Hin Hj Hj0 Hag HCj Hfs; set (inv := AP.la_inv a) in *.
    - (* [comment removed for export] *)
      destruct (FACTS a Hin) as (Hloi & Hpci & Hnxi).
      destruct (loop_ok_facts nx0 cs lJ lN inv nhi Hloi) as (_ & _ & _ & Flogi & _ & _ & _ & _).
      assert (HNe : edenot E' lN = edenot E' (ELit j)).
      { cbn [edenot]. rewrite <- (edenot_agree' (nxt cs) E E' lN Hag FvN). apply bv_eq. rewrite u_small by lia. cbn in Hj. lia. }
      assert (HCN : cs_ok E' (inst inv lJ lN) fx' R' M' m').
      { apply (proj2 (cs_ok_inst E' lJ lN inv fx' R' M' m' ltac:(lia) Flogi)). rewrite HNe.
        apply (proj1 (cs_ok_inst E' lJ (ELit j) inv fx' R' M' m' ltac:(lia) Flogi)). exact HCj. }
      destruct (check_each_ok _ _ _ _ _ Hk (inst inv lJ lN) (AP.la_k a) (in_map (fun a' => (inst (AP.la_inv a') lJ lN, AP.la_k a')) _ _ Hin)) as (s' & Hk' & Hev).
      unfold D0. apply (shape_eqv_transfer D E (m_fs model) s s' _ Hev).
      rewrite (sd_agree D E E' (m_fs model) s' ltac:(eapply env_agree_le; [exact Hag | exact Fle]) (check_vars SEGS IT A nx0 LIMIT HS XN XE XB XC KC _ _ _ _ _ _ Hk')).
      rewrite <- Hfs. replace h with (pc (inst inv lJ lN)) by (unfold h; rewrite pc_inst; exact Hpci).
      apply (IH (AP.lc_raise lc (nxt (inst inv lJ lN))) (AP.la_k a) _ s' (proj2 (Hgalts a Hin)) Hk' E' fx' R' M' m' D HCN); [|exact HD].
      rewrite Hfs. apply LCOK_raise; [| rewrite (nxt_inst inv lJ lN); unfold inv; rewrite Hnxi; clear -Fle FJ FJh; lia]. eapply LCOK_agree_gb; [exact HL | eapply env_agree_le; [exact Hag | exact Hg']].
    - (* [comment removed for export] *)
      destruct (FACTS a Hin) as (Hloi & Hpci & Hnxi).
      destruct (loop_ok_facts nx0 cs lJ lN inv nhi Hloi) as (_ & _ & _ & Flogi & Fleni & _ & _ & _).
      set (E'' := upd E' lJ (Z_to_bv 64 j)).
      assert (Hjlt : j < Nv) by lia.
      assert (HCinv : cs_ok E'' inv fx' R' M' m').
      { unfold E''. replace (Z_to_bv 64 j) with (edenot E' (ELit j)) by reflexivity.
        apply (proj1 (cs_ok_inst E' lJ (ELit j) inv fx' R' M' m' ltac:(lia) Flogi)). exact HCj. }
      assert (Hag'' : env_agree (nxt cs) E E'').
      { eapply env_agree_trans; [exact Hag|]. eapply env_agree_le; [apply upd_agree | exact FJ]. }
      assert (HNE'' : edenot E'' lN = edenot E lN) by (symmetry; eapply (edenot_agree' (nxt cs)); [exact Hag'' | exact FvN]).
      assert (HJ'' : ev E'' lJ = Z_to_bv 64 j) by (unfold E''; apply upd_at).
      assert (HCb : cs_ok E'' (loop_body_state lJ lN nhi inv) fx' R' M' m').
      { unfold loop_body_state, add_kn. apply cs_ok_set_kn; [exact HCinv|]. apply Forall_app. split; [|exact (co_know HCinv)].
        constructor; [|constructor; [|constructor]]; cbn [kentry_ok edenot].
        - rewrite HJ'', u_small by lia. lia.
        - unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite HNE'', HJ''. fold Nv. rewrite u_small by lia.
          rewrite Z.mod_small by lia. lia. }
      replace h with (pc (loop_body_state lJ lN nhi inv)) by exact Hpci.
      pose proof (check_bodies_ok _ _ _ _ Hbody (loop_body_state lJ lN nhi inv) (AP.la_body a)
                    (in_map (fun a' => (loop_body_state lJ lN nhi (AP.la_inv a'), AP.la_body a')) _ _ Hin)) as Hb1.
      refine (IH _ (AP.la_body a) _ SNext (proj1 (Hgalts a Hin)) Hb1 E'' fx' R' M' m' D0 HCb _ HD0).
      cbn [LCOK]. split.
      { split; [lia|]. split; [lia|].
        intros Hho. unfold D0. rewrite Hfs.
        rewrite <- (HOLES_agree 0%nat E E'' (m_fs model) ltac:(eapply env_agree_le; [exact Hag'' | exact Fle])).
        apply orb_prop in Hho as [Hho|Hxn].
        - intros tr. exact (sd_holes_only_eq D E (m_fs model) s Hho tr).
        - apply andb_prop in Hxn as [Hxm Hnoh].
          pose proof (LCOK_xmode lc D E (m_fs model) HL Hxm) as HxD.
          eapply t_eq_trans; [exact (sd_next_or_holes_D D E (m_fs model) s Hnoh HxD) | exact HxD]. }
      intros nx Hinx E3 fx3 R3 M3 m3 Hag3 HC3 Hfs3.
      apply in_map_iff in Hinx as (a' & <- & Hin'). set (inv' := AP.la_inv a') in *.
      destruct (FACTS a' Hin') as (Hloi' & _ & _).
      destruct (loop_ok_facts nx0 cs lJ lN inv' nhi Hloi') as (_ & _ & _ & Flogi' & _ & _ & _ & _).
      assert (HJ3 : ev E3 lJ = Z_to_bv 64 j) by (rewrite <- HJ''; symmetry; apply (proj1 Hag3); lia).
      assert (Hnext : edenot E3 (eaddz (EVar lJ) 1) = Z_to_bv 64 (j + 1)).
      { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite HJ3. apply bv_eq. rewrite u_add64, !u_small by lia. rewrite Z.mod_small by lia. reflexivity. }
      set (E4 := upd E3 lJ (Z_to_bv 64 (j + 1))).
      apply (IHm (j + 1) a' E4 fx3 R3 M3 m3); [exact Hin' | lia | lia | | | rewrite Hfs3; exact Hfs].
      + eapply env_agree_trans; [exact Hag''|]. eapply env_agree_trans; [eapply env_agree_le; [exact Hag3 | lia]|].
        eapply env_agree_le; [apply upd_agree | exact FJ].
      + apply (proj2 (cs_ok_inst E4 lJ (ELit (j + 1)) inv' fx3 R3 M3 m3 ltac:(lia) Flogi')).
        unfold E4. cbn [edenot]. rewrite upd_upd. rewrite <- Hnext.
        apply (proj1 (cs_ok_inst E3 lJ (eaddz (EVar lJ) 1) inv' fx3 R3 M3 m3 ltac:(lia) Flogi')). exact HC3. }
  apply existsb_exists in Hex as [a1 [Hin1 Hent]].
  destruct (FACTS a1 Hin1) as (Hlo1 & _ & Hnx1). rewrite <- Hnx1 in Hent.
  destruct (loop_ok_facts nx0 cs lJ lN (AP.la_inv a1) nhi Hlo1) as (_ & _ & _ & Flog1 & _ & _ & _ & _).
  destruct (entails_tw_sound (Datatypes.S lJ) (nxt (AP.la_inv a1)) lw E cs (inst (AP.la_inv a1) lJ e0) fx R M model HC Hent ltac:(lia)) as (E1 & Hag1 & HC1 & _).
  (* [comment removed for export] *)
  destruct (start_ok_sound E cs lN e0 fx R M model HC Hst) as [Hle0 Hag0]. fold Nv in Hle0.
  set (j0 := bv_unsigned (edenot E e0)) in *. pose proof (u64_range (edenot E e0)) as Rj0. fold j0 in Rj0.
  assert (He1 : edenot E1 e0 = edenot E1 (ELit j0)).
  { rewrite <- (Hag0 E1 ltac:(eapply env_agree_le; [exact Hag1 | lia])). change (edenot E1 (ELit j0)) with (Z_to_bv 64 j0).
    apply bv_eq. rewrite u_small by lia. reflexivity. }
  assert (HC1' : cs_ok E1 (inst (AP.la_inv a1) lJ (ELit j0)) fx R M model).
  { apply (proj2 (cs_ok_inst E1 lJ (ELit j0) (AP.la_inv a1) fx R M model ltac:(lia) Flog1)). rewrite <- He1.
    apply (proj1 (cs_ok_inst E1 lJ e0 (AP.la_inv a1) fx R M model ltac:(lia) Flog1)). exact HC1. }
  unfold D0 in Q. apply (Q (Z.to_nat (Nv - j0)) j0 a1 E1 fx R M model); [exact Hin1 | lia | lia | eapply env_agree_le; [exact Hag1 | lia] | exact HC1' | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma check_via_sound : forall fuel bfuel,
  (forall lc p cs s, gplan_ok p = true -> CHECK bfuel fuel lc cs p = COk s ->
     forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
     RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s)) ->
  forall lc cs p vj alts vlo vka s,
  gplan_ok vka = true -> (forall a, In a alts -> gplan_ok (snd a) = true) ->
  AP.check_via nx0 (CHECK bfuel fuel) lc cs p vj alts vlo vka = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros fuel bfuel IH lc cs p vj alts vlo vka s Hgpa Hgpk Hc E fx R M model D HC HL Hg HD.
  unfold AP.check_via in Hc.
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hv; [|discriminate] end.
  apply andb_prop in Hv as [Hv Hne].
  destruct (AP.check_each (fun js k => CHECK bfuel fuel (AP.lc_raise lc (nxt js)) js k) p cs alts) as [sk|] eqn:Hk; [|discriminate].
  pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
  (* [comment removed for export] *)
  destruct alts as [|[js0 k0] rest] eqn:Halts; [discriminate|]. rewrite <- Halts in *.
  assert (Hv0 : via_ok nx0 cs js0 vlo = true) by (apply (proj1 (forallb_forall _ _) Hv (js0, k0)); rewrite Halts; left; reflexivity).
  unfold via_ok in Hv0. repeat match type of Hv0 with (_ && _)%bool = true => apply andb_prop in Hv0 as [Hv0 ?X] end.
  repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
  assert (Hgb' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
  { destruct lc as [c|]; [cbn [lc_guard] in Hg; apply Nat.leb_le in Hg; exact Hg | lia]. }
  apply (IH (Some (JC vj (map fst alts) sk (nxt cs) vlo (lc_xmode lc))) vka cs s Hgpa Hc E fx R M model D HC); [|exact HD].
  cbn [LCOK]. split; [split; [lia | split; [lia |]]|].
  { (* [comment removed for export] *)
    intros Hxm. exact (LCOK_xmode lc D E (m_fs model) HL Hxm). }
  intros js Hin E' fx' R' M' m' Hag HC' Hfs. rewrite <- Hfs.
  apply in_map_iff in Hin as ([js' k] & Hjs & Hin). cbn [fst] in Hjs. subst js'.
  destruct (check_each_ok _ _ _ _ _ Hk js k Hin) as (s' & Hk' & Hev).
  apply (shape_eqv_transfer D E' (m_fs m') sk s' _ Hev).
  apply (IH (AP.lc_raise lc (nxt js)) k js s' (Hgpk (js, k) Hin) Hk' E' fx' R' M' m' D HC'); [|exact HD].
  assert (Hvj : via_ok nx0 cs js vlo = true) by (apply (proj1 (forallb_forall _ _) Hv (js, k)); exact Hin).
  unfold via_ok in Hvj. repeat match type of Hvj with (_ && _)%bool = true => apply andb_prop in Hvj as [Hvj ?Y] end.
  repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
  rewrite Hfs. apply LCOK_raise; [|lia]. eapply LCOK_agree_gb; [exact HL|]. eapply env_agree_le; [exact Hag | exact Hgb'].
Qed.

(* [comment removed for export] *)
Lemma check_branch_sound : forall fuel bfuel,
  (forall lc p cs s, gplan_ok p = true -> CHECK bfuel fuel lc cs p = COk s ->
     forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
     RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s)) ->
  forall lc cs p e k1 k2 s,
  gplan_ok k1 = true -> gplan_ok k2 = true ->
  AP.check_branch (CHECK bfuel fuel lc) cs p e k1 k2 = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  intros fuel bfuel IH lc cs p e k1 k2 s Hgk1 Hgk2 Hc E fx R M model D HC HL Hg HD.
  assert (SAME : forall k cs' s', gplan_ok k = true -> CHECK bfuel fuel lc cs' k = COk s' -> cs_ok E cs' fx R M model ->
            nxt cs = nxt cs' -> RZ (cfg fx R (pc cs') M model) (sd D E (m_fs model) s')).
  { intros k cs' s' Hgk Hk HC' Hn. apply (IH lc k cs' s' Hgk Hk E fx R M model D HC'); [|exact HD].
    eapply LCOK_agree; [exact HL | | apply env_agree_refl]. unfold lc_guard in *. rewrite <- Hn. exact Hg. }
  unfold AP.check_branch in Hc.
  destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
  destruct (Z.leb lo 0 && Z.ltb 0 hi)%bool.
  2: { cbn [negb] in Hc. destruct (Z.leb hi 0); [exact (SAME k1 _ s Hgk1 Hc HC eq_refl) | exact (SAME k2 _ s Hgk2 Hc HC eq_refl)]. }
  cbn [negb] in Hc.
  pose proof (APS.brange_sound SEGS E _ (kn cs) e lo hi (co_know HC) Hr) as Hb.
  assert (HCl : bv_unsigned (edenot E e) <= 0 -> cs_ok E (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)) fx R M model).
  { intros Hm. apply cs_ok_set_kn; [exact HC|]. constructor; [cbn [kentry_ok]; lia|]. apply Forall_app. split; [|exact (co_know HC)].
    apply (probe_lin_facts_sound E M (kn cs) e false (co_know HC)). exact Hm. }
  assert (HCr : 0 < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)) fx R M model).
  { intros Hm. apply cs_ok_set_kn; [exact HC|]. constructor; [cbn [kentry_ok]; lia|]. apply Forall_app. split; [|exact (co_know HC)].
    apply (probe_lin_facts_sound E M (kn cs) e true (co_know HC)). lia. }
  destruct (kn_contra (kn (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)))) eqn:Hk1.
  { destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCl Hle)) Hk1).
    - exact (SAME k2 _ s Hgk2 Hc (HCr ltac:(lia)) eq_refl). }
  destruct (kn_contra (kn (set_kn cs (KRange e (0 + 1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)))) eqn:Hk2.
  { destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exact (SAME k1 _ s Hgk1 Hc (HCl Hle) eq_refl).
    - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCr ltac:(lia))) Hk2). }
  destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo 0 :: probe_lin_facts (kn cs) e false ++ kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
  destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (0+1) hi :: probe_lin_facts (kn cs) e true ++ kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
  destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
  destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
  + exact (SAME k1 _ s1 Hgk1 H1 (HCl Hle) eq_refl).
  + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME k2 _ s2 Hgk2 H2 (HCr ltac:(lia)) eq_refl).
Qed.

Theorem check_sound : forall fuel bfuel lc p cs s,
  gplan_ok p = true ->
  CHECK bfuel fuel lc cs p = COk s ->
  forall E fx R M model D, cs_ok E cs fx R M model -> LCOK lc D E (m_fs model) -> D [] ->
  RZ (cfg fx R (pc cs) M model) (sd D E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel lc p cs s Hgp Hc E fx R M model D HC HL HD; [discriminate|].
  cbn [AP.check] in Hc. rewrite ?fact_okM_fe, ?factle_okM_fe in Hc.
  match type of Hc with (if negb ?g then _ else _) = _ => destruct g eqn:Hg; [|discriminate] end. cbn [negb] in Hc.
  assert (CONT : forall k cs' s', gplan_ok k = true -> CHECK bfuel fuel lc cs' k = COk s' ->
            forall E' fx' R' M' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' ->
            m_fs model' = m_fs model -> RZ (cfg fx' R' (pc cs') M' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hgk Hk. eapply cont_agree; [exact Hk | exact HL | exact Hg | exact HD | intros; eapply IH; eassumption]. }
  assert (SAME : forall k cs' s', gplan_ok k = true -> CHECK bfuel fuel lc cs' k = COk s' -> cs_ok E cs' fx R M model ->
            RZ (cfg fx R (pc cs') M model) (sd D E (m_fs model) s')).
  { intros k cs' s' Hgk Hk HC'. refine (CONT k cs' s' Hgk Hk E fx R M model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl). }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lw lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc|nw|mwj mww|bkf bkt|crr crmid crk1 crk2|fve fvv fvlo fvhi fvk|hwh hww|fle flb flhi flk|fse fsc fshi fsk|flr flo flb2 flh2 flk2|frr fro frlo frhi frk|fxr fxph fxe fxb fxhi fxk|gxr gxph gxe gxlo gxhi gxk|cth|mJ mN malts mw|wj walts wlo wka|bpz bpnz|aid aargs ak1 ak2];
    cbn [gplan_ok] in Hgp; try discriminate Hgp;
    repeat match type of Hgp with (_ && _)%bool = true => apply andb_prop in Hgp as [Hgp ?X] end.
  - (* [comment removed for export] *)
    destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
    intros E' fx' R' M' model' Hag HC1 Hfs. exact (CONT k cs1 s Hgp Hc E' fx' R' M' model' Hag HC1 Hfs).
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { pose proof (APS.brange_sound SEGS E _ (kn cs) e lo hi (co_know HC) Hr) as Hb.
         destruct (Z.leb_spec hi mid) as [Hle|Hgt]; [exact (SAME k1 _ s Hgp Hc HC) | exact (SAME k2 _ s Hgp2 Hc HC)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    destruct (split_sound cs e mid lo hi E fx R M model HC Hr) as [HCl HCr].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
    + exact (SAME k1 _ s1 Hgp H1 (HCl Hle)).
    + exact (SAME k2 _ s2 Hgp2 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (brange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (SAME ck1 _ s Hgp Hc HC) | exact (SAME ck2 _ s Hgp2 Hc HC)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (split_sound cs ce cmid lo hi E fx R M model HC Hr) as [HCl HCr].
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))) eqn:Hk1.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCl Hle)) Hk1).
      - exact (SAME ck2 _ s Hgp2 Hc (HCr ltac:(lia))). }
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) eqn:Hk2.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exact (SAME ck1 _ s Hgp Hc (HCl Hle)).
      - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCr ltac:(lia))) Hk2). }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
    destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
    + exact (SAME ck1 _ s1 Hgp H1 (HCl Hle)).
    + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME ck2 _ s2 Hgp2 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (node_casedisj cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
    destruct (casedisj_sound cs db1 db2 csa csb E fx R M model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc.
    + exact (SAME dk1 _ s1 Hgp H1 HC').
    + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME dk2 _ s2 Hgp2 H2 HC').
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (kn_contra_sound SEGS E _ (kn cs) (co_know HC) Hk).
  - (* [comment removed for export] *)
    destruct (fact_ok (kn cs) K) eqn:Hf; [|discriminate].
    exact (SAME k _ s Hgp Hc (fact_sound E cs fx R M model K HC Hf)).
  - (* [comment removed for export] *)
    destruct (node_join SEGS cs jb joff jn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (join_sound jb joff jn cs cs1 E fx R M model HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hgp Hc HC1).
  - (* [comment removed for export] *)
    exact (SAME k _ s Hgp Hc (forget_sound E cs fx R M model ixs HC)).
  - (* [comment removed for export] *)
    assert (Hpc : pc (node_droprange cs db dn) = pc cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
    rewrite <- Hpc. exact (SAME k _ s Hgp Hc (droprange_sound E cs fx R M model db dn HC)).
  - (* [comment removed for export] *)
    rewrite <- (pc_set_kn cs (kn_keep (kn cs) gws)).
    exact (SAME k _ s Hgp Hc (gckeep_sound E cs fx R M model gws HC)).
  - (* [comment removed for export] *)
    destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate].
    destruct (bump_sound E cs fx R M model bm cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hgp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havoc_sound E cs fx R M model hrs cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbig_sound E cs fx R M model hbK cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fresh_sound r logc fb cs cs1 E fx R M model HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_ext_sound xid xargs cs cs1 E fx R M model); [apply sd_has_nil; exact HD | exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hgp Hc).
  - (* [comment removed for export] *)
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_emit_sound eid eargs cs fd ps cs1 E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD |]. exact (CONT k cs1 s1 Hgp H1).
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (XB bid bargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    (* [comment removed for export] *)
    destruct (kn_contra (kn csa)) eqn:Hka.
    { eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD | | exact (CONT kb2 csb s Hgp2 Hc)].
      intros E' fx' R' M' model' Hag HC' Hfs. exfalso. exact (kn_contra_sound SEGS E' _ _ (co_know HC') Hka). }
    destruct (kn_contra (kn csb)) eqn:Hkb.
    { eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD | exact (CONT kb1 csa s Hgp Hc) |].
      intros E' fx' R' M' model' Hag HC' Hfs. exfalso. exact (kn_contra_sound SEGS E' _ _ (co_know HC') Hkb). }
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv sa sb) eqn:Hse; [|discriminate]. injection Hc as <-.
    eapply (node_ext2_sound bid bargs cs csa csb E fx R M model); [exact HC | exact Hn | apply sd_has_nil; exact HD
      | exact (CONT kb1 csa sa Hgp H1) |].
    intros E' fx' R' M' model' Hag HC' Hfs. eapply shape_eqv_transfer; [exact Hse|]. exact (CONT kb2 csb sb Hgp2 H2 E' fx' R' M' model' Hag HC' Hfs).
  - (* [comment removed for export] *)
    rename X into Hgpk. rename Hgp into Hgpb.
    eapply (check_loop_sound fuel bfuel (IH bfuel)); [ | exact Hc | exact HC | exact HL | exact Hg | exact HD].
    intros a [<-|[]]. split; [exact Hgpb | exact Hgpk].
  - (* [comment removed for export] *)
    eapply check_next_sound; [exact Hc | exact HC | exact HL].
  - (* [comment removed for export] *)
    unfold AP.check_handoff in Hc.
    destruct (HS h) as [ch|] eqn:Hh; [|discriminate].
    destruct (entails cs ch ||| entails_tw A nx0 (nxt ch) [] cs ch)%bool eqn:He; [|discriminate].
    assert (HR : RZ (cfg fx R (pc cs) M model) (HOLES h E (m_fs model))).
    { apply orb_prop in He as [He|He].
      - destruct (entails_sound E cs ch fx R M model HC He) as [HC' Hpc].
        pose proof (HS_sound h ch Hh E fx R M model HC') as HR. rewrite Hpc in HR. exact HR.
      - destruct (entails_tw_sound nx0 (nxt ch) [] E cs ch fx R M model HC He ltac:(lia)) as (E' & Hag & HC' & Hpc).
        pose proof (HS_sound h ch Hh E' fx R M model HC') as HR. rewrite Hpc in HR.
        rewrite (HOLES_agree h E E' (m_fs model) Hag). exact HR. }
    destruct (lc_xmode lc) eqn:Hxm; injection Hc as <-; cbn [sd]; [|exact HR].
    pose proof (LCOK_xmode lc D E (m_fs model) HL Hxm) as Hx.
    eapply RZ_conseq; [exact HR|]. rewrite (HOLES_same h). intros tr. pose proof (Hx tr). tauto.
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_exit cs) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply node_exit_sound; eassumption.
  - (* [comment removed for export] *)
    destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (intro_sound E cs fx R M model ilo ihi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT ik cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
    destruct (brange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (Z.ltb hi 1 ||| Z.ltb 0 lo)%bool eqn:Hdec.
    { destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate].
      eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
      intros E' fx' R' M' model' Hag HC1 Hfs. exact (CONT dk cs1 s Hgp Hc E' fx' R' M' model' Hag HC1 Hfs). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|] eqn:Hra; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (split_sound cs e 0 lo hi E fx R M model HC Hr) as [HCl HCr].
    destruct (diamond_join_sound (nxt cs) djp drs ca cb csj Hj) as [Ja Jb].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    + rewrite <- (pc_set_kn cs (KRange e lo 0 :: kn cs)).
      eapply run_block_gc_sound; [exact Hgb | exact Hra | exact (HCl Hle) |].
      intros E' fx' R' M' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Ja E' fx' R' M' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hgp Hc E'' fx' R' M' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
    + rewrite <- (pc_set_kn cs (KRange e 1 hi :: kn cs)).
      eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact (HCr ltac:(lia)) |].
      intros E' fx' R' M' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Jb E' fx' R' M' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hgp Hc E'' fx' R' M' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
  - (* [comment removed for export] *)
    destruct (node_rename _ cs rnm) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (rename_sound _ E cs fx R M model rnm cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars SEGS IT A nx0 LIMIT HS XN XE XB XC KC _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hgp | exact Hc | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    destruct (node_compact _ cs) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (compact_sound _ E cs fx R M model cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars SEGS IT A nx0 LIMIT HS XN XE XB XC KC _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hgp | exact Hc | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    rename X into Hgpk. rename Hgp into Hgpa.
    eapply (check_via_sound fuel bfuel (IH bfuel)); [exact Hgpa | | exact Hc | exact HC | exact HL | exact Hg | exact HD].
    intros a [<-|[]]. exact Hgpk.
  - (* [comment removed for export] *)
    eapply check_merge_sound; [exact Hc | exact HC | exact HL].
  - (* [comment removed for export] *)
    destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate].
    destruct (abstractcell_sound E cs fx R M model ab an cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME ak _ s Hgp Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocwords_sound E cs fx R M model hws cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT hwk cs1 s Hgp Hc E' fx R M model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate].
    destruct (respell_sound E cs fx R M model rsr rse cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME rsk _ s Hgp Hc HC1).
  - (* [comment removed for export] *)
    eapply check_next_sound; [exact Hc | exact HC | exact HL].
  - (* [comment removed for export] *)
    eapply check_merge_sound; [exact Hc | exact HC | exact HL].
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (branch_probe2 IT cs) as [[e pos]|] eqn:Hbp; [|discriminate]. cbv zeta in Hc.
    eapply (check_branch_sound fuel bfuel (IH bfuel)); [ | | exact Hc | exact HC | exact HL | exact Hg | exact HD];
      destruct pos; assumption.
  - (* [comment removed for export] *)
    rename X into Hgp2. cbv zeta in Hc.
    set (ce := reg cs crr) in Hc.
    destruct (brange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo crmid && Z.ltb crmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi crmid); [exact (SAME crk1 _ s Hgp Hc HC) | exact (SAME crk2 _ s Hgp2 Hc HC)]. }
    cbn [negb] in Hc.
    destruct (split_sound cs ce crmid lo hi E fx R M model HC Hr) as [HCl HCr].
    destruct (kn_contra (kn (set_kn cs (KRange ce lo crmid :: kn cs)))) eqn:Hk1.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) crmid) as [Hle|Hgt].
      - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCl Hle)) Hk1).
      - exact (SAME crk2 _ s Hgp2 Hc (HCr ltac:(lia))). }
    destruct (kn_contra (kn (set_kn cs (KRange ce (crmid + 1) hi :: kn cs)))) eqn:Hk2.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) crmid) as [Hle|Hgt].
      - exact (SAME crk1 _ s Hgp Hc (HCl Hle)).
      - exfalso. exact (kn_contra_sound SEGS E _ _ (co_know (HCr ltac:(lia))) Hk2). }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo crmid :: kn cs)) crk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (crmid+1) hi :: kn cs)) crk2) as [s2|] eqn:H2; [|discriminate].
    destruct (AP.shape_eqv s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-.
    destruct (Z.leb_spec (bv_unsigned (edenot E ce)) crmid) as [Hle|Hgt].
    + exact (SAME crk1 _ s1 Hgp H1 (HCl Hle)).
    + eapply shape_eqv_transfer; [exact Hse|]. exact (SAME crk2 _ s2 Hgp2 H2 (HCr ltac:(lia))).  - (* [comment removed for export] *)
    destruct (factvia_ok (kn cs) fve fvv fvlo fvhi) eqn:Hf; [|discriminate].
    refine (SAME fvk _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factvia_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    unfold AP.check_handoff in Hc.
    destruct (HS hwh) as [ch|] eqn:Hh; [|discriminate].
    destruct (entails cs ch ||| entails_tw A nx0 (nxt ch) hww cs ch)%bool eqn:He; [|discriminate].
    assert (HR : RZ (cfg fx R (pc cs) M model) (HOLES hwh E (m_fs model))).
    { apply orb_prop in He as [He|He].
      - destruct (entails_sound E cs ch fx R M model HC He) as [HC' Hpc].
        pose proof (HS_sound hwh ch Hh E fx R M model HC') as HR. rewrite Hpc in HR. exact HR.
      - destruct (entails_tw_sound nx0 (nxt ch) hww E cs ch fx R M model HC He ltac:(lia)) as (E' & Hag & HC' & Hpc).
        pose proof (HS_sound hwh ch Hh E' fx R M model HC') as HR. rewrite Hpc in HR.
        rewrite (HOLES_agree hwh E E' (m_fs model) Hag). exact HR. }
    destruct (lc_xmode lc) eqn:Hxm; injection Hc as <-; cbn [sd]; [|exact HR].
    pose proof (LCOK_xmode lc D E (m_fs model) HL Hxm) as Hx.
    eapply RZ_conseq; [exact HR|]. rewrite (HOLES_same hwh). intros tr. pose proof (Hx tr). tauto.
  - (* [comment removed for export] *)
    destruct (factle_ok (kn cs) fle flb flhi) eqn:Hf; [|discriminate].
    refine (SAME flk _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factle_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    destruct (factscale_ok (kn cs) fse fsc fshi) eqn:Hf; [|discriminate].
    refine (SAME fsk _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factscale_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (factle_ok (kn cs) (eaddz (reg cs flr) flo) flb2 flh2) eqn:Hf; [|discriminate].
    refine (SAME flk2 _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factle_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (fact_ok (kn cs) (KRange (eaddz (reg cs frr) fro) frlo frhi)) eqn:Hf; [|discriminate].
    refine (SAME frk _ s Hgp Hc _). exact (fact_sound E cs fx R M model _ HC Hf).
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (factle_ok (kn cs) (APC.esubst fxph (reg cs fxr) fxe) (APC.esubst fxph (reg cs fxr) fxb) fxhi) eqn:Hf; [|discriminate].
    refine (SAME fxk _ s Hgp Hc _). unfold add_kn. apply cs_ok_set_kn; [exact HC|].
    constructor; [eapply factle_ok_sound; [exact (co_know HC) | exact Hf] | exact (co_know HC)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. destruct (fact_ok (kn cs) (KRange (APC.esubst gxph (reg cs gxr) gxe) gxlo gxhi)) eqn:Hf; [|discriminate].
    refine (SAME gxk _ s Hgp Hc _). exact (fact_sound E cs fx R M model _ HC Hf).
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (kn_contra_sound SEGS E _ (kn cs) (co_know HC) Hk).
  - (* [comment removed for export] *)
    eapply (check_loop_sound fuel bfuel (IH bfuel)); [ | exact Hc | exact HC | exact HL | exact Hg | exact HD].
    intros a Hin. exact (gplan_ok_lalts malts a Hgp Hin).
  - (* [comment removed for export] *)
    rename X into Hgpv.
    eapply (check_via_sound fuel bfuel (IH bfuel)); [exact Hgp | | exact Hc | exact HC | exact HL | exact Hg | exact HD].
    intros a Hin. eapply (gplan_ok_valts walts wka a); [|exact Hin]. cbn [gplan_ok]. fold gplan_ok. rewrite Hgp, Hgpv. reflexivity.
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (branch_probe2 IT cs) as [[e pos]|] eqn:Hbp; [|discriminate].
    eapply (check_branch_sound fuel bfuel (IH bfuel)); [exact Hgp | exact Hgp2 | exact Hc | exact HC | exact HL | exact Hg | exact HD].
  - (* [comment removed for export] *)
    rename X into Hgp2.
    destruct (XC aid aargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ak1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ak2) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-.
    assert (HALT : RZ (cfg fx R (pc cs) M model) (t_alt2 (sd D E (m_fs model) sa) (sd D E (m_fs model) sb))).
    { eapply (node_alt2x_sound aid aargs cs csa csb E fx R M model);
        [exact HC | exact Hn | apply sd_has_nil; exact HD | apply sd_has_nil; exact HD
        | exact (CONT ak1 csa sa Hgp H1) | exact (CONT ak2 csb sb Hgp2 H2)]. }
    destruct (shape_eqb sa sb) eqn:Hse.
    + apply shape_eqb_eq in Hse. subst sb. eapply RZ_conseq; [exact HALT|]. intros tr. unfold t_alt2. tauto.
    + eapply RZ_conseq; [exact HALT|]. apply sd_salt2. exact HD.
Qed.

End Sound.

Arguments co_regs {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_log {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_know {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_halt {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_lazy {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_fs {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_fds {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_ainv {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_uinv {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_fx {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_perm {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_top {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_mat {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
Arguments co_floor {SEGS RC PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model} _.
End GPS.
