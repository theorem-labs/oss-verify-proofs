(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module SymRun.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


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
  | KWr a _ => saddr_vars_lt b a
  | KDisj a1 _ a2 _ => saddr_vars_lt b a1 && saddr_vars_lt b a2
  end.

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Fixpoint log_vars_lt (b : nat) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r
  end.

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

Lemma mem_denot_agree : forall b E E' base log,
  env_agree b E E' -> log_vars_lt b log = true -> mem_denot E base log = mem_denot E' base log.
Proof.
  intros b E E' base log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt mem_denot]; intros H.
  - reflexivity.
  - apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
    rewrite IH by exact H3. rewrite (adenot_agree b E E' a Ha H1), (edenot_agree b E E' v Ha H2).
    reflexivity.
Qed.

Lemma flat_agree : forall b E E' a n,
  env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
  intros b E E' a n Ha H. unfold flat, estart.
  rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.

Lemma log_flat_agree : forall b E E' log,
  env_agree b E E' -> log_vars_lt b log = true -> log_flat E log -> log_flat E' log.
Proof.
  intros b E E' log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt log_flat]; intros H Hl.
  - exact I.
  - apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
    destruct Hl as (Hw & Hf & Hr). split; [exact Hw|]. split.
    + apply (flat_agree b E E' a _ Ha H1). exact Hf.
    + apply IH; assumption.
Qed.

Lemma know_ok_agree : forall segs b E E' base kn,
  env_agree b E E' -> kn_vars_lt b kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
  intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
  - constructor.
  - apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
    constructor; [| apply IH; assumption].
    destruct Ha as [Hv Hb].
    destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2]; cbn [kentry_vars_lt kentry_ok] in *;
      [ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
              | rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
              | unfold flat, estart in *; rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK); exact Hk1
              | apply andb_prop in HK as [HK1 HK2]; unfold estart in *;
                rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1),
                        <- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK2); exact Hk1 ].
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
Qed.

(* [comment removed for export] *)
Lemma vals_app_agree : forall vals extra ebs,
  env_agree (length vals) (Env (vals_ev vals) ebs) (Env (vals_ev (vals ++ extra)) ebs).
Proof.
  intros vals extra ebs. split; [|reflexivity]. intros n Hn. cbn [ev]. unfold vals_ev.
  rewrite app_nth1 by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma st_ok_entry : forall E base rom pc sr kn nx regs,
  regs_ok E sr regs -> know_ok segs E base kn ->
  st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
  intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
  split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

Theorem run_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  scs_denot segs base E scs ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
                        (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
  eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

(* [comment removed for export] *)
Theorem carry_after : forall E base log kn hints kn' scs hs',
  carry log kn hints = (kn', scs, hs') ->
  log_flat E log -> know_ok segs E base kn -> scs_denot segs base E scs ->
  know_ok segs E (mem_denot E base log) kn'.
Proof. intros. eapply carry_sound; eauto. Qed.

(* [comment removed for export] *)
Lemma reg_val : forall E sr R (r : reg), regs_ok E sr R -> getr R r = edenot E (sr_get sr r).
Proof. intros E sr R r HR. apply HR. Qed.

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
Definition sr_init : list expr :=
  [ELit 0; ELit 0; EVar 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].

Lemma regs_ok_init : forall (sp : word) rest ebs,
  regs_ok (Env (vals_ev (sp :: rest)) ebs) sr_init
          (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp).
Proof.
  intros sp rest ebs r.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - pose proof (ridx_range r) as Hlt.
    rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
    set (n := ridx r) in *. clearbody n.
    do 32 (destruct n as [|n]; [vm_compute in Hr0 |- *; first [discriminate | reflexivity] |]).
    exfalso. lia.
Qed.

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

Lemma stk_ok_grows : forall segs mem mem' sp K,
  stk_ok segs mem sp K -> mem_grows mem mem' -> stk_ok segs mem' sp K.
Proof.
  intros segs mem mem' sp K Hs Hg a n H1 H2. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
Qed.

Lemma stk_ok_mem_denot : forall segs E mem log sp K,
  stk_ok segs mem sp K -> stk_ok segs (mem_denot E mem log) sp K.
Proof. intros. eapply stk_ok_grows; [eassumption | apply mem_denot_grows]. Qed.

(* [comment removed for export] *)
Lemma stk_ok_init : forall segs ph sp argv envp uid hw (rdraw : EntryDraw),
  stk_ok segs (wrap_mem ph sp argv envp uid hw rdraw) sp stack_max_size.
Proof.
  intros segs ph sp argv envp uid hw rdraw a n H1 H2.
  apply store_ok_wrap_window; assumption.
Qed.

Lemma kwr_of_stk_ok : forall segs E mem (e : expr) (sp : word) K,
  edenot E e = sp -> stk_ok segs mem sp K -> (0 <= K <= bv_unsigned sp)%Z ->
  kentry_ok segs E mem (KWr (SA e (- K)) K).
Proof.
  intros segs E mem e sp K He Hs HK. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off]. rewrite He.
  pose proof (u64_range sp). split; [lia|].
  intros d m Hd Hm. apply Hs; rewrite u_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma kword_intro : forall segs E mem (e : expr) (a : word) off w (v : expr) (x : word),
  edenot E e = a -> edenot E v = x -> (1 <= w)%nat -> (w <= 8)%nat ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + Z.of_nat w <= 2 ^ 64)%Z ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned a + off)) w = Some (word_to_le_bytes w x) ->
  kentry_ok segs E mem (KWord (SA e off) w v).
Proof.
  intros segs E mem e a off w v x He Hv Hw1 Hw H1 H2 Hr. cbn [kentry_ok]. unfold flat, estart, adenot, v_addi.
  cbn [a_base a_off]. rewrite He, Hv. split; [exact Hw|]. split; [lia | exact Hr].
Qed.

Lemma krange_intro : forall segs E mem (e : expr) lo hi,
  (lo <= bv_unsigned (edenot E e) <= hi)%Z -> kentry_ok segs E mem (KRange e lo hi).
Proof. intros. cbn [kentry_ok]. lia. Qed.

Lemma kalign_intro : forall segs E mem (e : expr) m,
  (0 < m)%Z -> (bv_unsigned (edenot E e) mod m = 0)%Z -> kentry_ok segs E mem (KAlign e m).
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kimg_intro : forall segs E mem lo hi,
  (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  kentry_ok segs E mem (KImg lo hi).
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kzero_intro : forall segs E mem (e : expr) (a : word) off (n : expr) len,
  edenot E e = a -> bv_unsigned (edenot E n) = len ->
  (0 <= bv_unsigned a + off)%Z -> (0 < len)%Z -> (bv_unsigned a + off + len <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < len)%Z -> mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (Z_to_bv 8 0)) ->
  kentry_ok segs E mem (KZero (SA e off) n).
Proof.
  intros segs E mem e a off n len He Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
  cbn [a_base a_off]. rewrite He, Hn. split; [lia | exact Hz].
Qed.

Lemma kblob_intro : forall segs E mem (e : expr) (a : word) off (n : expr) k bs,
  edenot E e = a -> eb E k = bs -> bv_unsigned (edenot E n) = Z.of_nat (length bs) ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off < 2 ^ 64)%Z ->
  (bv_unsigned a + off + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < Z.of_nat (length bs))%Z ->
     mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
  kentry_ok segs E mem (KBlob (SA e off) n k).
Proof.
  intros segs E mem e a off n k bs He Hb Hn H1 H1' H2 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
  cbn [a_base a_off]. rewrite He, Hn, Hb. split; [lia|]. split; [reflexivity | exact Hz].
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_none_low : forall ph sp argv envp uid hw (rdraw : EntryDraw) (i : Z),
  (0 <= i)%Z -> (i < bv_unsigned sp - stack_max_size)%Z ->
  wrap_mem ph sp argv envp uid hw rdraw (Z_to_bv 64 i) = None.
Proof.
  intros ph sp argv envp uid hw rdraw i H0 Hi. unfold wrap_mem.
  pose proof (u64_range sp) as Hsp.
  assert (Hu : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; unfold stack_max_size in Hi; lia).
  unfold stack_to_mem. rewrite Hu.
  replace (Z.leb (bv_unsigned sp) i) with false by (symmetry; apply Z.leb_gt; unfold stack_max_size in Hi; lia).
  replace (Z.leb (bv_unsigned sp - stack_max_size) i) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ext_val_zx_id : forall n (v : word),
  (bv_unsigned v < 2 ^ (8 * Z.of_nat n))%Z -> ext_val false 0 n v = v.
Proof.
  intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma ext_val_sx_id : forall n (v : word),
  (1 <= n)%nat -> (bv_unsigned v < 2 ^ (8 * Z.of_nat n - 1))%Z -> ext_val true 0 n v = v.
Proof.
  intros n v Hn Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  assert (Hp : (2 ^ (8 * Z.of_nat n - 1) * 2 = 2 ^ (8 * Z.of_nat n))%Z).
  { rewrite Z.mul_comm, <- Z.pow_succ_r by lia. f_equal. lia. }
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia.
  rewrite <- Hp. rewrite Z.div_mul by lia.
  rewrite Z.mod_small by lia. replace (bv_unsigned v + 2 ^ (8 * Z.of_nat n - 1) - 2 ^ (8 * Z.of_nat n - 1))%Z
    with (bv_unsigned v) by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma branch_eq_lit : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_EQ v (Z_to_bv 64 z) = Z.eqb (bv_unsigned v) z.
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ne_lit : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_NE v (Z_to_bv 64 z) = negb (Z.eqb (bv_unsigned v) z).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ltu_lit_r : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_LTU v (Z_to_bv 64 z) = Z.ltb (bv_unsigned v) z.
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ltu_lit_l : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_LTU (Z_to_bv 64 z) v = Z.ltb z (bv_unsigned v).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_geu_lit_r : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_GEU v (Z_to_bv 64 z) = negb (Z.ltb (bv_unsigned v) z).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_geu_lit_l : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_GEU (Z_to_bv 64 z) v = negb (Z.ltb z (bv_unsigned v)).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.
End FPX_1.


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
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; sc_auto extra
              | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
                          (eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc ]
          end
      end
    end
  end.

End SymRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module SymDrive.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Frame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition blobs_ev (bl : list (list byte)) : nat -> list byte := fun n => nth n bl [].

Section Drive.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rz_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     srealizes segs scfg (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  srealizes segs scfg (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [|reflexivity].
  eapply carry_after; eassumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kread (kn : list kentry) (b : expr) (k : Z) (n : nat) : option expr :=
  match know_lookup segs kn b k n false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Lemma kread_sound : forall E M kn b k n v,
  know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b k) (Z.of_nat n) ->
  exists bs, rdn segs M (adenot E (SA b k)) n = Some bs /\ length bs = n
             /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl. unfold kread in Hr.
  pose proof (know_lookup_sound segs E M kn b k n false [] [] Hkn Hn1 Hn8) as Hs.
  destruct (know_lookup segs kn b k n false [] []) as [v' scs h|scs h|]; try discriminate.
  destruct scs; [|discriminate]. injection Hr as ->.
  destruct (Hs ltac:(constructor) Hfl) as (bs & A & B & C). exists bs. unfold extz in C. auto.
Qed.

Lemma word_to_le_bytes_of_lez : forall n bs,
  length bs = n -> (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros n bs Hl Hn. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
  assert (Hlt : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
  rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma kread_rdn : forall E M kn b k n v,
  know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b k) (Z.of_nat n) ->
  rdn segs M (adenot E (SA b k)) n = Some (word_to_le_bytes n (edenot E v)).
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl.
  destruct (kread_sound E M kn b k n v Hkn Hr Hn1 Hn8 Hfl) as (bs & A & B & C).
  rewrite A, <- C, word_to_le_bytes_of_lez by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint kblob_find (kn : list kentry) (b : expr) (k : Z) : option (expr * nat) :=
  match kn with
  | [] => None
  | KBlob (SA kb kk) len bk :: rest =>
      if (expr_eqb b kb && Z.eqb k kk)%bool then Some (len, bk) else kblob_find rest b k
  | _ :: rest => kblob_find rest b k
  end.

Lemma kblob_find_sound : forall E M kn b k len bk,
  know_ok segs E M kn -> kblob_find kn b k = Some (len, bk) ->
  kentry_ok segs E M (KBlob (SA b k) len bk).
Proof.
  intros E M kn b k len bk Hkn. induction kn as [|K rest IH]; cbn [kblob_find]; intros H; [discriminate|].
  apply Forall_cons_iff in Hkn as [HK Hrest].
  destruct K as [| |[kb kk] len' bk'| | | | |]; try (apply IH; assumption).
  destruct (expr_eqb b kb && Z.eqb k kk)%bool eqn:Heq; [|apply IH; assumption].
  apply andb_prop in Heq as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst.
  injection H as <- <-. exact HK.
Qed.

Lemma kblob_rdn : forall E M kn b k len bk,
  know_ok segs E M kn -> kblob_find kn b k = Some (len, bk) ->
  rdn segs M (adenot E (SA b k)) (length (eb E bk)) = Some (eb E bk).
Proof.
  intros E M kn b k len bk Hkn Hf.
  pose proof (kblob_find_sound E M kn b k len bk Hkn Hf) as HK. cbn [kentry_ok] in HK.
  destruct HK as (Hfl & Hlen & Hb).
  apply rdn_pointwise.
  - reflexivity.
  - rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
  - intros j Hj. rewrite (flat_u E _ _ Hfl). rewrite Hb by lia. rewrite Nat2Z.id. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma env_ext_regs : forall vals x ebs sr R,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R -> regs_ok (Env (vals_ev (vals ++ [x])) ebs) sr R.
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma env_ext_know : forall vals x ebs M kn,
  kn_vars_lt (length vals) kn = true ->
  know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ [x])) ebs) M kn.
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma vals_ev_last : forall vals x, vals_ev (vals ++ [x]) (length vals) = x.
Proof. intros. unfold vals_ev. rewrite nth_middle || (rewrite app_nth2, Nat.sub_diag by lia; reflexivity). reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_addi_pc4 : forall pc, (0 <= pc)%Z -> (pc + 4 < 2 ^ 64)%Z ->
  v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof. intros pc H0 H1. unfold v_addi. rewrite u_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma regs_set_a0 : forall E sr R v e,
  regs_ok E sr R -> edenot E e = v -> regs_ok E (sr_upd sr (ridx 10) e) (regupd R 10 v).
Proof. intros. apply regs_ok_set; [assumption | discriminate | assumption]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition junk_vals (R' : bvmap 5 word) : list word :=
  map (fun i => getr R' (Z_to_bv 5 (Z.of_nat i))) (seq 0 32).

Definition sr_after_call_j (sr : list expr) (kept : list nat) (jbase : nat) : list expr :=
  map (fun i => if existsb (Nat.eqb i) kept then nth i sr (ELit 0) else EVar (jbase + i))
      (seq 0 32).

Lemma nth_map_seq_gen : forall {A} (f : nat -> A) len s n d, (n < len)%nat ->
  nth n (map f (seq s len)) d = f (s + n)%nat.
Proof.
  intros A f len. induction len as [|len IH]; intros s n d H; [lia|].
  cbn [seq map]. destruct n as [|n].
  - cbn [nth]. rewrite Nat.add_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) n len d, (n < len)%nat ->
  nth n (map f (seq 0 len)) d = f n.
Proof. intros. rewrite nth_map_seq_gen by assumption. reflexivity. Qed.

Lemma sr_vars_lt_nth : forall b sr n, sr_vars_lt b sr = true -> expr_vars_lt b (nth n sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|e t IH]; intros n H; [destruct n; reflexivity|].
  cbn [sr_vars_lt] in H. apply andb_prop in H as [He Ht]. destruct n; [exact He | apply IH; exact Ht].
Qed.

Lemma regs_after_call : forall vals ebs sr R R' kept,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall i, In i kept -> (i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i))) ->
  ~ In 0%nat kept ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sr_after_call_j sr kept (length vals)) R'.
Proof.
  intros vals ebs sr R R' kept Hlt HR Hkept H0 r.
  pose proof (ridx_range r) as Hr.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - unfold sr_after_call_j. rewrite nth_map_seq by exact Hr.
    destruct (existsb (Nat.eqb (ridx r)) kept) eqn:Hex.
    + apply existsb_exists in Hex as (i & Hin & Heqi). apply Nat.eqb_eq in Heqi. subst i.
      destruct (Hkept _ Hin) as [_ Hg]. rewrite ridx_roundtrip in Hg. rewrite Hg.
      pose proof (HR r) as Hv. unfold sr_get in Hv. rewrite Hr0 in Hv. rewrite Hv.
      eapply edenot_agree; [apply vals_app_agree|]. apply sr_vars_lt_nth. exact Hlt.
    + cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia.
      replace (length vals + ridx r - length vals)%nat with (ridx r) by lia.
      unfold junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.

End Drive.

End FPX_1.

End SymDrive.
Module SymDriveX.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma know_nth : forall segs E M kn i K,
  know_ok segs E M kn -> nth_error kn i = Some K -> kentry_ok segs E M K.
Proof.
  intros segs E M kn i K HK Hn. unfold know_ok in HK.
  apply (proj1 (Forall_forall _ _) HK K). eapply nth_error_In. exact Hn.
Qed.

Lemma know_ok_app : forall segs E M k1 k2,
  know_ok segs E M (k1 ++ k2) <-> know_ok segs E M k1 /\ know_ok segs E M k2.
Proof. intros. unfold know_ok. apply Forall_app. Qed.

Lemma know_ok_cons : forall segs E M K kn,
  kentry_ok segs E M K -> know_ok segs E M kn -> know_ok segs E M (K :: kn).
Proof. intros. constructor; assumption. Qed.

(* [comment removed for export] *)
Fixpoint kindex (p : kentry -> bool) (kn : list kentry) (i : nat) : option nat :=
  match kn with
  | [] => None
  | K :: r => if p K then Some i else kindex p r (S i)
  end.

(* [comment removed for export] *)
Definition is_krange (e : expr) (K : kentry) : bool :=
  match K with KRange e' _ _ => expr_eqb e e' | _ => false end.
Definition is_kalign (e : expr) (K : kentry) : bool :=
  match K with KAlign e' _ => expr_eqb e e' | _ => false end.
Definition is_kdisj (b1 : expr) (b2 : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA c1 _) _ (SA c2 _) _ => expr_eqb b1 c1 && expr_eqb b2 c2
  | _ => false
  end.
(* [comment removed for export] *)
Definition is_kwr_cov (b : expr) (k m : Z) (K : kentry) : bool :=
  match K with
  | KWr (SA c kk) len => expr_eqb b c && Z.leb kk k && Z.leb (k + m) (kk + len)
  | _ => false
  end.
(* [comment removed for export] *)
Definition is_kimg_cov (a n : Z) (K : kentry) : bool :=
  match K with
  | KImg lo hi => Z.leb lo a && Z.leb (a + n) hi
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_agree : forall segs M M' n (a : word),
  (forall j, (j < n)%nat -> M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = M' (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
  rdn segs M a n = rdn segs M' a n.
Proof.
  intros segs M M' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn].
  pose proof (Hag 0%nat ltac:(lia)) as H0.
  rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  rewrite (IH (a + 1)); [reflexivity|].
  intros j Hj. rewrite w_add_1.
  pose proof (u64_range a) as Ha.
  destruct (Z_lt_le_dec (bv_unsigned a + 1) (2 ^ 64)) as [Hlt | Hge].
  - rewrite u_small by lia.
    replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
    apply Hag. lia.
  - replace (Z_to_bv 64 (bv_unsigned a + 1)) with (Z_to_bv 64 0)
      by (apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; replace (bv_unsigned a + 1)%Z with (2^64)%Z by lia; reflexivity).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    specialize (Hag (S j) ltac:(lia)).
    replace (bv_unsigned a + Z.of_nat (S j))%Z with (2 ^ 64 + Z.of_nat j)%Z in Hag by lia.
    replace (Z_to_bv 64 (2 ^ 64 + Z.of_nat j)) with (Z_to_bv 64 (0 + Z.of_nat j)) in Hag; [exact Hag|].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite <- (Zplus_mod_idemp_l (2 ^ 64) (Z.of_nat j)), Z_mod_same_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_untouched : forall segs M (a : Z) n,
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> M (Z_to_bv 64 i) = None) ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros segs M a n H0 Hnw Hnone. apply rdn_agree. intros j Hj.
  rewrite u_small by lia. rewrite Hnone by lia. reflexivity.
Qed.

Lemma kimg_rdn : forall segs E M kn i lo hi (a : Z) n,
  know_ok segs E M kn -> nth_error kn i = Some (KImg lo hi) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros segs E M kn i lo hi a n HK Hn Hlo Hhi.
  pose proof (know_nth segs E M kn i _ HK Hn) as (H0 & H64 & Hnone).
  apply rdn_untouched; [lia | lia |]. intros j Hj. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kwr_store_ok : forall segs E M kn i b kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA b kk) len) ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z ->
  store_ok segs M (adenot E (SA b k)) m = true.
Proof.
  intros segs E M kn i b kk len k m HK Hn H1 H2.
  pose proof (know_nth segs E M kn i _ HK Hn) as (Hfl & Hst).
  unfold adenot. cbn [a_base a_off].
  destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
  specialize (Hst (k - kk)%Z m ltac:(lia) ltac:(lia)).
  replace (bv_unsigned (edenot E b) + kk + (k - kk))%Z with (bv_unsigned (edenot E b) + k)%Z in Hst by lia.
  unfold v_addi. exact Hst.
Qed.

(* [comment removed for export] *)
Lemma kwr_store_ok_lit : forall segs E M kn i kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA (ELit 0) kk) len) ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z -> (0 <= k < 2 ^ 64)%Z ->
  store_ok segs M (Z_to_bv 64 k) m = true.
Proof.
  intros segs E M kn i kk len k m HK Hn H1 H2 Hk.
  pose proof (kwr_store_ok segs E M kn i (ELit 0) kk len k m HK Hn H1 H2) as H.
  unfold adenot, v_addi in H. cbn [a_base a_off edenot] in H.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H. rewrite Z.add_0_l in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_below_b (spi : nat) (ihi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && Z.leb (k + Z.of_nat w) 0 && Z.leb (- 2 ^ 40) k
  | SE (SA (ELit 0) k) w _ => Z.leb 0 k && Z.leb (k + Z.of_nat w) ihi
  | _ => false
  end.

Definition log_below_b (spi : nat) (ihi : Z) (log : list sentry) : bool :=
  forallb (entry_below_b spi ihi) log.

Lemma entry_below_sound : forall E spi ihi b k w v (x : word),
  entry_below_b spi ihi (SE (SA b k) w v) = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
  (bv_unsigned (adenot E (SA b k)) + Z.of_nat w <= bv_unsigned x)%Z.
Proof.
  intros E spi ihi b k w v x He Hsp Hx1 Hx2.
  unfold adenot, v_addi. cbn [a_base a_off]. pose proof (u64_range x) as Hxr.
  destruct b as [z|i| | | | | |]; cbn [entry_below_b] in He; try discriminate.
  - destruct z; try discriminate. apply andb_prop in He as [He1 He2].
    apply Z.leb_le in He1. apply Z.leb_le in He2. cbn [edenot].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l, u_small by lia. lia.
  - apply andb_prop in He as [He1 He3]. apply andb_prop in He1 as [He1 He2].
    apply Nat.eqb_eq in He1. subst i. apply Z.leb_le in He2. apply Z.leb_le in He3.
    cbn [edenot]. pose proof (u64_range (ev E spi)) as Hs. rewrite u_small by lia. lia.
Qed.

Lemma mem_denot_above : forall E M log spi ihi (x : word),
  log_below_b spi ihi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi ihi x Hb Hsp Hx1 Hx2.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_below_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  pose proof (entry_below_sound E spi ihi b k w v x He Hsp Hx1 Hx2) as Hbnd.
  pose proof (u64_range x) as Hxr.
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. lia.
  - rewrite length_N_to_le_bytes. right. lia.
Qed.

Lemma rdn_mem_denot_above : forall segs E M log spi ihi (a : word) n,
  log_below_b spi ihi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned a)%Z -> (ihi <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs (mem_denot E M log) a n = rdn segs M a n.
Proof.
  intros segs E M log spi ihi a n Hb Hsp H1 H2 Hnw.
  apply rdn_agree. intros j Hj. pose proof (u64_range a).
  apply (mem_denot_above E M log spi ihi); try assumption; rewrite u_small by lia; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint esub (f t : expr) (e : expr) : expr :=
  if expr_eqb e f then t else
  match e with
  | EAlu op a b => EAlu op (esub f t a) (esub f t b)
  | EAluw op a b => EAluw op (esub f t a) (esub f t b)
  | EMd op a b => EMd op (esub f t a) (esub f t b)
  | EMdw op a b => EMdw op (esub f t a) (esub f t b)
  | EExt sx lo n a => EExt sx lo n (esub f t a)
  | _ => e
  end.

Lemma esub_sound : forall E f t e,
  edenot E f = edenot E t -> edenot E (esub f t e) = edenot E e.
Proof.
  intros E f t e Hft. induction e; cbn [esub];
    (destruct (expr_eqb _ f) eqn:Eq;
     [apply expr_eqb_eq in Eq; rewrite <- Eq in Hft; symmetry; exact Hft|]);
    cbn [edenot]; try reflexivity;
    try (rewrite IHe1, IHe2; reflexivity);
    try (rewrite IHe; reflexivity).
Qed.

Definition asub (f t : expr) (a : saddr) : saddr := SA (esub f t (a_base a)) (a_off a).

Lemma asub_sound : forall E f t a,
  edenot E f = edenot E t -> adenot E (asub f t a) = adenot E a.
Proof. intros E f t [b k] H. unfold asub, adenot. cbn [a_base a_off]. rewrite esub_sound by exact H. reflexivity. Qed.

Lemma asub_estart : forall E f t a,
  edenot E f = edenot E t -> estart E (asub f t a) = estart E a.
Proof. intros E f t [b k] H. unfold asub, estart. cbn [a_base a_off]. rewrite esub_sound by exact H. reflexivity. Qed.

Definition ksub (f t : expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asub f t a) w (esub f t v)
  | KZero a n => KZero (asub f t a) (esub f t n)
  | KBlob a n bk => KBlob (asub f t a) (esub f t n) bk
  | KImg lo hi => K
  | KAlign e m => KAlign (esub f t e) m
  | KRange e lo hi => KRange (esub f t e) lo hi
  | KWr a n => KWr (asub f t a) n
  | KDisj a1 n1 a2 n2 => KDisj (asub f t a1) n1 (asub f t a2) n2
  end.

Lemma flat_asub : forall E f t a n,
  edenot E f = edenot E t -> flat E (asub f t a) n <-> flat E a n.
Proof. intros E f t a n H. unfold flat. rewrite asub_estart by exact H. tauto. Qed.

Lemma ksub_sound : forall segs E M f t K,
  edenot E f = edenot E t -> kentry_ok segs E M K -> kentry_ok segs E M (ksub f t K).
Proof.
  intros segs E M f t K H HK. destruct K; cbn [ksub kentry_ok] in *.
  - rewrite (asub_sound E f t a H), (esub_sound E f t v H). rewrite (flat_asub E f t a _ H). exact HK.
  - unfold elenZ in *. rewrite (esub_sound E f t n H), (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
  - unfold elenZ in *. rewrite (esub_sound E f t n H), (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
  - exact HK.
  - rewrite (esub_sound E f t e H). exact HK.
  - rewrite (esub_sound E f t e H). exact HK.
  - rewrite (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
  - rewrite (asub_estart E f t a1 H), (asub_estart E f t a2 H). exact HK.
Qed.

Lemma know_ok_ksub : forall segs E M f t kn,
  edenot E f = edenot E t -> know_ok segs E M kn -> know_ok segs E M (map (ksub f t) kn).
Proof.
  intros segs E M f t kn H HK. unfold know_ok in *. apply Forall_map.
  eapply Forall_impl; [|exact HK]. intros K. apply ksub_sound. exact H.
Qed.

Lemma regs_ok_esub : forall E f t sr R,
  edenot E f = edenot E t -> regs_ok E sr R -> regs_ok E (map (esub f t) sr) R.
Proof.
  intros E f t sr R H HR r. rewrite (HR r). unfold sr_get.
  destruct (bv_eqb r 0); [reflexivity|].
  revert sr HR. generalize (ridx r) as i. intros i sr _.
  revert i. induction sr as [|e rest IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [|i]; cbn [map nth].
    + symmetry. apply esub_sound. exact H.
    + apply IH.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_ext : forall E sr sr' R,
  length sr = length sr' ->
  (forall i, (i < length sr)%nat -> edenot E (nth i sr (ELit 0)) = edenot E (nth i sr' (ELit 0))) ->
  regs_ok E sr R -> regs_ok E sr' R.
Proof.
  intros E sr sr' R Hlen Heq HR r. rewrite (HR r). unfold sr_get.
  destruct (bv_eqb r 0); [reflexivity|].
  destruct (Nat.lt_ge_cases (ridx r) (length sr)) as [Hlt | Hge].
  - apply Heq. exact Hlt.
  - rewrite !nth_overflow by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma junk_vals_length : forall R, length (junk_vals R) = 32%nat.
Proof. intros R. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.

Lemma vals_ev_app_l : forall vals extra n, (n < length vals)%nat ->
  vals_ev (vals ++ extra) n = vals_ev vals n.
Proof. intros. unfold vals_ev. rewrite app_nth1 by assumption. reflexivity. Qed.

Lemma vals_ev_app_r : forall vals extra n,
  vals_ev (vals ++ extra) (length vals + n) = vals_ev extra n.
Proof. intros. unfold vals_ev. rewrite app_nth2_plus. reflexivity. Qed.

(* [comment removed for export] *)
Lemma env_app_know : forall segs vals extra ebs M kn,
  kn_vars_lt (length vals) kn = true ->
  know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ extra)) ebs) M kn.
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma env_app_regs : forall vals extra ebs sr R,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R -> regs_ok (Env (vals_ev (vals ++ extra)) ebs) sr R.
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma env_app_edenot : forall vals extra ebs e,
  expr_vars_lt (length vals) e = true ->
  edenot (Env (vals_ev (vals ++ extra)) ebs) e = edenot (Env (vals_ev vals) ebs) e.
Proof. intros. symmetry. eapply edenot_agree; [apply vals_app_agree | assumption]. Qed.

(* [comment removed for export] *)
Lemma regs_after_keeps : forall vals ebs sr R R' (kept : list reg),
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall r : reg, In r kept -> getr R' r = getr R r) ->
  ~ In 0%bv kept ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs)
          (sr_after_call_j sr (map ridx kept) (length vals)) R'.
Proof.
  intros vals ebs sr R R' kept Hlt HR Hk H0.
  apply (regs_after_call vals ebs sr R R' (map ridx kept) Hlt HR).
  - intros i Hi. apply in_map_iff in Hi as (r & <- & Hr). split; [apply ridx_range|].
    rewrite ridx_roundtrip. apply Hk. exact Hr.
  - intros Hin. apply in_map_iff in Hin as (r & Hr0 & Hr). apply H0.
    replace 0%bv with r; [exact Hr|]. apply ridx_inj. rewrite Hr0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma know_after_store : forall segs E M kn sa w v bs kn' scs hs,
  carry [SE sa w v] kn [] = (kn', scs, hs) -> scs = [] ->
  know_ok segs E M kn -> (w <= 8)%nat -> flat E sa (Z.of_nat w) ->
  bs = word_to_le_bytes w (edenot E v) ->
  know_ok segs E (wbytes M (adenot E sa) bs) kn'.
Proof.
  intros segs E M kn sa w v bs kn' scs hs Hc -> HK Hw Hfl ->.
  change (wbytes M (adenot E sa) (word_to_le_bytes w (edenot E v))) with (mem_denot E M [SE sa w v]).
  eapply carry_after; [exact Hc | | exact HK | constructor].
  cbn [log_flat]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_bv_lit : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma flat_intro : forall E b k n,
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (0 <= n)%Z ->
  (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z ->
  flat E (SA b k) n.
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ECALLW : bv 32 := Z_to_bv 32 0x73.
Lemma is_ecall_ECALLW : is_ecall ECALLW = true. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma adenot_lit0 : forall E a, adenot E (SA (ELit 0) a) = Z_to_bv 64 a.
Proof. intros. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l. reflexivity. Qed.

Lemma edenot_add_lit : forall E b k, edenot E (EAlu ALU_ADD b (ELit k)) = adenot E (SA b k).
Proof.
  intros. cbn [edenot]. rewrite alu_add. unfold adenot, v_addi, v_add. cbn [a_base a_off].
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Zplus_mod_idemp_r.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac split_foralls :=
  repeat lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| ]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| ]
  end.

(* [comment removed for export] *)
Ltac run_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- srealizes _ ?scfg (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run segs scfg fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_compute; reflexivity
            | vm_compute; reflexivity
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with HR HK fuel stops scr NX keep
  end.

(* [comment removed for export] *)
Ltac regv HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e;
    lazymatch e with ELit _ => cbn [edenot] | _ => idtac end
  end.

(* [comment removed for export] *)
Ltac krd HK a n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (ELit 0) a n) in
    lazymatch r with
    | Some ?v =>
        pose proof (kread_rdn segs E M kn (ELit 0) a n v HK
                      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
                      ltac:(unfold flat, estart; cbn [a_base a_off edenot];
                            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as H;
        rewrite adenot_lit0 in H; cbn [edenot] in H
    | None => fail "krd: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac krdv HK i k n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (EVar i) k n) in
    lazymatch r with
    | Some ?v =>
        let Hf := fresh "Hflat" in
        assert (Hf : flat E (SA (EVar i) k) (Z.of_nat n));
        [ | pose proof (kread_rdn segs E M kn (EVar i) k n v HK
                          ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hf) as H;
            clear Hf; cbn [edenot] in H ]
    | None => fail "krdv: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac kidx kn p :=
  let r := eval vm_compute in (kindex p kn 0) in
  lazymatch r with Some ?i => i | None => fail "kidx: no such entry" end.

(* [comment removed for export] *)
Ltac krd_solve HK :=
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some _ =>
      let H := fresh "Hrd" in
      krd HK a n H; rewrite H; clear H;
      first [ reflexivity | rewrite ?Z_to_bv_bv_unsigned; reflexivity | idtac ]
  end.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Lemma callee_kept_no0 : ~ In (0%bv : reg) callee_kept.
Proof.
  unfold callee_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => ranges_apart allkn ub uk un b k (Z.of_nat w)
  | KZero (SA b k) (ELit l) => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
  | KBlob (SA b k) (ELit l) _ => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
  | KImg _ _ => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart allkn ub uk un b k n
  | _ => false
  end.

Definition kn_unfill (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
  List.filter (kentry_apart_b kn ub uk un) kn.

Lemma unfill_outside : forall (a n : word) M (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  unfill a n M x = M x.
Proof.
  intros a n M x H. unfold unfill.
  destruct H as [H|H].
  - rewrite (proj2 (Z.leb_gt _ _) H). reflexivity.
  - destruct (bv_unsigned a <=? bv_unsigned x)%Z; [|reflexivity].
    rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

Lemma unfill_none : forall (a n : word) M (x : word), M x = None -> unfill a n M x = None.
Proof. intros a n M x H. unfold unfill. rewrite H. destruct (_ && _)%bool; reflexivity. Qed.

Lemma wview_ext : forall segs M M' (x : word), M' x = M x -> wview segs M' x = wview segs M x.
Proof. intros segs M M' x H. unfold wview. rewrite H. reflexivity. Qed.

Lemma store_ok_agree : forall segs M M' (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z -> M' x = M x) ->
  store_ok segs M a n = true -> store_ok segs M' a n = true.
Proof.
  intros segs M M' a n Hnw Hag Hs. apply store_ok_of_all; [exact Hnw|].
  intros x Hx. rewrite (wview_ext segs M M' x (Hag x Hx)). exact (store_ok_all segs M n a Hnw Hs x Hx).
Qed.

Lemma know_ok_unfill : forall segs E M kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un -> (un < 2 ^ 64)%Z ->
  know_ok segs E (unfill (adenot E (SA ub uk)) (Z_to_bv 64 un) M) (kn_unfill kn ub uk un).
Proof.
  intros segs E M kn ub uk un HK Hfl Hun.
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  set (a := adenot E (SA ub uk)) in *. set (nw := Z_to_bv 64 un).
  assert (Hn : bv_unsigned nw = un) by (subst nw; apply u_small; lia).
  (* [comment removed for export] *)
  assert (OUT : forall x : word,
            (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z ->
            unfill a nw M x = M x).
  { intros x Hx. apply unfill_outside. rewrite Hu, Hn. exact Hx. }
  unfold know_ok, kn_unfill. apply Forall_forall. intros K HinF.
  apply filter_In in HinF as [Hin Hb].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (APART : forall b k n, ranges_apart kn ub uk un b k n = true ->
            ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
  { intros b k n H. eapply ranges_apart_sound; [exact HK | exact H]. }
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kentry_apart_b] in Hb; cbn [kentry_ok] in HKK |- *; try exact HKK.
  - (* [comment removed for export] *)
    destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hr. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hf) as Hub. destruct Hf as (G1 & G2 & G3 & G4).
    apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hb); lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try discriminate.
    apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct HKK as (Hf & Hz). split; [exact Hf|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
    intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
    rewrite u_small by lia. destruct (APART b k l Hap); lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try discriminate.
    apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct HKK as (Hf & Hlen & Hz). split; [exact Hf|]. split; [exact Hlen|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
    intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
    rewrite u_small by lia. destruct (APART b k l Hap); lia.
  - (* [comment removed for export] *)
    destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
    intros i Hi. apply unfill_none. apply Hnone. exact Hi.
  - (* [comment removed for export] *)
    destruct HKK as (Hf & Hst). split; [exact Hf|].
    destruct Hf as (G1 & G2 & G3 & G4).
    intros d m Hd Hm. destruct m as [|m]; [reflexivity|].
    apply (store_ok_agree segs M); [rewrite u_small by lia; lia | | apply Hst; assumption].
    intros x Hx. rewrite u_small in Hx by lia. apply OUT. destruct (APART b k n Hb); lia.
Qed.
End FPX_2.



Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End SymDriveX.
Module SymDriveH4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma low32_zero_sext : low32 (Z_to_bv 64 0) = sext 32 (0 : bv 12).
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma edenot_addw0_r : forall E a,
  (bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
  edenot E (EAluw ALU_ADD a (ELit 0)) = edenot E a.
Proof.
  intros E a Ha. cbn [edenot]. rewrite low32_zero_sext, w_addiw.
  change (bv_signed (0 : bv 12)) with 0%Z. apply v_addiw_id. exact Ha.
Qed.

Lemma alu32_add_comm : forall x y : bv 32, alu32 ALU_ADD x y = alu32 ALU_ADD y x.
Proof.
  intros x y. change (x + y = y + x). apply bv_eq.
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma edenot_addw0_l : forall E a,
  (bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
  edenot E (EAluw ALU_ADD (ELit 0) a) = edenot E a.
Proof.
  intros E a Ha. cbn [edenot]. rewrite alu32_add_comm.
  pose proof (edenot_addw0_r E a Ha) as H. cbn [edenot] in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma edenot_exts4 : forall E a,
  (bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
  edenot E (EExt true 0 4 a) = edenot E a.
Proof.
  intros E a Ha. cbn [edenot]. apply ext_val_sx_id; [lia|].
  change (2 ^ (8 * Z.of_nat 4 - 1))%Z with (2 ^ 31)%Z. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma edenot_extu4 : forall E a,
  (bv_unsigned (edenot E a) < 2 ^ 32)%Z ->
  edenot E (EExt false 0 4 a) = edenot E a.
Proof.
  intros E a Ha. cbn [edenot]. apply ext_val_zx_id.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. exact Ha.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac intisms E e Hsmall :=
  repeat first [ rewrite (edenot_addw0_r E e Hsmall)
               | rewrite (edenot_addw0_l E e Hsmall)
               | rewrite (edenot_exts4 E e Hsmall) ].
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition win_out_b (spi : nat) (lo hi ihi : Z) (b : expr) (k n : Z) : bool :=
  match b with
  | EVar i => Nat.eqb i spi && (Z.leb (k + n) lo || Z.leb hi k)
              && Z.leb (- 2 ^ 40) k && Z.leb (k + n) (2 ^ 40) && Z.leb 0 n
  | ELit z => Z.eqb z 0 && Z.leb 0 k && Z.leb 0 n && Z.leb (k + n) ihi
  | _ => false
  end.

(* [comment removed for export] *)
Definition win_ok (E : env) (spi : nat) (lo hi ihi : Z) : Prop :=
  (2 ^ 41 <= bv_unsigned (ev E spi))%Z /\ (bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64)%Z
  /\ (lo <= hi)%Z /\ (- 2 ^ 40 <= lo)%Z /\ (hi <= 2 ^ 40)%Z
  /\ (0 <= ihi)%Z /\ (ihi <= bv_unsigned (ev E spi) + lo)%Z.

Lemma win_out_sound : forall E spi lo hi ihi b k n,
  win_out_b spi lo hi ihi b k n = true -> win_ok E spi lo hi ihi ->
  (0 <= bv_unsigned (edenot E b) + k)%Z
  /\ (bv_unsigned (edenot E b) + k < 2 ^ 64 /\ bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z
  /\ (0 <= n)%Z
  /\ forall x : word,
       (bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n)%Z ->
       ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z.
Proof.
  intros E spi lo hi ihi b k n Hb (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate.
  - repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
    apply Z.eqb_eq in Hb. subst z.
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
    cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat split; try lia.
  - repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
    apply Nat.eqb_eq in Hb. subst i.
    repeat match goal with
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : (_ || _)%bool = true |- _ => apply orb_prop in H
           end.
    cbn [edenot]. repeat split; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition entry_out_b (spi : nat) (lo hi ihi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
  end.

Definition log_out_b (spi : nat) (lo hi ihi : Z) (log : list sentry) : bool :=
  forallb (entry_out_b spi lo hi ihi) log.

Lemma mem_denot_out : forall E M log spi lo hi ihi (x : word),
  log_out_b spi lo hi ihi log = true -> win_ok E spi lo hi ihi ->
  (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi lo hi ihi x Hb Hw Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_out_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_out_b] in He.
  destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) He Hw) as (A & B & C & D).
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
    pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k)) as [L|G]; [left; lia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k + Z.of_nat w)) as [L2|G2]; [|right; lia].
    exfalso. apply (D x); lia.
Qed.

Lemma rdn_mem_denot_out : forall segs E M log spi lo hi ihi (a : word) n,
  log_out_b spi lo hi ihi log = true -> win_ok E spi lo hi ihi ->
  (bv_unsigned (ev E spi) + lo <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned (ev E spi) + hi)%Z ->
  rdn segs (mem_denot E M log) a n = rdn segs M a n.
Proof.
  intros segs E M log spi lo hi ihi a n Hb Hw H1 H2.
  destruct Hw as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  apply rdn_agree. intros j Hj. pose proof (u64_range a).
  apply (mem_denot_out E M log spi lo hi ihi); [exact Hb | repeat split; assumption |].
  rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_out_b (spi : nat) (lo hi ihi : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
  | KZero (SA b k) (ELit n) => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
  | KBlob (SA b k) (ELit n) _ => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
  | KImg l h => Z.leb h ihi
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr _ _ => true
  | _ => false
  end.

Definition kn_cut (spi : nat) (lo hi ihi : Z) (kn : list kentry) : list kentry :=
  List.filter (kentry_out_b spi lo hi ihi) kn.

Lemma elenZ_lit_small : forall E n, (0 <= n < 2 ^ 64)%Z -> elenZ E (ELit n) = n.
Proof. intros E n Hn. unfold elenZ. cbn [edenot]. apply u_small. lia. Qed.

Lemma kentry_cut_sound : forall segs E M M' spi lo hi ihi K,
  win_ok E spi lo hi ihi ->
  (forall x : word,
     ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z -> M' x = M x) ->
  mem_grows M M' ->
  kentry_ok segs E M K -> kentry_out_b spi lo hi ihi K = true -> kentry_ok segs E M' K.
Proof.
  intros segs E M M' spi lo hi ihi K Hw Hag Hg HK Hb.
  pose proof Hw as Hw'. destruct Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|a n|a1 n1 a2 n2]; cbn [kentry_out_b] in Hb;
    cbn [kentry_ok] in HK |- *; try exact HK.
  - (* [comment removed for export] *)
    destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
    destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) Hb Hw) as (A & B & C & D).
    rewrite <- Hr. apply rdn_agree. intros j Hj. apply Hag. 
    pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
    rewrite Hu. apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz).
    assert (Hn0 : (0 <= n)%Z).
    { destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
        repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
        repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hlen & Hz).
    assert (Hn0 : (0 <= n)%Z).
    { destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
        repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
        repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
    rewrite elenZ_lit_small in Hfl, Hlen, Hz |- * by lia.
    split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    apply Z.leb_le in Hb. destruct HK as (H0 & H64 & Hnone).
    split; [exact H0|]. split; [exact H64|]. intros i Hi.
    rewrite Hag; [apply Hnone; exact Hi|]. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    eapply store_ok_mono; [exact Hg|]. apply Hst; assumption.
Qed.

Theorem know_cut_sound : forall segs E M M' spi lo hi ihi kn,
  win_ok E spi lo hi ihi ->
  (forall x : word,
     ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M kn -> know_ok segs E M' (kn_cut spi lo hi ihi kn).
Proof.
  intros segs E M M' spi lo hi ihi kn Hw Hag Hg HK. unfold know_ok in *.
  induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HK2].
  change (kn_cut spi lo hi ihi (K :: rest))
    with (if kentry_out_b spi lo hi ihi K then K :: kn_cut spi lo hi ihi rest else kn_cut spi lo hi ihi rest).
  destruct (kentry_out_b spi lo hi ihi K) eqn:Hb.
  - constructor; [|apply IH; exact HK2]. eapply kentry_cut_sound; eauto.
  - apply IH. exact HK2.
Qed.

(* [comment removed for export] *)
Lemma wbytes_agree_out : forall M (a : word) bs E spi lo hi,
  (bv_unsigned (ev E spi) + lo <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned (ev E spi) + hi)%Z ->
  (bv_unsigned (ev E spi) + hi <= 2 ^ 64)%Z ->
  forall x : word,
    ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
    wbytes M a bs x = M x.
Proof.
  intros M a bs E spi lo hi H1 H2 H3 x Hx. pose proof (u64_range x).
  apply wbytes_outside; [lia|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a)) as [L|G]; [left; exact L | right].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [L2|G2]; [|exact G2].
  exfalso. apply Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma krange_of_know : forall segs E M kn i e lo hi,
  know_ok segs E M kn -> nth_error kn i = Some (KRange e lo hi) ->
  (lo <= bv_unsigned (edenot E e) <= hi)%Z.
Proof.
  intros segs E M kn i e lo hi HK Hn.
  pose proof (know_nth segs E M kn i _ HK Hn) as H. cbn [kentry_ok] in H. lia.
Qed.
End FPX_2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End SymDriveH4.
Module RefReadLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Frame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kfootprint (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a n => Some (estart E a, elenZ E n)
  | KBlob a n _ => Some (estart E a, elenZ E n)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | _ => None
  end.

Definition kfoot_far (E : env) (K : kentry) (wa wn : Z) : Prop :=
  match kfootprint E K with
  | None => True
  | Some (s, n) => (s + n <= wa \/ wa + wn <= s)%Z
  end.

Lemma wbytes_same_far : forall m (a : word) bs (x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x + 1 <= bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof.
  intros m a bs x Hnw Hfar. apply wbytes_outside; [|exact Hnw]. unfold in_rng. lia.
Qed.

Lemma kentry_ok_wbytes_far : forall segs E M (a : word) bs K,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  kfoot_far E K (bv_unsigned a) (Z.of_nat (length bs)) ->
  kentry_ok segs E M K -> kentry_ok segs E (wbytes M a bs) K.
Proof.
  intros segs E M a bs K Hnw Hfar HK.
  destruct K as [[b k] w v|[b k] n|[b k] n bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kfoot_far kfootprint kentry_ok] in *; try exact HK.
  - destruct HK as (Hw & Hfl & Hr). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hr. pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    apply rdn_agree. intros j Hj. rewrite Hu. apply wbytes_same_far; [exact Hnw|].
    rewrite u_small by lia. unfold estart in *. cbn [a_base a_off] in *. lia.
  - destruct HK as (Hfl & Hz). split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite wbytes_same_far; [apply Hz; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
  - destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite wbytes_same_far; [apply Hz; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
  - destruct HK as (H0 & H64 & Hnone). split; [exact H0|]. split; [exact H64|]. intros i Hi.
    rewrite wbytes_same_far; [apply Hnone; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
  - destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    eapply store_ok_mono; [apply wbytes_grows|]. apply Hst; assumption.
Qed.

Lemma know_ok_wbytes_far : forall segs E M (a : word) bs kn,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  Forall (fun K => kfoot_far E K (bv_unsigned a) (Z.of_nat (length bs))) kn ->
  know_ok segs E M kn -> know_ok segs E (wbytes M a bs) kn.
Proof.
  intros segs E M a bs kn Hnw Hfar HK. unfold know_ok in *.
  induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in Hfar as [F1 F2]. apply Forall_cons_iff in HK as [K1 K2].
  constructor; [eapply kentry_ok_wbytes_far; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma wbytes_nil' : forall m (a : word), wbytes m a [] = m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mem_denot_1 : forall E M a w v,
  mem_denot E M [SE a w v] = wbytes M (adenot E a) (word_to_le_bytes w (edenot E v)).
Proof. reflexivity. Qed.

Lemma mem_denot_nil : forall E M, mem_denot E M [] = M.
Proof. reflexivity. Qed.

Lemma rdn_wbytes_self : forall segs m (a : word) bs,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  rdn segs (wbytes m a bs) a (length bs) = Some bs.
Proof. intros. apply rdn_wbytes_hit. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma word_to_nat_lit : forall z, (0 <= z < 2 ^ 64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof. intros z Hz. unfold word_to_nat. rewrite u_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma file_read_all : forall data (cnt : Z),
  (Z.of_nat (length data) <= cnt < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 0) (Z_to_bv 64 cnt) = data.
Proof.
  intros data cnt Hc. rewrite file_read_unguarded. rewrite !word_to_nat_lit by lia. cbn [Z.to_nat skipn].
  apply firstn_all2. lia.
Qed.

(* [comment removed for export] *)
Lemma file_read_eof : forall data (off cnt : word),
  (Z.of_nat (length data) <= bv_unsigned off)%Z -> file_read data off cnt = [].
Proof.
  intros data off cnt Ho. rewrite file_read_unguarded.
  rewrite skipn_all2 by (unfold word_to_nat; lia). apply firstn_nil.
Qed.

(* [comment removed for export] *)
Lemma file_read_full : forall data (off cnt : Z),
  (0 <= off)%Z -> (0 <= cnt)%Z -> (off + cnt <= Z.of_nat (length data))%Z -> (Z.of_nat (length data) < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data)
  /\ length (file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt)) = Z.to_nat cnt.
Proof.
  intros data off cnt H0 H1 H2 H3. rewrite !file_read_unguarded. rewrite !word_to_nat_lit by lia.
  split; [reflexivity|]. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma len_word_Z : forall bs : list byte, len_word bs = Z_to_bv 64 (Z.of_nat (length bs)).
Proof. intros. reflexivity. Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End RefReadLib.
