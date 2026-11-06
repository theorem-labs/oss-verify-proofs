(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlanSound.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module SEG.
Import AX2. Import AX2S. Import APC. Import APS.
Section WithFP1. Context {FP : PropExec.FPState}.
Definition bc_eqb (x y : branch_cond) : bool :=
  match x, y with
  | BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
  | _, _ => false
  end.

Lemma bc_eqb_eq : forall x y, bc_eqb x y = true -> x = y.
Proof. intros x y H. destruct x, y; cbn in H; try discriminate; reflexivity. Qed.

(* [comment removed for export] *)
Definition sc_eqb (x y : sidecond) : bool :=
  match x, y with
  | SCBr t c a b, SCBr t' c' a' b' => Bool.eqb t t' && bc_eqb c c' && expr_eqb a a' && expr_eqb b b'
  | SCReadBase a n sx e, SCReadBase a' n' sx' e' => saddr_eqb a a' && Nat.eqb n n' && Bool.eqb sx sx' && expr_eqb e e'
  | SCEq a b, SCEq a' b' => expr_eqb a a' && expr_eqb b b'
  | _, _ => sidecond_eqb x y
  end%bool.

Lemma sc_eqb_eq : forall x y, sc_eqb x y = true -> x = y.
Proof.
  intros x y H. unfold sc_eqb in H.
  destruct x, y; try (apply sidecond_eqb_eq in H; exact H); try discriminate.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Bool.eqb_prop in H1. apply bc_eqb_eq in H2. apply expr_eqb_eq in H3. apply expr_eqb_eq in H4. subst. reflexivity.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply saddr_eqb_eq in H1. apply Nat.eqb_eq in H2. apply Bool.eqb_prop in H3. apply expr_eqb_eq in H4. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst. reflexivity.
Qed.

Fixpoint scs_eqb (a b : list sidecond) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => sc_eqb x y && scs_eqb a' b'
  | _, _ => false
  end.

Lemma scs_eqb_eq : forall a b, scs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [scs_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply sc_eqb_eq in H1. rewrite H1, (IH b H2). reflexivity.
Qed.

Fixpoint exprs_eqb (a b : list expr) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => expr_eqb x y && exprs_eqb a' b'
  | _, _ => false
  end.

Lemma exprs_eqb_eq : forall a b, exprs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [exprs_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. rewrite H1, (IH b H2). reflexivity.
Qed.

(* [comment removed for export] *)
Definition kn_inclb (a b : list kentry) : bool := forallb (fun K => existsb (kentry_eqb K) b) a.

(* [comment removed for export] *)
Definition fp_item : Type := (expr * Z * Z)%type.

Definition out_fp (E : env) (fp : list fp_item) (x : word) : Prop :=
  Forall (fun it => match it with (b, lo, hi) =>
            bv_unsigned x < bv_unsigned (edenot E b) + lo \/ bv_unsigned (edenot E b) + hi <= bv_unsigned x end) fp.

(* [comment removed for export] *)
Definition log_fp (log : list sentry) (fp : list fp_item) : bool :=
  forallb (fun se => match se with SE (SA b o) w _ =>
             existsb (fun it => match it with (b', lo, hi) =>
                        expr_eqb b b' && Z.leb lo o && Z.leb (o + Z.of_nat w) hi end) fp end) log.

Record seg : Type := SEGM {
  g_pc    : Z;
  g_sr    : list expr;
  g_kn    : list kentry;
  g_nx    : nat;
  g_scr   : scripts;
  g_fuel  : nat;
  g_stops : list Z;
  (* [comment removed for export] *)
  g_opc   : Z;
  g_osr   : list expr;
  g_okn   : list kentry;
  g_fp    : list fp_item;
  g_scs   : list sidecond
}.

Section WithSegs.
Variable segs : list Segment.

Lemma kn_inclb_sound : forall E M a b, kn_inclb a b = true -> know_ok segs E M b -> know_ok segs E M a.
Proof.
  intros E M a b H HK. unfold know_ok in *. apply Forall_forall. intros K HinK.
  unfold kn_inclb in H. pose proof (proj1 (forallb_forall _ _) H K HinK) as H'. clear H. rename H' into H.
  apply existsb_exists in H as (K' & Hin' & Heq). apply kentry_eqb_eq in Heq. subst K'.
  exact (proj1 (Forall_forall _ _) HK _ Hin').
Qed.

Lemma mem_denot_out : forall E M log fp x,
  log_flat E log -> log_fp log fp = true -> out_fp E fp x -> mem_denot E M log x = M x.
Proof.
  intros E M log fp x Hlf Hfp Hout. induction log as [|[[b o] w v] rest IH]; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hfl & Hlf').
  cbn [log_fp forallb] in Hfp. apply andb_prop in Hfp as [H1 H2].
  cbn [mem_denot]. rewrite wbytes_out.
  - apply IH; assumption.
  - rewrite length_N_to_le_bytes. rewrite (flat_u E _ _ Hfl). destruct Hfl as (F1 & F2 & F3 & F4). lia.
  - rewrite length_N_to_le_bytes. rewrite (flat_u E _ _ Hfl).
    apply existsb_exists in H1 as ([[b' lo] hi] & Hin & Hb).
    apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [H3 H4].
    apply expr_eqb_eq in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. subst b'.
    pose proof (proj1 (Forall_forall _ _) Hout _ Hin) as Hx. cbn in Hx.
    unfold estart. cbn [a_base a_off]. lia.
Qed.

Definition seg_run (G : seg) : sym_state * list sidecond * scripts :=
  sym_exec segs (g_fuel G) true (g_stops G) (g_scr G) (SS (g_pc G) (g_sr G) [] (g_kn G) (g_nx G)) [].

Definition seg_check (G : seg) : bool :=
  let '(ssF, scs, _) := seg_run G in
  (Z.eqb (s_pc ssF) (g_opc G) && exprs_eqb (s_regs ssF) (g_osr G) && scs_eqb scs (g_scs G)
   && match carry (s_log ssF) (s_know ssF) [] with
      | (knF, [], _) => kn_inclb (g_okn G) knF
      | _ => false
      end
   && log_fp (s_log ssF) (g_fp G))%bool.

Definition seg_sound (G : seg) : Prop :=
  forall E R M rom,
    regs_ok E (g_sr G) R -> know_ok segs E M (g_kn G) -> scs_denot segs M E (g_scs G) ->
    exists R' M',
      msteps segs (mkst R (Z_to_bv 64 (g_pc G)) M rom) (mkst R' (Z_to_bv 64 (g_opc G)) M' rom)
      /\ regs_ok E (g_osr G) R' /\ know_ok segs E M' (g_okn G)
      /\ (forall x, out_fp E (g_fp G) x -> M' x = M x) /\ mem_grows M M'.

Theorem seg_sound_by_check : forall G, seg_check G = true -> seg_sound G.
Proof.
  intros G H E R M rom HR HK Hscs. unfold seg_check, seg_run in H.
  destruct (sym_exec segs (g_fuel G) true (g_stops G) (g_scr G) (SS (g_pc G) (g_sr G) [] (g_kn G) (g_nx G)) [])
    as [[ssF scs] scr'] eqn:Hrun.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply exprs_eqb_eq in H2. apply scs_eqb_eq in H3. subst scs.
  destruct (carry (s_log ssF) (s_know ssF) []) as [[knF scs0] hs] eqn:Hc. destruct scs0; [|discriminate].
  destruct (sym_exec_ex segs (g_fuel G) true (g_stops G) (g_scr G) (SS (g_pc G) (g_sr G) [] (g_kn G) (g_nx G)) [] ssF (g_scs G) scr'
              E M rom (mkst R (Z_to_bv 64 (g_pc G)) M rom) Hrun Hscs
              (st_ok_entry segs E M rom (g_pc G) (g_sr G) (g_kn G) (g_nx G) R HR HK)) as (R' & HR' & Hlf & Hms).
  exists R', (mem_denot E M (s_log ssF)).
  split; [rewrite <- H1; exact Hms|]. split; [rewrite <- H2; exact HR'|]. split.
  - eapply kn_inclb_sound; [exact H4|].
    eapply (carry_sound segs E M M); [exact Hc | exact Hlf | | constructor].
    destruct (sym_exec_sound segs (g_fuel G) true (g_stops G) (g_scr G) (SS (g_pc G) (g_sr G) [] (g_kn G) (g_nx G)) [] ssF (g_scs G) scr'
              E M rom (mkst R (Z_to_bv 64 (g_pc G)) M rom) Hrun Hscs
              (st_ok_entry segs E M rom (g_pc G) (g_sr G) (g_kn G) (g_nx G) R HR HK)) as (ms' & _ & Hst').
    destruct Hst' as (R2 & _ & _ & _ & HKF). exact HKF.
  - split; [| apply mem_denot_grows].
    intros x Hx. eapply mem_denot_out; [exact Hlf | exact H5 | exact Hx].
Qed.

End WithSegs.
End WithFP1.

End SEG.
