(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import PropExec MState Frame Regs6ss RzEqv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Divembc SpinAlg.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tset_tset_same {A} : forall (p : positive) (x y : A) (t : tree A),
  tset p x (tset p y t) = tset p x t.
Proof.
  induction p as [p IH|p IH|]; intros x y [|l v r]; cbn; try rewrite IH; reflexivity.
Qed.

Lemma bvmap_set_set_same : forall (k : reg) (v v' : word) (R : bvmap 5 word),
  bvmap_set k v (bvmap_set k v' R) = bvmap_set k v R.
Proof. intros. unfold bvmap_set. apply tset_tset_same. Qed.

Lemma bvmap_set_id_val : forall (k : reg) (v : word) (R : bvmap 5 word),
  bvmap_set k v R = R -> reg_get R k = v.
Proof.
  intros k v R H. unfold reg_get. rewrite <- H. rewrite bvmap_get_set_same. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rsetT (k : reg) (v : word) (R : bvmap 5 word) : bvmap 5 word :=
  if is_x0 k then R else bvmap_set k v R.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma rsetT_eqv : forall k v R R', xregs_eqv R R' -> xregs_eqv (rsetT k v R) (rsetT k v R').
Proof. intros k v R R' H. unfold rsetT. destruct (is_x0 k); [exact H| apply xregs_eqv_set; exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fcvt_fty (t : fcvt_ty) : option ffmt :=
  match t with FC_S => Some FMT_S | FC_D => Some FMT_D | _ => None end.

Definition gpr_dest (i : instr) : option reg :=
  match i with
  | Lui rd _ | Auipc rd _ | Jal rd _ | Jalr rd _ _ | Load _ _ rd _ _
  | OpImm _ rd _ _ | ShiftImm _ rd _ _ | Op _ rd _ _ | OpImm32 rd _ _ | ShiftImm32 _ rd _ _ | Op32 _ rd _ _
  | Mul _ rd _ _ | Mul32 _ rd _ _ | Lr _ _ _ rd _ | Sc _ _ _ rd _ _ | Amo _ _ _ _ rd _ _
  | Csr _ rd _ _ | CsrI _ rd _ _ | Fcmp _ _ rd _ _ | Fclass _ rd _ => Some rd
  | Fmv FMV_X_F _ rd _ => Some rd
  | Fcvt dst src rd _ _ =>
      match fcvt_fty dst, fcvt_fty src with None, Some _ => Some rd | _, _ => None end
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Park.
  Variables R R' : bvmap 5 word.

  Definition core_rest (c c' : core) : Prop :=
    c_fregs c = c_fregs c' /\ c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

  Definition core_park (ko : option reg) (c c' : core) : Prop :=
    match ko with
    | None => c_regs c = R /\ c_regs c' = R'
    | Some k => exists v, c_regs c = rsetT k v R /\ c_regs c' = rsetT k v R'
    end /\ core_rest c c'.

  Inductive eff_park (ko : option reg) : eff -> eff -> Prop :=
  | PkDone : forall c c', core_park ko c c' -> eff_park ko (EDone c) (EDone c')
  | PkIllegal : forall c c', eff_park ko (EIllegal c) (EIllegal c')
  | PkDefinedIllegal : forall c c', eff_park ko (EDefinedIllegal c) (EDefinedIllegal c')   (* [comment removed for export] *)
  | PkEcall : forall c c', eff_park ko (EEcall c) (EEcall c')
  | PkEbreak : forall c c', eff_park ko (EEbreak c) (EEbreak c')
  | PkFault : forall c c', eff_park ko (EFault c) (EFault c')
  | PkLoad : forall n a k k', (forall v, eff_park ko (k v) (k' v)) -> eff_park ko (ELoad n a k) (ELoad n a k')
  | PkStore : forall n a v k k', eff_park ko k k' -> eff_park ko (EStore n a v k) (EStore n a v k').

  Lemma park_base : forall F pc fc rv, core_park None (Core R F pc fc rv) (Core R' F pc fc rv).
  Proof. intros. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

  Local Ltac ctac :=
    unfold core_park, core_rest, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
           accrue, fwrite, inval_resv, rsetT in *; simpl in *.

  Lemma park_rset : forall k v c c', core_park None c c' -> core_park (Some k) (rset k v c) (rset k v c').
  Proof.
    intros k v [R1 F p f s] [R1' F' p' f' s'] H. ctac. (first [ dand5 H as [-> ->] -> -> -> -> | destruct H as ([-> ->] & -> & -> & -> & ->) ]).
    destruct (is_x0 k); simpl; (split; [exists v; split; reflexivity| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit]).
  Qed.
  Lemma park_fset : forall ko r v c c', core_park ko c c' -> core_park ko (fset r v c) (fset r v c').
  Proof. intros ko r v [R1 F p f s] [R1' F' p' f' s'] H. ctac. (first [ dand5 H as HR -> -> -> -> | destruct H as (HR & -> & -> & -> & ->) ]). split; [exact HR| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit]. Qed.
  Lemma park_with_pc : forall ko v c c', core_park ko c c' -> core_park ko (with_pc v c) (with_pc v c').
  Proof. intros ko v [R1 F p f s] [R1' F' p' f' s'] H. ctac. (first [ dand5 H as HR -> -> -> -> | destruct H as (HR & -> & -> & -> & ->) ]). split; [exact HR| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit]. Qed.
  Lemma park_with_fcsr : forall ko v c c', core_park ko c c' -> core_park ko (with_fcsr v c) (with_fcsr v c').
  Proof. intros ko v [R1 F p f s] [R1' F' p' f' s'] H. ctac. (first [ dand5 H as HR -> -> -> -> | destruct H as (HR & -> & -> & -> & ->) ]). split; [exact HR| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit]. Qed.
  Lemma park_with_resv : forall ko v c c', core_park ko c c' -> core_park ko (with_resv v c) (with_resv v c').
  Proof. intros ko v [R1 F p f s] [R1' F' p' f' s'] H. ctac. (first [ dand5 H as HR -> -> -> -> | destruct H as (HR & -> & -> & -> & ->) ]). split; [exact HR| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit]. Qed.
  Lemma park_accrue : forall ko fl c c', core_park ko c c' -> core_park ko (accrue fl c) (accrue fl c').
  Proof. intros ko fl [R1 F p f s] [R1' F' p' f' s'] H. ctac. (first [ dand5 H as HR -> -> -> -> | destruct H as (HR & -> & -> & -> & ->) ]). split; [exact HR| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit]. Qed.
  Lemma park_fwrite : forall ko fmt r v c c', core_park ko c c' -> core_park ko (fwrite fmt r v c) (fwrite fmt r v c').
  Proof.
    intros ko fmt r v [R1 F p f s] [R1' F' p' f' s'] H. ctac. (first [ dand5 H as HR -> -> -> -> | destruct H as (HR & -> & -> & -> & ->) ]).
    destruct fmt; simpl; (split; [exact HR| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit]).
  Qed.
  Lemma park_inval_resv : forall ko a c c', core_park ko c c' -> core_park ko (inval_resv a c) (inval_resv a c').
  Proof.
    intros ko a [R1 F p f s] [R1' F' p' f' s'] H. ctac. (first [ dand5 H as HR -> -> -> -> | destruct H as (HR & -> & -> & -> & ->) ]).
    destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; (split; [exact HR| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit]).
  Qed.
  Lemma park_if : forall ko (b : bool) c1 c1' c2 c2',
    core_park ko c1 c1' -> core_park ko c2 c2' -> core_park ko (if b then c1 else c2) (if b then c1' else c2').
  Proof. intros ko [] c1 c1' c2 c2' H1 H2; assumption. Qed.

  (* [comment removed for export] *)
  Local Ltac solve_core :=
    repeat first [ apply park_rset | apply park_fset | apply park_with_pc
                 | apply park_with_fcsr | apply park_with_resv | apply park_accrue
                 | apply park_fwrite | apply park_inval_resv | apply park_if
                 | match goal with |- core_park _ (match ?X with _ => _ end) _ => destruct X end ];
    apply park_base.

  Local Ltac park_struct :=
    repeat first
      [ apply PkDone; solve_core
      | apply PkIllegal | apply PkDefinedIllegal | apply PkEcall | apply PkEbreak | apply PkFault
      | apply PkLoad; intros ?
      | apply PkStore
      | match goal with |- eff_park _ (match ?X with _ => _ end) _ => destruct X end
      | match goal with |- eff_park _ (match ?X with _ => _ end _) _ => destruct X end ].

  Local Ltac unfold_exec :=
    cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                              with_pc load_val store_val exec_csr resolve_rm frm_of gpr_dest fcvt_fty].

  (* [comment removed for export] *)
  Lemma exec_park : forall F pc fc rv sz i,
    xregs_eqv R R' ->
    eff_park (gpr_dest i) (exec sz i (Core R F pc fc rv)) (exec sz i (Core R' F pc fc rv)).
  Proof.
    intros F pc fc rv sz i HR.
    pose proof (rget_eqv R R' F pc fc rv HR) as HG.
    destruct i; unfold_exec; rewrite ?HG; park_struct.
  Qed.
End Park.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition osetT (ko : option reg) (v : word) (R : bvmap 5 word) : bvmap 5 word :=
  match ko with None => R | Some k => rsetT k v R end.

(* [comment removed for export] *)
Lemma osetT_eqv : forall ko v R R', xregs_eqv R R' -> xregs_eqv (osetT ko v R) (osetT ko v R').
Proof. intros [k|] v R R' H; cbn; [apply rsetT_eqv; exact H| exact H]. Qed.
(* [comment removed for export] *)
Lemma osetT_fix : forall ko v v' R R', osetT ko v R = R -> osetT ko v' R = R -> osetT ko v' (osetT ko v R') = osetT ko v R'.
Proof.
  intros [k|] v v' R R' H1 H2; cbn in *; [|reflexivity].
  unfold rsetT in *. destruct (is_x0 k) eqn:Hk; [reflexivity|].
  rewrite <- (bvmap_set_id_val k v R H1), (bvmap_set_id_val k v' R H2). apply bvmap_set_set_same.
Qed.

Definition dest_of_word (w : bv 32) : option reg :=
  if is_ecall w then None else match decode_any w with Some (i, _) => gpr_dest i | None => None end.

(* [comment removed for export] *)
Definition ms_rest_eq (a b : machine_state) : Prop :=
  ms_fregs a = ms_fregs b /\ ms_pc_val a = ms_pc_val b /\ ms_svc_pending a = ms_svc_pending b /\
  ms_resv a = ms_resv b /\ ms_fcsr a = ms_fcsr b /\ ms_mem a = ms_mem b /\ ms_rom a = ms_rom b.

(* [comment removed for export] *)
Lemma ms_eq_of_parts : forall a b, ms_regs a = ms_regs b -> ms_rest_eq a b -> a = b.
Proof.
  (intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro'] HR; (first [ intro dR_26; dand7 dR_26 as H1 H2 H3 H4 H5 H6 H7 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) ])); cbn in *; subst; reflexivity.
Qed.

Definition rep_park (R R' : bvmap 5 word) (ko : option reg) (r r' : machine_result (access_report machine_state)) : Prop :=
  match r, r' with
  | MachineOk a, MachineOk b =>
      (exists v, ms_regs (@access_value _ a) = osetT ko v R /\ ms_regs (@access_value _ b) = osetT ko v R')
      /\ ms_rest_eq (@access_value _ a) (@access_value _ b)
      /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_park : forall R R' ko t t', eff_park R R' ko t t' -> forall m,
  match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
  | MachineOk a, MachineOk b =>
      core_park R R' ko (fst (@access_value _ a)) (fst (@access_value _ b))
      /\ snd (@access_value _ a) = snd (@access_value _ b)
      /\ @accessed_ranges _ a = @accessed_ranges _ b
  | MachineFault, MachineFault => True
  | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros R R' ko t t' H. induction H; intros m; cbn [interp_eff_accesses]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [ra| |]; destruct (interp_eff_accesses segs (k' _) m) as [rb| |];
      cbn [access_value accessed_ranges] in *; try exact H0; try contradiction.
    (first [ dand3 H0 as C S -> | destruct H0 as (C & S & ->) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try apply C; exact S.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_park (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [ra| |]; destruct (interp_eff_accesses segs k' _) as [rb| |];
      cbn [access_value accessed_ranges] in *; try exact IHeff_park; try contradiction.
    (first [ dand3 IHeff_park as C S -> | destruct IHeff_park as (C & S & ->) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try apply C; exact S.
Qed.

Lemma decode_exec_park : forall ms ms' w, ms_eqv ms ms' ->
  rep_park (ms_regs ms) (ms_regs ms') (dest_of_word w) (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
  intros ms ms' w Heqv. pose proof (ms_reg_eqv ms ms' 17 Heqv) as H17.
  destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
  (first [ dand8 Heqv as HR HF Hpc Hsvc Hrv Hfc Hm Hro | destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro) ]); simpl in *; subst.
  unfold decode_exec_accesses, dest_of_word. destruct (is_ecall w).
  - simpl. rewrite H17. split; [exists w0; split; reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
    pose proof (interp_park R R' (gpr_dest i) _ _ (exec_park R R' F' pc' fc' rv' (Z_to_bv 64 isz) i HR) m') as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F' pc' fc' rv')) m') as [[[c m1] acc]| |];
    destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc']| |];
    simpl in *; try exact K; try contradiction.
    (first [ dand3 K as [HRR (H2 & H3 & H4 & H5)] -> -> | destruct K as ([HRR (H2 & H3 & H4 & H5)] & -> & ->) ]). split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; simpl; auto].
    destruct (gpr_dest i) as [k|]; cbn [osetT].
    + (first [ dex1 HRR as v; destruct HRR as [E1 E2] | dand3 HRR as v E1 E2 | destruct HRR as (v & E1 & E2) ]). exists v. simpl. split; assumption.
    + destruct HRR as [E1 E2]. exists w0. simpl. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma step_park : forall ms, exists ko, forall ms', ms_eqv ms ms' ->
  rep_park (ms_regs ms) (ms_regs ms') ko (RiscvSemantics.step_accesses segs ms) (RiscvSemantics.step_accesses segs ms').
Proof.
  intros ms. unfold RiscvSemantics.step_accesses, ms_pc.
  destruct (fetch_word segs (ms_pc_val ms)) as [w|] eqn:F1.
  { exists (dest_of_word w). intros ms' Heqv. (first [ pose proof (Heqv) as dR_14; dand8 dR_14 as _ _ Hpc _ _ _ Hm _ | pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _) ]).
    rewrite <- Hpc, F1. apply decode_exec_park. exact Heqv. }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)) as [w|] eqn:F2.
  { exists (dest_of_word w). intros ms' Heqv. (first [ pose proof (Heqv) as dR_15; dand8 dR_15 as _ _ Hpc _ _ _ Hm _ | pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _) ]).
    rewrite <- Hpc, <- Hm, F1, F2. apply decode_exec_park. exact Heqv. }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)) as [w|] eqn:F3.
  { exists (dest_of_word w). intros ms' Heqv. (first [ pose proof (Heqv) as dR_16; dand8 dR_16 as _ _ Hpc _ _ _ Hm _ | pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _) ]).
    rewrite <- Hpc, <- Hm, F1, F2, F3. apply decode_exec_park. exact Heqv. }
  exists None. intros ms' Heqv. (first [ pose proof (Heqv) as dR_17; dand8 dR_17 as _ _ Hpc _ _ _ Hm _ | pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _) ]).
  rewrite <- Hpc, <- Hm, F1, F2, F3.
  unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

(* [comment removed for export] *)
Lemma acct_park : forall ms md, exists ko, forall ms' ms1 md1, ms_eqv ms ms' ->
  mi_account_step segs ms md = MachineOk (ms1, md1) ->
  exists ms1', mi_account_step segs ms' md = MachineOk (ms1', md1)
    /\ (exists v, ms_regs ms1 = osetT ko v (ms_regs ms) /\ ms_regs ms1' = osetT ko v (ms_regs ms'))
    /\ ms_rest_eq ms1 ms1'.
Proof.
  intros ms md. destruct (step_park ms) as [ko K]. exists ko. intros ms' ms1 md1 Heqv HA.
  specialize (K ms' Heqv). unfold mi_account_step in *.
  destruct (RiscvSemantics.step_accesses segs ms) as [[msa acc]| |]; try discriminate.
  destruct (RiscvSemantics.step_accesses segs ms') as [[msb acc']| |]; cbn in K; try contradiction.
  (first [ dand3 K as V RE <- | destruct K as (V & RE & <-) ]). cbn [access_value accessed_ranges] in *.
  destruct (materialize_model_accesses md acc) as [md'|]; [|discriminate].
  injection HA as <- <-. exists msb. split; [reflexivity|]. split; [exact V| exact RE].
Qed.

Lemma ms_rest_eq_trans : forall a b c, ms_rest_eq a b -> ms_rest_eq b c -> ms_rest_eq a c.
Proof. intros a b c (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence. Qed.
Lemma ms_rest_eq_sym : forall a b, ms_rest_eq a b -> ms_rest_eq b a.
Proof. intros a b (?&?&?&?&?&?&?). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma to_spin_of_fix : forall ms ms' md,
  ms_eqv ms ms' -> ms_svc_pending ms = None ->
  mi_account_step segs ms md = MachineOk (ms, md) -> to_spin segs ms' md.
Proof.
  intros ms ms' md Heqv Hsvc FIX.
  destruct (acct_park ms md) as [ko K].
  (first [ pose proof ((K ms' ms md Heqv FIX)) as dR_19; dex1 dR_19 as ms1'; dand3 dR_19 as A1 (v & E1 & E2) RE1 | pose proof ((K ms' ms md Heqv FIX)) as dR_19; dand4 dR_19 as ms1' A1 (v & E1 & E2) RE1 | destruct (K ms' ms md Heqv FIX) as (ms1' & A1 & (v & E1 & E2) & RE1) ]).
  pose proof Heqv as (HR & REST).
  assert (Hsvc' : ms_svc_pending ms' = None) by ((first [ dand4 REST as _ _ Hs _ | destruct REST as (_ & _ & Hs & _) ]); congruence).
  (* [comment removed for export] *)
  assert (Heqv1 : ms_eqv ms ms1').
  { split; [| exact RE1]. rewrite E1, E2. apply osetT_eqv. exact HR. }
  (first [ pose proof ((K ms1' ms md Heqv1 FIX)) as dR_21; dex1 dR_21 as ms2'; dand3 dR_21 as A2 (v2 & E1' & E2') RE2 | pose proof ((K ms1' ms md Heqv1 FIX)) as dR_21; dand4 dR_21 as ms2' A2 (v2 & E1' & E2') RE2 | destruct (K ms1' ms md Heqv1 FIX) as (ms2' & A2 & (v2 & E1' & E2') & RE2) ]).
  assert (FIX1 : ms2' = ms1').
  { apply ms_eq_of_parts.
    - rewrite E2', E2. apply (osetT_fix ko v v2 (ms_regs ms)); symmetry; assumption.
    - apply (ms_rest_eq_trans ms2' ms ms1'); [apply ms_rest_eq_sym; exact RE2| exact RE1]. }
  rewrite FIX1 in A2.
  apply (ts_step segs ms' md ms1' md Hsvc' A1).
  apply (ts_spin segs ms1' md); [| exact A2].
  (first [ dand4 RE1 as _ _ Hs _ | destruct RE1 as (_ & _ & Hs & _) ]). congruence.
Qed.

Theorem to_spin_eqv : forall ms md, to_spin segs ms md -> forall ms', ms_eqv ms ms' -> to_spin segs ms' md.
Proof.
  intros ms md H. induction H as [ms md Hsvc FIX | ms md ms1 md1 Hsvc HA Hspin IH]; intros ms' Heqv.
  - exact (to_spin_of_fix ms ms' md Heqv Hsvc FIX).
  - destruct (acct_park ms md) as [ko K].
    (first [ pose proof ((K ms' ms1 md1 Heqv HA)) as dR_23; dex1 dR_23 as ms1'; dand3 dR_23 as A1 (v & E1 & E2) RE1 | pose proof ((K ms' ms1 md1 Heqv HA)) as dR_23; dand4 dR_23 as ms1' A1 (v & E1 & E2) RE1 | destruct (K ms' ms1 md1 Heqv HA) as (ms1' & A1 & (v & E1 & E2) & RE1) ]).
    assert (Hsvc' : ms_svc_pending ms' = None) by ((first [ dand5 Heqv as _ _ _ Hs _ | destruct Heqv as (_ & _ & _ & Hs & _) ]); congruence).
    apply (ts_step segs ms' md ms1' md1 Hsvc' A1). apply IH.
    split; [| exact RE1]. rewrite E1, E2. apply osetT_eqv. exact (proj1 Heqv).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem srealizes_eqv : forall c T, srealizes segs c T ->
  forall c', cfg_eqv c c' -> srealizes segs c' T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq]; intros c' Heqv.
  - destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [Hms Hmo]; cbn in Hms, Hmo. subst mo'.
    destruct Hnode as [Hn1 Hn2].
    apply (srz_node segs (mkCfg ms' mo) I evs (fun i => xport_cfg segs ms ms' (nx i)) T i0).
    + split.
      * intros i. exact (proj1 (sstep_xport segs ms ms' mo (evs i) (SNext (nx i)) Hms (Hn1 i))).
      * intros e st Hst'.
        destruct (sstep_xport segs ms' ms mo e st (ms_eqv_sym _ _ Hms) Hst') as [S _].
        (first [ pose proof ((Hn2 e (xport segs ms' ms st) S)) as dR_25; dex1 dR_25 as i; destruct dR_25 as [-> Hx] | pose proof ((Hn2 e (xport segs ms' ms st) S)) as dR_25; dand3 dR_25 as i -> Hx | destruct (Hn2 e (xport segs ms' ms st) S) as (i & -> & Hx) ]).
        exists i. split; [reflexivity|].
        rewrite <- (xport_round_trip segs ms ms' mo (evs i) st Hms Hst'). rewrite Hx. reflexivity.
    + intros i. apply (IH i).
      exact (proj2 (sstep_xport segs ms ms' mo (evs i) (SNext (nx i)) Hms (Hn1 i))).
  - apply srz_halt. destruct Heqv as [_ <-]. exact Hh.
  - destruct Hspin as [[] _].   (* [comment removed for export] *)
  - eapply srz_conseq; [apply IH; exact Heqv| exact Heq].
Qed.

Corollary srealizes_ms_eqv : forall ms ms' mo T,
  ms_eqv ms ms' -> srealizes segs (mkCfg ms mo) T -> srealizes segs (mkCfg ms' mo) T.
Proof. intros ms ms' mo T Heqv H. apply (srealizes_eqv _ T H). split; [exact Heqv| reflexivity]. Qed.

(* [comment removed for export] *)
Theorem srealizes_of_mkR : forall (R F : bvmap 5 word) pc fc rv m rom mo T
    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  PropExec.getr R 1 = x1 -> PropExec.getr R 2 = x2 -> PropExec.getr R 3 = x3 -> PropExec.getr R 4 = x4 ->
  PropExec.getr R 5 = x5 -> PropExec.getr R 6 = x6 -> PropExec.getr R 7 = x7 -> PropExec.getr R 8 = x8 ->
  PropExec.getr R 9 = x9 -> PropExec.getr R 10 = x10 -> PropExec.getr R 11 = x11 -> PropExec.getr R 12 = x12 ->
  PropExec.getr R 13 = x13 -> PropExec.getr R 14 = x14 -> PropExec.getr R 15 = x15 -> PropExec.getr R 16 = x16 ->
  PropExec.getr R 17 = x17 -> PropExec.getr R 18 = x18 -> PropExec.getr R 19 = x19 -> PropExec.getr R 20 = x20 ->
  PropExec.getr R 21 = x21 -> PropExec.getr R 22 = x22 -> PropExec.getr R 23 = x23 -> PropExec.getr R 24 = x24 ->
  PropExec.getr R 25 = x25 -> PropExec.getr R 26 = x26 -> PropExec.getr R 27 = x27 -> PropExec.getr R 28 = x28 ->
  PropExec.getr R 29 = x29 -> PropExec.getr R 30 = x30 -> PropExec.getr R 31 = x31 ->
  srealizes segs (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                                x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom) mo) T ->
  srealizes segs (mkCfg (MS R F pc fc rv m rom) mo) T.
Proof.
  intros. eapply srealizes_ms_eqv; [| eassumption].
  split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit].
  apply xregs_eqv_sym. apply mkR_eqv_of; rewrite <- RzEqv.getr_reg_get by reflexivity; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithSegs.
