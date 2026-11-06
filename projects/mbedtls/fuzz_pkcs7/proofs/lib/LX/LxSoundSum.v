(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec CellsX Arr HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxSum LxStep LxRun LxDenot LxSoundExpr LxSoundDec LxSoundMem LxSoundStep LxSoundRun.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zforall (n : nat) (k : list Z -> Prop) : Prop :=
  match n with O => k [] | S n' => forall x : Z, zforall n' (fun l => k (x :: l)) end.
Fixpoint zexists (n : nat) (k : list Z -> Prop) : Prop :=
  match n with O => k [] | S n' => exists x : Z, zexists n' (fun l => k (x :: l)) end.
Fixpoint bforall (n : nat) (k : list (list byte) -> Prop) : Prop :=
  match n with O => k [] | S n' => forall x : list byte, bforall n' (fun l => k (x :: l)) end.
Fixpoint wforall (n : nat) (k : list word -> Prop) : Prop :=
  match n with O => k [] | S n' => forall x : word, wforall n' (fun l => k (x :: l)) end.
(* [comment removed for export] *)
Fixpoint lforall (n : nat) (k : list (list word) -> Prop) : Prop :=
  match n with O => k [] | S n' => forall x : list word, lforall n' (fun l => k (x :: l)) end.
Fixpoint lexists (n : nat) (k : list (list word) -> Prop) : Prop :=
  match n with O => k [] | S n' => exists x : list word, lexists n' (fun l => k (x :: l)) end.
Lemma lforall_apply : forall n k l, lforall n k -> length l = n -> k l.
Proof.
  induction n as [|n IH]; intros k [|x l] H Hl; cbn in Hl |- *; try discriminate; [exact H|].
  apply (IH (fun l' => k (x :: l'))); [apply H| lia].
Qed.
Lemma lexists_elim : forall n k, lexists n k -> exists l, length l = n /\ k l.
Proof.
  induction n as [|n IH]; intros k H; cbn in H.
  - exists []. split; [reflexivity| exact H].
  - destruct H as [x H]. destruct (IH _ H) as (l & Hl & Hk). exists (x :: l). split; [cbn; lia| exact Hk].
Qed.

Lemma zforall_apply : forall n k l, zforall n k -> length l = n -> k l.
Proof.
  induction n as [|n IH]; intros k [|x l] H Hl; cbn in Hl |- *; try discriminate; [exact H|].
  apply (IH (fun l' => k (x :: l'))); [apply H| lia].
Qed.
Lemma bforall_apply : forall n k l, bforall n k -> length l = n -> k l.
Proof.
  induction n as [|n IH]; intros k [|x l] H Hl; cbn in Hl |- *; try discriminate; [exact H|].
  apply (IH (fun l' => k (x :: l'))); [apply H| lia].
Qed.
Lemma wforall_apply : forall n k l, wforall n k -> length l = n -> k l.
Proof.
  induction n as [|n IH]; intros k [|x l] H Hl; cbn in Hl |- *; try discriminate; [exact H|].
  apply (IH (fun l' => k (x :: l'))); [apply H| lia].
Qed.
Lemma zexists_elim : forall n k, zexists n k -> exists l, length l = n /\ k l.
Proof.
  induction n as [|n IH]; intros k H; cbn in H.
  - exists []. split; [reflexivity| exact H].
  - destruct H as [x H]. destruct (IH _ H) as (l & Hl & Hk). exists (x :: l). split; [cbn; lia| exact Hk].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rgetZ (R : list word) (r : Z) : word :=
  match r with Zpos p => pget R p (Z_to_bv 64 0) | _ => Z_to_bv 64 0 end.
Definition rsetZ (R : list word) (r : Z) (v : word) : list word :=
  match r with Zpos p => pset R p v (Z_to_bv 64 0) | _ => R end.

(* [comment removed for export] *)
Fixpoint rclob (R : list word) (cl : list (Z * positive)) (E : env) : list word :=
  match cl with
  | [] => R
  | (r, j) :: cl' => rclob (rsetZ R r (Z_to_bv 64 (ez E j))) cl' E
  end.

(* [comment removed for export] *)
Fixpoint rb_tele (R : list word) (E : env) (rb : list (Z * positive)) (P : Prop) : Prop :=
  match rb with
  | [] => P
  | (r, i) :: rb' => rgetZ R r = Z_to_bv 64 (ez E i) -> rb_tele R E rb' P
  end.

(* [comment removed for export] *)
Fixpoint gb_tele (E : env) (GS : list Z) (gb : list (positive * nat)) (P : Prop) : Prop :=
  match gb with
  | [] => P
  | (i, n) :: gb' => ez E i = nth n GS 0 -> gb_tele E GS gb' P
  end.

(* [comment removed for export] *)
Definition bb_facts (bb : list (positive * positive * positive)) : list mfact :=
  map (fun b => match b with (ia, il, kb) => MBy (EZv ia) (EZv il) kb end) bb.

(* [comment removed for export] *)
Fixpoint pf_conj (CS : Z -> Prop) (E : env) (pf : list pfact) (P : Prop) : Prop :=
  match pf with [] => P | f :: pf' => pfact_ok CS E f /\ pf_conj CS E pf' P end.
Fixpoint mf_conj (segs : list Segment) (L : asan_layout) (CS : Z -> Prop) (E : env) (m : mem) (mf : list mfact) (P : Prop) : Prop :=
  match mf with [] => P | f :: mf' => mfact_ok segs L CS E m f /\ mf_conj segs L CS E m mf' P end.

(* [comment removed for export] *)
Fixpoint oq_tele (OPS : list (mem -> Prop)) (m : mem) (ks : list nat) (P : Prop) : Prop :=
  match ks with [] => P | k :: ks' => nth k OPS (fun _ => True) m -> oq_tele OPS m ks' P end.
Fixpoint oq_conj (OPS : list (mem -> Prop)) (m : mem) (ks : list nat) (P : Prop) : Prop :=
  match ks with [] => P | k :: ks' => nth k OPS (fun _ => True) m /\ oq_conj OPS m ks' P end.

(* [comment removed for export] *)
Lemma zforall_intro : forall n k, (forall l, length l = n -> k l) -> zforall n k.
Proof.
  induction n as [|n IH]; intros k H; cbn; [apply H; reflexivity|].
  intros x. apply IH. intros l Hl. apply H. cbn. rewrite Hl. reflexivity.
Qed.
Lemma lforall_intro : forall n k, (forall l, length l = n -> k l) -> lforall n k.
Proof.
  induction n as [|n IH]; intros k H; cbn; [apply H; reflexivity|].
  intros x. apply IH. intros l Hl. apply H. cbn. rewrite Hl. reflexivity.
Qed.
Lemma oq_tele_intro : forall OQ mm ks P, ((forall k, In k ks -> nth k OQ (fun _ => True) mm) -> P) -> oq_tele OQ mm ks P.
Proof.
  intros OQ mm ks P. induction ks as [|k ks IH]; cbn; intros H; [apply H; intros k []|].
  intros Hk. apply IH. intros H'. apply H. intros k' [<-|Hin]; [exact Hk| apply H'; exact Hin].
Qed.
Lemma mf_tele_intro : forall segs G E mm mf P, (Forall (mfact_ok segs (g_L G) (g_CS G) E mm) mf -> P) -> mf_tele segs G E mm mf P.
Proof.
  intros segs G E mm mf P. induction mf as [|f mf IH]; cbn; intros H; [apply H; constructor|].
  intros Hf. apply IH. intros H'. apply H. constructor; [exact Hf| exact H'].
Qed.
Lemma pf_tele_intro : forall G E pf P, (Forall (pfact_ok (g_CS G) E) pf -> P) -> pf_tele G E pf P.
Proof.
  intros G E pf P. induction pf as [|f pf IH]; cbn; intros H; [apply H; constructor|].
  intros Hf. apply IH. intros H'. apply H. constructor; [exact Hf| exact H'].
Qed.

Section Valid.
  Variable segs : list Segment.
  Variable AL : asan_layout.
  Variable GS : list Z.               (* [comment removed for export] *)
  Variable OPS : list (mem -> Prop).  (* [comment removed for export] *)
  Variable LAWS : list (list (Z * Z) -> mem -> mem -> Prop).  (* [comment removed for export] *)
  Variable PROPS : list (list Z -> Prop).  (* [comment removed for export] *)
  Variable su : summary.

  (* [comment removed for export] *)
  Definition sum_frame (law : option nat) (X : list (Z * Z)) (m m' : mem) : Prop :=
    match law with
    | None => munch X m m' /\ wmono segs m m' /\ mem_inv segs m'
    | Some l => nth l LAWS (fun _ _ _ => True) X m m' /\ mem_inv segs m'
    end.

  Definition sum_postP (CS : Z -> Prop) (F : bvmap 5 word) (fc : bv 32) (m : mem)
             (ps : list Z) (bss : list (list byte)) (lss : list (list word)) (R : list word) : machine_state -> Prop :=
    fun ms' => zexists (su_nr su) (fun rs => lexists (su_nrl su) (fun rls =>
      let E' := ENV (ps ++ rs) [] bss OPS (lss ++ rls) [] LAWS PROPS [] lx_nohp lx_nocw [] lx_nomodel [] [] in
      exists m' : mem,
        ms' = MS (rdw (rclob R (su_clob su) E')) F (ret_pc (rgetZ R 1)) fc None m' (seg_rom segs)
        /\ mf_conj segs AL CS E' m' (su_mpost su)
             (pf_conj CS E' (su_post su)
                (oq_conj OPS m' (su_oreq su)
                   (sum_frame (su_law su) (wden E' (su_W su)) m m'))))).

  (* [comment removed for export] *)
  Definition sum_valid_at (CS : Z -> Prop) (ps : list Z) (bss : list (list byte)) (lss : list (list word)) : Prop :=
      forall (F : bvmap 5 word) (fc : bv 32) (m : mem),
      wforall 31 (fun R =>
        let E := ENV ps [] bss OPS lss [] LAWS PROPS [] lx_nohp lx_nocw [] lx_nomodel [] [] in
        let G := GL AL CS F fc m m in
        (if su_acc su then cs_ok AL CS /\ al_wf AL else (forall x, CS x)) ->
        match su_sb su with Some i => ez E i = al_sb AL | None => True end ->
        mem_inv segs m ->
        gb_tele E GS (su_gbind su)
        (rb_tele R E (su_rbind su)
          (match su_stk su with Some (ilo, ihi) => stk segs m (ez E ilo) (ez E ihi) | None => True end ->
           mf_tele segs G E m (su_mbind su ++ bb_facts (su_bbind su) ++ su_req su)
             (pf_tele G E (su_pre su)
                (oq_tele OPS m (su_oreq su)
                   (evtA segs AL CS (sum_postP CS F fc m ps bss lss R)
                      (MS (rdw R) F (Z_to_bv 64 (su_pc su)) fc None m (seg_rom segs)))))))).

  (* [comment removed for export] *)
  Definition summary_validP (CS : Z -> Prop) : Prop :=
    match su_heap su with
    | None => zforall (su_np su) (fun ps => bforall (su_nb su) (fun bss => lforall (su_nl su) (fun lss => sum_valid_at CS ps bss lss)))
    | Some _ => False
    end.
  (* [comment removed for export] *)
  Definition summary_validG1 : Prop :=
    match su_heap su with
    | None => zforall (su_np su) (fun ps => bforall (su_nb su) (fun bss => lforall (su_nl su) (fun lss => forall CS : Z -> Prop, sum_valid_at CS ps bss lss)))
    | Some _ => False
    end.
End Valid.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ValidH.
  Variable segs : list Segment.
  Variable AL : asan_layout.
  Variable GS : list Z.
  Variable OPS : list (mem -> Prop).
  Variable LAWS : list (list (Z * Z) -> mem -> mem -> Prop).
  Variable PROPS : list (list Z -> Prop).
  Variable LB0 : lx_blks.             (* [comment removed for export] *)
  Variable HP : lx_hpred.             (* [comment removed for export] *)
  Variable CW : lx_cwpred.            (* [comment removed for export] *)
  Variable LH : lx_hlaws.             (* [comment removed for export] *)
  Variable HRS : lx_hress.            (* [comment removed for export] *)
  Variable TGT : Model -> machine_state -> Prop.   (* [comment removed for export] *)
  Variable su : summary.
  Variable hc : heapcall.

  (* [comment removed for export] *)
  Definition eff_list (E : env) (eff : bleff) (LB : list (Z * Z)) : list (Z * Z) :=
    match eff with
    | BENone => LB
    | BECons ja en => (ez E ja, zdenp E en) :: LB
    | BEPop ja => lb_remove (ez E ja) LB
    | BEOpq => eblv E 1
    end.
  Definition law_list (E : env) (eff : bleff) (LB : list (Z * Z)) : list (Z * Z) :=
    match eff with BEPop ja => lb_remove (ez E ja) LB | _ => LB end.
  (* [comment removed for export] *)
  Definition eff_pre (E : env) (eff : bleff) (LB : list (Z * Z)) : Prop :=
    match eff with BEPop ja => exists n, In (ez E ja, n) LB | _ => True end.
  (* [comment removed for export] *)
  Definition eff_post (E : env) (eff : bleff) (LB : list (Z * Z)) : Prop :=
    match eff with
    | BECons ja en =>
        (forall b k, In (b, k) LB -> ez E ja + zdenp E en <= b \/ b + k <= ez E ja)
        /\ match hc_obj hc with
           | Some j => forall b k, eprop E j [b; k] -> k = 0 \/ ez E ja + zdenp E en <= b \/ b + k <= ez E ja
           | None => True
           end
    | BEOpq => forall b, In b LB -> In b (eblv E 1)
    | _ => True
    end.
  (* [comment removed for export] *)
  Definition blforall (eff : bleff) (LB : list (Z * Z)) (k : list (list (Z * Z)) -> Prop) : Prop :=
    match eff with BEOpq => forall LB' : list (Z * Z), k [LB; LB'] | _ => k [LB] end.

  (* [comment removed for export] *)
  Fixpoint hr_tele (E : env) (m : mem) (LB LBN : list (Z * Z)) (hp : list (nat * list expr)) (P : Prop) : Prop :=
    match hp with
    | [] => P
    | (j, xs) :: hp' => lx_hres segs CW LB0 (nth j HRS hres_d) LB LBN (map (zdenp E) xs) [] m -> hr_tele E m LB LBN hp' P
    end.
  (* [comment removed for export] *)
  Definition heap_caseK (CS : Z -> Prop) (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list (Z * Z))
      (ps : list Z) (bss : list (list byte)) (lss : list (list word)) (R : list word)
      (post : list pfact) (mpost : list mfact) (eff : bleff) (hposts : list (nat * list expr)) : Prop :=
    zforall (su_nr su) (fun rs => lforall (su_nrl su) (fun rls => forall (m' : mem) (mo' : Model), blforall eff LB (fun lbs =>
      let E := ENV ps [] bss OPS lss [] LAWS PROPS LB0 HP CW LH mo' lbs HRS in
      let E' := ENV (ps ++ rs) [] bss OPS (lss ++ rls) [] LAWS PROPS LB0 HP CW LH mo' lbs HRS in
      let G' := GL AL CS F fc m m' in
      mf_tele segs G' E' m' mpost
        (pf_tele G' E' post
           (oq_tele OPS m' (su_oreq su)
             (hr_tele E' m' LB (eff_list E' eff LB) hposts
              (HP (eff_list E' eff LB) m' mo' ->
               eff_post E' eff LB ->
               nth (hc_law hc) LH lx_hlawd (law_list E' eff LB) (ez E (hc_sp hc)) (wden E' (su_W su)) m m' ->
               mem_inv segs m' ->
               TGT mo' (MS (rdw (rclob R (su_clob su) E')) F (ret_pc (rgetZ R 1)) fc None m' (seg_rom segs))))))))).

  Definition sum_validH_at (CS : Z -> Prop) (ps : list Z) (bss : list (list byte)) (lss : list (list word)) : Prop :=
      forall (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (LB : list (Z * Z)),
      wforall 31 (fun R =>
        let E := ENV ps [] bss OPS lss [] LAWS PROPS LB0 HP CW LH mo [LB] HRS in
        let G := GL AL CS F fc m m in
        (if su_acc su then cs_ok AL CS /\ al_wf AL else (forall x, CS x)) ->
        match su_sb su with Some i => ez E i = al_sb AL | None => True end ->
        mem_inv segs m ->
        gb_tele E GS (su_gbind su)
        (rb_tele R E (su_rbind su)
          (match su_stk su with Some (ilo, ihi) => stk segs m (ez E ilo) (ez E ihi) | None => True end ->
           mf_tele segs G E m (su_mbind su ++ bb_facts (su_bbind su) ++ su_req su)
             (pf_tele G E (su_pre su)
                (oq_tele OPS m (su_oreq su)
                   ((forall b, In b LB0 -> In b LB) ->
                    HP LB m mo ->
                    eff_pre E (hc_eff hc) LB ->
                    heap_caseK CS F fc m LB ps bss lss R (su_post su) (su_mpost su) (hc_eff hc) (hc_hpost hc) ->
                    match hc_alt hc with
                    | Some (post2, mpost2, eff2) => heap_caseK CS F fc m LB ps bss lss R post2 mpost2 eff2 []
                    | None => True
                    end ->
                    TGT mo (MS (rdw R) F (Z_to_bv 64 (su_pc su)) fc None m (seg_rom segs)))))))).

  (* [comment removed for export] *)
  Definition summary_validHR (CS : Z -> Prop) : Prop :=
    su_heap su = Some hc /\
    zforall (su_np su) (fun ps => bforall (su_nb su) (fun bss => lforall (su_nl su) (fun lss => sum_validH_at CS ps bss lss))).

  Lemma hr_tele_intro : forall E mm LB LBN hp P,
    ((forall jx, In jx hp -> lx_hres segs CW LB0 (nth (fst jx) HRS hres_d) LB LBN (map (zdenp E) (snd jx)) [] mm) -> P) -> hr_tele E mm LB LBN hp P.
  Proof.
    intros E mm LB LBN hp P. induction hp as [|[j xs] hp IH]; cbn; intros H; [apply H; intros jx []|].
    intros Hj. apply IH. intros H'. apply H. intros jx [<-|Hin]; [exact Hj| apply H'; exact Hin].
  Qed.
  Definition bl_lbs (eff : bleff) (LB lbx : list (Z * Z)) : list (list (Z * Z)) :=
    match eff with BEOpq => [LB; lbx] | _ => [LB] end.
  Lemma blforall_intro : forall eff LB (k : list (list (Z * Z)) -> Prop), (forall lbx, k (bl_lbs eff LB lbx)) -> blforall eff LB k.
  Proof. intros eff LB k H. destruct eff; cbn; try (intros; apply H). all: apply (H []). Qed.
End ValidH.
(* [comment removed for export] *)
Definition summary_validH (segs : list Segment) (AL : asan_layout) (GS : list Z) (OPS : list (mem -> Prop))
    (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)) (PROPS : list (list Z -> Prop))
    (LB0 : lx_blks) (HP : lx_hpred) (CW : lx_cwpred) (LH : lx_hlaws) (TGT : Model -> machine_state -> Prop)
    (su : summary) (hc : heapcall) (CS : Z -> Prop) : Prop :=
  summary_validHR segs AL GS OPS LAWS PROPS LB0 HP CW LH [] TGT su hc CS.

(* [comment removed for export] *)
Definition summary_validL (segs : list Segment) (AL : asan_layout) (GS : list Z) (OPS : list (mem -> Prop))
    (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)) (su : summary) (CS : Z -> Prop) : Prop :=
  forall PROPS, summary_validP segs AL GS OPS LAWS PROPS su CS.
(* [comment removed for export] *)
Definition summary_validO (segs : list Segment) (AL : asan_layout) (GS : list Z) (OPS : list (mem -> Prop)) (su : summary) (CS : Z -> Prop) : Prop :=
  forall LAWS, summary_validL segs AL GS OPS LAWS su CS.
(* [comment removed for export] *)
Definition summary_validG (segs : list Segment) (AL : asan_layout) (GS : list Z) (su : summary) : Prop :=
  forall OPS LAWS PROPS, summary_validG1 segs AL GS OPS LAWS PROPS su.
(* [comment removed for export] *)
Definition summary_valid (segs : list Segment) (AL : asan_layout) (su : summary) : Prop := summary_validG segs AL [] su.

Lemma zforall_mono : forall n (k k' : list Z -> Prop), (forall l, k l -> k' l) -> zforall n k -> zforall n k'.
Proof. induction n as [|n IH]; intros k k' H X; cbn in X |- *; [apply H; exact X|]. intros z. apply (IH (fun l => k (z :: l))); [intros l; apply H| apply X]. Qed.
Lemma bforall_mono : forall n (k k' : list (list byte) -> Prop), (forall l, k l -> k' l) -> bforall n k -> bforall n k'.
Proof. induction n as [|n IH]; intros k k' H X; cbn in X |- *; [apply H; exact X|]. intros z. apply (IH (fun l => k (z :: l))); [intros l; apply H| apply X]. Qed.
Lemma lforall_mono : forall n (k k' : list (list word) -> Prop), (forall l, k l -> k' l) -> lforall n k -> lforall n k'.
Proof. induction n as [|n IH]; intros k k' H X; cbn in X |- *; [apply H; exact X|]. intros z. apply (IH (fun l => k (z :: l))); [intros l; apply H| apply X]. Qed.
Lemma wforall_mono : forall n (k k' : list word -> Prop), (forall l, k l -> k' l) -> wforall n k -> wforall n k'.
Proof. induction n as [|n IH]; intros k k' H X; cbn in X |- *; [apply H; exact X|]. intros z. apply (IH (fun l => k (z :: l))); [intros l; apply H| apply X]. Qed.
Lemma gb_tele_mono : forall E GS GS' gb P,
  (forall i n, In (i, n) gb -> nth n GS' 0 = nth n GS 0) -> gb_tele E GS gb P -> gb_tele E GS' gb P.
Proof.
  intros E GS GS' gb P. induction gb as [|[i n] gb IH]; intros H X; cbn in X |- *; [exact X|].
  intros Heq. apply IH; [intros i' n' Hin; apply (H i' n'); right; exact Hin|]. apply X. rewrite Heq. apply (H i n). left; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma summary_validG_ext : forall segs AL GS GSX su,
  forallb (fun jn => Nat.ltb (snd jn) (length GS)) (su_gbind su) = true ->
  summary_validG segs AL GS su -> summary_validG segs AL (GS ++ GSX) su.
Proof.
  intros segs AL GS GSX su Hgb V OPS LAWS PROPS. unfold summary_validG1. pose proof (V OPS LAWS PROPS) as V0. unfold summary_validG1 in V0.
  destruct (su_heap su); [exact V0|].
  eapply zforall_mono; [| exact V0]. cbn beta. intros ps X.
  eapply bforall_mono; [| exact X]. cbn beta. intros bss Y.
  eapply lforall_mono; [| exact Y]. cbn beta. intros lss Y' CS F fc m.
  eapply wforall_mono; [| exact (Y' CS F fc m)]. cbn beta. intros R W E G ACC SB MI.
  apply (gb_tele_mono E GS (GS ++ GSX)). 2: exact (W ACC SB MI).
  intros i n Hin. rewrite forallb_forall in Hgb. specialize (Hgb _ Hin). cbn [snd] in Hgb. apply Nat.ltb_lt in Hgb.
  apply app_nth1. exact Hgb.
Qed.
Lemma summary_validG_P : forall segs AL GS su, summary_validG segs AL GS su -> forall OPS LAWS PROPS CS, summary_validP segs AL GS OPS LAWS PROPS su CS.
Proof.
  intros segs AL GS su V OPS LAWS PROPS CS. unfold summary_validP. pose proof (V OPS LAWS PROPS) as V0. unfold summary_validG1 in V0.
  destruct (su_heap su); [exact V0|]. eapply zforall_mono; [|exact V0]. cbn beta. intros ps X.
  eapply bforall_mono; [|exact X]. cbn beta. intros bss Y. eapply lforall_mono; [|exact Y]. cbn beta. intros lss W. apply W.
Qed.
Lemma summary_validG_L : forall segs AL GS su, summary_validG segs AL GS su -> forall OPS LAWS CS, summary_validL segs AL GS OPS LAWS su CS.
Proof. intros segs AL GS su V OPS LAWS CS PROPS. apply summary_validG_P. exact V. Qed.
Lemma summary_validG_O : forall segs AL GS su, summary_validG segs AL GS su -> forall OPS CS, summary_validO segs AL GS OPS su CS.
Proof. intros segs AL GS su V OPS CS LAWS. apply summary_validG_L. exact V. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bval_den (E : env) (bv : bval) : list byte :=
  match bv with BVar k => eb E k | BCells cs => cells_bytes (csden E cs) end.

Section SubstDen.
  Variable E : env.      (* [comment removed for export] *)
  Variable E' : env.     (* [comment removed for export] *)
  Variable th : subst.
  Variable tb : bsubst.
  Variable tl : lsubst.
  (* [comment removed for export] *)
  Hypothesis TH : forall i e, sub_get th i = Some e -> zden E e = ez E' i.
  Hypothesis TB : forall kb k, bsub_get tb kb = Some (BVar k) -> eb E k = eb E' kb.   (* [comment removed for export] *)
  Hypothesis TL : forall j l, lsub_get tl j = Some l -> ldenw E l = el E' j.           (* [comment removed for export] *)

  Lemma renorm_den : forall e, zden E (renorm e) = zden E e.
  Proof.
    induction e as [z|i|i|a IHa b IHb|c a IHa|o a IHa b IHb]; cbn [renorm]; try reflexivity.
    - cbn. lia. - cbn. lia.
    - rewrite eadd_den, IHa, IHb. reflexivity.
    - rewrite emulc_den, IHa. reflexivity.
    - assert (GEN : zden E (eatom (EOp o (renorm a) (renorm b))) = opden o (zden E a) (zden E b)) by (cbn; rewrite IHa, IHb; lia).
      destruct (renorm a) as [x| | | | |]; try exact GEN. destruct (renorm b) as [y| | | | |]; try exact GEN.
      cbn in IHa, IHb. subst. cbn. destruct o; reflexivity.
  Qed.

  Lemma eloc_enoU : forall n e, eloc n e = true -> enoU e = true.
  Proof.
    induction e; cbn; intros H; try reflexivity; try discriminate;
      try (apply andb_prop in H as [H1 H2]; rewrite IHe1, IHe2 by assumption; reflexivity).
    apply IHe. exact H.
  Qed.

  Lemma sxe_den : forall e, ebound th e = true -> enoU e = true -> zden E (sxe th e) = zden E' e.
  Proof.
    intros e HB HU. unfold sxe. rewrite renorm_den.
    induction e as [z|i|i|a IHa b IHb|c a IHa|o a IHa b IHb]; cbn [sxe_raw]; cbn in HB, HU.
    - reflexivity.
    - destruct (sub_get th i) as [e|] eqn:G; [|discriminate]. cbn. apply TH. exact G.
    - discriminate.
    - apply andb_prop in HB as [B1 B2]. apply andb_prop in HU as [U1 U2]. cbn. rewrite IHa, IHb by assumption. reflexivity.
    - cbn. rewrite IHa by assumption. reflexivity.
    - apply andb_prop in HB as [B1 B2]. apply andb_prop in HU as [U1 U2]. cbn. rewrite IHa, IHb by assumption. reflexivity.
  Qed.

  Lemma sxe_denp : forall e, ebound th e = true -> enoU e = true -> zdenp E (sxe th e) = zdenp E' e.
  Proof. intros. rewrite !zdenp_ok. apply sxe_den; assumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bbound (kb : positive) : bool := match bsub_get tb kb with Some (BVar _) => true | _ => false end.

  Definition cbound (c : cellx) : bool :=
    match c with
    | XZ w e => okw w && ebound th e && enoU e
    | XB w k => bbound k
    | XSl c _ _ => false
    | XRep w e => ebound th e && enoU e
    | _ => false
    end.

  Lemma sxb_den : forall kb, bbound kb = true -> eb E (sxb tb kb) = eb E' kb.
  Proof.
    intros kb H. unfold bbound, sxb in *. destruct (bsub_get tb kb) as [[k|cs]|] eqn:G; try discriminate. apply (TB kb k). exact G.
  Qed.

  Lemma sxc_den : forall c, cbound c = true -> cden E (sxc th tb c) = cden E' c.
  Proof.
    intros c H. destruct c as [i|w e|w k|w i|c o l|wr er]; cbn in H; try discriminate.
    - apply andb_prop in H as [H HU]. apply andb_prop in H as [HW HB]. cbn [sxc].
      destruct (okw_cases w HW) as [-> |[-> |[-> | ->]]]; cbn [cden]; rewrite (sxe_denp e HB HU); reflexivity.
    - cbn [sxc cden]. rewrite (sxb_den k H). reflexivity.
    - apply andb_prop in H as [HB HU]. cbn [sxc cden]. rewrite (sxe_denp er HB HU). reflexivity.
  Qed.

  Lemma sxcs_den : forall cs, forallb cbound cs = true -> csden E (map (sxc th tb) cs) = csden E' cs.
  Proof.
    induction cs as [|c cs IH]; cbn; intros H; [reflexivity|]. apply andb_prop in H as [H1 H2].
    unfold csden. cbn [map]. rewrite (sxc_den c H1). f_equal. apply IH. exact H2.
  Qed.

  Definition pbound (f : pfact) : bool :=
    match f with
    | FGe e => ebound th e && enoU e
    | FSep a b c d | FOr2 a b c d => forallb (fun e => ebound th e && enoU e) [a; b; c; d]
    | FSep0 z a b c d | FOr3z z a b c d => forallb (fun e => ebound th e && enoU e) [z; a; b; c; d]
    | FAl a _ => ebound th a && enoU a
    | FCr a b | FLe a b | FLt a b | FEq a b => forallb (fun e => ebound th e && enoU e) [a; b]
    | FShb _ _ _ _ => false
    | FProp _ xs => forallb (fun e => ebound th e && enoU e) xs
    end.

  Lemma sxes_denp : forall xs, forallb (fun e => ebound th e && enoU e) xs = true -> map (zdenp E) (map (sxe th) xs) = map (zdenp E') xs.
  Proof.
    induction xs as [|x xs IH]; cbn -[zdenp sxe ebound enoU]; intros H; [reflexivity|].
    apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [HB HU]. rewrite (sxe_denp x HB HU), IH by assumption. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Hypothesis EP : epr E = epr E'.
  Lemma sxp_ok : forall CS f, pbound f = true -> pfact_ok CS E (sxp th f) <-> pfact_ok CS E' f.
  Proof.
    intros CS f H.
    destruct f as [| | | | | | | | | | |pj pxs]; [| | | | | | | | | | | unfold pfact_ok, eprop; cbn [sxp]; cbn [pbound] in H; rewrite (sxes_denp pxs H), EP; tauto].
    all: cbn -[zdenp sxe Z.pow Z.of_N] in H |- *; try discriminate;
      repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end;
      repeat match goal with
        | HB : ebound th ?e = true, HU : enoU ?e = true |- _ => rewrite (sxe_denp e HB HU); clear HB
        end; tauto.
  Qed.

  Definition mbound (f : mfact) : bool :=
    match f with
    | MRw a cs | MRo a cs => ebound th a && enoU a && forallb cbound cs
    | MBy a n k => ebound th a && enoU a && ebound th n && enoU n && bbound k
    | MStk a b | MAobj a b => ebound th a && enoU a && ebound th b && enoU b
    | MOpq _ _ _ => false
    | MArr _ _ _ _ _ => false
    | MMunch _ _ _ | MWmono _ _ | MLaw _ _ _ _ => false    (* [comment removed for export] *)
    | MCli _ a b | MCobj _ a b => ebound th a && enoU a && ebound th b && enoU b   (* [comment removed for export] *)
    | MHeap _ _ | MLawH _ _ _ _ _ _ | MCliH _ _ _ _ | MApartBl _ _ _ | MOqH _ _ | MHpr _ _ _ _ _ => false   (* [comment removed for export] *)
    end.
  (* [comment removed for export] *)
  Definition mboundA (f : mfact) : bool :=
    match f with
    | MArr a w (LBase j) n _ => (N.eqb w 4 || N.eqb w 8) && ebound th a && enoU a && ebound th n && enoU n
                               && match lsub_get tl j with Some _ => true | None => false end
    | _ => mbound f
    end.

  (* [comment removed for export] *)
  Hypothesis EL : forall l, elaw E l = elaw E' l.

  Lemma sxm_ok0 : forall segs L CS mm f, mbound f = true ->
    mfact_ok segs L CS E mm (sxm th tb tl f) <-> mfact_ok segs L CS E' mm f.
  Proof.
    intros segs L CS mm f H. destruct f; try discriminate; cbn -[zdenp sxe csden map sxc eb sxb Z.of_nat lawcli lawobj elaw] in H |- *;
      repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end;
      repeat match goal with
        | HB : ebound th ?e = true, HU : enoU ?e = true |- _ => rewrite (sxe_denp e HB HU); clear HB
        | HC : forallb cbound ?cs = true |- _ => rewrite (sxcs_den cs HC); clear HC
        | HK : bbound ?k = true |- _ => rewrite (sxb_den k HK); clear HK
        end; rewrite ?EL; tauto.
  Qed.
  Lemma sxm_ok : forall segs L CS mm f, mboundA f = true ->
    mfact_ok segs L CS E mm (sxm th tb tl f) <-> mfact_ok segs L CS E' mm f.
  Proof.
    intros segs L CS mm f H. destruct f as [| | | | | |a w [j|] n wr| | | | | | | | | | |hj ho hn hxs hok]; try exact (sxm_ok0 segs L CS mm _ H).
    cbn [mboundA] in H. repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end.
    destruct (lsub_get tl j) as [lc|] eqn:TJ; [|discriminate].
    cbn [sxm sxl]. rewrite TJ.
    assert (W48 : w = 4%N \/ w = 8%N).
    { match goal with G : N.eqb w 4 || N.eqb w 8 = true |- _ => apply orb_prop in G as [G|G]; apply N.eqb_eq in G; [left|right]; exact G end. }
    destruct W48 as [-> | ->]; cbn [mfact_ok];
      repeat match goal with
        | HB : ebound th ?e = true, HU : enoU ?e = true |- _ => rewrite (sxe_denp e HB HU); clear HB
        end; rewrite (TL j lc TJ); cbn [ldenw]; tauto.
  Qed.

  Lemma sxw_den : forall W, forallb (fun lh => ebound th (fst lh) && enoU (fst lh) && ebound th (snd lh) && enoU (snd lh)) W = true ->
    wden E (sxw th W) = wden E' W.
  Proof.
    induction W as [|[l h] W IH]; cbn -[sxe zdenp]; intros H; [reflexivity|].
    repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end. unfold wden in *. cbn -[sxe zdenp].
    rewrite (sxe_denp l), (sxe_denp h) by assumption. f_equal. apply IH. assumption.
  Qed.
End SubstDen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition thsub (th th' : subst) : Prop := forall i e, sub_get th i = Some e -> sub_get th' i = Some e.
Definition tbsub (tb tb' : bsubst) : Prop := forall kb k, bsub_get tb kb = Some k -> bsub_get tb' kb = Some k.

Lemma thsub_refl : forall th, thsub th th. Proof. intros th i e H; exact H. Qed.
Lemma thsub_trans : forall a b c, thsub a b -> thsub b c -> thsub a c. Proof. intros a b c H1 H2 i e H. apply H2, H1, H. Qed.
Lemma tbsub_refl : forall tb, tbsub tb tb. Proof. intros tb i e H; exact H. Qed.
Lemma tbsub_trans : forall a b c, tbsub a b -> tbsub b c -> tbsub a c. Proof. intros a b c H1 H2 i e H. apply H2, H1, H. Qed.

Lemma bind_ok : forall th i e th', bind th i e = Some th' -> sub_get th' i = Some e /\ thsub th th'.
Proof.
  intros th i e th' H. unfold bind in H. destruct (sub_get th i) as [e'|] eqn:G.
  - destruct (expr_eqb e' e) eqn:EQ; [|discriminate]. injection H; intros <-. apply expr_eqb_eq in EQ. subst e'.
    split; [exact G| apply thsub_refl].
  - injection H; intros <-. split; [cbn; rewrite Pos.eqb_refl; reflexivity|].
    intros j e2 Hj. cbn. destruct (Pos.eqb_spec j i) as [->|]; [rewrite G in Hj; discriminate| exact Hj].
Qed.

Lemma ebound_mono : forall th th' e, thsub th th' -> ebound th e = true -> ebound th' e = true.
Proof.
  intros th th' e HS. induction e; cbn; intros H; try reflexivity; try exact H.
  - destruct (sub_get th i) as [x|] eqn:G; [|discriminate]. rewrite (HS _ _ G). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply IHe. exact H.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
Qed.

Lemma sxe_ext : forall th th' e, thsub th th' -> ebound th e = true -> sxe th' e = sxe th e.
Proof.
  intros th th' e HS H. unfold sxe. f_equal. induction e; cbn in H |- *; try reflexivity.
  - destruct (sub_get th i) as [x|] eqn:G; [|discriminate]. rewrite (HS _ _ G). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
Qed.

Lemma match_regs_ok : forall ss rb th th', match_regs ss rb th = Some th' ->
  thsub th th' /\ Forall (fun ri => sub_get th' (snd ri) = Some (rd_expr ss (fst ri))) rb.
Proof.
  intros ss rb. induction rb as [|[r i] rb IH]; intros th th' H; cbn in H.
  - injection H; intros <-. split; [apply thsub_refl| constructor].
  - destruct (bind th i (rd_expr ss r)) as [th1|] eqn:B; [|discriminate].
    destruct (bind_ok _ _ _ _ B) as [G1 S1]. destruct (IH _ _ H) as [S2 F2].
    split; [eapply thsub_trans; eauto|]. constructor; [cbn; apply S2; exact G1| exact F2].
Qed.

Lemma find_rw_In : forall mf a cs, find_rw mf a = Some cs -> In (MRw a cs) mf.
Proof.
  induction mf as [|f mf IH]; intros a cs H; cbn in H; [discriminate|].
  destruct f as [b ds|b ds|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try (right; apply IH; exact H).
  destruct (expr_eqb a b) eqn:EQ; [|right; apply IH; exact H]. apply expr_eqb_eq in EQ. subst b. injection H; intros <-. left; reflexivity.
Qed.

Lemma pat_local_den : forall E pe j, pat_local pe = Some j -> zdenp E pe = ez E j /\ forall th, ebound th pe = match sub_get th j with Some _ => true | None => false end.
Proof.
  intros E pe j H. unfold pat_local in H.
  destruct pe as [z|i|i|a b|c a|o a b]; try discriminate.
  - injection H; intros <-. split; [reflexivity| intros th; reflexivity].
  - destruct a as [| | | |c a'|]; try discriminate. destruct c as [|p|]; try discriminate. destruct p; try discriminate.
    destruct a' as [|i| | | |]; try discriminate. destruct b as [z| | | | |]; try discriminate. destruct z; try discriminate.
    injection H; intros <-. split; [cbn; reflexivity|]. intros th. cbn. destruct (sub_get th i); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cden_XZ_ext : forall E1 E2 w a b, zdenp E1 a = zdenp E2 b -> cden E1 (XZ w a) = cden E2 (XZ w b).
Proof. intros E1 E2 w a b H. cbn [cden]. rewrite H. reflexivity. Qed.

Lemma cell_match_den : forall E E' c e (w : N) pe,
  cell_expr c = Some e -> N.eqb (cellx_size c) w = true -> zdenp E' pe = zden E e -> cden E c = cden E' (XZ w pe).
Proof.
  intros E E' c e w pe HC HS HD. apply N.eqb_eq in HS. subst w. rewrite <- zdenp_ok in HD.
  destruct c as [i|w' e'|w' k|w' i|c o l|wr er]; cbn in HC; try discriminate.
  - injection HC; intros <-. cbn [cellx_size cden]. rewrite HD. cbn. rewrite w64_of_unsigned. reflexivity.
  - injection HC; intros <-. cbn [cellx_size]. symmetry. apply cden_XZ_ext. exact HD.
  - destruct w' as [|p]; [discriminate|].
    destruct p as [p|p|]; try discriminate; destruct p as [p|p|]; try discriminate; [destruct p; try discriminate|];
      injection HC; intros <-; cbn [cellx_size cden]; rewrite HD; cbn; rewrite w64_of_unsigned; reflexivity.
Qed.
Lemma take_cells_ok : forall cs n pre rest, take_cells cs n = Some (pre, rest) -> cs = pre ++ rest /\ Z.of_N (cells_sizeN pre) = n.
Proof.
  induction cs as [|c cs IH]; intros n pre rest H; cbn [take_cells] in H.
  - destruct (Z.eqb_spec n 0); [|discriminate]. injection H; intros <- <-. split; [reflexivity| cbn; lia].
  - destruct (Z.eqb_spec n 0). { injection H; intros <- <-. split; [reflexivity| cbn; lia]. }
    destruct (Z.ltb n (Z.of_N (cellx_size c))) eqn:LT; [discriminate|]. apply Z.ltb_ge in LT.
    destruct (take_cells cs (n - Z.of_N (cellx_size c))) as [[p r]|] eqn:TC; [|discriminate]. injection H; intros <- <-.
    destruct (IH _ _ _ TC) as [E1 E2]. split; [cbn; rewrite E1; reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma take_cellsx_ok : forall E cs n pre rest, take_cellsx cs n = Some (pre, rest) -> cells_wf (csden E cs) ->
  cells_wf (csden E (pre ++ rest)) /\ cells_bytes (csden E (pre ++ rest)) = cells_bytes (csden E cs) /\ Z.of_N (cells_sizeN pre) = n.
Proof.
  intros E cs. unfold csden. induction cs as [|c cs IH]; intros n pre rest H WF; cbn [take_cellsx] in H.
  - destruct (Z.eqb_spec n 0); [|discriminate]. injection H; intros <- <-. split; [exact WF| split; [reflexivity| cbn; lia]].
  - destruct (Z.eqb_spec n 0). { injection H; intros <- <-. split; [exact WF| split; [reflexivity| cbn; lia]]. }
    cbn [map cells_wf] in WF. destruct WF as [WC WCS]. pose proof (cbytes_length _ WC) as LC. rewrite cden_size in LC.
    destruct (Z.ltb_spec n (Z.of_N (cellx_size c))) as [LT|GE].
    + destruct (Z.ltb_spec 0 n) as [PO|]; [|discriminate]. injection H; intros <- <-.
      destruct (mk_slice_ok E c 0 (Z.to_N n) WC ltac:(lia)) as (S1 & W1 & B1).
      destruct (mk_slice_ok E c (Z.to_N n) (Z.to_N (Z.of_N (cellx_size c) - n)) WC ltac:(lia)) as (S2 & W2 & B2).
      cbn [app map cells_wf cells_bytes cells_sizeN]. split; [split; [exact W1| split; [exact W2| exact WCS]]|]. split; [| rewrite S1; cbn; lia].
      rewrite app_assoc. f_equal. rewrite B1, B2. change (N.to_nat 0) with 0%nat. rewrite skipn_O.
      replace (N.to_nat (Z.to_N (Z.of_N (cellx_size c) - n))) with (length (skipn (N.to_nat (Z.to_N n)) (cbytes (cden E c)))) by (rewrite skipn_length; lia).
      rewrite firstn_all. apply firstn_skipn.
    + destruct (take_cellsx cs (n - Z.of_N (cellx_size c))) as [[p r]|] eqn:TC; [|discriminate]. injection H; intros <- <-.
      destruct (IH _ _ _ TC WCS) as (E1 & E2 & E3). cbn [app map cells_wf cells_bytes cells_sizeN].
      split; [split; [exact WC| exact E1]|]. split; [rewrite E2; reflexivity| lia].
Qed.

Lemma mk_slice_expr : forall c o l e, cell_expr (mk_slice c o l) = Some e -> mk_slice c o l = c \/ exists z, e = ELit z.
Proof.
  intros c o l e H. unfold mk_slice in H |- *. destruct (N.eqb o 0 && N.eqb l (cellx_size c)); [left; reflexivity| right].
  assert (M2 : forall b o' e', cell_expr (mk_slice2 b o' l) = Some e' -> exists z, e' = ELit z).
  { intros b o' e' H'. unfold mk_slice2 in H'. destruct b as [i|w [z| | | | |]|w k|w i|c' o2 l2|wr er]; cbn in H'; try discriminate.
    - destruct (okw w && okw l); cbn in H'; [injection H'; intros <-; eexists; reflexivity| discriminate].
    - destruct (N.leb (o' + l) wr); cbn in H'; discriminate. }
  destruct c as [i|w ez|w k|w i|c' o2 l2|wr er]; exact (M2 _ _ _ H).
Qed.
Lemma take_cellsx_in : forall cs n pre rest, take_cellsx cs n = Some (pre, rest) ->
  forall c0, In c0 (pre ++ rest) -> In c0 cs \/ exists c o l, In c cs /\ c0 = mk_slice c o l.
Proof.
  induction cs as [|c cs IH]; intros n pre rest H c0 Hin; cbn [take_cellsx] in H.
  - destruct (Z.eqb n 0); [|discriminate]. injection H; intros <- <-. left. exact Hin.
  - destruct (Z.eqb n 0). { injection H; intros <- <-. left. exact Hin. }
    destruct (Z.ltb n (Z.of_N (cellx_size c))).
    + destruct (Z.ltb 0 n); [|discriminate]. injection H; intros <- <-. cbn [app] in Hin.
      destruct Hin as [<-|[<-|Hin]]; [right; exists c; eexists; eexists; split; [left; reflexivity| reflexivity] ..| left; right; exact Hin].
    + destruct (take_cellsx cs (n - Z.of_N (cellx_size c))) as [[p r]|] eqn:TC; [|discriminate]. injection H; intros <- <-.
      cbn [app] in Hin. destruct Hin as [<-|Hin]; [left; left; reflexivity|].
      destruct (IH _ _ _ TC c0 Hin) as [X|(c1 & o & l & Hc1 & ->)]; [left; right; exact X| right]. exists c1, o, l. split; [right; exact Hc1| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_bytes_eq : forall segs m a cs1 cs2,
  rw_cells segs m a cs1 -> cells_bytes cs1 = cells_bytes cs2 -> cells_wf cs2 -> rw_cells segs m a cs2.
Proof.
  intros segs m a cs1 cs2 [[W1 B1] WR] EQ W2.
  assert (SZ : cells_size cs2 = cells_size cs1).
  { rewrite <- (cells_bytes_length cs1 W1), <- (cells_bytes_length cs2 W2), EQ. reflexivity. }
  split; [split; [exact W2| rewrite <- EQ; exact B1]| rewrite SZ; exact WR].
Qed.

(* [comment removed for export] *)
Lemma xrep_expose_ok : forall E w c cs' c2 cs2, xrep_expose w c cs' = (c2, cs2) ->
  cells_bytes (csden E (c2 :: cs2)) = cells_bytes (csden E (c :: cs')) /\ (cells_wf (csden E (c :: cs')) -> cells_wf (csden E (c2 :: cs2))).
Proof.
  intros E w c cs' c2 cs2 H.
  assert (TRIV : (c, cs') = (c2, cs2) -> cells_bytes (csden E (c2 :: cs2)) = cells_bytes (csden E (c :: cs')) /\ (cells_wf (csden E (c :: cs')) -> cells_wf (csden E (c2 :: cs2))))
    by (intros X; injection X; intros <- <-; split; [reflexivity| intros Y; exact Y]).
  unfold xrep_expose in H. destruct c as [i|w' e'|w' k|w' i|c o l|n e]; try exact (TRIV H).
  destruct (is_lit e) as [z|] eqn:LZ; [|exact (TRIV H)]. destruct (Z.eqb_spec z 0) as [->|]; [|exact (TRIV H)].
  destruct (okw w) eqn:OK; [|exact (TRIV H)]. cbn [andb] in H. apply is_lit_den with (E := E) in LZ.
  assert (ZC : forall cs0, cells_bytes (csden E (XZ w (ELit 0) :: cs0)) = repeat (Z_to_bv 8 0) (N.to_nat w) ++ cells_bytes (csden E cs0)
                         /\ (cells_wf (csden E cs0) -> cells_wf (csden E (XZ w (ELit 0) :: cs0)))).
  { intros cs0. unfold csden. cbn [map cells_bytes cells_wf].
    unfold okw in OK. destruct w as [|p]; [discriminate|].
    repeat (destruct p as [p|p|]; try discriminate); cbn; (split; [reflexivity| intros Y; split; [first [exact I | reflexivity] | exact Y]]). }
  assert (RC : forall k cs0, cells_bytes (csden E (XRep k e :: cs0)) = repeat (Z_to_bv 8 0) (N.to_nat k) ++ cells_bytes (csden E cs0)
                          /\ (cells_wf (csden E (XRep k e :: cs0)) <-> cells_wf (csden E cs0))).
  { intros k cs0. unfold csden. cbn [map cells_bytes cells_wf cden cbytes cell_wf]. rewrite zdenp_ok, LZ. split; [reflexivity|].
    rewrite repeat_length. tauto. }
  destruct (N.ltb_spec w n) as [LT|GE].
  - injection H; intros <- <-. destruct (ZC (XRep (n - w) e :: cs')) as [B1 W1]. destruct (RC (n - w)%N cs') as [B2 W2]. destruct (RC n cs') as [B3 W3].
    rewrite B1, B2, B3, app_assoc, <- repeat_app. replace (N.to_nat w + N.to_nat (n - w))%nat with (N.to_nat n) by lia.
    split; [reflexivity|]. intros Y. apply W1. apply (proj2 W2). apply (proj1 W3). exact Y.
  - destruct (N.eqb_spec w n) as [->|]; [|exact (TRIV H)]. injection H; intros <- <-.
    destruct (ZC cs') as [B1 W1]. destruct (RC n cs') as [B3 W3]. rewrite B1, B3. split; [reflexivity|]. intros Y. apply W1. apply (proj1 W3). exact Y.
Qed.

(* [comment removed for export] *)
Lemma match_cells_ok : forall pats cs th tb th' tb',
  match_cells pats cs th tb = Some (th', tb') ->
  thsub th th' /\ tbsub tb tb' /\
  forall E E' thF tbF, thsub th' thF -> tbsub tb' tbF ->
    (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
    (forall kb bv, bsub_get tbF kb = Some bv -> bval_den E bv = eb E' kb) ->
    cells_wf (csden E cs) ->
    cells_bytes (csden E cs) = cells_bytes (csden E' pats) /\ cells_wf (csden E' pats).
Proof.
  induction pats as [|p pats IH]; intros cs th tb th' tb' H.
  - destruct cs; cbn in H; [|discriminate]. injection H; intros <- <-.
    split; [apply thsub_refl|]. split; [apply tbsub_refl|]. intros; split; [reflexivity| exact I].
  - (* [comment removed for export] *)
    assert (HEAD : forall c cs' th1 tb1, match_cells pats cs' th1 tb1 = Some (th', tb') ->
              (forall E E' thF tbF, thsub th' thF -> tbsub tb' tbF ->
                 (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
                 (forall kb bv, bsub_get tbF kb = Some bv -> bval_den E bv = eb E' kb) -> cden E c = cden E' p) ->
              thsub th th1 -> tbsub tb tb1 ->
              thsub th th' /\ tbsub tb tb' /\
              forall E E' thF tbF, thsub th' thF -> tbsub tb' tbF ->
                (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
                (forall kb bv, bsub_get tbF kb = Some bv -> bval_den E bv = eb E' kb) ->
                cells_wf (csden E (c :: cs')) ->
                cells_bytes (csden E (c :: cs')) = cells_bytes (csden E' (p :: pats)) /\ cells_wf (csden E' (p :: pats))).
    { intros c cs' th1 tb1 M HC S1 T1. destruct (IH _ _ _ _ _ M) as (S2 & T2 & R2).
      split; [eapply thsub_trans; eauto|]. split; [eapply tbsub_trans; eauto|].
      intros E E' thF tbF SF TF TH TB WF. unfold csden in *. cbn [map cells_bytes cells_wf] in WF |- *. destruct WF as [WFc WF].
      destruct (R2 E E' thF tbF SF TF TH TB WF) as [B2 W2]. rewrite <- (HC E E' thF tbF SF TF TH TB), B2.
      split; [reflexivity| split; [exact WFc| exact W2]]. }
    destruct p as [i|w pe|w kb|w i|c o l|wr er]; cbn [match_cells] in H; try discriminate.
    + (* [comment removed for export] *)
      destruct cs as [|c0 cs0]; [discriminate|].
      destruct (xrep_expose w c0 cs0) as [c cs] eqn:XE.
      (* [comment removed for export] *)
      enough (R : thsub th th' /\ tbsub tb tb' /\
              forall E E' thF tbF, thsub th' thF -> tbsub tb' tbF ->
                (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
                (forall kb bv, bsub_get tbF kb = Some bv -> bval_den E bv = eb E' kb) ->
                cells_wf (csden E (c :: cs)) ->
                cells_bytes (csden E (c :: cs)) = cells_bytes (csden E' (XZ w pe :: pats)) /\ cells_wf (csden E' (XZ w pe :: pats))).
      { destruct R as (S & T & R). split; [exact S|]. split; [exact T|]. intros E E' thF tbF SF TF TH TB WF.
        destruct (xrep_expose_ok E w c0 cs0 c cs XE) as [B W]. rewrite <- B. apply (R E E' thF tbF SF TF TH TB (W WF)). }
      destruct (N.eqb (cellx_size c) w) eqn:SZ; [|discriminate].
      destruct (cell_expr c) as [e|] eqn:CE; [|discriminate].
      destruct (pat_local pe) as [j|] eqn:PL.
      * destruct (bind th j e) as [th1|] eqn:B; [|discriminate].
        destruct (bind_ok _ _ _ _ B) as [G1 S1].
        apply (HEAD c cs th1 tb H); [| exact S1| apply tbsub_refl].
        intros E E' thF tbF SF TF TH TB. apply cell_match_den with (e := e); [exact CE| exact SZ|].
        destruct (pat_local_den E' pe j PL) as [-> _]. symmetry. apply TH. apply SF.
        destruct (IH _ _ _ _ _ H) as (S2 & _ & _). apply S2. exact G1.
      * destruct (ebound th pe) eqn:EB; [|discriminate]. destruct (enoU pe) eqn:EU; [|discriminate].
        destruct (expr_eqb (sxe th pe) e) eqn:EQ; [|discriminate]. cbn [andb] in H.
        apply (HEAD c cs th tb H); [| apply thsub_refl| apply tbsub_refl].
        intros E E' thF tbF SF TF TH TB. apply cell_match_den with (e := e); [exact CE| exact SZ|].
        destruct (IH _ _ _ _ _ H) as (S2 & _ & _).
        apply expr_eqb_eq in EQ. rewrite <- EQ. rewrite <- (sxe_ext th thF pe) by (try exact EB; eapply thsub_trans; eauto).
        rewrite zdenp_ok. symmetry. apply (sxe_den E E' thF TH).
        -- eapply ebound_mono; [|exact EB]. eapply thsub_trans; eauto.
        -- exact EU.
    + (* [comment removed for export] *)
      assert (CELLS : forall cs0, (match bsub_get tb kb, take_cellsx cs0 (Z.of_N w) with
                                    | None, Some (taken, cs') => match_cells pats cs' th ((kb, BCells taken) :: tb)
                                    | _, _ => None end) = Some (th', tb') ->
                 thsub th th' /\ tbsub tb tb' /\
                 forall E E' thF tbF, thsub th' thF -> tbsub tb' tbF ->
                   (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
                   (forall kb bv, bsub_get tbF kb = Some bv -> bval_den E bv = eb E' kb) ->
                   cells_wf (csden E cs0) ->
                   cells_bytes (csden E cs0) = cells_bytes (csden E' (XB w kb :: pats)) /\ cells_wf (csden E' (XB w kb :: pats))).
      { intros cs0 M. destruct (bsub_get tb kb) as [bv0|] eqn:BG; [discriminate|].
        destruct (take_cellsx cs0 (Z.of_N w)) as [[taken cs']|] eqn:TC; [|discriminate].
        destruct (IH _ _ _ _ _ M) as (S2 & T2 & R2). split; [exact S2|].
        split. { intros kb2 k2 Hk. apply T2. cbn. destruct (Pos.eqb_spec kb2 kb) as [->|]; [rewrite BG in Hk; discriminate| exact Hk]. }
        intros E E' thF tbF SF TF TH TB WF0. destruct (take_cellsx_ok E cs0 _ _ _ TC WF0) as (WF & BY0 & SZ). rewrite <- BY0. clear WF0 BY0.
        unfold csden in *. rewrite map_app, cells_bytes_app in *. rewrite cells_wf_app in WF. destruct WF as [WFt WF].
        cbn [map cells_bytes cells_wf cden cbytes].
        destruct (R2 E E' thF tbF SF TF TH TB WF) as [B2 W2]. rewrite B2.
        assert (KB : eb E' kb = cells_bytes (map (cden E) taken)).
        { symmetry. apply (TB kb (BCells taken)). apply TF, T2. cbn. rewrite Pos.eqb_refl. reflexivity. }
        rewrite KB. split; [reflexivity|]. split; [|exact W2].
        pose proof (csden_wf_bytes_length E taken WFt) as LT. unfold csden in LT. cbn [cell_wf]. rewrite LT. lia. }
      destruct cs as [|c cs]; [exact (CELLS [] H)|].
      destruct c as [i'|w' e'|w' k|w' i'|c' o' l'|wr' er']; try exact (CELLS _ H).
      destruct (N.eqb w w') eqn:WW; [|discriminate]. apply N.eqb_eq in WW. subst w'.
      destruct (bsub_get tb kb) as [[k'|cs']|] eqn:BG; [| discriminate|].
      * destruct (Pos.eqb_spec k k'); [|discriminate]. subst k'.
        apply (HEAD _ cs th tb H); [| apply thsub_refl| apply tbsub_refl].
        intros E E' thF tbF SF TF TH TB. cbn [cden]. destruct (IH _ _ _ _ _ H) as (_ & T2 & _).
        rewrite <- (TB kb (BVar k)) by (apply TF, T2; exact BG). reflexivity.
      * apply (HEAD _ cs th ((kb, BVar k) :: tb) H); [| apply thsub_refl|].
        2:{ intros kb2 k2 Hk. cbn. destruct (Pos.eqb_spec kb2 kb) as [->|]; [rewrite BG in Hk; discriminate| exact Hk]. }
        intros E E' thF tbF SF TF TH TB. cbn [cden]. destruct (IH _ _ _ _ _ H) as (_ & T2 & _).
        rewrite <- (TB kb (BVar k)); [reflexivity|]. apply TF, T2. cbn. rewrite Pos.eqb_refl. reflexivity.
Qed.
Lemma match_chunks_ok : forall mf mb th tb th' tb',
  match_chunks mf mb th tb = Some (th', tb') ->
  thsub th th' /\ tbsub tb tb' /\
  forall segs L CS m E E' thF tbF, thsub th' thF -> tbsub tb' tbF ->
    (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
    (forall kb bv, bsub_get tbF kb = Some bv -> bval_den E bv = eb E' kb) ->
    Forall (fun f => match f with MRw a _ => enoU a = true | _ => True end) mb ->
    Forall (mfact_ok segs L CS E m) mf ->
    Forall (fun f => match f with MArr _ _ _ _ _ => True | _ => mfact_ok segs L CS E' m f end) mb.   (* [comment removed for export] *)
Proof.
  induction mb as [|f mb IH]; intros th tb th' tb' H.
  - cbn in H. injection H; intros <- <-. split; [apply thsub_refl|]. split; [apply tbsub_refl|]. intros; constructor.
  - cbn [match_chunks] in H. destruct f as [a pats|a cs|a n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try discriminate.
    2:{ destruct (IH _ _ _ _ H) as (S2 & T2 & R2). split; [exact S2|]. split; [exact T2|].
        intros segs L CS m E E' thF tbF SF TF TH TB HU HM. inversion HU as [|f' mb' HUa HU']; subst f' mb'.
        constructor; [exact I| exact (R2 segs L CS m E E' thF tbF SF TF TH TB HU' HM)]. }
    destruct (ebound th a) eqn:EB; [|discriminate].
    destruct (find_rw mf (sxe th a)) as [cs|] eqn:FR; [|discriminate].
    destruct (match_cells pats cs th tb) as [[th1 tb1]|] eqn:MC; [|discriminate].
    destruct (match_cells_ok _ _ _ _ _ _ MC) as (S1 & T1 & R1). destruct (IH _ _ _ _ H) as (S2 & T2 & R2).
    split; [eapply thsub_trans; eauto|]. split; [eapply tbsub_trans; eauto|].
    intros segs L CS m E E' thF tbF SF TF TH TB HU HM. inversion HU as [|f' mb' HUa HU']; subst f' mb'.
    constructor; [| exact (R2 segs L CS m E E' thF tbF SF TF TH TB HU' HM)].
    apply find_rw_In in FR. rewrite List.Forall_forall in HM. specialize (HM _ FR). cbn in HM |- *. rewrite zdenp_ok in HM |- *.
    destruct (R1 E E' thF tbF ltac:(eapply thsub_trans; eauto) ltac:(eapply tbsub_trans; eauto) TH TB (proj1 (proj1 HM))) as [BY WF].
    rewrite <- (sxe_den E E' thF TH a); [| eapply ebound_mono; [|exact EB]; eapply thsub_trans; [|exact SF]; eapply thsub_trans; eauto | exact HUa].
    rewrite (sxe_ext th thF a); [| | exact EB]. 2:{ eapply thsub_trans; [|exact SF]; eapply thsub_trans; eauto. }
    exact (rw_cells_bytes_eq segs m _ _ _ HM BY WF).
Qed.

(* [comment removed for export] *)
Definition stk_just (mf0 mf : list mfact) (lo h : expr) : Prop :=
  In (MStk lo h) mf \/ exists h' cs, In (MStk lo h') mf /\ In (MRw h' cs) mf0 /\ forall E, zden E h = zden E h' + Z.of_N (cells_sizeN cs).
Lemma frame_fills_sound : forall mf0 h hi, frame_fills mf0 h hi = true ->
  exists cs, In (MRw h cs) mf0 /\ forall E, zden E hi = zden E h + Z.of_N (cells_sizeN cs).
Proof.
  intros mf0 h hi H. unfold frame_fills in H. apply existsb_exists in H as (f & Hin & Hf).
  destruct f as [b cs| | | | | | | | | | | | | | | | |hj ho hn hxs hok]; try discriminate.
  apply andb_prop in Hf as [E1 E2]. apply expr_eqb_eq in E1. subst b. apply expr_eqb_eq in E2.
  exists cs. split; [exact Hin|]. intros E. rewrite <- (enorm_den E hi), <- E2, enorm_den, eadd_den. reflexivity.
Qed.
Lemma match_stk_ok : forall mf0 mf h i th th', match_stk mf0 mf h i th = Some th' ->
  thsub th th' /\ exists lo, sub_get th' i = Some lo /\ stk_just mf0 mf lo h.
Proof.
  intros mf0. induction mf as [|f mf IH]; intros h i th th' H; cbn -[frame_fills expr_eqb bind] in H; [discriminate|].
  assert (LIFT : forall lo', stk_just mf0 mf lo' h -> stk_just mf0 (f :: mf) lo' h).
  { intros lo' [IN|(h' & cs & IN & INC & EQ)]; [left; right; exact IN| right; exists h', cs; split; [right; exact IN| split; [exact INC| exact EQ]]]. }
  destruct f as [a pats|a cs|a n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try (destruct (IH _ _ _ _ H) as (S & lo' & G & IN); split; [exact S| exists lo'; split; [exact G| apply LIFT; exact IN]]).
  destruct (expr_eqb hi h) eqn:EQ.
  - apply expr_eqb_eq in EQ. subst hi. destruct (bind_ok _ _ _ _ H) as [G S]. split; [exact S|]. exists lo. split; [exact G| left; left; reflexivity].
  - destruct (frame_fills mf0 hi h) eqn:FF.
    + destruct (bind_ok _ _ _ _ H) as [G S]. split; [exact S|]. exists lo. split; [exact G|].
      destruct (frame_fills_sound _ _ _ FF) as (cs & INC & EQ2). right. exists hi, cs. split; [left; reflexivity| split; [exact INC| exact EQ2]].
    + destruct (IH _ _ _ _ H) as (S & lo' & G & IN). split; [exact S|]. exists lo'. split; [exact G| apply LIFT; exact IN].
Qed.
Lemma stk_just_sound : forall segs L CS E m mf0 mf lo h,
  Forall (mfact_ok segs L CS E m) mf -> Forall (mfact_ok segs L CS E m) mf0 -> stk_just mf0 mf lo h ->
  stk segs m (zden E lo) (zden E h).
Proof.
  intros segs L CS E m mf0 mf lo h HM HM0 [IN|(h' & cs & IN & INC & EQ)]; rewrite List.Forall_forall in HM.
  - pose proof (HM _ IN) as X. cbn in X. rewrite !zdenp_ok in X. exact X.
  - pose proof (HM _ IN) as X. cbn in X. rewrite !zdenp_ok in X.
    rewrite List.Forall_forall in HM0. pose proof (HM0 _ INC) as Y. cbn [mfact_ok] in Y. rewrite zdenp_ok in Y.
    pose proof (stk_of_rw_cells segs m _ _ Y) as Z0. rewrite (csden_size E cs) in Z0.
    replace (Z.of_nat (N.to_nat (cells_sizeN cs))) with (Z.of_N (cells_sizeN cs)) in Z0 by lia.
    rewrite EQ. destruct X as (X0 & X1 & X2). destruct Z0 as (Z1 & Z2 & Z3).
    split; [exact X0|]. split; [exact Z2|]. intros a Ha.
    destruct (Z_lt_dec a (zden E h')); [apply X2; lia| apply Z3; lia].
Qed.

Lemma mby_facts_In : forall mf a n k, In (a, n, k) (mby_facts mf) -> In (MBy a n k) mf.
Proof.
  induction mf as [|f mf IH]; intros a n k H; cbn in H; [destruct H|].
  destruct f; try (right; apply IH; exact H). destruct H as [H|H]; [injection H; intros <- <- <-; left; reflexivity| right; apply IH; exact H].
Qed.

Lemma bind_bytes_ok : forall bb cands th tb k th' tb',
  bind_bytes bb cands th tb k = Some (th', tb') ->
  thsub th th' /\ tbsub tb tb' /\ k th' = true /\
  Forall (fun b => match b with (ia, il, kb) =>
            exists a n kc, In (a, n, kc) cands /\ sub_get th' ia = Some a /\ sub_get th' il = Some n /\ bsub_get tb' kb = Some (BVar kc) end) bb.
Proof.
  induction bb as [|[[ia il] kb] bb IH]; intros cands th tb k th' tb' H; cbn [bind_bytes] in H.
  - destruct (k th) eqn:K; [|discriminate]. injection H; intros <- <-.
    split; [apply thsub_refl|]. split; [apply tbsub_refl|]. split; [exact K| constructor].
  - lazymatch goal with |- ?G =>
    lazymatch type of H with ?F cands = ?R =>
      enough (GEN : forall cs, (forall x, In x cs -> In x cands) -> F cs = R -> G) by (apply (GEN cands); [intros x Hx; exact Hx| exact H])
    end end.
    clear H. induction cs as [|[[a n] kc] cs IHc]; intros INCL H; [discriminate|].
    cbn in H. destruct (bsub_get tb kb) eqn:BG; [discriminate|].
    assert (INCL' : forall x, In x cs -> In x cands) by (intros x Hx; apply INCL; right; exact Hx).
    destruct (bind th ia a) as [th1|] eqn:B1; [|apply IHc; assumption].
    destruct (bind th1 il n) as [th2|] eqn:B2; [|apply IHc; assumption].
    destruct (bind_bytes bb cands th2 ((kb, BVar kc) :: tb) k) as [[th3 tb3]|] eqn:BB; [|apply IHc; assumption].
    injection H; intros <- <-.
    destruct (bind_ok _ _ _ _ B1) as [G1 S1]. destruct (bind_ok _ _ _ _ B2) as [G2 S2].
    destruct (IH _ _ _ _ _ _ BB) as (S3 & T3 & K3 & F3).
    split; [eapply thsub_trans; [|exact S3]; eapply thsub_trans; eauto|].
    split. { intros kb2 k2 Hk. apply T3. cbn. destruct (Pos.eqb_spec kb2 kb) as [->|]; [rewrite BG in Hk; discriminate| exact Hk]. }
    split; [exact K3|]. constructor; [|exact F3].
    exists a, n, kc. split; [apply INCL; left; reflexivity|].
    split; [apply S3, S2; exact G1|]. split; [apply S3; exact G2|]. apply T3. cbn. rewrite Pos.eqb_refl. reflexivity.
Qed.

Lemma all_bound_ok : forall th n i j, all_bound th n i = true -> (i <= j)%positive -> (Pos.to_nat j < Pos.to_nat i + n)%nat -> sub_get th j <> None.
Proof.
  intros th n. induction n as [|n IH]; intros i j H Hij Hj; [lia|]. cbn in H.
  destruct (sub_get th i) as [e|] eqn:G; [|discriminate].
  destruct (Pos.eq_dec i j) as [<-|NE]; [rewrite G; discriminate|].
  apply (IH (Pos.succ i)); [exact H| lia| lia].
Qed.

Lemma all_bbound_ok : forall tb n i j, all_bbound tb n i = true -> (i <= j)%positive -> (Pos.to_nat j < Pos.to_nat i + n)%nat -> bsub_get tb j <> None.
Proof.
  intros tb n. induction n as [|n IH]; intros i j H Hij Hj; [lia|]. cbn in H.
  destruct (bsub_get tb i) as [e|] eqn:G; [|discriminate].
  destruct (Pos.eq_dec i j) as [<-|NE]; [rewrite G; discriminate|].
  apply (IH (Pos.succ i)); [exact H| lia| lia].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Decide.
  Variable CS : Z -> Prop.
  Variable E : env.
  Notation nonneg := (fun e : expr => 0 <= zden E e).
  Notation pfok := (pfact_ok CS E).

  Definition gcs_ok (gcs : list (list expr)) : Prop := Exists (fun gc => Forall nonneg gc) gcs.

  Lemma goal_case_ok_sound : forall pf gc, Forall pfok pf -> goal_case_ok pf gc = true -> Forall nonneg gc.
  Proof.
    intros pf gc HP H. unfold goal_case_ok in H. apply List.Forall_forall. intros e He.
    rewrite lforallb_forall in H. apply (lin_ge_sound CS E pf e HP). apply H. exact He.
  Qed.

  Lemma hyp_cases_sound : forall h, pfok h -> hyp_cases h <> [] -> Exists (fun hc => Forall pfok hc) (hyp_cases h).
  Proof.
    intros h Hh NE. destruct h; cbn in NE |- *; try congruence; cbn in Hh; rewrite !zdenp_ok in Hh.
    - destruct Hh as [Hl|Hr].
      + apply Exists_cons_hd. constructor; [|constructor]. cbn. rewrite zdenp_ok, sep_l_den. lia.
      + apply Exists_cons_tl, Exists_cons_hd. constructor; [|constructor]. cbn. rewrite zdenp_ok, sep_r_den. lia.
    - destruct Hh as [Hz|[Hl|Hr]].
      + apply Exists_cons_hd. constructor; [cbn; rewrite zdenp_ok; lia|]. constructor; [|constructor]. cbn. rewrite zdenp_ok, emulc_den. lia.
      + apply Exists_cons_tl, Exists_cons_hd. constructor; [|constructor]. cbn. rewrite zdenp_ok, sep_l_den. lia.
      + apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. constructor; [|constructor]. cbn. rewrite zdenp_ok, sep_r_den. lia.
  Qed.

  Lemma goal_case_ok0_sound : forall pf gc, Forall pfok pf -> goal_case_ok0 pf gc = true -> Forall nonneg gc.
  Proof.
    intros pf gc HP H. unfold goal_case_ok0 in H. apply List.Forall_forall. intros e He.
    rewrite lforallb_forall in H. apply (lin_ge0_sound CS E pf e HP). apply H. exact He.
  Qed.

  Lemma goal_case_ok00_sound : forall pf gc, Forall pfok pf -> goal_case_ok00 pf gc = true -> Forall nonneg gc.
  Proof.
    intros pf gc HP H. unfold goal_case_ok00 in H. apply List.Forall_forall. intros e He.
    rewrite lforallb_forall in H. apply (lin_ge00_sound CS E pf e HP). apply H. exact He.
  Qed.

  Lemma goal_case_okS_sound : forall pf gc, Forall pfok pf -> goal_case_okS pf gc = true -> Forall nonneg gc.
  Proof.
    intros pf gc HP H. unfold goal_case_okS in H. apply List.Forall_forall. intros e He.
    rewrite lforallb_forall in H. apply (lin_geS_sound CS E pf e HP). apply H. exact He.
  Qed.

  Lemma ins_ranked_In : forall sc h l x, In x (ins_ranked sc h l) -> x = (sc, h) \/ In x l.
  Proof.
    induction l as [|[sc' h'] l IH]; cbn -[Nat.ltb].
    - intros x [<-|[]]. left; reflexivity.
    - destruct (Nat.ltb sc' sc); cbn -[Nat.ltb]; intros x Hx.
      + destruct Hx as [<-|Hx]; [left; reflexivity| right; exact Hx].
      + destruct Hx as [<-|Hx]; [right; left; reflexivity|]. destruct (IH _ Hx) as [->|X]; [left; reflexivity| right; right; exact X].
  Qed.
  Lemma rank_hyps_In : forall ga pf acc sh, In sh (rank_hyps ga pf acc) -> In (snd sh) pf \/ In sh acc.
  Proof.
    induction pf as [|h pf IH]; cbn; intros acc sh Hin; [right; exact Hin|].
    destruct (IH _ _ Hin) as [X|X]; [left; right; exact X|].
    destruct (sep_rel ga h); [|right; exact X].
    apply ins_ranked_In in X as [->|X]; [left; left; reflexivity| right; exact X].
  Qed.

  Lemma rank_hyps2_In : forall ga0 ga pf acc sh, In sh (rank_hyps2 ga0 ga pf acc) -> In (snd sh) pf \/ In sh acc.
  Proof.
    intros ga0 ga pf. unfold rank_hyps2. induction pf as [|h pf IH]; cbn; intros acc sh Hin; [right; exact Hin|].
    destruct (IH _ _ Hin) as [X|X]; [left; right; exact X|].
    destruct (sep_rel ga h); [|right; exact X].
    apply ins_ranked_In in X as [->|X]; [left; left; reflexivity| right; exact X].
  Qed.
  Lemma singletons_sound : forall gcs gs, singletons gcs = Some gs -> Exists nonneg gs -> gcs_ok gcs.
  Proof.
    induction gcs as [|gc gcs IH]; intros gs H X; cbn in H.
    - injection H; intros <-. inversion X.
    - destruct gc as [|g [|g' gc']]; try discriminate.
      destruct (singletons gcs) as [gs'|] eqn:S; [|discriminate]. injection H; intros <-.
      apply Exists_cons in X. destruct X as [X|X].
      + apply Exists_cons_hd. constructor; [exact X| constructor].
      + apply Exists_cons_tl. apply (IH gs' eq_refl X).
  Qed.
  Lemma gcs_probe_sound : forall deep pf gcs, Forall pfok pf -> gcs_probe deep pf gcs = true -> gcs_ok gcs.
  Proof.
    intros deep pf gcs HP H. unfold gcs_probe in H.
    destruct (singletons gcs) as [gs|] eqn:S.
    - apply (singletons_sound gcs gs S). exact (lin_ge_fm_sound CS E deep pf gs HP H).
    - apply lexistsb_exists in H as (gc & Hin & Hgc). apply Exists_exists. exists gc. split; [exact Hin|].
      apply List.Forall_forall. intros e He. rewrite lforallb_forall in Hgc. specialize (Hgc e He).
      apply (lin_ge_fm_sound CS E deep pf [e] HP) in Hgc. inversion Hgc; subst; [assumption|]. inversion H0.
  Qed.
  Lemma rank_hypsA_In : forall ga0 ga pf sh, In sh (rank_hypsA ga0 ga pf) -> In (snd sh) pf.
  Proof.
    intros ga0 ga pf. unfold rank_hypsA.
    assert (GEN : forall acc sh, In sh ((fix go (pf0 : list pfact) (acc0 : list (nat * pfact)) {struct pf0} : list (nat * pfact) :=
               match pf0 with
               | [] => acc0
               | h :: pf' => go pf' match hyp_cases h with [] => acc0 | _ :: _ => ins_ranked (8 * hyp_score ga0 h + hyp_score ga h) h acc0 end
               end) pf acc) -> In (snd sh) pf \/ In sh acc).
    { induction pf as [|h pf IH]; cbn; intros acc sh Hin; [right; exact Hin|].
      destruct (IH _ _ Hin) as [X|X]; [left; right; exact X|].
      destruct (hyp_cases h); [right; exact X|].
      apply ins_ranked_In in X as [->|X]; [left; left; reflexivity| right; exact X]. }
    intros sh Hin. destruct (GEN [] sh Hin) as [X|[]]. exact X.
  Qed.
  Lemma casewise_sound : forall all gprobe pf gcs,
    (forall pf', Forall pfok pf' -> gprobe pf' gcs = true -> gcs_ok gcs) ->
    Forall pfok pf -> casewise_gen all gprobe pf gcs = true -> gcs_ok gcs.
  Proof.
    intros all gprobe pf gcs GC HP H. unfold casewise_gen in H.
    apply lexistsb_exists in H as (sh & Hsh & Hc). rewrite List.Forall_forall in HP.
    assert (Hh : In (snd sh) pf) by (destruct all; [exact (rank_hypsA_In _ _ _ _ Hsh)| apply rank_hyps2_In in Hsh as [Hh|[]]; exact Hh]).
    clear Hsh. set (h := snd sh) in *. pose proof (HP h Hh) as Ph.
      destruct (hyp_cases h) as [|hc0 hcs] eqn:HC; [discriminate|].
      pose proof (hyp_cases_sound h Ph ltac:(rewrite HC; discriminate)) as X. rewrite HC in X.
      apply Exists_exists in X as (hc & Hin & Hhc).
      rewrite lforallb_forall in Hc. specialize (Hc hc Hin).
      eapply GC; [|exact Hc]. apply Forall_app. split; [exact Hhc|]. apply List.Forall_forall. exact HP.
  Qed.
  Lemma dec_disj_by_sound : forall gdir gcase pf gcs,
    (forall pf' gc, Forall pfok pf' -> gdir pf' gc = true -> Forall nonneg gc) ->
    (forall pf' gc, Forall pfok pf' -> gcase pf' gc = true -> Forall nonneg gc) ->
    Forall pfok pf -> dec_disj_by gdir gcase pf gcs = true -> gcs_ok gcs.
  Proof.
    intros gdir gcase pf gcs GD GC HP H. unfold dec_disj_by in H.
    destruct (lexistsb (gdir pf) gcs) eqn:D1.
    - apply lexistsb_exists in D1 as (gc & Hin & Hgc). apply Exists_exists. exists gc. split; [exact Hin| eapply GD; eauto].
    - eapply (casewise_sound false _ pf gcs); [|exact HP| exact H]. cbn beta. intros pf' HP' X.
      apply lexistsb_exists in X as (gc & Hgin & Hgc). apply Exists_exists. exists gc. split; [exact Hgin| eapply GC; eauto].
  Qed.
  Lemma dec_disj_cheap_sound : forall pf gcs, Forall pfok pf -> dec_disj_cheap pf gcs = true -> gcs_ok gcs.
  Proof.
    intros pf gcs HP H. unfold dec_disj_cheap in H.
    destruct (gcs_probe false pf gcs) eqn:D1.
    - exact (gcs_probe_sound false pf gcs HP D1).
    - eapply (casewise_sound false _ pf gcs); [|exact HP| exact H]. intros pf' HP' X. exact (gcs_probe_sound false pf' gcs HP' X).
  Qed.
  Lemma dec_disj_rest_sound : forall pf gcs, Forall pfok pf -> dec_disj_rest pf gcs = true -> gcs_ok gcs.
  Proof.
    intros pf gcs HP H. unfold dec_disj_rest in H.
    destruct (gcs_probe true pf gcs) eqn:D1.
    - exact (gcs_probe_sound true pf gcs HP D1).
    - destruct (dec_disj_by goal_case_okS goal_case_ok pf gcs) eqn:D2.
      + exact (dec_disj_by_sound _ _ pf gcs goal_case_okS_sound goal_case_ok_sound HP D2).
      + eapply (casewise_sound true _ pf gcs); [|exact HP| exact H]. intros pf' HP' X. exact (gcs_probe_sound true pf' gcs HP' X).
  Qed.
  Lemma dec_disj_sound : forall pf gcs, Forall pfok pf -> dec_disj pf gcs = true -> gcs_ok gcs.
  Proof.
    intros pf gcs HP H. unfold dec_disj in H.
    destruct (dec_disj_cheap pf gcs) eqn:D0.
    - exact (dec_disj_cheap_sound pf gcs HP D0).
    - exact (dec_disj_rest_sound pf gcs HP H).
  Qed.

  Lemma gcs1 : forall e gcs, gcs_ok ([e] :: gcs) -> 0 <= zden E e \/ gcs_ok gcs.
  Proof. intros e gcs H. apply Exists_cons in H. destruct H as [H|H]; [left; inversion H; assumption| right; exact H]. Qed.
  Lemma gcs2 : forall e1 e2 gcs, gcs_ok ([e1; e2] :: gcs) -> (0 <= zden E e1 /\ 0 <= zden E e2) \/ gcs_ok gcs.
  Proof. intros e1 e2 gcs H. apply Exists_cons in H. destruct H as [H|H]; [left; inversion H; inversion H3; split; assumption| right; exact H]. Qed.
  Lemma gcs0 : gcs_ok [] -> False.
  Proof. intros H. inversion H. Qed.

  Lemma pf_decide_sound : forall pf crs O f,
    Forall pfok pf -> Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) crs -> osound E O ->
    pf_decide pf crs O f = true -> pfok f.
  Proof.
    intros pf crs O f HP CR HO H. unfold pf_decide in H.
    destruct (pf_mem f pf) eqn:PM.
    { apply pf_mem_In in PM. rewrite List.Forall_forall in HP. apply HP. exact PM. }
    destruct f; cbn -[Z.pow Z.of_N]; rewrite ?zdenp_ok; try discriminate.
    - apply (lin_ge_sound CS E pf); assumption.
    - apply (dec_disj_sound pf) in H; [|exact HP]. apply gcs1 in H as [H|H]; [rewrite sep_l_den in H; lia|].
      apply gcs1 in H as [H|H]; [rewrite sep_r_den in H; lia| destruct (gcs0 H)].
    - apply (dec_disj_sound pf) in H; [|exact HP]. apply gcs2 in H as [[H1 H2]|H]; [rewrite emulc_den in H1; lia|].
      apply gcs1 in H as [H|H]; [rewrite sep_l_den in H; lia|].
      apply gcs1 in H as [H|H]; [rewrite sep_r_den in H; lia| destruct (gcs0 H)].
    - apply N.leb_le in H. apply (eal_mod E O); assumption.
    - apply (in_some_crange_sound CS E pf crs); assumption.
    - apply (dec_le_sound CS E pf); assumption.
    - apply (dec_lt_sound CS E pf); assumption.
    - apply (dec_eq_sound CS E pf); assumption.
    - apply (dec_disj_sound pf) in H; [|exact HP]. apply gcs1 in H as [H|H]; [rewrite eadd_den, emulc_den in H; lia|].
      apply gcs1 in H as [H|H]; [rewrite eadd_den, emulc_den in H; lia| destruct (gcs0 H)].
    - apply (dec_disj_sound pf) in H; [|exact HP]. apply gcs2 in H as [[H1 H2]|H]; [rewrite emulc_den in H1; lia|].
      apply gcs1 in H as [H|H]; [rewrite eadd_den, emulc_den in H; lia|].
      apply gcs1 in H as [H|H]; [rewrite eadd_den, emulc_den in H; lia| destruct (gcs0 H)].
  Qed.
End Decide.

Section Survive.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variable C : lxcfg.
  Variables m m' : mem.
  Variable pf : list pfact.
  Variable W : list (expr * expr).
  Hypothesis HP : Forall (pfact_ok CS E) pf.
  Hypothesis HACC : forall A, c_acc C = Some A -> ac_got A = al_got L /\ ac_gsb A = al_gsb L /\ cs_ok L CS.
  Hypothesis HSB : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb L.
  Variable crs : list (expr * expr).
  Hypothesis HCR : Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) crs.
  Hypothesis MU : munch (wden E W) m m'.
  Hypothesis WM : wmono segs m m'.
  Hypothesis MI' : mem_inv segs m'.
  Hypothesis HPF : hp_frame segs (ehp E) (ecw E).   (* [comment removed for export] *)
  Hypothesis HBK : hp_blk (ecw E).

  Lemma dec_apartS_sound : forall lo hi b sz, dec_apartS pf lo hi b sz = true ->
    zden E b + zden E sz <= zden E lo \/ zden E hi <= zden E b.
  Proof.
    intros lo hi b sz H. unfold dec_apartS in H.
    destruct (overlap0 true pf lo hi b sz false); [discriminate|].
    destruct (sep_lookup false pf lo (eadd hi (emulc (-1) lo)) b sz) eqn:SL.
    { destruct (sep_lookup_sound CS E false pf _ _ _ _ HP SL) as [[X _]|X]; [discriminate|]. rewrite eadd_den, emulc_den in X. lia. }
    destruct (dec_disj_cheap pf _) eqn:DC.
    { apply (dec_disj_cheap_sound CS E pf) in DC; [|exact HP].
      apply gcs1 in DC as [X|DC]; [rewrite sep_l_den, eadd_den, emulc_den in X; lia|].
      apply gcs1 in DC as [X|DC]; [rewrite sep_r_den in X; lia| destruct (gcs0 _ DC)]. }
    destruct (overlap0 false pf lo hi b sz false); [discriminate|].
    unfold dec_apart_rest in H. apply (lin_ge_list2_sound CS E) in H; [|exact HP].
    apply Exists_cons in H. destruct H as [H|H]; [rewrite sep_l_den, eadd_den, emulc_den in H; lia|].
    apply Exists_cons in H. destruct H as [H|H]; [rewrite sep_r_den in H; lia| apply Exists_nil in H; contradiction].
  Qed.
  Lemma dec_apart0S_sound : forall lo hi b sz, dec_apart0S pf lo hi b sz = true ->
    zden E sz <= 0 \/ zden E b + zden E sz <= zden E lo \/ zden E hi <= zden E b.
  Proof.
    intros lo hi b sz H. unfold dec_apart0S in H.
    destruct (overlap0 true pf lo hi b sz true); [discriminate|].
    destruct (sep_lookup false pf lo (eadd hi (emulc (-1) lo)) b sz) eqn:SL.
    { destruct (sep_lookup_sound CS E false pf _ _ _ _ HP SL) as [[X _]|X]; [discriminate|]. rewrite eadd_den, emulc_den in X. lia. }
    assert (G : gcs_ok E [[sep_l lo (eadd hi (emulc (-1) lo)) b]; [sep_r lo b sz]; [emulc (-1) sz]] ->
                zden E sz <= 0 \/ zden E b + zden E sz <= zden E lo \/ zden E hi <= zden E b).
    { intros X. apply gcs1 in X as [X|X]; [rewrite sep_l_den, eadd_den, emulc_den in X; lia|].
      apply gcs1 in X as [X|X]; [rewrite sep_r_den in X; lia|].
      apply gcs1 in X as [X|X]; [rewrite emulc_den in X; lia| destruct (gcs0 _ X)]. }
    destruct (dec_disj_cheap pf _) eqn:DC.
    { apply G. apply (dec_disj_cheap_sound CS E pf); [exact HP| exact DC]. }
    destruct (overlap0 false pf lo hi b sz true); [discriminate|].
    apply G. apply (dec_disj_rest_sound CS E pf); [exact HP| exact H].
  Qed.

  Lemma all_apart_sound : forall W' b sz, all_apart pf W' b sz = true -> disjoint_from (wden E W') (zden E b) (zden E sz).
  Proof.
    induction W' as [|[lo hi] W' IH]; cbn -[dec_apartS eadd emulc]; intros b sz H; [exact I|].
    destruct (dec_apartS pf lo hi b sz) eqn:H1; [|discriminate].
    apply dec_apartS_sound in H1. rewrite !zdenp_ok. split; [lia| apply IH; exact H].
  Qed.

  Lemma all_apart0_sound : forall W' b sz, all_apart0 pf W' b sz = true -> zden E sz <= 0 \/ disjoint_from (wden E W') (zden E b) (zden E sz).
  Proof.
    induction W' as [|[lo hi] W' IH]; cbn -[dec_apart0S eadd emulc]; intros b sz H; [right; exact I|].
    destruct (dec_apart0S pf lo hi b sz) eqn:H1; [|discriminate].
    apply dec_apart0S_sound in H1.
    destruct (IH _ _ H) as [Z0|D]; [left; exact Z0|].
    destruct H1 as [H1|[H1|H1]]; [left; exact H1| right | right]; rewrite !zdenp_ok; split; [lia| exact D| lia| exact D].
  Qed.

  Lemma w_all_client_sound : forall W',
    w_all_client pf crs W' = true -> w_client CS (wden E W').
  Proof.
    intros W'. induction W' as [|[lo hi] W' IH]; cbn; intros H; [constructor|].
    apply andb_prop in H as [H1 H2]. constructor; [|apply IH; exact H2]. cbn [fst snd]. rewrite !zdenp_ok.
    apply (in_some_crange_sound CS E pf crs) in H1; [|exact HP| exact HCR]. rewrite eadd_den, emulc_den in H1.
    replace (zden E hi - zden E lo) with (zden E hi + -1 * zden E lo) by lia. exact H1.
  Qed.

  Lemma all_nonempty_sound : forall W', all_nonempty pf W' = true -> Forall (fun iv => fst iv < snd iv) (wden E W').
  Proof.
    induction W' as [|[lo hi] W' IH]; cbn; intros H; [constructor|].
    apply andb_prop in H as [H1 H2]. constructor; [|apply IH; exact H2]. cbn [fst snd]. rewrite !zdenp_ok.
    apply (dec_lt_sound CS E pf); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma hpr_munch_ok : forall mf0 W0 m1 m2 qj qo qn qxs qok,
    Forall (mfact_ok segs L CS E m1) mf0 -> munch (wden E W0) m1 m2 -> wmono segs m1 m2 -> mem_inv segs m2 ->
    lforallb (fun lh => hpr_iv_ok pf mf0 qo qn qok (fst lh) (eadd (snd lh) (emulc (-1) (fst lh)))) W0 = true ->
    mfact_ok segs L CS E m1 (MHpr qj qo qn qxs qok) -> mfact_ok segs L CS E m2 (MHpr qj qo qn qxs qok).
  Proof.
    intros mf0 W0 m1 m2 qj qo qn qxs qok HM0 MU0 WM0 MI2 H Hf.
    destruct Hf as [HR (HOK & HBK' & HCW & HI0 & HI1)]. split; [| exact (conj HOK (conj HBK' (conj HCW (conj HI0 HI1))))].
    apply (HOK _ _ _ m1 _ HR MI2). intros x Hx HIN HNCW. rewrite lforallb_forall in H.
    assert (OUTG : forall W1, (forall lh, In lh W1 -> hpr_iv_ok pf mf0 qo qn qok (fst lh) (eadd (snd lh) (emulc (-1) (fst lh))) = true) ->
                              outside (wden E W1) x).
    { clear HR H MU0. induction W1 as [|[lo hi] W1 IH]; cbn; intros HW; [exact I|]. split.
      - pose proof (hpr_iv_ok_out segs L CS E m1 pf mf0 qo qn qok lo (eadd hi (emulc (-1) lo)) x HP HM0 HBK' HCW HI0
                      (HW (lo, hi) (or_introl eq_refl)) HIN HNCW) as X. rewrite eadd_den, emulc_den in X. rewrite !zdenp_ok. lia.
      - apply IH. intros lh Hlh. apply HW. right. exact Hlh. }
    pose proof (OUTG W0 H) as OUT.
    split; [| intros V; apply WM0; exact V].
    pose proof (MU0 (wa x)) as X. rewrite wa_unsigned in X by lia. exact (X OUT).
  Qed.

  Lemma mf_survives_call_sound : forall (wcl wne : bool) mf0 f,
    Forall (mfact_ok segs L CS E m) mf0 ->
    (wcl = true -> w_client CS (wden E W)) -> (wne = true -> Forall (fun iv => fst iv < snd iv) (wden E W)) ->
    mfact_ok segs L CS E m f -> mf_survives_call C pf crs mf0 W wcl wne f = true -> mfact_ok segs L CS E m' f.
  Proof.
    intros wcl wne mf0 f HM0 WCL0 WNE0 Hf H.
    assert (WCL : wcl && wne = true -> w_client CS (wden E W) /\ Forall (fun iv => fst iv < snd iv) (wden E W)).
    { intros X. apply andb_prop in X as [X1 X2]. split; [exact (WCL0 X1)| exact (WNE0 X2)]. } destruct f as [b cs|b cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok].
    6:{ (* [comment removed for export] *)
        cbn [mfact_ok] in Hf |- *. cbn [mf_survives_call] in H. destruct Hf as [HPm LAW]. split; [|exact LAW].
        apply (LAW (wden E W) m m' HPm MU WM). unfold wden. apply List.Forall_forall. intros iv Hiv.
        apply in_map_iff in Hiv as ([l h] & <- & Hin). rewrite lforallb_forall in H. specialize (H _ Hin). cbn [fst snd] in H |- *.
        pose proof (opq_iv_ok_sound L CS E C HACC HSB pf crs l (eadd h (emulc (-1) l)) ok_l sh_l HP HCR H) as X.
        rewrite eadd_den, emulc_den in X. rewrite !zdenp_ok. replace (zden E h) with (zden E l + (zden E h + -1 * zden E l)) by lia. exact X. }
    6:{ (* [comment removed for export] *)
        cbn [mf_survives_call] in H. apply all_apart0_sound in H. rewrite emulc_den in H.
        eapply (marr_transport segs L CS E m m'); [exact Hf| exact MU| exact WM|].
        destruct H as [H|H]; [left| right; exact H].
        destruct (marr_cases rw_) as [-> |[-> |[-> |(N1 & N4 & N8)]]]; cbn [Z.of_N] in H; try lia.
        exfalso. cbn in Hf. destruct rw_ as [|p]; [exact Hf|]. repeat (destruct p as [p|p|]; try exact (proj1 Hf); try exact Hf; try congruence). }
    6-10: exact Hf.   (* [comment removed for export] *)
    7-10: exact Hf.   (* [comment removed for export] *)
    6:{ (* [comment removed for export] *)
        cbn [mfact_ok] in Hf |- *. cbn [mf_survives_call] in H. destruct Hf as [[HPm HCW] HREST]. split; [|exact HREST]. split; [|exact HCW].
        apply (HPF (blden E qbl) m m' (ecur E) (wden E W) HPm MU WM). unfold wden at 1. apply List.Forall_forall. intros iv Hiv x Hx.
        apply in_map_iff in Hiv as ([l h] & <- & Hin). rewrite lforallb_forall in H. specialize (H _ Hin). cbn [fst snd] in H, Hx.
        pose proof (opq_iv_ok_sound L CS E C HACC HSB pf crs l (eadd h (emulc (-1) l)) qok [] HP HCR H) as X.
        rewrite eadd_den, emulc_den in X. rewrite !zdenp_ok in Hx.
        replace (zden E l + (zden E h + -1 * zden E l)) with (zden E h) in X by lia.
        destruct X as [(lo & hi & Hin' & Hlo & Hhi)|X]; [cbn [fst snd] in Hlo, Hhi|].
        - rewrite List.Forall_forall in HCW. apply (HCW (lo, hi) Hin'); [cbn [fst snd]; lia| exact (proj1 HREST)].
        - exfalso. destruct (X x ltac:(cbn [fst snd]; lia)) as (c & lo & hi & [] & _). }
    6:{ (* [comment removed for export] *) cbn [mf_survives_call] in H. exact (hpr_munch_ok mf0 W m m' _ _ _ _ _ HM0 MU WM MI' H Hf). }
    all: cbn in Hf, H |- *; rewrite ?zdenp_ok in Hf |- *.
    - eapply rw_cells_transport; [exact Hf| exact MU| exact WM|]. rewrite csden_size. replace (Z.of_nat (N.to_nat (cells_sizeN cs))) with (Z.of_N (cells_sizeN cs)) by lia.
      destruct (all_apart pf W b (ELit (Z.of_N (cells_sizeN cs)))) eqn:AP.
      + apply all_apart_sound in AP. cbn [zden] in AP. exact AP.
      + (* [comment removed for export] *)
        apply andb_prop in H as [H CA]. apply andb_prop in H as [WC POS]. apply Z.ltb_lt in POS. destruct (WCL WC) as [HWC HNE]. clear AP WCL.
        assert (GEN : forall W', w_client CS (wden E W') -> Forall (fun iv => fst iv < snd iv) (wden E W') ->
                                 disjoint_from (wden E W') (zden E b) (Z.of_N (cells_sizeN cs))).
        { induction W' as [|[lo hi] W' IH]; cbn; intros HW HL; [exact I|].
          inversion HW; subst. inversion HL; subst. cbn [fst snd] in *. rewrite !zdenp_ok in *. split; [|apply IH; assumption].
          assert (PW : forall z y, zden E lo <= z < zden E lo + (zden E hi - zden E lo) ->
                                   zden E b <= y < zden E b + zden E (ELit (Z.of_N (cells_sizeN cs))) -> z <> y).
          { apply (class_apart_sound L CS E C HACC HSB pf crs AcClient lo (zden E hi - zden E lo) b _ HP HCR); [|exact CA]. cbn. assumption. }
          cbn [zden] in PW. pose proof (pointwise_apart (zden E lo) (zden E hi - zden E lo) (zden E b) (Z.of_N (cells_sizeN cs)) ltac:(lia) POS PW). lia. }
        apply GEN; assumption.
    - assert (AP : all_apart pf W b (ELit (Z.of_N (cells_sizeN cs))) = true -> ro_cells segs m' (zden E b) (csden E cs)).
      { intros HA. apply all_apart_sound in HA. cbn [zden] in HA. eapply ro_cells_transport; [exact Hf| exact MU|]. rewrite csden_size.
        replace (Z.of_nat (N.to_nat (cells_sizeN cs))) with (Z.of_N (cells_sizeN cs)) by lia. exact HA. }
      destruct (wcl && wne && is_static C b && N.eqb (cells_sizeN cs) 8) eqn:ST; [|exact (AP H)]. clear H.
      apply andb_prop in ST as [ST S8]. apply andb_prop in ST as [WC IS]. apply N.eqb_eq in S8. destruct (WCL WC) as [HWC HNE].
      unfold is_static in IS. destruct (c_acc C) as [A|] eqn:HCA; [|discriminate]. destruct (is_lit b) as [z|] eqn:LB; [|discriminate].
      apply is_lit_den with (E := E) in LB. destruct (HACC A eq_refl) as (G1 & G2 & CSOK).
      eapply ro_cells_transport; [exact Hf| exact MU|]. rewrite csden_size, S8. cbn [N.to_nat Z.of_nat Pos.to_nat Pos.iter_op Nat.add Pos.of_succ_nat].
      destruct CSOK as (_ & C2 & _).
      apply (disjoint_of_cs CS); [exact HWC| exact HNE|]. intros i Hi. rewrite LB.
      apply orb_prop in IS as [IS|IS]; apply Z.eqb_eq in IS; rewrite IS; [rewrite G1; exact (proj1 (C2 i Hi))| rewrite G2; exact (proj2 (C2 i Hi))].
    - destruct Hf as [HB HL]. split; [|exact HL]. apply all_apart0_sound in H. destruct H as [Z0|D].
      + assert (eb E k = []) as -> by (destruct (eb E k); [reflexivity| cbn in HL; lia]).
        pose proof (bytes_at_bound _ _ _ _ HB). apply bytes_at_nil_any; cbn in *; lia.
      + eapply bytes_at_transport; [exact HB| exact MU|]. rewrite HL. exact D.
    - apply all_apart_sound in H. rewrite eadd_den, emulc_den in H.
      eapply stk_transport_disjoint; [exact Hf| exact MU| exact WM|]. replace (zden E hi - zden E lo) with (zden E hi + -1 * zden E lo) by lia. exact H.
    - destruct (c_acc C) as [A|] eqn:HCA; [|discriminate]. pose proof (WCL0 H) as HWC. destruct (HACC A eq_refl) as (_ & _ & CSOK).
      eapply (aobj_munch segs L CS CSOK); [exact HWC| exact MU| exact Hf].
  Qed.
End Survive.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section PAgree.
  Variable segs : list Segment.
  Definition pagree (a n : Z) (m m' : mem) : Prop :=
    forall x, a <= x < a + n -> 0 <= x < 2 ^ 64 -> m' (wa x) = m (wa x) /\ (wview segs m (wa x) <> None -> wview segs m' (wa x) <> None).

  Lemma pagree_sub : forall a n b k m m', pagree a n m m' -> a <= b -> b + k <= a + n -> pagree b k m m'.
  Proof. intros a n b k m m' H H1 H2 x Hx HR. apply H; lia. Qed.
  Lemma bytes_at_agree : forall m m' A bs, bytes_at segs m A bs -> pagree A (Z.of_nat (length bs)) m m' -> bytes_at segs m' A bs.
  Proof.
    intros m m' A bs (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    destruct (AG (A + Z.of_nat i) ltac:(lia) ltac:(lia)) as [X _]. rewrite X. reflexivity.
  Qed.
  Lemma wr_at_agree : forall m m' A n, wr_at segs m A n -> pagree A n m m' -> wr_at segs m' A n.
  Proof.
    intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    destruct (AG (A + i) ltac:(lia) ltac:(lia)) as [_ X]. apply X, HW, Hi.
  Qed.
  Lemma rw_cells_agree : forall m m' A cs, rw_cells segs m A cs -> pagree A (Z.of_nat (cells_size cs)) m m' -> rw_cells segs m' A cs.
  Proof.
    intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
    - eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
    - eapply wr_at_agree; [exact HW| exact AG].
  Qed.
  Lemma ro_cells_agree : forall m m' A cs, ro_cells segs m A cs -> pagree A (Z.of_nat (cells_size cs)) m m' -> ro_cells segs m' A cs.
  Proof.
    intros m m' A cs [Hwf HB] AG. split; [exact Hwf|]. eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  Qed.
  Lemma stk_agree : forall m m' lo hi, stk segs m lo hi -> pagree lo (hi - lo) m m' -> stk segs m' lo hi.
  Proof.
    intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|]. intros a Ha.
    destruct (HS a Ha) as [HW [b Hb]]. destruct (AG a ltac:(lia) ltac:(lia)) as [X Y].
    split; [apply Y, HW|]. exists b. unfold mrd in Hb |- *. rewrite X. exact Hb.
  Qed.
  Lemma marr_agree : forall L CS E m m' a w l n wr,
    mfact_ok segs L CS E m (MArr a w l n wr) -> pagree (zden E a) (Z.of_N w * zden E n) m m' -> mfact_ok segs L CS E m' (MArr a w l n wr).
  Proof.
    intros L CS E m m' a w l n wr Hf AG.
    destruct (marr_cases w) as [-> |[-> |[-> | (N1 & N4 & N8)]]].
    - cbn -[u8arr bytes_at ldenb Z.of_nat Z.mul Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *. destruct Hf as [H HL]. split; [|exact HL].
      destruct wr; [destruct H as [HB HW]; split|]; [eapply bytes_at_agree| eapply wr_at_agree| eapply bytes_at_agree]; try eassumption;
        (eapply pagree_sub; [exact AG| lia| lia]).
    - cbn -[u32arr bytes_at ldenw u32s Z.of_nat Z.mul Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *. destruct Hf as [H HL]. split; [|exact HL].
      destruct wr; [destruct H as [HB HW]; split|]; [eapply bytes_at_agree| eapply wr_at_agree| eapply bytes_at_agree]; try eassumption;
        (eapply pagree_sub; [exact AG| lia| rewrite ?u32s_length; lia]).
    - cbn -[u64arr bytes_at ldenw u64s Z.of_nat Z.mul Z.pow] in Hf |- *. rewrite ?zdenp_ok in Hf |- *. destruct Hf as [H HL]. split; [|exact HL].
      destruct wr; [destruct H as [HB HW]; split|]; [eapply bytes_at_agree| eapply wr_at_agree| eapply bytes_at_agree]; try eassumption;
        (eapply pagree_sub; [exact AG| lia| rewrite ?u64s_length; lia]).
    - exfalso. cbn in Hf. destruct w as [|p]; [exact Hf|]. repeat (destruct p as [p|p|]; try exact (proj1 Hf); try exact Hf; try congruence).
  Qed.
End PAgree.

(* [comment removed for export] *)
Section SurviveL.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variable C : lxcfg.
  Variables m m' : mem.
  Variable pf : list pfact.
  Variable mf : list mfact.
  Variable W : list (expr * expr).
  Variable l : nat.
  Variable dp : bool.
  Hypothesis HP : Forall (pfact_ok CS E) pf.
  Hypothesis HM : Forall (mfact_ok segs L CS E m) mf.
  Hypothesis LAW : elaw E l (wden E W) m m'.
  Hypothesis HACC : forall A, c_acc C = Some A -> ac_got A = al_got L /\ ac_gsb A = al_gsb L /\ cs_ok L CS.
  Hypothesis HSB : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb L.
  Variable crs : list (expr * expr).
  Hypothesis HCR : Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) crs.
  Variables wcl wne : bool.
  Hypothesis WCL0 : wcl = true -> w_client CS (wden E W).
  Hypothesis WNE0 : wne = true -> Forall (fun iv => fst iv < snd iv) (wden E W).

  Lemma tag_covers_sound : forall obj b n, tag_covers dp obj l mf pf b n = true ->
    exists a k, (if obj then lawobj segs L CS (elaw E l) (zden E a) (zden E k) else lawcli segs (elaw E l) (zden E a) (zden E k))
                /\ zden E a <= zden E b /\ zden E b + zden E n <= zden E a + zden E k.
  Proof.
    intros obj b n. induction HM as [|f mf' Hf HM' IH]; cbn [tag_covers]; intros H; [discriminate|].
    assert (INS : forall a k, (if iv_inside_syn b n a k then true else (if dp then dec_inside pf b n a k else dec_inside0 pf b n a k)) = true ->
                              zden E a <= zden E b /\ zden E b + zden E n <= zden E a + zden E k).
    { intros a k X. destruct (iv_inside_syn b n a k) eqn:SY; [exact (iv_inside_syn_sound E b n a k SY)|].
      destruct dp; [exact (dec_inside_sound CS E pf b n a k HP X)| exact (dec_inside0_sound CS E pf b n a k HP X)]. }
    destruct f as [?b0 ?cs|?b0 ?cs|?b0 ?n0 ?k0|?lo ?hi|?oa ?on|?ok_k ?ok_l ?sh_l|?ra_ ?rw_ ?rl_ ?rn_ ?rwr_|?mW ?mi ?mj|?mi ?mj|?ml ?mX ?mi ?mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok];
      cbn [tag_covers] in H; try exact (IH HM' H);
      (match type of H with (if ?c then true else _) = true => destruct c eqn:HC; [clear H; rename HC into H| exact (IH HM' H)] end);
      [destruct obj; [discriminate|] | destruct obj; [|discriminate]]; cbn [negb andb] in H;
      (destruct (Nat.eqb_spec l ml) as [<-|]; [|discriminate]);
      exists ma, mn; (split; [cbn [mfact_ok] in Hf; rewrite !zdenp_ok in Hf; exact Hf| exact (INS ma mn H)]).
  Qed.

  Lemma cli_pagree : forall a k b n, lawcli segs (elaw E l) (zden E a) (zden E k) ->
    zden E a <= zden E b -> zden E b + n <= zden E a + zden E k -> disjoint_from (wden E W) (zden E b) n ->
    pagree segs (zden E b) n m m'.
  Proof.
    intros a k b n CLI H1 H2 AP x Hx HR. apply (CLI (wden E W) m m' x LAW); [lia| exact HR|].
    exact (disjoint_outside _ _ _ _ AP Hx).
  Qed.

  Lemma law_survives_sound : forall f,
    mfact_ok segs L CS E m f -> law_survives dp C l pf crs mf W wcl wne f = true -> mfact_ok segs L CS E m' f.
  Proof.
    intros f Hf H. destruct f as [b cs|b cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok];
      cbn [law_survives] in H; try discriminate.
    7-15: exact Hf.
    4:{ (* [comment removed for export] *) cbv zeta in H. destruct (all_apart pf W lo (eadd hi (emulc (-1) lo))) eqn:AP; [|discriminate].
        apply (all_apart_sound CS E pf HP) in AP. rewrite eadd_den, emulc_den in AP.
        destruct (tag_covers_sound false _ _ H) as (a & k & CLI & INS). rewrite eadd_den, emulc_den in INS.
        cbn [mfact_ok] in Hf |- *. rewrite !zdenp_ok in Hf |- *.
        eapply stk_agree; [exact Hf|]. eapply (cli_pagree a k); [exact CLI| lia| lia|].
        replace (zden E hi - zden E lo) with (zden E hi + -1 * zden E lo) by lia. exact AP. }
    - (* [comment removed for export] *)
      cbv zeta in H.
      assert (APX : disjoint_from (wden E W) (zden E b) (Z.of_N (cells_sizeN cs))
                    /\ tag_covers dp false l mf pf b (ELit (Z.of_N (cells_sizeN cs))) = true).
      { destruct (all_apart pf W b (ELit (Z.of_N (cells_sizeN cs)))) eqn:AP.
        - split; [|exact H]. apply (all_apart_sound CS E pf HP) in AP. cbn [zden] in AP. exact AP.
        - match type of H with (if ?c then _ else _) = true => destruct c eqn:CA; [|discriminate] end. split; [|exact H].
          apply andb_prop in CA as [CA CAP]. apply andb_prop in CA as [CA POS]. apply andb_prop in CA as [WC WN]. apply Z.ltb_lt in POS.
          pose proof (WCL0 WC) as HWC. pose proof (WNE0 WN) as HNE.
          assert (GEN : forall W', w_client CS (wden E W') -> Forall (fun iv => fst iv < snd iv) (wden E W') ->
                                   disjoint_from (wden E W') (zden E b) (Z.of_N (cells_sizeN cs))).
          { induction W' as [|[lo hi] W' IH]; cbn; intros HW HL; [exact I|].
            inversion HW; subst. inversion HL; subst. cbn [fst snd] in *. rewrite !zdenp_ok in *. split; [|apply IH; assumption].
            assert (PW : forall z y, zden E lo <= z < zden E lo + (zden E hi - zden E lo) ->
                                     zden E b <= y < zden E b + zden E (ELit (Z.of_N (cells_sizeN cs))) -> z <> y).
            { apply (class_apart_sound L CS E C HACC HSB pf crs AcClient lo (zden E hi - zden E lo) b _ HP HCR); [|exact CAP]. cbn. assumption. }
            cbn [zden] in PW. pose proof (pointwise_apart (zden E lo) (zden E hi - zden E lo) (zden E b) (Z.of_N (cells_sizeN cs)) ltac:(lia) POS PW). lia. }
          apply GEN; assumption. }
      clear H. destruct APX as [AP H].
      destruct (tag_covers_sound false _ _ H) as (a & k & CLI & INS). cbn [zden] in INS.
      cbn [mfact_ok] in Hf |- *. rewrite !zdenp_ok in Hf |- *.
      eapply rw_cells_agree; [exact Hf|]. rewrite csden_size.
      eapply (cli_pagree a k); [exact CLI| lia| lia|]. replace (Z.of_nat (N.to_nat (cells_sizeN cs))) with (Z.of_N (cells_sizeN cs)) by lia. exact AP.
    - (* [comment removed for export] *) cbv zeta in H. destruct (all_apart pf W b (ELit (Z.of_N (cells_sizeN cs)))) eqn:AP; [|discriminate].
      apply (all_apart_sound CS E pf HP) in AP. cbn [zden] in AP.
      destruct (tag_covers_sound false _ _ H) as (a & k & CLI & INS). cbn [zden] in INS.
      cbn [mfact_ok] in Hf |- *. rewrite !zdenp_ok in Hf |- *.
      eapply ro_cells_agree; [exact Hf|]. rewrite csden_size.
      eapply (cli_pagree a k); [exact CLI| lia| lia|]. replace (Z.of_nat (N.to_nat (cells_sizeN cs))) with (Z.of_N (cells_sizeN cs)) by lia. exact AP.
    - (* [comment removed for export] *) destruct (all_apart0 pf W b n) eqn:AP; [|discriminate].
      apply (all_apart0_sound CS E pf HP) in AP.
      destruct (tag_covers_sound false _ _ H) as (a & kk & CLI & INS).
      cbn [mfact_ok] in Hf |- *. rewrite !zdenp_ok in Hf |- *. destruct Hf as [HB HL]. split; [|exact HL].
      destruct AP as [Z0|AP].
      + assert (eb E k = []) as -> by (destruct (eb E k); [reflexivity| cbn in HL; lia]).
        pose proof (bytes_at_bound _ _ _ _ HB). apply bytes_at_nil_any; cbn in *; lia.
      + eapply bytes_at_agree; [exact HB|]. rewrite HL. eapply (cli_pagree a kk); [exact CLI| lia| lia| exact AP].
    - (* [comment removed for export] *) destruct (tag_covers_sound true _ _ H) as (a & k & OBJ & INS).
      cbn [mfact_ok] in Hf |- *. rewrite !zdenp_ok in Hf |- *. exact (OBJ (wden E W) m m' _ _ LAW (proj1 INS) (proj2 INS) Hf).
    - (* [comment removed for export] *) cbv zeta in H. destruct (all_apart0 pf W ra_ (emulc (Z.of_N rw_) rn_)) eqn:AP; [|discriminate].
      apply (all_apart0_sound CS E pf HP) in AP. rewrite emulc_den in AP.
      destruct (tag_covers_sound false _ _ H) as (a & k & CLI & INS). rewrite emulc_den in INS.
      destruct AP as [Z0|AP].
      + (* [comment removed for export] *)
        eapply (marr_agree segs L CS E m m'); [exact Hf|]. intros x Hx HR. exfalso.
        assert (Z.of_N rw_ * zden E rn_ <= 0) by (apply Z.mul_nonneg_nonpos; lia). lia.
      + eapply (marr_agree segs L CS E m m'); [exact Hf|]. eapply (cli_pagree a k); [exact CLI| lia| lia| exact AP].
  Qed.
End SurviveL.

(* [comment removed for export] *)
Definition noheap (f : mfact) : bool := match f with MHeap _ _ => false | _ => true end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SurviveH.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variables m m' : mem.
  Variable pf : list pfact.
  Variable mf : list mfact.
  Variable blL : bklist.                (* [comment removed for export] *)
  Variable sp : expr.                  (* [comment removed for export] *)
  Variable X : list (expr * expr).     (* [comment removed for export] *)
  Variable l : nat.
  Hypothesis HP : Forall (pfact_ok CS E) pf.
  Hypothesis HM : Forall (mfact_ok segs L CS E m) mf.
  Hypothesis LAW : ehlaw E l (blden E blL) (zden E sp) (wden E X) m m'.
  Hypothesis MI' : mem_inv segs m'.
  Hypothesis HOK : hlaw_ok segs (ehlaw E l).
  Hypothesis EXT : forall b, In b (elb0 E) -> In b (blden E blL).

  Lemma tag_coversH_sound : forall b n, tag_coversH l mf pf sp b n = true ->
    exists s a k, hlawcli segs E (ehlaw E l) (zden E s) (zden E a) (zden E k) /\ zden E sp <= zden E s /\ zden E a <= zden E b /\ zden E b + zden E n <= zden E a + zden E k.
  Proof.
    intros b n. induction HM as [|f mf' Hf HM' IH]; cbn [tag_coversH]; intros H; [discriminate|].
    assert (INS : forall a k, (if iv_inside_syn b n a k then true else dec_inside pf b n a k) = true ->
                              zden E a <= zden E b /\ zden E b + zden E n <= zden E a + zden E k).
    { intros a k Y. destruct (iv_inside_syn b n a k) eqn:SY; [exact (iv_inside_syn_sound E b n a k SY)| exact (dec_inside_sound CS E pf b n a k HP Y)]. }
    destruct f as [?b0 ?cs|?b0 ?cs|?b0 ?n0 ?k0|?lo ?hi|?oa ?on|?ok_k ?ok_l ?sh_l|?ra_ ?rw_ ?rl_ ?rn_ ?rwr_|?mW ?mi ?mj|?mi ?mj|?ml ?mX ?mi ?mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok];
      cbn [tag_coversH] in H; try exact (IH HM' H).
    destruct (Nat.eqb_spec l ql) as [<-|]; [|exact (IH HM' H)].
    destruct (dec_le pf sp qs) eqn:LE; [|exact (IH HM' H)].
    match type of H with (if ?c then true else _) = true => destruct c eqn:CI end.
    - exists qs, qa, qn. split; [cbn [mfact_ok] in Hf; rewrite !zdenp_ok in Hf; exact Hf|].
      split; [exact (dec_le_sound CS E pf sp qs HP LE)| exact (INS qa qn CI)].
    - exact (IH HM' H).
  Qed.

  Lemma hcovered_pagree : forall b n, hcovered l pf mf blL sp b n = true ->
    disjoint_from (wden E X) (zden E b) (zden E n) -> pagree segs (zden E b) (zden E n) m m'.
  Proof.
    intros b n H AP x Hx HR. unfold hcovered in H.
    pose proof (disjoint_outside _ _ _ _ AP Hx) as OUT.
    destruct (dec_le pf sp b) eqn:LE.
    { apply (dec_le_sound CS E) in LE; [|exact HP]. apply (HOK _ _ _ _ _ x LAW HR OUT). left. lia. }
    destruct (bl_covers pf blL b n) eqn:BC.
    { destruct (bl_covers_sound CS E pf blL b n HP BC) as (a & k & Hin & Hlo & Hhi).
      apply (HOK _ _ _ _ _ x LAW HR OUT). right. exists (zden E a, zden E k). split; [exact Hin| cbn [fst snd]; lia]. }
    destruct (tag_coversH_sound b n H) as (s & a & k & CLI & Hs & Hlo & Hhi).
    apply (CLI _ _ _ _ _ x EXT Hs LAW); [lia| exact HR| exact OUT].
  Qed.

  Lemma oq_taggedH_In : forall k mf0, oq_taggedH l k mf0 = true -> In (MOqH l k) mf0.
  Proof.
    intros k mf0. induction mf0 as [|f mf0 IH]; cbn [oq_taggedH]; intros H; [discriminate|].
    destruct f; try (right; exact (IH H)).
    match type of H with (if ?c then _ else _) = true => destruct c eqn:C2 end; [|right; exact (IH H)].
    apply andb_prop in C2 as [A B]. apply Nat.eqb_eq in A. apply Nat.eqb_eq in B. subst. left. reflexivity.
  Qed.

  Lemma heap_survives_sound : forall f,
    mfact_ok segs L CS E m f -> heap_survives l pf mf blL sp X f = true -> mfact_ok segs L CS E m' f.
  Proof.
    intros f Hf H. destruct f as [b cs|b cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok];
      cbn [heap_survives] in H; try discriminate.
    all: try exact Hf.
    - (* [comment removed for export] *) cbv zeta in H. destruct (all_apart pf X b (ELit (Z.of_N (cells_sizeN cs)))) eqn:AP; [|discriminate].
      apply (all_apart_sound CS E pf HP) in AP.
      cbn [mfact_ok] in Hf |- *. rewrite !zdenp_ok in Hf |- *.
      eapply rw_cells_agree; [exact Hf|]. rewrite csden_size.
      replace (Z.of_nat (N.to_nat (cells_sizeN cs))) with (zden E (ELit (Z.of_N (cells_sizeN cs)))) by (cbn [zden]; lia).
      exact (hcovered_pagree _ _ H AP).
    - (* [comment removed for export] *) cbv zeta in H. destruct (all_apart pf X b (ELit (Z.of_N (cells_sizeN cs)))) eqn:AP; [|discriminate].
      apply (all_apart_sound CS E pf HP) in AP.
      cbn [mfact_ok] in Hf |- *. rewrite !zdenp_ok in Hf |- *.
      eapply ro_cells_agree; [exact Hf|]. rewrite csden_size.
      replace (Z.of_nat (N.to_nat (cells_sizeN cs))) with (zden E (ELit (Z.of_N (cells_sizeN cs)))) by (cbn [zden]; lia).
      exact (hcovered_pagree _ _ H AP).
    - (* [comment removed for export] *) destruct (all_apart pf X b n) eqn:AP; [|discriminate].
      apply (all_apart_sound CS E pf HP) in AP.
      cbn [mfact_ok] in Hf |- *. rewrite !zdenp_ok in Hf |- *. destruct Hf as [HB HL]. split; [|exact HL].
      eapply bytes_at_agree; [exact HB|]. rewrite HL. exact (hcovered_pagree _ _ H AP).
    - (* [comment removed for export] *)
      apply oq_taggedH_In in H. pose proof HM as HM0. rewrite List.Forall_forall in HM0. pose proof (HM0 _ H) as T. cbn [mfact_ok] in T.
      cbn [mfact_ok] in Hf |- *. destruct Hf as [P Q]. split; [|exact Q]. exact (T _ _ _ _ _ EXT LAW P).
    - (* [comment removed for export] *) cbv zeta in H. destruct (all_apart pf X ra_ (emulc (Z.of_N rw_) rn_)) eqn:AP; [|discriminate].
      apply (all_apart_sound CS E pf HP) in AP. rewrite emulc_den in AP.
      eapply (marr_agree segs L CS E m m'); [exact Hf|]. pose proof (hcovered_pagree _ _ H) as PG. rewrite emulc_den in PG. exact (PG AP).
    - (* [comment removed for export] *)
      destruct (bl_suffix qn blL) eqn:SUF; [|discriminate].
      destruct Hf as [HR (HOK' & HBK' & HCW & HI0 & HI1)]. split; [| exact (conj HOK' (conj HBK' (conj HCW (conj HI0 HI1))))].
      apply (HOK' _ _ _ m _ HR MI'). intros x Hx HIN HNCW. rewrite lforallb_forall in H.
      assert (OUTG : forall W1, (forall lh, In lh W1 -> hpr_iv_ok pf mf qo qn qok (fst lh) (eadd (snd lh) (emulc (-1) (fst lh))) = true) ->
                                outside (wden E W1) x).
      { clear HR H. induction W1 as [|[lo hi] W1 IH]; cbn; intros HW; [exact I|]. split.
        - pose proof (hpr_iv_ok_out segs L CS E m pf mf qo qn qok lo (eadd hi (emulc (-1) lo)) x HP HM HBK' HCW HI0
                        (HW (lo, hi) (or_introl eq_refl)) HIN HNCW) as Y. rewrite eadd_den, emulc_den in Y. rewrite !zdenp_ok. lia.
        - apply IH. intros lh Hlh. apply HW. right. exact Hlh. }
      apply (HOK _ _ _ _ _ x LAW Hx (OUTG X H)). right.
      destruct HIN as (bk & Hbk & Hr). exists bk. split; [exact (bl_suffix_incl E qn blL bk SUF Hbk)| exact Hr].
  Qed.

  Lemma heap_survives_noheap : forall f, heap_survives l pf mf blL sp X f = true -> noheap f = true.
  Proof. intros f H. destruct f; try reflexivity. cbn in H. discriminate. Qed.
End SurviveH.

(* [comment removed for export] *)
Lemma heap_find_In : forall mf bl ok, heap_find mf = Some (bl, ok) -> In (MHeap bl ok) mf.
Proof.
  induction mf as [|f mf IH]; cbn; intros bl ok H; [discriminate|].
  destruct f; try (right; apply IH; exact H). injection H; intros <- <-. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bl_pop_sound : forall segs L CS E m pf mf a bl n bl',
  Forall (pfact_ok CS E) pf -> Forall (mfact_ok segs L CS E m) mf ->
  bl_pop pf mf a bl = Some (n, bl') ->
  blden E bl' = lb_remove (zden E a) (blden E bl) /\ In (zden E a, zden E n) (blden E bl).
Proof.
  intros segs L CS E m pf mf a bl. induction bl as [|b k rest IH|kv]; intros n bl' HP HM H; cbn [bl_pop] in H; [discriminate| |discriminate].
  destruct (expr_eqb a b) eqn:EQ.
  - apply expr_eqb_eq in EQ. subst b. injection H; intros <- <-. cbn [blden lb_remove fst]. rewrite !zdenp_ok, Z.eqb_refl.
    split; [reflexivity| left; reflexivity].
  - match type of H with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
    apply andb_prop in C1 as [MM LT]. apply mf_mem_In in MM. apply (dec_lt_sound CS E) in LT; [|exact HP]. cbn [zden] in LT.
    destruct (bl_pop pf mf a rest) as [[n' rest']|] eqn:BP; [|discriminate].
    destruct (dec_lt pf (ELit 0) n') eqn:LT2; [|discriminate]. apply (dec_lt_sound CS E) in LT2; [|exact HP]. cbn [zden] in LT2.
    injection H; intros <- <-. destruct (IH n' rest' HP HM eq_refl) as [IH1 IH2].
    pose proof HM as HM0. rewrite List.Forall_forall in HM0. pose proof (HM0 _ MM) as AP. cbn [mfact_ok] in AP. rewrite !zdenp_ok in AP.
    assert (NE : zden E b <> zden E a).
    { intros EQ2. destruct (AP _ _ IH2) as [Y|Y]; lia. }
    cbn [blden lb_remove fst]. rewrite !zdenp_ok. destruct (Z.eqb_spec (zden E b) (zden E a)); [lia|].
    split; [rewrite IH1; reflexivity| right; exact IH2].
Qed.
(* [comment removed for export] *)
Lemma spine_seps_ok : forall CS E a n bl (A N : Z),
  zdenp E a = A -> zdenp E n = N ->
  (forall b k, In (b, k) (blden E bl) -> A + N <= b \/ b + k <= A) ->
  Forall (pfact_ok CS E) (spine_seps a n bl).
Proof.
  intros CS E a n bl A N Ha Hn. induction bl as [|b k bl IH|kv]; intros H; cbn [spine_seps]; [constructor| |constructor].
  constructor.
  - cbn [pfact_ok]. rewrite Ha, Hn. apply H. left. reflexivity.
  - apply IH. intros b' k' Hin. apply H. right. exact Hin.
Qed.
Lemma obj_seps_ok : forall CS E pf j a n (A N : Z),
  Forall (pfact_ok CS E) pf ->
  zdenp E a = A -> zdenp E n = N ->
  (forall b k, eprop E j [b; k] -> k = 0 \/ A + N <= b \/ b + k <= A) ->
  Forall (pfact_ok CS E) (obj_seps j a n pf).
Proof.
  intros CS E pf j a n A N HP Ha Hn H. induction HP as [|f pf Hf HP IH]; cbn [obj_seps]; [constructor|].
  destruct f as [| | | | | | | | | | |j' xs]; try exact IH.
  destruct xs as [|b [|k [|]]]; try exact IH.
  destruct (Nat.eqb_spec j j') as [<-|]; [|exact IH].
  constructor; [|exact IH]. cbn [pfact_ok]. rewrite Ha, Hn. apply H. cbn [pfact_ok map] in Hf. exact Hf.
Qed.
Lemma bl_pop_vars : forall pf mf a nx bl n bl', bl_pop pf mf a bl = Some (n, bl') -> blvars_lt nx bl = true -> blvars_lt nx bl' = true.
Proof.
  intros pf mf a nx bl. induction bl as [|b k rest IH|kv]; intros n bl' H V; cbn [bl_pop] in H; [discriminate| |discriminate].
  cbn [blvars_lt] in V. apply andb_prop in V as [V Vr]. 
  destruct (expr_eqb a b); [injection H; intros <- <-; exact Vr|].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  destruct (bl_pop pf mf a rest) as [[n' rest']|] eqn:BP; [|discriminate].
  destruct (dec_lt pf (ELit 0) n'); [|discriminate]. injection H; intros <- <-.
  cbn [blvars_lt]. rewrite V, (IH n' rest' eq_refl Vr). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma has_mfact_In : forall mf f, has_mfact mf f = true -> In f mf.
Proof.
  induction mf as [|g mf IH]; intros f H; cbn in H; [discriminate|].
  apply orb_prop in H as [H|H]; [apply mfact_eqb_eq in H; subst; left; reflexivity| right; apply IH; exact H].
Qed.

Lemma find_arr_In : forall mf a w wr l n, find_arr mf a w wr = Some (l, n) -> exists wr', In (MArr a w l n wr') mf /\ (wr = true -> wr' = true).
Proof.
  induction mf as [|g mf IH]; intros a w wr l n H; cbn in H; [discriminate|].
  assert (REST : find_arr mf a w wr = Some (l, n) -> exists wr', In (MArr a w l n wr') (g :: mf) /\ (wr = true -> wr' = true)).
  { intros X. destruct (IH _ _ _ _ _ X) as (wr' & Hin & Hw). exists wr'. split; [right; exact Hin| exact Hw]. }
  destruct g as [| | | | | |b w' l' n' wr'| | | | | | | | | | |hj ho hn hxs hok]; try exact (REST H).
  destruct (expr_eqb a b && N.eqb w w' && (negb wr || wr')) eqn:C; [|exact (REST H)].
  apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply expr_eqb_eq in C1. apply N.eqb_eq in C2. subst b w'.
  injection H; intros <- <-. exists wr'. split; [left; reflexivity|]. intros ->. destruct wr'; [reflexivity| discriminate].
Qed.
Lemma marr_ro : forall segs L CS E m a w l n, mfact_ok segs L CS E m (MArr a w l n true) -> mfact_ok segs L CS E m (MArr a w l n false).
Proof.
  intros segs L CS E m a w l n H.
  assert (TU : forall (A : Prop) B C, (A /\ B) /\ C -> A /\ C) by (intros A B C0 [[X _] Y]; split; assumption).
  destruct (marr_cases w) as [-> |[-> |[-> |(N1 & N4 & N8)]]]; try (cbn in H |- *; apply TU in H; exact H).
  exfalso. cbn in H. destruct w as [|p]; [exact H|]. repeat (destruct p as [p|p|]; try exact (proj1 H); try exact H; try congruence).
Qed.

Section ReqOk.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variable C : lxcfg.
  Variable m : mem.
  Variable pf : list pfact.
  Variable crs : list (expr * expr).
  Variable mf : list mfact.
  Hypothesis HP : Forall (pfact_ok CS E) pf.
  Hypothesis HACC : forall A, c_acc C = Some A -> ac_got A = al_got L /\ ac_gsb A = al_gsb L /\ cs_ok L CS.
  Hypothesis HSB : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb L.
  Hypothesis HCR : Forall (fun an => crange CS (zden E (fst an)) (zden E (snd an))) crs.
  Hypothesis HM : Forall (mfact_ok segs L CS E m) mf.

  Lemma bytes_at_slice : forall mm a bs k n, bytes_at segs mm a bs -> (k + n <= length bs)%nat ->
    bytes_at segs mm (a + Z.of_nat k) (firstn n (skipn k bs)).
  Proof.
    intros mm a bs k n H Hk.
    rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H]. rewrite firstn_length, Nat.min_l in H by lia.
    rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
  Qed.

  Lemma zero_cells_sound : forall cs off cnt i, zero_cells cs off cnt = true -> (i < cnt)%nat ->
    cell_lookup cs (off + Z.of_nat i) 1 = Some (XZ 1 (ELit 0)).
  Proof.
    intros cs off cnt. revert off. induction cnt as [|cnt IH]; intros off i H Hi; [lia|]. cbn [zero_cells] in H.
    destruct (cell_lookup cs off 1) as [c|] eqn:CL; [|discriminate].
    destruct i as [|i].
    - rewrite Z.add_0_r. rewrite CL. destruct c as [|w e| | | |]; try discriminate. destruct w as [|p]; [discriminate|]. destruct p; try discriminate.
      destruct e as [z| | | | |]; try discriminate. destruct z; try discriminate. reflexivity.
    - replace (off + Z.of_nat (S i)) with ((off + 1) + Z.of_nat i) by lia. apply IH; [|lia].
      destruct c as [|w e| | | |]; try discriminate. destruct w as [|p]; [discriminate|]. destruct p; try discriminate.
      destruct e as [z| | | | |]; try discriminate. destruct z; try discriminate. exact H.
  Qed.

  Lemma aobj_derivable_sound : forall a n, aobj_derivable C pf crs mf a n = true -> aobj segs L CS m (zden E a) (zden E n).
  Proof.
    intros a n H. unfold aobj_derivable in H. apply lexistsb_exists in H as (f & Hin & H).
    rewrite List.Forall_forall in HM. pose proof (HM f Hin) as Hf.
    destruct f as [b cs|b cs|b n' k'|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try discriminate.
    - (* [comment removed for export] *)
      destruct (c_acc C) as [A|] eqn:HCA; [|discriminate]. destruct (is_lit n) as [nz|] eqn:LN; [|discriminate].
      destruct (shadow_split (ac_sb A) b) as [[x kr]|] eqn:SS; [|discriminate].
      destruct (ediff_lit a (sh_c x kr)) as [d|] eqn:DF; [|discriminate].
      apply andb_prop in H as [H IC]. apply andb_prop in H as [H ZC]. apply andb_prop in H as [H ALX]. apply andb_prop in H as [H N8].
      apply andb_prop in H as [H NZ]. apply andb_prop in H as [D0 D8].
      apply Z.leb_le in D0. apply Z.eqb_eq in D8. apply Z.ltb_lt in NZ. apply Z.eqb_eq in N8. apply N.leb_le in ALX.
      apply (is_lit_den E) in LN. apply (ediff_lit_den E) in DF. rewrite sh_c_den in DF.
      apply (in_some_crange_sound CS E pf crs) in IC; [|exact HP| exact HCR]. rewrite LN in IC |- *.
      split; [exact IC|].
      destruct (HACC A eq_refl) as (_ & _ & CSOK). pose proof CSOK as (C1 & _ & _ & _).
      pose proof (shadow_addr L E A (HSB A eq_refl) b x kr SS) as SB. rewrite sh_c_den in SB. set (k := zden E kr) in *.
      pose proof (eal_sound E (mk_oracle pf) x (mk_oracle_sound CS E pf HP)) as ALS.
      assert (D8x : (8 | zden E x)).
      { eapply Z.divide_trans; [|exact ALS]. exists (2 ^ (Z.of_N (eal (mk_oracle pf) x) - 3)).
        change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      destruct D8x as [qx Hqx].
      pose proof (Z.div_mod d 8 ltac:(lia)) as Hd. rewrite D8, Z.add_0_r in Hd. set (qd := d / 8) in *.
      pose proof (Z.div_mod nz 8 ltac:(lia)) as Hn. rewrite N8, Z.add_0_r in Hn. set (qn := nz / 8) in *.
      cbn in Hf. rewrite zdenp_ok in Hf. destruct Hf as [[WFC HB] _].
      pose proof (csden_wf_bytes_length E cs WFC) as LEN.
      intros c Hc. exists (Z_to_bv 8 0). split; [| left; rewrite Z_to_bv_unsigned; reflexivity].
      pose proof (Z.div_mod (c - zden E a) 8 ltac:(lia)) as Hr. pose proof (Z.mod_pos_bound (c - zden E a) 8 ltac:(lia)) as MB.
      set (qi := (c - zden E a) / 8) in *.
      assert (Hqi : 0 <= qi < qn) by (subst qi qn; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
      pose proof (zero_cells_sound cs qd (Z.to_nat qn) (Z.to_nat qi) ZC ltac:(lia)) as CL.
      destruct (cell_lookup_sound E cs (qd + Z.of_nat (Z.to_nat qi)) 1 _ ltac:(lia) CL WFC) as (_ & _ & BY & BND).
      cbn [cden cbytes zdenp] in BY. change (N.to_nat 1%N) with 1%nat in BY.
      pose proof (bytes_at_slice m (zden E b) _ (Z.to_nat (qd + Z.of_nat (Z.to_nat qi))) 1 HB ltac:(rewrite LEN; lia)) as BA.
      rewrite <- BY in BA.
      replace (shadow_of L c) with (zden E b + Z.of_nat (Z.to_nat (qd + Z.of_nat (Z.to_nat qi)))); [exact BA|].
      rewrite SB. unfold shadow_of. rewrite Hqx.
      replace (qx * 8 + 8 * k) with ((qx + k) * 8) by lia. rewrite (Z.div_mul (qx + k)) by lia.
      replace c with ((qx + k + qd + qi) * 8 + (c - zden E a) mod 8) by lia.
      rewrite Z.div_add_l by lia. rewrite (Z.div_small ((c - zden E a) mod 8) 8) by lia. lia.
    - (* [comment removed for export] *)
      apply andb_prop in H as [H1 H2]. apply (dec_le_sound CS E pf) in H1; [|exact HP]. apply (dec_le_sound CS E pf) in H2; [|exact HP].
      rewrite !eadd_den in H2. cbn in Hf. rewrite !zdenp_ok in Hf. eapply (aobj_sub segs L); [exact Hf| lia| lia].
  Qed.

  Lemma req_ok_sound : forall g, req_ok C pf crs mf g = true -> mfact_ok segs L CS E m g.
  Proof.
    intros g H. unfold req_ok in H. apply orb_prop in H as [H|H].
    - apply has_mfact_In in H. rewrite List.Forall_forall in HM. exact (HM g H).
    - destruct g as [| | | |oa on| |a w l n wr| | | | | | | | | | |hj ho hn hxs hok]; try discriminate.
      + cbn. rewrite !zdenp_ok. apply aobj_derivable_sound. exact H.
      + destruct (find_arr mf a w wr) as [[l' n']|] eqn:FA; [|discriminate]. apply andb_prop in H as [H1 H2].
        apply lexpr_eqb_eq in H1. apply expr_eqb_eq in H2. subst l' n'.
        destruct (find_arr_In _ _ _ _ _ _ FA) as (wr' & Hin & Hwr). rewrite List.Forall_forall in HM. pose proof (HM _ Hin) as X.
        destruct wr; [rewrite (Hwr eq_refl) in X; exact X|]. destruct wr'; [exact (marr_ro segs L CS E m a w l n X)| exact X].
  Qed.
End ReqOk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition thP (P : expr -> Prop) (th : subst) : Prop := forall i e, sub_get th i = Some e -> P e.

Lemma bind_P : forall P th i e th', thP P th -> P e -> bind th i e = Some th' -> thP P th'.
Proof.
  intros P th i e th' HT He H. unfold bind in H. destruct (sub_get th i) as [e'|] eqn:G.
  - destruct (expr_eqb e' e); [|discriminate]. injection H; intros <-. exact HT.
  - injection H; intros <-. intros j e2 Hj. cbn in Hj. destruct (Pos.eqb j i); [injection Hj; intros <-; exact He| exact (HT _ _ Hj)].
Qed.

Lemma match_regs_P : forall P ss rb th th', thP P th -> (forall r, P (rd_expr ss r)) -> match_regs ss rb th = Some th' -> thP P th'.
Proof.
  intros P ss rb. induction rb as [|[r i] rb IH]; intros th th' HT HR H; cbn in H.
  - injection H; intros <-. exact HT.
  - destruct (bind th i (rd_expr ss r)) as [th1|] eqn:B; [|discriminate]. eapply IH; [| exact HR| exact H]. eapply bind_P; eauto.
Qed.

Lemma xrep_expose_P : forall (P : expr -> Prop) w c0 cs0 c cs, P (ELit 0) -> xrep_expose w c0 cs0 = (c, cs) ->
  (forall c' e, In c' (c0 :: cs0) -> cell_expr c' = Some e -> P e) -> (forall c' e, In c' (c :: cs) -> cell_expr c' = Some e -> P e).
Proof.
  intros P w c0 cs0 c cs HP0 H HC.
  assert (TRIV : (c0, cs0) = (c, cs) -> forall c' e, In c' (c :: cs) -> cell_expr c' = Some e -> P e) by (intros X; injection X; intros <- <-; exact HC).
  unfold xrep_expose in H. destruct c0 as [i|w' e'|w' k|w' i|cc o l|n e0]; try exact (TRIV H).
  destruct (is_lit e0); [|exact (TRIV H)]. destruct (Z.eqb z 0 && okw w); [|exact (TRIV H)].
  destruct (N.ltb w n); [|destruct (N.eqb w n); [|exact (TRIV H)]]; injection H; intros <- <-;
    intros c' e [<-|Hin] He; cbn in He;
    first [ injection He; intros <-; exact HP0
          | destruct Hin as [<-|Hin]; [cbn in He; discriminate| apply (HC c' e); [right; exact Hin| exact He]]
          | apply (HC c' e); [right; exact Hin| exact He] ].
Qed.

Lemma match_cells_P : forall P pats cs th tb th' tb',
  (forall z, P (ELit z)) -> thP P th -> (forall c e, In c cs -> cell_expr c = Some e -> P e) -> match_cells pats cs th tb = Some (th', tb') -> thP P th'.
Proof.
  intros P pats. induction pats as [|p pats IH]; intros cs th tb th' tb' HP0 HT HC H.
  - destruct cs; cbn in H; [|discriminate]. injection H; intros <- <-. exact HT.
  - destruct p as [i|w pe|w kb|w i|c o l|wr er]; cbn [match_cells] in H; try discriminate.
    + destruct cs as [|c0 cs0]; [discriminate|]. destruct (xrep_expose w c0 cs0) as [c cs] eqn:XE.
      pose proof (xrep_expose_P P w c0 cs0 c cs (HP0 0) XE HC) as HCx. clear HC. rename HCx into HC.
      destruct (N.eqb (cellx_size c) w); [|discriminate].
      destruct (cell_expr c) as [e|] eqn:CE; [|discriminate].
      assert (HC' : forall c0 e0, In c0 cs -> cell_expr c0 = Some e0 -> P e0) by (intros c1 e1 Hin He1; apply (HC c1 e1); [right; exact Hin| exact He1]).
      destruct (pat_local pe) as [j|].
      * destruct (bind th j e) as [th1|] eqn:B; [|discriminate]. eapply IH; [exact HP0| | exact HC'| exact H]. eapply bind_P; [exact HT| | exact B]. apply (HC c e); [left; reflexivity| exact CE].
      * destruct (ebound th pe && enoU pe && expr_eqb (sxe th pe) e); [|discriminate]. eapply IH; [exact HP0| exact HT| exact HC'| exact H].
    + assert (CELLS : forall cs0, (forall c e, In c cs0 -> cell_expr c = Some e -> P e) ->
                 (match bsub_get tb kb, take_cellsx cs0 (Z.of_N w) with
                  | None, Some (taken, cs') => match_cells pats cs' th ((kb, BCells taken) :: tb)
                  | _, _ => None end) = Some (th', tb') -> thP P th').
      { intros cs0 HC0 M. destruct (bsub_get tb kb); [discriminate|]. destruct (take_cellsx cs0 (Z.of_N w)) as [[taken cs']|] eqn:TC; [|discriminate].
        eapply IH; [exact HP0| exact HT| | exact M]. intros c0 e0 Hin He0.
        destruct (take_cellsx_in _ _ _ _ TC c0 ltac:(apply in_app_iff; right; exact Hin)) as [Hin0|(c1 & o & l & Hc1 & ->)]; [exact (HC0 c0 e0 Hin0 He0)|].
        destruct (mk_slice_expr c1 o l e0 He0) as [Ec|[z ->]]; [| apply HP0]. rewrite Ec in He0. exact (HC0 c1 e0 Hc1 He0). }
      destruct cs as [|c cs]; [exact (CELLS [] HC H)|].
      destruct c as [i'|w' e'|w' k|w' i'|c' o' l'|wr' er']; try exact (CELLS _ HC H).
      destruct (N.eqb w w'); [|discriminate].
      assert (HC' : forall c0 e0, In c0 cs -> cell_expr c0 = Some e0 -> P e0) by (intros c0 e0 Hin He0; apply (HC c0 e0); [right; exact Hin| exact He0]).
      destruct (bsub_get tb kb) as [[k'|cs']|]; [| discriminate|].
      * destruct (Pos.eqb k k'); [|discriminate]. eapply IH; [exact HP0| exact HT| exact HC'| exact H].
      * eapply IH; [exact HP0| exact HT| exact HC'| exact H].
Qed.

Lemma match_chunks_P : forall P mf mb th tb th' tb',
  (forall z, P (ELit z)) -> thP P th -> (forall a cs c e, In (MRw a cs) mf -> In c cs -> cell_expr c = Some e -> P e) ->
  match_chunks mf mb th tb = Some (th', tb') -> thP P th'.
Proof.
  intros P mf mb. induction mb as [|f mb IH]; intros th tb th' tb' HP0 HT HC H; cbn [match_chunks] in H.
  - injection H; intros <- <-. exact HT.
  - destruct f as [a pats|a cs|a n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try discriminate.
    2:{ eapply IH; [exact HP0| exact HT| exact HC| exact H]. }
    destruct (ebound th a); [|discriminate].
    destruct (find_rw mf (sxe th a)) as [cs|] eqn:FR; [|discriminate].
    destruct (match_cells pats cs th tb) as [[th1 tb1]|] eqn:MC; [|discriminate].
    apply find_rw_In in FR. eapply IH; [exact HP0| | exact HC| exact H]. eapply match_cells_P; [exact HP0| exact HT| | exact MC].
    intros c e Hin He. eapply HC; eauto.
Qed.

(* [comment removed for export] *)
Lemma lbind_ok : forall tl j l tl', lbind tl j l = Some tl' -> lsub_get tl' j = Some l /\ (forall i x, lsub_get tl i = Some x -> lsub_get tl' i = Some x).
Proof.
  intros tl j l tl' H. unfold lbind in H. destruct (lsub_get tl j) as [l0|] eqn:G.
  - destruct (lexpr_eqb l0 l) eqn:Q; [|discriminate]. apply lexpr_eqb_eq in Q. subst l0. injection H; intros <-. split; [exact G| intros; assumption].
  - injection H; intros <-. split; [cbn; rewrite Pos.eqb_refl; reflexivity|].
    intros i x Hi. cbn. destruct (Pos.eqb_spec i j) as [->|]; [rewrite G in Hi; discriminate| exact Hi].
Qed.
Lemma match_arrs_ok : forall pf mf mb th tl th' tl',
  match_arrs pf mf mb th tl = Some (th', tl') ->
  thsub th th' /\ (forall i x, lsub_get tl i = Some x -> lsub_get tl' i = Some x) /\
  forall segs L CS m E E' thF tlF, thsub th' thF -> (forall i x, lsub_get tl' i = Some x -> lsub_get tlF i = Some x) ->
    (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
    (forall j l, lsub_get tlF j = Some l -> ldenw E l = el E' j) ->
    Forall (fun f => match f with MArr a _ _ _ _ => enoU a = true | _ => True end) mb ->
    Forall (mfact_ok segs L CS E m) mf -> Forall (pfact_ok CS E) pf ->
    Forall (fun f => match f with MArr _ _ _ _ _ => mfact_ok segs L CS E' m f | _ => True end) mb.
Proof.
  intros pf mf mb. induction mb as [|f mb IH]; intros th tl th' tl' H.
  - cbn in H. injection H; intros <- <-. split; [apply thsub_refl|]. split; [intros; assumption|]. intros; constructor.
  - cbn [match_arrs] in H.
    assert (SKIP : match f with MArr _ _ _ _ _ => False | _ => True end -> match_arrs pf mf mb th tl = Some (th', tl') ->
              thsub th th' /\ (forall i x, lsub_get tl i = Some x -> lsub_get tl' i = Some x) /\
              forall segs L CS m E E' thF tlF, thsub th' thF -> (forall i x, lsub_get tl' i = Some x -> lsub_get tlF i = Some x) ->
                (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
                (forall j l, lsub_get tlF j = Some l -> ldenw E l = el E' j) ->
                Forall (fun f => match f with MArr a _ _ _ _ => enoU a = true | _ => True end) (f :: mb) ->
                Forall (mfact_ok segs L CS E m) mf -> Forall (pfact_ok CS E) pf ->
                Forall (fun f => match f with MArr _ _ _ _ _ => mfact_ok segs L CS E' m f | _ => True end) (f :: mb)).
    { intros NF X. destruct (IH _ _ _ _ X) as (S2 & T2 & R2). split; [exact S2|]. split; [exact T2|].
      intros segs L CS m E E' thF tlF SF TF TH TL HU HM HP. inversion HU as [|f' mb' HUa HU']; subst f' mb'.
      constructor; [destruct f; try exact I; destruct NF| exact (R2 segs L CS m E E' thF tlF SF TF TH TL HU' HM HP)]. }
    destruct f as [| | | | | |pa w [j|pl pi pw pv] pn wr| | | | | | | | | | |hj ho hn hxs hok]; try (apply SKIP; [exact I| exact H]); [|discriminate].
    clear SKIP.
    destruct (ebound th pa) eqn:EB; [|discriminate]. destruct (N.eqb w 4 || N.eqb w 8) eqn:W48; [|discriminate]. cbn [andb] in H.
    destruct (find_arr mf (sxe th pa) w wr) as [[lc n]|] eqn:FA; [|discriminate].
    destruct (lbind tl j lc) as [tl1|] eqn:LB; [|discriminate]. destruct (lbind_ok _ _ _ _ LB) as [G1 T1].
    match type of H with (match ?o with Some _ => _ | None => None end) = _ => destruct o as [th1|] eqn:BN; [|discriminate] end.
    assert (S1 : thsub th th1 /\ forall CS E E' thF, thsub th1 thF -> (forall i e, sub_get thF i = Some e -> zden E e = ez E' i) ->
                                      Forall (pfact_ok CS E) pf -> zden E n = zdenp E' pn).
    { destruct (pat_local pn) as [jn|] eqn:PL.
      - destruct (bind th jn n) as [thb|] eqn:BN1.
        + injection BN; intros <-. destruct (bind_ok _ _ _ _ BN1) as [Gn Sn]. split; [exact Sn|]. intros CS E E' thF SF TH _.
          destruct (pat_local_den E' pn jn PL) as [-> _]. apply TH. apply SF. exact Gn.
        + (* [comment removed for export] *)
          destruct (sub_get th jn) as [e|] eqn:Ge; [|discriminate]. destruct (dec_eq pf e n) eqn:DQ; [|discriminate].
          injection BN; intros <-. split; [apply thsub_refl|]. intros CS E E' thF SF TH HP.
          destruct (pat_local_den E' pn jn PL) as [-> _]. rewrite <- (TH jn e (SF jn e Ge)). symmetry. exact (dec_eq_sound CS E pf e n HP DQ).
      - destruct (ebound th pn) eqn:EBn; [|discriminate]. destruct (enoU pn) eqn:EUn; [|discriminate].
        destruct (expr_eqb (sxe th pn) n) eqn:EQ; [|discriminate]. injection BN; intros <-. split; [apply thsub_refl|].
        intros CS E E' thF SF TH _. apply expr_eqb_eq in EQ. rewrite <- EQ. rewrite <- (sxe_ext th thF pn SF EBn).
        rewrite zdenp_ok. apply (sxe_den E E' thF TH); [eapply ebound_mono; [exact SF| exact EBn]| exact EUn]. }
    destruct S1 as [S1 DN].
    destruct (IH _ _ _ _ H) as (S2 & T2 & R2).
    split; [eapply thsub_trans; [exact S1| exact S2]|]. split; [intros i x Hi; apply T2, T1, Hi|].
    intros segs L CS m E E' thF tlF SF TF TH TL HU HM HP. inversion HU as [|f' mb' HUa HU']; subst f' mb'.
    constructor; [| exact (R2 segs L CS m E E' thF tlF SF TF TH TL HU' HM HP)].
    destruct (find_arr_In _ _ _ _ _ _ FA) as (wr' & Hin & Hwr). rewrite List.Forall_forall in HM. pose proof (HM _ Hin) as X.
    assert (XA : mfact_ok segs L CS E m (MArr (sxe th pa) w lc n wr)).
    { destruct wr; [rewrite (Hwr eq_refl) in X; exact X|]. destruct wr'; [exact (marr_ro segs L CS E m _ w lc n X)| exact X]. }
    clear X.
    assert (EA : zdenp E (sxe th pa) = zdenp E' pa).
    { assert (S0F : thsub th thF) by (eapply thsub_trans; [exact S1|]; eapply thsub_trans; [exact S2| exact SF]).
      rewrite <- (sxe_ext th thF pa S0F EB). apply (sxe_denp E E' thF TH); [eapply ebound_mono; [exact S0F| exact EB]| exact HUa]. }
    assert (EL : ldenw E lc = ldenw E' (LBase j)) by (cbn [ldenw]; apply TL; apply TF, T2; exact G1).
    assert (EN : zdenp E n = zdenp E' pn) by (rewrite zdenp_ok; apply (DN CS E E' thF); [eapply thsub_trans; [exact S2| exact SF]| exact TH| exact HP]).
    assert (W : w = 4%N \/ w = 8%N) by (apply orb_prop in W48 as [W|W]; apply N.eqb_eq in W; [left|right]; exact W).
    destruct W as [-> | ->]; cbn [mfact_ok] in XA |- *; rewrite <- EA, <- EL, <- EN; exact XA.
Qed.
Lemma match_arrs_P : forall P pf mf mb th tl th' tl',
  thP P th -> (forall a w l n wr, In (MArr a w l n wr) mf -> P n) ->
  match_arrs pf mf mb th tl = Some (th', tl') -> thP P th'.
Proof.
  intros P pf mf mb. induction mb as [|f mb IH]; intros th tl th' tl' HT HN H; cbn [match_arrs] in H.
  - injection H; intros <- <-. exact HT.
  - destruct f as [| | | | | |pa w [j|pl pi pw pv] pn wr| | | | | | | | | | |hj ho hn hxs hok]; try (eapply IH; [exact HT| exact HN| exact H]); [|discriminate].
    destruct (ebound th pa && (N.eqb w 4 || N.eqb w 8)); [|discriminate].
    destruct (find_arr mf (sxe th pa) w wr) as [[lc n]|] eqn:FA; [|discriminate].
    destruct (lbind tl j lc) as [tl1|]; [|discriminate].
    match type of H with (match ?o with Some _ => _ | None => None end) = _ => destruct o as [th1|] eqn:BN; [|discriminate] end.
    eapply IH; [| exact HN| exact H].
    destruct (pat_local pn) as [jn|].
    + destruct (bind th jn n) as [thb|] eqn:BN1.
      * injection BN; intros <-. eapply bind_P; [exact HT| | exact BN1]. destruct (find_arr_In _ _ _ _ _ _ FA) as (wr' & Hin & _). exact (HN _ _ _ _ _ Hin).
      * destruct (sub_get th jn); [|discriminate]. destruct (dec_eq pf _ n); [|discriminate]. injection BN; intros <-. exact HT.
    + destruct (ebound th pn && enoU pn && expr_eqb (sxe th pn) n); [|discriminate]. injection BN; intros <-. exact HT.
Qed.

Lemma match_stk_P : forall P mf0 mf h i th th', thP P th -> (forall lo hi, In (MStk lo hi) mf -> P lo) -> match_stk mf0 mf h i th = Some th' -> thP P th'.
Proof.
  intros P mf0 mf. induction mf as [|f mf IH]; intros h i th th' HT HM H; cbn -[frame_fills expr_eqb bind] in H; [discriminate|].
  assert (HM' : forall lo hi, In (MStk lo hi) mf -> P lo) by (intros lo hi Hin; eapply HM; right; exact Hin).
  destruct f as [a pats|a cs|a n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try (eapply IH; [exact HT| exact HM'| exact H]).
  destruct (expr_eqb hi h); [|destruct (frame_fills mf0 hi h)].
  - eapply bind_P; [exact HT| | exact H]. eapply HM. left; reflexivity.
  - eapply bind_P; [exact HT| | exact H]. eapply HM. left; reflexivity.
  - eapply IH; [exact HT| exact HM'| exact H].
Qed.

Lemma bind_bytes_P : forall P bb cands th tb k th' tb',
  thP P th -> (forall a n kc, In (a, n, kc) cands -> P a /\ P n) -> bind_bytes bb cands th tb k = Some (th', tb') -> thP P th'.
Proof.
  intros P bb. induction bb as [|[[ia il] kb] bb IH]; intros cands th tb k th' tb' HT HC H; cbn [bind_bytes] in H.
  - destruct (k th); [|discriminate]. injection H; intros <- <-. exact HT.
  - lazymatch type of H with ?F cands = ?R =>
      enough (GEN : forall cs, (forall x, In x cs -> In x cands) -> F cs = R -> thP P th') by (apply (GEN cands); [intros x Hx; exact Hx| exact H])
    end.
    clear H. induction cs as [|[[a n] kc] cs IHc]; intros INCL H; [discriminate|]. cbn in H.
    assert (INCL' : forall x, In x cs -> In x cands) by (intros x Hx; apply INCL; right; exact Hx).
    destruct (bsub_get tb kb); [discriminate|].
    destruct (HC a n kc (INCL _ (or_introl eq_refl))) as [Pa Pn].
    destruct (bind th ia a) as [th1|] eqn:B1; [|apply IHc; assumption].
    destruct (bind th1 il n) as [th2|] eqn:B2; [|apply IHc; assumption].
    destruct (bind_bytes bb cands th2 ((kb, BVar kc) :: tb) k) as [[th3 tb3]|] eqn:BB; [|apply IHc; assumption].
    injection H; intros <- <-. eapply IH; [| exact HC| exact BB].
    eapply bind_P; [| exact Pn| exact B2]. eapply bind_P; [exact HT| exact Pa| exact B1].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pget_nth : forall {A} (l : list A) i d, pget l i d = nth (Pos.to_nat i - 1) l d.
Proof.
  induction l as [|x l IH]; intros i d.
  - cbn. destruct (Pos.to_nat i - 1)%nat; reflexivity.
  - rewrite pget_cons. destruct (Pos.eqb_spec i 1) as [->|NE]; [reflexivity|].
    rewrite IH. replace (Pos.to_nat i - 1)%nat with (S (Pos.to_nat (Pos.pred i) - 1))%nat by lia. reflexivity.
Qed.

Lemma bridge_bound : forall th n e, (forall i, (i < n)%positive -> sub_get th i <> None) -> eloc n e = true -> ebound th e = true.
Proof.
  intros th n e HB. induction e; cbn; intros H; try reflexivity; try discriminate.
  - apply Pos.ltb_lt in H. specialize (HB i H). destruct (sub_get th i); [reflexivity| congruence].
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply IHe. exact H.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
Qed.

Lemma bridge_p : forall th n f, (forall i, (i < n)%positive -> sub_get th i <> None) -> ploc n f = true -> pbound th f = true.
Proof.
  intros th n f HB H.
  destruct f as [| | | | | | | | | | |pj pxs];
    [ .. | cbn [ploc] in H; cbn [pbound]; revert H; induction pxs as [|x xs IH]; cbn -[eloc ebound enoU]; intros H;
           [reflexivity| apply andb_prop in H as [H1 H2]; rewrite (bridge_bound th n x HB H1), (eloc_enoU n x H1), (IH H2); reflexivity] ];
    cbn -[eloc ebound enoU] in H |- *; try discriminate;
    repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end;
    repeat match goal with G : eloc n ?e = true |- _ => rewrite (bridge_bound th n e HB G), (eloc_enoU n e G); clear G end; reflexivity.
Qed.

Lemma bridge_c : forall th tb n nb blobs c,
  (forall i, (i < n)%positive -> sub_get th i <> None) -> cell_blob_ok tb c = true ->
  cloc n nb blobs c = true -> cbound th tb c = true.
Proof.
  intros th tb n nb blobs c HB HK H. destruct c; cbn -[eloc ebound enoU okw bvar_bound] in H, HK |- *; try discriminate.
  - apply andb_prop in H as [H1 H2]. rewrite H1, (bridge_bound th n e HB H2), (eloc_enoU n e H2). reflexivity.
  - unfold bbound. unfold bvar_bound in HK. exact HK.
  - rewrite (bridge_bound th n e HB H), (eloc_enoU n e H). reflexivity.
Qed.

Lemma bridge_m : forall th tb tl n nb nl blobs f,
  (forall i, (i < n)%positive -> sub_get th i <> None) -> post_blobs_ok tb f = true ->
  (forall j, (j < nl)%positive -> lsub_get tl j <> None) ->
  mloc n nb nl blobs f = true -> mboundA th tb tl f = true.
Proof.
  intros th tb tl n nb nl blobs f HB HK HL H.
  destruct f as [| | | | | |aa ww [jj|] nn wwr| | | | | | | | | | |hj ho hn hxs hok].
  7:{ cbn -[eloc ebound enoU Pos.ltb] in H |- *. repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end.
      repeat match goal with G : eloc n ?e = true |- _ => rewrite (bridge_bound th n e HB G), (eloc_enoU n e G); clear G end.
      match goal with G : N.eqb _ _ || _ = true |- _ => rewrite G end. cbn [andb].
      match goal with G : Pos.ltb jj nl = true |- _ => apply Pos.ltb_lt in G; specialize (HL jj G) end.
      destruct (lsub_get tl jj); [reflexivity| exfalso; apply HL; reflexivity]. }
  7:{ discriminate. }
  all: unfold mboundA; try discriminate; cbn -[eloc ebound enoU cloc cbound forallb cell_blob_ok bvar_bound] in H, HK |- *;
    repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end;
    repeat match goal with G : eloc ?n' ?e = true |- _ => rewrite (bridge_bound th n' e HB G), (eloc_enoU n' e G); clear G end; cbn [andb].
  - apply forallb_forall. intros c Hc. rewrite forallb_forall in HK. lazymatch goal with G : forallb _ cs = true |- _ => rewrite forallb_forall in G; eapply bridge_c; [exact HB| apply HK; exact Hc| apply G; exact Hc] end.
  - apply forallb_forall. intros c Hc. rewrite forallb_forall in HK. lazymatch goal with G : forallb _ cs = true |- _ => rewrite forallb_forall in G; eapply bridge_c; [exact HB| apply HK; exact Hc| apply G; exact Hc] end.
  - unfold bbound. unfold bvar_bound in HK. exact HK.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma opq_find_In : forall mf k f, opq_find mf k = Some f -> exists ok sh, f = MOpq k ok sh /\ In f mf.
Proof.
  induction mf as [|g mf IH]; intros k f H; cbn in H; [discriminate|].
  destruct g as [? ?|? ?|? ? ?|? ?|? ?|k2 ok2 sh2|? ? ? ? ?|? ? ?|? ?|? ? ? ?|? ? ?|? ? ?|qbl qok|? ? ? ? ? ?|? ? ?|? ? ?|? ?|hj ho hn hxs hok]; try (destruct (IH k f H) as (ok & sh & E1 & Hin); exists ok, sh; split; [exact E1| right; exact Hin]).
  destruct (Nat.eqb_spec k k2) as [<-|NE].
  - injection H; intros <-. exists ok2, sh2. split; [reflexivity| left; reflexivity].
  - destruct (IH k f H) as (ok & sh & E1 & Hin). exists ok, sh. split; [exact E1| right; exact Hin].
Qed.
Lemma opq_required_In : forall mf ks l k, opq_required mf ks = Some l -> In k ks -> exists ok sh, In (MOpq k ok sh) mf.
Proof.
  intros mf ks. unfold opq_required. induction ks as [|k0 ks IH]; intros l k H Hin; [destruct Hin|]. cbn [fold_right] in H.
  match type of H with (match ?acc with _ => _ end) = _ => destruct acc as [l0|] eqn:R0; [|discriminate] end.
  destruct (opq_find mf k0) as [f|] eqn:F; [|discriminate].
  destruct Hin as [<-|Hin].
  - destruct (opq_find_In _ _ _ F) as (ok & sh & -> & Hf). exists ok, sh. exact Hf.
  - exact (IH l0 k eq_refl Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Setm.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variable k : nat.
  Variable mm : mem.

  Lemma zdenp_setm : forall e, zdenp (env_setm E k mm) e = zdenp E e.
  Proof. intros. rewrite !zdenp_ok. apply zden_setm. Qed.
  Lemma rden_setm : forall r, rden (env_setm E k mm) r = rden E r.
  Proof. intros [i|e]; cbn -[zdenp]; [reflexivity|]. rewrite zdenp_setm. reflexivity. Qed.
  Lemma regs_den_setm : forall rs, regs_den (env_setm E k mm) rs = regs_den E rs.
  Proof.
    intros rs. do 31 (destruct rs as [|? rs]; [reflexivity|]). destruct rs; [|reflexivity].
    cbn [regs_den]. rewrite !rden_setm. reflexivity.
  Qed.
  Lemma pc_den_setm : forall p, pc_den (env_setm E k mm) p = pc_den E p.
  Proof. intros [z|r]; cbn -[rden Z_to_bv]; [reflexivity|]. rewrite rden_setm. reflexivity. Qed.
  Lemma ms_den_setm : forall G ss m, ms_den segs G (env_setm E k mm) ss m = ms_den segs G E ss m.
  Proof. intros. unfold ms_den. rewrite regs_den_setm, pc_den_setm. reflexivity. Qed.
  Lemma cden_setm : forall c, cden (env_setm E k mm) c = cden E c.
  Proof.
    induction c as [i|w e|w kb|w i|c IH o l|wr er]; cbn -[zdenp N.to_nat cden]; cbn [cden]; try reflexivity.
    - rewrite !zdenp_setm. reflexivity.
    - fold (cden (env_setm E k mm) c) (cden E c). rewrite IH. reflexivity.
    - rewrite !zdenp_setm. reflexivity.
  Qed.
  Lemma csden_setm : forall cs, csden (env_setm E k mm) cs = csden E cs.
  Proof. intros cs. unfold csden. induction cs as [|c cs IH]; [reflexivity|]. cbn. rewrite cden_setm, IH. reflexivity. Qed.
  Lemma wden_setm : forall W, wden (env_setm E k mm) W = wden E W.
  Proof. intros W. unfold wden. apply map_ext. intros [lo hi]. cbn [fst snd]. rewrite !zdenp_setm. reflexivity. Qed.
  Lemma ldenw_setm : forall l, ldenw (env_setm E k mm) l = ldenw E l.
  Proof. induction l as [kb|l IH i w e]; cbn -[zdenp]; [reflexivity|]. rewrite IH, !zdenp_setm. reflexivity. Qed.
  Lemma ldenb_setm : forall l, ldenb (env_setm E k mm) l = ldenb E l.
  Proof. induction l as [kb|l IH i w e]; cbn -[zdenp wbytes upd_bytes]; [reflexivity|]. rewrite IH, !zdenp_setm. reflexivity. Qed.
  Lemma blden_setm : forall bl, blden (env_setm E k mm) bl = blden E bl.
  Proof. induction bl as [|a n bl IH|kv]; cbn -[zdenp env_setm]; [reflexivity| |reflexivity]. rewrite !zdenp_setm, IH. reflexivity. Qed.
  Lemma zdenps_setm : forall xs, map (zdenp (env_setm E k mm)) xs = map (zdenp E) xs.
  Proof. induction xs as [|x xs IH]; cbn -[zdenp env_setm]; [reflexivity|]. rewrite zdenp_setm, IH. reflexivity. Qed.
  Lemma pfact_ok_setm : forall f, pfact_ok CS (env_setm E k mm) f <-> pfact_ok CS E f.
  Proof.
    intros f.
    destruct f as [| | | | | | | | | | |pj pxs]; [| | | | | | | | | | | unfold pfact_ok, eprop; cbn [epr env_setm]; rewrite (zdenps_setm pxs); tauto].
    all: cbn -[zdenp Z.pow Z.of_N ez env_setm]; rewrite ?zdenp_setm; try tauto. all: rewrite !ez_setm; tauto.
  Qed.
  Lemma mfact_ok_setm : forall m f, mrefs_lt k f = true -> mfact_ok segs L CS (env_setm E k mm) m f <-> mfact_ok segs L CS E m f.
  Proof.
    intros m f MR. destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok].
    7:{ cbn [mfact_ok]. rewrite !zdenp_setm, ?ldenw_setm, ?ldenb_setm. tauto. }
    7:{ cbn [mrefs_lt] in MR. apply andb_prop in MR as [M1 M2]. apply Nat.ltb_lt in M1. apply Nat.ltb_lt in M2.
        cbn [mfact_ok]. rewrite wden_setm, !em_setm. destruct (Nat.eqb_spec mi k); [lia|]. destruct (Nat.eqb_spec mj k); [lia|]. tauto. }
    7:{ cbn [mrefs_lt] in MR. apply andb_prop in MR as [M1 M2]. apply Nat.ltb_lt in M1. apply Nat.ltb_lt in M2.
        cbn [mfact_ok]. rewrite !em_setm. destruct (Nat.eqb_spec mi k); [lia|]. destruct (Nat.eqb_spec mj k); [lia|]. tauto. }
    7:{ cbn [mrefs_lt] in MR. apply andb_prop in MR as [M1 M2]. apply Nat.ltb_lt in M1. apply Nat.ltb_lt in M2.
        cbn [mfact_ok]. rewrite wden_setm, !em_setm, elaw_setm. destruct (Nat.eqb_spec mi k); [lia|]. destruct (Nat.eqb_spec mj k); [lia|]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setm, elaw_setm. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setm, elaw_setm. tauto. }
    (* [comment removed for export] *)
    7:{ cbn [mfact_ok]. rewrite blden_setm, wden_setm. unfold ehp, ecw, ecur. cbn [env_setm]. tauto. }
    7:{ cbn [mrefs_lt] in MR. apply andb_prop in MR as [MR M3]. apply andb_prop in MR as [M1 M2]. apply Nat.ltb_lt in M1. apply Nat.ltb_lt in M2.
        cbn [mfact_ok]. rewrite blden_setm, zdenp_setm, wden_setm, !em_setm. unfold ehlaw. cbn [elh env_setm].
        destruct (Nat.eqb_spec qi k); [lia|]. destruct (Nat.eqb_spec qj k); [lia|]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setm. unfold hlawcli, ehlaw. cbn [elb0 elh env_setm]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setm, blden_setm. tauto. }
    7:{ cbn [mfact_ok]. unfold hlawopq, ehlaw, eo. cbn [elb0 elh eol env_setm]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !blden_setm, wden_setm, (map_ext _ _ zdenp_setm). unfold ehres, ecw, elb0. cbn [ehr env_setm]. tauto. }
    all: try solve [cbn [mfact_ok]; rewrite !wden_setm; unfold eo; cbn [eol env_setm]; tauto].
    all: cbn -[zdenp csden eb rw_cells ro_cells bytes_at stk aobj Z.of_nat] in MR |- *; rewrite ?zdenp_setm, ?csden_setm, ?eb_setm; try tauto.
  Qed.
  Lemma Forall_pf_setm : forall pf, Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS (env_setm E k mm)) pf.
  Proof. intros pf H. eapply Forall_impl; [|exact H]. intros f Hf. apply pfact_ok_setm. exact Hf. Qed.
  Lemma blrefs_lt_mono : forall a b bl, blrefs_lt a bl = true -> (a <= b)%nat -> blrefs_lt b bl = true.
  Proof.
    intros a b bl H Hab. induction bl as [|x n bl IH|kv]; cbn in H |- *; [reflexivity| exact (IH H)|].
    apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
  Qed.
  Lemma mrefs_lt_mono : forall a b f, mrefs_lt a f = true -> (a <= b)%nat -> mrefs_lt b f = true.
  Proof.
    intros a b f H Hab. destruct f; cbn [mrefs_lt] in H |- *; try reflexivity;
      repeat (apply andb_prop in H; destruct H as [H ?]);
      repeat match goal with
             | G : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in G
             | G : blrefs_lt a ?bl = true |- _ => apply (blrefs_lt_mono a b bl) in G; [|exact Hab]
             end;
      rewrite ?andb_true_iff; repeat split; try apply Nat.ltb_lt; try assumption; try lia.
  Qed.
End Setm.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Setls.
  Variable segs : list Segment.
  Variable G : gl.
  Notation L := (g_L G).
  Notation CS := (g_CS G).

  Lemma ew_setls : forall ls E nl i, ew (setls E nl ls) i = ew E i.
  Proof. induction ls as [|l ls IH]; intros E nl i; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma eb_setls : forall ls E nl i, eb (setls E nl ls) i = eb E i.
  Proof. induction ls as [|l ls IH]; intros E nl i; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma em_setls : forall ls E nl k, em (setls E nl ls) k = em E k.
  Proof. induction ls as [|l ls IH]; intros E nl k; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma epr_setls : forall ls E nl, epr (setls E nl ls) = epr E.
  Proof. induction ls as [|l ls IH]; intros E nl; cbn [setls]; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma eml_setls : forall ls E nl, eml (setls E nl ls) = eml E.
  Proof. induction ls as [|l ls IH]; intros E nl; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma eo_setls : forall ls E nl k, eo (setls E nl ls) k = eo E k.
  Proof. induction ls as [|l ls IH]; intros E nl k; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma elaw_setls : forall ls E nl k, elaw (setls E nl ls) k = elaw E k.
  Proof. induction ls as [|l ls IH]; intros E nl k; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma el_setls_old : forall ls E nl i, (i < nl)%positive -> el (setls E nl ls) i = el E i.
  Proof.
    induction ls as [|l ls IH]; intros E nl i Hi; cbn; [reflexivity|].
    rewrite IH by lia. rewrite el_setl. destruct (Pos.eqb_spec i nl); [lia| reflexivity].
  Qed.
  Lemma el_setls_at : forall ls E nl t, (t < length ls)%nat -> el (setls E nl ls) (Pos.of_nat (Pos.to_nat nl + t)) = nth t ls [].
  Proof.
    induction ls as [|l ls IH]; intros E nl [|t] Ht; cbn in Ht |- *; try lia.
    - rewrite el_setls_old by lia. rewrite el_setl. replace (Pos.of_nat (Pos.to_nat nl + 0)) with nl by lia. rewrite Pos.eqb_refl. reflexivity.
    - replace (Pos.to_nat nl + S t)%nat with (Pos.to_nat (Pos.succ nl) + t)%nat by lia. apply IH. lia.
  Qed.
  Lemma zdenp_setls : forall ls E nl e, zdenp (setls E nl ls) e = zdenp E e.
  Proof. intros. rewrite !zdenp_ok. apply zden_setls. Qed.
  Lemma rden_setls : forall ls E nl r, rden (setls E nl ls) r = rden E r.
  Proof. induction ls as [|l ls IH]; intros E nl r; cbn -[rden]; [reflexivity|]. rewrite IH. apply rden_setl. Qed.
  Lemma wden_setls : forall ls E nl W, wden (setls E nl ls) W = wden E W.
  Proof. induction ls as [|l ls IH]; intros E nl W; cbn -[wden]; [reflexivity|]. rewrite IH. apply wden_setl. Qed.
  Lemma mflvars_lt_mono : forall a b f, mflvars_lt a f = true -> (a <= b)%positive -> mflvars_lt b f = true.
  Proof.
    intros a b f H Hab. destruct f; cbn [mflvars_lt] in H |- *; try reflexivity.
    revert H. induction l as [k|l IH i w' v]; cbn; intros H; [apply Pos.ltb_lt in H; apply Pos.ltb_lt; lia| apply IH; exact H].
  Qed.
  Lemma llvars_lt_mono : forall a b l, llvars_lt a l = true -> (a <= b)%positive -> llvars_lt b l = true.
  Proof. intros a b l H Hab. induction l as [k|l IH i w' v]; cbn in H |- *; [apply Pos.ltb_lt in H; apply Pos.ltb_lt; lia| apply IH; exact H]. Qed.
  Lemma ldenw_setls : forall ls E nl l, llvars_lt nl l = true -> ldenw (setls E nl ls) l = ldenw E l.
  Proof.
    induction ls as [|x ls IH]; intros E nl l H; cbn -[ldenw]; [reflexivity|].
    rewrite IH by (eapply llvars_lt_mono; [exact H| lia]). apply ldenw_setl. exact H.
  Qed.
  Lemma mfact_ok_setls : forall ls E nl mm f, mflvars_lt nl f = true -> mfact_ok segs L CS (setls E nl ls) mm f <-> mfact_ok segs L CS E mm f.
  Proof.
    induction ls as [|l ls IH]; intros E nl mm f H; cbn -[mfact_ok]; [tauto|].
    rewrite IH by (eapply mflvars_lt_mono; [exact H| lia]). apply mfact_ok_setl. exact H.
  Qed.
  Lemma Forall_pf_setls : forall ls E nl pf, Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS (setls E nl ls)) pf.
  Proof. induction ls as [|l ls IH]; intros E nl pf H; cbn; [exact H|]. apply IH. apply Forall_pf_setl. exact H. Qed.
End Setls.

(* [comment removed for export] *)
Lemma elb0_setls : forall ls E nl, elb0 (setls E nl ls) = elb0 E.
Proof. induction ls as [|l ls IH]; intros E nl; cbn [setls]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma ehp_setls : forall ls E nl, ehp (setls E nl ls) = ehp E.
Proof. induction ls as [|l ls IH]; intros E nl; cbn [setls]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma ecw_setls : forall ls E nl, ecw (setls E nl ls) = ecw E.
Proof. induction ls as [|l ls IH]; intros E nl; cbn [setls]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma elh_setls : forall ls E nl, elh (setls E nl ls) = elh E.
Proof. induction ls as [|l ls IH]; intros E nl; cbn [setls]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma ehlaw_setls : forall ls E nl l, ehlaw (setls E nl ls) l = ehlaw E l.
Proof. intros. unfold ehlaw. rewrite elh_setls. reflexivity. Qed.
Lemma elbl_setls : forall ls E nl, elbl (setls E nl ls) = elbl E.
Proof. induction ls as [|l ls IH]; intros E nl; cbn [setls]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma ehr_setls : forall ls E nl, ehr (setls E nl ls) = ehr E.
Proof. induction ls as [|l ls IH]; intros E nl; cbn [setls]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma blden_setls : forall ls E nl bl, blden (setls E nl ls) bl = blden E bl.
Proof. intros ls E nl. induction bl as [|a n bl IH|kv]; cbn -[zdenp setls]; [apply elb0_setls| | unfold eblv; rewrite elbl_setls; reflexivity].
  rewrite !zdenp_setls, IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Setcur.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variable mo : Model.

  Lemma zdenp_setcur : forall e, zdenp (env_setcur E mo) e = zdenp E e.
  Proof. intros. rewrite !zdenp_ok. apply zden_setcur. Qed.
  Lemma rden_setcur : forall r, rden (env_setcur E mo) r = rden E r.
  Proof. intros [i|e]; cbn -[zdenp]; [reflexivity|]. rewrite zdenp_setcur. reflexivity. Qed.
  Lemma regs_den_setcur : forall rs, regs_den (env_setcur E mo) rs = regs_den E rs.
  Proof.
    intros rs. do 31 (destruct rs as [|? rs]; [reflexivity|]). destruct rs; [|reflexivity].
    cbn [regs_den]. rewrite !rden_setcur. reflexivity.
  Qed.
  Lemma pc_den_setcur : forall p, pc_den (env_setcur E mo) p = pc_den E p.
  Proof. intros [z|r]; cbn -[rden Z_to_bv]; [reflexivity|]. rewrite rden_setcur. reflexivity. Qed.
  Lemma ms_den_setcur : forall G ss m, ms_den segs G (env_setcur E mo) ss m = ms_den segs G E ss m.
  Proof. intros. unfold ms_den. rewrite regs_den_setcur, pc_den_setcur. reflexivity. Qed.
  Lemma cden_setcur : forall c, cden (env_setcur E mo) c = cden E c.
  Proof.
    induction c as [i|w e|w kb|w i|c IH o l|wr er]; cbn -[zdenp N.to_nat cden]; cbn [cden]; try reflexivity.
    - rewrite !zdenp_setcur. reflexivity.
    - fold (cden (env_setcur E mo) c) (cden E c). rewrite IH. reflexivity.
    - rewrite !zdenp_setcur. reflexivity.
  Qed.
  Lemma csden_setcur : forall cs, csden (env_setcur E mo) cs = csden E cs.
  Proof. intros cs. unfold csden. induction cs as [|c cs IH]; [reflexivity|]. cbn. rewrite cden_setcur, IH. reflexivity. Qed.
  Lemma wden_setcur : forall W, wden (env_setcur E mo) W = wden E W.
  Proof. intros W. unfold wden. apply map_ext. intros [lo hi]. cbn [fst snd]. rewrite !zdenp_setcur. reflexivity. Qed.
  Lemma ldenw_setcur : forall l, ldenw (env_setcur E mo) l = ldenw E l.
  Proof. induction l as [kb|l IH i w e]; cbn -[zdenp]; [reflexivity|]. rewrite IH, !zdenp_setcur. reflexivity. Qed.
  Lemma ldenb_setcur : forall l, ldenb (env_setcur E mo) l = ldenb E l.
  Proof. induction l as [kb|l IH i w e]; cbn -[zdenp wbytes upd_bytes]; [reflexivity|]. rewrite IH, !zdenp_setcur. reflexivity. Qed.
  Lemma blden_setcur : forall bl, blden (env_setcur E mo) bl = blden E bl.
  Proof. induction bl as [|a n bl IH|kv]; cbn -[zdenp env_setcur]; [reflexivity| |reflexivity]. rewrite !zdenp_setcur, IH. reflexivity. Qed.
  Lemma zdenps_setcur : forall xs, map (zdenp (env_setcur E mo)) xs = map (zdenp E) xs.
  Proof. induction xs as [|x xs IH]; cbn -[zdenp env_setcur]; [reflexivity|]. rewrite zdenp_setcur, IH. reflexivity. Qed.
  Lemma pfact_ok_setcur : forall f, pfact_ok CS (env_setcur E mo) f <-> pfact_ok CS E f.
  Proof.
    intros f.
    destruct f as [| | | | | | | | | | |pj pxs]; [| | | | | | | | | | | unfold pfact_ok, eprop; cbn [epr env_setcur]; rewrite (zdenps_setcur pxs); tauto].
    all: cbn -[zdenp Z.pow Z.of_N ez env_setcur]; rewrite ?zdenp_setcur; try tauto.
  Qed.
  Lemma Forall_pf_setcur : forall pf, Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS (env_setcur E mo)) pf.
  Proof. intros pf H. eapply Forall_impl; [|exact H]. intros f Hf. apply pfact_ok_setcur. exact Hf. Qed.
  Lemma mfact_ok_setcur : forall m f, noheap f = true -> mfact_ok segs L CS (env_setcur E mo) m f <-> mfact_ok segs L CS E m f.
  Proof.
    intros m f NH. destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok].
    7:{ cbn [mfact_ok]. rewrite !zdenp_setcur, ?ldenw_setcur, ?ldenb_setcur. tauto. }
    7:{ cbn [mfact_ok]. rewrite wden_setcur, !em_setcur. tauto. }
    7:{ cbn [mfact_ok]. rewrite !em_setcur. tauto. }
    7:{ cbn [mfact_ok]. rewrite wden_setcur, !em_setcur, elaw_setcur. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setcur, elaw_setcur. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setcur, elaw_setcur. tauto. }
    7:{ discriminate NH. }
    7:{ cbn [mfact_ok]. rewrite blden_setcur, zdenp_setcur, wden_setcur, !em_setcur. unfold ehlaw. cbn [elh env_setcur]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setcur. unfold hlawcli, ehlaw. cbn [elb0 elh env_setcur]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setcur, blden_setcur. tauto. }
    7:{ cbn [mfact_ok]. unfold hlawopq, ehlaw, eo. cbn [elb0 elh eol env_setcur]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !blden_setcur, wden_setcur, zdenps_setcur. unfold ehres, ecw, elb0. cbn [ehr env_setcur]. tauto. }
    all: try solve [cbn [mfact_ok]; rewrite !wden_setcur; unfold eo; cbn [eol env_setcur]; tauto].
    all: cbn -[zdenp csden eb rw_cells ro_cells bytes_at stk aobj Z.of_nat]; rewrite ?zdenp_setcur, ?csden_setcur, ?eb_setcur; try tauto.
  Qed.
End Setcur.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Setbl.
  Variable segs : list Segment.
  Variable L : asan_layout.
  Variable CS : Z -> Prop.
  Variable E : env.
  Variable k : nat.
  Variable lb : list (Z * Z).
  Lemma zdenp_setbl : forall e, zdenp (env_setbl E k lb) e = zdenp E e.
  Proof. intros. rewrite !zdenp_ok. apply zden_setbl. Qed.
  Lemma rden_setbl : forall r, rden (env_setbl E k lb) r = rden E r.
  Proof. intros [i|e]; cbn -[zdenp]; [reflexivity|]. rewrite zdenp_setbl. reflexivity. Qed.
  Lemma regs_den_setbl : forall rs, regs_den (env_setbl E k lb) rs = regs_den E rs.
  Proof.
    intros rs. do 31 (destruct rs as [|? rs]; [reflexivity|]). destruct rs; [|reflexivity].
    cbn [regs_den]. rewrite !rden_setbl. reflexivity.
  Qed.
  Lemma pc_den_setbl : forall p, pc_den (env_setbl E k lb) p = pc_den E p.
  Proof. intros [z|r]; cbn -[rden Z_to_bv]; [reflexivity|]. rewrite rden_setbl. reflexivity. Qed.
  Lemma ms_den_setbl : forall G ss m, ms_den segs G (env_setbl E k lb) ss m = ms_den segs G E ss m.
  Proof. intros. unfold ms_den. rewrite regs_den_setbl, pc_den_setbl. reflexivity. Qed.
  Lemma cden_setbl : forall c, cden (env_setbl E k lb) c = cden E c.
  Proof.
    induction c as [i|w e|w kk|w i|c IH o l|w e]; cbn -[zdenp cden]; cbn [cden]; try reflexivity.
    - rewrite !zdenp_setbl. reflexivity.
    - fold (cden (env_setbl E k lb) c) (cden E c). rewrite IH. reflexivity.
    - rewrite !zdenp_setbl. reflexivity.
  Qed.
  Lemma csden_setbl : forall cs, csden (env_setbl E k lb) cs = csden E cs.
  Proof. intros cs. unfold csden. induction cs as [|c cs IH]; [reflexivity|]. cbn. rewrite cden_setbl, IH. reflexivity. Qed.
  Lemma wden_setbl : forall W, wden (env_setbl E k lb) W = wden E W.
  Proof. intros W. unfold wden. apply map_ext. intros [lo hi]. cbn [fst snd]. rewrite !zdenp_setbl. reflexivity. Qed.
  Lemma ldenw_setbl : forall l, ldenw (env_setbl E k lb) l = ldenw E l.
  Proof. induction l as [kb|l IH i w e]; cbn -[zdenp]; [reflexivity|]. rewrite IH, !zdenp_setbl. reflexivity. Qed.
  Lemma ldenb_setbl : forall l, ldenb (env_setbl E k lb) l = ldenb E l.
  Proof. induction l as [kb|l IH i w e]; cbn -[zdenp wbytes upd_bytes]; [reflexivity|]. rewrite IH, !zdenp_setbl. reflexivity. Qed.
  Lemma eblv_setbl : forall j, eblv (env_setbl E k lb) j = if Nat.eqb j k then lb else eblv E j.
  Proof. intros j. unfold eblv, env_setbl. cbn [elbl]. apply nth_nset. Qed.
  Lemma blden_setbl : forall bl, blrefs_lt k bl = true -> blden (env_setbl E k lb) bl = blden E bl.
  Proof.
    induction bl as [|a n bl IH|kv]; cbn -[zdenp env_setbl Nat.ltb eblv]; intros H; [reflexivity| |].
    - rewrite !zdenp_setbl, IH by exact H. reflexivity.
    - rewrite eblv_setbl. apply Nat.ltb_lt in H. destruct (Nat.eqb_spec kv k); [lia| reflexivity].
  Qed.
  Lemma zdenps_setbl : forall xs, map (zdenp (env_setbl E k lb)) xs = map (zdenp E) xs.
  Proof. induction xs as [|x xs IH]; cbn -[zdenp env_setbl]; [reflexivity|]. rewrite zdenp_setbl, IH. reflexivity. Qed.
  Lemma pfact_ok_setbl : forall f, pfact_ok CS (env_setbl E k lb) f <-> pfact_ok CS E f.
  Proof.
    intros f.
    destruct f as [| | | | | | | | | | |pj pxs]; [| | | | | | | | | | | unfold pfact_ok, eprop; cbn [epr env_setbl]; rewrite zdenps_setbl; tauto].
    all: cbn -[zdenp Z.pow Z.of_N ez env_setbl]; rewrite ?zdenp_setbl; try tauto.
  Qed.
  Lemma Forall_pf_setbl : forall pf, Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS (env_setbl E k lb)) pf.
  Proof. intros pf H. eapply Forall_impl; [|exact H]. intros f Hf. apply pfact_ok_setbl. exact Hf. Qed.
  Lemma mfact_ok_setbl : forall m f, mrefs_lt k f = true -> mfact_ok segs L CS (env_setbl E k lb) m f <-> mfact_ok segs L CS E m f.
  Proof.
    intros m f MR. destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok];
      cbn [mrefs_lt] in MR; repeat (apply andb_prop in MR; destruct MR as [MR ?]).
    7:{ cbn [mfact_ok]. rewrite !zdenp_setbl, ?ldenw_setbl, ?ldenb_setbl. tauto. }
    7:{ cbn [mfact_ok]. rewrite wden_setbl. unfold em. cbn [eml env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. unfold em. cbn [eml env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. rewrite wden_setbl. unfold em, elaw. cbn [eml elw env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setbl. unfold elaw. cbn [elw env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setbl. unfold elaw. cbn [elw env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. rewrite blden_setbl, wden_setbl by assumption. unfold ehp, ecw, ecur, elh, elb0. cbn [env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. rewrite blden_setbl, zdenp_setbl, wden_setbl by assumption. unfold em, ehlaw. cbn [eml elh env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setbl. unfold hlawcli, ehlaw. cbn [elb0 elh env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !zdenp_setbl, blden_setbl by assumption. tauto. }
    7:{ cbn [mfact_ok]. unfold hlawopq, ehlaw, eo. cbn [elb0 elh eol env_setbl]. tauto. }
    7:{ cbn [mfact_ok]. rewrite !blden_setbl, wden_setbl, zdenps_setbl by assumption. unfold ehres, ecw, elb0. cbn [ehr env_setbl]. tauto. }
    all: try solve [cbn [mfact_ok]; rewrite !wden_setbl; unfold eo; cbn [eol env_setbl]; tauto].
    all: cbn -[zdenp csden eb rw_cells ro_cells bytes_at stk aobj Z.of_nat]; rewrite ?zdenp_setbl, ?csden_setbl, ?eb_setbl; try tauto.
  Qed.
End Setbl.

Section Main.
  Variable segs : list Segment.
  Variable AL : asan_layout.
  Variable GS : list Z.
  Variable OPS : list (mem -> Prop).
  Variable LAWS : list (list (Z * Z) -> mem -> mem -> Prop).
  Variable PROPS : list (list Z -> Prop).

  Variable CS : Z -> Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition summary_okP_at (su : summary) : Prop :=
    forall F fc m0 me C genv LB0 HP CW LH HRS (TGT : Model -> machine_state -> Prop),
      summary_at segs (GL AL CS F fc m0 me) C genv GS OPS LAWS PROPS LB0 HP CW LH HRS TGT su.

  Lemma match_globals_ok : forall genv gb th th', match_globals genv gb th = Some th' ->
    thsub th th' /\ Forall (fun gn => exists g, nth_error genv (snd gn) = Some g /\ sub_get th' (fst gn) = Some g) gb.
  Proof.
    intros genv gb. induction gb as [|[i n] gb IH]; intros th th' H; cbn in H.
    - injection H; intros <-. split; [apply thsub_refl| constructor].
    - destruct (nth_error genv n) as [g|] eqn:NG; [|discriminate].
      destruct (bind th i g) as [th1|] eqn:B; [|discriminate].
      destruct (bind_ok _ _ _ _ B) as [G1 S1]. destruct (IH _ _ H) as [S2 F2].
      split; [eapply thsub_trans; eauto|]. constructor; [|exact F2]. exists g. split; [exact NG| apply S2; exact G1].
  Qed.

  Lemma match_globals_P : forall P genv gb th th', thP P th -> (forall g, In g genv -> P g) -> match_globals genv gb th = Some th' -> thP P th'.
  Proof.
    intros P genv gb. induction gb as [|[i n] gb IH]; intros th th' HT HG H; cbn in H.
    - injection H; intros <-. exact HT.
    - destruct (nth_error genv n) as [g|] eqn:NG; [|discriminate].
      destruct (bind th i g) as [th1|] eqn:B; [|discriminate].
      eapply IH; [| exact HG| exact H]. eapply bind_P; [exact HT| | exact B]. apply HG. eapply nth_error_In. exact NG.
  Qed.

  Lemma gb_tele_elim : forall E gb P, gb_tele E GS gb P -> (forall i n, In (i, n) gb -> ez E i = nth n GS 0) -> P.
  Proof.
    induction gb as [|[i n] gb IH]; intros P H HE; cbn in H; [exact H|].
    apply (IH P); [apply H; apply HE; left; reflexivity|]. intros i' n' Hin. apply HE. right. exact Hin.
  Qed.

  Lemma Forall2_nth_error : forall (R : expr -> Z -> Prop) l1 l2 n a, Forall2 R l1 l2 -> nth_error l1 n = Some a -> R a (nth n l2 0).
  Proof.
    intros R l1 l2 n a H. revert n. induction H as [|x y l1' l2' Hxy H IH]; intros [|n] Hn; cbn in Hn; try discriminate.
    - injection Hn; intros <-. exact Hxy.
    - cbn. apply IH. exact Hn.
  Qed.

  (* [comment removed for export] *)
  Definition thv (th : subst) (i : positive) : expr := match sub_get th i with Some e => e | None => ELit 0 end.
  Definition pvals (E : env) (th : subst) (np : nat) : list Z := map (fun t => zden E (thv th (Pos.of_nat t))) (seq 1 np).
  Definition bvalk (E : env) (tb : bsubst) (k : positive) : list byte :=
    match bsub_get tb k with Some bv => bval_den E bv | None => [] end.
  Definition bvals (E : env) (tb : bsubst) (nb : nat) : list (list byte) := map (fun t => bvalk E tb (Pos.of_nat t)) (seq 1 nb).

  (* [comment removed for export] *)
  Definition tlv (tl : lsubst) (j : positive) : lexpr := match lsub_get tl j with Some l => l | None => LBase 1%positive end.
  Definition lvals (E : env) (tl : lsubst) (nl : nat) : list (list word) := map (fun t => ldenw E (tlv tl (Pos.of_nat t))) (seq 1 nl).
  Lemma lvals_length : forall E tl nl, length (lvals E tl nl) = nl.
  Proof. intros. unfold lvals. rewrite map_length, seq_length. reflexivity. Qed.

  Lemma pvals_length : forall E th np, length (pvals E th np) = np.
  Proof. intros. unfold pvals. rewrite map_length, seq_length. reflexivity. Qed.
  Lemma bvals_length : forall E tb nb, length (bvals E tb nb) = nb.
  Proof. intros. unfold bvals. rewrite map_length, seq_length. reflexivity. Qed.

  Lemma nth_map_seq : forall {B} (f : nat -> B) n s k d, (k < n)%nat -> nth k (map f (seq s n)) d = f (s + k)%nat.
  Proof.
    induction n as [|n IH]; intros s k d Hk; [lia|]. cbn [seq map]. destruct k as [|k]; cbn [nth]; [f_equal; lia|].
    rewrite IH by lia. f_equal. lia.
  Qed.

  Lemma pvals_get : forall E th np i, (Pos.to_nat i <= np)%nat -> pget (pvals E th np) i 0 = zden E (thv th i).
  Proof.
    intros E th np i Hi. rewrite pget_nth. unfold pvals. rewrite nth_map_seq by lia. f_equal. f_equal. lia.
  Qed.

  Lemma bvals_get : forall E tb nb k, (Pos.to_nat k <= nb)%nat -> pget (bvals E tb nb) k [] = bvalk E tb k.
  Proof.
    intros E tb nb k Hk. rewrite pget_nth. unfold bvals. rewrite nth_map_seq by lia. f_equal. f_equal. lia.
  Qed.
  Lemma lvals_get : forall E tl nl j, (Pos.to_nat j <= nl)%nat -> pget (lvals E tl nl) j [] = ldenw E (tlv tl j).
  Proof.
    intros E tl nl j Hj. rewrite pget_nth. unfold lvals. rewrite nth_map_seq by lia. f_equal. f_equal. lia.
  Qed.

  Lemma pget_app_l : forall {A} (l1 l2 : list A) i d, (Pos.to_nat i <= length l1)%nat -> pget (l1 ++ l2) i d = pget l1 i d.
  Proof. intros. rewrite !pget_nth. apply app_nth1. lia. Qed.
  Lemma pget_app_r : forall {A} (l1 l2 : list A) i d, (length l1 < Pos.to_nat i)%nat ->
    pget (l1 ++ l2) i d = nth (Pos.to_nat i - 1 - length l1) l2 d.
  Proof. intros. rewrite pget_nth. rewrite app_nth2 by lia. reflexivity. Qed.

  Lemma res_subst_get : forall f nr nx th i,
    sub_get (res_subst f nr nx th) i =
      if (Pos.leb f i && Pos.ltb i (Pos.of_nat (Pos.to_nat f + nr)))%bool
      then Some (eatom (EZv (Pos.of_nat (Pos.to_nat nx + (Pos.to_nat i - Pos.to_nat f)))))
      else sub_get th i.
  Proof.
    intros f nr. revert f. induction nr as [|nr IH]; intros f nx th i; cbn [res_subst].
    - destruct (Pos.leb_spec f i); destruct (Pos.ltb_spec i (Pos.of_nat (Pos.to_nat f + 0))); cbn; try reflexivity. exfalso. lia.
    - rewrite IH. cbn [sub_get].
      destruct (Pos.leb_spec (Pos.succ f) i); destruct (Pos.ltb_spec i (Pos.of_nat (Pos.to_nat (Pos.succ f) + nr)));
      destruct (Pos.eqb_spec i f); destruct (Pos.leb_spec f i); destruct (Pos.ltb_spec i (Pos.of_nat (Pos.to_nat f + S nr))); cbn [andb]; try reflexivity; try (exfalso; lia).
      + do 3 f_equal. lia.
      + subst i. do 3 f_equal. lia.
  Qed.

  Lemma lres_subst_get : forall f nr nx tl i,
    lsub_get (lres_subst f nr nx tl) i =
      if (Pos.leb f i && Pos.ltb i (Pos.of_nat (Pos.to_nat f + nr)))%bool
      then Some (LBase (Pos.of_nat (Pos.to_nat nx + (Pos.to_nat i - Pos.to_nat f))))
      else lsub_get tl i.
  Proof.
    intros f nr. revert f. induction nr as [|nr IH]; intros f nx tl i; cbn [lres_subst].
    - destruct (Pos.leb_spec f i); destruct (Pos.ltb_spec i (Pos.of_nat (Pos.to_nat f + 0))); cbn; try reflexivity. exfalso. lia.
    - rewrite IH. cbn [lsub_get].
      destruct (Pos.leb_spec (Pos.succ f) i); destruct (Pos.ltb_spec i (Pos.of_nat (Pos.to_nat (Pos.succ f) + nr)));
      destruct (Pos.eqb_spec i f); destruct (Pos.leb_spec f i); destruct (Pos.ltb_spec i (Pos.of_nat (Pos.to_nat f + S nr))); cbn [andb]; try reflexivity; try (exfalso; lia).
      + do 3 f_equal. lia.
      + subst i. do 3 f_equal. lia.
  Qed.
  Lemma lall_bound_ok : forall tl n i j, lall_bound tl n i = true -> (i <= j)%positive -> (Pos.to_nat j < Pos.to_nat i + n)%nat -> lsub_get tl j <> None.
  Proof.
    intros tl n. induction n as [|n IH]; intros i j H Hij Hj; [lia|]. cbn in H.
    destruct (lsub_get tl i) eqn:G; [|discriminate].
    destruct (Pos.eq_dec i j) as [<-|NE]; [rewrite G; discriminate|]. apply (IH (Pos.succ i)); [exact H| lia| lia].
  Qed.
  Lemma match_arrs_LQ : forall (Q : lexpr -> Prop) pf mf mb th tl th' tl',
    (forall j l, lsub_get tl j = Some l -> Q l) -> (forall a w l n wr, In (MArr a w l n wr) mf -> Q l) ->
    match_arrs pf mf mb th tl = Some (th', tl') -> forall j l, lsub_get tl' j = Some l -> Q l.
  Proof.
    intros Q pf mf mb. induction mb as [|f mb IH]; intros th tl th' tl' HT HN H; cbn [match_arrs] in H.
    - injection H; intros <- <-. exact HT.
    - destruct f as [| | | | | |pa w [j|pl pi pw pv] pn wr| | | | | | | | | | |hj ho hn hxs hok]; try (eapply IH; [exact HT| exact HN| exact H]); [|discriminate].
      destruct (ebound th pa && (N.eqb w 4 || N.eqb w 8)); [|discriminate].
      destruct (find_arr mf (sxe th pa) w wr) as [[lc n]|] eqn:FA; [|discriminate].
      destruct (lbind tl j lc) as [tl1|] eqn:LB; [|discriminate].
      match type of H with (match ?o with Some _ => _ | None => None end) = _ => destruct o as [th1|] eqn:BN; [|discriminate] end.
      eapply IH; [| exact HN| exact H].
      intros i x Hi. unfold lbind in LB. destruct (lsub_get tl j) as [l0|] eqn:G.
      + destruct (lexpr_eqb l0 lc); [|discriminate]. injection LB; intros <-. exact (HT i x Hi).
      + injection LB; intros <-. cbn in Hi. destruct (Pos.eqb_spec i j) as [->|].
        * injection Hi; intros <-. destruct (find_arr_In _ _ _ _ _ _ FA) as (wr' & Hin & _). exact (HN _ _ _ _ _ Hin).
        * exact (HT i x Hi).
  Qed.

  Lemma ez_setzs_at : forall vs E nx t, (t < length vs)%nat -> ez (setzs E nx vs) (Pos.of_nat (Pos.to_nat nx + t)) = nth t vs 0.
  Proof.
    induction vs as [|v vs IH]; intros E nx t Ht; cbn in Ht; [lia|]. cbn [setzs].
    destruct t as [|t].
    - replace (Pos.of_nat (Pos.to_nat nx + 0)) with nx by lia. cbn [nth]. rewrite ez_setzs_old by lia. rewrite ez_setz, Pos.eqb_refl. reflexivity.
    - cbn [nth]. rewrite <- (IH (env_setz E nx v) (Pos.succ nx) t) by lia. f_equal. lia.
  Qed.
  Lemma lget_nth : forall {A} (l : list A) n d, lget l n d = nth n l d.
  Proof. induction l as [|x l IH]; intros [|n] d; cbn; try reflexivity. apply IH. Qed.

  Lemma nth_map' : forall {A B} (f : A -> B) l n d d', (n < length l)%nat -> nth n (map f l) d' = f (nth n l d).
  Proof. induction l as [|x l IH]; intros [|n] d d' H; cbn in H |- *; try lia; [reflexivity|]. apply IH. lia. Qed.

  Lemma map_lset : forall {A B} (f : A -> B) l n x, map f (lset l n x) = lset (map f l) n (f x).
  Proof. induction l as [|y l IH]; intros [|n] x; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

  Lemma pset_lset : forall {A} (l : list A) p v d, (Pos.to_nat p <= length l)%nat -> pset l p v d = lset l (Pos.to_nat p - 1) v.
  Proof.
    induction l as [|x l IH]; intros p v d H; cbn in H; [lia|]. cbn [pset].
    destruct p as [q|q|].
    - replace (Pos.to_nat (xI q) - 1)%nat with (S (Pos.to_nat (Pos.pred (xI q)) - 1))%nat by lia. cbn [lset]. rewrite IH by lia. reflexivity.
    - replace (Pos.to_nat (xO q) - 1)%nat with (S (Pos.to_nat (Pos.pred (xO q)) - 1))%nat by lia. cbn [lset]. rewrite IH by lia. reflexivity.
    - reflexivity.
  Qed.

  Lemma set_regs_length : forall rs cl, length (set_regs rs cl) = length rs.
  Proof. intros rs cl. revert rs. induction cl as [|[r e] cl IH]; intros rs; cbn; [reflexivity|]. rewrite IH, lset_length. reflexivity. Qed.

  Lemma rb_tele_elim : forall R E rb P, rb_tele R E rb P -> (forall r i, In (r, i) rb -> rgetZ R r = Z_to_bv 64 (ez E i)) -> P.
  Proof.
    induction rb as [|[r i] rb IH]; intros P H HE; cbn in H; [exact H|].
    apply (IH P); [apply H; apply HE; left; reflexivity|]. intros r' i' Hin. apply HE. right. exact Hin.
  Qed.

  Lemma mf_tele_elim : forall G E mm mf P, mf_tele segs G E mm mf P -> Forall (mfact_ok segs (g_L G) (g_CS G) E mm) mf -> P.
  Proof.
    induction mf as [|f mf IH]; intros P H HF; cbn in H; [exact H|]. inversion HF; subst. apply (IH P); [apply H|]; assumption.
  Qed.

  Lemma pf_tele_elim : forall G E pf P, pf_tele G E pf P -> Forall (pfact_ok (g_CS G) E) pf -> P.
  Proof.
    induction pf as [|f pf IH]; intros P H HF; cbn in H; [exact H|]. inversion HF; subst. apply (IH P); [apply H|]; assumption.
  Qed.

  Lemma mf_conj_elim : forall L CS E mm mf P, mf_conj segs L CS E mm mf P -> Forall (mfact_ok segs L CS E mm) mf /\ P.
  Proof.
    induction mf as [|f mf IH]; intros P H; cbn in H; [split; [constructor| exact H]|].
    destruct H as [Hf H]. destruct (IH P H) as [HF HP]. split; [constructor; assumption| exact HP].
  Qed.

  Lemma oq_conj_elim : forall OQ mm ks P, oq_conj OQ mm ks P -> (forall k, In k ks -> nth k OQ (fun _ => True) mm) /\ P.
  Proof.
    intros OQ mm ks. induction ks as [|k ks IH]; intros P H; cbn in H; [split; [intros k []| exact H]|].
    destruct H as [Hk H]. destruct (IH P H) as [A B]. split; [|exact B]. intros k' [<-|Hin]; [exact Hk| apply A; exact Hin].
  Qed.
  Lemma oq_tele_elim : forall OQ mm ks P, oq_tele OQ mm ks P -> (forall k, In k ks -> nth k OQ (fun _ => True) mm) -> P.
  Proof.
    intros OQ mm ks. induction ks as [|k ks IH]; intros P H HK; cbn in H; [exact H|].
    apply (IH P); [apply H; apply HK; left; reflexivity| intros k' Hin; apply HK; right; exact Hin].
  Qed.
  Lemma pf_conj_elim : forall CS E pf P, pf_conj CS E pf P -> Forall (pfact_ok CS E) pf /\ P.
  Proof.
    induction pf as [|f pf IH]; intros P H; cbn in H; [split; [constructor| exact H]|].
    destruct H as [Hf H]. destruct (IH P H) as [HF HP]. split; [constructor; assumption| exact HP].
  Qed.


  Lemma keys_lt_sound : forall th n, forallb (fun p : positive * expr => Pos.ltb (fst p) n) th = true ->
    forall i e, sub_get th i = Some e -> (i < n)%positive.
  Proof.
    induction th as [|[j x] th IH]; intros n H i e G; cbn in H, G; [discriminate|].
    apply andb_prop in H as [H1 H2]. destruct (Pos.eqb_spec i j) as [->|]; [apply Pos.ltb_lt in H1; exact H1| eapply IH; eauto].
  Qed.

  Lemma bkeys_lt_sound : forall tb n, forallb (fun p : positive * bval => Pos.ltb (fst p) n) tb = true ->
    forall i k, bsub_get tb i = Some k -> (i < n)%positive.
  Proof.
    induction tb as [|[j x] tb IH]; intros n H i k G; cbn in H, G; [discriminate|].
    apply andb_prop in H as [H1 H2]. destruct (Pos.eqb_spec i j) as [->|]; [apply Pos.ltb_lt in H1; exact H1| eapply IH; eauto].
  Qed.

  Lemma install_post_Forall : forall (P : mfact -> Prop) kept new,
    Forall P kept -> Forall P new -> Forall P (install_post kept new).
  Proof.
    intros P kept new. revert kept. induction new as [|f new IH]; intros kept HK HN; cbn; [exact HK|].
    inversion HN; subst.
    assert (DR : forall a l, Forall P l -> Forall P (drop_rw_at l a)).
    { intros a l. induction l as [|g l IHl]; intros Hl; cbn; [constructor|]. inversion Hl; subst.
      destruct g; try (constructor; [assumption| apply IHl; assumption]).
      destruct (expr_eqb a a0); [apply IHl; assumption| constructor; [assumption| apply IHl; assumption]]. }
    destruct f; apply IH; try assumption; constructor; try assumption; apply DR; assumption.
  Qed.

  Lemma fold_pf_add_Forall : forall (P : pfact -> Prop) new base,
    Forall P base -> Forall P new -> Forall P (fold_left (fun l f => pf_add f l) new base).
  Proof.
    intros P new. induction new as [|f new IH]; intros base HB HN; cbn; [exact HB|]. inversion HN; subst.
    apply IH; [|assumption]. unfold pf_add. destruct (pf_mem f base); [exact HB| constructor; assumption].
  Qed.

  Lemma outside_app : forall A B x, outside (A ++ B) x <-> outside A x /\ outside B x.
  Proof. induction A as [|[lo hi] A IH]; intros B x; cbn; [tauto|]. rewrite IH. tauto. Qed.

  Lemma munch_app : forall A B (ma mb mc : mem), munch A ma mb -> munch B mb mc -> munch (A ++ B) ma mc.
  Proof.
    intros A B ma mb mc H1 H2 x Hx. apply outside_app in Hx as [HA HB]. rewrite (H2 x HB). apply H1. exact HA.
  Qed.

  (* [comment removed for export] *)
  Lemma w_add_sub : forall E pf W a b x,
    (forall l h, dec_le00 pf l h = true -> zden E l <= zden E h) -> zden E a <= zden E b ->
    outside (wden E (w_add pf W a b)) x -> outside (wden E W) x /\ ~ (zden E a <= x < zden E b).
  Proof.
    intros E pf W a b x DLE AB. unfold wden. induction W as [|[l h] W IH]; cbn [w_add map outside fst snd]; rewrite ?zdenp_ok.
    - intros [H _]. split; [exact I| exact H].
    - do 3 unlazy1. destruct (dec_le00 pf l a && dec_le00 pf b h) eqn:D12.
      + apply andb_prop in D12 as [D1 D2]. apply DLE in D1. apply DLE in D2. cbn [map outside fst snd]. rewrite !zdenp_ok.
        intros [H1 H2]. split; [split; [exact H1| exact H2]| lia].
      + destruct (expr_eqb b l && dec_le00 pf l h) eqn:D3.
        * apply andb_prop in D3 as [E1 D3]. apply expr_eqb_eq in E1. subst l. apply DLE in D3. cbn [map outside fst snd]. rewrite !zdenp_ok.
          intros [H1 H2]. split; [split; [lia| exact H2]| lia].
        * destruct (expr_eqb h a && dec_le00 pf l h) eqn:D4.
          -- apply andb_prop in D4 as [E2 D4]. apply expr_eqb_eq in E2. subst h. apply DLE in D4. cbn [map outside fst snd]. rewrite !zdenp_ok.
             intros [H1 H2]. split; [split; [lia| exact H2]| lia].
          -- cbn [map outside fst snd]. rewrite !zdenp_ok. intros [H1 H2]. destruct (IH H2) as [H3 H4]. split; [split; [exact H1| exact H3]| exact H4].
  Qed.

  Lemma w_adds_sub : forall E pf W0 W x,
    (forall l h, dec_le00 pf l h = true -> zden E l <= zden E h) ->
    outside (wden E (w_adds pf W0 W)) x -> outside (wden E W0 ++ wden E W) x.
  Proof.
    intros E pf W0 W x DLE. revert W0. induction W as [|[a b] W IH]; intros W0 H; cbn [w_adds] in H.
    - unfold wden in *. cbn. rewrite app_nil_r. exact H.
    - apply IH in H. apply outside_app in H as [H1 H2].
      assert (H0 : outside (wden E W0) x /\ ~ (zden E a <= x < zden E b)).
      { destruct (dec_le00 pf a b) eqn:D.
        - exact (w_add_sub E pf W0 a b x DLE (DLE _ _ D) H1).
        - unfold wden in H1 |- *. rewrite map_app in H1. apply outside_app in H1 as [H1 H3]. cbn in H3. rewrite !zdenp_ok in H3. tauto. }
      destruct H0 as [H0 Hab].
      apply outside_app. split; [exact H0|]. unfold wden in *. cbn [map outside fst snd]. rewrite !zdenp_ok. split; [exact Hab| exact H2].
  Qed.

  (* [comment removed for export] *)
  Lemma w_adds_ends : forall (Q : expr -> Prop) pf W0 W,
    Forall (fun lh => Q (fst lh) /\ Q (snd lh)) W0 -> Forall (fun lh => Q (fst lh) /\ Q (snd lh)) W ->
    Forall (fun lh => Q (fst lh) /\ Q (snd lh)) (w_adds pf W0 W).
  Proof.
    intros Q pf W0 W. revert W0. induction W as [|[a b] W IH]; intros W0 H0 H; cbn; [exact H0|]. inversion H as [|x l [Qa Qb] H']; subst.
    apply IH; [|exact H']. clear IH H H'. cbn [fst snd] in Qa, Qb.
    destruct (dec_le00 pf a b).
    2:{ apply Forall_app. split; [exact H0| constructor; [split; assumption| constructor]]. }
    induction W0 as [|[l h] W0 IH0]; cbn.
    - constructor; [split; assumption| constructor].
    - inversion H0 as [|x' l' [Ql Qh] H0']; subst. cbn [fst snd] in Ql, Qh. do 3 unlazy1.
      destruct (dec_le00 pf l a && dec_le00 pf b h); [exact H0|].
      destruct (expr_eqb b l && dec_le00 pf l h); [constructor; [split; assumption| exact H0']|].
      destruct (expr_eqb h a && dec_le00 pf l h); [constructor; [split; assumption| exact H0']|].
      constructor; [split; assumption| apply IH0; exact H0'].
  Qed.

  Lemma wden_ext : forall E1 E2 W, Forall (fun lh => zdenp E1 (fst lh) = zdenp E2 (fst lh) /\ zdenp E1 (snd lh) = zdenp E2 (snd lh)) W ->
    wden E1 W = wden E2 W.
  Proof.
    intros E1 E2 W H. unfold wden. induction H as [|[l h] W [H1 H2] H IH]; cbn; [reflexivity|]. cbn [fst snd] in H1, H2. rewrite H1, H2, IH. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma zden_app_env : forall OQ LW PQ QB1 QH1 QC1 QL1 QM1 QV1 QR1 QB2 QH2 QC2 QL2 QM2 QV2 QR2 LS1 LS2 ps rs bss e, eloc (Pos.of_nat (S (length ps))) e = true ->
    zden (ENV (ps ++ rs) [] bss OQ LS1 [] LW PQ QB1 QH1 QC1 QL1 QM1 QV1 QR1) e = zden (ENV ps [] bss OQ LS2 [] LW PQ QB2 QH2 QC2 QL2 QM2 QV2 QR2) e.
  Proof.
    intros OQ LW PQ QB1 QH1 QC1 QL1 QM1 QV1 QR1 QB2 QH2 QC2 QL2 QM2 QV2 QR2 LS1 LS2 ps rs bss e. induction e; cbn -[Pos.ltb Pos.of_nat pget]; intros H; try reflexivity; try discriminate.
    - unfold ez. cbn [ezl]. apply Pos.ltb_lt in H. rewrite pget_app_l by lia. reflexivity.
    - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
    - rewrite IHe by assumption. reflexivity.
    - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  Qed.

  Lemma ret_pc_lit : forall z, ret_pc (Z_to_bv 64 z) = Z_to_bv 64 (Z.land (zlow 64 z) (Z.lnot 1)).
  Proof.
    intros z. unfold ret_pc. replace (bv_not (Z_to_bv 64 1)) with (Z_to_bv 64 (Z.lnot 1) : word) by (apply bv_eq; reflexivity).
    rewrite w64_and. apply w64_eq. unfold zlow.
    rewrite <- (land_mod_pow2 z), <- (land_mod_pow2 (z mod 2 ^ 64)), Z.mod_mod by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem apply_summary0_sound : forall su F fc m0 me C genv E ss m,
    summary_validP segs AL GS OPS LAWS PROPS su CS ->
    Forall2 (fun g v => zden E g = v) genv GS -> eol E = OPS /\ elw E = LAWS /\ epr E = PROPS -> hp_frame segs (ehp E) (ecw E) -> hp_blk (ecw E) ->
    forallb (evars_lt (s_nx ss)) genv = true ->
    cfg_ok (GL AL CS F fc m0 me) C E -> length (s_rs ss) = 31%nat -> ss_wf C ss = true -> INV segs (GL AL CS F fc m0 me) E ss m ->
    match apply_summary0 C genv su ss with
    | SumOk k kl ss' =>
        evtA segs AL CS (fun ms' => exists vs ls m', length vs = k /\ length ls = kl /\ length (s_rs ss') = 31%nat
                                   /\ ms' = ms_den segs (GL AL CS F fc m0 me) (env_call E (s_nx ss) vs (s_nl ss) ls) ss' m'
                                   /\ INV segs (GL AL CS F fc m0 me) (env_call E (s_nx ss) vs (s_nl ss) ls) ss' m') (ms_den segs (GL AL CS F fc m0 me) E ss m)
    | SumOkL k kl ss' =>
        evtA segs AL CS (fun ms' => exists vs ls mc mp m', length vs = k /\ length ls = kl /\ length (s_rs ss') = 31%nat
                                   /\ s_nm ss' = S (S (s_nm ss))
                                   /\ ms' = ms_den segs (GL AL CS F fc m0 me) (env_law E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp) ss' m'
                                   /\ INV segs (GL AL CS F fc m0 me) (env_law E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp) ss' m') (ms_den segs (GL AL CS F fc m0 me) E ss m)
    | SumOkM _ _ _ _ => False     (* [comment removed for export] *)
    | SumFail _ => True
    end.
  Proof.
    intros su F fc m0 me C genv E ss m V GV (EO & ELW & EPR) HPFE HBKE GWF CFG Hlen WF HI.
    unfold summary_validP in V. destruct (su_heap su) as [hc0|] eqn:HEAP; [destruct V|].
    pose proof HI as (HM & HP & MU & WM & MI & SAME). cbn [g_L g_CS g_m0 g_F g_fc] in HM, HP, MU, WM |- *.
    pose proof (mk_oracle_sound CS E _ HP) as HO.
    pose proof (cranges_sound segs AL CS E m _ _ HP HM) as CR.
    unfold apply_summary0.
    destruct (su_wf su) eqn:SWF; [|exact I].
    destruct (Bool.eqb (su_acc su) (acc_mode C)) eqn:ACC; [|exact I]. apply Bool.eqb_prop in ACC.
    destruct (Nat.eqb_spec (length (s_rs ss)) 31) as [L31|]; [|exact I]. cbn [negb].
    destruct (forallb (mflvars_lt (s_nl ss)) (s_mf ss)) eqn:MLF; [|exact I]. cbn [negb].
    destruct (s_pc ss) as [pc|r] eqn:HPC; [|exact I].
    destruct (Z.eqb_spec pc (su_pc su)) as [->|]; [|exact I]. cbn [negb].
    match goal with |- match (match ?o with Some _ => _ | None => _ end) with _ => _ end => destruct o as [ra|] eqn:RA; [|exact I] end.
    destruct (sum_match C genv su ss) as [[[th tb] tl] code] eqn:SM. destruct code; try exact I.
    destruct (forallb (post_blobs_ok tb) (su_req su ++ su_mpost su)) eqn:PBO; [|exact I]. cbn [negb].
    destruct (opq_required (s_mf ss) (su_oreq su)) as [oql|] eqn:OQR; [|exact I].
    rewrite HEAP.
    rewrite forallb_app in PBO. apply andb_prop in PBO as [PBOreq PBOpost].
    (* [comment removed for export] *)
    unfold sum_match in SM.
    destruct (match_regs ss (su_rbind su) []) as [th0|] eqn:MR; [|discriminate].
    destruct (match_globals genv (su_gbind su) th0) as [th1|] eqn:MG; [|discriminate].
    match type of SM with match ?o with _ => _ end = _ => destruct o as [th2|] eqn:MSB; [|discriminate] end.
    destruct (match_chunks (s_mf ss) (su_mbind su) th2 []) as [[th3c tb3]|] eqn:MC; [|discriminate].
    destruct (match_arrs (s_pf ss) (s_mf ss) (su_mbind su) th3c []) as [[th3 tl3]|] eqn:MA; [|discriminate].
    match type of SM with match ?o with _ => _ end = _ => destruct o as [th4|] eqn:MST; [|discriminate] end.
    match type of SM with match ?o with _ => _ end = _ => destruct o as [[th5 tb5]|] eqn:BB; [| exfalso; injection SM; lia] end.
    destruct (all_bbound tb5 (su_nb su) 1) eqn:ABB; [|discriminate]. cbn [negb] in SM.
    destruct (lforallb (fun f => req_ok C (s_pf ss) (cranges (s_pf ss) (s_mf ss)) (s_mf ss) (sxm th5 tb5 tl3 f)) (su_req su)) eqn:REQ; [|discriminate]. cbn [negb] in SM.
    rewrite lforallb_forallb in REQ.
    match type of SM with (if negb ?c then _ else _) = _ => destruct c eqn:KEYS; [|discriminate] end. cbn [negb] in SM.
    injection SM; intros <- <- <-. apply andb_prop in KEYS as [KEYS LALL]. apply andb_prop in KEYS as [KEYS LKEYS]. apply andb_prop in KEYS as [KEYS BKEYS].
    (* [comment removed for export] *)
    destruct (match_regs_ok _ _ _ _ MR) as [S00 RB0]. destruct (match_globals_ok _ _ _ _ MG) as [S01 GB].
    assert (RB : Forall (fun ri => sub_get th1 (snd ri) = Some (rd_expr ss (fst ri))) (su_rbind su)).
    { eapply Forall_impl; [|exact RB0]. intros ri Hri. apply S01. exact Hri. }
    assert (S12 : thsub th1 th2 /\ match su_sb su, c_acc C with Some i, Some A => sub_get th2 i = Some (ac_sb A) | Some _, None => False | None, _ => True end).
    { destruct (su_sb su) as [isb|]; [destruct (c_acc C) as [A|]; [|discriminate]|].
      - destruct (bind_ok _ _ _ _ MSB) as [G S]. split; assumption.
      - injection MSB; intros <-. split; [apply thsub_refl| exact I]. }
    destruct S12 as [S12 SB].
    destruct (match_chunks_ok _ _ _ _ _ _ MC) as (S23c & T03 & R3). destruct (match_arrs_ok _ _ _ _ _ _ _ MA) as (S3A & TL3 & RAR).
    assert (S23 : thsub th2 th3) by (eapply thsub_trans; [exact S23c| exact S3A]).
    assert (S34 : thsub th3 th4 /\ match su_stk su with Some (ilo, ihi) => exists lo h, sub_get th4 ihi = Some h /\ sub_get th4 ilo = Some lo /\ stk_just (s_mf ss) (s_mf ss) lo h | None => True end).
    { destruct (su_stk su) as [[ilo ihi]|].
      - destruct (sub_get th3 ihi) as [h|] eqn:GH; [|discriminate]. destruct (match_stk_ok _ _ _ _ _ _ MST) as (S & lo & G & IN).
        split; [exact S|]. exists lo, h. split; [apply S; exact GH|]. split; [exact G| exact IN].
      - injection MST; intros <-. split; [apply thsub_refl| exact I]. }
    destruct S34 as [S34 STK].
    destruct (bind_bytes_ok _ _ _ _ _ _ _ BB) as (S45 & T35 & PREOK & BBF).
    apply andb_prop in PREOK as [ABD PRE]. rewrite lforallb_forallb in PRE.
    set (th := th5) in *. set (tb := tb5) in *. set (tl := tl3) in *.
    (* [comment removed for export] *)
    set (ps := pvals E th (su_np su)). set (bss := bvals E tb (su_nb su)). set (lss := lvals E tl (su_nl su)).
    set (E' := ENV ps [] bss OPS lss [] LAWS PROPS [] lx_nohp lx_nocw [] lx_nomodel [] []).
    assert (ELr : forall l0, elaw E l0 = elaw E' l0) by (intros l0; unfold elaw; rewrite ELW; reflexivity).
    assert (KEY : forall i e, sub_get th i = Some e -> (Pos.to_nat i <= (su_np su))%nat).
    { intros i e G. pose proof (keys_lt_sound _ _ KEYS i e G) as X. unfold su_npP in X. lia. }
    assert (BKEY : forall i kk, bsub_get tb i = Some kk -> (Pos.to_nat i <= (su_nb su))%nat).
    { intros i kk G. pose proof (bkeys_lt_sound _ _ BKEYS i kk G) as X. unfold su_nbP in X. lia. }
    assert (LKEY : forall j l, lsub_get tl j = Some l -> (Pos.to_nat j <= (su_nl su))%nat).
    { intros j l G. assert (X : Pos.ltb j (su_nlP su) = true).
      { rewrite forallb_forall in LKEYS. revert G. clear - LKEYS. induction tl as [|[j' l'] tl IH]; cbn; intros G; [discriminate|].
        destruct (Pos.eqb_spec j j') as [<-|]; [exact (LKEYS (j, l') (or_introl eq_refl))| apply IH; [intros p Hp; apply LKEYS; right; exact Hp| exact G]]. }
      apply Pos.ltb_lt in X. unfold su_nlP in X. lia. }
    assert (TLh : forall j l, lsub_get tl j = Some l -> ldenw E l = el E' j).
    { intros j l G. unfold E', lss, el. cbn [ell]. rewrite (lvals_get E tl (su_nl su) j (LKEY j l G)). unfold tlv. rewrite G. reflexivity. }
    assert (LBND : forall j, (j < su_nlP su)%positive -> lsub_get tl j <> None).
    { intros j Hj. apply (lall_bound_ok tl (su_nl su) 1); [exact LALL| lia| unfold su_nlP in Hj; lia]. }
    assert (TH : forall i e, sub_get th i = Some e -> zden E e = ez E' i).
    { intros i e G. unfold E', ps, ez. cbn [ezl]. rewrite (pvals_get E th (su_np su) i (KEY i e G)). unfold thv. rewrite G. reflexivity. }
    assert (TB : forall kb kk, bsub_get tb kb = Some kk -> bval_den E kk = eb E' kb).
    { intros kb kk G. unfold E', bss. unfold eb at 1. cbn [ebl]. rewrite (bvals_get E tb (su_nb su) kb (BKEY kb kk G)). unfold bvalk. rewrite G. reflexivity. }
    assert (TBv : forall kb kk, bsub_get tb kb = Some (BVar kk) -> eb E kk = eb E' kb).
    { intros kb kk G. exact (TB kb (BVar kk) G). }
    assert (BND : forall i, (i < su_npP su)%positive -> sub_get th i <> None).
    { intros i Hi. apply (all_bound_ok th (su_np su) 1); [exact ABD| lia| unfold su_npP in Hi; lia]. }
    assert (BBND : forall kb, (kb < su_nbP su)%positive -> bsub_get tb kb <> None).
    { intros kb Hk. apply (all_bbound_ok tb (su_nb su) 1); [exact ABB| lia| unfold su_nbP in Hk; lia]. }
    (* [comment removed for export] *)
    pose proof SWF as SWF0. unfold su_wf in SWF.
    apply andb_prop in SWF as [SWF WPOST]. apply andb_prop in SWF as [SWF WMPOST]. apply andb_prop in SWF as [SWF WCLOB].
    apply andb_prop in SWF as [SWF WW]. apply andb_prop in SWF as [SWF WPRE]. apply andb_prop in SWF as [SWF WREQ].
    apply andb_prop in SWF as [SWF WBB]. apply andb_prop in SWF as [SWF WSTK]. apply andb_prop in SWF as [SWF WMB].
    apply andb_prop in SWF as [SWF WSB]. apply andb_prop in SWF as [WRB WGB].
    (* [comment removed for export] *)
    set (R := map (rden E) (s_rs ss)).
    assert (LR : length R = 31%nat) by (unfold R; rewrite map_length; exact L31).
    pose proof (zforall_apply _ _ ps V (pvals_length E th (su_np su))) as V1. cbn beta in V1.
    pose proof (bforall_apply _ _ bss V1 (bvals_length E tb (su_nb su))) as V2b. cbn beta in V2b. clear V1.
    pose proof (lforall_apply _ _ lss V2b (lvals_length E tl (su_nl su))) as V2. cbn beta in V2. clear V2b.
    pose proof (wforall_apply _ _ R (V2 F fc m) LR) as V3. cbn beta in V3. clear V2. fold E' in V3.
    assert (ACCP : if su_acc su then cs_ok AL CS /\ al_wf AL else forall x, CS x).
    { unfold cfg_ok in CFG. cbn [g_L g_CS] in CFG. unfold acc_mode in ACC.
      destruct (su_acc su); destruct (c_acc C) as [A|]; try discriminate; [|exact CFG].
      destruct CFG as (C1 & C2 & _). split; assumption. }
    assert (SBP : match su_sb su with Some i => ez E' i = al_sb AL | None => True end).
    { destruct (su_sb su) as [isb|]; [|exact I]. destruct (c_acc C) as [A|] eqn:HCA; [|destruct SB].
      rewrite <- (TH isb (ac_sb A)) by (apply S45, S34, S23; exact SB).
      unfold cfg_ok in CFG. rewrite HCA in CFG. cbn [g_L g_CS] in CFG. destruct CFG as (_ & _ & S1 & _). rewrite <- zdenp_ok. exact S1. }
    pose proof (V3 ACCP SBP MI) as V4g. clear V3.
    assert (GBP : forall i n, In (i, n) (su_gbind su) -> ez E' i = nth n GS 0).
    { intros i n Hin. rewrite List.Forall_forall in GB. destruct (GB _ Hin) as (g & NG & Gi). cbn [fst snd] in NG, Gi.
      rewrite <- (TH i g) by (apply S45, S34, S23, S12; exact Gi). exact (Forall2_nth_error _ _ _ _ _ GV NG). }
    pose proof (gb_tele_elim _ _ _ V4g GBP) as V4. clear V4g.
    assert (RBP : forall r i, In (r, i) (su_rbind su) -> rgetZ R r = Z_to_bv 64 (ez E' i)).
    { intros r i Hin. rewrite List.Forall_forall in RB. pose proof (RB _ Hin) as G. cbn [fst snd] in G.
      rewrite forallb_forall in WRB. specialize (WRB _ Hin). cbn [fst snd] in WRB.
      apply andb_prop in WRB as [WRB R31]. apply andb_prop in WRB as [_ R1]. apply Z.leb_le in R1. apply Z.leb_le in R31.
      rewrite <- (TH i (rd_expr ss r)) by (apply S45, S34, S23, S12; exact G).
      destruct r as [|p|p]; try lia. unfold rgetZ. rewrite pget_nth. unfold R.
      rewrite (nth_map' (rden E) (s_rs ss) _ (RZ (ELit 0))) by lia.
      unfold rd_expr, rd_reg. cbn [Z.eqb]. rewrite lget_nth. replace (Z.to_nat (Z.pos p - 1)) with (Pos.to_nat p - 1)%nat by lia.
      symmetry. apply expr_of_reg_den. }
    pose proof (rb_tele_elim _ _ _ _ V4 RBP) as V5. clear V4.
    assert (STKP : match su_stk su with Some (ilo, ihi) => stk segs m (ez E' ilo) (ez E' ihi) | None => True end).
    { destruct (su_stk su) as [[ilo ihi]|]; [|exact I]. destruct STK as (lo & h & Gh & Glo & IN).
      rewrite <- (TH ilo lo), <- (TH ihi h) by (apply S45; assumption).
      exact (stk_just_sound segs AL CS E m _ _ _ _ HM HM IN). }
    specialize (V5 STKP).
    assert (MFP : Forall (mfact_ok segs AL CS E' m) (su_mbind su ++ bb_facts (su_bbind su) ++ su_req su)).
    { apply Forall_app. split; [|apply Forall_app; split].
      - assert (R3' : Forall (fun f => match f with MArr _ _ _ _ _ => True | _ => mfact_ok segs AL CS E' m f end) (su_mbind su)).
        { apply (R3 segs AL CS m E E' th tb); [eapply thsub_trans; [exact S3A|]; eapply thsub_trans; [exact S34| exact S45]| exact T35| exact TH| exact TB| |exact HM].
          apply List.Forall_forall. intros f Hf. rewrite forallb_forall in WMB. specialize (WMB f Hf).
          destruct f; try exact I. cbn -[eloc forallb cloc] in WMB. apply andb_prop in WMB as [WA _]. exact (eloc_enoU _ _ WA). }
        assert (RA' : Forall (fun f => match f with MArr _ _ _ _ _ => mfact_ok segs AL CS E' m f | _ => True end) (su_mbind su)).
        { apply (RAR segs AL CS m E E' th tl); [eapply thsub_trans; [exact S34| exact S45]| intros i x Hx; exact Hx| exact TH| exact TLh| |exact HM| exact HP].
          apply List.Forall_forall. intros f Hf. rewrite forallb_forall in WMB. specialize (WMB f Hf).
          destruct f as [| | | | | |fa fw [fj|] fn fwr| | | | | | | | | | |hj ho hn hxs hok]; try exact I; [|discriminate]. cbn -[eloc Pos.ltb orb N.eqb] in WMB.
          repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end.
          match goal with G : eloc _ fa = true |- _ => exact (eloc_enoU _ _ G) end. }
        rewrite List.Forall_forall in R3', RA'. apply List.Forall_forall. intros f Hf. specialize (R3' f Hf). specialize (RA' f Hf). destruct f; assumption.
      - unfold bb_facts. apply List.Forall_forall. intros f Hf. apply in_map_iff in Hf as ([[ia il] kb] & <- & Hin).
        rewrite List.Forall_forall in BBF. destruct (BBF _ Hin) as (a & n & kc & INC & Ga & Gn & Gk).
        apply mby_facts_In in INC. rewrite List.Forall_forall in HM. pose proof (HM _ INC) as X. cbn in X. rewrite !zdenp_ok in X.
        cbn [mfact_ok zdenp]. rewrite <- (TH ia a Ga), <- (TH il n Gn), <- (TB kb (BVar kc) Gk). exact X.
      - assert (HACC0 : forall A, c_acc C = Some A -> ac_got A = al_got AL /\ ac_gsb A = al_gsb AL /\ cs_ok AL CS).
        { intros A HCA. unfold cfg_ok in CFG. rewrite HCA in CFG. cbn [g_L g_CS] in CFG. destruct CFG as (C1 & _ & _ & _ & _ & G1 & G2). split; [exact G1| split; [exact G2| exact C1]]. }
        assert (HSB0 : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb AL).
        { intros A HCA. unfold cfg_ok in CFG. rewrite HCA in CFG. cbn [g_L g_CS] in CFG. destruct CFG as (_ & _ & S1 & _). exact S1. }
        apply List.Forall_forall. intros f Hf. rewrite forallb_forall in REQ. pose proof (REQ f Hf) as X.
        apply (req_ok_sound segs AL CS E C m _ _ _ HP HACC0 HSB0 CR HM) in X. apply (sxm_ok E E' th tb tl TH TBv TLh ELr) in X; [exact X|].
        rewrite forallb_forall in WREQ. rewrite forallb_forall in PBOreq. eapply bridge_m; [exact BND| exact (PBOreq f Hf)| exact LBND| exact (WREQ f Hf)]. }
    pose proof (mf_tele_elim _ E' m _ _ V5 MFP) as V6. clear V5.
    assert (PFP : Forall (pfact_ok CS E') (su_pre su)).
    { apply List.Forall_forall. intros f Hf. rewrite forallb_forall in PRE. pose proof (PRE f Hf) as X.
      assert (EPR' : epr E = epr E') by (rewrite EPR; reflexivity).
      apply (pf_decide_sound CS E _ _ _ _ HP CR HO) in X. apply (sxp_ok E E' th TH EPR') in X; [exact X|].
      rewrite forallb_forall in WPRE. eapply bridge_p; [exact BND| exact (WPRE f Hf)]. }
    pose proof (pf_tele_elim _ E' _ _ V6 PFP) as V7. clear V6.
    (* [comment removed for export] *)
    assert (OQF : forall k, In k (su_oreq su) -> exists ok sh, In (MOpq k ok sh) (s_mf ss)) by (intros k Hk; exact (opq_required_In _ _ _ _ OQR Hk)).
    assert (OQP : forall k, In k (su_oreq su) -> nth k OPS (fun _ => True) m).
    { intros k Hk. destruct (OQF k Hk) as (ok & sh & Hin). rewrite List.Forall_forall in HM. pose proof (HM _ Hin) as X.
      cbn [mfact_ok] in X. destruct X as [X _]. unfold eo in X. rewrite EO in X. exact X. }
    pose proof (oq_tele_elim _ _ _ _ V7 OQP) as EV. clear V7.
    (* [comment removed for export] *)
    assert (MSE : ms_den segs (GL AL CS F fc m0 me) E ss m = MS (rdw R) F (Z_to_bv 64 (su_pc su)) fc None m (seg_rom segs)).
    { unfold ms_den. cbn [g_F g_fc]. rewrite HPC, regs_den_rdw. reflexivity. }
    (* [comment removed for export] *)
    enough (COMMON : evtA segs AL CS (fun ms' => exists rs rls m', length rs = su_nr su /\ length rls = su_nrl su /\ length (s_rs (sum_post C su ss th tb tl ra)) = 31%nat
               /\ ms' = ms_den segs (GL AL CS F fc m0 me) (env_call E (s_nx ss) rs (s_nl ss) rls) (sum_post C su ss th tb tl ra) m'
               /\ (su_law su = None -> INV segs (GL AL CS F fc m0 me) (env_call E (s_nx ss) rs (s_nl ss) rls) (sum_post C su ss th tb tl ra) m')
               /\ (forall l, su_law su = Some l ->
                     Nat.ltb (s_ref ss) (s_nm ss) && Nat.ltb 0 (s_nm ss) && forallb (mrefs_lt (s_nm ss)) (s_mf ss) = true ->
                     INV segs (GL AL CS F fc m0 me) (env_law E (s_nx ss) rs (s_nl ss) rls (s_nm ss) m m') (sum_post C su ss th tb tl ra) m'))
               (ms_den segs (GL AL CS F fc m0 me) E ss m)).
    { destruct (su_law su) as [l|] eqn:HLAW.
      - destruct (Nat.ltb (s_ref ss) (s_nm ss) && Nat.ltb 0 (s_nm ss) && forallb (mrefs_lt (s_nm ss)) (s_mf ss)) eqn:NMC; [|exact I]. cbv beta iota.
        eapply evtA_mono; [exact COMMON|]. cbv beta. intros ms1 (rs & rls & m' & Lrs & Lrls & L31' & EQ & _ & HINV).
        exists rs, rls, m, m', m'. split; [exact Lrs|]. split; [exact Lrls|]. split; [exact L31'|]. split; [unfold sum_post; rewrite HLAW; reflexivity|].
        split; [rewrite EQ; unfold env_law; rewrite !ms_den_setm; reflexivity| exact (HINV l eq_refl eq_refl)].
      - eapply evtA_mono; [exact COMMON|]. cbv beta. intros ms1 (rs & rls & m' & Lrs & Lrls & L31' & EQ & HINV & _).
        exists rs, rls, m'. split; [exact Lrs|]. split; [exact Lrls|]. split; [exact L31'|]. split; [exact EQ| exact (HINV eq_refl)]. }
    rewrite MSE. eapply evtA_mono; [exact EV|]. cbv beta. intros ms' POST.
    unfold sum_postP in POST. apply zexists_elim in POST as (rs & Lrs & POST). apply lexists_elim in POST as (rls & Lrls & m' & -> & POSTF).
    apply mf_conj_elim in POSTF as [QMF POSTF]. apply pf_conj_elim in POSTF as [QPF POSTF]. apply oq_conj_elim in POSTF as [QOQ QFR].
    (* [comment removed for export] *)
    set (th' := res_subst (su_npP su) (su_nr su) (s_nx ss) th).
    set (tl' := lres_subst (su_nlP su) (su_nrl su) (s_nl ss) tl).
    set (Ef := env_call E (s_nx ss) rs (s_nl ss) rls). set (Es := ENV (ps ++ rs) [] bss OPS (lss ++ rls) [] LAWS PROPS [] lx_nohp lx_nocw [] lx_nomodel [] []) in *.
    assert (SRS : s_rs (sum_post C su ss th tb tl ra) = set_regs (s_rs ss) (map (fun rj => (fst rj, sxe th' (EZv (snd rj)))) (su_clob su)))
      by (unfold sum_post; destruct (su_law su); reflexivity).
    assert (SPC : s_pc (sum_post C su ss th tb tl ra) = ra) by (unfold sum_post; destruct (su_law su); reflexivity).
    assert (ELs : forall l0, elaw Ef l0 = elaw Es l0) by (intros l0; unfold Ef, env_call; rewrite elaw_setls, elaw_setzs; unfold elaw; rewrite ELW; reflexivity).
    assert (EPs : epr Ef = epr Es) by (unfold Ef, env_call; rewrite epr_setls, epr_setzs; rewrite EPR; reflexivity).
    assert (ZEf : forall e, zden Ef e = zden (setzs E (s_nx ss) rs) e) by (intros e; unfold Ef, env_call; apply zden_setls).
    (* [comment removed for export] *)
    pose proof WF as WF0. unfold ss_wf in WF.
    apply andb_prop in WF as [WF WSBc]. apply andb_prop in WF as [WF WWc]. apply andb_prop in WF as [WF WPFc].
    apply andb_prop in WF as [WF WMFc]. apply andb_prop in WF as [WPCc WRc].
    assert (WFP : thP (fun e => evars_lt (s_nx ss) e = true) th).
    { assert (T0 : thP (fun e => evars_lt (s_nx ss) e = true) []) by (intros i e G; discriminate).
      assert (RDX : forall r, evars_lt (s_nx ss) (rd_expr ss r) = true).
      { intros r. unfold rd_expr, rd_reg. destruct (Z.eqb r 0); [reflexivity|]. rewrite lget_nth.
        destruct (Nat.lt_ge_cases (Z.to_nat (r - 1)) (length (s_rs ss))) as [LT|GE].
        - rewrite forallb_forall in WRc. specialize (WRc _ (nth_In _ (RZ (ELit 0)) LT)). destruct (nth _ _ _) as [i|e]; cbn in WRc |- *; [reflexivity| exact WRc].
        - rewrite nth_overflow by lia. reflexivity. }
      assert (T0' : thP (fun e => evars_lt (s_nx ss) e = true) th0) by (eapply match_regs_P; [exact T0| exact RDX| exact MR]).
      assert (T1 : thP (fun e => evars_lt (s_nx ss) e = true) th1).
      { eapply match_globals_P; [exact T0'| | exact MG]. intros g Hg. rewrite forallb_forall in GWF. apply GWF. exact Hg. }
      assert (T2 : thP (fun e => evars_lt (s_nx ss) e = true) th2).
      { destruct (su_sb su) as [isb|]; [destruct (c_acc C) as [A|]; [|destruct SB]|].
        - eapply bind_P; [exact T1| exact WSBc| exact MSB].
        - injection MSB; intros <-. exact T1. }
      assert (T3c : thP (fun e => evars_lt (s_nx ss) e = true) th3c).
      { eapply match_chunks_P; [intros; reflexivity| exact T2| | exact MC]. intros a cs c e Hin Hc He.
        rewrite forallb_forall in WMFc. specialize (WMFc _ Hin). cbn -[evars_lt forallb cvars_lt] in WMFc. apply andb_prop in WMFc as [_ Wcs].
        rewrite forallb_forall in Wcs. specialize (Wcs _ Hc).
        destruct c as [i|w e'|w kk|w i|c o l|wr er]; cbn in He; try discriminate.
        - injection He; intros <-. reflexivity.
        - injection He; intros <-. exact Wcs.
        - destruct w as [|q]; [discriminate|]. destruct q as [q|q|]; try discriminate; destruct q as [q|q|]; try discriminate;
            [destruct q; try discriminate|]; injection He; intros <-; reflexivity. }
      assert (T3 : thP (fun e => evars_lt (s_nx ss) e = true) th3).
      { eapply match_arrs_P; [exact T3c| | exact MA]. intros a w l n wr Hin.
        rewrite forallb_forall in WMFc. specialize (WMFc _ Hin). cbn -[evars_lt lvars_lt] in WMFc. repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end. assumption. }
      assert (T4 : thP (fun e => evars_lt (s_nx ss) e = true) th4).
      { destruct (su_stk su) as [[ilo ihi]|].
        - destruct (sub_get th3 ihi) as [h|]; [|discriminate]. eapply match_stk_P; [exact T3| | exact MST].
          intros lo hi Hin. rewrite forallb_forall in WMFc. specialize (WMFc _ Hin). cbn -[evars_lt] in WMFc. apply andb_prop in WMFc as [Wlo _]. exact Wlo.
        - injection MST; intros <-. exact T3. }
      eapply bind_bytes_P; [exact T4| | exact BB]. intros a n kc Hin. apply mby_facts_In in Hin.
      rewrite forallb_forall in WMFc. specialize (WMFc _ Hin). cbn -[evars_lt] in WMFc. apply andb_prop in WMFc as [Wa Wn]. split; assumption. }
    (* [comment removed for export] *)
    assert (THs : forall i e, sub_get th' i = Some e -> zden Ef e = ez Es i).
    { intros i e G. rewrite ZEf. unfold th' in G. rewrite res_subst_get in G.
      match type of G with (if ?c then _ else _) = _ => destruct c eqn:RNG end.
      - apply andb_prop in RNG as [R1 R2]. apply Pos.leb_le in R1. apply Pos.ltb_lt in R2. unfold su_npP in R1, R2. fold (su_np su) in R1, R2.
        injection G; intros <-. rewrite eatom_den. cbn [zden]. rewrite ez_setzs_at by (rewrite Lrs; unfold su_npP in *; lia).
        unfold Es, ez. cbn [ezl]. unfold ps. rewrite pget_app_r by (rewrite pvals_length; unfold su_npP in *; lia). rewrite pvals_length. f_equal. unfold su_npP in *. lia.
      - pose proof (KEY i e G) as Ki. rewrite zden_setzs by (apply (WFP i e G)). rewrite (TH i e G).
        unfold E', Es, ez, ps. cbn [ezl]. rewrite pget_app_l by (rewrite pvals_length; lia). reflexivity. }
    assert (TBs : forall kb kk, bsub_get tb kb = Some (BVar kk) -> eb Ef kk = eb Es kb).
    { intros kb kk G. unfold Ef, env_call. rewrite eb_setls, eb_setzs. pose proof (TB kb (BVar kk) G) as X. cbn [bval_den] in X. rewrite X. reflexivity. }
    (* [comment removed for export] *)
    assert (TLQ : forall j l, lsub_get tl j = Some l -> lvars_lt (s_nx ss) l = true /\ llvars_lt (s_nl ss) l = true).
    { refine (match_arrs_LQ (fun l => lvars_lt (s_nx ss) l = true /\ llvars_lt (s_nl ss) l = true) _ _ _ _ _ _ _ _ _ MA); [intros j l G; discriminate|].
      intros a w l n wr Hin. rewrite forallb_forall in WMFc. rewrite forallb_forall in MLF. pose proof (WMFc _ Hin) as X. pose proof (MLF _ Hin) as Y.
      cbn -[evars_lt lvars_lt] in X. cbn in Y. repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end. split; assumption. }
    assert (TLs : forall j l, lsub_get tl' j = Some l -> ldenw Ef l = el Es j).
    { intros j l G. unfold tl' in G. rewrite lres_subst_get in G.
      match type of G with (if ?c then _ else _) = _ => destruct c eqn:RNG end.
      - apply andb_prop in RNG as [R1 R2]. apply Pos.leb_le in R1. apply Pos.ltb_lt in R2. unfold su_nlP in R1, R2.
        injection G; intros <-. cbn [ldenw]. unfold Ef, env_call. rewrite el_setls_at by (rewrite Lrls; unfold su_nrl, su_nlP in *; lia).
        unfold Es, el. cbn [ell]. unfold lss. rewrite pget_app_r by (rewrite lvals_length; unfold su_nlP in *; lia). rewrite lvals_length. f_equal. unfold su_nlP in *. lia.
      - pose proof (LKEY j l G) as Kj. destruct (TLQ j l G) as [Q1 Q2]. unfold Ef, env_call. rewrite ldenw_setls by exact Q2. rewrite ldenw_setzs by exact Q1.
        rewrite (TLh j l G). unfold E', Es, el. cbn [ell]. rewrite pget_app_l by (unfold lss; rewrite lvals_length; lia). reflexivity. }
    assert (LBNDs : forall j, (j < su_nlaP su)%positive -> lsub_get tl' j <> None).
    { intros j Hj. unfold tl'. rewrite lres_subst_get.
      match goal with |- (if ?c then _ else _) <> _ => destruct c eqn:RNG end; [discriminate|].
      apply LBND. unfold su_nlaP, su_nrl in *. unfold su_nlP in *.
      destruct (Pos.leb_spec (Pos.of_nat (S (su_nl su))) j); destruct (Pos.ltb_spec j (Pos.of_nat (Pos.to_nat (Pos.of_nat (S (su_nl su))) + (su_nla su - su_nl su)))); cbn in RNG; try discriminate; lia. }
    assert (S5s : thsub th th').
    { intros i e G. unfold th'. rewrite res_subst_get. pose proof (KEY i e G) as Ki.
      match goal with |- (if ?c then _ else _) = _ => destruct c eqn:RNG end; [|exact G].
      apply andb_prop in RNG as [R1 _]. apply Pos.leb_le in R1. unfold su_npP in R1. lia. }
    assert (BNDs : forall i, (i < su_nallP su)%positive -> sub_get th' i <> None).
    { intros i Hi. unfold th'. rewrite res_subst_get.
      match goal with |- (if ?c then _ else _) <> _ => destruct c eqn:RNG end; [discriminate|].
      apply BND. unfold su_nallP in Hi. unfold su_npP.
      destruct (Pos.leb_spec (su_npP su) i); destruct (Pos.ltb_spec i (Pos.of_nat (Pos.to_nat (su_npP su) + (su_nr su)))); cbn in RNG; try discriminate;
        unfold su_npP in *; lia. }
    exists rs, rls, m'. split; [exact Lrs|]. split; [exact Lrls|].
    split. { rewrite SRS, set_regs_length. exact L31. }
    (* [comment removed for export] *)
    assert (RSEQ : map (rden Ef) (s_rs (sum_post C su ss th tb tl ra)) = rclob R (su_clob su) Es).
    { rewrite SRS.
      assert (BASE : map (rden Ef) (s_rs ss) = R).
      { unfold R. apply map_ext_in. intros r Hr. unfold Ef, env_call. rewrite rden_setls. apply rden_setzs. rewrite forallb_forall in WRc. apply WRc. exact Hr. }
      assert (CL : forall rj, In rj (su_clob su) -> 1 <= fst rj <= 31 /\ (su_npP su <= snd rj)%positive /\ (snd rj < su_nallP su)%positive).
      { intros rj Hin. rewrite forallb_forall in WCLOB. specialize (WCLOB rj Hin).
        repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end.
        repeat match goal with
          | G : Pos.leb _ _ = true |- _ => apply Pos.leb_le in G
          | G : Pos.ltb _ _ = true |- _ => apply Pos.ltb_lt in G
          | G : Z.leb _ _ = true |- _ => apply Z.leb_le in G
          | G : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in G
          | G : negb (Z.eqb _ _) = true |- _ => apply Bool.negb_true_iff in G; apply Z.eqb_neq in G
          end; lia. }
      assert (GEN : forall cl l R0, (forall rj, In rj cl -> 1 <= fst rj <= 31 /\ (su_npP su <= snd rj)%positive /\ (snd rj < su_nallP su)%positive) ->
                length l = 31%nat -> map (rden Ef) l = R0 ->
                map (rden Ef) (set_regs l (map (fun rj => (fst rj, sxe th' (EZv (snd rj)))) cl)) = rclob R0 cl Es).
      { induction cl as [|[r j] cl IH]; intros l R0 CL0 Hl BASE0; cbn [set_regs map rclob fst snd]; [exact BASE0|].
        apply IH.
        - intros rj Hin. apply CL0. right. exact Hin.
        - rewrite lset_length. exact Hl.
        - rewrite map_lset, BASE0. destruct (CL0 (r, j) (or_introl eq_refl)) as (Hr & Hj1 & Hj2). cbn [fst snd] in Hr, Hj1, Hj2.
          rewrite mkreg_den. rewrite (sxe_den Ef Es th' THs); [| | reflexivity].
          2:{ cbn. destruct (sub_get th' j) eqn:G; [reflexivity|]. exfalso. exact (BNDs j Hj2 G). }
          cbn [zden]. unfold rsetZ. destruct r as [|p|p]; try lia. rewrite pset_lset by (rewrite <- BASE0, map_length; lia).
          replace (Z.to_nat (Z.pos p - 1)) with (Pos.to_nat p - 1)%nat by lia. reflexivity. }
      exact (GEN (su_clob su) (s_rs ss) R CL L31 BASE). }
    split.
    { (* [comment removed for export] *)
      unfold ms_den. cbn [g_F g_fc]. f_equal.
      - rewrite regs_den_rdw. fold Ef. rewrite RSEQ. reflexivity.
      - (* [comment removed for export] *) rewrite SPC.
        assert (R1 : rgetZ R 1 = rden E (rd_reg ss 1)).
        { unfold rgetZ, R. rewrite pget_nth. rewrite (nth_map' (rden E) (s_rs ss) _ (RZ (ELit 0))) by lia.
          unfold rd_reg. cbn [Z.eqb]. rewrite lget_nth. reflexivity. }
        rewrite R1. destruct (rd_reg ss 1) as [j|e] eqn:RR1.
        + injection RA; intros <-. cbn [pc_den rden]. unfold Ef, env_call. rewrite ew_setls, ew_setzs. reflexivity.
        + destruct (is_lit e) as [z|] eqn:LZ; [|discriminate]. injection RA; intros <-. cbn [pc_den rden].
          apply is_lit_den with (E := E) in LZ. rewrite zdenp_ok, LZ. apply ret_pc_lit. }
    (* [comment removed for export] *)
    set (W := sxw th (su_W su)).
    assert (WWB : forallb (fun lh => ebound th (fst lh) && enoU (fst lh) && ebound th (snd lh) && enoU (snd lh)) (su_W su) = true).
    { apply forallb_forall. intros [l h] Hin. rewrite forallb_forall in WW. specialize (WW _ Hin). cbn [fst snd] in WW |- *.
      apply andb_prop in WW as [Wl Wh].
      rewrite (bridge_bound th _ l BND Wl), (bridge_bound th _ h BND Wh), (eloc_enoU _ l Wl), (eloc_enoU _ h Wh). reflexivity. }
    assert (EE : forall e, eloc (su_npP su) e = true -> zden E' e = zden Es e).
    { intros e He. unfold E', Es. symmetry. apply zden_app_env. unfold ps. rewrite pvals_length. exact He. }
    assert (WE : wden E W = wden Es (su_W su)).
    { unfold W. rewrite (sxw_den E E' th TH _ WWB). apply wden_ext. apply List.Forall_forall. intros [l h] Hin.
      rewrite forallb_forall in WW. specialize (WW _ Hin). cbn [fst snd] in WW |- *. apply andb_prop in WW as [Wl Wh].
      rewrite !zdenp_ok. rewrite (EE l Wl), (EE h Wh). split; reflexivity. }
    assert (HACC : forall A, c_acc C = Some A -> ac_got A = al_got AL /\ ac_gsb A = al_gsb AL /\ cs_ok AL CS).
    { intros A HCA. unfold cfg_ok in CFG. rewrite HCA in CFG. cbn [g_L g_CS] in CFG. destruct CFG as (C1 & _ & _ & _ & _ & G1 & G2). split; [exact G1| split; [exact G2| exact C1]]. }
    assert (DLE : forall l h, dec_le00 (s_pf ss) l h = true -> zden E l <= zden E h) by (intros l h; apply (dec_le00_sound CS E); exact HP).
    assert (THf : forall i e, sub_get th i = Some e -> zden Ef e = ez Es i) by (intros i e G0; apply THs; apply S5s; exact G0).
    assert (WEf : wden Ef W = wden Es (su_W su)) by (unfold W; exact (sxw_den _ Es th THf _ WWB)).
    assert (HSB : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb AL).
    { intros A HCA. unfold cfg_ok in CFG. rewrite HCA in CFG. cbn [g_L g_CS] in CFG. destruct CFG as (_ & _ & S1 & _). exact S1. }
    split.
    { (* [comment removed for export] *)
    intros HLAW. unfold sum_frame in QFR. rewrite HLAW in QFR. destruct QFR as (QMU & QWM & QMI).
    assert (MU2 : munch (wden E W) m m') by (rewrite WE; exact QMU).
    unfold INV. unfold sum_post. rewrite HLAW. cbn [s_mf s_pf s_W s_same]. fold th'. fold tl'. fold W. cbn [g_L g_CS g_m0]. fold Ef.
    match goal with |- context [refm ?E1 ?S1] =>
      replace (refm E1 S1) with (refm E ss) by (unfold refm, em; cbn [s_ref]; unfold Ef, env_call; rewrite eml_setls, eml_setzs_gen; reflexivity) end.
    split; [|split; [|split; [|split; [eapply wmono_trans; [exact WM| exact QWM]| split; [exact QMI| apply same_gone]]]]].
    - (* [comment removed for export] *) apply install_post_Forall.
      + apply Forall_app. split.
        * apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin Hsv].
          rewrite forallb_forall in WMFc. rewrite forallb_forall in MLF.
          unfold Ef, env_call. apply (proj2 (mfact_ok_setls segs (GL AL CS F fc m0 me) rls _ (s_nl ss) m' f (MLF _ Hin))).
          apply (mfact_ok_setzs segs (GL AL CS F fc m0 me) E rs (s_nx ss) m' f (WMFc _ Hin)). cbn [g_L g_CS].
          pose proof HM as HMF. rewrite List.Forall_forall in HM.
          refine (mf_survives_call_sound segs AL CS E C m m' (s_pf ss) W HP HACC HSB _ CR MU2 QWM QMI HPFE _ _ (s_mf ss) f HMF _ _ (HM _ Hin) Hsv).
          { intros W1. eapply w_all_client_sound; [exact HP| exact CR| exact W1]. }
          { intros W2. eapply all_nonempty_sound; [exact HP| exact W2]. }
        * (* [comment removed for export] *)
          rewrite OQR. apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin _].
          assert (HinM : In f (s_mf ss) /\ exists k ok sh, f = MOpq k ok sh /\ In k (su_oreq su)).
          { clear - OQR Hin. revert oql OQR Hin. unfold opq_required. induction (su_oreq su) as [|k0 ks IH]; intros oql OQR Hin.
            - cbn in OQR. injection OQR; intros <-. destruct Hin.
            - cbn [fold_right] in OQR.
              match type of OQR with (match ?acc with _ => _ end) = _ => destruct acc as [l0|] eqn:R0; [|discriminate] end.
              destruct (opq_find (s_mf ss) k0) as [g|] eqn:Fg; [|discriminate]. injection OQR; intros <-.
              destruct Hin as [<-|Hin].
              + destruct (opq_find_In _ _ _ Fg) as (ok & sh & -> & Hg). split; [exact Hg| exists k0, ok, sh; split; [reflexivity| left; reflexivity]].
              + destruct (IH l0 eq_refl Hin) as [A (k & ok & sh & B & Ck)]. split; [exact A| exists k, ok, sh; split; [exact B| right; exact Ck]]. }
          destruct HinM as [HinM (k & ok & sh & -> & Hk)].
          rewrite forallb_forall in WMFc.
          unfold Ef, env_call. apply (proj2 (mfact_ok_setls segs (GL AL CS F fc m0 me) rls _ (s_nl ss) m' (MOpq k ok sh) eq_refl)).
          apply (mfact_ok_setzs segs (GL AL CS F fc m0 me) E rs (s_nx ss) m' _ (WMFc _ HinM)). cbn [g_L g_CS mfact_ok].
          rewrite List.Forall_forall in HM. pose proof (HM _ HinM) as X. cbn [mfact_ok] in X. destruct X as [_ LAW].
          split; [|exact LAW]. unfold eo. rewrite EO. apply QOQ. exact Hk.
      + apply List.Forall_forall. intros g Hg. apply in_map_iff in Hg as (f & <- & Hf).
        rewrite List.Forall_forall in QMF. rewrite forallb_forall in WMPOST.
        apply (sxm_ok _ Es th' tb tl' THs TBs TLs ELs); [| exact (QMF _ Hf)].
        eapply (bridge_m th' tb tl' _ _ _ true); [exact BNDs| rewrite forallb_forall in PBOpost; exact (PBOpost _ Hf)| exact LBNDs| exact (WMPOST _ Hf)].
    - (* [comment removed for export] *) apply fold_pf_add_Forall.
      + unfold Ef, env_call. apply (Forall_pf_setls (GL AL CS F fc m0 me)). apply (Forall_pf_setzs (GL AL CS F fc m0 me) E rs (s_nx ss)); [exact WPFc| exact HP].
      + apply List.Forall_forall. intros g Hg. apply in_flat_map in Hg as (f & Hf & Hg).
        rewrite List.Forall_forall in QPF. rewrite forallb_forall in WPOST.
        assert (PF : pfact_ok CS Ef (sxp th' f)).
        { apply (sxp_ok _ Es th' THs EPs); [| exact (QPF _ Hf)]. eapply bridge_p; [exact BNDs| exact (WPOST _ Hf)]. }
        pose proof (norm_pf_ok (GL AL CS F fc m0 me) _ _ PF) as X. cbn [g_CS] in X. rewrite List.Forall_forall in X. apply X. exact Hg.
    - (* [comment removed for export] *)
      assert (ENDS : Forall (fun lh => zdenp Ef (fst lh) = zdenp E (fst lh) /\ zdenp Ef (snd lh) = zdenp E (snd lh))
                            (w_adds (s_pf ss) (s_W ss) W)).
      { apply (w_adds_ends (fun e => zdenp Ef e = zdenp E e)).
        - apply List.Forall_forall. intros [l h] Hin. rewrite forallb_forall in WWc. specialize (WWc _ Hin). cbn [fst snd] in WWc |- *.
          apply andb_prop in WWc as [Wl Wh]. rewrite !zdenp_ok, !ZEf. rewrite !zden_setzs by assumption. split; reflexivity.
        - unfold W, sxw. apply List.Forall_forall. intros lh Hin. apply in_map_iff in Hin as ([l h] & <- & Hin). cbn [fst snd].
          rewrite forallb_forall in WW. pose proof (WW _ Hin) as X. cbn [fst snd] in X. apply andb_prop in X as [Wl Wh].
          rewrite !zdenp_ok.
          rewrite (sxe_den _ Es th THf l), (sxe_den _ Es th THf h);
            [| eapply bridge_bound; [exact BND| exact Wh] | exact (eloc_enoU _ _ Wh) | eapply bridge_bound; [exact BND| exact Wl] | exact (eloc_enoU _ _ Wl)].
          rewrite (sxe_den E E' th TH l), (sxe_den E E' th TH h);
            [| eapply bridge_bound; [exact BND| exact Wh] | exact (eloc_enoU _ _ Wh) | eapply bridge_bound; [exact BND| exact Wl] | exact (eloc_enoU _ _ Wl)].
          rewrite (EE l Wl), (EE h Wh). split; reflexivity. }
      rewrite (wden_ext _ E _ ENDS).
      eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU MU2)].
      intros x Hx. exact (w_adds_sub E (s_pf ss) (s_W ss) W x DLE Hx).
    }
    (* [comment removed for export] *)
    intros l HLAW NMC.
    apply andb_prop in NMC as [NMC MRF]. apply andb_prop in NMC as [RLT NM0]. apply Nat.ltb_lt in RLT. apply Nat.ltb_lt in NM0.
    unfold sum_frame in QFR. rewrite HLAW in QFR. destruct QFR as [QLAW QMI].
    set (kc := s_nm ss) in *. set (E2 := env_law E (s_nx ss) rs (s_nl ss) rls kc m m').
    assert (E2f : E2 = env_setm (env_setm Ef kc m) (S kc) m') by reflexivity.
    assert (LAWm : elaw E l (wden E W) m m') by (unfold elaw; rewrite ELW, WE; exact QLAW).
    assert (EM2 : forall j, (j < kc)%nat -> em E2 j = em E j).
    { intros j Hj. rewrite E2f. rewrite !em_setm. destruct (Nat.eqb_spec j (S kc)); [lia|]. destruct (Nat.eqb_spec j kc); [lia|]. unfold Ef, env_call. rewrite em_setls. apply em_setzs. }
    assert (EMc : em E2 kc = m).
    { rewrite E2f. rewrite !em_setm. destruct (Nat.eqb_spec kc (S kc)); [lia|]. rewrite Nat.eqb_refl. reflexivity. }
    assert (EMp : em E2 (S kc) = m') by (rewrite E2f; rewrite em_setm, Nat.eqb_refl; reflexivity).
    assert (ZD2 : forall e, zden E2 e = zden Ef e) by (intros e; rewrite E2f; rewrite !zden_setm; reflexivity).
    assert (WD2 : forall W0, wden E2 W0 = wden Ef W0) by (intros W0; rewrite E2f; rewrite !wden_setm; reflexivity).
    assert (EL2 : forall l0, elaw E2 l0 = elaw Es l0) by (intros l0; rewrite E2f; rewrite !elaw_setm; apply ELs).
    assert (THs2 : forall i e, sub_get th' i = Some e -> zden E2 e = ez Es i) by (intros i e G0; rewrite ZD2; apply THs; exact G0).
    assert (TBs2 : forall kb kk, bsub_get tb kb = Some (BVar kk) -> eb E2 kk = eb Es kb) by (intros kb kk G0; rewrite E2f; rewrite !eb_setm; apply TBs; exact G0).
    assert (TLs2 : forall j l0, lsub_get tl' j = Some l0 -> ldenw E2 l0 = el Es j) by (intros j l0 G0; rewrite E2f; rewrite !ldenw_setm; apply TLs; exact G0).
    unfold INV. unfold sum_post. rewrite HLAW. cbn [s_mf s_pf s_W s_same s_ref s_nm]. fold th'. fold tl'. fold W. fold kc. cbn [g_L g_CS g_m0].
    unfold refm. cbn [s_ref]. rewrite EMp.
    split; [|split; [|split; [intros x Hx; reflexivity| split; [apply wmono_refl| split; [exact QMI| apply same_gone]]]]].
    - (* [comment removed for export] *)
      rewrite forallb_forall in WMFc. rewrite forallb_forall in MRF.
      apply Forall_app. split.
      + constructor; [|constructor; [|constructor; [|constructor]]]; cbn [mfact_ok].
        * rewrite (EM2 (s_ref ss) RLT), EMc, WD2. unfold Ef, env_call. rewrite wden_setls, (wden_setzs E rs (s_nx ss) (s_W ss) WWc). exact MU.
        * rewrite (EM2 (s_ref ss) RLT), EMc. exact WM.
        * rewrite EMc, EMp, EL2, WD2, WEf. exact QLAW.
      + apply install_post_Forall.
        * apply Forall_app. split.
          -- apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin Hsv].
             rewrite E2f. rewrite forallb_forall in MLF.
             apply (proj2 (mfact_ok_setm segs AL CS _ (S kc) m' m' f (mrefs_lt_mono kc (S kc) f (MRF _ Hin) ltac:(lia)))).
             apply (proj2 (mfact_ok_setm segs AL CS _ kc m m' f (MRF _ Hin))).
             unfold Ef, env_call. apply (proj2 (mfact_ok_setls segs (GL AL CS F fc m0 me) rls _ (s_nl ss) m' f (MLF _ Hin))).
             apply (mfact_ok_setzs segs (GL AL CS F fc m0 me) E rs (s_nx ss) m' f (WMFc _ Hin)). cbn [g_L g_CS].
             pose proof HM as HMl. rewrite List.Forall_forall in HMl.
             refine (law_survives_sound segs AL CS E C m m' (s_pf ss) (s_mf ss) W l true HP HM LAWm HACC HSB _ CR _ _ _ _ f (HMl _ Hin) Hsv).
             { intros W1. eapply w_all_client_sound; [exact HP| exact CR| exact W1]. }
             { intros W2. eapply all_nonempty_sound; [exact HP| exact W2]. }
          -- (* [comment removed for export] *)
             rewrite OQR. apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin _].
             assert (HinM : In f (s_mf ss) /\ exists k ok sh, f = MOpq k ok sh /\ In k (su_oreq su)).
             { clear - OQR Hin. revert oql OQR Hin. unfold opq_required. induction (su_oreq su) as [|k0 ks IH]; intros oql OQR Hin.
               - cbn in OQR. injection OQR; intros <-. destruct Hin.
               - cbn [fold_right] in OQR.
                 match type of OQR with (match ?acc with _ => _ end) = _ => destruct acc as [l0|] eqn:R0; [|discriminate] end.
                 destruct (opq_find (s_mf ss) k0) as [g|] eqn:Fg; [|discriminate]. injection OQR; intros <-.
                 destruct Hin as [<-|Hin].
                 + destruct (opq_find_In _ _ _ Fg) as (ok & sh & -> & Hg). split; [exact Hg| exists k0, ok, sh; split; [reflexivity| left; reflexivity]].
                 + destruct (IH l0 eq_refl Hin) as [A (k & ok & sh & B & Ck)]. split; [exact A| exists k, ok, sh; split; [exact B| right; exact Ck]]. }
             destruct HinM as [HinM (k & ok & sh & -> & Hk)]. rewrite E2f.
             apply (proj2 (mfact_ok_setm segs AL CS _ (S kc) m' m' (MOpq k ok sh) eq_refl)). apply (proj2 (mfact_ok_setm segs AL CS _ kc m m' (MOpq k ok sh) eq_refl)).
             unfold Ef, env_call. apply (proj2 (mfact_ok_setls segs (GL AL CS F fc m0 me) rls _ (s_nl ss) m' (MOpq k ok sh) eq_refl)).
             apply (mfact_ok_setzs segs (GL AL CS F fc m0 me) E rs (s_nx ss) m' _ (WMFc _ HinM)). cbn [g_L g_CS mfact_ok].
             rewrite List.Forall_forall in HM. pose proof (HM _ HinM) as X. cbn [mfact_ok] in X. destruct X as [_ LAW].
             split; [|exact LAW]. unfold eo. rewrite EO. apply QOQ. exact Hk.
        * apply List.Forall_forall. intros g Hg. apply in_map_iff in Hg as (f & <- & Hf).
          rewrite List.Forall_forall in QMF. rewrite forallb_forall in WMPOST.
          apply (sxm_ok _ Es th' tb tl' THs2 TBs2 TLs2 EL2); [| exact (QMF _ Hf)].
          eapply (bridge_m th' tb tl' _ _ _ true); [exact BNDs| rewrite forallb_forall in PBOpost; exact (PBOpost _ Hf)| exact LBNDs| exact (WMPOST _ Hf)].
    - (* [comment removed for export] *) rewrite E2f. apply Forall_pf_setm, Forall_pf_setm. apply fold_pf_add_Forall.
      + unfold Ef, env_call. apply (Forall_pf_setls (GL AL CS F fc m0 me)). apply (Forall_pf_setzs (GL AL CS F fc m0 me) E rs (s_nx ss)); [exact WPFc| exact HP].
      + apply List.Forall_forall. intros g Hg. apply in_flat_map in Hg as (f & Hf & Hg).
        rewrite List.Forall_forall in QPF. rewrite forallb_forall in WPOST.
        assert (PF : pfact_ok CS Ef (sxp th' f)).
        { apply (sxp_ok _ Es th' THs EPs); [| exact (QPF _ Hf)]. eapply bridge_p; [exact BNDs| exact (WPOST _ Hf)]. }
        pose proof (norm_pf_ok (GL AL CS F fc m0 me) _ _ PF) as X. cbn [g_CS] in X. rewrite List.Forall_forall in X. apply X. exact Hg.
  Qed.

  (* [comment removed for export] *)
  Theorem apply_summary0_soundH : forall su hc F fc m0 me C genv E ss m (TGT : Model -> machine_state -> Prop),
    summary_validHR segs AL GS OPS LAWS PROPS (elb0 E) (ehp E) (ecw E) (elh E) (ehr E) TGT su hc CS ->
    Forall2 (fun g v => zden E g = v) genv GS -> eol E = OPS /\ elw E = LAWS /\ epr E = PROPS -> Forall (hlaw_ok segs) (elh E) ->
    forallb (evars_lt (s_nx ss)) genv = true ->
    cfg_ok (GL AL CS F fc m0 me) C E -> length (s_rs ss) = 31%nat -> ss_wf C ss = true -> INV segs (GL AL CS F fc m0 me) E ss m ->
    forall k kl ss1 oss2, apply_summary0 C genv su ss = SumOkM k kl ss1 oss2 ->
    heap_kont segs (GL AL CS F fc m0 me) TGT E ss k kl ss1 ->
    match oss2 with Some ss2 => heap_kont segs (GL AL CS F fc m0 me) TGT E ss k kl ss2 | None => True end ->
    TGT (ecur E) (ms_den segs (GL AL CS F fc m0 me) E ss m).
  Proof.
    intros su hc F fc m0 me C genv E ss m TGT [HEAP V] GV (EO & ELW & EPR) HLOK GWF CFG Hlen WF HI k kl ss1 oss2 AP0 KONT1 KONT2.
    pose proof HI as (HM & HP & MU & WM & MI & SAME). cbn [g_L g_CS g_m0 g_F g_fc] in HM, HP, MU, WM |- *.
    pose proof (mk_oracle_sound CS E _ HP) as HO.
    pose proof (cranges_sound segs AL CS E m _ _ HP HM) as CR.
    unfold apply_summary0 in AP0.
    destruct (su_wf su) eqn:SWF; [|discriminate].
    destruct (Bool.eqb (su_acc su) (acc_mode C)) eqn:ACC; [|discriminate]. apply Bool.eqb_prop in ACC.
    destruct (Nat.eqb_spec (length (s_rs ss)) 31) as [L31|]; [|discriminate]. cbn [negb] in AP0.
    destruct (forallb (mflvars_lt (s_nl ss)) (s_mf ss)) eqn:MLF; [|discriminate]. cbn [negb] in AP0.
    destruct (s_pc ss) as [pc|r] eqn:HPC; [|discriminate].
    destruct (Z.eqb_spec pc (su_pc su)) as [->|]; [|discriminate]. cbn [negb] in AP0.
    match type of AP0 with (match ?o with _ => _ end) = _ => destruct o as [ra|] eqn:RA; [|discriminate] end.
    destruct (sum_match C genv su ss) as [[[th tb] tl] code] eqn:SM. destruct code; try discriminate.
    destruct (forallb (post_blobs_ok tb) (su_req su ++ su_mpost su)) eqn:PBO; [|discriminate]. cbn [negb] in AP0.
    destruct (opq_required (s_mf ss) (su_oreq su)) as [oql|] eqn:OQR; [|discriminate].
    rewrite HEAP in AP0.
    destruct (Nat.ltb (s_ref ss) (s_nm ss) && Nat.ltb 0 (s_nm ss) && forallb (mrefs_lt (s_nm ss)) (s_mf ss)) eqn:NMC; [|discriminate].
    destruct (hc_wf su hc tb) eqn:HWF; [|discriminate]. cbn [negb] in AP0.
    destruct (sum_postH su hc ss th tb tl ra (su_post su) (su_mpost su) (hc_eff hc) (hc_hpost hc)) as [ssA|] eqn:PH1; [|discriminate].
    assert (CASES : k = su_nr su /\ kl = su_nrl su /\ ss1 = ssA /\
              match hc_alt hc with
              | None => True
              | Some (post2, mpost2, eff2) => exists ss2, oss2 = Some ss2 /\ sum_postH su hc ss th tb tl ra post2 mpost2 eff2 [] = Some ss2
              end).
    { revert AP0. destruct (hc_alt hc) as [[[post2 mpost2] eff2]|]; intros AP0.
      - destruct eff2 as [|ja2 en2|ja2|]; [| | discriminate|];
          match type of AP0 with (match ?o with _ => _ end) = _ => destruct o as [ss2|] eqn:PH2; [|discriminate] end;
          injection AP0; intros E4 E3 E2 E1; subst k kl ss1 oss2; (split; [reflexivity| split; [reflexivity| split; [reflexivity| exists ss2; split; [reflexivity| first [exact PH2| reflexivity]]]]]).
      - injection AP0; intros E4 E3 E2 E1; subst k kl ss1 oss2. split; [reflexivity| split; [reflexivity| split; [reflexivity| exact I]]]. }
    clear AP0. destruct CASES as (-> & -> & -> & ALT).
    rewrite forallb_app in PBO. apply andb_prop in PBO as [PBOreq PBOpost].
    apply andb_prop in NMC as [NMC MRF]. apply andb_prop in NMC as [RLT NM0]. apply Nat.ltb_lt in RLT. apply Nat.ltb_lt in NM0.
    (* [comment removed for export] *)
    unfold sum_match in SM.
    destruct (match_regs ss (su_rbind su) []) as [th0|] eqn:MR; [|discriminate].
    destruct (match_globals genv (su_gbind su) th0) as [th1|] eqn:MG; [|discriminate].
    match type of SM with match ?o with _ => _ end = _ => destruct o as [th2|] eqn:MSB; [|discriminate] end.
    destruct (match_chunks (s_mf ss) (su_mbind su) th2 []) as [[th3c tb3]|] eqn:MC; [|discriminate].
    destruct (match_arrs (s_pf ss) (s_mf ss) (su_mbind su) th3c []) as [[th3 tl3]|] eqn:MA; [|discriminate].
    match type of SM with match ?o with _ => _ end = _ => destruct o as [th4|] eqn:MST; [|discriminate] end.
    match type of SM with match ?o with _ => _ end = _ => destruct o as [[th5 tb5]|] eqn:BB; [| exfalso; injection SM; lia] end.
    destruct (all_bbound tb5 (su_nb su) 1) eqn:ABB; [|discriminate]. cbn [negb] in SM.
    destruct (lforallb (fun f => req_ok C (s_pf ss) (cranges (s_pf ss) (s_mf ss)) (s_mf ss) (sxm th5 tb5 tl3 f)) (su_req su)) eqn:REQ; [|discriminate]. cbn [negb] in SM.
    rewrite lforallb_forallb in REQ.
    match type of SM with (if negb ?c then _ else _) = _ => destruct c eqn:KEYS; [|discriminate] end. cbn [negb] in SM.
    injection SM; intros <- <- <-. apply andb_prop in KEYS as [KEYS LALL]. apply andb_prop in KEYS as [KEYS LKEYS]. apply andb_prop in KEYS as [KEYS BKEYS].
    (* [comment removed for export] *)
    destruct (match_regs_ok _ _ _ _ MR) as [S00 RB0]. destruct (match_globals_ok _ _ _ _ MG) as [S01 GB].
    assert (RB : Forall (fun ri => sub_get th1 (snd ri) = Some (rd_expr ss (fst ri))) (su_rbind su)).
    { eapply Forall_impl; [|exact RB0]. intros ri Hri. apply S01. exact Hri. }
    assert (S12 : thsub th1 th2 /\ match su_sb su, c_acc C with Some i, Some A => sub_get th2 i = Some (ac_sb A) | Some _, None => False | None, _ => True end).
    { destruct (su_sb su) as [isb|]; [destruct (c_acc C) as [A|]; [|discriminate]|].
      - destruct (bind_ok _ _ _ _ MSB) as [G S]. split; assumption.
      - injection MSB; intros <-. split; [apply thsub_refl| exact I]. }
    destruct S12 as [S12 SB].
    destruct (match_chunks_ok _ _ _ _ _ _ MC) as (S23c & T03 & R3). destruct (match_arrs_ok _ _ _ _ _ _ _ MA) as (S3A & TL3 & RAR).
    assert (S23 : thsub th2 th3) by (eapply thsub_trans; [exact S23c| exact S3A]).
    assert (S34 : thsub th3 th4 /\ match su_stk su with Some (ilo, ihi) => exists lo h, sub_get th4 ihi = Some h /\ sub_get th4 ilo = Some lo /\ stk_just (s_mf ss) (s_mf ss) lo h | None => True end).
    { destruct (su_stk su) as [[ilo ihi]|].
      - destruct (sub_get th3 ihi) as [h|] eqn:GH; [|discriminate]. destruct (match_stk_ok _ _ _ _ _ _ MST) as (S & lo & G & IN).
        split; [exact S|]. exists lo, h. split; [apply S; exact GH|]. split; [exact G| exact IN].
      - injection MST; intros <-. split; [apply thsub_refl| exact I]. }
    destruct S34 as [S34 STK].
    destruct (bind_bytes_ok _ _ _ _ _ _ _ BB) as (S45 & T35 & PREOK & BBF).
    apply andb_prop in PREOK as [ABD PRE]. rewrite lforallb_forallb in PRE.
    set (th := th5) in *. set (tb := tb5) in *. set (tl := tl3) in *.
    (* [comment removed for export] *)
    destruct (heap_find (s_mf ss)) as [[bl ok]|] eqn:HF.
    2:{ exfalso. unfold sum_postH in PH1. rewrite HF in PH1. discriminate. }
    pose proof (heap_find_In _ _ _ HF) as HFin.
    set (LB := blden E bl).
    (* [comment removed for export] *)
    set (ps := pvals E th (su_np su)). set (bss := bvals E tb (su_nb su)). set (lss := lvals E tl (su_nl su)).
    set (E' := ENV ps [] bss OPS lss [] LAWS PROPS (elb0 E) (ehp E) (ecw E) (elh E) (ecur E) [LB] (ehr E)).
    assert (ELr : forall l0, elaw E l0 = elaw E' l0) by (intros l0; unfold elaw; rewrite ELW; reflexivity).
    assert (KEY : forall i e, sub_get th i = Some e -> (Pos.to_nat i <= (su_np su))%nat).
    { intros i e G. pose proof (keys_lt_sound _ _ KEYS i e G) as X. unfold su_npP in X. lia. }
    assert (BKEY : forall i kk, bsub_get tb i = Some kk -> (Pos.to_nat i <= (su_nb su))%nat).
    { intros i kk G. pose proof (bkeys_lt_sound _ _ BKEYS i kk G) as X. unfold su_nbP in X. lia. }
    assert (LKEY : forall j l, lsub_get tl j = Some l -> (Pos.to_nat j <= (su_nl su))%nat).
    { intros j l G. assert (X : Pos.ltb j (su_nlP su) = true).
      { rewrite forallb_forall in LKEYS. revert G. clear - LKEYS. induction tl as [|[j' l'] tl IH]; cbn; intros G; [discriminate|].
        destruct (Pos.eqb_spec j j') as [<-|]; [exact (LKEYS (j, l') (or_introl eq_refl))| apply IH; [intros p Hp; apply LKEYS; right; exact Hp| exact G]]. }
      apply Pos.ltb_lt in X. unfold su_nlP in X. lia. }
    assert (TLh : forall j l, lsub_get tl j = Some l -> ldenw E l = el E' j).
    { intros j l G. unfold E', lss, el. cbn [ell]. rewrite (lvals_get E tl (su_nl su) j (LKEY j l G)). unfold tlv. rewrite G. reflexivity. }
    assert (LBND : forall j, (j < su_nlP su)%positive -> lsub_get tl j <> None).
    { intros j Hj. apply (lall_bound_ok tl (su_nl su) 1); [exact LALL| lia| unfold su_nlP in Hj; lia]. }
    assert (TH : forall i e, sub_get th i = Some e -> zden E e = ez E' i).
    { intros i e G. unfold E', ps, ez. cbn [ezl]. rewrite (pvals_get E th (su_np su) i (KEY i e G)). unfold thv. rewrite G. reflexivity. }
    assert (TB : forall kb kk, bsub_get tb kb = Some kk -> bval_den E kk = eb E' kb).
    { intros kb kk G. unfold E', bss. unfold eb at 1. cbn [ebl]. rewrite (bvals_get E tb (su_nb su) kb (BKEY kb kk G)). unfold bvalk. rewrite G. reflexivity. }
    assert (TBv : forall kb kk, bsub_get tb kb = Some (BVar kk) -> eb E kk = eb E' kb).
    { intros kb kk G. exact (TB kb (BVar kk) G). }
    assert (BND : forall i, (i < su_npP su)%positive -> sub_get th i <> None).
    { intros i Hi. apply (all_bound_ok th (su_np su) 1); [exact ABD| lia| unfold su_npP in Hi; lia]. }
    assert (BBND : forall kb, (kb < su_nbP su)%positive -> bsub_get tb kb <> None).
    { intros kb Hk. apply (all_bbound_ok tb (su_nb su) 1); [exact ABB| lia| unfold su_nbP in Hk; lia]. }
    assert (THL : forall j, (j < su_npP su)%positive -> zden E (sxe th (EZv j)) = ez E' j).
    { intros j Hj. rewrite (sxe_den E E' th TH (EZv j)); [reflexivity| |reflexivity]. cbn. destruct (sub_get th j) eqn:G; [reflexivity|]. exfalso. exact (BND j Hj G). }
    (* [comment removed for export] *)
    pose proof SWF as SWF0. unfold su_wf in SWF.
    apply andb_prop in SWF as [SWF WPOST]. apply andb_prop in SWF as [SWF WMPOST]. apply andb_prop in SWF as [SWF WCLOB].
    apply andb_prop in SWF as [SWF WW]. apply andb_prop in SWF as [SWF WPRE]. apply andb_prop in SWF as [SWF WREQ].
    apply andb_prop in SWF as [SWF WBB]. apply andb_prop in SWF as [SWF WSTK]. apply andb_prop in SWF as [SWF WMB].
    apply andb_prop in SWF as [SWF WSB]. apply andb_prop in SWF as [WRB WGB].
    unfold hc_wf in HWF. apply andb_prop in HWF as [HWF WALT]. apply andb_prop in HWF as [HWF WHP1]. apply andb_prop in HWF as [WSP WEFF1]. apply Pos.ltb_lt in WSP.
    (* [comment removed for export] *)
    set (R := map (rden E) (s_rs ss)).
    assert (LR : length R = 31%nat) by (unfold R; rewrite map_length; exact L31).
    pose proof (zforall_apply _ _ ps V (pvals_length E th (su_np su))) as V1. cbn beta in V1.
    pose proof (bforall_apply _ _ bss V1 (bvals_length E tb (su_nb su))) as V2b. cbn beta in V2b. clear V1.
    pose proof (lforall_apply _ _ lss V2b (lvals_length E tl (su_nl su))) as V2. cbn beta in V2. clear V2b.
    pose proof (wforall_apply _ _ R (V2 F fc m (ecur E) LB) LR) as V3. cbn beta in V3. clear V2. fold E' in V3.
    assert (ACCP : if su_acc su then cs_ok AL CS /\ al_wf AL else forall x, CS x).
    { unfold cfg_ok in CFG. cbn [g_L g_CS] in CFG. unfold acc_mode in ACC.
      destruct (su_acc su); destruct (c_acc C) as [A|]; try discriminate; [|exact CFG].
      destruct CFG as (C1 & C2 & _). split; assumption. }
    assert (SBP : match su_sb su with Some i => ez E' i = al_sb AL | None => True end).
    { destruct (su_sb su) as [isb|]; [|exact I]. destruct (c_acc C) as [A|] eqn:HCA; [|destruct SB].
      rewrite <- (TH isb (ac_sb A)) by (apply S45, S34, S23; exact SB).
      unfold cfg_ok in CFG. rewrite HCA in CFG. cbn [g_L g_CS] in CFG. destruct CFG as (_ & _ & S1 & _). rewrite <- zdenp_ok. exact S1. }
    pose proof (V3 ACCP SBP MI) as V4g. clear V3.
    assert (GBP : forall i n, In (i, n) (su_gbind su) -> ez E' i = nth n GS 0).
    { intros i n Hin. rewrite List.Forall_forall in GB. destruct (GB _ Hin) as (g & NG & Gi). cbn [fst snd] in NG, Gi.
      rewrite <- (TH i g) by (apply S45, S34, S23, S12; exact Gi). exact (Forall2_nth_error _ _ _ _ _ GV NG). }
    pose proof (gb_tele_elim _ _ _ V4g GBP) as V4. clear V4g.
    assert (RBP : forall r i, In (r, i) (su_rbind su) -> rgetZ R r = Z_to_bv 64 (ez E' i)).
    { intros r i Hin. rewrite List.Forall_forall in RB. pose proof (RB _ Hin) as G. cbn [fst snd] in G.
      rewrite forallb_forall in WRB. specialize (WRB _ Hin). cbn [fst snd] in WRB.
      apply andb_prop in WRB as [WRB R31]. apply andb_prop in WRB as [_ R1]. apply Z.leb_le in R1. apply Z.leb_le in R31.
      rewrite <- (TH i (rd_expr ss r)) by (apply S45, S34, S23, S12; exact G).
      destruct r as [|p|p]; try lia. unfold rgetZ. rewrite pget_nth. unfold R.
      rewrite (nth_map' (rden E) (s_rs ss) _ (RZ (ELit 0))) by lia.
      unfold rd_expr, rd_reg. cbn [Z.eqb]. rewrite lget_nth. replace (Z.to_nat (Z.pos p - 1)) with (Pos.to_nat p - 1)%nat by lia.
      symmetry. apply expr_of_reg_den. }
    pose proof (rb_tele_elim _ _ _ _ V4 RBP) as V5. clear V4.
    assert (STKP : match su_stk su with Some (ilo, ihi) => stk segs m (ez E' ilo) (ez E' ihi) | None => True end).
    { destruct (su_stk su) as [[ilo ihi]|]; [|exact I]. destruct STK as (lo & h & Gh & Glo & IN).
      rewrite <- (TH ilo lo), <- (TH ihi h) by (apply S45; assumption).
      exact (stk_just_sound segs AL CS E m _ _ _ _ HM HM IN). }
    specialize (V5 STKP).
    assert (HACC : forall A, c_acc C = Some A -> ac_got A = al_got AL /\ ac_gsb A = al_gsb AL /\ cs_ok AL CS).
    { intros A HCA. unfold cfg_ok in CFG. rewrite HCA in CFG. cbn [g_L g_CS] in CFG. destruct CFG as (C1 & _ & _ & _ & _ & G1 & G2). split; [exact G1| split; [exact G2| exact C1]]. }
    assert (HSB : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb AL).
    { intros A HCA. unfold cfg_ok in CFG. rewrite HCA in CFG. cbn [g_L g_CS] in CFG. destruct CFG as (_ & _ & S1 & _). exact S1. }
    assert (MFP : Forall (mfact_ok segs AL CS E' m) (su_mbind su ++ bb_facts (su_bbind su) ++ su_req su)).
    { apply Forall_app. split; [|apply Forall_app; split].
      - assert (R3' : Forall (fun f => match f with MArr _ _ _ _ _ => True | _ => mfact_ok segs AL CS E' m f end) (su_mbind su)).
        { apply (R3 segs AL CS m E E' th tb); [eapply thsub_trans; [exact S3A|]; eapply thsub_trans; [exact S34| exact S45]| exact T35| exact TH| exact TB| |exact HM].
          apply List.Forall_forall. intros f Hf. rewrite forallb_forall in WMB. specialize (WMB f Hf).
          destruct f; try exact I. cbn -[eloc forallb cloc] in WMB. apply andb_prop in WMB as [WA _]. exact (eloc_enoU _ _ WA). }
        assert (RA' : Forall (fun f => match f with MArr _ _ _ _ _ => mfact_ok segs AL CS E' m f | _ => True end) (su_mbind su)).
        { apply (RAR segs AL CS m E E' th tl); [eapply thsub_trans; [exact S34| exact S45]| intros i x Hx; exact Hx| exact TH| exact TLh| |exact HM| exact HP].
          apply List.Forall_forall. intros f Hf. rewrite forallb_forall in WMB. specialize (WMB f Hf).
          destruct f as [| | | | | |fa fw [fj|] fn fwr| | | | | | | | | | |hj ho hn hxs hok]; try exact I; [|discriminate]. cbn -[eloc Pos.ltb orb N.eqb] in WMB.
          repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end.
          match goal with G : eloc _ fa = true |- _ => exact (eloc_enoU _ _ G) end. }
        rewrite List.Forall_forall in R3', RA'. apply List.Forall_forall. intros f Hf. specialize (R3' f Hf). specialize (RA' f Hf). destruct f; assumption.
      - unfold bb_facts. apply List.Forall_forall. intros f Hf. apply in_map_iff in Hf as ([[ia il] kb] & <- & Hin).
        rewrite List.Forall_forall in BBF. destruct (BBF _ Hin) as (a & n & kc & INC & Ga & Gn & Gk).
        apply mby_facts_In in INC. rewrite List.Forall_forall in HM. pose proof (HM _ INC) as X. cbn in X. rewrite !zdenp_ok in X.
        cbn [mfact_ok zdenp]. rewrite <- (TH ia a Ga), <- (TH il n Gn), <- (TB kb (BVar kc) Gk). exact X.
      - apply List.Forall_forall. intros f Hf. rewrite forallb_forall in REQ. pose proof (REQ f Hf) as X.
        apply (req_ok_sound segs AL CS E C m _ _ _ HP HACC HSB CR HM) in X. apply (sxm_ok E E' th tb tl TH TBv TLh ELr) in X; [exact X|].
        rewrite forallb_forall in WREQ. rewrite forallb_forall in PBOreq. eapply bridge_m; [exact BND| exact (PBOreq f Hf)| exact LBND| exact (WREQ f Hf)]. }
    pose proof (mf_tele_elim _ E' m _ _ V5 MFP) as V6. clear V5.
    assert (PFP : Forall (pfact_ok CS E') (su_pre su)).
    { apply List.Forall_forall. intros f Hf. rewrite forallb_forall in PRE. pose proof (PRE f Hf) as X.
      assert (EPR' : epr E = epr E') by (rewrite EPR; reflexivity).
      apply (pf_decide_sound CS E _ _ _ _ HP CR HO) in X. apply (sxp_ok E E' th TH EPR') in X; [exact X|].
      rewrite forallb_forall in WPRE. eapply bridge_p; [exact BND| exact (WPRE f Hf)]. }
    pose proof (pf_tele_elim _ E' _ _ V6 PFP) as V7. clear V6.
    assert (OQF : forall k, In k (su_oreq su) -> exists ok' sh, In (MOpq k ok' sh) (s_mf ss)) by (intros k Hk; exact (opq_required_In _ _ _ _ OQR Hk)).
    assert (OQP : forall k, In k (su_oreq su) -> nth k OPS (fun _ => True) m).
    { intros k Hk. destruct (OQF k Hk) as (ok' & sh & Hin). rewrite List.Forall_forall in HM. pose proof (HM _ Hin) as X.
      cbn [mfact_ok] in X. destruct X as [X _]. unfold eo in X. rewrite EO in X. exact X. }
    pose proof (oq_tele_elim _ _ _ _ V7 OQP) as EV. clear V7.
    (* [comment removed for export] *)
    assert (MSE : ms_den segs (GL AL CS F fc m0 me) E ss m = MS (rdw R) F (Z_to_bv 64 (su_pc su)) fc None m (seg_rom segs)).
    { unfold ms_den. cbn [g_F g_fc]. rewrite HPC, regs_den_rdw. reflexivity. }
    rewrite MSE.
    (* [comment removed for export] *)
    pose proof WF as WF0. unfold ss_wf in WF.
    apply andb_prop in WF as [WF WSBc]. apply andb_prop in WF as [WF WWc]. apply andb_prop in WF as [WF WPFc].
    apply andb_prop in WF as [WF WMFc]. apply andb_prop in WF as [WPCc WRc].
    assert (WFP : thP (fun e => evars_lt (s_nx ss) e = true) th).
    { assert (T0 : thP (fun e => evars_lt (s_nx ss) e = true) []) by (intros i e G; discriminate).
      assert (RDX : forall r, evars_lt (s_nx ss) (rd_expr ss r) = true).
      { intros r. unfold rd_expr, rd_reg. destruct (Z.eqb r 0); [reflexivity|]. rewrite lget_nth.
        destruct (Nat.lt_ge_cases (Z.to_nat (r - 1)) (length (s_rs ss))) as [LT|GE].
        - rewrite forallb_forall in WRc. specialize (WRc _ (nth_In _ (RZ (ELit 0)) LT)). destruct (nth _ _ _) as [i|e]; cbn in WRc |- *; [reflexivity| exact WRc].
        - rewrite nth_overflow by lia. reflexivity. }
      assert (T0' : thP (fun e => evars_lt (s_nx ss) e = true) th0) by (eapply match_regs_P; [exact T0| exact RDX| exact MR]).
      assert (T1 : thP (fun e => evars_lt (s_nx ss) e = true) th1).
      { eapply match_globals_P; [exact T0'| | exact MG]. intros g Hg. rewrite forallb_forall in GWF. apply GWF. exact Hg. }
      assert (T2 : thP (fun e => evars_lt (s_nx ss) e = true) th2).
      { destruct (su_sb su) as [isb|]; [destruct (c_acc C) as [A|]; [|destruct SB]|].
        - eapply bind_P; [exact T1| exact WSBc| exact MSB].
        - injection MSB; intros <-. exact T1. }
      assert (T3c : thP (fun e => evars_lt (s_nx ss) e = true) th3c).
      { eapply match_chunks_P; [intros; reflexivity| exact T2| | exact MC]. intros a cs c e Hin Hc He.
        rewrite forallb_forall in WMFc. specialize (WMFc _ Hin). cbn -[evars_lt forallb cvars_lt] in WMFc. apply andb_prop in WMFc as [_ Wcs].
        rewrite forallb_forall in Wcs. specialize (Wcs _ Hc).
        destruct c as [i|w e'|w kk|w i|c o l|wr er]; cbn in He; try discriminate.
        - injection He; intros <-. reflexivity.
        - injection He; intros <-. exact Wcs.
        - destruct w as [|q]; [discriminate|]. destruct q as [q|q|]; try discriminate; destruct q as [q|q|]; try discriminate;
            [destruct q; try discriminate|]; injection He; intros <-; reflexivity. }
      assert (T3 : thP (fun e => evars_lt (s_nx ss) e = true) th3).
      { eapply match_arrs_P; [exact T3c| | exact MA]. intros a w l n wr Hin.
        rewrite forallb_forall in WMFc. specialize (WMFc _ Hin). cbn -[evars_lt lvars_lt] in WMFc. repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end. assumption. }
      assert (T4 : thP (fun e => evars_lt (s_nx ss) e = true) th4).
      { destruct (su_stk su) as [[ilo ihi]|].
        - destruct (sub_get th3 ihi) as [h|]; [|discriminate]. eapply match_stk_P; [exact T3| | exact MST].
          intros lo hi Hin. rewrite forallb_forall in WMFc. specialize (WMFc _ Hin). cbn -[evars_lt] in WMFc. apply andb_prop in WMFc as [Wlo _]. exact Wlo.
        - injection MST; intros <-. exact T3. }
      eapply bind_bytes_P; [exact T4| | exact BB]. intros a n kc Hin. apply mby_facts_In in Hin.
      rewrite forallb_forall in WMFc. specialize (WMFc _ Hin). cbn -[evars_lt] in WMFc. apply andb_prop in WMFc as [Wa Wn]. split; assumption. }
    set (W := sxw th (su_W su)).
    assert (WWB : forallb (fun lh => ebound th (fst lh) && enoU (fst lh) && ebound th (snd lh) && enoU (snd lh)) (su_W su) = true).
    { apply forallb_forall. intros [l h] Hin. rewrite forallb_forall in WW. specialize (WW _ Hin). cbn [fst snd] in WW |- *.
      apply andb_prop in WW as [Wl Wh].
      rewrite (bridge_bound th _ l BND Wl), (bridge_bound th _ h BND Wh), (eloc_enoU _ l Wl), (eloc_enoU _ h Wh). reflexivity. }
    assert (DLE : forall l h, dec_le00 (s_pf ss) l h = true -> zden E l <= zden E h) by (intros l h; apply (dec_le00_sound CS E); exact HP).
    pose proof WMFc as WMFl. rewrite forallb_forall in WMFl. pose proof MLF as MLFl. rewrite forallb_forall in MLFl.
    pose proof MRF as MRFl. rewrite forallb_forall in MRFl. pose proof HM as HMl. rewrite List.Forall_forall in HMl.
    pose proof (WMFl _ HFin) as HV. cbn [mfvars_lt] in HV. apply andb_prop in HV as [BLV OKV].
    pose proof (HMl _ HFin) as HPF0. cbn [mfact_ok] in HPF0. destruct HPF0 as [[HHP0 HOK0] [EXT0 HREST0]].
    assert (EXTl : forall b, In b (elb0 E) -> In b LB) by (exact EXT0).
    pose proof (MRFl _ HFin) as BLR. cbn [mrefs_lt] in BLR.   (* [comment removed for export] *)
    pose proof (ehlaw_ok segs E (hc_law hc) HLOK) as HOKl.
    (* [comment removed for export] *)
    assert (GENK : forall post mpost eff hposts ssX,
      forallb (mloc (su_nallP su) (su_nbP su) (su_nlaP su) true) mpost = true ->
      forallb (ploc (su_nallP su)) post = true ->
      bleff_wf su eff = true ->
      forallb (fun jx => forallb (eloc (su_nallP su)) (snd jx)) hposts = true ->
      forallb (post_blobs_ok tb) mpost = true ->
      sum_postH su hc ss th tb tl ra post mpost eff hposts = Some ssX ->
      heap_kont segs (GL AL CS F fc m0 me) TGT E ss (su_nr su) (su_nrl su) ssX ->
      heap_caseK segs AL OPS LAWS PROPS (elb0 E) (ehp E) (ecw E) (elh E) (ehr E) TGT su hc CS F fc m LB ps bss lss R post mpost eff hposts).
    { intros post mpost eff hposts ssX WMPOSTx WPOSTx WEFF WHPx PBOpostX PHX KONT.
      unfold heap_caseK. apply zforall_intro. intros rs Lrs. cbn beta. apply lforall_intro. intros rls Lrls. cbn beta. intros m' mo'.
      apply blforall_intro. intros lbx. cbv zeta.
      apply mf_tele_intro. cbn [g_L g_CS]. intros QMF. apply pf_tele_intro. cbn [g_CS]. intros QPF. apply oq_tele_intro. intros QOQ.
      apply hr_tele_intro. intros QHR.
      intros HHP HEP HLAW MI'.
      change (ez (ENV ps [] bss OPS lss [] LAWS PROPS (elb0 E) (ehp E) (ecw E) (elh E) mo'
                  (bl_lbs eff LB lbx) (ehr E)) (hc_sp hc))
        with (ez E' (hc_sp hc)) in HLAW.
      set (lbs := bl_lbs eff LB lbx) in *.
      set (Es := ENV (ps ++ rs) [] bss OPS (lss ++ rls) [] LAWS PROPS (elb0 E) (ehp E) (ecw E) (elh E) mo' lbs (ehr E)) in *.
      (* [comment removed for export] *)
      set (th' := res_subst (su_npP su) (su_nr su) (s_nx ss) th).
      set (tl' := lres_subst (su_nlP su) (su_nrl su) (s_nl ss) tl).
      set (Ef := env_call E (s_nx ss) rs (s_nl ss) rls).
      set (kc := s_nm ss) in *.
      set (E2 := env_heap E (s_nx ss) rs (s_nl ss) rls kc m m' mo' lbx).
      assert (E2f : E2 = env_setbl (env_setcur (env_setm (env_setm Ef kc m) (S kc) m') mo') (S kc) lbx) by reflexivity.
      set (sp := sxe th (EZv (hc_sp hc))).
      unfold sum_postH in PHX. rewrite HF in PHX. cbv beta iota in PHX. fold th' tl' kc W sp in PHX.
      match type of PHX with (match ?o with _ => _ end) = _ => destruct o as [[[[blN blL] extra] pextra]|] eqn:EFF; [|discriminate] end.
      injection PHX. clear PHX. intros PHX.
      assert (ELs : forall l0, elaw Ef l0 = elaw Es l0) by (intros l0; unfold Ef, env_call; rewrite elaw_setls, elaw_setzs; unfold elaw; rewrite ELW; reflexivity).
      assert (EPs : epr Ef = epr Es) by (unfold Ef, env_call; rewrite epr_setls, epr_setzs; rewrite EPR; reflexivity).
      assert (ZEf : forall e, zden Ef e = zden (setzs E (s_nx ss) rs) e) by (intros e; unfold Ef, env_call; apply zden_setls).
      (* [comment removed for export] *)
      assert (THs : forall i e, sub_get th' i = Some e -> zden Ef e = ez Es i).
      { intros i e G. rewrite ZEf. unfold th' in G. rewrite res_subst_get in G.
        match type of G with (if ?c then _ else _) = _ => destruct c eqn:RNG end.
        - apply andb_prop in RNG as [R1 R2]. apply Pos.leb_le in R1. apply Pos.ltb_lt in R2. unfold su_npP in R1, R2. fold (su_np su) in R1, R2.
          injection G; intros <-. rewrite eatom_den. cbn [zden]. rewrite ez_setzs_at by (rewrite Lrs; unfold su_npP in *; lia).
          unfold Es, ez. cbn [ezl]. unfold ps. rewrite pget_app_r by (rewrite pvals_length; unfold su_npP in *; lia). rewrite pvals_length. f_equal. unfold su_npP in *. lia.
        - pose proof (KEY i e G) as Ki. rewrite zden_setzs by (apply (WFP i e G)). rewrite (TH i e G).
          unfold E', Es, ez, ps. cbn [ezl]. rewrite pget_app_l by (rewrite pvals_length; lia). reflexivity. }
      assert (TBs : forall kb kk, bsub_get tb kb = Some (BVar kk) -> eb Ef kk = eb Es kb).
      { intros kb kk G. unfold Ef, env_call. rewrite eb_setls, eb_setzs. pose proof (TB kb (BVar kk) G) as X. cbn [bval_den] in X. rewrite X. reflexivity. }
      assert (TLQ : forall j l, lsub_get tl j = Some l -> lvars_lt (s_nx ss) l = true /\ llvars_lt (s_nl ss) l = true).
      { refine (match_arrs_LQ (fun l => lvars_lt (s_nx ss) l = true /\ llvars_lt (s_nl ss) l = true) _ _ _ _ _ _ _ _ _ MA); [intros j l G; discriminate|].
        intros a w l n wr Hin. pose proof (WMFl _ Hin) as X. pose proof (MLFl _ Hin) as Y.
        cbn -[evars_lt lvars_lt] in X. cbn in Y. repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end. split; assumption. }
      assert (TLs : forall j l, lsub_get tl' j = Some l -> ldenw Ef l = el Es j).
      { intros j l G. unfold tl' in G. rewrite lres_subst_get in G.
        match type of G with (if ?c then _ else _) = _ => destruct c eqn:RNG end.
        - apply andb_prop in RNG as [R1 R2]. apply Pos.leb_le in R1. apply Pos.ltb_lt in R2. unfold su_nlP in R1, R2.
          injection G; intros <-. cbn [ldenw]. unfold Ef, env_call. rewrite el_setls_at by (rewrite Lrls; unfold su_nrl, su_nlP in *; lia).
          unfold Es, el. cbn [ell]. unfold lss. rewrite pget_app_r by (rewrite lvals_length; unfold su_nlP in *; lia). rewrite lvals_length. f_equal. unfold su_nlP in *. lia.
        - pose proof (LKEY j l G) as Kj. destruct (TLQ j l G) as [Q1 Q2]. unfold Ef, env_call. rewrite ldenw_setls by exact Q2. rewrite ldenw_setzs by exact Q1.
          rewrite (TLh j l G). unfold E', Es, el. cbn [ell]. rewrite pget_app_l by (unfold lss; rewrite lvals_length; lia). reflexivity. }
      assert (LBNDs : forall j, (j < su_nlaP su)%positive -> lsub_get tl' j <> None).
      { intros j Hj. unfold tl'. rewrite lres_subst_get.
        match goal with |- (if ?c then _ else _) <> _ => destruct c eqn:RNG end; [discriminate|].
        apply LBND. unfold su_nlaP, su_nrl in *. unfold su_nlP in *.
        destruct (Pos.leb_spec (Pos.of_nat (S (su_nl su))) j); destruct (Pos.ltb_spec j (Pos.of_nat (Pos.to_nat (Pos.of_nat (S (su_nl su))) + (su_nla su - su_nl su)))); cbn in RNG; try discriminate; lia. }
      assert (S5s : thsub th th').
      { intros i e G. unfold th'. rewrite res_subst_get. pose proof (KEY i e G) as Ki.
        match goal with |- (if ?c then _ else _) = _ => destruct c eqn:RNG end; [|exact G].
        apply andb_prop in RNG as [R1 _]. apply Pos.leb_le in R1. unfold su_npP in R1. lia. }
      assert (BNDs : forall i, (i < su_nallP su)%positive -> sub_get th' i <> None).
      { intros i Hi. unfold th'. rewrite res_subst_get.
        match goal with |- (if ?c then _ else _) <> _ => destruct c eqn:RNG end; [discriminate|].
        apply BND. unfold su_nallP in Hi. unfold su_npP.
        destruct (Pos.leb_spec (su_npP su) i); destruct (Pos.ltb_spec i (Pos.of_nat (Pos.to_nat (su_npP su) + (su_nr su)))); cbn in RNG; try discriminate;
          unfold su_npP in *; lia. }
      assert (EE : forall e, eloc (su_npP su) e = true -> zden E' e = zden Es e).
      { intros e He. unfold E', Es. symmetry. apply zden_app_env. unfold ps. rewrite pvals_length. exact He. }
      assert (WE : wden E W = wden Es (su_W su)).
      { unfold W. rewrite (sxw_den E E' th TH _ WWB). apply wden_ext. apply List.Forall_forall. intros [l h] Hin.
        rewrite forallb_forall in WW. specialize (WW _ Hin). cbn [fst snd] in WW |- *. apply andb_prop in WW as [Wl Wh].
        rewrite !zdenp_ok. rewrite (EE l Wl), (EE h Wh). split; reflexivity. }
      assert (THf : forall i e, sub_get th i = Some e -> zden Ef e = ez Es i) by (intros i e G0; apply THs; apply S5s; exact G0).
      assert (WEf : wden Ef W = wden Es (su_W su)) by (unfold W; exact (sxw_den _ Es th THf _ WWB)).
      assert (SPE : zden E sp = ez E' (hc_sp hc)) by (unfold sp; exact (THL _ WSP)).
      assert (SPs : ez Es (hc_sp hc) = ez E' (hc_sp hc)).
      { symmetry. pose proof (EE (EZv (hc_sp hc))) as X. cbn [zden eloc] in X. apply X. apply Pos.ltb_lt. exact WSP. }
      assert (SPf : zden Ef sp = ez E' (hc_sp hc)).
      { unfold sp. rewrite (sxe_den Ef Es th THf (EZv (hc_sp hc))); [cbn [zden]; exact SPs| |reflexivity].
        cbn. destruct (sub_get th (hc_sp hc)) eqn:G; [reflexivity|]. exfalso. exact (BND _ WSP G). }
      (* [comment removed for export] *)
      assert (EM2 : forall j, (j < kc)%nat -> em E2 j = em E j).
      { intros j Hj. rewrite E2f. rewrite em_setbl, em_setcur, !em_setm. destruct (Nat.eqb_spec j (S kc)); [lia|]. destruct (Nat.eqb_spec j kc); [lia|]. unfold Ef, env_call. rewrite em_setls. apply em_setzs. }
      assert (EMc : em E2 kc = m).
      { rewrite E2f. rewrite em_setbl, em_setcur, !em_setm. destruct (Nat.eqb_spec kc (S kc)); [lia|]. rewrite Nat.eqb_refl. reflexivity. }
      assert (EMp : em E2 (S kc) = m') by (rewrite E2f; rewrite em_setbl, em_setcur, em_setm, Nat.eqb_refl; reflexivity).
      assert (ZD2 : forall e, zden E2 e = zden Ef e) by (intros e; rewrite E2f; rewrite zden_setbl, zden_setcur, !zden_setm; reflexivity).
      assert (ZP2 : forall e, zdenp E2 e = zdenp Ef e) by (intros e; rewrite !zdenp_ok; apply ZD2).
      assert (WD2 : forall W0, wden E2 W0 = wden Ef W0) by (intros W0; rewrite E2f; rewrite wden_setbl, wden_setcur, !wden_setm; reflexivity).
      assert (EL2 : forall l0, elaw E2 l0 = elaw Es l0) by (intros l0; rewrite E2f; rewrite elaw_setbl, elaw_setcur, !elaw_setm; apply ELs).
      assert (EHL2 : forall l0, ehlaw E2 l0 = ehlaw E l0).
      { intros l0. rewrite E2f. unfold ehlaw. cbn [elh env_setbl env_setcur env_setm]. unfold Ef, env_call. rewrite elh_setls, elh_setzs. reflexivity. }
      assert (EHP2 : ehp E2 = ehp E) by (rewrite E2f; cbn [ehp env_setbl env_setcur env_setm]; unfold Ef, env_call; rewrite ehp_setls, ehp_setzs; reflexivity).
      assert (EHLS2 : elh E2 = elh E) by (rewrite E2f; cbn [elh env_setbl env_setcur env_setm]; unfold Ef, env_call; rewrite elh_setls, elh_setzs; reflexivity).
      assert (ECW2 : ecw E2 = ecw E) by (rewrite E2f; cbn [ecw env_setbl env_setcur env_setm]; unfold Ef, env_call; rewrite ecw_setls, ecw_setzs; reflexivity).
      assert (ELB2 : elb0 E2 = elb0 E) by (rewrite E2f; cbn [elb0 env_setbl env_setcur env_setm]; unfold Ef, env_call; rewrite elb0_setls, elb0_setzs; reflexivity).
      assert (EHR2 : ehr E2 = ehr E) by (rewrite E2f; cbn [ehr env_setbl env_setcur env_setm]; unfold Ef, env_call; rewrite ehr_setls, ehr_setzs; reflexivity).
      assert (ECUR2 : ecur E2 = mo') by (rewrite E2f; reflexivity).
      assert (EBLV2 : eblv E2 (S kc) = lbx) by (rewrite E2f; rewrite eblv_setbl, Nat.eqb_refl; reflexivity).
      assert (BL2 : forall bl0, blvars_lt (s_nx ss) bl0 = true -> blrefs_lt (S kc) bl0 = true -> blden E2 bl0 = blden E bl0).
      { intros bl0 Hb Hr. rewrite E2f. rewrite blden_setbl by exact Hr. rewrite blden_setcur, !blden_setm. unfold Ef, env_call. rewrite blden_setls. apply blden_setzs. exact Hb. }
      assert (BLRS : blrefs_lt (S kc) bl = true) by (eapply blrefs_lt_mono; [exact BLR| lia]).
      assert (THs2 : forall i e, sub_get th' i = Some e -> zden E2 e = ez Es i) by (intros i e G0; rewrite ZD2; apply THs; exact G0).
      assert (TBs2 : forall kb kk, bsub_get tb kb = Some (BVar kk) -> eb E2 kk = eb Es kb) by (intros kb kk G0; rewrite E2f; rewrite eb_setbl, eb_setcur, !eb_setm; apply TBs; exact G0).
      assert (TLs2 : forall j l0, lsub_get tl' j = Some l0 -> ldenw E2 l0 = el Es j) by (intros j l0 G0; rewrite E2f; rewrite ldenw_setbl, ldenw_setcur, !ldenw_setm; apply TLs; exact G0).
      (* [comment removed for export] *)
      assert (PFf : Forall (pfact_ok CS Ef) (s_pf ss)).
      { unfold Ef, env_call. apply (Forall_pf_setls (GL AL CS F fc m0 me)). apply (Forall_pf_setzs (GL AL CS F fc m0 me) E rs (s_nx ss)); [exact WPFc| exact HP]. }
      assert (BLf : forall bl0, blvars_lt (s_nx ss) bl0 = true -> blden Ef bl0 = blden E bl0).
      { intros bl0 Hb. unfold Ef, env_call. rewrite blden_setls. apply blden_setzs. exact Hb. }
      assert (EFX : (blvars_lt (s_nx ss) blL = true /\ blrefs_lt (S kc) blL = true
                     /\ (forall b, In b (elb0 E) -> In b (blden E blL)) /\ (forall b, In b (elb0 E) -> In b (blden E2 blN)))
                    /\ blden E blL = law_list Es eff LB
                    /\ blden E2 blN = eff_list Es eff LB
                    /\ Forall (mfact_ok segs AL CS E2 m') extra
                    /\ Forall (pfact_ok CS Ef) pextra).
      { destruct eff as [|ja en|ja|]; cbn [heff_apply] in EFF.
        - injection EFF; intros <- <- <- <-. cbn [law_list eff_list].
          split; [split; [exact BLV| split; [exact BLRS| split; [exact EXTl| rewrite (BL2 bl BLV BLRS); exact EXTl]]]|].
          split; [reflexivity|]. split; [exact (BL2 bl BLV BLRS)| split; constructor].
        - injection EFF; intros <- <- <- <-. cbn [bleff_wf] in WEFF. cbn [law_list eff_list]. apply andb_prop in WEFF as [Wja Wen]. apply Pos.ltb_lt in Wja.
          cbn [eff_post] in HEP. destruct HEP as [HEP1 HEP2].
          assert (DjaF : zdenp Ef (sxe th' (EZv ja)) = ez Es ja).
          { rewrite zdenp_ok. rewrite (sxe_den Ef Es th' THs (EZv ja)); [reflexivity| |reflexivity]. cbn. destruct (sub_get th' ja) eqn:G; [reflexivity|]. exfalso. exact (BNDs ja Wja G). }
          assert (DenF : zdenp Ef (sxe th' en) = zdenp Es en).
          { apply (sxe_denp Ef Es th' THs); [eapply bridge_bound; [exact BNDs| exact Wen]| exact (eloc_enoU _ _ Wen)]. }
          assert (Dja : zdenp E2 (sxe th' (EZv ja)) = ez Es ja) by (rewrite ZP2; exact DjaF).
          assert (Den : zdenp E2 (sxe th' en) = zdenp Es en) by (rewrite ZP2; exact DenF).
          split; [split; [exact BLV| split; [exact BLRS| split; [exact EXTl| cbn [blden]; intros b Hb; right; rewrite (BL2 bl BLV BLRS); exact (EXTl b Hb)]]]|].
          split; [reflexivity|]. split; [|split].
          + cbn [blden]. rewrite Dja, Den, (BL2 bl BLV BLRS). reflexivity.
          + constructor; [|constructor]. cbn [mfact_ok]. rewrite (BL2 bl BLV BLRS), Dja, Den. exact HEP1.
          + apply Forall_app. split.
            * apply (spine_seps_ok CS Ef _ _ bl _ _ DjaF DenF). rewrite (BLf bl BLV). exact HEP1.
            * destruct (hc_obj hc) as [j|]; [|constructor].
              apply (obj_seps_ok CS Ef (s_pf ss) j _ _ _ _ PFf DjaF DenF).
              intros b k Hp. apply HEP2. unfold eprop. rewrite <- EPs. exact Hp.
        - cbn [bleff_wf] in WEFF. apply Pos.ltb_lt in WEFF.
          destruct (bl_pop (s_pf ss) (s_mf ss) (sxe th (EZv ja)) bl) as [[n bl']|] eqn:BP; [|discriminate].
          destruct (bl_pop_sound segs AL CS E m _ _ _ _ _ _ HP HM BP) as [RM _].
          pose proof (bl_pop_vars _ _ _ (s_nx ss) _ _ _ BP BLV) as BLV'.
          assert (Eja : ez Es ja = zden E (sxe th (EZv ja))).
          { rewrite (THL ja WEFF). symmetry. pose proof (EE (EZv ja)) as X. cbn [zden eloc] in X. apply X. apply Pos.ltb_lt. exact WEFF. }
          assert (BLR' : blrefs_lt (S kc) bl' = true).
          { clear - BP BLRS. revert n bl' BP. induction bl as [|b0 k0 rest IH|kv]; intros n bl' BP; cbn [bl_pop] in BP; try discriminate.
            cbn [blrefs_lt] in BLRS. destruct (expr_eqb (sxe th (EZv ja)) b0).
            - injection BP; intros <- <-. exact BLRS.
            - match type of BP with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
              destruct (bl_pop (s_pf ss) (s_mf ss) (sxe th (EZv ja)) rest) as [[n' rest']|] eqn:BP'; [|discriminate].
              match type of BP with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
              injection BP; intros <- <-. cbn [blrefs_lt]. exact (IH BLRS n' rest' eq_refl). }
          match type of EFF with (if ?c then _ else _) = _ => destruct c eqn:B0; [|discriminate] end.
          injection EFF; intros <- <- <- <-.
          pose proof (fun b => blden_ext0 E bl' b B0) as X0. pose proof (fun b => blden_ext0 E2 bl' b B0) as X2.
          cbn [law_list eff_list]. rewrite Eja. split; [split; [exact BLV'| split; [exact BLR'| split; [exact X0| rewrite <- ELB2; exact X2]]]|].
          split; [exact RM|]. split; [rewrite (BL2 bl' BLV' BLR'); exact RM| split; constructor].
        - (* [comment removed for export] *)
          injection EFF; intros <- <- <- <-. cbn [law_list eff_list eff_post] in HEP |- *.
          assert (EBN : blden E2 (LxMem.BLV (S kc)) = lbx) by (cbn [blden]; exact EBLV2).
          split; [split; [exact BLV| split; [exact BLRS| split; [exact EXTl| rewrite EBN; intros b Hb; apply HEP; apply EXTl; exact Hb]]]|].
          split; [reflexivity|]. split; [| split; constructor]. rewrite EBN. unfold Es, eblv. reflexivity. }
      destruct EFX as ((BLLV & BLLR & EXTL & EXTN) & BLL & BLN & EXTRA & PEXTRA).
      assert (LAWE : ehlaw E (hc_law hc) (blden E blL) (zden E sp) (wden E W) m m').
      { rewrite BLL, SPE, WE. unfold ehlaw. exact HLAW. }
      (* [comment removed for export] *)
      enough (POST : ms_den segs (GL AL CS F fc m0 me) E2 ssX m' = MS (rdw (rclob R (su_clob su) Es)) F (ret_pc (rgetZ R 1)) fc None m' (seg_rom segs)
                     /\ INV segs (GL AL CS F fc m0 me) E2 ssX m').
      { destruct POST as [EQ INVx]. rewrite <- EQ. apply (KONT rs rls m m' mo' lbx m' Lrs Lrls); [rewrite <- PHX; cbn [s_rs]; rewrite set_regs_length; exact L31| rewrite <- PHX; reflexivity| exact INVx]. }
      rewrite <- PHX.
      split.
      { (* [comment removed for export] *)
        unfold ms_den. cbn [g_F g_fc s_rs s_pc]. f_equal.
        - rewrite regs_den_rdw. f_equal.
          transitivity (map (rden Ef) (set_regs (s_rs ss) (map (fun rj => (fst rj, sxe th' (EZv (snd rj)))) (su_clob su)))).
          { apply map_ext. intros r0. rewrite E2f. rewrite rden_setbl, rden_setcur, !rden_setm. reflexivity. }
          assert (BASE : map (rden Ef) (s_rs ss) = R).
          { unfold R. apply map_ext_in. intros r0 Hr. unfold Ef, env_call. rewrite rden_setls. apply rden_setzs. rewrite forallb_forall in WRc. apply WRc. exact Hr. }
          assert (CL : forall rj, In rj (su_clob su) -> 1 <= fst rj <= 31 /\ (su_npP su <= snd rj)%positive /\ (snd rj < su_nallP su)%positive).
          { intros rj Hin. rewrite forallb_forall in WCLOB. specialize (WCLOB rj Hin).
            repeat match goal with G : _ && _ = true |- _ => apply andb_prop in G; destruct G end.
            repeat match goal with
              | G : Pos.leb _ _ = true |- _ => apply Pos.leb_le in G
              | G : Pos.ltb _ _ = true |- _ => apply Pos.ltb_lt in G
              | G : Z.leb _ _ = true |- _ => apply Z.leb_le in G
              | G : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in G
              | G : negb (Z.eqb _ _) = true |- _ => apply Bool.negb_true_iff in G; apply Z.eqb_neq in G
              end; lia. }
          assert (GEN : forall cl l R0, (forall rj, In rj cl -> 1 <= fst rj <= 31 /\ (su_npP su <= snd rj)%positive /\ (snd rj < su_nallP su)%positive) ->
                    length l = 31%nat -> map (rden Ef) l = R0 ->
                    map (rden Ef) (set_regs l (map (fun rj => (fst rj, sxe th' (EZv (snd rj)))) cl)) = rclob R0 cl Es).
          { induction cl as [|[r j] cl IH]; intros l R0 CL0 Hl BASE0; cbn [set_regs map rclob fst snd]; [exact BASE0|].
            apply IH.
            - intros rj Hin. apply CL0. right. exact Hin.
            - rewrite lset_length. exact Hl.
            - rewrite map_lset, BASE0. destruct (CL0 (r, j) (or_introl eq_refl)) as (Hr & Hj1 & Hj2). cbn [fst snd] in Hr, Hj1, Hj2.
              rewrite mkreg_den. rewrite (sxe_den Ef Es th' THs); [| | reflexivity].
              2:{ cbn. destruct (sub_get th' j) eqn:G; [reflexivity|]. exfalso. exact (BNDs j Hj2 G). }
              cbn [zden]. unfold rsetZ. destruct r as [|p|p]; try lia. rewrite pset_lset by (rewrite <- BASE0, map_length; lia).
              replace (Z.to_nat (Z.pos p - 1)) with (Pos.to_nat p - 1)%nat by lia. reflexivity. }
          exact (GEN (su_clob su) (s_rs ss) R CL L31 BASE).
        - (* [comment removed for export] *)
          assert (R1 : rgetZ R 1 = rden E (rd_reg ss 1)).
          { unfold rgetZ, R. rewrite pget_nth. rewrite (nth_map' (rden E) (s_rs ss) _ (RZ (ELit 0))) by lia.
            unfold rd_reg. cbn [Z.eqb]. rewrite lget_nth. reflexivity. }
          rewrite R1. destruct (rd_reg ss 1) as [j|e] eqn:RR1.
          + injection RA; intros <-. cbn [pc_den rden]. rewrite E2f. rewrite ew_setbl, ew_setcur, !ew_setm. unfold Ef, env_call. rewrite ew_setls, ew_setzs. reflexivity.
          + destruct (is_lit e) as [z|] eqn:LZ; [|discriminate]. injection RA; intros <-. cbn [pc_den rden].
            apply is_lit_den with (E := E) in LZ. rewrite zdenp_ok, LZ. symmetry. apply ret_pc_lit. }
      (* [comment removed for export] *)
      unfold INV. cbn [s_mf s_pf s_W s_same s_ref s_nm]. cbn [g_L g_CS g_m0 g_me]. unfold refm. cbn [s_ref]. rewrite EMp.
      split; [|split; [|split; [intros x Hx; reflexivity| split; [apply wmono_refl| split; [exact MI'| apply same_gone]]]]].
      - (* [comment removed for export] *)
        cbn [app]. constructor; [|constructor; [|constructor]]; [cbn [mfact_ok]| cbn [mfact_ok]| cbn [mfact_ok]|].
        + rewrite (EM2 (s_ref ss) RLT), EMc, WD2. unfold Ef, env_call. rewrite wden_setls, (wden_setzs E rs (s_nx ss) (s_W ss) WWc). exact MU.
        + rewrite (EM2 (s_ref ss) RLT), EMc. exact WM.
        + rewrite EHL2, (BL2 blL BLLV BLLR), ZP2, WD2, EMc, EMp, WEf, BLL, zdenp_ok, SPf. unfold ehlaw. exact HLAW.
        + apply install_post_Forall.
          * apply Forall_app. split.
            -- (* [comment removed for export] *)
               apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin Hsv]. rewrite E2f.
               apply (proj2 (mfact_ok_setbl segs AL CS _ (S kc) lbx m' f (mrefs_lt_mono kc (S kc) f (MRFl _ Hin) ltac:(lia)))).
               apply (proj2 (mfact_ok_setcur segs AL CS _ mo' m' f ltac:(eapply heap_survives_noheap; exact Hsv))).
               apply (proj2 (mfact_ok_setm segs AL CS _ (S kc) m' m' f (mrefs_lt_mono kc (S kc) f (MRFl _ Hin) ltac:(lia)))).
               apply (proj2 (mfact_ok_setm segs AL CS _ kc m m' f (MRFl _ Hin))).
               unfold Ef, env_call. apply (proj2 (mfact_ok_setls segs (GL AL CS F fc m0 me) rls _ (s_nl ss) m' f (MLFl _ Hin))).
               apply (mfact_ok_setzs segs (GL AL CS F fc m0 me) E rs (s_nx ss) m' f (WMFl _ Hin)). cbn [g_L g_CS].
               exact (heap_survives_sound segs AL CS E m m' (s_pf ss) (s_mf ss) blL sp W (hc_law hc) HP HM LAWE MI' HOKl EXTL f (HMl _ Hin) Hsv).
            -- constructor.
               ++ (* [comment removed for export] *)
                  cbn [mfact_ok]. unfold lx_heapkit. rewrite EHP2, ECUR2, ECW2, ELB2, EHLS2, BLN, WD2. split; [split; [exact HHP|]| split; [|exact HREST0]].
                  ** unfold Ef, env_call. rewrite wden_setls, (wden_setzs E rs (s_nx ss) ok OKV). exact HOK0.
                  ** intros b Hb. rewrite <- BLN. apply EXTN. exact Hb.
               ++ apply Forall_app. split; [exact EXTRA|]. apply Forall_app. split.
                  (* [comment removed for export] *)
                  { apply List.Forall_forall. intros g Hg. apply in_map_iff in Hg as ([j xs] & <- & Hjx). cbn [fst snd].
                  rewrite forallb_forall in WHPx. pose proof (WHPx _ Hjx) as Wxs. cbn [snd] in Wxs.
                  pose proof (QHR _ Hjx) as HR. cbn [fst snd] in HR.
                  cbn [mfact_ok]. unfold ehres. rewrite ECW2, ELB2, EHR2, (BL2 bl BLV BLRS), BLN, WD2. fold LB.
                  unfold Ef, env_call. rewrite wden_setls, (wden_setzs E rs (s_nx ss) ok OKV).
                  assert (XS : map (zdenp E2) (map (sxe th') xs) = map (zdenp Es) xs).
                  { rewrite map_map. apply map_ext_in. intros e He. rewrite forallb_forall in Wxs. pose proof (Wxs e He) as We.
                    rewrite ZP2. apply (sxe_denp Ef Es th' THs); [eapply bridge_bound; [exact BNDs| exact We]| exact (eloc_enoU _ _ We)]. }
                  rewrite XS.
                  destruct HR as [HR1 (HR2 & HR3 & _ & HR5 & HR6)]. split; [exact HR1|]. split; [exact HR2|]. split; [exact HR3|].
                  split; [exact HOK0|]. split; [exact EXTl| exact HR6]. }
                  (* [comment removed for export] *)
                  rewrite OQR. apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin _].
                  assert (HinM : In f (s_mf ss) /\ exists k ok' sh, f = MOpq k ok' sh /\ In k (su_oreq su)).
                  { clear - OQR Hin. revert oql OQR Hin. unfold opq_required. induction (su_oreq su) as [|k0 ks IH]; intros oql OQR Hin.
                    - cbn in OQR. injection OQR; intros <-. destruct Hin.
                    - cbn [fold_right] in OQR.
                      match type of OQR with (match ?acc with _ => _ end) = _ => destruct acc as [l0|] eqn:R0; [|discriminate] end.
                      destruct (opq_find (s_mf ss) k0) as [g|] eqn:Fg; [|discriminate]. injection OQR; intros <-.
                      destruct Hin as [<-|Hin].
                      + destruct (opq_find_In _ _ _ Fg) as (ok' & sh & -> & Hg). split; [exact Hg| exists k0, ok', sh; split; [reflexivity| left; reflexivity]].
                      + destruct (IH l0 eq_refl Hin) as [A (k & ok' & sh & B & Ck)]. split; [exact A| exists k, ok', sh; split; [exact B| right; exact Ck]]. }
                  destruct HinM as [HinM (k & ok' & sh & -> & Hk)]. rewrite E2f.
                  apply (proj2 (mfact_ok_setbl segs AL CS _ (S kc) lbx m' (MOpq k ok' sh) eq_refl)).
                  apply (proj2 (mfact_ok_setcur segs AL CS _ mo' m' (MOpq k ok' sh) eq_refl)).
                  apply (proj2 (mfact_ok_setm segs AL CS _ (S kc) m' m' (MOpq k ok' sh) eq_refl)).
                  apply (proj2 (mfact_ok_setm segs AL CS _ kc m m' (MOpq k ok' sh) eq_refl)).
                  unfold Ef, env_call. apply (proj2 (mfact_ok_setls segs (GL AL CS F fc m0 me) rls _ (s_nl ss) m' (MOpq k ok' sh) eq_refl)).
                  apply (mfact_ok_setzs segs (GL AL CS F fc m0 me) E rs (s_nx ss) m' _ (WMFl _ HinM)). cbn [g_L g_CS mfact_ok].
                  pose proof (HMl _ HinM) as X. cbn [mfact_ok] in X. destruct X as [_ LAW].
                  split; [|exact LAW]. unfold eo. rewrite EO. apply QOQ. exact Hk.
          * apply List.Forall_forall. intros g Hg. apply in_map_iff in Hg as (f & <- & Hf).
            rewrite List.Forall_forall in QMF. rewrite forallb_forall in WMPOSTx.
            apply (sxm_ok _ Es th' tb tl' THs2 TBs2 TLs2 EL2); [| exact (QMF _ Hf)].
            eapply (bridge_m th' tb tl' _ _ _ true); [exact BNDs| rewrite forallb_forall in PBOpostX; exact (PBOpostX _ Hf)| exact LBNDs| exact (WMPOSTx _ Hf)].
      - (* [comment removed for export] *) rewrite E2f. apply Forall_pf_setbl, Forall_pf_setcur, Forall_pf_setm, Forall_pf_setm. apply fold_pf_add_Forall; [exact PFf|].
        apply Forall_app. split.
        + (* [comment removed for export] *)
          apply List.Forall_forall. intros g Hg. apply in_flat_map in Hg as (f & Hf & Hg).
          rewrite List.Forall_forall in PEXTRA. pose proof (norm_pf_ok (GL AL CS F fc m0 me) _ _ (PEXTRA _ Hf)) as X. cbn [g_CS] in X.
          rewrite List.Forall_forall in X. apply X. exact Hg.
        + apply List.Forall_forall. intros g Hg. apply in_flat_map in Hg as (f & Hf & Hg).
          rewrite List.Forall_forall in QPF. rewrite forallb_forall in WPOSTx.
          assert (PF : pfact_ok CS Ef (sxp th' f)).
          { apply (sxp_ok _ Es th' THs EPs); [| exact (QPF _ Hf)]. eapply bridge_p; [exact BNDs| exact (WPOSTx _ Hf)]. }
          pose proof (norm_pf_ok (GL AL CS F fc m0 me) _ _ PF) as X. cbn [g_CS] in X. rewrite List.Forall_forall in X. apply X. exact Hg. }
    (* [comment removed for export] *)
    assert (EPRE : eff_pre E' (hc_eff hc) LB).
    { unfold sum_postH in PH1. rewrite HF in PH1. cbv beta iota in PH1.
      revert PH1 WEFF1. destruct (hc_eff hc) as [|ja en|ja|]; intros PH1 WEFF1; cbn [eff_pre]; [exact I| exact I| |exact I].
      cbn [heff_apply] in PH1. cbn [bleff_wf] in WEFF1. apply Pos.ltb_lt in WEFF1.
      destruct (bl_pop (s_pf ss) (s_mf ss) (sxe th (EZv ja)) bl) as [[n bl']|] eqn:BP; [|discriminate].
      destruct (bl_pop_sound segs AL CS E m _ _ _ _ _ _ HP HM BP) as [_ IN].
      exists (zden E n). unfold LB. rewrite <- (THL ja WEFF1). exact IN. }
    apply EV.
    - exact EXTl.
    - exact HHP0.
    - exact EPRE.
    - exact (GENK (su_post su) (su_mpost su) (hc_eff hc) (hc_hpost hc) ssA WMPOST WPOST WEFF1 WHP1 PBOpost PH1 KONT1).
    - revert ALT WALT KONT2. destruct (hc_alt hc) as [[[post2 mpost2] eff2]|]; intros ALT WALT KONT2; [|exact I].
      destruct ALT as (ss2 & -> & PH2).
      apply andb_prop in WALT as [WALT PBO2]. apply andb_prop in WALT as [WALT WEFF2]. apply andb_prop in WALT as [WMPOST2 WPOST2].
      exact (GENK post2 mpost2 eff2 [] ss2 WMPOST2 WPOST2 WEFF2 eq_refl PBO2 PH2 KONT2).
  Qed.

  (* [comment removed for export] *)

  Lemma carve_chunk_ok : forall CS' E mm a n f, mfact_ok segs AL CS' E mm f -> Forall (mfact_ok segs AL CS' E mm) (carve_chunk a n f).
  Proof.
    intros CS' E mm a n f Hf. unfold carve_chunk.
    assert (ONE : Forall (mfact_ok segs AL CS' E mm) [f]) by (constructor; [exact Hf| constructor]).
    destruct f as [b cs|b cs|b n' k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try exact ONE.
    destruct (ediff_lit a b) as [off|] eqn:ED; [|exact ONE].
    match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:CND; [|exact ONE] end.
    destruct (take_cellsx cs off) as [[pre rest]|] eqn:T1; [|exact ONE].
    destruct (take_cellsx rest n) as [[mid post]|] eqn:T2; [|exact ONE].
    apply ediff_lit_den with (E := E) in ED.
    cbn in Hf. rewrite zdenp_ok in Hf.
    destruct (take_cellsx_ok E cs off pre rest T1 (proj1 (proj1 Hf))) as (WF1 & BY1 & L1).
    assert (WFR : cells_wf (csden E rest)) by (unfold csden in WF1 |- *; rewrite map_app, cells_wf_app in WF1; exact (proj2 WF1)).
    destruct (take_cellsx_ok E rest n mid post T2 WFR) as (WF2 & BY2 & L2).
    assert (Hf' : rw_cells segs mm (zden E b) (csden E pre ++ csden E mid ++ csden E post)).
    { eapply rw_cells_reshape; [exact Hf| |]; unfold csden in WF1, WF2, BY1, BY2 |- *; rewrite !map_app in WF1, WF2, BY1, BY2.
      - rewrite cells_wf_app in WF1. rewrite cells_wf_app. split; [exact (proj1 WF1)| exact WF2].
      - rewrite <- BY1, !cells_bytes_app, <- cells_bytes_app, BY2. reflexivity. }
    clear Hf. rename Hf' into Hf.
    apply rw_cells_split3 in Hf as (H1 & H2 & H3). fold (csden E pre) in H1, H2, H3. fold (csden E mid) in H2, H3. fold (csden E post) in H3.
    rewrite !csden_size in H2. rewrite !csden_size in H3.
    replace (zden E b + Z.of_nat (N.to_nat (cells_sizeN pre))) with (zden E a) in H2, H3 by lia.
    replace (zden E a + Z.of_nat (N.to_nat (cells_sizeN mid))) with (zden E (eadd a (ELit n))) in H3 by (rewrite eadd_den; cbn [zden]; lia).
    apply Forall_app. split.
    - destruct pre; [apply List.Forall_nil| apply List.Forall_cons; [cbn; rewrite zdenp_ok; exact H1| apply List.Forall_nil]].
    - apply List.Forall_cons; [cbn; rewrite zdenp_ok; exact H2|].
      destruct post; [apply List.Forall_nil| apply List.Forall_cons; [cbn; rewrite zdenp_ok; exact H3| apply List.Forall_nil]].
  Qed.

  Lemma carve_mf_ok : forall CS' E mm cuts mf, Forall (mfact_ok segs AL CS' E mm) mf -> Forall (mfact_ok segs AL CS' E mm) (carve_mf mf cuts).
  Proof.
    intros CS' E mm cuts. induction cuts as [|[a n] cuts IH]; intros mf H; cbn; [exact H|].
    apply IH. apply List.Forall_forall. intros f Hf. apply in_flat_map in Hf as (g & Hg & Hfg).
    rewrite List.Forall_forall in H. pose proof (carve_chunk_ok CS' E mm a n g (H g Hg)) as X. rewrite List.Forall_forall in X. apply X. exact Hfg.
  Qed.

  Theorem apply_summary_soundP_at : forall su, summary_validP segs AL GS OPS LAWS PROPS su CS -> summary_okP_at su.
  Proof.
    intros su V F fc m0 me C genv LB0 HPd CWd LH HRSd TGT E ss m [GV [EO [_ [HPFE [HBKE _]]]]] CFG Hlen WF HI.
    unfold apply_summary.
    set (ss1 := set_mf ss (carve_mf (s_mf ss) (su_cuts C genv su ss ++ tag_cuts su (s_mf ss)))).
    assert (GEN : forall res, (if ss_wf C ss1 && forallb (evars_lt (s_nx ss1)) genv then apply_summary0 C genv su ss1 else SumFail 54) = res ->
              match res with SumFail _ => True | _ =>
              ss_wf C ss1 = true /\ forallb (evars_lt (s_nx ss1)) genv = true /\ INV segs (GL AL CS F fc m0 me) E ss1 m /\ apply_summary0 C genv su ss1 = res end).
    { intros res H. destruct (ss_wf C ss1 && forallb (evars_lt (s_nx ss1)) genv) eqn:WF1; [|subst res; exact I]. apply andb_prop in WF1 as [WF1 GWF].
      assert (HI1 : INV segs (GL AL CS F fc m0 me) E ss1 m).
      { destruct HI as (HM & HP & REST). split; [|split; [exact HP| exact REST]]. unfold ss1, set_mf. cbn [s_mf]. apply carve_mf_ok. exact HM. }
      destruct res; [| | |exact I]; (split; [exact WF1| split; [exact GWF| split; [exact HI1| exact H]]]). }
    intros [| |oss2] k kl ss' AP; cbn [sum_answer] in AP; destruct (GEN _ AP) as (WF1 & GWF & HI1 & AP0);
      pose proof (apply_summary0_sound su F fc m0 me C genv E ss1 m V GV EO HPFE HBKE GWF CFG Hlen WF1 HI1) as X; rewrite AP0 in X; [exact X| exact X| destruct X].
  Qed.
End Main.
End LXH.

(* [comment removed for export] *)
Definition summary_okP (segs : list Segment) (AL : asan_layout) (GS : list Z) (OPS : list (mem -> Prop))
    (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)) (PROPS : list (list Z -> Prop)) (CS : Z -> Prop) (su : summary) : Prop :=
  forall lxHT : lx_hints, @summary_okP_at lxHT segs AL GS OPS LAWS PROPS CS su.
Theorem apply_summary_soundP : forall segs AL GS OPS LAWS PROPS CS su, summary_validP segs AL GS OPS LAWS PROPS su CS -> summary_okP segs AL GS OPS LAWS PROPS CS su.
Proof. intros segs AL GS OPS LAWS PROPS CS su V lxHT. apply apply_summary_soundP_at. exact V. Qed.

(* [comment removed for export] *)
Definition summary_okL (segs : list Segment) (AL : asan_layout) (GS : list Z) (OPS : list (mem -> Prop))
    (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)) (CS : Z -> Prop) (su : summary) : Prop :=
  forall PROPS, summary_okP segs AL GS OPS LAWS PROPS CS su.
Theorem apply_summary_soundL : forall segs AL GS OPS LAWS CS su, summary_validL segs AL GS OPS LAWS su CS -> summary_okL segs AL GS OPS LAWS CS su.
Proof. intros segs AL GS OPS LAWS CS su V PROPS. apply apply_summary_soundP. apply V. Qed.
Lemma summary_okL_P : forall segs AL GS OPS LAWS PROPS CS su, summary_okL segs AL GS OPS LAWS CS su -> summary_okP segs AL GS OPS LAWS PROPS CS su.
Proof. intros segs AL GS OPS LAWS PROPS CS su H. apply H. Qed.
(* [comment removed for export] *)
Definition summary_okO (segs : list Segment) (AL : asan_layout) (GS : list Z) (OPS : list (mem -> Prop)) (CS : Z -> Prop) (su : summary) : Prop :=
  forall LAWS, summary_okL segs AL GS OPS LAWS CS su.
Theorem apply_summary_soundO : forall segs AL GS OPS CS su, summary_validO segs AL GS OPS su CS -> summary_okO segs AL GS OPS CS su.
Proof. intros segs AL GS OPS CS su V LAWS. apply apply_summary_soundL. apply V. Qed.
Lemma summary_okO_P : forall segs AL GS OPS LAWS PROPS CS su, summary_okO segs AL GS OPS CS su -> summary_okP segs AL GS OPS LAWS PROPS CS su.
Proof. intros segs AL GS OPS LAWS PROPS CS su H. apply H. Qed.
(* [comment removed for export] *)
Lemma summary_okO_L : forall segs AL GS OPS LAWS CS su, summary_okO segs AL GS OPS CS su -> summary_okL segs AL GS OPS LAWS CS su.
Proof. intros segs AL GS OPS LAWS CS su H. apply H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition summary_okG (segs : list Segment) (AL : asan_layout) (GS : list Z) (su : summary) : Prop :=
  forall OPS CS, summary_okO segs AL GS OPS CS su.
Theorem apply_summary_soundG : forall segs AL GS su, summary_validG segs AL GS su -> summary_okG segs AL GS su.
Proof. intros segs AL GS su V OPS CS. apply apply_summary_soundO. apply summary_validG_O. exact V. Qed.
Lemma summary_okG_L : forall segs AL GS OPS LAWS CS su, summary_okG segs AL GS su -> summary_okL segs AL GS OPS LAWS CS su.
Proof. intros segs AL GS OPS LAWS CS su H. apply H. Qed.
Lemma summary_okG_P : forall segs AL GS OPS LAWS PROPS CS su, summary_okG segs AL GS su -> summary_okP segs AL GS OPS LAWS PROPS CS su.
Proof. intros segs AL GS OPS LAWS PROPS CS su H. apply H. Qed.
Definition summary_ok (segs : list Segment) (AL : asan_layout) (su : summary) : Prop := summary_okG segs AL [] su.
Theorem apply_summary_sound : forall segs AL su, summary_valid segs AL su -> summary_ok segs AL su.
Proof. intros segs AL su. apply apply_summary_soundG. Qed.

(* [comment removed for export] *)
Definition summary_okMR (segs : list Segment) (AL : asan_layout) (GS : list Z) (OPS : list (mem -> Prop))
    (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)) (PROPS : list (list Z -> Prop))
    (LB0 : list (Z * Z)) (HP : list (Z * Z) -> mem -> Model -> Prop) (CW : list (Z * Z) -> Z -> Prop)
    (LH : list (list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop)) (HRS : lx_hress) (TGT : Model -> machine_state -> Prop)
    (CS : Z -> Prop) (su : summary) : Prop :=
  forall (lxHT : lx_hints) F fc m0 me C genv, @summary_at lxHT segs (GL AL CS F fc m0 me) C genv GS OPS LAWS PROPS LB0 HP CW LH HRS TGT su.
(* [comment removed for export] *)
Definition summary_okM (segs : list Segment) (AL : asan_layout) (GS : list Z) (OPS : list (mem -> Prop))
    (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)) (PROPS : list (list Z -> Prop))
    (LB0 : list (Z * Z)) (HP : list (Z * Z) -> mem -> Model -> Prop) (CW : list (Z * Z) -> Z -> Prop)
    (LH : list (list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop)) (TGT : Model -> machine_state -> Prop)
    (CS : Z -> Prop) (su : summary) : Prop :=
  summary_okMR segs AL GS OPS LAWS PROPS LB0 HP CW LH [] TGT CS su.
Lemma summary_okP_MR : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su,
  summary_okP segs AL GS OPS LAWS PROPS CS su -> summary_okMR segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su.
Proof. intros * H lxHT F fc m0 me C genv. apply H. Qed.
Lemma summary_okP_M : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su,
  summary_okP segs AL GS OPS LAWS PROPS CS su -> summary_okM segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su.
Proof. intros * H lxHT F fc m0 me C genv. apply H. Qed.
Lemma summary_okL_MR : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su,
  summary_okL segs AL GS OPS LAWS CS su -> summary_okMR segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su.
Proof. intros * H. apply summary_okP_MR, summary_okL_P, H. Qed.
Lemma summary_okO_MR : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su,
  summary_okO segs AL GS OPS CS su -> summary_okMR segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su.
Proof. intros * H. apply summary_okP_MR, summary_okO_P, H. Qed.
Lemma summary_okG_MR : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su,
  summary_okG segs AL GS su -> summary_okMR segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su.
Proof. intros * H. apply summary_okP_MR, summary_okG_P, H. Qed.

Lemma summary_okL_M : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su,
  summary_okL segs AL GS OPS LAWS CS su -> summary_okM segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su.
Proof. intros * H. apply summary_okP_M, summary_okL_P, H. Qed.
Lemma summary_okO_M : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su,
  summary_okO segs AL GS OPS CS su -> summary_okM segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su.
Proof. intros * H. apply summary_okP_M, summary_okO_P, H. Qed.
Lemma summary_okG_M : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su,
  summary_okG segs AL GS su -> summary_okM segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su.
Proof. intros * H. apply summary_okP_M, summary_okG_P, H. Qed.

Section LXH2a.
Context {lxHT : lx_hints}.
(* [comment removed for export] *)
Lemma apply_summary0_heapM : forall C genv su ss hc, su_heap su = Some hc ->
  match apply_summary0 C genv su ss with SumOk _ _ _ | SumOkL _ _ _ => False | _ => True end.
Proof.
  intros C genv su ss hc HEAP. unfold apply_summary0.
  destruct (negb (su_wf su)); [exact I|].
  destruct (negb (Bool.eqb (su_acc su) (acc_mode C))); [exact I|].
  destruct (negb (Nat.eqb (length (s_rs ss)) 31)); [exact I|].
  destruct (negb (forallb (mflvars_lt (s_nl ss)) (s_mf ss))); [exact I|].
  destruct (s_pc ss) as [pc|r]; [|exact I].
  destruct (negb (Z.eqb pc (su_pc su))); [exact I|].
  match goal with |- match (match ?x with _ => _ end) with _ => _ end => destruct x as [ra|]; [|exact I] end.
  destruct (sum_match C genv su ss) as [[[th tb] tl] code]. destruct code; try exact I.
  destruct (negb (forallb (post_blobs_ok tb) (su_req su ++ su_mpost su))); [exact I|].
  destruct (opq_required (s_mf ss) (su_oreq su)); [|exact I].
  rewrite HEAP.
  destruct (Nat.ltb (s_ref ss) (s_nm ss) && Nat.ltb 0 (s_nm ss) && forallb (mrefs_lt (s_nm ss)) (s_mf ss)); [|exact I].
  destruct (negb (hc_wf su hc tb)); [exact I|].
  destruct (sum_postH su hc ss th tb tl ra (su_post su) (su_mpost su) (hc_eff hc)); [|exact I].
  destruct (hc_alt hc) as [[[p2 m2] e2]|]; [|exact I].
  destruct e2; try exact I; destruct (sum_postH su hc ss th tb tl ra p2 m2 _); exact I.
Qed.
End LXH2a.

(* [comment removed for export] *)
Theorem apply_summary_soundMR : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su hc,
  summary_validHR segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT su hc CS -> summary_okMR segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su.
Proof.
  intros segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS su hc V lxHT2 F fc m0 me C genv E ss m (GV & EO & (ELB & EHP & ECW & ELH & EHR) & HPFE & HBKE & HLOK) CFG Hlen WF HI.
  unfold apply_summary.
  set (ss1 := set_mf ss (carve_mf (s_mf ss) (su_cuts C genv su ss ++ tag_cuts su (s_mf ss)))).
  assert (GEN : forall res, (if ss_wf C ss1 && forallb (evars_lt (s_nx ss1)) genv then apply_summary0 C genv su ss1 else SumFail 54) = res ->
            match res with SumFail _ => True | _ =>
            ss_wf C ss1 = true /\ forallb (evars_lt (s_nx ss1)) genv = true /\ INV segs (GL AL CS F fc m0 me) E ss1 m /\ apply_summary0 C genv su ss1 = res end).
  { intros res H. destruct (ss_wf C ss1 && forallb (evars_lt (s_nx ss1)) genv) eqn:WF1; [|subst res; exact I]. apply andb_prop in WF1 as [WF1 GWF].
    assert (HI1 : INV segs (GL AL CS F fc m0 me) E ss1 m).
    { destruct HI as (HM & HPf & REST). split; [|split; [exact HPf| exact REST]]. unfold ss1, set_mf. cbn [s_mf]. apply carve_mf_ok. exact HM. }
    destruct res; [| | |exact I]; (split; [exact WF1| split; [exact GWF| split; [exact HI1| exact H]]]). }
  pose proof (apply_summary0_heapM C genv su ss1 hc (proj1 V)) as KIND.
  intros [| |oss2] k kl ss' AP; cbn [sum_answer] in AP; destruct (GEN _ AP) as (WF1 & GWF & HI1 & AP0); rewrite AP0 in KIND; [destruct KIND| destruct KIND|].
  subst LB0 HP CW LH HRS. intros KONT1 KONT2.
  exact (apply_summary0_soundH segs AL GS OPS LAWS PROPS CS su hc F fc m0 me C genv E ss1 m TGT V GV EO HLOK GWF CFG Hlen WF1 HI1 k kl ss' oss2 AP0 KONT1 KONT2).
Qed.
(* [comment removed for export] *)
Theorem apply_summary_soundM : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su hc,
  summary_validH segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT su hc CS -> summary_okM segs AL GS OPS LAWS PROPS LB0 HP CW LH TGT CS su.
Proof. intros *. apply apply_summary_soundMR. Qed.

(* [comment removed for export] *)
Section LXH2.
Context {lxHT : lx_hints}.

(* [comment removed for export] *)
Lemma sums_ok_atM : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS F fc m0 me C genv l,
  Forall (summary_okMR segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS) l -> Forall (summary_at segs (GL AL CS F fc m0 me) C genv GS OPS LAWS PROPS LB0 HP CW LH HRS TGT) l.
Proof. intros * H. eapply Forall_impl; [|exact H]. intros su Hs. apply Hs. Qed.
Lemma sums_ok_atP : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS F fc m0 me C genv l,
  Forall (summary_okP segs AL GS OPS LAWS PROPS CS) l -> Forall (summary_at segs (GL AL CS F fc m0 me) C genv GS OPS LAWS PROPS LB0 HP CW LH HRS TGT) l.
Proof. intros * H. eapply Forall_impl; [|exact H]. intros su Hs. apply Hs. Qed.
Lemma sums_ok_atL : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS F fc m0 me C genv l,
  Forall (summary_okL segs AL GS OPS LAWS CS) l -> Forall (summary_at segs (GL AL CS F fc m0 me) C genv GS OPS LAWS PROPS LB0 HP CW LH HRS TGT) l.
Proof. intros * H. eapply Forall_impl; [|exact H]. intros su Hs. apply Hs. Qed.
Lemma sums_ok_atO : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS F fc m0 me C genv l,
  Forall (summary_okO segs AL GS OPS CS) l -> Forall (summary_at segs (GL AL CS F fc m0 me) C genv GS OPS LAWS PROPS LB0 HP CW LH HRS TGT) l.
Proof. intros * H. eapply Forall_impl; [|exact H]. intros su Hs. apply Hs. Qed.
Lemma sums_ok_at : forall segs AL GS OPS LAWS PROPS LB0 HP CW LH HRS TGT CS F fc m0 me C genv l,
  Forall (summary_okG segs AL GS) l -> Forall (summary_at segs (GL AL CS F fc m0 me) C genv GS OPS LAWS PROPS LB0 HP CW LH HRS TGT) l.
Proof. intros * H. eapply Forall_impl; [|exact H]. intros su Hs. apply Hs. Qed.
Lemma sums_ok_at0 : forall segs AL OPS LAWS PROPS LB0 HP CW LH HRS TGT CS F fc m0 me C genv l,
  Forall (summary_ok segs AL) l -> Forall (summary_at segs (GL AL CS F fc m0 me) C genv [] OPS LAWS PROPS LB0 HP CW LH HRS TGT) l.
Proof. intros * H. eapply Forall_impl; [|exact H]. intros su Hs. apply Hs. Qed.

(* [comment removed for export] *)
Lemma evt_evtA_all : forall segs AL (CS : Z -> Prop) Q ms,
  (forall x, CS x) -> evt segs Q ms -> evtA segs AL CS Q ms.
Proof.
  intros segs AL CS Q ms HCS (ms' & ST & HQ). exists ms'. split; [|exact HQ]. clear HQ.
  induction ST as [ms0|ms0 ms1 ms2 [SV STP] ST IH]; [constructor|].
  eapply mstepsA_cons; [|exact IH]. split; [exact SV|].
  unfold RiscvSemantics.step in STP.
  destruct (step_accesses segs ms0) as [[ms1' acc]| |]; cbn in STP; try discriminate.
  injection STP; intros ->. exists acc. split; [reflexivity|]. intros z _. left. apply HCS.
Qed.

(* [comment removed for export] *)
Lemma lx_w64u : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. exact w64_of_unsigned. Qed.
Lemma lx_urange : forall w : word, 0 <= bv_unsigned w /\ bv_unsigned w <= two64 - 1.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. unfold two64. cbn in R |- *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EntryLinks.
  Variable segs : list Segment.
  Variable G : gl.
  Variable C : lxcfg.
  Variable E : env.
  Variable pf : list pfact.
  Hypothesis CFG : cfg_ok G C E.
  Hypothesis HP : Forall (pfact_ok (g_CS G) E) pf.
  Hypothesis HPF : hp_frame segs (ehp E) (ecw E).

  (* [comment removed for export] *)
  Definition link_ok (lk : elink) (m1 m2 : mem) : Prop :=
    match lk with
    | ELaw l X => elaw E l (wden E X) m1 m2
    | EMunch W => munch (wden E W) m1 m2 /\ wmono segs m1 m2 /\ mem_inv segs m2
    end.

  (* [comment removed for export] *)
  Fixpoint chain_ok (ch : list (elink * list mfact)) (srcs : list mem) (m : mem) {struct ch} : Prop :=
    match ch, srcs with
    | [], [] => True
    | (lk, mfk) :: ch', mk :: srcs' =>
        Forall (mfact_ok segs (g_L G) (g_CS G) E mk) mfk
        /\ link_ok lk mk (match srcs' with [] => m | mk' :: _ => mk' end)
        /\ chain_ok ch' srcs' m
    | _, _ => False
    end.

  Let HACC : forall A, c_acc C = Some A -> ac_got A = al_got (g_L G) /\ ac_gsb A = al_gsb (g_L G) /\ cs_ok (g_L G) (g_CS G).
  Proof.
    intros A HCA. unfold cfg_ok in CFG. rewrite HCA in CFG. destruct CFG as (C1 & _ & _ & _ & _ & G1 & G2).
    split; [exact G1| split; [exact G2| exact C1]].
  Qed.
  Let HSB : forall A, c_acc C = Some A -> zdenp E (ac_sb A) = al_sb (g_L G).
  Proof. intros A HCA. unfold cfg_ok in CFG. rewrite HCA in CFG. destruct CFG as (_ & _ & S1 & _). exact S1. Qed.

  Lemma link_ivls_den : forall X, wden E (link_ivls X) = wden E X.
  Proof.
    intros X. unfold wden, link_ivls. rewrite map_map. apply map_ext. intros [l h]. cbn [fst snd]. rewrite !zdenp_ok, !enorm_den. reflexivity.
  Qed.

  Lemma link_filter_ok : forall lk m1 m2 mf,
    Forall (mfact_ok segs (g_L G) (g_CS G) E m1) mf -> link_ok lk m1 m2 ->
    Forall (mfact_ok segs (g_L G) (g_CS G) E m2) (link_filter C pf mf lk).
  Proof.
    intros lk m1 m2 mf HM0 HL. unfold link_filter.
    set (mfN := map norm_mf mf). set (pfN := pf_nodup (flat_map norm_pf pf) ++ flat_map mf_bounds mfN).
    assert (HM : Forall (mfact_ok segs (g_L G) (g_CS G) E m1) mfN).
    { subst mfN. apply List.Forall_forall. intros f Hf. apply in_map_iff in Hf as (g & <- & Hg). apply norm_mf_ok.
      rewrite List.Forall_forall in HM0. exact (HM0 g Hg). }
    assert (HPN : Forall (pfact_ok (g_CS G) E) pfN).
    { subst pfN. apply Forall_app. split.
      - assert (ND : forall l f, In f (pf_nodup l) -> In f l).
        { induction l as [|g l IHl]; intros f Hf; cbn in Hf; [exact Hf|]. unfold pf_add in Hf at 1. fold (pf_nodup l) in Hf.
          destruct (pf_mem g (pf_nodup l)); [right; apply IHl; exact Hf|]. destruct Hf as [<-|Hf]; [left; reflexivity| right; apply IHl; exact Hf]. }
        apply List.Forall_forall. intros f Hf. apply ND in Hf. apply in_flat_map in Hf as (g & Hg & Hfg).
        rewrite List.Forall_forall in HP. pose proof (norm_pf_ok G E g (HP g Hg)) as X. rewrite List.Forall_forall in X. exact (X f Hfg).
      - clear - HM. induction HM as [|f l Hf HM IH]; [constructor|]. cbn [flat_map]. apply Forall_app. split; [|exact IH].
        eapply mf_bounds_ok. exact Hf. }
    pose proof (cranges_sound segs (g_L G) (g_CS G) E m1 pfN mfN HPN HM) as CR.
    destruct lk as [l X|W]; cbn [link_ok] in HL; cbv zeta.
    - rewrite <- (link_ivls_den X) in HL.
      apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin Hsv].
      refine (law_survives_sound segs (g_L G) (g_CS G) E C m1 m2 pfN mfN (link_ivls X) l false HPN HM HL HACC HSB _ CR _ _ _ _ f _ Hsv).
      + intros W1. eapply w_all_client_sound; [exact HPN| exact CR| exact W1].
      + intros W2. eapply all_nonempty_sound; [exact HPN| exact W2].
      + rewrite List.Forall_forall in HM. exact (HM f Hin).
    - destruct HL as (MU & WM & MI). rewrite <- (link_ivls_den W) in MU.
      apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin Hsv].
      apply andb_prop in Hsv as [_ Hsv].
      refine (mf_survives_call_sound segs (g_L G) (g_CS G) E C m1 m2 pfN (link_ivls W) HPN HACC HSB _ CR MU WM MI HPF _ _ mfN f HM _ _ _ Hsv).
      + intros W1. eapply w_all_client_sound; [exact HPN| exact CR| exact W1].
      + intros W2. eapply all_nonempty_sound; [exact HPN| exact W2].
      + rewrite List.Forall_forall in HM. exact (HM f Hin).
  Qed.

  Lemma links_filter_ok : forall ch srcs m acc,
    chain_ok ch srcs m ->
    Forall (mfact_ok segs (g_L G) (g_CS G) E (match srcs with [] => m | mk :: _ => mk end)) acc ->
    Forall (mfact_ok segs (g_L G) (g_CS G) E m) (links_filter C pf ch acc).
  Proof.
    induction ch as [|[lk mfk] ch IH]; intros srcs m acc CH HA; destruct srcs as [|mk srcs]; cbn [chain_ok] in CH; try contradiction.
    - exact HA.
    - destruct CH as (HMk & HL & CH'). cbn [links_filter]. apply (IH srcs m); [exact CH'|].
      apply (link_filter_ok lk mk); [| exact HL]. apply Forall_app. split; [exact HMk| exact HA].
  Qed.

  Lemma is_tagb_any : forall f m m', is_tagb f = true -> mfact_ok segs (g_L G) (g_CS G) E m f -> mfact_ok segs (g_L G) (g_CS G) E m' f.
  Proof. intros f m m' H Hf. destruct f; cbn [is_tagb] in H; try discriminate; exact Hf. Qed.

  (* [comment removed for export] *)
  Lemma entry_links_ok : forall ch srcs m mf,
    Forall (mfact_ok segs (g_L G) (g_CS G) E m) mf -> chain_ok ch srcs m ->
    Forall (mfact_ok segs (g_L G) (g_CS G) E m) (links_entry C pf ch mf).
  Proof.
    intros ch srcs m mf HM CH. unfold links_entry. apply install_post_Forall; [| exact HM].
    apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin _]. revert f Hin. apply List.Forall_forall.
    apply (links_filter_ok ch srcs m); [exact CH|].
    apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin Ht]. rewrite List.Forall_forall in HM.
    apply (is_tagb_any f m); [exact Ht| exact (HM f Hin)].
  Qed.
End EntryLinks.

End LXH2.
