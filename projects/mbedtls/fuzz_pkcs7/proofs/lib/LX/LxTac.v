(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr AEvt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxSum LxStep LxRun LxDenot LxSoundExpr LxSoundRun LxSoundSum.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxPost.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition lx_seen (P : Prop) : Prop := P.
(* [comment removed for export] *)
Definition lx_hidden (P : Prop) : Prop := P.
(* [comment removed for export] *)
Definition lx_dup (P : Prop) : Prop := P.

(* [comment removed for export] *)
Class LxImg (segs : list Segment) (Ly : asan_layout) := {
  li_lo : Z; li_hi : Z; li_got : Z; li_gsb : Z;
  li_ok : li_lo = al_img_lo Ly /\ li_hi = al_img_hi Ly /\ li_got = al_got Ly /\ li_gsb = al_gsb Ly }.

Lemma li_abase_got {segs Ly} {LI : LxImg segs Ly} : forall m, abase segs Ly m -> ro_cells segs m li_got [C8 (Z_to_bv 64 li_gsb)].
Proof. intros m H. destruct li_ok as (_ & _ & E1 & E2). rewrite E1, E2. exact (abase_got segs Ly m H). Qed.
Lemma li_abase_gsb {segs Ly} {LI : LxImg segs Ly} : forall m, abase segs Ly m -> ro_cells segs m li_gsb [C8 (Z_to_bv 64 (al_sb Ly))].
Proof. intros m H. destruct li_ok as (_ & _ & E1 & E2). rewrite E2. exact (abase_gsb segs Ly m H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition genv_okp (segs : list Segment) (E : env) (genv : list expr) (GS : list Z) (OPS : list (mem -> Prop)) (LAWS : list (list (Z * Z) -> mem -> mem -> Prop))
    (PROPS : list (list Z -> Prop)) (LB0 : lx_blks) (HP : lx_hpred) (CW : lx_cwpred) (LH : lx_hlaws) (HRS : lx_hress) : Prop :=
  Forall2 (fun g v => zdenp E g = v) genv GS
  /\ ((eol E = OPS /\ elw E = LAWS /\ epr E = PROPS) /\ (elb0 E = LB0 /\ ehp E = HP /\ ecw E = CW /\ elh E = LH /\ ehr E = HRS)
      /\ (hp_frame segs (ehp E) (ecw E) /\ hp_blk (ecw E) /\ Forall (hlaw_ok segs) (elh E))).
Lemma genv_okp_ok : forall segs E genv GS OPS LAWS PROPS LB0 HP CW LH HRS,
  genv_okp segs E genv GS OPS LAWS PROPS LB0 HP CW LH HRS -> genv_ok segs genv GS OPS LAWS PROPS LB0 HP CW LH HRS E.
Proof. intros * [H HO]. unfold genv_ok. split; [|exact HO]. eapply Forall2_impl; [|exact H]. intros g v Hg. rewrite <- zdenp_ok. exact Hg. Qed.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

Lemma lx_sound_t : forall segs G C pl genv pm GS OPS LAWS PROPS LB0 HP CW LH HRS E ss ms (Q : machine_state -> Prop) t,
  Forall (summary_at segs G C genv GS OPS LAWS PROPS LB0 HP CW LH HRS (fun _ ms' => evtA segs (g_L G) (g_CS G) Q ms')) (p_sums pl) ->
  genv_okp segs E genv GS OPS LAWS PROPS LB0 HP CW LH HRS ->
  cfg_ok G C E -> length (s_rs ss) = 31%nat -> st_ok segs G E ss ms ->
  lx_runp segs C pl genv pm ss = t ->
  oblig segs G E t (fun _ ms' => evtA segs (g_L G) (g_CS G) Q ms') ->
  evtA segs (g_L G) (g_CS G) Q ms.
Proof.
  intros * SU GV CFG L ST <- OB.
  exact (lx_sound segs G C pl genv GS OPS LAWS PROPS LB0 HP CW LH HRS (fun _ ms' => evtA segs (g_L G) (g_CS G) Q ms') (tgt_law_evtA segs _ _ Q) SU pm E ss ms
           (genv_okp_ok _ _ _ _ _ _ _ _ _ _ _ _ GV) CFG L ST OB).
Qed.

Lemma lx_sound_plain_t : forall segs G C pl genv pm GS OPS LAWS PROPS LB0 HP CW LH HRS E ss ms (Q : machine_state -> Prop) t,
  Forall (summary_at segs G C genv GS OPS LAWS PROPS LB0 HP CW LH HRS (fun _ ms' => evt segs Q ms')) (p_sums pl) ->
  genv_okp segs E genv GS OPS LAWS PROPS LB0 HP CW LH HRS ->
  cfg_ok G C E -> length (s_rs ss) = 31%nat -> st_ok segs G E ss ms ->
  lx_runp segs C pl genv pm ss = t ->
  oblig segs G E t (fun _ ms' => evt segs Q ms') ->
  evt segs Q ms.
Proof.
  intros * SU GV CFG L ST <- OB.
  exact (lx_sound segs G C pl genv GS OPS LAWS PROPS LB0 HP CW LH HRS (fun _ ms' => evt segs Q ms') (tgt_law_evt segs _ _ Q) SU pm E ss ms
           (genv_okp_ok _ _ _ _ _ _ _ _ _ _ _ _ GV) CFG L ST OB).
Qed.

(* [comment removed for export] *)
Lemma lx_aevtM_evt : forall segs mo (Q : config -> Prop) ms,
  MOK mo -> evt segs (fun ms' => aevtM segs mo Q ms') ms -> aevtM segs mo Q ms.
Proof. intros segs mo Q ms MK (ms' & ST & H). eapply aevtM_msteps; eauto. Qed.
Lemma lx_sound_aevtM_t : forall segs G C pl genv pm GS OPS LAWS PROPS LB0 HP CW LH HRS E ss ms (Q : config -> Prop) t,
  Forall (summary_at segs G C genv GS OPS LAWS PROPS LB0 HP CW LH HRS (tgt_aevtM segs Q)) (p_sums pl) ->
  genv_okp segs E genv GS OPS LAWS PROPS LB0 HP CW LH HRS ->
  cfg_ok G C E -> length (s_rs ss) = 31%nat -> st_ok segs G E ss ms ->
  lx_runp segs C pl genv pm ss = t ->
  MOK (ecur E) ->
  oblig segs G E t (tgt_aevtM segs Q) ->
  aevtM segs (ecur E) Q ms.
Proof.
  intros * SU GV CFG L ST <- MK OB.
  exact (lx_sound segs G C pl genv GS OPS LAWS PROPS LB0 HP CW LH HRS (tgt_aevtM segs Q) (tgt_law_aevtM segs _ _ Q) SU pm E ss ms
           (genv_okp_ok _ _ _ _ _ _ _ _ _ _ _ _ GV) CFG L ST OB MK).
Qed.

(* [comment removed for export] *)
Lemma lx_sound_aevtA_t : forall segs G C pl genv pm GS OPS LAWS PROPS LB0 HP CW LH HRS E ss ms AI K (Q : config -> Prop) t,
  ainv_laws (g_L G) AI -> kinv_laws AI (g_CS G) K ->
  Forall (summary_at segs G C genv GS OPS LAWS PROPS LB0 HP CW LH HRS (fun _ ms' => aevtA segs K Q ms')) (p_sums pl) ->
  genv_okp segs E genv GS OPS LAWS PROPS LB0 HP CW LH HRS ->
  cfg_ok G C E -> length (s_rs ss) = 31%nat -> st_ok segs G E ss ms ->
  lx_runp segs C pl genv pm ss = t ->
  oblig segs G E t (fun _ ms' => aevtA segs K Q ms') ->
  aevtA segs K Q ms.
Proof.
  intros * AL KL SU GV CFG L ST <- OB.
  refine (lx_sound segs G C pl genv GS OPS LAWS PROPS LB0 HP CW LH HRS (fun _ ms' => aevtA segs K Q ms') _ SU pm E ss ms (genv_okp_ok _ _ _ _ _ _ _ _ _ _ _ _ GV) CFG L ST OB).
  intros mo P ms0 EV KK. eapply (aevtA_cut_evtA segs (g_L G) AI AL (g_CS G) (g_CS G) K P Q ms0 KL EV); [intros x Hx; exact Hx| exact KK].
Qed.

End LXH.


(* [comment removed for export] *)
Lemma lx_heapkit_rebase : forall segs P CW LH LB0 LB OK m mo,
  lx_heapkit segs P CW LH LB0 LB OK m mo -> lx_heapkit segs P CW LH LB LB OK m mo.
Proof.
  intros * [[HP HOK] [EXT REST]]. split; [split; [exact HP|]| split; [intros b Hb; exact Hb| exact REST]].
  eapply Forall_impl; [|exact HOK]. cbn beta. intros iv H x Hx LB' HX. apply (H x Hx LB'). intros b Hb. apply HX, EXT, Hb.
Qed.
Lemma lx_hcli_rebase : forall segs LB0 LB LAW smax a n,
  lx_hcli segs LB0 LAW smax a n -> (forall b, In b LB0 -> In b LB) -> lx_hcli segs LB LAW smax a n.
Proof. intros * H EXT LB' sp X m1 m2 x HX. apply H. intros b Hb. apply HX, EXT, Hb. Qed.
Lemma lx_hopq_rebase : forall LB0 LB LAW P,
  lx_hopq LB0 LAW P -> (forall b, In b LB0 -> In b LB) -> lx_hopq LB LAW P.
Proof. intros * H EXT LB' sp X m1 m2 HX. apply H. intros b Hb. apply HX, EXT, Hb. Qed.
(* [comment removed for export] *)
Definition lx_fprop (PR : list (list Z -> Prop)) (j : nat) (vs : list Z) : Prop := nth j PR (fun _ => True) vs.

(* [comment removed for export] *)
Definition lx_link (LAW : list (Z * Z) -> mem -> mem -> Prop) (X : list (Z * Z)) (m1 m2 : mem) : Prop := LAW X m1 m2.
Definition lx_mlink (segs : list Segment) (W : list (Z * Z)) (m1 m2 : mem) : Prop := munch W m1 m2 /\ wmono segs m1 m2 /\ mem_inv segs m2.

(* [comment removed for export] *)
Ltac lx_incl_tac := let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; repeat first [ exact Hb | apply List.in_cons ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac lx_is_lit z := lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
(* [comment removed for export] *)
Ltac lx_is_klit z := lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac | Z.pow (Zpos _) (Zpos _) => idtac end.

Ltac lx_app1 l x :=
  lazymatch l with
  | nil => constr:(cons x nil)
  | cons ?y ?l' => let r := lx_app1 l' x in constr:(cons y r)
  end.

Ltac lx_mem x l :=
  lazymatch l with
  | nil => constr:(false)
  | cons x _ => constr:(true)
  | cons _ ?l' => lx_mem x l'
  end.

Ltac lx_idx x l :=
  lazymatch l with
  | cons x _ => constr:(xH)
  | cons _ ?l' => let k := lx_idx x l' in eval cbv in (Pos.succ k)
  | nil => fail 0 "lx: atom not collected:" x
  end.

Ltac lx_len l := eval cbv in (Pos.of_nat (S (length l))).

(* [comment removed for export] *)
Ltac lx_getO := lazymatch goal with o := ?v : list (mem -> Prop) |- _ => v end.
(* [comment removed for export] *)
Ltac lx_getLW := lazymatch goal with o := ?v : list (list (Z * Z) -> mem -> mem -> Prop) |- _ => v end.
(* [comment removed for export] *)
Ltac lx_getLH := lazymatch goal with o := ?v : list (list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop) |- _ => v end.
Ltac lx_oidx P l :=
  lazymatch l with
  | cons P _ => constr:(O)
  | cons _ ?l' => let k := lx_oidx P l' in constr:(S k)
  | nil => fail 0 "lx: opaque predicate not in the run's OPS list:" P
  end.
(* [comment removed for export] *)
Ltac lx_snoc l x :=
  lazymatch l with
  | nil => constr:(cons x nil)
  | cons ?y ?l' => let r := lx_snoc l' x in constr:(cons y r)
  end.
Ltac lx_add_ops m :=
  repeat match goal with
  | H : lx_opq _ _ _ ?P _ _ m |- _ =>
      let l := lx_getO in
      lazymatch lx_mem P l with
      | false => lazymatch goal with o := _ : list (mem -> Prop) |- _ => clear o end;
                 let l' := lx_snoc l P in pose (lxO := l')
      end
  end.

(* [comment removed for export] *)
Ltac lx_getZ := lazymatch goal with z := ?v : list Z |- _ => v end.
Ltac lx_getW := lazymatch goal with z := ?v : list word |- _ => v end.
Ltac lx_getB := lazymatch goal with z := ?v : list (list byte) |- _ => v end.
Ltac lx_getL := lazymatch goal with z := ?v : list (list word) |- _ => v end.

Ltac lx_addZ t :=
  let l := lx_getZ in let b := lx_mem t l in
  lazymatch b with true => idtac | false =>
    let l' := lx_app1 l t in lazymatch goal with z := _ : list Z |- _ => clear z; pose (lxZ := l') end end.
Ltac lx_addW t :=
  let l := lx_getW in let b := lx_mem t l in
  lazymatch b with true => idtac | false =>
    let l' := lx_app1 l t in lazymatch goal with z := _ : list word |- _ => clear z; pose (lxW := l') end end.
Ltac lx_addB t :=
  let l := lx_getB in let b := lx_mem t l in
  lazymatch b with true => idtac | false =>
    let l' := lx_app1 l t in lazymatch goal with z := _ : list (list byte) |- _ => clear z; pose (lxB := l') end end.
(* [comment removed for export] *)
Ltac lx_addL t :=
  let l := lx_getL in let b := lx_mem t l in
  lazymatch b with true => idtac | false =>
    let l' := lx_app1 l t in lazymatch goal with z := _ : list (list word) |- _ => clear z; pose (lxL := l') end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac lx_colZ t :=
  lazymatch t with
  | Z.add ?a ?b => lx_colZ a; lx_colZ b
  | Z.sub ?a ?b => lx_colZ a; lx_colZ b
  | Z.opp ?a => lx_colZ a
  | Z.mul ?c ?a => tryif lx_is_lit c then lx_colZ a
                  else tryif lx_is_klit a then (lx_colZ c; lx_addZ t)        (* [comment removed for export] *)
                  else tryif lx_is_klit c then (lx_colZ a; lx_addZ t)        (* [comment removed for export] *)
                  else (lx_colZ c; lx_colZ a)
  | Z.shiftr ?a ?k => tryif lx_is_lit k then lx_colZ a else lx_addZ t
  | bv_unsigned ?w => lx_addW w
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.pow ?a ?b => tryif (lx_is_lit a; lx_is_lit b) then idtac else lx_addZ t
  | _ => lx_addZ t
  end.

Ltac lx_colW v :=
  lazymatch v with
  | Z_to_bv 64 ?t => lx_colZ t
  | _ => lx_addW v
  end.

(* [comment removed for export] *)
Ltac lx_closed_nat n :=
  lazymatch n with
  | O => idtac
  | S ?m => lx_closed_nat m
  | Z.to_nat ?z => lx_is_lit z
  | N.to_nat ?z => lazymatch z with N0 => idtac | Npos _ => idtac end
  | Pos.to_nat ?p => lazymatch p with xH => idtac | xO _ => idtac | xI _ => idtac end
  | Nat.of_num_uint _ => idtac
  | _ => lazymatch isnatcst n with true => idtac end
  end.

(* [comment removed for export] *)
Ltac lx_same_nat n k := let n1 := eval cbv in (N.of_nat n) in let k1 := eval cbv in (N.of_nat k) in constr_eq n1 k1.

Ltac lx_colCells cs :=
  lazymatch cs with
  | nil => idtac
  | cons ?c ?cs' =>
      lazymatch c with
      | C8 ?v => lx_colW v
      | C4 (Z_to_bv 64 ?t) => lx_colZ t
      | C4 ?v => lx_addW v
      | C2 (Z_to_bv 64 ?t) => lx_colZ t
      | C2 ?v => lx_addW v
      | C1 (Z_to_bv 8 ?t) => lx_colZ t
      (* [comment removed for export] *)
      | CB ?n (repeat (Z_to_bv 8 ?t) ?k) => lx_closed_nat n; lx_same_nat n k; lx_colZ t
      | CB ?n ?l => lx_closed_nat n; lx_addB l
      end; lx_colCells cs'
  end.

(* [comment removed for export] *)
Ltac lx_colIvls W :=
  lazymatch W with
  | nil => idtac
  | cons (?lo, ?hi) ?W' => lx_colZ lo; lx_colZ hi; lx_colIvls W'
  end.

Ltac lx_colZs l :=
  lazymatch l with
  | nil => idtac
  | cons ?t ?l' => lx_colZ t; lx_colZs l'
  end.

(* [comment removed for export] *)
Ltac lx_colHypM m T :=
  lazymatch T with
  | rw_cells _ m ?a ?cs => lx_colZ a; lx_colCells cs
  | ro_cells _ m ?a ?cs => lx_colZ a; lx_colCells cs
  (* [comment removed for export] *)
  | bytes_at _ m ?a (u32s ?l) => lx_colZ a; lx_addL l; lx_colZ constr:(Z.of_nat (length l)); lx_colZ constr:(Z.of_nat (length (u32s l)))
  | bytes_at _ m ?a (u64s ?l) => lx_colZ a; lx_addL l; lx_colZ constr:(Z.of_nat (length l)); lx_colZ constr:(Z.of_nat (length (u64s l)))
  | u8arr _ m ?a ?l => lx_colZ a; lx_addB l; lx_colZ constr:(Z.of_nat (length l))
  | u32arr _ m ?a ?l => lx_colZ a; lx_addL l; lx_colZ constr:(Z.of_nat (length l)); lx_colZ constr:(Z.of_nat (length (u32s l)))
  | u64arr _ m ?a ?l => lx_colZ a; lx_addL l; lx_colZ constr:(Z.of_nat (length l)); lx_colZ constr:(Z.of_nat (length (u64s l)))
  | bytes_at _ m ?a ?l => lx_colZ a; lx_addB l; lx_colZ constr:(Z.of_nat (length l))
  | stk _ m ?lo ?hi => lx_colZ lo; lx_colZ hi
  | aobj _ ?AL _ m ?a ?n => lx_colZ a; lx_colZ n; lx_colZ constr:(al_sb AL)
  | lx_opq _ _ _ ?P ?OK ?SH m => let l := lx_getO in lazymatch lx_mem P l with true => lx_colIvls OK; lx_colIvls SH end
  | _ => fail
  end.

Ltac lx_colHyp m T :=
  lazymatch T with
  | crange _ ?a ?n => lx_colZ a; lx_colZ n
  | Z.le ?a ?b => lx_colZ a; lx_colZ b
  | Z.lt ?a ?b => lx_colZ a; lx_colZ b
  | @eq Z (Z.modulo ?a ?k) Z0 => lx_colZ a
  | @eq Z ?a ?b => lx_colZ a; lx_colZ b
  (* [comment removed for export] *)
  | ?z = 0 \/ ?a <= ?b \/ ?c <= ?d => lx_colZ z; lx_colZ a; lx_colZ b; lx_colZ c; lx_colZ d
  | ?a <= ?b \/ ?c <= ?d => lx_colZ a; lx_colZ b; lx_colZ c; lx_colZ d
  (* [comment removed for export] *)
  | lawcli _ ?LAW ?a ?n => let l := lx_getLW in lazymatch lx_mem LAW l with true => lx_colZ a; lx_colZ n
                             | false => idtac "lx: WARNING: tag hypothesis IGNORED, its law is not in the run's LAWS list:" LAW; fail end
  | lawobj _ _ _ ?LAW ?a ?n => let l := lx_getLW in lazymatch lx_mem LAW l with true => lx_colZ a; lx_colZ n
                             | false => idtac "lx: WARNING: tag hypothesis IGNORED, its law is not in the run's LAWS list:" LAW; fail end
  (* [comment removed for export] *)
  | lx_fprop _ _ ?vs => lx_colZs vs
  (* [comment removed for export] *)
  | lx_heapkit _ _ _ _ _ _ ?OK m _ => lx_colIvls OK
  | lx_hcli _ _ ?LAW ?sm ?a ?n => let l := lx_getLH in lazymatch lx_mem LAW l with true => lx_colZ sm; lx_colZ a; lx_colZ n
                             | false => idtac "lx: WARNING: heap tag hypothesis IGNORED, its law is not in the run's heap LAWS list:" LAW; fail end
  | lx_hopq _ ?LAW ?P => let l := lx_getLH in lazymatch lx_mem LAW l with true => let lo := lx_getO in lazymatch lx_mem P lo with true => idtac end
                             | false => idtac "lx: WARNING: heap tag hypothesis IGNORED, its law is not in the run's heap LAWS list:" LAW; fail end
  | _ => lx_colHypM m T
  end.


Ltac lx_colRegs R :=
  lazymatch R with
  | mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
      lx_colW x1; lx_colW x2; lx_colW x3; lx_colW x4; lx_colW x5; lx_colW x6; lx_colW x7; lx_colW x8;
      lx_colW x9; lx_colW x10; lx_colW x11; lx_colW x12; lx_colW x13; lx_colW x14; lx_colW x15; lx_colW x16;
      lx_colW x17; lx_colW x18; lx_colW x19; lx_colW x20; lx_colW x21; lx_colW x22; lx_colW x23; lx_colW x24;
      lx_colW x25; lx_colW x26; lx_colW x27; lx_colW x28; lx_colW x29; lx_colW x30; lx_colW x31
  end.


Ltac lx_colW_ivls W :=
  lazymatch W with
  | nil => idtac
  | cons (?lo, ?hi) ?W' => lx_colZ lo; lx_colZ hi; lx_colW_ivls W'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac lx_reZ t :=
  lazymatch t with
  | Z.add ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:(EAdd x y)
  | Z.sub ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:(EAdd x (EMulC (-1) y))
  | Z.opp ?a => let x := lx_reZ a in constr:(EMulC (-1) x)
  | Z.mul ?c ?a =>
      lazymatch c with
      | Z0 => let x := lx_reZ a in constr:(EMulC c x)
      | Zpos _ => let x := lx_reZ a in constr:(EMulC c x)
      | Zneg _ => let x := lx_reZ a in constr:(EMulC c x)
      (* [comment removed for export] *)
      | _ => lazymatch a with
             | Z0 => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
             | Zpos _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
             | Zneg _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
             | Z.pow (Zpos _) (Zpos _) => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
             | _ => lazymatch c with
                    | Z.pow (Zpos _) (Zpos _) => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
                    | _ => let x := lx_reZ c in let y := lx_reZ a in constr:(EOp OMul x y)
                    end
             end
      end
  | Z.shiftr ?a ?k =>
      lazymatch k with
      | Zpos _ => let x := lx_reZ a in constr:(EOp OShr x (ELit k))
      | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
      end
  | bv_unsigned ?w => let l := lx_getW in let i := lx_idx w l in constr:(EUv i)
  | Z0 => constr:(ELit 0) | Zpos _ => constr:(ELit t) | Zneg _ => constr:(ELit t)
  | Z.pow ?a ?b =>
      lazymatch a with
      | Zpos _ => lazymatch b with
                  | Zpos _ => let v := eval cbv in t in constr:(ELit v)
                  | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
                  end
      | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
      end
  | _ => let l := lx_getZ in let i := lx_idx t l in constr:(EZv i)
  end.

Ltac lx_reReg v :=
  lazymatch v with
  | Z_to_bv 64 ?t => let e := lx_reZ t in constr:(RZ e)
  | _ => let l := lx_getW in let i := lx_idx v l in constr:(RW i)
  end.

Ltac lx_reCell c :=
  lazymatch c with
  | C8 (Z_to_bv 64 ?t) => let e := lx_reZ t in constr:(XZ 8 e)
  | C8 ?v => let l := lx_getW in let i := lx_idx v l in constr:(XW i)
  | C4 (Z_to_bv 64 ?t) => let e := lx_reZ t in constr:(XZ 4 e)
  | C4 ?v => let l := lx_getW in let i := lx_idx v l in constr:(XWn 4 i)
  | C2 (Z_to_bv 64 ?t) => let e := lx_reZ t in constr:(XZ 2 e)
  | C2 ?v => let l := lx_getW in let i := lx_idx v l in constr:(XWn 2 i)
  | C1 (Z_to_bv 8 ?t) => let e := lx_reZ t in constr:(XZ 1 e)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  | CB ?n (repeat (Z_to_bv 8 ?t) ?k) =>
      let chk := match goal with _ => lx_closed_nat n; lx_same_nat n k end in
      let e := lx_reZ t in let w := eval cbv in (N.of_nat n) in constr:(XRep w e)
  | CB ?n ?bs =>
      let chk := match goal with _ => lx_closed_nat n end in
      let l := lx_getB in let i := lx_idx bs l in let w := eval cbv in (N.of_nat n) in constr:(XB w i)
  end.

Ltac lx_reCells cs :=
  lazymatch cs with
  | nil => constr:(@nil cellx)
  | cons ?c ?cs' => let x := lx_reCell c in let r := lx_reCells cs' in constr:(cons x r)
  end.

Ltac lx_reRegs R :=
  lazymatch R with
  | mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
      let r1 := lx_reReg x1 in let r2 := lx_reReg x2 in let r3 := lx_reReg x3 in let r4 := lx_reReg x4 in
      let r5 := lx_reReg x5 in let r6 := lx_reReg x6 in let r7 := lx_reReg x7 in let r8 := lx_reReg x8 in
      let r9 := lx_reReg x9 in let r10 := lx_reReg x10 in let r11 := lx_reReg x11 in let r12 := lx_reReg x12 in
      let r13 := lx_reReg x13 in let r14 := lx_reReg x14 in let r15 := lx_reReg x15 in let r16 := lx_reReg x16 in
      let r17 := lx_reReg x17 in let r18 := lx_reReg x18 in let r19 := lx_reReg x19 in let r20 := lx_reReg x20 in
      let r21 := lx_reReg x21 in let r22 := lx_reReg x22 in let r23 := lx_reReg x23 in let r24 := lx_reReg x24 in
      let r25 := lx_reReg x25 in let r26 := lx_reReg x26 in let r27 := lx_reReg x27 in let r28 := lx_reReg x28 in
      let r29 := lx_reReg x29 in let r30 := lx_reReg x30 in let r31 := lx_reReg x31 in
      constr:([r1; r2; r3; r4; r5; r6; r7; r8; r9; r10; r11; r12; r13; r14; r15; r16; r17; r18; r19; r20;
               r21; r22; r23; r24; r25; r26; r27; r28; r29; r30; r31])
  end.

Ltac lx_log2N k :=
  lazymatch k with
  | 2 => constr:(1%N) | 4 => constr:(2%N) | 8 => constr:(3%N) | 16 => constr:(4%N) | 32 => constr:(5%N)
  | 64 => constr:(6%N) | 4096 => constr:(12%N)
  end.

(* [comment removed for export] *)
Ltac lx_reW_ivls W :=
  lazymatch W with
  | nil => constr:(@nil (expr * expr))
  | cons (?lo, ?hi) ?W' => let x := lx_reZ lo in let y := lx_reZ hi in let r := lx_reW_ivls W' in
                           constr:(cons (x, y) r)
  end.

Ltac lx_reZs l :=
  lazymatch l with
  | nil => constr:(@nil expr)
  | cons ?t ?l' => let x := lx_reZ t in let r := lx_reZs l' in constr:(cons x r)
  end.

(* [comment removed for export] *)
Ltac lx_reHypM m T :=
  lazymatch T with
  | rw_cells _ m ?a ?cs => let x := lx_reZ a in let c := lx_reCells cs in constr:((cons (MRw x c) nil, @nil pfact))
  | ro_cells _ m ?a ?cs => let x := lx_reZ a in let c := lx_reCells cs in constr:((cons (MRo x c) nil, @nil pfact))
  (* [comment removed for export] *)
  | bytes_at _ m ?a (u32s ?ws) => let x := lx_reZ a in let n := lx_reZ constr:(Z.of_nat (length ws)) in let n4 := lx_reZ constr:(Z.of_nat (length (u32s ws))) in
                          let l := lx_getL in let i := lx_idx ws l in
                          constr:((cons (MArr x 4%N (LBase i) n false) nil, cons (FEq (EMulC 4 n) n4) nil))
  | bytes_at _ m ?a (u64s ?ws) => let x := lx_reZ a in let n := lx_reZ constr:(Z.of_nat (length ws)) in let n8 := lx_reZ constr:(Z.of_nat (length (u64s ws))) in
                          let l := lx_getL in let i := lx_idx ws l in
                          constr:((cons (MArr x 8%N (LBase i) n false) nil, cons (FEq (EMulC 8 n) n8) nil))
  | u8arr _ m ?a ?bs => let x := lx_reZ a in let n := lx_reZ constr:(Z.of_nat (length bs)) in let l := lx_getB in let i := lx_idx bs l in
                          constr:((cons (MArr x 1%N (LBase i) n true) nil, @nil pfact))
  | u32arr _ m ?a ?ws => let x := lx_reZ a in let n := lx_reZ constr:(Z.of_nat (length ws)) in let n4 := lx_reZ constr:(Z.of_nat (length (u32s ws))) in
                          let l := lx_getL in let i := lx_idx ws l in
                          constr:((cons (MArr x 4%N (LBase i) n true) nil, cons (FEq (EMulC 4 n) n4) nil))
  | u64arr _ m ?a ?ws => let x := lx_reZ a in let n := lx_reZ constr:(Z.of_nat (length ws)) in let n8 := lx_reZ constr:(Z.of_nat (length (u64s ws))) in
                          let l := lx_getL in let i := lx_idx ws l in
                          constr:((cons (MArr x 8%N (LBase i) n true) nil, cons (FEq (EMulC 8 n) n8) nil))
  | bytes_at _ m ?a ?bs => let x := lx_reZ a in let n := lx_reZ constr:(Z.of_nat (length bs)) in let l := lx_getB in let i := lx_idx bs l in
                          constr:((cons (MBy x n i) nil, @nil pfact))
  | stk _ m ?lo ?hi => let x := lx_reZ lo in let y := lx_reZ hi in constr:((cons (MStk x y) nil, @nil pfact))
  | aobj _ _ _ m ?a ?n => let x := lx_reZ a in let y := lx_reZ n in constr:((cons (MAobj x y) nil, @nil pfact))
  | lx_opq _ _ _ ?P ?OK ?SH m =>
      let l := lx_getO in let k := lx_oidx P l in let ok := lx_reW_ivls OK in let sh := lx_reW_ivls SH in
      constr:((cons (MOpq k ok sh) nil, @nil pfact))
  end.

Ltac lx_reHyp m T :=
  lazymatch T with
  | crange _ ?a ?n => let x := lx_reZ a in let y := lx_reZ n in constr:((@nil mfact, cons (FCr x y) nil))
  | @eq Z (Z.modulo ?a ?k) Z0 => let x := lx_reZ a in let j := lx_log2N k in constr:((@nil mfact, cons (FAl x j) nil))
  | Z.le ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:((@nil mfact, cons (FLe x y) nil))
  | Z.lt ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:((@nil mfact, cons (FLt x y) nil))
  | @eq Z ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:((@nil mfact, cons (FEq x y) nil))
  | ?z = 0 \/ ?a <= ?b \/ ?c <= ?d =>
      let z' := lx_reZ z in let a' := lx_reZ a in let b' := lx_reZ b in let c' := lx_reZ c in let d' := lx_reZ d in
      constr:((@nil mfact, cons (FOr3z z' a' b' c' d') nil))
  | ?a <= ?b \/ ?c <= ?d =>
      let a' := lx_reZ a in let b' := lx_reZ b in let c' := lx_reZ c in let d' := lx_reZ d in
      constr:((@nil mfact, cons (FOr2 a' b' c' d') nil))
  | lawcli _ ?LAW ?a ?n =>
      let l := lx_getLW in let k := lx_oidx LAW l in let x := lx_reZ a in let y := lx_reZ n in
      constr:((cons (MCli k x y) nil, @nil pfact))
  | lawobj _ _ _ ?LAW ?a ?n =>
      let l := lx_getLW in let k := lx_oidx LAW l in let x := lx_reZ a in let y := lx_reZ n in
      constr:((cons (MCobj k x y) nil, @nil pfact))
  | lx_fprop _ ?j ?vs => let xs := lx_reZs vs in constr:((@nil mfact, cons (FProp j xs) nil))
  (* [comment removed for export] *)
  | lx_heapkit _ _ _ _ _ _ ?OK m _ => let ok := lx_reW_ivls OK in constr:((cons (MHeap BL0 ok) nil, @nil pfact))
  | lx_hcli _ _ ?LAW ?sm ?a ?n =>
      let l := lx_getLH in let k := lx_oidx LAW l in let w := lx_reZ sm in let x := lx_reZ a in let y := lx_reZ n in
      constr:((cons (MCliH k w x y) nil, @nil pfact))
  | lx_hopq _ ?LAW ?P =>
      let l := lx_getLH in let k := lx_oidx LAW l in let lo := lx_getO in let j := lx_oidx P lo in
      constr:((cons (MOqH k j) nil, @nil pfact))
  | _ => lx_reHypM m T
  end.


Lemma lx_sep_shift : forall a n e c : Z, (a + n <= e - c \/ e <= a) -> (a + n <= e - c \/ e - c + c <= a).
Proof. intros; lia. Qed.
Lemma lx_sep0_shift : forall z a n e c : Z, (z = 0 \/ a + n <= e - c \/ e <= a) -> (z = 0 \/ a + n <= e - c \/ e - c + c <= a).
Proof. intros; lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_pose_dup t T := pose proof (t : lx_dup T).

(* [comment removed for export] *)
Ltac lx_arith_conj A :=
  lazymatch A with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | @eq Z _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | ?X /\ ?Y => lx_arith_conj X; lx_arith_conj Y
  | _ \/ _ => idtac
  | _ => fail
  end.

(* [comment removed for export] *)
Lemma lx_dorc : forall (z1 z2 a b c d : Z), (z1 = 0 /\ z2 = 0) \/ (a <= b /\ c <= d) ->
  (z1 = 0 \/ a <= b \/ a <= b) /\ (z1 = 0 \/ c <= d \/ c <= d) /\ (z2 = 0 \/ a <= b \/ a <= b) /\ (z2 = 0 \/ c <= d \/ c <= d).
Proof. intros; lia. Qed.
Lemma lx_dorc' : forall (z1 z2 a b c d : Z), (a <= b /\ c <= d) \/ (z1 = 0 /\ z2 = 0) ->
  (z1 = 0 \/ a <= b \/ a <= b) /\ (z1 = 0 \/ c <= d \/ c <= d) /\ (z2 = 0 \/ a <= b \/ a <= b) /\ (z2 = 0 \/ c <= d \/ c <= d).
Proof. intros; lia. Qed.

Ltac lx_prep segs AL m :=
  repeat match goal with
         | H : (?z1 = 0 /\ ?z2 = 0) \/ (?a <= ?b /\ ?c <= ?d) |- _ => lazymatch type of H with lx_seen _ => fail | lx_dup _ => fail | ?T =>
             let X := fresh in pose proof (lx_dorc z1 z2 a b c d H) as X;
             lx_pose_dup (proj1 X) (z1 = 0 \/ a <= b \/ a <= b); lx_pose_dup (proj1 (proj2 X)) (z1 = 0 \/ c <= d \/ c <= d);
             lx_pose_dup (proj1 (proj2 (proj2 X))) (z2 = 0 \/ a <= b \/ a <= b); lx_pose_dup (proj2 (proj2 (proj2 X))) (z2 = 0 \/ c <= d \/ c <= d);
             clear X; change (lx_seen T) in H end
         | H : (?a <= ?b /\ ?c <= ?d) \/ (?z1 = 0 /\ ?z2 = 0) |- _ => lazymatch type of H with lx_seen _ => fail | lx_dup _ => fail | ?T =>
             let X := fresh in pose proof (lx_dorc' z1 z2 a b c d H) as X;
             lx_pose_dup (proj1 X) (z1 = 0 \/ a <= b \/ a <= b); lx_pose_dup (proj1 (proj2 X)) (z1 = 0 \/ c <= d \/ c <= d);
             lx_pose_dup (proj1 (proj2 (proj2 X))) (z2 = 0 \/ a <= b \/ a <= b); lx_pose_dup (proj2 (proj2 (proj2 X))) (z2 = 0 \/ c <= d \/ c <= d);
             clear X; change (lx_seen T) in H end
         | H : ?A /\ ?B |- _ => lazymatch type of H with lx_seen _ => fail | lx_dup _ => fail | ?T =>
             tryif (lx_arith_conj A; lx_arith_conj B) then
               (lx_pose_dup (proj1 H) A; lx_pose_dup (proj2 H) B; change (lx_seen T) in H)
             else change (lx_seen T) in H end
         | H : lx_dup (?A /\ ?B) |- _ =>
             lx_pose_dup (proj1 H) A; lx_pose_dup (proj2 H) B; clear H
         | H : abase segs AL m |- _ => lazymatch type of H with lx_seen _ => fail | ?T =>
             (* [comment removed for export] *)
             let g := eval hnf in (@li_got segs AL _) in let b := eval hnf in (@li_gsb segs AL _) in
             lx_pose_dup (li_abase_got m H) (ro_cells segs m g [C8 (Z_to_bv 64 b)]);
             lx_pose_dup (li_abase_gsb m H) (ro_cells segs m b [C8 (Z_to_bv 64 (al_sb AL))]);
             change (lx_seen T) in H end
         | H : cs_ok AL ?CS |- _ => lazymatch type of H with lx_seen _ => fail | ?T =>
             lx_pose_dup (proj1 (cs_ok_sb AL CS H)) (0 <= al_sb AL); lx_pose_dup (proj2 (cs_ok_sb AL CS H)) (al_sb AL < 2 ^ 64);
             change (lx_seen T) in H end
         end.

(* [comment removed for export] *)
Ltac lx_byte_cells :=
  repeat match goal with
         | H : rw_cells _ _ _ ?cs |- _ =>
             match cs with context [C1 ?b] =>
               lazymatch b with
               | Z_to_bv _ _ => fail
               | _ => lazymatch type of b with bv 8 =>
                        rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b) in H;
                        let z := fresh "lxbz" in let e := fresh "LXBZ" in
                        remember (bv_unsigned b) as z eqn:e in H;
                        lazymatch type of e with ?T => change (lx_hidden T) in e end
                      end
               end
             end
         end.

Ltac lx_clear_dups := repeat match goal with H : lx_dup _ |- _ => clear H end.

Ltac lx_unseen := repeat match goal with H : lx_seen ?T |- _ => change T in H end.

Ltac lx_strip T := lazymatch T with lx_dup ?U => U | _ => T end.

(* [comment removed for export] *)
Ltac lx_collect_hyps m :=
  repeat match goal with
         | H : ?T0 |- _ => lazymatch T0 with lx_seen _ => fail | lx_hidden _ => fail | _ =>
             let T := lx_strip T0 in lx_colHyp m T; change (lx_seen T0) in H end
         end;
  lx_unseen.

(* [comment removed for export] *)
Ltac lx_reify_hyps m :=
  repeat match goal with
         | H : ?T0 |- _ => lazymatch T0 with lx_seen _ => fail | lx_hidden _ => fail | _ =>
             let T := lx_strip T0 in
             let r := lx_reHyp m T in
             lazymatch r with (?mf, ?pf) =>
               lazymatch goal with a := ?mf0 : list mfact |- _ =>
                 lazymatch goal with b := ?pf0 : list pfact |- _ =>
                   let mf1 := eval cbv [List.app] in (mf0 ++ mf) in
                   let pf1 := eval cbv [List.app] in (pf0 ++ pf) in
                   clear a b; pose (lxMF := mf1); pose (lxPF := pf1)
                 end end
             end;
             change (lx_seen T0) in H end
         end;
  lx_unseen.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_link_laws m l :=
  lazymatch goal with
  | H : lx_link ?LAW ?X ?m1 m |- _ =>
      let l1 := lazymatch lx_mem LAW l with true => l | false => lx_snoc l LAW end in lx_link_laws m1 l1
  | H : lx_mlink _ ?W ?m1 m |- _ => lx_link_laws m1 l
  | |- _ => l
  end.
Ltac lx_has_links m :=
  lazymatch goal with
  | H : lx_link _ _ _ m |- _ => constr:(true)
  | H : lx_mlink _ _ _ m |- _ => constr:(true)
  | |- _ => constr:(false)
  end.
(* [comment removed for export] *)
Ltac lx_collect_hypsM m :=
  repeat match goal with
         | H : ?T0 |- _ => lazymatch T0 with lx_seen _ => fail | lx_hidden _ => fail | _ =>
             let T := lx_strip T0 in lx_colHypM m T; change (lx_seen T0) in H end
         end;
  lx_unseen.
Ltac lx_col_links m :=
  lazymatch goal with
  | H : lx_link ?LAW ?X ?m1 m |- _ => lx_colIvls X; lx_collect_hypsM m1; lx_col_links m1
  | H : lx_mlink _ ?W ?m1 m |- _ => lx_colIvls W; lx_collect_hypsM m1; lx_col_links m1
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lx_reify_hypsM m :=
  let run := match goal with _ =>
    pose (lxMFk := @nil mfact); pose (lxPFk := @nil pfact);
    repeat match goal with
           | H : ?T0 |- _ => lazymatch T0 with lx_seen _ => fail | lx_hidden _ => fail | _ =>
               let T := lx_strip T0 in
               let r := lx_reHypM m T in
               lazymatch r with (?mf, ?pf) =>
                 lazymatch goal with a := ?mf0 : list mfact |- _ =>
                   lazymatch goal with b := ?pf0 : list pfact |- _ =>
                     let mf1 := eval cbv [List.app] in (mf0 ++ mf) in
                     let pf1 := eval cbv [List.app] in (pf0 ++ pf) in
                     clear a b; pose (lxMFk := mf1); pose (lxPFk := pf1)
                   end end
               end;
               change (lx_seen T0) in H end
           end;
    lx_unseen end in
  let mf := lazymatch goal with a := ?v : list mfact |- _ => v end in
  let pf := lazymatch goal with b := ?v : list pfact |- _ => v end in
  let clr := match goal with _ => lazymatch goal with a := _ : list mfact |- _ => clear a end; lazymatch goal with b := _ : list pfact |- _ => clear b end end in
  constr:((mf, pf)).
(* [comment removed for export] *)
Ltac lx_re_links segs m :=
  lazymatch goal with
  | H : lx_link ?LAW ?X ?m1 m |- _ =>
      let r0 := lx_re_links segs m1 in
      lazymatch r0 with (?ch, ?pfa, ?srcs) =>
        let r1 := lx_reify_hypsM m1 in
        lazymatch r1 with (?mf1, ?pf1) =>
          let l := lx_getLW in let k := lx_oidx LAW l in let Xr := lx_reW_ivls X in
          let ch' := lx_snoc ch constr:((ELaw k Xr, mf1)) in
          let pf' := eval cbv [List.app] in (pfa ++ pf1) in
          let srcs' := lx_snoc srcs m1 in
          constr:((ch', pf', srcs'))
        end
      end
  | H : lx_mlink _ ?W ?m1 m |- _ =>
      let r0 := lx_re_links segs m1 in
      lazymatch r0 with (?ch, ?pfa, ?srcs) =>
        let r1 := lx_reify_hypsM m1 in
        lazymatch r1 with (?mf1, ?pf1) =>
          let Wr := lx_reW_ivls W in
          let ch' := lx_snoc ch constr:((EMunch Wr, mf1)) in
          let pf' := eval cbv [List.app] in (pfa ++ pf1) in
          let srcs' := lx_snoc srcs m1 in
          constr:((ch', pf', srcs'))
        end
      end
  | |- _ => constr:((@nil (elink * list mfact), @nil pfact, @nil mem))
  end.

(* [comment removed for export] *)
Definition lx_spelling : Prop := True.
Ltac lx_spell := lazymatch goal with _ : lx_spelling |- _ => idtac | |- _ => assert lx_spelling by exact I end.
(* [comment removed for export] *)
Definition lx_pruning : Prop := True.
Ltac lx_prune_same := lazymatch goal with _ : lx_pruning |- _ => idtac | |- _ => assert lx_pruning by exact I end.
Ltac lx_alias_term t :=
  let e := lx_reZ t in
  lazymatch e with
  | EZv _ => idtac | EUv _ => idtac | ELit _ => idtac
  | _ => lx_addZ t; let l := lx_getZ in let j := lx_idx t l in
         lazymatch goal with b := ?pf0 : list pfact |- _ =>
           let pf1 := eval cbv [List.app] in (pf0 ++ [FEq (EZv j) e]) in clear b; pose (lxPF := pf1) end
  end.
Ltac lx_alias_reg v := lazymatch v with Z_to_bv 64 ?t => lx_alias_term t | _ => idtac end.
Ltac lx_alias_regs R :=
  lazymatch R with
  | mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 => lx_alias_reg x1; lx_alias_reg x2; lx_alias_reg x3; lx_alias_reg x4; lx_alias_reg x5; lx_alias_reg x6; lx_alias_reg x7; lx_alias_reg x8; lx_alias_reg x9; lx_alias_reg x10; lx_alias_reg x11; lx_alias_reg x12; lx_alias_reg x13; lx_alias_reg x14; lx_alias_reg x15; lx_alias_reg x16; lx_alias_reg x17; lx_alias_reg x18; lx_alias_reg x19; lx_alias_reg x20; lx_alias_reg x21; lx_alias_reg x22; lx_alias_reg x23; lx_alias_reg x24; lx_alias_reg x25; lx_alias_reg x26; lx_alias_reg x27; lx_alias_reg x28; lx_alias_reg x29; lx_alias_reg x30; lx_alias_reg x31
  end.
Ltac lx_alias_ivls W :=
  lazymatch W with
  | nil => idtac
  | cons (?lo, ?hi) ?W' => lx_alias_term lo; lx_alias_term hi; lx_alias_ivls W'
  end.

(* [comment removed for export] *)
Ltac lx_prod_fact j c x :=
  let cv := eval cbv in c in let ex := lx_reZ x in
  lazymatch goal with b := ?pf0 : list pfact |- _ =>
    let pf1 := eval cbv [List.app] in (pf0 ++ [FEq (EZv j) (EMulC cv ex)]) in clear b; pose (lxPF := pf1) end.
Ltac lx_prod_facts_of l all :=
  lazymatch l with
  | nil => idtac
  | cons ?t ?l' =>
      (lazymatch t with
       | Z.mul ?c ?a =>
           tryif lx_is_lit c then idtac
           else tryif lx_is_klit a then (let j := lx_idx t all in lx_prod_fact j a c)
           else tryif lx_is_klit c then (let j := lx_idx t all in lx_prod_fact j c a)
           else idtac
       | _ => idtac
       end);
      lx_prod_facts_of l' all
  end.
Ltac lx_prod_facts := let l := lx_getZ in lx_prod_facts_of l l.

(* [comment removed for export] *)
Ltac lx_unfold_oblig :=
  lazy [oblig leaf_oblig mf_tele pf_tele mfact_ok pfact_ok ms_den regs_den pc_den rden cden csden zdenp opden cnden kden
        ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv refm ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget pset pad_set env_setz g_L g_CS g_F g_fc g_m0 g_me c_acc ac_sb wden List.map List.app List.nth fst snd
        s_pc s_rs s_mf s_pf s_W s_nx s_same s_ref s_nm
        Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred xorb].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_letG := lazymatch goal with g := _ : gl |- _ => g end.
Ltac lx_letE := lazymatch goal with e := _ : env |- _ => e end.
Definition lx_kont := Model -> machine_state -> Prop.
Ltac lx_letK := lazymatch goal with k := _ : lx_kont |- _ => k end.
Ltac lx_unfold_spine := lazy [oblig Pos.succ].
Ltac lx_unfold_leaf_spine := lazy [leaf_oblig mf_tele pf_tele s_mf s_pf s_W s_same].
Ltac lx_unfold_inEG H e g :=
  lazy [e g mfact_ok pfact_ok ms_den regs_den pc_den rden cden csden zdenp opden cnden kden
        ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv refm ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget pset pad_set env_setz g_L g_CS g_F g_fc g_m0 g_me c_acc ac_sb wden List.map List.app List.nth fst snd
        s_pc s_rs s_mf s_pf s_W s_nx s_same s_ref s_nm
        Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred xorb] in H.
Ltac lx_unfold_goalEG e g :=
  lazy [e g mfact_ok pfact_ok ms_den regs_den pc_den rden cden csden zdenp opden cnden kden
        ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv refm ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget pset pad_set env_setz g_L g_CS g_F g_fc g_m0 g_me c_acc ac_sb wden List.map List.app List.nth fst snd
        s_pc s_rs s_mf s_pf s_W s_nx s_same s_ref s_nm
        Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred xorb].
Ltac lx_unfold_goalEGK e g k :=
  lazy [e g k tgt_aevtM mfact_ok pfact_ok ms_den regs_den pc_den rden cden csden zdenp opden cnden kden
        ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv refm ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget pset pad_set env_setz g_L g_CS g_F g_fc g_m0 g_me c_acc ac_sb wden List.map List.app List.nth fst snd
        s_pc s_rs s_mf s_pf s_W s_nx s_same s_ref s_nm
        Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred xorb].
Ltac lx_unfold_in H := let e := lx_letE in let g := lx_letG in lx_unfold_inEG H e g.
(* [comment removed for export] *)
Ltac lx_bind_env v :=
  match goal with
  | |- context [env_setz ?x ?i v] =>
      is_var x;
      (* [comment removed for export] *)
      let x' := lx_letE in constr_eq x x';
      let e := fresh "lxE" in set (e := env_setz x i v);
      lazy [x' env_setz pset pad_set ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr
            Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred] in (value of e)
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lx_bind_envl l :=
  match goal with
  | |- context [env_setl ?x ?i l] =>
      is_var x;
      let x' := lx_letE in constr_eq x x';
      let e := fresh "lxE" in set (e := env_setl x i l);
      lazy [x' env_setl pset pad_set ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr
            Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred] in (value of e)
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lx_bind_mems mc mp :=
  match goal with
  | |- context [env_setm (env_setm ?x ?i mc) ?j mp] =>
      is_var x;
      let x' := lx_letE in constr_eq x x';
      let e := fresh "lxE" in set (e := env_setm (env_setm x i mc) j mp);
      lazy [x' env_setm nset ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr] in (value of e)
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lx_bind_heap mc mp mo lb :=
  match goal with
  | |- context [env_setbl (env_setcur (env_setm (env_setm ?x ?i mc) ?j mp) mo) ?j lb] =>
      is_var x;
      let x' := lx_letE in constr_eq x x';
      let e := fresh "lxE" in set (e := env_setbl (env_setcur (env_setm (env_setm x i mc) j mp) mo) j lb);
      lazy [x' env_setbl env_setcur env_setm nset ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr] in (value of e)
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lx_unfold_all :=
  let e := lx_letE in let g := lx_letG in let k := lx_letK in
  (* [comment removed for export] *)
  lazymatch goal with |- ?G =>
  let t := eval lazy [e g k tgt_aevtM oblig leaf_oblig mf_tele pf_tele mfact_ok pfact_ok ms_den regs_den pc_den rden cden csden zdenp opden cnden kden
        ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv refm ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget pset pad_set env_setz g_L g_CS g_F g_fc g_m0 g_me c_acc ac_sb wden List.map List.app List.nth fst snd
        s_pc s_rs s_mf s_pf s_W s_nx s_same s_ref s_nm
        Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred xorb] in G in change t end;
  try clear k; try clear e; try clear g.
Ltac lx_clear_lets :=
  repeat match goal with
         | k := _ : lx_kont |- _ => clear k
         | e := _ : env |- _ => clear e
         | g := _ : gl |- _ => clear g
         end.
(* [comment removed for export] *)
Ltac lx_unfold_obligL := let e := lx_letE in let g := lx_letG in lx_unfold_goalEG e g; lx_unfold_oblig.

(* [comment removed for export] *)
Ltac lx_chg_goalEG e g :=
  lazymatch goal with |- ?G =>
    let t := eval lazy [e g mfact_ok pfact_ok ms_den regs_den pc_den rden cden csden zdenp opden cnden kden
        ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv refm ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget pset pad_set env_setz g_L g_CS g_F g_fc g_m0 g_me c_acc ac_sb wden List.map List.app List.nth fst snd
        s_pc s_rs s_mf s_pf s_W s_nx s_same s_ref s_nm
        Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred xorb] in G in
    change t end.
(* [comment removed for export] *)
Ltac lx_chg_obligL := let e := lx_letE in let g := lx_letG in lx_chg_goalEG e g.
(* [comment removed for export] *)
Ltac lx_chg_leafEGK e g k :=
  lazymatch goal with |- ?G =>
    let t := eval lazy [e g k tgt_aevtM oblig leaf_oblig mf_tele pf_tele mfact_ok pfact_ok ms_den regs_den pc_den rden cden csden zdenp opden cnden kden
        ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv refm ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget pset pad_set env_setz g_L g_CS g_F g_fc g_m0 g_me c_acc ac_sb wden List.map List.app List.nth fst snd
        s_pc s_rs s_mf s_pf s_W s_nx s_same s_ref s_nm
        Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred xorb] in G in
    change t end.
(* [comment removed for export] *)
Ltac lx_eval_EG e g T :=
  eval lazy [e g tgt_aevtM mfact_ok pfact_ok ms_den regs_den pc_den rden cden csden zdenp opden cnden kden
        ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv refm ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget pset pad_set env_setz g_L g_CS g_F g_fc g_m0 g_me c_acc ac_sb wden List.map List.app List.nth fst snd
        s_pc s_rs s_mf s_pf s_W s_nx s_same s_ref s_nm
        Pos.pred Pos.pred_double Pos.succ Pos.eqb N.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.pred xorb] in T.

(* [comment removed for export] *)
Definition lx_folding : Prop := True.
Ltac lx_fold_leaves := lazymatch goal with _ : lx_folding |- _ => idtac | |- _ => assert lx_folding by exact I end.
(* [comment removed for export] *)
Ltac lx_fold_default := constr:(false).

(* [comment removed for export] *)
Lemma lx_len_u32s : forall ws, 4 * Z.of_nat (length ws) = Z.of_nat (length (u32s ws)).
Proof. intros ws. rewrite u32s_length, Nat2Z.inj_mul. reflexivity. Qed.
Lemma lx_len_u64s : forall ws, 8 * Z.of_nat (length ws) = Z.of_nat (length (u64s ws)).
Proof. intros ws. rewrite u64s_length, Nat2Z.inj_mul. reflexivity. Qed.
(* [comment removed for export] *)
Lemma lx_st_ok_intro : forall segs G E ss ms m,
  ms = ms_den segs G E ss m ->
  Forall (mfact_ok segs (g_L G) (g_CS G) E m) (s_mf ss) ->
  Forall (pfact_ok (g_CS G) E) (s_pf ss) ->
  munch (wden E (s_W ss)) (refm E ss) m -> wmono segs (refm E ss) m -> mem_inv segs m ->
  (s_same ss = true -> m = g_me G) ->
  st_ok segs G E ss ms.
Proof. intros * -> MF PF MU WM MI SM. exists m. split; [reflexivity|]. repeat (split; [assumption|]). exact SM. Qed.
(* [comment removed for export] *)
Lemma lx_cfg_ok_introA : forall segs Ly (LI : LxImg segs Ly) G E sb,
  g_L G = Ly -> cs_ok (g_L G) (g_CS G) -> al_wf (g_L G) -> zdenp E sb = al_sb (g_L G) ->
  cfg_ok G (LXC (Some (ACFG sb li_lo li_hi li_got li_gsb))) E.
Proof. intros * EL CS WF SB. unfold cfg_ok. cbn [c_acc ac_sb ac_img_lo ac_img_hi ac_got ac_gsb]. split; [exact CS| split; [exact WF| split; [exact SB|]]]. rewrite EL. exact (@li_ok segs Ly LI). Qed.

(* [comment removed for export] *)
Ltac lx_lia_lengths :=
  repeat match goal with H : ?T |- _ =>
           lazymatch T with
           | Z.of_nat (length _) = _ => fail
           | _ = Z.of_nat (length _) => fail
           | _ => clear H
           end end;
  rewrite ?u32s_length, ?u64s_length; lia.
Ltac lx_close_fact :=
  first [ assumption
        (* [comment removed for export] *)
        | lazymatch goal with
          | |- lx_heapkit _ _ _ _ _ _ _ _ _ => eapply lx_heapkit_rebase; eassumption
          | |- lx_hcli _ _ _ _ _ _ => eapply lx_hcli_rebase; [eassumption| lx_incl_tac]
          | |- lx_hopq _ _ _ => eapply lx_hopq_rebase; [eassumption| lx_incl_tac]
          end
        | split; [assumption| reflexivity]     (* [comment removed for export] *)
        | apply List.Forall_nil
        | exact (lx_len_u32s _) | exact (lx_len_u64s _)     (* [comment removed for export] *)
        | exact (Z.mul_comm _ _) | reflexivity                (* [comment removed for export] *)
        | lx_lia_lengths
        (* [comment removed for export] *)
        | match goal with |- ?g => idtac "lx: note: entry fact re-proved by lia (respell the hypothesis to save the certificate):" g end; lia
        | match goal with |- ?g => idtac "lx: could not re-prove the reified fact (st_ok):" g; fail end ].
(* [comment removed for export] *)
Ltac lx_close_factF :=
  let e := lx_letE in let g := lx_letG in
  lazymatch goal with |- ?G =>
    let T := lx_eval_EG e g G in
    first [ match goal with H : T |- _ => exact H end
          | lazymatch T with
            | _ /\ _ = _ => refine (conj _ _); [ lazymatch goal with |- ?A => let TA := lx_eval_EG e g A in match goal with H : TA |- _ => exact H end end
                                             | first [ reflexivity | change T; lx_close_fact ] ]
            end
          | change T; lx_close_fact ]
  end.

(* [comment removed for export] *)
Definition lx_no_layout : asan_layout := AL 0 0 0 0 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_closed_ivls W :=
  lazymatch W with
  | nil => idtac
  | cons (_, _) ?W' => lx_closed_ivls W'
  end.

(* [comment removed for export] *)
Ltac lx_report_fails t :=
  let f := eval vm_compute in (rt_fails t (@nil (Z * Z))) in
  lazymatch f with
  | nil => idtac
  | _ => idtac "lx: the run has FAILURES (pc, code) — its obligation is not provable:" f
  end.

(* [comment removed for export] *)
Ltac lx_reify_pack mode segs R pc m m0 GS W :=
  pose (lxZ := @nil Z); pose (lxW := @nil word); pose (lxB := @nil (list byte)); pose (lxL := @nil (list word));
  (* [comment removed for export] *)
  lazymatch goal with
  | SU : Forall (summary_okMR _ _ _ ?OPS _ _ _ _ _ _ _ _ _) _ |- _ => pose (lxO := OPS)
  | SU : Forall (summary_okM _ _ _ ?OPS _ _ _ _ _ _ _ _) _ |- _ => pose (lxO := OPS)
  | SU : Forall (summary_okP _ _ _ ?OPS _ _ _) _ |- _ => pose (lxO := OPS)
  | SU : forall AL', Forall (summary_okP _ AL' _ ?OPS _ _ _) _ |- _ => pose (lxO := OPS)
  | SU : Forall (summary_okL _ _ _ ?OPS _ _) _ |- _ => pose (lxO := OPS)
  | SU : forall AL', Forall (summary_okL _ AL' _ ?OPS _ _) _ |- _ => pose (lxO := OPS)
  | SU : Forall (summary_okO _ _ _ ?OPS _) _ |- _ => pose (lxO := OPS)
  | SU : forall AL', Forall (summary_okO _ AL' _ ?OPS _) _ |- _ => pose (lxO := OPS)
  | |- _ => pose (lxO := @nil (mem -> Prop)); lx_add_ops m
  end;
  (* [comment removed for export] *)
  let laws := lazymatch goal with
              | SU : Forall (summary_okMR _ _ _ _ ?LW _ _ _ _ _ _ _ _) _ |- _ => LW
              | SU : Forall (summary_okM _ _ _ _ ?LW _ _ _ _ _ _ _) _ |- _ => LW
              | SU : Forall (summary_okP _ _ _ _ ?LW _ _) _ |- _ => LW
              | SU : forall AL', Forall (summary_okP _ AL' _ _ ?LW _ _) _ |- _ => LW
              | SU : Forall (summary_okL _ _ _ _ ?LW _) _ |- _ => LW
              | SU : forall AL', Forall (summary_okL _ AL' _ _ ?LW _) _ |- _ => LW
              | |- _ => constr:(@nil (list (Z * Z) -> mem -> mem -> Prop))
              end in
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  let laws := lazymatch laws with
              | nil => lx_link_laws m laws
              | _ => let l2 := lx_link_laws m laws in
                     let chk := match goal with _ => first [ constr_eq l2 laws
                                                           | fail 0 "lx: an entry link's LAW is not in the summaries hypothesis' LAWS list:" l2 "vs" laws ] end in
                     laws
              end in
  pose (lxLW := (laws : list (list (Z * Z) -> mem -> mem -> Prop)));
  (* [comment removed for export] *)
  let props := lazymatch goal with
              | SU : Forall (summary_okMR _ _ _ _ _ ?PR _ _ _ _ _ _ _) _ |- _ => PR
              | SU : Forall (summary_okM _ _ _ _ _ ?PR _ _ _ _ _ _) _ |- _ => PR
              | SU : Forall (summary_okP _ _ _ _ _ ?PR _) _ |- _ => PR
              | SU : forall AL', Forall (summary_okP _ AL' _ _ _ ?PR _) _ |- _ => PR
              | |- _ => constr:(@nil (list Z -> Prop))
              end in
  (* [comment removed for export] *)
  let props := eval hnf in props in
  pose (lxPR := props);
  (* [comment removed for export] *)
  let hctx := lazymatch goal with
              | HK : lx_heapkit _ ?P ?CW ?LH _ ?LB _ m ?mo |- _ => constr:((LB, P, CW, LH, mo))
              | |- _ => constr:((@nil (Z * Z), lx_nohp, lx_nocw, @nil (list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop), lx_nomodel))
              end in
  let lh := lazymatch hctx with (_, _, _, ?LH, _) => LH end in
  pose (lxLH := (lh : list (list (Z * Z) -> Z -> list (Z * Z) -> mem -> mem -> Prop)));
  lazymatch mode with Some (?AL, _) => lx_colZ constr:(al_sb AL) | None => idtac end;
  lx_colZs GS;
  lx_colRegs R; lx_colW_ivls W; lx_collect_hyps m;
  (* [comment removed for export] *)
  lx_col_links m;
  let lk := lx_re_links segs m in
  let ch := lazymatch lk with (?c, _, _) => c end in
  let pfk := lazymatch lk with (_, ?p, _) => p end in
  let srcs := lazymatch lk with (_, _, ?q) => q end in
  pose (lxMF := @nil mfact); pose (lxPF := pfk);
  lx_reify_hyps m;
  lx_prod_facts;
  lazymatch goal with _ : lx_spelling |- _ => lx_alias_regs R; lx_alias_ivls W | |- _ => idtac end;
  let zs := lx_getZ in let ws := lx_getW in let bs := lx_getB in let ls := lx_getL in
  let mf := lazymatch goal with a := ?v : list mfact |- _ => v end in
  let pf := lazymatch goal with a := ?v : list pfact |- _ => v end in
  let rs := lx_reRegs R in
  let nx := lx_len zs in let nl := lx_len ls in
  let Wr := lx_reW_ivls W in
  let genv := lx_reZs GS in let genv := eval cbv in (List.map enorm genv) in   (* [comment removed for export] *)
  let ops := lx_getO in
  let props := lazymatch goal with x := ?v : list (list Z -> Prop) |- _ => v end in
  let hrs := lazymatch goal with
             | SU : Forall (summary_okMR _ _ _ _ _ _ _ _ _ _ ?HR _ _) _ |- _ => HR
             | |- _ => constr:(@nil (list (Z * Z) -> list (Z * Z) -> list Z -> mem -> Prop))
             end in
  let E := lazymatch hctx with (?LB, ?P, ?CW, ?LH, ?mo) =>
             constr:(ENV zs ws bs ops ls (cons m0 nil) laws props LB P CW LH mo (@nil (list (Z * Z))) (hrs : lx_hress)) end in
  let ss := constr:(SSTN (PCz pc) rs mf pf Wr nx true nl) in
  (* [comment removed for export] *)
  let sb := lazymatch mode with
            | Some (?AL, _) =>
                match goal with
                | ASB : al_sb AL = ?z |- _ => let chk := match goal with _ => lx_is_lit z end in constr:(ELit z)
                | _ => lx_reZ constr:(al_sb AL)
                end
            | None => constr:(ELit 0)
            end in
  exact (E, ss, genv, sb, (ch, srcs)).

Definition lx_pack_ty := (env * sstate * list expr * expr * (list (elink * list mfact) * list mem))%type.

(* [comment removed for export] *)
Ltac lx_hpf_tac := first [ exact (hp_frame_nohp _) | assumption | lx_chg_obligL; assumption | fail 0 "lx: no hp_frame fact for the run's heap predicate" ].
Ltac lx_hbk_tac := first [ exact hp_blk_nocw | assumption | lx_chg_obligL; assumption | fail 0 "lx: no hp_blk fact for the run's heap predicate" ].
Ltac lx_hlaw_tac := first [ apply List.Forall_nil | assumption | lx_chg_obligL; assumption | fail 0 "lx: no hlaw_ok facts for the run's heap laws" ].

(* [comment removed for export] *)
Ltac lx_dump_on := fail.
Ltac lx_dump_run segs C pl genv pm ss :=
  tryif lx_dump_on then
    (let c := eval vm_compute in C in
     let p := eval vm_compute in pl in
     let g := eval vm_compute in genv in
     let b := eval vm_compute in pm in
     let s0 := eval vm_compute in ss in
     idtac "(*LXDUMP*) Definition dRUN := (@lx_runp lxh_empty" segs c p g b s0 ").")
  else idtac.

Ltac lx_run_core dbg kind pl mode segs Q R F pc fc m :=
  (* [comment removed for export] *)
  let HTv := match goal with
             | |- _ => let h := constr:(_ : lx_hints) in h
             | |- _ => constr:(lxh_empty)
             end in
  (* [comment removed for export] *)
  let pm := lazymatch goal with _ : lx_pruning |- _ => constr:(true) | |- _ => constr:(false) end in
  (* [comment removed for export] *)
  first [ lazymatch goal with MU : munch ?W _ m |- _ => lx_closed_ivls W end
        | match goal with MU : munch ?W _ m |- _ => lx_closed_ivls W end
        | pose proof (munch_refl [] m : munch [] m m);
          lazymatch goal with
          | WM : wmono segs m m |- _ => idtac
          | |- _ => pose proof (wmono_refl segs m : wmono segs m m)
          end ];
  let MU := match goal with MU : munch ?W ?m0 m |- _ => let _ := match goal with _ => lx_closed_ivls W end in MU end in
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  let m0 := lazymatch type of MU with munch _ ?m0 _ => m0 end in
  let WM := lazymatch goal with WM : wmono segs m0 m |- _ => WM | |- _ => fail 0 "lx: no hypothesis wmono segs" m0 m end in
  let MI := lazymatch goal with MI : mem_inv segs m |- _ => MI | |- _ => fail 0 "lx: no hypothesis mem_inv segs" m end in
  let GS := lazymatch goal with
            | SU : Forall (summary_okMR _ _ ?GS _ _ _ _ _ _ _ _ _ _) _ |- _ => GS
            | SU : Forall (summary_okM _ _ ?GS _ _ _ _ _ _ _ _ _) _ |- _ => GS
            | SU : Forall (summary_okP _ _ ?GS _ _ _ _) _ |- _ => GS
            | SU : forall AL', Forall (summary_okP _ AL' ?GS _ _ _ _) _ |- _ => GS
            | SU : Forall (summary_okL _ _ ?GS _ _ _) _ |- _ => GS
            | SU : forall AL', Forall (summary_okL _ AL' ?GS _ _ _) _ |- _ => GS
            | SU : Forall (summary_okO _ _ ?GS _ _) _ |- _ => GS
            | SU : forall AL', Forall (summary_okO _ AL' ?GS _ _) _ |- _ => GS
            | SU : Forall (summary_okG _ _ ?GS) _ |- _ => GS
            | SU : forall AL', Forall (summary_okG _ AL' ?GS) _ |- _ => GS
            | |- _ => constr:(@nil Z)
            end in
  let d0 := constr:(ltac:(lx_reify_pack mode segs R pc m m0 GS W) : lx_pack_ty) in
  let d := eval lazy zeta in d0 in
  lx_unseen;
  let E := lazymatch d with (?E, _, _, _, _) => E end in
  let ss0 := lazymatch d with (_, ?ss, _, _, _) => ss end in
  let genv := lazymatch d with (_, _, ?genv, _, _) => genv end in
  let sb := lazymatch d with (_, _, _, ?sb, _) => sb end in
  let ch := lazymatch d with (_, _, _, _, (?ch, _)) => ch end in
  let srcs := lazymatch d with (_, _, _, _, (_, ?q)) => q end in
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  let link_eval C := lazymatch ch with
                   | nil => constr:(tt)
                   | _ => lazymatch ss0 with SSTN _ _ ?mf0 ?pf0 _ _ _ _ => eval vm_compute in (@links_run HTv C pf0 ch mf0) end
                   end in
  let link_ss rr := lazymatch ch with
                   | nil => ss0
                   | _ => lazymatch ss0 with SSTN ?pc0 ?rs0 ?mf0 ?pf0 ?Wr0 ?nx0 ?sm0 ?nl0 =>
                            lazymatch rr with (?R, _) => constr:(SSTN pc0 rs0 R pf0 Wr0 nx0 sm0 nl0) end end
                   end in
  let link_report rr := lazymatch ch with
                   | nil => idtac
                   | _ => lazymatch ss0 with SSTN _ _ ?mf0 ?pf0 _ _ _ _ =>
                            let kept := lazymatch rr with (_, (?k, _)) => k end in
                            let dr := lazymatch rr with (_, (_, ?d)) => d end in
                            lazymatch dr with
                            | nil => idtac "lx: entry links: carried" kept "facts, dropped none"
                            | _ => let drd := eval lazy [List.map mfact_ok pfact_ok cden csden zdenp opden ez ew eb eo el em elaw eprop ehlaw blden hlawcli hlawopq ehres eblv ezl ewl ebl eol ell eml elw epr elb0 ehp ecw elh ecur elbl ehr ldenw ldenb wbytes pget List.nth wden fst snd List.app N.to_nat Pos.pred Pos.pred_double Pos.succ] in
                                                (List.map (mfact_ok segs lx_no_layout (fun _ => True) E m) dr) in
                                   idtac "lx: entry links: carried" kept "facts; DROPPED (stated here at the entry memory for reading; they held at an older one):" drd
                            end end
                   end in
  let ops := lazymatch E with ENV _ _ _ ?ops _ _ _ _ _ _ _ _ _ _ _ => ops end in
  let laws := lazymatch E with ENV _ _ _ _ _ _ ?laws _ _ _ _ _ _ _ _ => laws end in
  let props := lazymatch E with ENV _ _ _ _ _ _ _ ?props _ _ _ _ _ _ _ => props end in
  let lb0 := lazymatch E with ENV _ _ _ _ _ _ _ _ ?x _ _ _ _ _ _ => x end in
  let hp := lazymatch E with ENV _ _ _ _ _ _ _ _ _ ?x _ _ _ _ _ => x end in
  let cw := lazymatch E with ENV _ _ _ _ _ _ _ _ _ _ ?x _ _ _ _ => x end in
  let lh := lazymatch E with ENV _ _ _ _ _ _ _ _ _ _ _ ?x _ _ _ => x end in
  let hrs := lazymatch E with ENV _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?x => x end in
  let clr := idtac in
  (* [comment removed for export] *)
  let forall_tac := idtac;
      lazymatch goal with |- @Forall ?A ?P ?l => let l' := eval cbv beta iota delta [s_mf s_pf SSTN SST] in l in change (@Forall A P l') end;
      repeat (lazymatch goal with |- Forall _ (cons _ _) => apply List.Forall_cons; [lx_close_factF|] end);
      (apply List.Forall_nil) in
  (* [comment removed for export] *)
  let chain_tac := idtac;
      repeat (lazymatch goal with
              | |- chain_ok _ _ _ (cons _ _) _ _ => split; [ forall_tac | split; [ first [ assumption | lx_chg_obligL; assumption ] | ] ]
              end);
      (exact I) in
  (* [comment removed for export] *)
  let mforall_tac := idtac;
      lazymatch goal with |- @Forall ?A ?P ?l => let l' := eval cbv beta iota delta [s_mf SSTN SST] in l in change (@Forall A P l') end;
      lazymatch ch with
      | nil => forall_tac
      | _ =>
        lazymatch goal with |- Forall (mfact_ok _ (g_L ?g) (g_CS _) ?e ?mx) ?R =>
          lazymatch goal with LXCFG : cfg_ok _ ?C0 _, LXPF : Forall (pfact_ok _ _) ?pf0, LXHPF : hp_frame _ _ _ |- _ =>
            lazymatch ss0 with SSTN _ _ ?mf0 _ _ _ _ _ =>
              let EQ := fresh "LXEQ" in
              assert (EQ : @links_entry HTv C0 pf0 ch mf0 = R) by (vm_cast_no_check (@eq_refl (list mfact) R));
              rewrite <- EQ; clear EQ;
              refine (@entry_links_ok HTv segs g C0 e pf0 LXCFG LXPF LXHPF ch srcs mx mf0 _ _); [ forall_tac | chain_tac ]
            end
          end
        end
      end in
  let st_ok_tac := idtac;
      lazymatch goal with |- st_ok _ ?g ?e ?ss ?ms =>
        refine (lx_st_ok_intro segs g e ss ms m _ _ _ _ _ MI _);
        [ first [ reflexivity | lx_chg_obligL; reflexivity ]
        | mforall_tac
        | first [ lazymatch goal with LXPF : Forall (pfact_ok _ _) _ |- _ => exact LXPF end | forall_tac ]
        | first [ exact MU | lx_chg_obligL; exact MU ]
        | first [ exact WM | lx_chg_obligL; exact WM ]
        | first [ exact (fun _ => eq_refl) | lx_chg_obligL; intros _; reflexivity ] ]
      end in
  (* [comment removed for export] *)
  let link_pre_tac g e C cfgt := lazymatch ch with
      | nil => idtac
      | _ => lazymatch ss0 with SSTN _ _ _ ?pf0 _ _ _ _ =>
               assert (LXCFG : cfg_ok g C e) by cfgt;
               assert (LXPF : Forall (pfact_ok (g_CS g) e) pf0) by forall_tac;
               assert (LXHPF : hp_frame segs (ehp e) (ecw e)) by lx_hpf_tac
             end
      end in
  let cfg_use_tac cfgt := first [ lazymatch goal with LXCFG : cfg_ok _ _ _ |- _ => exact LXCFG end | cfgt ] in
  let cast_tac t := idtac; vm_cast_no_check (@eq_refl rtree t) in
  let genv_tac := idtac; (unfold genv_okp; split; [repeat (apply List.Forall2_cons; [first [reflexivity | lx_chg_obligL; reflexivity]|]); apply List.Forall2_nil
                                                  | split; [split; [|split]; reflexivity
                                                          | split; [split; [|split; [|split; [|split]]]; reflexivity | split; [lx_hpf_tac| split; [lx_hbk_tac| lx_hlaw_tac]]]]]) in
  (* [comment removed for export] *)
  let sums_tac := idtac; first [ apply List.Forall_nil
                               | lazymatch goal with SU : Forall (summary_okMR _ _ _ _ _ _ _ _ _ _ _ _ _) _ |- _ => exact (sums_ok_atM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SU) end
                               | lazymatch goal with SU : Forall (summary_okM _ _ _ _ _ _ _ _ _ _ _ _) _ |- _ => exact (sums_ok_atM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SU) end
                               | lazymatch goal with SU : Forall (summary_okP _ _ _ _ _ _ _) _ |- _ => exact (sums_ok_atP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SU) end
                               | lazymatch goal with SU : forall AL', Forall (summary_okP _ AL' _ _ _ _ _) _ |- _ => exact (sums_ok_atP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SU _)) end
                               | lazymatch goal with SU : Forall (summary_okL _ _ _ _ _ _) _ |- _ => exact (sums_ok_atL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SU) end
                               | lazymatch goal with SU : forall AL', Forall (summary_okL _ AL' _ _ _ _) _ |- _ => exact (sums_ok_atL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SU _)) end
                               | lazymatch goal with SU : Forall (summary_okO _ _ _ _ _) _ |- _ => exact (sums_ok_atO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SU) end
                               | lazymatch goal with SU : forall AL', Forall (summary_okO _ AL' _ _ _) _ |- _ => exact (sums_ok_atO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SU _)) end
                               | lazymatch goal with SU : Forall (summary_okG _ _ _) _ |- _ => exact (sums_ok_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SU) end
                               | lazymatch goal with SU : forall AL', Forall (summary_okG _ AL' _) _ |- _ => exact (sums_ok_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SU _)) end
                               | lazymatch goal with SU : Forall (summary_ok _ _) _ |- _ => exact (sums_ok_at0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SU) end
                               | lazymatch goal with SU : forall AL', Forall (summary_ok _ AL') _ |- _ => exact (sums_ok_at0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SU _)) end
                               | lazymatch goal with SU : Forall _ (p_sums _) |- _ => exact SU end
                               (* [comment removed for export] *)
                               | lazymatch goal with
                                 | SU : Forall (summary_okM _ _ _ _ _ _ _ _ _ _ (tgt_aevtM _ ?Q1) _) _ |- Forall (summary_at _ _ _ _ _ _ _ _ _ _ _ _ _ (tgt_aevtM _ ?Q2)) _ =>
                                     first [ constr_eq Q1 Q2
                                           | fail 0 "lx: the summaries hypothesis is stated for the post" Q1 "but the goal's post is" Q2 "(pose SU from the goal AFTER your last rewrite of it)" ]
                                 end;
                                 lazymatch goal with
                                 | SU : Forall (summary_okM _ _ ?GS1 ?O1 ?L1 ?P1 ?B1 ?H1 ?C1 ?LH1 _ _) _ |- Forall (summary_at _ _ _ _ ?GS2 ?O2 ?L2 ?P2 ?B2 ?H2 ?C2 ?LH2 _ _) _ =>
                                     fail 0 "lx: the summaries hypothesis (summary_okM) does not fit the run: its GS/OPS/LAWS/PROPS/LB0/HP/CW/LH =" GS1 O1 L1 P1 B1 H1 C1 LH1 "vs the run's" GS2 O2 L2 P2 B2 H2 C2 LH2
                                 end
                               | fail 0 "lx: the plan has summaries: need a hypothesis  Forall (summary_ok segs AL) (p_sums pl)  or  Forall (summary_okG segs AL GS) (p_sums pl)  (see lx_run_tacS)" ] in
  (* [comment removed for export] *)
  let run_tac := idtac; lx_clear_dups; try clear MU; try clear WM;
      try (lazymatch goal with H : cfg_ok _ _ _ |- _ => clear H end);
      try (lazymatch goal with H : Forall (pfact_ok _ _) _ |- _ => clear H end);
      try (lazymatch goal with H : hp_frame _ (ehp _) (ecw _) |- _ => clear H end);
      lazymatch goal with |- oblig _ _ _ _ ?K => let k := fresh "lxK" in set (k := K : lx_kont) end;
      lx_unfold_spine in
  let dbg_tac C := idtac;
      lx_clear_dups;
      let rr := link_eval C in let ss := link_ss rr in link_report rr;
      pose (lxE := E); pose (lxC := C); pose (lxSS := ss);
      lx_dump_run segs C pl genv pm ss;
      let t := eval vm_compute in (@lx_runp HTv segs C pl genv pm ss) in pose (lxT := t);
      let f := eval vm_compute in (rt_fails t []) in pose (lxFails := f);
      let l := eval vm_compute in (rt_leaf_pcs t []) in pose (lxLeaves := l) in
  lazymatch mode with
  | Some (?AL, ?CS) =>
      let CSOK := lazymatch goal with H : cs_ok AL CS |- _ => H | |- _ => fail 0 "lx: need a hypothesis (cs_ok" AL CS ")" end in
      let ALWF := lazymatch goal with H : al_wf AL |- _ => H | |- _ => fail 0 "lx: need a hypothesis (al_wf" AL ")" end in
      (* [comment removed for export] *)
      let G := constr:(GL AL CS F fc m0 m) in
      let A := constr:(ACFG (enorm sb) li_lo li_hi li_got li_gsb) in
      let C := eval vm_compute in (LXC (Some A)) in
      (* [comment removed for export] *)
      lazymatch C with
      | LXC (Some (ACFG _ ?lo ?hi ?got ?gsb)) =>
          first [ lx_is_lit lo; lx_is_lit hi; lx_is_lit got; lx_is_lit gsb
                | fail 100 "lx: the image instance (lximg: li_lo li_hi li_got li_gsb) does not compute to literals:" lo hi got gsb "— make it transparent (pose (lxi := ..) / Let / Defined), never pose proof / Qed" ]
      end;
      clr;
      lazymatch dbg with
      | true => dbg_tac C
      | false =>
      let rr := link_eval C in let ss := link_ss rr in link_report rr;
      lx_dump_run segs C pl genv pm ss;
      let t := eval vm_compute in (@lx_runp HTv segs C pl genv pm ss) in
      lx_report_fails t;
      (* [comment removed for export] *)
      let cfg_tac := idtac;
          first [ refine (lx_cfg_ok_introA segs AL _ _ _ _ eq_refl CSOK ALWF _); first [reflexivity | symmetry; assumption | assumption | lx_chg_obligL; first [reflexivity | symmetry; assumption | assumption]]
                | lx_unfold_obligL; cbn [cfg_ok c_acc g_L g_CS];
                  pose proof (@li_ok segs AL _) as LIOK;
                  split; [exact CSOK| split; [exact ALWF| split; [first [reflexivity | symmetry; assumption | assumption] | exact LIOK]]] ] in
      lazymatch kind with
      | 0 => let g := fresh "lxG" in pose (g := G); let e := fresh "lxE" in pose (e := E);
             link_pre_tac g e C cfg_tac;
             eapply (@lx_sound_t HTv segs g C pl genv pm GS ops laws props lb0 hp cw lh hrs e ss _ Q t); [ sums_tac | genv_tac | cfg_use_tac cfg_tac | reflexivity | st_ok_tac | cast_tac t | run_tac ]
      | 1 => lazymatch goal with
             | KL : kinv_laws ?AI CS ?K, LAWS : ainv_laws AL ?AI |- _ =>
                 let g := fresh "lxG" in pose (g := G); let e := fresh "lxE" in pose (e := E);
                 link_pre_tac g e C cfg_tac;
                 eapply (@lx_sound_aevtA_t HTv segs g C pl genv pm GS ops laws props lb0 hp cw lh hrs e ss _ AI K Q t LAWS KL); [ sums_tac | genv_tac | cfg_use_tac cfg_tac | reflexivity | st_ok_tac | cast_tac t | run_tac ]
             | |- _ => fail 0 "lx: aevtA mode needs hypotheses kinv_laws AI CS K and ainv_laws AL AI"
             end
      end
      end
  | None =>
      let G := constr:(GL lx_no_layout (fun _ : Z => True) F fc m0 m) in
      let C := constr:(LXC None) in
      clr;
      lazymatch dbg with
      | true => dbg_tac C
      | false =>
      let rr := link_eval C in let ss := link_ss rr in link_report rr;
      lx_dump_run segs C pl genv pm ss;
      let t := eval vm_compute in (@lx_runp HTv segs C pl genv pm ss) in
      lx_report_fails t;
      let g := fresh "lxG" in pose (g := G); let e := fresh "lxE" in pose (e := E);
      let cfg_tac := idtac; exact (fun _ : Z => I) in
      link_pre_tac g e C cfg_tac;
      lazymatch kind with
      | 2 => (* [comment removed for export] *)
             eapply (@lx_sound_aevtM_t HTv segs g C pl genv pm GS ops laws props lb0 hp cw lh hrs e ss _ Q t);
             [ sums_tac
             | genv_tac
             | (* [comment removed for export] *) cfg_use_tac cfg_tac
             | (* [comment removed for export] *) reflexivity
             | st_ok_tac
             | cast_tac t
             | (* [comment removed for export] *) first [ assumption | lx_chg_obligL; assumption | fail 0 "lx: heap-class run: a hypothesis  MOK <the goal's model>  is needed" ]
             | run_tac ]
      | _ =>
      eapply (@lx_sound_plain_t HTv segs g C pl genv pm GS ops laws props lb0 hp cw lh hrs e ss _ Q t);
      [ sums_tac
      | genv_tac
      | (* [comment removed for export] *) cfg_use_tac cfg_tac
      | (* [comment removed for export] *) reflexivity
      | st_ok_tac
      | cast_tac t
      | run_tac ]
      end
      end
  end.

(* [comment removed for export] *)
Ltac lx_run_gen dbg pl :=
  lazymatch goal with
  | |- evtA ?segs ?AL ?CS ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m (seg_rom _)) =>
      lx_prep segs AL m;
      lx_run_core dbg 0 pl constr:(Some (AL, CS)) segs Q R F pc fc m
  | |- aevtA ?segs ?K ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m (seg_rom _)) =>
      (* [comment removed for export] *)
      lazymatch goal with
      | KL : kinv_laws ?AI ?CS K, LAWS : ainv_laws ?AL ?AI |- _ =>
          lx_prep segs AL m;
          lx_run_core dbg 1 pl constr:(Some (AL, CS)) segs Q R F pc fc m
      | |- _ => fail 0 "lx: aevtA goal: pose (kinv_laws AI CS K) and (ainv_laws AL AI) first (ARt: KF_kinv / AIh_laws)"
      end
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m (seg_rom _)) =>
      lx_prep segs lx_no_layout m;
      lx_run_core dbg 0 pl constr:(@None (asan_layout * (Z -> Prop))) segs Q R F pc fc m
  | |- aevtM ?segs ?mo ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m (seg_rom _)) =>
      lazymatch goal with
      | HK : lx_heapkit _ _ _ _ _ _ _ m mo |- _ =>
          (* [comment removed for export] *)
          let h := fresh "LXHK" in pose proof HK as h;
          let a := fresh "LXHPF" in let b := fresh "LXHBK" in let c := fresh "LXHLAW" in
          destruct h as [_ [_ [a [b c]]]];
          lx_prep segs lx_no_layout m;
          lx_run_core dbg 2 pl constr:(@None (asan_layout * (Z -> Prop))) segs Q R F pc fc m;
          try clear a b c
      | MK : MOK mo |- _ =>
          (* [comment removed for export] *)
          apply (lx_aevtM_evt segs mo Q _ MK); lx_run_gen dbg pl
      | |- _ => fail 0 "lx: aevtM goal: a hypothesis  MOK" mo " is needed (Lib/AEvt.MOK)"
      end
  end.

Ltac lx_run_tac pl := lx_run_gen false pl.

(* [comment removed for export] *)
Ltac lx_run_tacS pl H :=
  let LXSUMS := fresh "LXSUMS" in pose proof H as LXSUMS; lx_run_gen false pl; try clear LXSUMS.

(* [comment removed for export] *)
Ltac lx_debug pl := lx_run_gen true pl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_split_len H :=
  let h := fresh "LXarr" in pose proof (proj1 H) as h;
  let l := fresh "LXlen" in pose proof (proj2 H) as l;
  (* [comment removed for export] *)
  move h after H; move l after h; clear H; rename h into H.
Ltac lx_leaf_finish lxm :=
  repeat match goal with
         | H : bytes_at _ _ _ _ /\ _ |- _ => lx_split_len H
         | H : u8arr _ _ _ _ /\ _ |- _ => lx_split_len H
         | H : u32arr _ _ _ _ /\ _ |- _ => lx_split_len H
         | H : u64arr _ _ _ _ /\ _ |- _ => lx_split_len H
         end;
  (* [comment removed for export] *)
  try match goal with H : lxm = _ |- _ => rename H into LXSAME end;
  (* [comment removed for export] *)
  try (lazymatch goal with |- MOK ?mo -> aevtM _ _ _ _ => let h := fresh "LXMOK" in intros h end);
  try (lazymatch goal with |- aevtM _ ?mo _ _ => match goal with H : MOK mo |- _ => rename H into LXMOK end end);
  try (lazymatch goal with |- aevtM _ ?mo _ (MS _ _ _ _ _ ?mx _) => match goal with H : lx_heapkit _ _ _ _ _ _ _ mx mo |- _ => rename H into LXHK end end).
Ltac lx_tree :=
  lazymatch goal with
  | |- (_ = true -> _) /\ (_ = false -> _) =>
      (* [comment removed for export] *)
      split; [ let h := fresh "LXKT" in intros h; lx_unfold_in h; lx_tree
             | let h := fresh "LXKF" in intros h; lx_unfold_in h; lx_tree ]
  (* [comment removed for export] *)
  | |- oblig _ _ _ _ _ /\ _ => split; lx_tree
  | |- leaf_oblig _ _ _ _ _ /\ _ => split; lx_tree
  | |- (_ /\ _) /\ _ => split; lx_tree
  | |- (forall _ : Z, _) /\ _ => split; lx_tree
  | |- (forall _ : list word, _) /\ _ => split; lx_tree
  | |- (forall _ : mem, _) /\ _ => split; lx_tree
  | |- True /\ _ => split; lx_tree
  | |- False /\ _ => fail 0 "lx: a failed node in the tree (lx_debug shows lxFails)"
  | |- forall _ : Z, _ => let v := fresh "lxv" in intro v; lx_bind_env v; lx_tree
  (* [comment removed for export] *)
  | |- forall _ : list word, _ => let l := fresh "lxl" in intro l; lx_bind_envl l; lx_tree
  (* [comment removed for export] *)
  | |- forall _ : mem, forall _ : mem, forall _ : Model, forall _ : list (Z * Z), _ =>
      let mc := fresh "lxmc" in let mp := fresh "lxmp" in let mo := fresh "lxmo" in let lb := fresh "lxlb" in
      intros mc mp mo lb; lx_bind_heap mc mp mo lb; lx_tree
  (* [comment removed for export] *)
  | |- forall _ : mem, forall _ : mem, _ =>
      let mc := fresh "lxmc" in let mp := fresh "lxmp" in intros mc mp; lx_bind_mems mc mp; lx_tree
  (* [comment removed for export] *)
  | |- leaf_oblig _ _ _ _ _ =>
      let e := lx_letE in let g := lx_letG in let k := lx_letK in
      let fd := lx_fold_default in
      let fm := lazymatch goal with _ : lx_folding |- _ => constr:(true) | |- _ => fd end in
      lazymatch fm with
      | true =>
          (* [comment removed for export] *)
          lazymatch goal with |- ?G => let t := eval lazy [leaf_oblig mf_tele pf_tele s_mf s_pf s_W s_same s_ref s_nm] in G in change t end;
          lazymatch goal with
          | |- forall _ : mem, _ =>
              let mx := fresh "lxm" in intro mx; intros;
              repeat match goal with
                     | H : mfact_ok _ _ _ _ _ _ |- _ => lx_unfold_inEG H e g
                     | H : pfact_ok _ _ _ |- _ => lx_unfold_inEG H e g
                     | H : munch (wden _ _) _ _ |- _ => lx_unfold_inEG H e g
                     | H : wmono _ (refm _ _) _ |- _ => lx_unfold_inEG H e g
                     | H : mx = g_me _ |- _ => lx_unfold_inEG H e g
                     | H : MOK (ecur _) |- _ => lx_unfold_inEG H e g
                     end;
              lx_chg_leafEGK e g k;
              lx_leaf_finish mx; lx_clear_lets
          end
      | false =>
          (* [comment removed for export] *)
          lx_chg_leafEGK e g k;
          lazymatch goal with
          | |- forall _ : mem, _ =>
              let mx := fresh "lxm" in intro mx; intros; lx_leaf_finish mx; lx_clear_lets
          end
      end
  (* [comment removed for export] *)
  | |- forall _ : mem, _ => let mx := fresh "lxm" in intro mx; intros; lx_leaf_finish mx
  | |- True => exact I
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac lx_weq :=
  lazymatch goal with
  | |- @eq (bv _) _ _ => first [reflexivity | f_equal; lia | apply w64_eq; cbn; lia]
  end.

(* [comment removed for export] *)
Lemma lx_bvu64 : forall x, bv_unsigned (Z_to_bv 64 x) = zlow 64 x.
Proof. exact zlow64_unsigned. Qed.

(* [comment removed for export] *)
Ltac lx_lia :=
  rewrite ?lx_bvu64;
  first [ lia
        | unfold zlow, zswrap; lia
        | progress (unfold zlow, zswrap in * ); lia ].


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_leaf_aevtM :=
  lazymatch goal with
  | |- evt _ (fun _ => aevtM _ _ _ _) _ => apply evt_done; lazymatch goal with |- ?G => let t := eval cbv beta in G in change t end
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac lx_chg_hnf := lazymatch goal with |- ?G => let t := eval hnf in G in change t end.
Ltac lx_chg_beta := lazymatch goal with |- ?G => let t := eval cbv beta in G in change t end.
Ltac lx_post :=
  lx_leaf_aevtM;
  first [apply evtA_done | apply evt_done | (apply aevtA_done; intros ?mo' [?HK' ?MF']) | (apply aevtM_done; lx_chg_beta) | idtac];
  lx_chg_hnf; lx_exs; lx_ands; [> reflexivity | ..]; try assumption.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_sum_unfold :=
  lazy [summary_valid summary_validG summary_validG1 summary_validO summary_validL summary_validP sum_valid_at sum_frame SUM SUMG SUMX SUMXL sum_postP zforall zexists bforall wforall lforall lexists
        summary_validH summary_validHR sum_validH_at heap_caseK eff_list law_list eff_pre eff_post su_heap HC hc_law hc_sp hc_hreq hc_eff hc_alt hc_hpost
        blforall hr_tele lx_hres eblv ehres hres_d elbl ehr
        gb_tele rb_tele mf_tele pf_tele oq_tele oq_conj mf_conj pf_conj bb_facts
        rclob rdw rgetZ rsetZ List.nth
        su_pc su_acc su_np su_nr su_nb su_rbind su_gbind su_sb su_mbind su_stk su_bbind su_req su_pre su_W su_clob su_mpost su_post su_oreq su_law
        su_nl su_nla su_nrl lmax lloc_of List.fold_right Nat.max Nat.sub
        mfact_ok pfact_ok cden csden zdenp opden ldenw ldenb
        ez ew eb el eprop ezl ewl ebl ell epr pget pset pad_set g_L g_CS g_F g_fc g_m0 wden List.map List.app fst snd
        Pos.pred Pos.pred_double Pos.succ Pos.eqb Pos.to_nat Pos.iter_op Nat.add Nat.pred];
  (* [comment removed for export] *)
  repeat match goal with |- context [N.to_nat ?w] => lazymatch w with N0 => idtac | Npos _ => idtac end;
                                                     let k := eval cbv in (N.to_nat w) in change (N.to_nat w) with k end;
  (* [comment removed for export] *)
  try (lazymatch goal with |- forall _ : list (mem -> Prop), _ => intros ?LXOPS end);
  try (lazymatch goal with |- forall _ : list (list (Z * Z) -> mem -> mem -> Prop), _ => intros ?LXLAWS end);
  try (lazymatch goal with |- forall _ : list (list Z -> Prop), _ => intros ?LXPROPS end).

(* [comment removed for export] *)
Lemma lx_uw64 : forall z, 0 <= z -> z <= two64 - 1 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H1 H2. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus, two64 in *. cbn in *. lia. Qed.

Lemma lx_w8u : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Ltac lx_unify_val n a b :=
  lazymatch b with
  | Z_to_bv n ?e => first [ is_evar e; lazymatch a with Z_to_bv n ?x => unify e x | _ => unify e (bv_unsigned a) end | idtac ]
  | _ => idtac
  end.
Ltac lx_unify_reg a b := lx_unify_val 64%N a b.
Ltac lx_sum_regs :=
  lazymatch goal with
  | |- MS (mkR ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20 ?a21 ?a22 ?a23 ?a24 ?a25 ?a26 ?a27 ?a28 ?a29 ?a30 ?a31) _ _ _ _ ?ma _
       = MS (mkR ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 ?b8 ?b9 ?b10 ?b11 ?b12 ?b13 ?b14 ?b15 ?b16 ?b17 ?b18 ?b19 ?b20 ?b21 ?b22 ?b23 ?b24 ?b25 ?b26 ?b27 ?b28 ?b29 ?b30 ?b31) _ _ _ _ ?mb _ =>
      lx_unify_reg a1 b1; lx_unify_reg a2 b2; lx_unify_reg a3 b3; lx_unify_reg a4 b4; lx_unify_reg a5 b5; lx_unify_reg a6 b6;
      lx_unify_reg a7 b7; lx_unify_reg a8 b8; lx_unify_reg a9 b9; lx_unify_reg a10 b10; lx_unify_reg a11 b11; lx_unify_reg a12 b12;
      lx_unify_reg a13 b13; lx_unify_reg a14 b14; lx_unify_reg a15 b15; lx_unify_reg a16 b16; lx_unify_reg a17 b17; lx_unify_reg a18 b18;
      lx_unify_reg a19 b19; lx_unify_reg a20 b20; lx_unify_reg a21 b21; lx_unify_reg a22 b22; lx_unify_reg a23 b23; lx_unify_reg a24 b24;
      lx_unify_reg a25 b25; lx_unify_reg a26 b26; lx_unify_reg a27 b27; lx_unify_reg a28 b28; lx_unify_reg a29 b29; lx_unify_reg a30 b30;
      lx_unify_reg a31 b31; first [is_evar mb; unify mb ma | idtac]; rewrite ?lx_w64u; reflexivity
  end.
Ltac lx_unify_cell a b :=
  lazymatch b with
  | C8 ?v => lazymatch a with C8 ?u => lx_unify_val 64%N u v | _ => idtac end
  | C4 ?v => lazymatch a with C4 ?u => lx_unify_val 64%N u v | _ => idtac end
  | C2 ?v => lazymatch a with C2 ?u => lx_unify_val 64%N u v | _ => idtac end
  | C1 ?v => lazymatch a with C1 ?u => lx_unify_val 8%N u v | _ => idtac end
  | _ => idtac
  end.
Ltac lx_unify_cells xs ys :=
  lazymatch ys with
  | nil => idtac
  | cons ?y ?ys' => lazymatch xs with cons ?x ?xs' => lx_unify_cell x y; lx_unify_cells xs' ys' | _ => idtac end
  end.
(* [comment removed for export] *)
Ltac lx_sum_fact :=
  lazymatch goal with
  | |- rw_cells ?sg ?mm ?A ?cs =>
      match goal with H : rw_cells sg mm A ?cs' |- _ => lx_unify_cells cs' cs; rewrite ?lx_w64u, ?lx_w8u; exact H end
  | |- bytes_at ?sg ?mm ?A ?bs => match goal with H : bytes_at sg mm A _ |- _ => exact H end
  | |- stk ?sg ?mm _ _ => match goal with H : stk sg mm _ _ |- _ => exact H end
  (* [comment removed for export] *)
  | |- u32arr ?sg ?mm ?A _ /\ _ => split; [match goal with H : u32arr sg mm A _ |- _ => exact H end | first [lia | idtac]]
  | |- u64arr ?sg ?mm ?A _ /\ _ => split; [match goal with H : u64arr sg mm A _ |- _ => exact H end | first [lia | idtac]]
  | |- u8arr ?sg ?mm ?A _ /\ _ => split; [match goal with H : u8arr sg mm A _ |- _ => exact H end | first [lia | idtac]]
  | |- bytes_at ?sg ?mm ?A _ /\ _ => split; [match goal with H : bytes_at sg mm A _ |- _ => exact H end | first [lia | idtac]]
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lx_wz a := lazymatch a with Z_to_bv 64 _ => a | _ => constr:(Z_to_bv 64 (bv_unsigned a)) end.
Ltac lx_aevtM_zregs :=
  lazymatch goal with
  | |- aevtM ?sg ?mo ?Q (MS (mkR ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20 ?a21 ?a22 ?a23 ?a24 ?a25 ?a26 ?a27 ?a28 ?a29 ?a30 ?a31) ?F ?pc ?fc ?st ?m ?ro) =>
      let b1 := lx_wz a1 in let b2 := lx_wz a2 in let b3 := lx_wz a3 in let b4 := lx_wz a4 in let b5 := lx_wz a5 in let b6 := lx_wz a6 in
      let b7 := lx_wz a7 in let b8 := lx_wz a8 in let b9 := lx_wz a9 in let b10 := lx_wz a10 in let b11 := lx_wz a11 in let b12 := lx_wz a12 in
      let b13 := lx_wz a13 in let b14 := lx_wz a14 in let b15 := lx_wz a15 in let b16 := lx_wz a16 in let b17 := lx_wz a17 in
      let b18 := lx_wz a18 in let b19 := lx_wz a19 in let b20 := lx_wz a20 in let b21 := lx_wz a21 in let b22 := lx_wz a22 in
      let b23 := lx_wz a23 in let b24 := lx_wz a24 in let b25 := lx_wz a25 in let b26 := lx_wz a26 in let b27 := lx_wz a27 in
      let b28 := lx_wz a28 in let b29 := lx_wz a29 in let b30 := lx_wz a30 in let b31 := lx_wz a31 in
      (* [comment removed for export] *)
      replace (MS (mkR a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31) F pc fc st m ro)
         with (MS (mkR a1 a2 a3 a4 b5 b6 b7 a8 a9 b10 b11 b12 b13 b14 b15 b16 b17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 b28 b29 b30 b31) F pc fc st m ro)
         by (rewrite ?lx_w64u; reflexivity)
  end.

(* [comment removed for export] *)
Ltac lx_sum_post :=
  lx_exs; lx_ands; [> lx_sum_regs | ..]; lx_sum_fact; first [ eassumption | lia | idtac ].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lx_opq_intro : forall segs L CS (P : mem -> Prop) (Wr : Z -> Prop) (OK SH : list ivl) m,
  P m ->
  (forall W m1 m2, P m1 -> munch W m1 m2 -> wmono segs m1 m2 ->
     Forall (fun iv => forall a, fst iv <= a < snd iv -> Wr a) W -> P m2) ->
  (forall lo hi a, In (lo, hi) OK -> lo <= a < hi -> Wr a) ->
  (forall lo hi c, In (lo, hi) SH -> lo <= c < hi -> CS c -> Wr (shadow_of L c)) ->
  lx_opq segs L CS P OK SH m.
Proof.
  intros segs L CS P Wr OK SH m HP LAW HOK HSH. split; [exact HP|].
  intros W m1 m2 H1 MU WM HA. apply (LAW W m1 m2 H1 MU WM).
  eapply Forall_impl; [|exact HA]. intros [lo hi] [X|X] a Ha; cbn [fst snd] in *.
  - destruct X as (lo' & hi' & Hin & H1' & H2'). eapply HOK; [exact Hin| lia].
  - destruct (X a Ha) as (c & lo' & hi' & Hin & Hc & HCS & ->). eapply HSH; eauto.
Qed.

Lemma lx_opq_holds : forall segs L CS P OK SH m, lx_opq segs L CS P OK SH m -> P m.
Proof. intros * [H _]. exact H. Qed.

(* [comment removed for export] *)
Lemma lx_opq_transport : forall segs L CS P OK SH m m' W,
  lx_opq segs L CS P OK SH m -> munch W m m' -> wmono segs m m' -> Forall (opq_allowed L CS OK SH) W ->
  lx_opq segs L CS P OK SH m'.
Proof. intros * [H LAW] MU WM HA. split; [exact (LAW W m m' H MU WM HA)| exact LAW]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_lia_colT T :=
  lazymatch T with
  | ?A /\ ?B => lx_lia_colT A; lx_lia_colT B
  | Z.le ?a ?b => lx_colZ a; lx_colZ b
  | Z.lt ?a ?b => lx_colZ a; lx_colZ b
  | Z.ge ?a ?b => lx_colZ a; lx_colZ b
  | Z.gt ?a ?b => lx_colZ a; lx_colZ b
  | @eq Z (Z.modulo ?a ?k) Z0 => lx_is_lit k; lx_colZ a
  | @eq Z ?a ?b => lx_colZ a; lx_colZ b
  | ?z = 0 \/ ?a <= ?b \/ ?c <= ?d => lx_colZ z; lx_colZ a; lx_colZ b; lx_colZ c; lx_colZ d
  | ?a <= ?b \/ ?c <= ?d => lx_colZ a; lx_colZ b; lx_colZ c; lx_colZ d
  end.
Ltac lx_lia_reT T :=
  lazymatch T with
  | ?A /\ ?B => let x := lx_lia_reT A in let y := lx_lia_reT B in eval cbv beta iota delta [List.app] in (x ++ y)
  | Z.le ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:(cons (FLe x y) nil)
  | Z.lt ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:(cons (FLt x y) nil)
  | Z.ge ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:(cons (FLe y x) nil)
  | Z.gt ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:(cons (FLt y x) nil)
  | @eq Z (Z.modulo ?a ?k) Z0 => let x := lx_reZ a in let j := lx_log2N k in constr:(cons (FAl x j) nil)
  | @eq Z ?a ?b => let x := lx_reZ a in let y := lx_reZ b in constr:(cons (FEq x y) nil)
  | ?z = 0 \/ ?a <= ?b \/ ?c <= ?d =>
      let z' := lx_reZ z in let a' := lx_reZ a in let b' := lx_reZ b in let c' := lx_reZ c in let d' := lx_reZ d in
      constr:(cons (FOr3z z' a' b' c' d') nil)
  | ?a <= ?b \/ ?c <= ?d =>
      let a' := lx_reZ a in let b' := lx_reZ b in let c' := lx_reZ c in let d' := lx_reZ d in
      constr:(cons (FOr2 a' b' c' d') nil)
  end.

(* [comment removed for export] *)
Ltac lx_lia_goal_terms G :=
  lazymatch G with
  | Z.le ?a ?b => constr:(cons (b - a) nil)
  | Z.lt ?a ?b => constr:(cons (b - a - 1) nil)
  | Z.ge ?a ?b => constr:(cons (a - b) nil)
  | Z.gt ?a ?b => constr:(cons (a - b - 1) nil)
  | False => constr:(cons (-1) nil)
  | Z.le ?a ?b \/ Z.le ?c ?d => constr:(cons (b - a) (cons (d - c) nil))
  | Z.lt ?a ?b \/ Z.le ?c ?d => constr:(cons (b - a - 1) (cons (d - c) nil))
  | Z.le ?a ?b \/ Z.lt ?c ?d => constr:(cons (b - a) (cons (d - c - 1) nil))
  | Z.lt ?a ?b \/ Z.lt ?c ?d => constr:(cons (b - a - 1) (cons (d - c - 1) nil))
  end.

Definition lx_lia_hyp_ty := @sigT Prop (fun P => P).

(* [comment removed for export] *)
Ltac lx_lia_collect :=
  repeat match goal with
         | H : ?T |- _ => lazymatch T with lx_seen _ => fail | _ => lx_lia_colT T; change (lx_seen T) in H end
         end.
Ltac lx_lia_hyps acc :=
  match goal with
  | H : lx_seen ?T |- _ =>
      let u := match goal with _ => change T in H end in
      let fs := lx_lia_reT T in
      lx_lia_hyps constr:(cons (@pair (list pfact) lx_lia_hyp_ty fs (@existT Prop (fun P : Prop => P) T H)) acc)
  | |- _ => acc
  end.
Ltac lx_lia_sel l idxs acc :=
  (* [comment removed for export] *)
  lazymatch idxs with
  | nil => acc
  | cons ?i ?idxs' => let h := eval cbv in (snd (nth (N.to_nat i) l (nil, @existT Prop (fun P : Prop => P) True I))) in
                      lx_lia_sel l idxs' constr:(cons h acc)
  end.
Ltac lx_lia_pack gts :=
  pose (lxZ := @nil Z); pose (lxW := @nil word); pose (lxB := @nil (list byte)); pose (lxL := @nil (list word));
  lx_colZs gts; lx_lia_collect;
  let l := lx_lia_hyps constr:(@nil (list pfact * lx_lia_hyp_ty)) in
  let gs := lx_reZs gts in
  let hyps := eval cbv beta iota delta [List.map fst] in (List.map fst l) in
  let r := eval vm_compute in (lx_lia_pick hyps gs) in
  lazymatch r with
  | Some ?idxs => let sel := lx_lia_sel l idxs constr:(@nil lx_lia_hyp_ty) in exact sel
  | None => fail
  end.
Ltac lx_lia_revert sel :=
  lazymatch sel with
  | nil => idtac
  | cons (@existT _ _ _ ?H) ?sel' => try revert H; lx_lia_revert sel'
  end.
Ltac lx_clear_all := repeat match goal with H : _ |- _ => clear H end.
(* [comment removed for export] *)
Lemma lx_uw_range : forall w : word, 0 <= bv_unsigned w < 18446744073709551616.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.
Ltac lx_lia_words :=
  repeat match goal with |- context [bv_unsigned ?w] =>
    lazymatch goal with
    | _ : 0 <= bv_unsigned w < _ |- _ => fail
    | |- _ => pose proof (lx_uw_range w)
    end end.
Ltac lx_lia_atom :=
  lazymatch goal with |- ?G =>
    let gts := lx_lia_goal_terms G in
    let sel0 := constr:(ltac:(lx_lia_pack gts) : list lx_lia_hyp_ty) in
    let sel := eval lazy zeta in sel0 in
    lx_lia_revert sel; lx_clear_all; lx_lia_words; intros; lia
  end.
Ltac lx_slia :=
  intros;
  lazymatch goal with
  | |- _ /\ _ => split; lx_slia
  | |- not _ => unfold not at 1; lx_slia
  | |- @eq Z ?a ?b => first [ apply Z.le_antisymm; lx_slia | lia ]
  | |- _ => first [ lx_lia_atom | lia ]
  end.
