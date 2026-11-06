(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlh4s RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.

Module RASlu8u.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.RASltfw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlts3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.RASltfw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux F_mm4hw RAlllfc RF_mx3o Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_mm4hw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RF_m79e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlooxi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASlico OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlku2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlxag OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.ASlojxo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.ASlo1am.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition lowW (spv : Z) (iv : Z * Z) : Prop :=
  (0 <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x63000 <= fst iv \/ (CTX <= fst iv /\ snd iv <= CTX + 928)))
  \/ iv = (spv - 144, spv).

Lemma lowW_meta spv st m' q : mrep st m' -> meta_slot st q -> lowW spv (conc st q, conc st q + 40).
Proof.
  intros MR MS. (first [ pose proof ((meta_slot_bounds st m' q MR MS)) as dR_1; dand4 dR_1 as Gpos GC GI _ | destruct (meta_slot_bounds st m' q MR MS) as (Gpos & GC & GI & _) ]). left. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). cbn [fst snd]. lia.
Qed.

Definition metaW (spv : Z) (st : mstate) (iv : Z * Z) : Prop :=
  (exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (CTX + 16, CTX + 24) \/ iv = (spv - 144, spv).

Lemma failW_shape st mt spv :
  meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (metaW spv st) (failW st mt spv).
Proof.
  intros MS FL. unfold failW.
  constructor; [right; right; reflexivity|].
  constructor; [left; exists mt; auto|].
  constructor; [right; left; reflexivity|].
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; [|constructor].
  destruct (FL h eq_refl) as [MSh FP].
  constructor; [left; exists h; auto|].
  destruct (m_prev (get_meta_rec st h)) as [p|] eqn:HP; [|constructor].
  constructor; [left; exists p; auto| constructor].
Qed.

Lemma failW_low st mt m' spv :
  mrep st m' -> meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (lowW spv) (failW st mt spv).
Proof.
  intros MR MS FL. eapply Forall_impl; [| exact (failW_shape st mt spv MS FL)].
  intros [lo hi] [(q & MSq & E1 & E2)|[E|E]]; [cbn in E1, E2; subst; eapply lowW_meta; eassumption| inversion E; subst; left; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX; cbn; lia| inversion E; subst; right; reflexivity].
Qed.

Lemma lowW_disjoint spv W a n : Forall (lowW spv) W -> alloc_ceiling <= a -> (a + n <= spv - 144 \/ spv <= a) -> disjoint_from W a n.
Proof. intros FW Ha Hs. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(H1 & H2 & H3)|E]; [cbn in *; lia| inversion E; subst; lia]. Qed.

Lemma lowW_disjoint_img spv W a n : Forall (lowW spv) W -> 0x10000 <= a -> a + n <= 0x63000 -> (a + n <= CTX \/ CTX + 928 <= a) ->
  alloc_ceiling <= spv - 144 -> disjoint_from W a n.
Proof. intros FW H1 H2 H3 H4. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(X1 & X2 & X3)|E]; [cbn in *; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| inversion E; subst; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. Qed.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section LEVEL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_okd (c_init_done (ctx st0)) m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := Mall8ro.ist_facts_proof st0 LB st AR IS.

Lemma nfail_ok : NFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof.
  intros st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC.
  (first [ dand31 NC as TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL C1R SMc LEAF MI'' ST'' ERR'' AUX'' MR'' TK'' UA'' PE'' MREL'' BL'' PSM'' PSF'' PSO'' AI'' CTR'' FR'' PE04 MR4 | destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4) ]).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (AS_STACK_ge sc) as ASG. pose proof CLO as CLO'. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (errno_lit5 tp TP) as EA.
  (first [ pose proof ((nest_class sc SC cnt1 C1R SMc)) as dR_3; dand6 dR_3 as ENR JR FITN SCJ NRR NFIT | destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT) ]).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), (-1); split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (Mall8ro.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (Mall8ro.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 (-1) AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (conc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  (first [ pose proof ((meta_slot_bounds st2 m4 mm MR4 MSL)) as dR_4; dand4 dR_4 as Gpos GC GI _ | pose proof (meta_slot_bounds st2 m4 mm MR4 MSL) as (Gpos & GC & GI & _) ]).
  (* [comment removed for export] *)
  pose proof (lf_freelist _ (isf_lf _ _ F3)) as FFL. change (fact_freelist (strip st3)) with (fact_freelist st3) in FFL.
  assert (FL : forall h, c_free_meta_head (ctx st3) = Some h ->
            meta_slot st3 h /\ h <> mm /\ exists p, m_prev (get_meta_rec st3 h) = Some p /\ meta_slot st3 p /\ p <> mm).
  { intros h Hh. (first [ pose proof ((FFL h Hh)) as dR_5; dand8 dR_5 as MSh MEMh NXh p HP MSp MEMp NXp | destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp) ]). destruct (NFL h Hh) as [NE1 NE2].
    change (meta_slot (strip st3) h) in MSh. change (get_meta_rec (strip st3) h) with (get_meta_rec st3 h) in MEMh, NXh, HP.
    change (meta_slot (strip st3) p) in MSp.
    split; [exact MSh|]. split; [exact NE1|]. exists p. split; [exact HP|]. split; [exact MSp|]. intros ->. apply NE2. exact HP. }
  rewrite as_free_meta_eq. cbn [as_kq].
  iprefixT. unfold rnest_regs.
  eapply evt_cut.
  { rewrite <- GE. unfold rFRM in FR''. replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) in FR'' by lia.
    eapply (rfailm1_walk st3 mm MS3 FL); [exact MR''| exact MI''| exact FR''| lia]. }
  cbv beta. (intros ms'; (first [ intro dR_17; dex4 dR_17 as a1x s6x m7 junk'; dand6 dR_17 as -> FR7 MU7 WM7 MI7 MR7 | intro dR_17; dand10 dR_17 as a1x s6x m7 junk' -> FR7 MU7 WM7 MI7 MR7 | intros (a1x & s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7) ])).
  assert (LW : Forall (lowW (bv_unsigned sp)) (failW st3 mm (bv_unsigned sp))).
  { eapply (failW_low st3 mm m'' _ MR'' MS3). intros h Hh. (first [ pose proof ((FL h Hh)) as dR_6; dand6 dR_6 as MSh _ p HP MSp _ | destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _) ]).
    split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
  assert (ST7 : stk rsegs m7 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU7| exact WM7| apply (lowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]].
    replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR7 : rw_cells rsegs m7 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU7| exact WM7|]. rewrite EA. apply (lowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold CTX; cbn; lia| lia]. }
  eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
  cbv beta. (intros ms'; (first [ intro dR_18; dex2 dR_18 as a1y a2y; destruct dR_18 as [-> ST8] | intro dR_18; dand4 dR_18 as a1y a2y -> ST8 | intros (a1y & a2y & -> & ST8) ])). apply evt_done.
  (* [comment removed for export] *)
  set (stF := as_fm_st st3 mm) in *.
  (first [ pose proof ((fm_proj st3 mm)) as dR_7; dand13 dR_7 as PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10 PF11 PF12 _ | destruct (fm_proj st3 mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _) ]). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (FS : Forall (metaW (bv_unsigned sp) st3) (failW st3 mm (bv_unsigned sp))).
  { apply (failW_shape st3 mm _ MS3). intros h Hh; (first [ pose proof ((FL h Hh)) as dR_8; dand6 dR_8 as MSh _ p HP MSp _ | destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _) ]); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
  assert (PE07 : pres_except (malloc_fp st0 stF lo (bv_unsigned sp)) m m7).
  { eapply pres_except_trans.
    - eapply pres_except_mono; [exact PE04|]. intros a Ha. eapply malloc_fp_mono; [| exact Ha]. intros rid r Hr.
      (first [ pose proof ((mrel_regions _ _ MREL'' rid r Hr)) as dR_9; dex1 dR_9 as r'; dand4 dR_9 as Hr' K' B' L' | pose proof ((mrel_regions _ _ MREL'' rid r Hr)) as dR_9; dand5 dR_9 as r' Hr' K' B' L' | destruct (mrel_regions _ _ MREL'' rid r Hr) as (r' & Hr' & K' & B' & L') ]). exists r'. rewrite PF1. auto.
    - eapply pres_except_trans.
      + eapply pres_except_mono; [exact PE''|]. intros a Ha. eapply (malloc_fp_widen (Clg:=Clg) st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia)); [| exact Ha].
        intros rid r Hr. exists r. rewrite PF1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. lia.
      + eapply pres_except_of_munch'; [exact MU7| exact WM7|].
        intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
        * cbn in E1, E2. subst lo' hi'. left. do 3 right.
          assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
          (first [ pose proof ((meta_chunk_facts stF m7 q MR7 MSq')) as dR_10; dand7 dR_10 as _ _ _ _ _ _ (rid0 & r0 & H0 & K0 & L0 & H0') | destruct (meta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')) ]).
          exists rid0, r0. split; [exact H0|]. split; [exact K0|].
          assert (EC : conc stF q = conc st3 q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
        * inversion E; subst. left. right. right. left. unfold CTX in *. lia.
        * inversion E; subst. left. left. lia. }
  apply HK. unfold as_post2.
  do 14 eexists. exists m7, errv''. split; [reflexivity|].
  split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
  split; [eapply (auxv_okd_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
  split; [exact MR7|].
  split; [eapply ticks_ok_same; [rewrite PF2; reflexivity| rewrite PF6; reflexivity| exact TK'']|].
  split. { eapply (unk_agree_xfer o st3 m'' stF m7 UA'').
    - exact PF2.
    - intros rid r Hk Hr. rewrite PF1 in Hr. exact Hr.
    - intros b. rewrite PF3. tauto.
    - intros rid r off h Hr Hk Ho Hc NG.
      pose proof MR'' as (WF3 & _). (first [ pose proof (WF3) as dR_11; dand4 dR_11 as _ WR3 DJ3 _ | pose proof WF3 as (_ & WR3 & DJ3 & _) ]). (first [ pose proof ((WR3 _ _ Hr)) as dR_12; dand5 dR_12 as R0 _ _ RC _ | destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      (first [ pose proof ((rregion_facts st3 m'' rid r MR'' Hr)) as dR_13; dand5 dR_13 as _ _ _ RI1 RI2 | destruct (rregion_facts st3 m'' rid r MR'' Hr) as (_ & _ & _ & RI1 & RI2) ]). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
      pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
      + cbn in E1, E2. subst lo' hi'.
        (first [ pose proof ((meta_chunk_facts st3 m'' q MR'' MSq)) as dR_14; dand7 dR_14 as _ _ _ _ _ GRG _ | destruct (meta_chunk_facts st3 m'' q MR'' MSq) as (_ & _ & _ & _ & _ & GRG & _) ]). destruct (GRG rid r Hr Hk); lia.
      + inversion E; subst. unfold CTX in Ha. lia.
      + inversion E; subst. lia. }
  split; [exact PE07|].
  split. { split.
    - intros rid r Hr. rewrite <- REG1 in Hr. (first [ pose proof ((amr_regions _ _ _ REL rid r Hr)) as dR_15; dex1 dR_15 as r'; dand5 dR_15 as H' K' B' L' _ | pose proof ((amr_regions _ _ _ REL rid r Hr)) as dR_15; dand6 dR_15 as r' H' K' B' L' _ | destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _) ]).
      (first [ pose proof ((mrel_regions _ _ MREL'' rid r' H')) as dR_16; dex1 dR_16 as r''; dand4 dR_16 as H'' K'' B'' L'' | pose proof ((mrel_regions _ _ MREL'' rid r' H')) as dR_16; dand5 dR_16 as r'' H'' K'' B'' L'' | destruct (mrel_regions _ _ MREL'' rid r' H') as (r'' & H'' & K'' & B'' & L'') ]). exists r''. rewrite PF1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; [congruence| congruence| lia].
    - rewrite PF7. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
    - rewrite PF8, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
  split. { unfold brk_link_ps in BL'' |- *. rewrite PF11. destruct (c_brk (ctx st3)) as [| |brid boff]; auto.
           unfold conc, get_region. rewrite PF1. exact BL''. }
  split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
  split. { constructor.
    - intros c' Hc'. rewrite PF9, (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
    - intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
    - rewrite PF6, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
    - intros H; exfalso; lia.
    - intros _ H; exfalso; lia. }
  split; [rewrite PF12; exact CTR''|].
  left. reflexivity.
Qed.
End LEVEL.
End RASlu8u.

Module RASlpv4.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASla24 RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlku2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.ASlojxo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.ASlo1am OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.RASltfw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlku2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlts3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.RASltfw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux F_mm4hw RAlllfc RF_mx3o Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_mm4hw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RF_m79e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlooxi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASlico OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlxag.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma grp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. (intros EG; (first [ intro dR_23; dex2 dR_23 as b gh; dand3 dR_23 as Hb Hf Ho | intro dR_23; dand5 dR_23 as b gh Hb Hf Ho | intros (b & gh & Hb & Hf & Ho) ])). exists b, gh. rewrite EG. auto. Qed.

Lemma mrep_st_model stT sc cnt ai ml mt p (SC : 0 <= sc < 48) (CNT : 1 <= cnt <= 32)
      (REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml) (P0 : 0 <= snd p) m :
  mrep (stFin stT sc cnt ai ml mt p) m -> mrep (st_model stT sc cnt ai mt p) m.
Proof.
  intros MR. eapply (mrep_extW _ _ _ MR); try reflexivity.
  intros q. apply (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
Qed.

End CEIL.

Section LEVEL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_okd (c_init_done (ctx st0)) m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := Mall8ro.ist_facts_proof st0 LB st AR IS.

#[using="HK TP ERR LO CLO AUX MR FIT RQ SC ER IS AR errv req LB"] Lemma nsucc_ok : NSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof.
  intros st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC I0 HA3 SO3 SPAN3 RDV3.
  (first [ dand31 NC as TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL C1R SMc LEAF MI'' ST'' ERR'' AUX'' MR'' TK'' UA'' PE'' MREL'' BL'' PSM'' PSF'' PSO'' AI'' CTR'' FR'' PE04 MR4 | destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4) ]).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (AS_STACK_ge sc) as ASG. pose proof CLO as CLO'. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (errno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  (first [ pose proof ((nest_class sc SC cnt1 C1R SMc)) as dR_2; dand6 dR_2 as ENR JR FITN SCJ NRR NFIT | destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT) ]).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), idx; split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (Mall8ro.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (Mall8ro.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 idx AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (conc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  (first [ pose proof ((meta_slot_bounds st3 m'' mm MR'' MS3)) as dR_3; dand4 dR_3 as Gpos GC GI _ | pose proof (meta_slot_bounds st3 m'' mm MR'' MS3) as (Gpos & GC & GI & _) ]).
  (* [comment removed for export] *)
  pose proof (so_mem _ _ _ _ _ _ SO3) as Hmem3. pose proof (so_reg _ _ _ _ _ _ SO3) as Hr3. pose proof (so_kind _ _ _ _ _ _ SO3) as Hk3.
  pose proof (so_mslot _ _ _ _ _ _ SO3) as MSLg. pose proof (so_fit _ _ _ _ _ _ SO3) as FIT3. pose proof (so_idx _ _ _ _ _ _ SO3) as IDX3.
  pose proof (so_b0 _ _ _ _ _ _ SO3) as B30. pose proof (so_span _ _ _ _ _ _ SO3) as SP3. pose proof (so_li _ _ _ _ _ _ SO3) as LI3.
  pose proof (mf_active _ _ MF3) as FA3. change (fact_active (strip st3)) with (fact_active st3) in FA3.
  (first [ pose proof ((FA3 (ncls sc cnt1) g3 HA3)) as dR_4; dand3 dR_4 as _ GSC3 _ | destruct (FA3 (ncls sc cnt1) g3 HA3) as (_ & GSC3 & _) ]).
  pose proof (lf_host_stride _ (isf_lf _ _ F3) g3 b3 Hmem3 ltac:(change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3); rewrite GSC3; lia)) as STR3.
  change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in STR3. rewrite GSC3 in STR3.
  (first [ pose proof ((lf_mw _ (isf_lf _ _ F3) g3)) as dR_5; dand3 dR_5 as MW3 _ _ | pose proof (lf_mw _ (isf_lf _ _ F3) g3) as (MW3 & _ & _) ]). change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in MW3.
  set (strideg := get_stride (get_meta_rec st3 g3)) in *.
  set (szc := size_class sc) in *.
  assert (FITg : 16 * szc * cnt1 + 16 <= strideg) by lia.
  assert (SZC1 : 16 * szc <= 16 * szc * cnt1) by nia.
  assert (SO_N : slot_ok st3 g3 b3 r3 idx (UNIT * size_class (ncls sc cnt1) - IB)) by (eapply slot_ok_N; [exact SO3| unfold IB; lia| unfold UNIT, IB; lia]).
  set (X := snd b3 + (16 + strideg * idx)) in *.
  set (p := (fst b3, X) : aptr).
  (first [ pose proof ((rregion_facts st3 m'' (fst b3) r3 MR'' Hr3)) as dR_6; dand5 dR_6 as R4 RAL RC RI1 RI2 | pose proof (rregion_facts st3 m'' (fst b3) r3 MR'' Hr3) as (R4 & RAL & RC & RI1 & RI2) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (CB3 : conc st3 b3 = r_base r3 + snd b3) by (apply conc_region'; exact Hr3).
  assert (CP : conc st3 p = r_base r3 + X) by (apply conc_region'; exact Hr3).
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (XEND : X + strideg <= round_up_pg (r_len r3)).
  { unfold X. eapply Z.le_trans; [| exact SP3]. fold strideg.
    assert (strideg * idx + strideg <= strideg * (m_last_idx (get_meta_rec st3 g3) + 1)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    lia. }
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  assert (JR' : 0 <= ncls sc cnt1 < 48) by lia.
  assert (FRESH3 : forall o' v t, X <= o' < X + strideg - 4 -> (r_cells (get_shadow st3 (fst b3))) !! o' = Some (v, t) -> (t < s_tick st3)%N).
  { intros o' v t Ho Hc. eapply (ai_fresh _ _ _ _ _ AI'' I0 (fst b3) X (strideg - 4)); [| | exact Hc]; [| lia].
    exists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  (* [comment removed for export] *)
  rewrite (nest_model_eq st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SO_N STR3).
  replace (slot_of st3 g3 idx) with p by (unfold slot_of, slot_start'; rewrite Hmem3; reflexivity).
  (first [ pose proof ((nt_tail_hyps st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)) as dR_7; dand10 dR_7 as TMS TREC TREG TP0 TP16 TPEND TGN TNOG TOLD TTK | destruct (nt_tail_hyps st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)
    as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK) ]).
  fold strideg X p in TMS, TREC, TREG, TP0, TP16, TPEND, TGN, TNOG, TOLD, TTK.
  set (stT := nt_stT st3 g3 b3 idx sc cnt1 mm) in *.
  assert (ACT3 : active st3 sc = None).
  { rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). exact ACT0. }
  assert (ACTT : active stT sc = None) by (unfold stT; rewrite ntT_active; exact ACT3).
  rewrite (ag_tail_kq_eq sc k bail stT mm p cnt1 (cnt1 - 1)); [| rewrite TREC; reflexivity| rewrite TREC; reflexivity| exact ACTT].
  (first [ pose proof ((ntT_proj st3 g3 b3 idx sc cnt1 mm)) as dR_8; dand8 dR_8 as TPR TPG TPA TPT TPN TPRS TPC TPS | destruct (ntT_proj st3 g3 b3 idx sc cnt1 mm) as (TPR & TPG & TPA & TPT & TPN & TPRS & TPC & TPS) ]). fold stT in TPR, TPG, TPA, TPT, TPN, TPRS, TPC, TPS.
  assert (URT : 0 <= usage stT sc < 2^60).
  { unfold stT. rewrite ntT_usage. pose proof (mf_usage _ _ MF3 sc) as U. exact U. }
  assert (TCONC : forall q, conc stT q = conc st3 q) by (intros q; unfold stT; apply ntT_conc).
  (* [comment removed for export] *)
  iprefixT. unfold rnest_regs. rewrite <- GE.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rnenf_walk st3 m'' o g3 b3 r3 idx (ncls sc cnt1) MR'' UA'' JR' HA3 MSLg MW3 GSC3 STR3 SO_N TK''); [exact CTR''| exact MI'']. }
  cbv beta. (intros ms'; (first [ intro dR_24; dex15 dR_24 as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m5; dand6 dR_24 as -> MU5 WM5 MI5 MR5 TK5 | intro dR_24; dand21 dR_24 as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m5 -> MU5 WM5 MI5 MR5 TK5 | intros (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5 & -> & MU5 & WM5 & MI5 & MR5 & TK5) ])).
  fold strideg.
  (* [comment removed for export] *)
  assert (MWmm : mw_ok (get_meta_rec st3 mm)) by (rewrite G3; unfold mw_ok, meta0; cbn; lia).
  eapply evt_cut.
  { change (wz cnt1) with (Z_to_bv 64 cnt1).
    eapply (enfD_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' JR' SO_N TK''); [exact MS3| exact MWmm| exact C1R| exact MR5| exact TK5| exact MI5]. }
  cbv beta. (intros ms'; (first [ intro dR_25; dex1 dR_25 as m6; dand6 dR_25 as -> MU6 WM6 MI6 MR6 TK6 | intro dR_25; dand7 dR_25 as m6 -> MU6 WM6 MI6 MR6 TK6 | intros (m6 & -> & MU6 & WM6 & MI6 & MR6 & TK6) ])).
  fold strideg in MU5, MU6, MR6, TK6 |- *.
  change (wr8 (fst b3, snd b3 + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192) (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g3 b3 idx)))
    with (nt_stW st3 g3 b3 idx mm) in MR6, TK6.
  (* [comment removed for export] *)
  set (P := conc st3 b3 + 16 + strideg * idx) in *.
  assert (EP : P = r_base r3 + X) by (unfold P, X; rewrite CB3; lia).
  eapply evt_cut.
  { replace (wz (size_class sc * UNIT)) with (Z_to_bv 64 (16 * szc)) by (unfold wz, szc, UNIT; f_equal; lia).
    replace (Z_to_bv 64 (P + 12)) with (Z_to_bv 64 (P + 12 + 16 * szc * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (cnt1 + 1)) with (Z_to_bv 64 (cnt1 + 1 - 0)) by (f_equal; lia).
    eapply (zero_loop_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' STR3 SO_N (Z.to_nat (cnt1 + 1)) 0 szc cnt1 (nt_stW st3 g3 b3 idx mm) m6 m6);
      [lia| lia| unfold szc; lia| lia| unfold strideg in FITg; lia
      | apply (proj1 (ntW_proj st3 g3 b3 idx mm))| apply (proj1 (proj2 (ntW_proj st3 g3 b3 idx mm)))
      | exact MR6| exact TK6| exact MI6| apply munch_refl| apply wmono_refl]. }
  cbv beta. (intros ms'; (first [ intro dR_26; dex1 dR_26 as m7; dand9 dR_26 as -> MU7 WM7 MI7 MR7 TK7 RG7 GR7 PW7 | intro dR_26; dand10 dR_26 as m7 -> MU7 WM7 MI7 MR7 TK7 RG7 GR7 PW7 | intros (m7 & -> & MU7 & WM7 & MI7 & MR7 & TK7 & RG7 & GR7 & PW7) ])).
  change (zero_hdrs (pp st3 g3 b3 idx) (16 * szc) 0 (Z.to_nat (cnt1 + 1)) (nt_stW st3 g3 b3 idx mm)) with stT in MR7, TK7, RG7, GR7.
  fold P in MU7, PW7.
  (* [comment removed for export] *)
  eapply evt_cut.
  { replace (Z_to_bv 64 P) with (Z_to_bv 64 (conc stT p)) by (rewrite TCONC, CP, EP; reflexivity).
    replace (Z_to_bv 64 (conc st3 mm)) with (Z_to_bv 64 (conc stT mm)) by (rewrite TCONC; reflexivity).
    eapply (tail_walk (Clg:=Clg) stT sc cnt1 (cnt1 - 1) 0 mm p r3 SC C1R ltac:(lia) ltac:(lia) TMS TREC TREG Hk3 TP0 TP16 TPEND TGN TNOG TOLD URT ACTT TK7);
      [exact MR7| exact MI7]. }
  cbv beta. (intros ms'; (first [ intro dR_27; dex6 dR_27 as s0x a1x a2y a3x a4z m8; dand6 dR_27 as -> MU8 WM8 MI8 MR8 TK8 | intro dR_27; dand12 dR_27 as s0x a1x a2y a3x a4z m8 -> MU8 WM8 MI8 MR8 TK8 | intros (s0x & a1x & a2y & a3x & a4z & m8 & -> & MU8 & WM8 & MI8 & MR8 & TK8) ])).
  (* [comment removed for export] *)
  set (W58 := ([(P - 3, P); (conc st3 mm, conc st3 mm + 40); (P - 3, P - 2); (P + 12, P + 12 + 16 * szc * cnt1 + 1)]%Z ++ tailW stT sc mm p)).
  assert (LOWW : Forall (fun iv : Z * Z => snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x63000 <= fst iv \/ (CTX <= fst iv /\ snd iv <= CTX + 928))) W58).
  { apply Forall_forall. intros [lo' hi'] HI. cbn [fst snd]. unfold W58, tailW in HI. rewrite !TCONC, CP in HI. cbn [app In] in HI.
    pose proof (round_up_pg_ge (r_len r3)).
    destruct HI as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; inversion E; subst; unfold CTX; lia. }
  assert (MU58 : munch W58 m'' m8).
  { intros x Hx. unfold W58 in Hx. rewrite outside_app' in Hx. destruct Hx as [H4x H8].
    rewrite (MU8 x H8). cbn [outside] in H4x. (first [ dand5 H4x as H5 H6a H6b H7 _ | destruct H4x as (H5 & H6a & H6b & H7 & _) ]).
    rewrite (MU7 x) by (cbn; auto). rewrite (MU6 x) by (cbn; auto). rewrite (MU5 x) by (cbn; auto). reflexivity. }
  assert (WM58 : wmono rsegs m'' m8).
  { eapply wmono_trans; [exact WM5|]. eapply wmono_trans; [exact WM6|]. eapply wmono_trans; [exact WM7| exact WM8]. }
  assert (DJhigh : forall A n, alloc_ceiling <= A -> disjoint_from W58 A n).
  { intros A n HA. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [H _]. lia. }
  assert (DJimg : forall A n, 0x10000 <= A -> A + n <= 0x63000 -> (A + n <= CTX \/ CTX + 928 <= A) -> disjoint_from W58 A n).
  { intros A n H1 H2 H3. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [_ H]. unfold CTX in *. lia. }
  assert (FR8 : rw_cells rsegs m8 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact FR''. }
  assert (ST8 : stk rsegs m8 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR8 : rw_cells rsegs m8 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU58| exact WM58|]. rewrite EA. apply DJimg; [lia| cbn; lia| unfold CTX; cbn; lia]. }
  set (stF := st_model stT sc cnt1 (cnt1 - 1) mm p).
  assert (MRF : mrep stF m8) by (exact (mrep_st_model stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 m8 MR8)).
  eapply evt_cut. { unfold rFRM in FR8. eapply (ras_ret0 sp gp tp); [exact MRF| exact MI8| exact FR8| exact ST8| exact CLO| lia]. }
  cbv beta. (intros ms'; (first [ intro dR_28; dex2 dR_28 as a1w a2w; destruct dR_28 as [-> ST9] | intro dR_28; dand4 dR_28 as a1w a2w -> ST9 | intros (a1w & a2w & -> & ST9) ])). apply evt_done.
  apply HK.
  (* [comment removed for export] *)
  fold strideg in MU7, PW7. fold P in MU7, PW7.
  (first [ pose proof ((smg_proj stT sc cnt1 (cnt1 - 1) mm p)) as dR_10; dand10 dR_10 as PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10 | destruct (smg_proj stT sc cnt1 (cnt1 - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10) ]).
  fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
  rewrite TPR in PF1. rewrite TPA in PF4. rewrite TPT in PF5. rewrite TPN in PF6. rewrite TPRS in PF7.
  assert (CTXT : ctx stT = ctx st3) by (unfold stT; apply ntT_ctx).
  rewrite CTXT in PF8, PF9, PF10.
  assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK8]; reflexivity).
  assert (MSF : meta_slot stF mm) by (apply (proj1 (smg_meta_slot stT sc cnt1 (cnt1 - 1) mm p mm)); exact TMS).
  assert (CF : forall q, conc stF q = conc st3 q) by (intros q; unfold stF; rewrite (smg_conc stT sc cnt1 (cnt1 - 1) mm p q); apply TCONC).
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR'' as (WF3 & _). (first [ pose proof (WF3) as dR_11; dand4 dR_11 as RS3 WR3 DJ3 _ | pose proof WF3 as (RS3 & WR3 & DJ3 & _) ]).
  assert (STRF : get_stride (get_meta_rec stF mm) = 16 * szc) by (exact (ntF_stride st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)).
  (* [comment removed for export] *)
  assert (HOLD2 : forall q rq, (s_regions st2) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. (first [ pose proof ((mrel_regions _ _ MREL'' q rq Hq)) as dR_12; dex1 dR_12 as r'; dand4 dR_12 as Hr' K' B' L' | pose proof ((mrel_regions _ _ MREL'' q rq Hq)) as dR_12; dand5 dR_12 as r' Hr' K' B' L' | destruct (mrel_regions _ _ MREL'' q rq Hq) as (r' & Hr' & K' & B' & L') ]). exists r'. rewrite PF1. auto. }
  assert (HOLD3 : forall q rq, (s_regions st3) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. exists rq. rewrite PF1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. lia. }
  assert (INSPAN : forall a, r_base r3 + X - 4 <= a < r_base r3 + X + strideg - 4 -> malloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. eapply (malloc_fp_widen (Clg:=Clg) st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3). apply SPAN3. unfold X in Ha. lia. }
  assert (INMETA : forall a, conc st3 mm <= a < conc st3 mm + 40 -> malloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. left. do 3 right. (first [ pose proof ((meta_chunk_facts stF m8 mm MRF MSF)) as dR_13; dand7 dR_13 as _ _ _ _ _ _ (rid0 & rr0 & H0 & K0 & L0 & H0') | destruct (meta_chunk_facts stF m8 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')) ]).
    exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite CF in L0, H0'. lia. }
  assert (INCTX : forall a, CTX <= a < CTX + 928 -> malloc_fp st0 stF lo (bv_unsigned sp) a) by (intros a Ha; left; right; right; left; exact Ha).
  (* [comment removed for export] *)
  assert (HDR0N : cell_read (get_shadow st3 (fst b3)) (X + strideg - 4) = Known 0).
  { pose proof (mf_hdr0 _ _ MF3 g3 b3 (idx + 1) Hmem3 ltac:(lia)) as H.
    unfold sstart_of in H. rewrite Hmem3 in H. cbn [default from_option id snd] in H. fold strideg in H. unfold IB, UNIT in H.
    replace (X + strideg - 4) with (snd b3 + 16 + strideg * (idx + 1) - 4) by (unfold X; lia). exact H. }
  assert (M6A : m6 (wa (r_base r3 + (X + strideg - 4))) = Some (b8 0)).
  { apply (region_byte_raw (nt_stW st3 g3 b3 idx mm) m6 (fst b3) r3 (X + strideg - 4) 0 MR6).
    - rewrite (proj1 (ntW_proj st3 g3 b3 idx mm)). exact Hr3.
    - exact Hk3.
    - lia.
    - rewrite (ntW_cell_read_other st3 g3 b3 idx (ncls sc cnt1) sc mm SC JR' (X + strideg - 4)) by (unfold X; lia). exact HDR0N. }
  assert (PE67 : pres_except (malloc_fp st0 stF lo (bv_unsigned sp)) m6 m7).
  { intros a Ha NC. split; [| intros W; apply WM7; exact W].
    destruct (arith_prog_dec a (P + 12) (16 * szc) cnt1 ltac:(lia)) as [(j & Hj & Ea)|NA].
    - destruct (Z_lt_le_dec a (P + strideg - 4)) as [LT|GE'].
      + exfalso. apply NC. apply INSPAN. lia.
      + assert (J16 : 16 * szc * j <= 16 * szc * cnt1) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (Ea' : a = r_base r3 + (X + strideg - 4)) by lia.
        rewrite Ea', M6A.
        apply (region_byte_raw stT m7 (fst b3) r3 (X + strideg - 4) 0 MR7); [rewrite TPR; exact Hr3| exact Hk3| lia|].
        assert (EJ : 16 * szc * j = 16 * szc * cnt1) by lia.
        replace (X + strideg - 4) with (X + 12 + cnt1 * (16 * szc)) by lia.
        unfold stT. apply (ntT_cell_read_zero st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R TK''). lia.
    - apply PW7. rewrite wa_unsigned by lia. intros j Hj. specialize (NA j Hj). lia. }
  assert (PE08 : pres_except (malloc_fp st0 stF lo (bv_unsigned sp)) m m8).
  { eapply pres_except_trans. { eapply pres_except_mono; [exact PE04|]. intros a Ha. exact (malloc_fp_mono st0 st2 stF lo (bv_unsigned sp) a HOLD2 Ha). }
    eapply pres_except_trans. { eapply pres_except_mono; [exact PE''|]. intros a Ha. exact (malloc_fp_widen (Clg:=Clg) st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3 Ha). }
    eapply pres_except_trans. { eapply pres_except_of_munch; [exact MU5| exact WM5|]. intros a Ha NC. cbn. split; [|exact I]. intros Xa; apply NC. apply INSPAN. lia. }
    eapply pres_except_trans. { eapply pres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros Xa; apply NC; [apply INMETA; lia| apply INSPAN; lia]. }
    eapply pres_except_trans. { exact PE67. }
    eapply pres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. unfold tailW. rewrite !TCONC, CP. cbn.
    split; [|split; [|split; [|split; [|exact I]]]]; intros Xa; apply NC; [apply INCTX; unfold CTX in *; lia| apply INMETA; lia| apply INSPAN; lia| apply INCTX; unfold CTX in *; lia]. }
  (* [comment removed for export] *)
  assert (UAF : unk_agree stF o m8).
  { intros rid rr off h Hrr Kr Ho Hc NG. rewrite PF1 in Hrr.
    (first [ pose proof ((WR3 _ _ Hrr)) as dR_14; dand5 dR_14 as R0 _ _ RCr _ | destruct (WR3 _ _ Hrr) as (R0 & _ & _ & RCr & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    (first [ pose proof ((rregion_facts st3 m'' rid rr MR'' Hrr)) as dR_15; dand5 dR_15 as _ _ _ RI1r RI2r | destruct (rregion_facts st3 m'' rid rr MR'' Hrr) as (_ & _ & _ & RI1r & RI2r) ]). specialize (RI1r ltac:(lia)). specialize (RI2r ltac:(lia)).
    (first [ pose proof ((meta_chunk_facts st3 m'' mm MR'' MS3)) as dR_16; dand7 dR_16 as _ _ _ _ _ GRG _ | destruct (meta_chunk_facts st3 m'' mm MR'' MS3) as (_ & _ & _ & _ & _ & GRG & _) ]). pose proof (GRG rid rr Hrr Kr) as GRr.
    assert (NG3 : ~ grp_hdr_cov st3 rid off).
    { intros CV. apply NG. unfold stF. apply (smg_grp_hdr_cov_old stT sc cnt1 (cnt1 - 1) mm p TP0 rid off TGN).
      eapply grp_hdr_cov_same; [exact TPG| exact CV]. }
    destruct (N.eq_dec rid (fst b3)) as [->|NE].
    - rewrite Hr3 in Hrr. inversion Hrr; subst rr.
      destruct (ntF_unknown st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N TK'' off h ltac:(lia) Hc) as [CV|(Hc3 & NH & NZ)].
      { exfalso. apply NG. exact CV. }
      rewrite <- (UA'' (fst b3) r3 off h Hr3 Kr Ho Hc3 NG3).
      assert (NHC : ~ (X <= off < X + 12)).
      { intros Hx. apply NG. unfold stF. change (fst b3) with (fst p). apply (smg_grp_hdr_cov stT sc cnt1 (cnt1 - 1) mm p SC). unfold p. cbn [snd]. lia. }
      assert (HB : 0 <= r_base r3 + off < 2 ^ 64) by (try (generalize alloc_ceiling_val); clear - R4 RC Ho; try pose proof alloc_ceiling_val; lia).
      transitivity (m7 (wa (r_base r3 + off))). { apply MU8. rewrite wa_unsigned by exact HB. unfold tailW. rewrite !TCONC, CP. cbn. unfold CTX. try (generalize alloc_ceiling_val); clear - SC RI2 Ho GRr NHC; try pose proof alloc_ceiling_val. lia. }
      transitivity (m6 (wa (r_base r3 + off))). { apply PW7. rewrite wa_unsigned by exact HB. intros j Hj E. apply NZ. exists j. split; [exact Hj|]. try (generalize alloc_ceiling_val); clear - E EP CB3; try pose proof alloc_ceiling_val. lia. }
      transitivity (m5 (wa (r_base r3 + off))). { apply MU6. rewrite wa_unsigned by exact HB. cbn. try (generalize alloc_ceiling_val); clear - GRr Ho NHC NH EP; try pose proof alloc_ceiling_val. lia. }
      apply MU5. rewrite wa_unsigned by exact HB. cbn. try (generalize alloc_ceiling_val); clear - NHC NH EP; try pose proof alloc_ceiling_val. lia.
    - assert (Hc3 : cell_read (get_shadow st3 rid) off = Unknown h).
      { rewrite <- (ntF_shadow_other st3 g3 b3 idx sc cnt1 mm rid NE). exact Hc. }
      rewrite <- (UA'' rid rr off h Hrr Kr Ho Hc3 NG3).
      pose proof (lr_lo_group rr Kr) as LR1. pose proof (lr_lo_group r3 Hk3) as LR2.
      assert (NE' : fst b3 <> rid) by (intros E; apply NE; symmetry; exact E).
      pose proof (round_up_pg_ge (r_len r3)) as RU3.
      assert (HB : 0 <= r_base rr + off < 2 ^ 64) by (try (generalize alloc_ceiling_val); clear - R0 RCr Ho; try pose proof alloc_ceiling_val; lia).
      assert (DD : r_base rr + off + 12 <= r_base r3 + X \/ r_base r3 + X + strideg <= r_base rr + off).
      { destruct (DJ3 _ _ _ _ Hr3 Hrr NE') as [D|D]; try (generalize alloc_ceiling_val); clear - D LR1 LR2 Ho B30 SK XEND; try pose proof alloc_ceiling_val; lia. }
      transitivity (m7 (wa (r_base rr + off))). { apply MU8. rewrite wa_unsigned by exact HB. unfold tailW. rewrite !TCONC, CP. cbn [outside]. unfold CTX. try (generalize alloc_ceiling_val); clear - SC RI2r Ho GRr DD FITg SZC1 SZR; try pose proof alloc_ceiling_val. lia. }
      transitivity (m6 (wa (r_base rr + off))). { apply MU7. rewrite wa_unsigned by exact HB. cbn [outside]. try (generalize alloc_ceiling_val); clear - DD EP FITg; try pose proof alloc_ceiling_val. lia. }
      transitivity (m5 (wa (r_base rr + off))). { apply MU6. rewrite wa_unsigned by exact HB. cbn [outside]. try (generalize alloc_ceiling_val); clear - GRr Ho DD EP FIT3 NRR; try pose proof alloc_ceiling_val. lia. }
      apply MU5. rewrite wa_unsigned by exact HB. cbn [outside]. try (generalize alloc_ceiling_val); clear - DD EP FIT3 NRR; try pose proof alloc_ceiling_val. lia. }
  assert (RSP3 : ret_span st3 (ncls sc cnt1) idx (fst b3) X (strideg - 4)).
  { exists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  unfold as_post2.
  do 14 eexists. exists m8, errv''. split; [reflexivity|].
  split; [exact MI8|]. split; [exact ST9|]. split; [exact ERR8|].
  split; [eapply (auxv_okd_malloc_fp_ER st0 st m MR ER stF m8); [exact MRF| exact AUX| exact PE08| exact CLO| lia]|].
  split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE08|].
  split. { split.
    - intros q rq Hq. rewrite <- REG1 in Hq. (first [ pose proof ((amr_regions _ _ _ REL q rq Hq)) as dR_17; dex1 dR_17 as r'; dand5 dR_17 as H' K' B' L' _ | pose proof ((amr_regions _ _ _ REL q rq Hq)) as dR_17; dand6 dR_17 as r' H' K' B' L' _ | destruct (amr_regions _ _ _ REL q rq Hq) as (r' & H' & K' & B' & L' & _) ]).
      (first [ pose proof ((HOLD2 q r' H')) as dR_18; dex1 dR_18 as r''; dand4 dR_18 as H'' K'' B'' L'' | pose proof ((HOLD2 q r' H')) as dR_18; dand5 dR_18 as r'' H'' K'' B'' L'' | destruct (HOLD2 q r' H') as (r'' & H'' & K'' & B'' & L'') ]). exists r''. split; [exact H''|]. split; [rewrite K''; exact K'|]. split; [rewrite B''; exact B'|]. lia.
    - rewrite PF6. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
    - rewrite PF7, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
  split. { unfold brk_link_ps in BL'' |- *. rewrite PF8. destruct (c_brk (ctx st3)) as [| |brid boff]; auto. rewrite CF. exact BL''. }
  split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
  split. { constructor.
    - intros c' Hc'. unfold stF. rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p c'). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold stT. rewrite ntT_active. rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
    - intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
    - rewrite PF5, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
    - intros _ rid' S len RSP o' v t Ho Hc.
      (first [ pose proof ((smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP)) as dR_19; dand3 dR_19 as -> -> -> | destruct (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) as (-> & -> & ->) ]).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho.
      unfold p in Hc, Ho. cbn [fst snd] in Hc, Ho. rewrite PF5.
      unfold stF, stT, p in Hc. rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') in Hc by (fold szc; lia).
      eapply FRESH3; [| exact Hc]. lia.
    - intros E0 _ rid' S len RSP o' Ho.
      (first [ pose proof ((smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP)) as dR_20; dand3 dR_20 as -> -> -> | destruct (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) as (-> & -> & ->) ]).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho. unfold p in Ho. cbn [snd] in Ho.
      (first [ pose proof ((ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 o' ltac:(lia))) as dR_21; dand3 dR_21 as V1 V2 V3 | destruct (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 o' ltac:(lia)) as (V1 & V2 & V3) ]).
      unfold p. cbn [fst]. unfold stF, stT, p. split; [| split].
      + rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') by (fold szc; lia). exact V1.
      + rewrite (ntF_span_hav st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' SO_N o') by lia. exact V2.
      + rewrite (ntF_havp st3 g3 b3 idx sc cnt1 mm). exact V3. }
  split. { rewrite PF9. exact CTR''. }
  right. split; [lia|]. exists mm, p, r3.
  split; [unfold stF; rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p sc), Z.eqb_refl; reflexivity|].
  split; [unfold stF, stT, p, X; apply (nt_slot_ok st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N STR3 ltac:(fold szc; lia) G3 MS3 TK'' FRESH3 req); lia|].
  rewrite STRF. unfold p. cbn [fst snd]. split.
  + intros a Ha. apply INSPAN. lia.
  + intros E0. replace (X + (16 + 16 * szc * 0) + -3) with (X + 13) by lia.
    (first [ pose proof ((ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 (X + 13) ltac:(lia))) as dR_22; dand3 dR_22 as V1 V2 V3 | destruct (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 (X + 13) ltac:(lia)) as (V1 & V2 & V3) ]).
    unfold stF, stT. apply (ntF_rdv13 st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N o V1 V2 V3).
Qed.
End LEVEL.
End RASlpv4.

Module RASlt5l.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASl0ja OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlanm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlx4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASl8jf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.ASlojxo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RF_m79e.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y RF_mk75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Malluin Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASl0ja OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlanm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlx4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASl8jf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlts3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlxag OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.RASltfw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl4er.RASlu8u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl4er.RASlpv4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RF_m79e.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Section LEVEL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_okd (c_init_done (ctx st0)) m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := Mall8ro.ist_facts_proof st0 LB st AR IS.

Lemma rhmm_ok : HMM_stmt k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof using A1 AR AUX CLO ER FIT HK LO MR RQ SC TP.
  clear A0 F0 IS AC TK UA BL ST MI ERR.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R BIGc.
  (first [ dand23 CT as TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO | destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO) ]).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (AS_STACK_ge sc) as ASG. pose proof CLO as CLO'. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (errno_lit5 tp TP) as EA.
  pose proof (Mall8ro.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2) as URall. change (fact_usage (strip st2)) with (fact_usage st2) in URall.
  (first [ pose proof ((mf_ctx _ _ MF2)) as dR_2; dand6 dR_2 as FC1 FC2 FC3 FC4 FC5 FC6 | pose proof (mf_ctx _ _ MF2) as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6) ]).
  change (ctx (strip st2)) with (ctx st2) in FC1, FC2, FC3, FC4. change (bounces (strip st2)) with (bounces st2) in FC5. change (unmap_seq (strip st2)) with (unmap_seq st2) in FC6.
  pose proof (size_class_range sc SC) as SZR.
  unfold rcnt_state.
  replace (size_class sc * UNIT * cnt1) with (UNIT * size_class sc * cnt1) by lia.
  replace (size_class sc * UNIT) with (UNIT * size_class sc) by lia.
  set (size := UNIT * size_class sc) in *.
  assert (SZ : 16 <= size < 2^18) by (subst size; unfold UNIT; lia).
  rewrite A1. rewrite (ag_mmap_eq sc req k bail st2 mm cnt1).
  set (stS := step_seq (account_bounce sc st2)).
  set (nos := is_bouncing sc st2).
  set (u1 := mm_usage1 stS sc (usage st2 sc)).
  set (cR := mm_cnt_red sc size cnt1 u1 nos).
  assert (CRR : 1 <= cR <= 32) by (subst cR; apply mm_cnt_red_range; exact C1R).
  destruct (mm_final size req u1 cR nos) as [c nd] eqn:EF.
  (first [ pose proof ((mm_final_props size req u1 cR nos c nd CRR ltac:(lia) ltac:(lia) ltac:(subst size; unfold UNIT; lia) EF)) as dR_3; dand4 dR_3 as CR NDM NDR NDC | destruct (mm_final_props size req u1 cR nos c nd CRR ltac:(lia) ltac:(lia) ltac:(subst size; unfold UNIT; lia) EF) as (CR & NDM & NDR & NDC) ]).
  assert (NDB : 16 <= nd < 2^40).
  { pose proof (round_up_pg_props (req + 20) ltac:(lia)). pose proof (round_up_pg_props (size * c + 16) ltac:(nia)).
    assert (size * c <= 2^18 * 32) by nia. destruct NDC as [[Ec En]|[LE En]]; rewrite En; lia. }
  cbv beta iota.
  (* [comment removed for export] *)
  iprefixT.
  eapply evt_cut. { eapply (mm_seq_walk sc SC); [exact MR3| exact FC4| exact FC5| exact FC6| exact MI3]. }
  cbv beta. (intros ms'; (first [ intro dR_35; dex6 dR_35 as u0 u1' wa3 wa6 wa7 m4; dand6 dR_35 as -> -> MU4 WM4 MI4 MR4 | intro dR_35; dand12 dR_35 as u0 u1' wa3 wa6 wa7 m4 -> -> MU4 WM4 MI4 MR4 | intros (u0 & u1' & wa3 & wa6 & wa7 & m4 & -> & -> & MU4 & WM4 & MI4 & MR4) ])).
  fold nos stS in MR4 |- *.
  (* [comment removed for export] *)
  (first [ pose proof ((stS_shape sc st2)) as dR_4; dex1 dR_4 as fS; destruct dR_4 as [ES HS] | pose proof ((stS_shape sc st2)) as dR_4; dand3 dR_4 as fS ES HS | destruct (stS_shape sc st2) as (fS & ES & HS) ]). fold stS in ES.
  assert (US : forall i, usage stS i = usage st2 i) by (intros i; unfold usage; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (proj2 (HS _))); reflexivity).
  eapply evt_cut.
  { replace (wz (size + 16)) with (wz (size + 16)) by reflexivity.
    eapply (mmc_walk sc size req nos SC SZ RQ) with (st := stS) (m := m4); [exact MR4| exact C1R| apply URall| intros i; rewrite US; apply URall]. }
  cbv beta. unfold mmc_post. (intros ms'; (first [ intro dR_36; dand10 dR_36 as v0 va0 va1 va2 va3 va4 va5 va6 va7 -> | intros (v0 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & ->) ])).
  fold u1. fold cR. rewrite ?EF. cbn [fst snd].
  (* [comment removed for export] *)
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [exact FR3| exact MU4| exact WM4|]. unfold seqW, CTX. cbn. lia. }
  assert (ST4 : stk rsegs m4 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4|]. unfold seqW, CTX. cbn. lia. }
  assert (ERR4 : rw_cells rsegs m4 (errno_addr tp) [C4 errv']).
  { eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4|]. rewrite EA. unfold seqW, CTX. cbn. lia. }
  assert (PE04 : pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m4).
  { eapply pres_except_trans; [exact PE03|]. eapply pres_except_of_munch; [exact MU4| exact WM4|].
    intros a Ha NC. unfold seqW. cbn. split; [|exact I]. intros X. apply NC. left. right. right. left. unfold CTX in *. lia. }
  assert (AUX4 : auxv_okd (c_init_done (ctx st0)) m4 (bv_unsigned sp)).
  { eapply auxv_okd_frame; [exact AUX3| exact MU4| exact WM4|]. unfold seqW, AUXV_CELL, CTX, LIBC. constructor; [cbn; lia| constructor]. }
  (first [ pose proof ((meta_slot_bounds st2 m3 mm MR3 MSL)) as dR_5; dand4 dR_5 as Gpos GC GI _ | pose proof (meta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _) ]).
  (* [comment removed for export] *)
  eapply evt_cut. { eapply mm_call_walk. }
  cbv beta. intros ms' ->.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -144) by (subst sp'; apply unsigned_lit; lia).
  eapply implT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lia | rewrite SP'; lia | exact CLO
    | rewrite SP', EA; lia | rewrite TP; unfold PTP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  (* [comment removed for export] *)
  assert (REGS : s_regions stS = s_regions st2) by (rewrite ES; reflexivity).
  assert (SHS : s_shadow stS = s_shadow st2) by (rewrite ES; reflexivity).
  assert (GRS : s_groups stS = s_groups st2) by (rewrite ES; reflexivity).
  assert (ARS : s_areas stS = s_areas st2) by (rewrite ES; reflexivity).
  assert (TKS' : s_tick stS = s_tick st2) by (rewrite ES; reflexivity).
  assert (NRS : s_next_rid stS = s_next_rid st2) by (rewrite ES; reflexivity).
  assert (RSS : s_reserved stS = s_reserved st2) by (rewrite ES; reflexivity).
  assert (RECS : forall q, get_meta_rec stS q = get_meta_rec st2 q) by (intros q; rewrite ES; reflexivity).
  assert (ACTS : forall c', active stS c' = active st2 c') by (intros c'; unfold active; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (HS _)); reflexivity).
  assert (BRKS : c_brk (ctx stS) = c_brk (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (HS _))))).
  assert (CTRS : c_mmap_counter (ctx stS) = c_mmap_counter (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (HS _)))))).
  assert (FMHS : c_free_meta_head (ctx stS) = c_free_meta_head (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (proj2 (HS _))))))).
  assert (CONCS : forall q, conc stS q = conc st2 q) by (intros q; unfold conc, get_region; rewrite REGS; reflexivity).
  assert (MSLS : meta_slot stS mm) by (eapply meta_slot_same_areas; [exact ARS| exact MSL]).
  assert (TKS : ticks_ok stS) by (eapply ticks_ok_same; [exact SHS| exact TKS'| exact TK3]).
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR as (WF & _). (first [ pose proof (WF) as dR_6; dand4 dR_6 as RS0 WR0 DJ0 _ | pose proof WF as (RS0 & WR0 & DJ0 & _) ]).
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (first [ dex15 PO as v0' v1 v2 v3 v4' v5 v6 v7 v8 v9 v10 v11 v12 v13 m6; dand7 PO as -> MU6 WM6 MI6 ST6 ERR6 He | dand22 PO as v0' v1 v2 v3 v4' v5 v6 v7 v8 v9 v10 v11 v12 v13 m6 -> MU6 WM6 MI6 ST6 ERR6 He | destruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He) ]).
    cbn [mmap_val]. unfold mm_after. fold stS. destruct (mmap_answer_ok_err (live_ranges stS) nd e He) as [-> ->]. cbn [negb].
    rewrite as_free_meta_eq. cbn [as_kq].
    rewrite SP' in MU6, ST6. rewrite EA in MU6.
    replace (ret_pc (Z_to_bv 64 0x24374)) with (Z_to_bv 64 0x24374) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : mrep stS m6).
    { eapply (wrapper_munch_keeps stS m4 m6 (bv_unsigned sp - 144) lo MR4); [| exact WM6| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia].
      eapply munch_weaken; [| exact MU6]. intros y; cbn; lia. }
    (* [comment removed for export] *)
    pose proof (lf_freelist _ (isf_lf _ _ F2)) as FFL. change (fact_freelist (strip st2)) with (fact_freelist st2) in FFL.
    assert (FL : forall h, c_free_meta_head (ctx stS) = Some h ->
              meta_slot stS h /\ h <> mm /\ exists p, m_prev (get_meta_rec stS h) = Some p /\ meta_slot stS p /\ p <> mm).
    { intros h Hh. rewrite FMHS in Hh. (first [ pose proof ((FFL h Hh)) as dR_8; dand8 dR_8 as MSh MEMh NXh p HP MSp MEMp NXp | destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp) ]).
      change (meta_slot (strip st2) h) in MSh. change (get_meta_rec (strip st2) h) with (get_meta_rec st2 h) in MEMh, NXh, HP.
      change (meta_slot (strip st2) p) in MSp. change (get_meta_rec (strip st2) p) with (get_meta_rec st2 p) in MEMp, NXp.
      split; [eapply meta_slot_same_areas; [exact ARS| exact MSh]|].
      split; [intros ->; rewrite G0 in NXh; apply NXh; reflexivity|].
      exists p. rewrite RECS. split; [exact HP|]. split; [eapply meta_slot_same_areas; [exact ARS| exact MSp]|].
      intros ->. rewrite G0 in NXp. apply NXp. reflexivity. }
    iprefixT.
    eapply evt_cut. { eapply mm_ret_fail_walk. }
    cbv beta. intros ms' ->.
    eapply evt_cut. { rewrite <- (CONCS mm). subst sp'. unfold rFRM in FR6. eapply (rfailm2_walk stS mm MSLS FL); [exact MR6| exact MI6| exact FR6| lia]. }
    cbv beta. (intros ms'; (first [ intro dR_37; dex3 dR_37 as s6x m7 junk'; dand6 dR_37 as -> FR7 MU7 WM7 MI7 MR7 | intro dR_37; dand9 dR_37 as s6x m7 junk' -> FR7 MU7 WM7 MI7 MR7 | intros (s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7) ])).
    assert (LW : Forall (lowW (bv_unsigned sp)) (failW stS mm (bv_unsigned sp))).
    { eapply (failW_low stS mm m6 _ MR6 MSLS). intros h Hh. (first [ pose proof ((FL h Hh)) as dR_9; dand6 dR_9 as MSh _ p HP MSp _ | destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _) ]).
      split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
    assert (ST7 : stk rsegs m7 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [exact ST6| exact MU7| exact WM7| apply (lowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]]. }
    assert (ERR7 : rw_cells rsegs m7 (errno_addr tp) [C4 (Z_to_bv 64 (F_mm4hw.mmap_fix_errno e))]).
    { eapply rw_cells_transport; [exact ERR6| exact MU7| exact WM7|]. rewrite EA. apply (lowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold CTX; cbn; lia| lia]. }
    eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
    cbv beta. (intros ms'; (first [ intro dR_38; dex2 dR_38 as a1y a2y; destruct dR_38 as [-> ST8] | intro dR_38; dand4 dR_38 as a1y a2y -> ST8 | intros (a1y & a2y & -> & ST8) ])). apply evt_done.
    (* [comment removed for export] *)
    set (stF := as_fm_st stS mm) in *.
    (first [ pose proof ((fm_proj stS mm)) as dR_10; dand13 dR_10 as PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10 PF11 PF12 _ | destruct (fm_proj stS mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _) ]). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
    assert (FS : Forall (metaW (bv_unsigned sp) stS) (failW stS mm (bv_unsigned sp))).
    { apply (failW_shape stS mm _ MSLS). intros h Hh; (first [ pose proof ((FL h Hh)) as dR_11; dand6 dR_11 as MSh _ p HP MSp _ | destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _) ]); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
    assert (PE07 : pres_except (malloc_fp st0 stF lo (bv_unsigned sp)) m m7).
    { eapply pres_except_trans.
      - eapply pres_except_mono; [exact PE04|]. intros a Ha. eapply malloc_fp_mono; [| exact Ha]. intros rid r Hr. exists r. rewrite PF1, REGS. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia.
      - eapply pres_except_trans.
        + eapply pres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros X; apply NC; left; [left; lia| right; left; rewrite unsigned_lit by lia; lia].
        + eapply pres_except_of_munch'; [exact MU7| exact WM7|].
          intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          * cbn in E1, E2. subst lo' hi'. left. do 3 right.
            assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
            (first [ pose proof ((meta_chunk_facts stF m7 q MR7 MSq')) as dR_12; dand7 dR_12 as _ _ _ _ _ _ (rid0 & r0 & H0 & K0 & L0 & H0') | destruct (meta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')) ]).
            exists rid0, r0. split; [exact H0|]. split; [exact K0|].
            assert (EC : conc stF q = conc stS q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
          * inversion E; subst. left. right. right. left. unfold CTX in *. lia.
          * inversion E; subst. left. left. lia. }
    apply HK. unfold as_post2.
    do 14 eexists. exists m7, (Z_to_bv 64 (F_mm4hw.mmap_fix_errno e)). split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
    split; [eapply (auxv_okd_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
    split; [exact MR7|].
    split; [eapply ticks_ok_same; [rewrite PF2; exact SHS| rewrite PF6; exact TKS'| exact TK3]|].
    split. { eapply (unk_agree_xfer o st2 m3 stF m7 UA3).
      - rewrite PF2. exact SHS.
      - intros rid r Hk Hr. rewrite PF1, REGS in Hr. exact Hr.
      - intros b. rewrite PF3, GRS. split; intros X; exact X.
      - intros rid r off h Hr Hk Ho Hc NG.
        pose proof MR3 as (WF3 & _). (first [ pose proof (WF3) as dR_13; dand4 dR_13 as _ WR3 DJ3 _ | pose proof WF3 as (_ & WR3 & DJ3 & _) ]). (first [ pose proof ((WR3 _ _ Hr)) as dR_14; dand5 dR_14 as R0 _ _ RC _ | destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
        (first [ pose proof ((rregion_facts st2 m3 rid r MR3 Hr)) as dR_15; dand5 dR_15 as _ _ _ RI1 RI2 | destruct (rregion_facts st2 m3 rid r MR3 Hr) as (_ & _ & _ & RI1 & RI2) ]). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
        transitivity (m6 (wa (r_base r + off))).
        { apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
          pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          - cbn in E1, E2. subst lo' hi'. rewrite CONCS in Ha.
            assert (MSq2 : meta_slot st2 q) by (eapply meta_slot_same_areas; [symmetry; exact ARS| exact MSq]).
            (first [ pose proof ((meta_chunk_facts st2 m3 q MR3 MSq2)) as dR_16; dand7 dR_16 as _ _ _ _ _ GRG _ | destruct (meta_chunk_facts st2 m3 q MR3 MSq2) as (_ & _ & _ & _ & _ & GRG & _) ]). destruct (GRG rid r Hr Hk); lia.
          - inversion E; subst. unfold CTX in Ha. lia.
          - inversion E; subst. lia. }
        transitivity (m4 (wa (r_base r + off))).
        { apply MU6. rewrite wa_unsigned by lia. cbn. lia. }
        apply MU4. rewrite wa_unsigned by lia. unfold seqW, CTX. cbn. lia. }
    split; [exact PE07|].
    split. { split; [| rewrite PF7, NRS, <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite PF8, RSS, (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
             intros rid r Hr. rewrite <- REG1 in Hr. (first [ pose proof ((amr_regions _ _ _ REL rid r Hr)) as dR_17; dex1 dR_17 as r'; dand5 dR_17 as H' K' B' L' _ | pose proof ((amr_regions _ _ _ REL rid r Hr)) as dR_17; dand6 dR_17 as r' H' K' B' L' _ | destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _) ]). exists r'. rewrite PF1, REGS. auto. }
    split. { unfold brk_link_ps in *. rewrite PF11, BRKS. destruct (c_brk (ctx st2)) as [| |rid off]; auto.
             unfold conc, get_region. rewrite PF1, REGS. exact BL2. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite PF9, ACTS, (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ARS. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF6, TKS', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split; [rewrite PF12, CTRS; exact FC1|].
    left. reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (first [ dex15 PO as v0' v1 v2 v3 v4' v5 v6 v7 v8 v9 v10 v11 v12 v13 m6; dand7 PO as -> MU6 WM6 MI6 ST6 ERR6 AOK | dand22 PO as v0' v1 v2 v3 v4' v5 v6 v7 v8 v9 v10 v11 v12 v13 m6 -> MU6 WM6 MI6 ST6 ERR6 AOK | destruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & AOK) ]).
    cbn [mmap_val]. unfold mm_after. fold stS.
    destruct (mmap_answer_ok (live_ranges stS) nd xa) eqn:VOK. 2:{ cbn [negb]. apply implT_undef. }
    cbn [negb].
    (first [ pose proof ((mmap_answer_ok_addr (Clg:=Clg) (live_ranges stS) nd xa ltac:(lia) AOK VOK)) as dR_19; dand5 dR_19 as X0 XA XC XRF ISE | destruct (mmap_answer_ok_addr (Clg:=Clg) (live_ranges stS) nd xa ltac:(lia) AOK VOK) as (X0 & XA & XC & XRF & ISE) ]). rewrite ISE.
    rewrite SP' in MU6, ST6.
    assert (RU : round_up_pg nd = nd) by (unfold round_up_pg; change (PGSZ - 1) with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia).
    rewrite RU in XC, XRF.
    assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : mrep stS m6).
    { eapply (mrep_transport_high stS m4 m6); [exact MR4| exact MU6| exact WM6| intros lo' hi' [E|[]]; inversion E; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. }
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid stS). set (r0 := {| r_kind := RKGroup; r_base := xa; r_len := nd |}).
    set (stN := set_next_rid (N.succ rid) (set_regions (<[rid:=r0]> (s_regions stS)) stS)).
    assert (EstN : stN = fst (new_region RKGroup xa nd stS)) by reflexivity.
    pose proof (mf_ptrs _ _ MF2) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) stS).
    { rewrite ES. apply ptrs_in_upd_ctx_scalar; try (intros cc; pose proof (HS cc) as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); assumption).
      eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. rewrite NRS. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; rewrite NRS; lia)) as [FRr FRs].
    unfold F_mm4hw.mmap_raw in ST6 |- *. cbn [negb] in ST6 |- *. rewrite mmap_len_round_up, RU in ST6 |- *.
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    set (mz := apply_zeros m6 [(wa xa, Z_to_bv 64 nd)]) in *.
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + nd <= a) -> mz (wa a) = m6 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + nd -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : mrep stN mz).
    { rewrite EstN. eapply (mrep_new_region (Clg:=Clg) stS m6 mz xa nd RKGroup MR6 PT1 ltac:(rewrite SHS; exact FRs) X0 XA ltac:(lia));
        rewrite ?mmap_len_round_up, ?RU; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    pose proof MR6 as (WF6 & _). (first [ pose proof (WF6) as dR_20; dand4 dR_20 as RS6 WR6 DJ6 _ | pose proof WF6 as (RS6 & WR6 & DJ6 & _) ]).
    assert (XI : xa + nd <= 0x10000 \/ 0x63000 <= xa).
    { assert (RFimg : ranges_free p0_reserved xa nd = true).
      { apply ranges_free_intro. intros b kk HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS6. exact HI. }
      apply (reserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv rsegs mz).
    { unfold mz. apply (mem_inv_zeros rsegs m6 xa nd); try lia; [exact MI6|]. intros w Hw. apply p0_ro_addr_false. lia. }
    assert (MUz : munch [(xa, xa + nd)] m6 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono rsegs m6 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono rsegs m6 xa nd); try lia; exact Hw).
    assert (FRz : rw_cells rsegs mz (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR6| exact MUz| exact WMz|]. cbn. lia. }
    assert (STz : stk rsegs mz lo (bv_unsigned sp + -144)) by exact ST6.
    assert (ERRz : rw_cells rsegs mz (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [exact ERR6| exact MUz| exact WMz|]. rewrite EA. cbn. lia. }
    (* [comment removed for export] *)
    assert (MSLN : meta_slot stN mm) by (eapply meta_slot_same_areas; [| exact MSLS]; rewrite EstN; reflexivity).
    assert (RECN : get_meta_rec stN mm = meta0) by (rewrite EstN; change (get_meta_rec (fst (new_region RKGroup xa nd stS)) mm) with (get_meta_rec stS mm); rewrite RECS; exact G0).
    assert (CTRN : c_mmap_counter (ctx stN) = c_mmap_counter (ctx st2)) by (rewrite EstN; change (ctx (fst (new_region RKGroup xa nd stS))) with (ctx stS); exact CTRS).
    assert (GCN : conc stN mm = conc st2 mm).
    { rewrite <- CONCS. rewrite EstN. apply nr_conc. cbn [fst].
      (first [ dex3 MSLS as ar arr kk; dand3 MSLS as Ha Hk -> | dand6 MSLS as ar arr kk Ha Hk -> | destruct MSLS as (ar & arr & kk & Ha & Hk & ->) ]). unfold aadd. cbn [fst]. intros E.
      (first [ dand10 PT1 as _ _ _ _ _ _ _ _ P9 _ | destruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _) ]). destruct (P9 _ _ Ha) as [X _]. exact (X E). }
    replace (ret_pc (Z_to_bv 64 0x24374)) with (Z_to_bv 64 0x24374) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    iprefixT.
    eapply evt_cut.
    { rewrite <- GCN. subst sp'.
      eapply (mm_ret_ok_walk (Clg:=Clg) stN sc c size nd xa (c_mmap_counter (ctx st2)) mm SC ltac:(lia) SZ ltac:(lia) NDM X0 ltac:((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia) MSLN RECN CTRN FC1);
        [exact MRz| exact MIz]. }
    cbv beta. (intros ms'; (first [ intro dR_39; dex3 dR_39 as xa3 xa4 m8; dand6 dR_39 as -> MU8 WM8 MI8 MR8 CTR8 | intro dR_39; dand9 dR_39 as xa3 xa4 m8 -> MU8 WM8 MI8 MR8 CTR8 | intros (xa3 & xa4 & m8 & -> & MU8 & WM8 & MI8 & MR8 & CTR8) ])).
    set (stT := mm_st4 stN nd mm) in *.
    (* [comment removed for export] *)
    assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (ML : 0 <= Z.shiftr nd 12 < 2^52) by (rewrite ND12; Z.div_mod_to_equations; lia).
    assert (RECT : get_meta_rec stT mm = {| m_prev := None; m_next := None; m_mem := None; m_avail := 0; m_freed := 0; m_last_idx := 0; m_freeable := 0; m_sizeclass := 0; m_maplen := Z.shiftr nd 12 |}).
    { unfold stT, mm_st4. rewrite rec_upd_ctx. unfold upd_meta. rewrite get_meta_rec_put_same, RECN. unfold m_set_maplen, meta0. cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass].
      f_equal. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (HrT : (s_regions stT) !! rid = Some r0) by (unfold stT, mm_st4, upd_meta; cbn; first [apply lookup_insert_eq | rewrite EstN; apply nr_lookup_new]).
    assert (GNT : forall off, (s_groups stT) !! (rid, off) = None).
    { intros off. change (s_groups stT) with (s_groups stS). destruct ((s_groups stS) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
      (first [ dand10 PT1 as _ _ _ _ _ _ _ _ _ P10 | destruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10) ]). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
    assert (SHT : (s_shadow stT) !! rid = None) by (change (s_shadow stT) with (s_shadow stS); rewrite SHS; exact FRs).
    assert (ACTT : active stT sc = None).
    { unfold stT, mm_st4. unfold active, ctx, upd_ctx, upd_meta. cbn. change (c_active (s_ctx stS) !! sc) with (active stS sc). rewrite ACTS, (amr_active _ _ _ REL). exact ACT0. }
    assert (TKT : ticks_ok stT).
    { eapply ticks_ok_same; [| | exact TK3]; [change (s_shadow stT) with (s_shadow stS); exact SHS| change (s_tick stT) with (s_tick stS); exact TKS']. }
    pose proof (mm_ai_range stN c size nd mm ltac:(lia) SZ) as AIR.
    eapply evt_cut.
    { replace (Z_to_bv 64 xa) with (Z_to_bv 64 (conc stT (rid, 0))) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; f_equal; lia).
      change (conc stN mm) with (conc stT mm).
      eapply (tail_walk (Clg:=Clg) stT sc c (mm_ai c size) (Z.shiftr nd 12) mm (rid, 0) r0 SC ltac:(lia) AIR ML);
        [eapply meta_slot_same_areas; [| exact MSLN]; reflexivity| exact RECT| exact HrT| reflexivity| cbn; lia| cbn; reflexivity
        | cbn [snd r_len r0]; rewrite RU; lia| apply GNT
        | intros b' gh Hb' Hf'; exfalso; destruct b' as [b1 b2]; cbn in Hf'; subst b1; rewrite GNT in Hb'; discriminate
        | intros o' v t Ho Hc; exfalso; unfold get_shadow in Hc; rewrite SHT in Hc; cbn in Hc; rewrite lookup_empty in Hc; discriminate
        | change (usage stT sc) with (usage stS sc); rewrite US; apply URall
        | exact ACTT| exact TKT| exact MR8| exact MI8]. }
    cbv beta. (intros ms'; (first [ intro dR_40; dex6 dR_40 as s0x a1x a2x a3x a4x m9; dand6 dR_40 as -> MU9 WM9 MI9 MR9 TK9 | intro dR_40; dand12 dR_40 as s0x a1x a2x a3x a4x m9 -> MU9 WM9 MI9 MR9 TK9 | intros (s0x & a1x & a2x & a3x & a4x & m9 & -> & MU9 & WM9 & MI9 & MR9 & TK9) ])).
    assert (GT : conc stT mm = conc st2 mm) by (change (conc stT mm) with (conc stN mm); exact GCN).
    assert (PT : conc stT (rid, 0) = xa) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; lia).
    (* [comment removed for export] *)
    assert (FR9 : rw_cells rsegs m9 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [| exact MU9| exact WM9| unfold tailW; rewrite GT, PT; unfold CTX; cbn; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia].
      eapply rw_cells_transport; [exact FRz| exact MU8| exact WM8|]. rewrite GCN. unfold CTX. cbn. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
    assert (ST9 : stk rsegs m9 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [| exact MU9| exact WM9| unfold tailW; rewrite GT, PT; unfold CTX; cbn; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia].
      eapply stk_transport_disjoint; [exact STz| exact MU8| exact WM8| rewrite GCN; unfold CTX; cbn; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. }
    eapply evt_cut. { unfold rFRM in FR9. eapply (ras_ret0 sp gp tp); [exact MR9| exact MI9| exact FR9| exact ST9| exact CLO| lia]. }
    cbv beta. (intros ms'; (first [ intro dR_41; dex2 dR_41 as a1y a2y; destruct dR_41 as [-> ST10] | intro dR_41; dand4 dR_41 as a1y a2y -> ST10 | intros (a1y & a2y & -> & ST10) ])). apply evt_done.
    rewrite (ag_tail_kq_eq sc k bail stT mm (rid, 0) c (mm_ai c size)); [| rewrite RECT; reflexivity| rewrite RECT; reflexivity| exact ACTT].
    apply HK.
    (* [comment removed for export] *)
    set (ai := mm_ai c size) in *. set (ml := Z.shiftr nd 12) in *.
    set (stF := st_model stT sc c ai mm (rid, 0)).
    assert (C32 : 1 <= c <= 32) by lia.
    assert (EML : nd = 4096 * ml) by (subst ml; rewrite ND12; Z.div_mod_to_equations; lia).
    assert (ML28 : 1 <= ml < 2^28) by lia.
    assert (Hk0 : r_kind r0 = RKGroup) by reflexivity.
    assert (LEN0 : r_len r0 = nd) by reflexivity.
    assert (MST : meta_slot stT mm) by (eapply meta_slot_same_areas; [| exact MSLN]; reflexivity).
    assert (Esz : size = 16 * size_class sc) by reflexivity.
    assert (NDC' : c = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * c + 16 <= nd /\ nd < 16 * size_class sc * c + 16 + 4096).
    { pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 _]. pose proof (round_up_pg_props (size * c + 16) ltac:(nia)) as [N1 _].
      rewrite <- Esz. destruct NDC as [[Ec En]|[LE En]]; [left; split; [exact Ec| rewrite En; lia] | right; split; [exact LE| rewrite En at 1; lia]]. }
    (first [ pose proof ((sm_slot_ok stT sc c ai ml mm rid r0 SC C32 AIR ML28 RECT HrT Hk0 SHT GNT req nd RQ FIT LEN0 EML NDR ltac:(lia) NDC' MST)) as dR_24; dand4 dR_24 as SO STR S16 SND | destruct (sm_slot_ok stT sc c ai ml mm rid r0 SC C32 AIR ML28 RECT HrT Hk0 SHT GNT req nd RQ FIT LEN0 EML NDR ltac:(lia) NDC' MST) as (SO & STR & S16 & SND) ]).
    fold stF in SO, STR, S16, SND.
    (first [ pose proof ((sm_proj stT sc c ai mm rid)) as dR_25; dand10 dR_25 as PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10 | pose proof (sm_proj stT sc c ai mm rid) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10) ]).
    fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
    assert (MRF : mrep stF m9) by (exact (mrep_st_model (Clg:=Clg) stT sc c ai ml mm (rid, 0) SC C32 RECT ltac:(cbn; lia) m9 MR9)).
    assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK9]; reflexivity).
    assert (MSF : meta_slot stF mm) by (apply (proj1 (sm_meta_slot stT sc c ai mm rid mm)); exact MST).
    (* [comment removed for export] *)
    assert (REGT : s_regions stT = <[rid:=r0]> (s_regions stS)) by reflexivity.
    assert (SHT' : s_shadow stT = s_shadow st2) by (transitivity (s_shadow stS); [reflexivity| exact SHS]).
    assert (GRT : s_groups stT = s_groups st2) by (transitivity (s_groups stS); [reflexivity| exact GRS]).
    assert (ART : s_areas stT = s_areas st2) by (transitivity (s_areas stS); [reflexivity| exact ARS]).
    assert (TKT' : s_tick stT = s_tick st2) by (transitivity (s_tick stS); [reflexivity| exact TKS']).
    assert (NRT : s_next_rid stT = N.succ rid) by reflexivity.
    assert (RST : s_reserved stT = s_reserved st2) by (transitivity (s_reserved stS); [reflexivity| exact RSS]).
    assert (BRKT : c_brk (ctx stT) = c_brk (ctx st2)) by (transitivity (c_brk (ctx stS)); [reflexivity| exact BRKS]).
    assert (ACTT' : forall c', active stT c' = active st2 c') by (intros c'; transitivity (active stS c'); [reflexivity| apply ACTS]).
    assert (GF : conc stF mm = conc st2 mm) by (rewrite (sm_conc stT sc c ai mm rid); exact GT).
    assert (HOLD : forall q rq, (s_regions st2) !! q = Some rq -> (s_regions stF) !! q = Some rq /\ q <> rid).
    { intros q rq Hq. assert (NE : q <> rid) by (intros ->; rewrite FRr in Hq; discriminate).
      split; [| exact NE]. rewrite PF1, REGT, lookup_insert_ne, REGS by congruence. exact Hq. }
    assert (MREL0S : forall q rq, (s_regions st0) !! q = Some rq ->
              exists r', (s_regions stS) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
    { intros q rq Hq. (first [ pose proof ((mrel_regions _ _ (er_mrel _ _ ER) q rq Hq)) as dR_26; dex1 dR_26 as r1; dand4 dR_26 as H1 K1 B1 L1 | pose proof ((mrel_regions _ _ (er_mrel _ _ ER) q rq Hq)) as dR_26; dand5 dR_26 as r1 H1 K1 B1 L1 | destruct (mrel_regions _ _ (er_mrel _ _ ER) q rq Hq) as (r1 & H1 & K1 & B1 & L1) ]). rewrite <- REG1 in H1.
      (first [ pose proof ((amr_regions _ _ _ REL q r1 H1)) as dR_27; dex1 dR_27 as r2; dand5 dR_27 as H2 K2 B2 L2 _ | pose proof ((amr_regions _ _ _ REL q r1 H1)) as dR_27; dand6 dR_27 as r2 H2 K2 B2 L2 _ | destruct (amr_regions _ _ _ REL q r1 H1) as (r2 & H2 & K2 & B2 & L2 & _) ]). exists r2. rewrite REGS. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; try congruence. lia. }
    assert (FRESH : forall a, xa <= a < xa + nd -> fresh_addr st0 a).
    { intros a Ha. eapply (fresh_addr_anti st0 stS); [| exact MREL0S|].
      - rewrite RS6, <- RS0. exact (mrel_reserved _ _ (er_mrel _ _ ER)).
      - split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|]. eapply (ranges_free_sub _ xa nd); [exact XRF| lia| lia| lia]. }
    assert (HFP2 : forall a, malloc_fp st0 st2 lo (bv_unsigned sp) a -> malloc_fp st0 stF lo (bv_unsigned sp) a).
    { intros a Ha. eapply malloc_fp_mono; [| exact Ha]. intros q rq Hq. exists rq. split; [apply (proj1 (HOLD q rq Hq))|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. lia. }
    (* [comment removed for export] *)
    assert (OLDW : forall q rq off, (s_regions st2) !! q = Some rq -> r_kind rq = RKGroup -> 0 <= off < round_up_pg (r_len rq) ->
              m9 (wa (r_base rq + off)) = m3 (wa (r_base rq + off))).
    { intros q rq off Hq Hk Ho.
      assert (HqS : (s_regions stS) !! q = Some rq) by (rewrite REGS; exact Hq).
      (first [ pose proof ((WR6 _ _ HqS)) as dR_28; dand5 dR_28 as R0 _ _ RC _ | destruct (WR6 _ _ HqS) as (R0 & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      (first [ pose proof ((rregion_facts st2 m3 q rq MR3 Hq)) as dR_29; dand5 dR_29 as _ _ _ RI1 RI2 | destruct (rregion_facts st2 m3 q rq MR3 Hq) as (_ & _ & _ & RI1 & RI2) ]). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      (first [ pose proof ((meta_chunk_facts st2 m3 mm MR3 MSL)) as dR_30; dand7 dR_30 as _ _ _ _ _ GRG _ | destruct (meta_chunk_facts st2 m3 mm MR3 MSL) as (_ & _ & _ & _ & _ & GRG & _) ]). pose proof (GRG q rq Hq Hk) as GRq.
      pose proof (In_live_ranges stS q rq HqS) as HIq. unfold region_live_range in HIq. rewrite Hk in HIq.
      pose proof (ranges_free_In _ _ _ _ _ XRF HIq) as DJq.
      pose proof (lr_lo_group rq Hk) as LRq.
      (* [comment removed for export] *)
      transitivity (m8 (wa (r_base rq + off))). { apply MU9. rewrite wa_unsigned by (try (generalize alloc_ceiling_val); clear - Ho R0 RC; try pose proof alloc_ceiling_val; lia). unfold tailW. rewrite GT, PT. cbn. unfold CTX. try (generalize alloc_ceiling_val); clear - Ho R0 RC RI2 GRq DJq SC SND S16; try pose proof alloc_ceiling_val; lia. }
      transitivity (mz (wa (r_base rq + off))). { apply MU8. rewrite wa_unsigned by (try (generalize alloc_ceiling_val); clear - Ho R0 RC; try pose proof alloc_ceiling_val; lia). rewrite GCN. cbn. unfold CTX. try (generalize alloc_ceiling_val); clear - Ho R0 RI2 GRq; try pose proof alloc_ceiling_val; lia. }
      transitivity (m6 (wa (r_base rq + off))). { apply ZO; [try (generalize alloc_ceiling_val); clear - Ho R0 RC; try pose proof alloc_ceiling_val; lia | try (generalize alloc_ceiling_val); clear - Ho R0 DJq; try pose proof alloc_ceiling_val; lia]. }
      transitivity (m4 (wa (r_base rq + off))). { apply MU6. rewrite wa_unsigned by (try (generalize alloc_ceiling_val); clear - Ho R0 RC; try pose proof alloc_ceiling_val; lia). cbn. try (generalize alloc_ceiling_val); clear - Ho R0 RC CLO' LO ASG; try pose proof alloc_ceiling_val; lia. }
      apply MU4. rewrite wa_unsigned by (try (generalize alloc_ceiling_val); clear - Ho R0 RC; try pose proof alloc_ceiling_val; lia). unfold seqW, CTX. cbn. try (generalize alloc_ceiling_val); clear - Ho R0 RI2; try pose proof alloc_ceiling_val; lia. }
    assert (UAF : unk_agree stF o m9).
    { eapply (unk_agree_transfer st2 stF o m3 m9 UA3). intros q rq Hq Hk.
      rewrite PF1, REGT, REGS in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      - right. rewrite lookup_insert_eq in Hq. inversion Hq; subst rq. cbn [r_len r_base]. intros off h Ho Hc.
        rewrite (sm_cell_read stT sc c ai mm rid SHT off ltac:(lia)) in Hc.
        destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T. apply (sm_grp_hdr_cov stT sc c ai mm rid SC). lia.
      - left. rewrite lookup_insert_ne in Hq by congruence.
        split; [exact Hq|].
        split. { rewrite (sm_shadow_other stT sc c ai mm rid q NE). unfold get_shadow. rewrite SHT'. reflexivity. }
        split. { intros off X. apply (sm_grp_hdr_cov_old stT sc c ai mm rid GNT). eapply grp_hdr_cov_same; [exact GRT| exact X]. }
        intros off h Ho Hc NG. exact (OLDW q rq off Hq Hk Ho). }
    assert (PE09 : pres_except (malloc_fp st0 stF lo (bv_unsigned sp)) m m9).
    { eapply pres_except_trans. { eapply pres_except_mono; [exact PE04| exact HFP2]. }
      eapply pres_except_trans. { eapply pres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. left. left. lia. }
      eapply pres_except_trans. { eapply pres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. do 4 right. apply FRESH. lia. }
      eapply pres_except_trans.
      { eapply pres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. rewrite GCN. cbn. split; [|split; [|exact I]]; intros X; apply NC.
        - left. do 3 right. (first [ pose proof ((meta_chunk_facts stF m9 mm MRF MSF)) as dR_31; dand7 dR_31 as _ _ _ _ _ _ (rid0 & rr0 & H0 & K0 & L0 & H0') | destruct (meta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')) ]).
          exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
        - left. right. right. left. unfold CTX in *. lia. }
      eapply pres_except_of_munch; [exact MU9| exact WM9|]. intros a Ha NC. unfold tailW. rewrite GT, PT. cbn.
      split; [|split; [|split; [|split; [|exact I]]]]; intros X; apply NC.
      - left. right. right. left. unfold CTX in *. lia.
      - left. do 3 right. (first [ pose proof ((meta_chunk_facts stF m9 mm MRF MSF)) as dR_32; dand7 dR_32 as _ _ _ _ _ _ (rid0 & rr0 & H0 & K0 & L0 & H0') | destruct (meta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')) ]).
        exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
      - do 4 right. apply FRESH. lia.
      - left. right. right. left. unfold CTX in *. lia. }
    assert (ERR9 : rw_cells rsegs m9 (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [| exact MU9| exact WM9|].
      - eapply rw_cells_transport; [exact ERRz| exact MU8| exact WM8|]. rewrite EA, GCN. cbn. unfold CTX. lia.
      - unfold tailW. rewrite GT, PT, EA. cbn. unfold CTX. lia. }
    unfold as_post2.
    do 14 eexists. exists m9, errv'. split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST10|]. split; [exact ERR9|].
    split; [eapply (auxv_okd_malloc_fp_ER st0 st m MR ER stF m9); [exact MRF| exact AUX| exact PE09| exact CLO| lia]|].
    split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE09|].
    split. { split.
      - intros q rq Hq. rewrite <- REG1 in Hq. (first [ pose proof ((amr_regions _ _ _ REL q rq Hq)) as dR_33; dex1 dR_33 as r'; dand5 dR_33 as H' K' B' L' _ | pose proof ((amr_regions _ _ _ REL q rq Hq)) as dR_33; dand6 dR_33 as r' H' K' B' L' _ | destruct (amr_regions _ _ _ REL q rq Hq) as (r' & H' & K' & B' & L' & _) ]).
        exists r'. split; [apply (proj1 (HOLD q r' H'))|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
      - rewrite PF6, NRT. pose proof (amr_next_rid _ _ _ REL) as NX1. pose proof (tr_next _ _ _ TR) as NX0. subst rid. rewrite NRS. lia.
      - rewrite PF7, RST, (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
    split. { unfold brk_link_ps in BL2 |- *. rewrite PF8, BRKT. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:EB; auto.
             rewrite (sm_conc stT sc c ai mm rid). rewrite <- (CONCS (brid, boff)) in BL2.
             replace (conc stT (brid, boff)) with (conc stS (brid, boff)); [exact BL2|].
             change (conc stT (brid, boff)) with (conc stN (brid, boff)). rewrite EstN. symmetry. apply nr_conc. cbn [fst].
             (first [ dand8 PT1 as _ _ _ _ _ _ P7 _ | destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _) ]). rewrite BRKS in P7. first [rewrite EB in P7; exact P7 | exact P7]. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite (sm_active stT sc c ai mm rid). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite ACTT', (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ART. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF5, TKT', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros _ rid' S len RS o' v t Ho Hc. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        rewrite (sm_cells_none stT sc c ai mm rid SHT) in Hc. discriminate.
      - intros _ _ rid' S len RS o' Ho. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        split; [apply (sm_cells_none stT sc c ai mm rid SHT)|].
        split; [apply (sm_hav_none stT sc c ai mm rid SHT); lia| apply (sm_havp_none stT sc c ai mm rid SHT)]. }
    split. { rewrite PF9, CTR8. unfold u32. Z.div_mod_to_equations. lia. }
    right. split; [lia|]. exists mm, (rid, 0), r0.
    split; [rewrite (sm_active stT sc c ai mm rid), Z.eqb_refl; reflexivity|]. split; [exact SO|]. split.
    + intros a Ha. replace (r_base r0) with xa in Ha by reflexivity. cbn [fst snd] in Ha. do 4 right. apply FRESH. rewrite Z.mul_0_r in Ha. lia.
    + intros _. cbn [fst snd]. replace (0 + (16 + get_stride (get_meta_rec stF mm) * 0) + -3) with 13 by lia.
      apply (sm_rdv stT sc c ai mm rid SHT).
Qed.
End LEVEL.
End RASlt5l.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlxag OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl4er.RASlt5l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.RASltfw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl4er.RASlu8u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl4er.RASlpv4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall8ro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_sy88u MRep MRepAux F_mm4hw RAlllfc RF_mx3o Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlfjn.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_mm4hw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RF_m79e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.ASlot_W8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RASlxag OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.RASltfw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl4er.RASlu8u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl4er.RASlpv4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlfjn.

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Theorem alloc_slot_ok (am_pre : mstate -> Prop) :
  alloc_meta_stmt am_pre -> AMP_AS am_pre -> forall f, alloc_slot_stmt2 f.
Proof.
  intros AM AMP f. induction f as [|f IHf].
  - intros R k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv
           PRE MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK.
    cbn [alloc_slot]. apply implT_undef.
  - intros R k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv
           PRE MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK.
    destruct PRE as ((LB & AR & IS) & ER & AC & SC & RQ & FIT).
    pose proof (Mall8ro.ist_facts_proof st0 LB st AR IS) as F0.
    pose proof (AS_STACK_ge sc) as ASG.
    rewrite (alloc_slot_S full_lay f sc req k bail st). subst a0.
    eapply (ta_phase (Clg:=Clg) (as_k full_lay f sc req k bail) bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
              (taf_of_facts st LB sc F0 SC) SC CLO ltac:(lia)).
    + (* [comment removed for export] *)
      intros stX g3 msk kk m' t0' t1' a1' a2' a3' a4' a5' a6' a7' TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
      exact (hk1_ok f k bail o s Q ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv
                AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK stX g3 msk kk m' t0' t1' a1' a2' a3' a4' a5' a6' a7' TR HA GM MSK MR0 LBK KK MR' MI' ST' PE).
    + reflexivity.
    + exact MR.
    + exact MI.
    + exact ST.
    + (* [comment removed for export] *)
      intros st1 m' t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' junk TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
      unfold as_k. cbn [Z.eqb negb].
      eapply (ag_phase f k bail o s Q ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv
                AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK am_pre AM AMP); [| exact TF| exact TR| exact ACT0| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      (* [comment removed for export] *)
      refine (hag_ok f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req AR SC RQ FIT _ _).
      * (* [comment removed for export] *)
        exact (rhmm_ok k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req
                 AR ER SC RQ FIT MR AUX CLO LO TP A1 HK).
      * (* [comment removed for export] *)
        refine (hnest_ok f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc AR ER SC MR CLO LO TP IHf _ _).
        -- exact (nfail_ok f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req errv
                   AR IS ER SC RQ MR AUX CLO LO ERR TP HK).
        -- exact (nsucc_ok f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req errv
                   AR IS ER SC RQ FIT MR AUX CLO LO ERR TP HK).
Qed.

End CEIL.
