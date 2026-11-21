(** * Bridge.Infl.IStep — one trip of the mode machine (pair I3, the step half).

    S5's [dispatch] is an [if] chain on the integer mode, RT's [inf_step] a [match] on the
    [Mode]; [hdr_rel] equates S5's mode with [m_val] of RT's, so the two select the same
    arm.  [trip_ok] is the union of the per-arm lemmas over the modes [imode] admits. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl IRelInfl14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IArmHead IArmType IArmStored
  IArmCheck IArmTable IArmLen IArmLit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma inv_mode : forall w q, inv w q -> IS.is_mode (IS.w_s w) = RI.m_val (RI.q_mode q).
Proof. intros w q [[Hrel _] _]. exact (proj1 (proj1 (proj1 Hrel))). Qed.

Ltac dispatch_to m :=
  unfold IA.dispatch, IS.abind, IS.gs;
  match goal with H : IS.is_mode (IS.w_s ?w) = _ |- _ => rewrite H end;
  cbn [RI.m_val];
  cbv [IS.HEAD IS.FLAGS IS.TIME IS.OS IS.EXLEN IS.EXTRA IS.NAME IS.COMMENT IS.HCRC IS.DICTID
       IS.DICT IS.TYPE IS.TYPEDO IS.STORED IS.COPY_ IS.COPY IS.TABLE IS.LENLENS IS.CODELENS
       IS.LEN_ IS.LEN IS.LENEXT IS.DIST IS.DISTEXT IS.MATCH IS.LIT IS.CHECK IS.LENGTH IS.DONE
       IS.BAD IS.MEM];
  cbn [Z.eqb Pos.eqb].

Theorem trip_ok : forall c w q,
  ctx_rel FL c -> inv w q ->
  step_ok (IA.dispatch IS.ivar_ref FL w) (RI14.inf_step14 c q).
Proof.
  intros c w q Hc Hi.
  pose proof (inv_mode w q Hi) as Hm.
  pose proof Hi as [_ Hmd]. unfold imode in Hmd.
  unfold RI14.inf_step14. revert Hm Hmd.
  destruct (RI.q_mode q) eqn:E; intros Hm Hmd; cbv zeta in Hmd; try contradiction; dispatch_to E.
  - apply arm_HEAD_ok; assumption.
  - apply arm_DICTID_ok; assumption.
  - apply arm_TYPE_ok; assumption.
  - apply arm_TYPEDO_ok; [assumption | exact (proj1 Hi) | left; assumption].
  - apply arm_STORED_ok; assumption.
  - apply arm_COPY__ok; [exact (proj1 Hi) | assumption | exact Hmd].
  - apply arm_COPY_ok; [exact (proj1 Hi) | assumption | exact Hmd].
  - apply arm_TABLE_ok; assumption.
  - apply arm_LEN__ok; assumption.
  - apply arm_LEN_ok; assumption.
  - apply arm_MATCH_ok; assumption.
  - apply arm_LIT_ok; assumption.
  - apply arm_CHECK_ok; assumption.
Qed.
