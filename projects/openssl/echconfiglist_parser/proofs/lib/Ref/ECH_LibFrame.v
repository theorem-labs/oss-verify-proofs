(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState ECH_C2_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma magree_of_munch : forall (R : Z -> Prop) W m m',
  munch W m m' -> wmono rsegs m m' -> (forall a, 0 <= a < 2^64 -> R a -> outside W a) -> magree R m m'.
Proof.
  intros R W m m' MU WM HO a Ha Hr. split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. apply HO; assumption.
  - intros Hw. apply WM. exact Hw.
Qed.

(* [comment removed for export] *)
Definition off_libx (iv : Z * Z) : Prop :=
  snd iv <= IMG_LO \/ IMG_HI <= fst iv \/ (RERRNO <= fst iv /\ snd iv <= RERRNO + 4).

Lemma LIBX_outside : forall W a, Forall off_libx W -> rin_ivs LIBX a -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a FW HX; [exact I|].
  cbn. split; [| apply IH; [exact (Forall_inv_tail FW)| exact HX]].
  pose proof (Forall_inv FW) as K. unfold off_libx, IMG_LO, IMG_HI, RERRNO in K. cbn [fst snd] in K.
  unfold LIBX, LIBX0 in HX. cbn [rin_ivs fst snd] in HX. lia.
Qed.

Lemma magree_libx_of_munch : forall W m m',
  munch W m m' -> wmono rsegs m m' -> Forall off_libx W -> magree (lib_addr []) m m'.
Proof.
  intros W m m' MU WM FW. eapply magree_of_munch; [exact MU| exact WM|].
  intros a Ha [HX|(b & [] & _)]. apply LIBX_outside; assumption.
Qed.

Lemma CTX_statics_munch : forall W m m' x,
  CTX_statics m x -> munch W m m' -> wmono rsegs m m' -> Forall off_libx W -> CTX_statics m' x.
Proof. intros W m m' x CS MU WM FW. eapply CTX_statics_frame; [exact CS| eapply magree_libx_of_munch; eassumption]. Qed.

Lemma ERR_statics_munch : forall W m m' c,
  ERR_statics m c -> munch W m m' -> wmono rsegs m m' -> Forall off_libx W -> ERR_statics m' c.
Proof. intros W m m' c ES MU WM FW. eapply ERR_statics_frame; [exact ES| eapply magree_libx_of_munch; eassumption]. Qed.

(* [comment removed for export] *)
Definition chain_sep (c : errchain) : Prop :=
  let es := blk_addr (ec_es c) in
     (blk_addr (ec_mkey c) + 72 <= es \/ es + ERRST_SIZE <= blk_addr (ec_mkey c))
  /\ (blk_addr (ec_sa c) + 32 <= es \/ es + ERRST_SIZE <= blk_addr (ec_sa c))
  /\ (blk_addr (ec_nodes c) + 128 <= es \/ es + ERRST_SIZE <= blk_addr (ec_nodes c)).

(* [comment removed for export] *)
Definition chain_free (c : errchain) (lo : Z) (iv : Z * Z) : Prop :=
  lo <= fst iv \/ (IMG_LO <= fst iv /\ snd iv <= IMG_HI)
  \/ (chain_sep c /\ blk_addr (ec_es c) <= fst iv /\ snd iv <= blk_addr (ec_es c) + ERRST_SIZE).

Lemma ERR_chain_munch : forall LIB W m m' c lo,
  ERR_chain LIB m c -> chain_below c lo -> munch W m m' -> wmono rsegs m m' -> Forall (chain_free c lo) W -> ERR_chain LIB m' c.
Proof.
  intros LIB W m m' c lo EC CB MU WM FW. unfold ERR_chain, sa_cells in *.
  destruct EC as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
  pose proof (Forall_inv RR) as R2. pose proof (Forall_inv (Forall_inv_tail RR)) as R3.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RR))) as R4.
  unfold rblock_range in R2, R3, R4. unfold chain_below in CB.
  assert (DJ : forall A n, (A = blk_addr (ec_mkey c) + O_MKEY_ERR /\ n = 8) \/ (A = blk_addr (ec_sa c) /\ n = 32) \/ (A = blk_addr (ec_nodes c) /\ n = 8) ->
               disjoint_from W A n).
  { intros A n HA. clear - FW HA CB R2 R3 R4 Z2 Z3 Z4. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
    pose proof (Forall_inv FW) as K. unfold chain_free, chain_sep, IMG_LO, IMG_HI, ERRST_SIZE, O_MKEY_ERR in *. cbn [fst snd] in K. cbv zeta in K.
    rewrite Z2 in R2. rewrite Z3 in R3. rewrite Z4 in R4. lia. }
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - eapply rw_cells_transport; [exact K2| exact MU| exact WM|]. apply DJ. left. split; reflexivity.
  - eapply rw_cells_transport; [exact K3| exact MU| exact WM|]. apply DJ. right; left. split; reflexivity.
  - eapply rw_cells_transport; [exact K4| exact MU| exact WM|]. apply DJ. right; right. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ERRST_munch : forall LB W m m' a E,
  ERRST LB m a E -> munch W m m' -> wmono rsegs m m' -> disjoint_from W a ERRST_SIZE -> ERRST LB m' a E.
Proof.
  intros LB W m m' a E H MU WM DJ. eapply ERRST_agree with (R := fun x => a <= x < a + ERRST_SIZE); [| exact H| intros x Hx; exact Hx].
  eapply magree_of_munch; [exact MU| exact WM|]. intros x Hx Hr. eapply disjoint_outside; [exact DJ| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma EXLOCK_munch : forall LIB W m m' b,
  EXLOCK LIB m b -> munch W m m' -> wmono rsegs m m' -> disjoint_from W (blk_addr b) 12 -> EXLOCK LIB m' b.
Proof.
  intros LIB W m m' b (I1 & Z1 & R1 & C1) MU WM DJ. split; [exact I1|]. split; [exact Z1|]. split; [exact R1|].
  unfold MUTEX in *. eapply rw_cells_transport; [exact C1| exact MU| exact WM| exact DJ].
Qed.

End HCW.

(* [comment removed for export] *)
Ltac libx_windows :=
  repeat (apply Forall_cons; [unfold off_libx, IMG_LO, IMG_HI, RERRNO; cbn [fst snd]; lia|]); apply Forall_nil.
Ltac chain_windows :=
  repeat (apply Forall_cons; [unfold chain_free, IMG_LO, IMG_HI, ERRST_SIZE; cbn [fst snd];
                              first [lia | right; right; split; [assumption| lia]]|]); apply Forall_nil.
