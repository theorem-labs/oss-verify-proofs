(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface CJ_tree ICPT_iface ICPT_musl Drv_icpt_defs Drv_base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition DICPT (m : word -> option byte) : Prop :=
  ro_cells bsegs m 0xa3440 [C8 (Z_to_bv 64 0xa00d4)]       (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xa3448 [C8 (Z_to_bv 64 0x93b5c)]    (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xa3530 [C8 (Z_to_bv 64 0x9b25c)].   (* [comment removed for export] *)

Definition dicpt_addr (a : Z) : Prop :=
  (0xa3440 <= a < 0xa3448) \/ (0xa3448 <= a < 0xa3450) \/ (0xa3530 <= a < 0xa3538).

Lemma DICPT_fwrite : forall m, DICPT m -> fwrite_icpt_cells m.
Proof. intros m (_ & H & _). exact H. Qed.

(* [comment removed for export] *)
Lemma DICPT_icpt_cells2 : forall m, DICPT m -> ro_cells bsegs m 0xa3438 [C8 (Z_to_bv 64 0x8fe44)] -> icpt_cells2 m.
Proof. intros m (_ & _ & H) HF. split; [exact HF| exact H]. Qed.

Lemma ro_cells_magree : forall P m m' A cs,
  magree P m m' -> ro_cells bsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  ro_cells bsegs m' A cs.
Proof.
  intros P m m' A cs HP [Hwf HB] HR. split; [exact Hwf|].
  eapply bytes_at_magree; eauto. rewrite cells_bytes_length by assumption. exact HR.
Qed.

Lemma DICPT_magree : forall m m', DICPT m -> magree dicpt_addr m m' -> DICPT m'.
Proof.
  intros m m' (D1 & D2 & D3) AG. unfold DICPT.
  split; [| split]; (eapply ro_cells_magree; [exact AG| eassumption| unfold dicpt_addr; cbn; intros; lia]).
Qed.

Lemma DICPT_munch : forall W m m', DICPT m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => snd iv <= 0xa3440 \/ 0xa3538 <= fst iv) W -> DICPT m'.
Proof.
  intros W m m' D MU WM FW. eapply DICPT_magree; [exact D|].
  eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha Hd.
  apply (outside_of_Forall (fun iv => snd iv <= 0xa3440 \/ 0xa3538 <= fst iv)); [exact FW|].
  cbn [fst snd]. intros lo hi H. unfold dicpt_addr in Hd. lia.
Qed.

Lemma dicpt_client : forall sp0 LB LF SP a, dicpt_addr a -> cj_client_addr sp0 LB LF SP a.
Proof.
  intros sp0 LB LF SP a Hd. right; left. apply aclient_image_of; unfold dicpt_addr, ADATA_LO, AIMG_HI in *; lia.
Qed.

Lemma DICPT_cj_pres : forall sp0 LB LF SP m m', DICPT m -> cj_pres sp0 LB LF SP m m' -> DICPT m'.
Proof.
  intros sp0 LB LF SP m m' D PR. eapply DICPT_magree; [exact D|].
  eapply magree_of_cj_pres; [exact PR|]. intros a _ Hd. apply dicpt_client. exact Hd.
Qed.


End CeilWrap.
