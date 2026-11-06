(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require FinFun.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstate.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_fs_lib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Vectors.FinFun.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_artR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mts_cells (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa1f80 [C8 (Z_to_bv 64 0xaa278)] /\ ro_cells asegs m 0xaa278 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ ro_cells asegs m 0xa1f88 [C8 (Z_to_bv 64 0xaaf68)] /\ ro_cells asegs m 0xaaf68 [C8 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0xa1f90 [C8 (Z_to_bv 64 0xaaf70)] /\ ro_cells asegs m 0xaaf70 [C8 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0xa1f98 [C8 (Z_to_bv 64 0xaaf60)] /\ ro_cells asegs m 0xaaf60 [C8 (Z_to_bv 64 0x7fffffffffff)].

Lemma mts_cells_of : forall st m, RTREP st m -> mts_cells m.
Proof.
  intros st m HR. pose proof (rr_link st m HR) as HL. pose proof (rr_consts st m HR) as HC.
  destruct HC as (K1 & _ & _ & _ & _ & K6 & K7 & K8 & _).
  unfold mts_cells. repeat match goal with |- _ /\ _ => split end.
  - apply (R_link_at m 0xa1f80 0xaa278 HL); vm_compute; reflexivity.
  - exact K1.
  - apply (R_link_at m 0xa1f88 0xaaf68 HL); vm_compute; reflexivity.
  - exact K7.
  - apply (R_link_at m 0xa1f90 0xaaf70 HL); vm_compute; reflexivity.
  - exact K8.
  - apply (R_link_at m 0xa1f98 0xaaf60 HL); vm_compute; reflexivity.
  - exact K6.
Qed.

Lemma mts_cells_munch : forall W m m', mts_cells m -> munch W m m' ->
  (forall a sz, a + sz <= 0x1e4000 -> disjoint_from W a sz) -> mts_cells m'.
Proof.
  intros W m m' H MU D. unfold mts_cells in *.
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with |- ro_cells _ _ ?a ?cs =>
    match type of H with context [ro_cells asegs m a cs] =>
      let rec pick H := lazymatch type of H with
        | ro_cells asegs m a cs /\ _ => exact (proj1 H)
        | ro_cells asegs m a cs => exact H
        | _ /\ _ => pick (proj2 H) end in
      eapply (ro_cells_transport asegs W m m'); [ pick H | exact MU | apply D; cbn; lia ] end end.
Qed.

(* [comment removed for export] *)
Definition tls_cells (st : rtstate) (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa3d40 [C8 (Z_to_bv 64 0x9be44)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa2c60 [C8 (Z_to_bv 64 1)]                               (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa2c68 [C8 (Z_to_bv 64 0xfffffffffffff800)]              (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5dd248 [C8 (Z_to_bv 64 0x5dd270)]                        (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5dd278 [C8 (Z_to_bv 64 0x5dda50)]                        (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)]                        (* [comment removed for export] *)
  /\ ro_cells asegs m 0x13be31 [C1 (Z_to_bv 8 1)]                                (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1fd0 [C8 (Z_to_bv 64 0x139d18)]                        (* [comment removed for export] *)
  /\ ro_cells asegs m 0x139d18 [C4 (Z_to_bv 64 0)]                               (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa2c70 [C8 (Z_to_bv 64 0x8)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5dd258 [C8 (Z_to_bv 64 (tl_dtls_block (st_tls st)))]     (* [comment removed for export] *)
  /\ ro_cells asegs m (tl_dtls_block (st_tls st) + 24) [C8 (Z_to_bv 64 (tl_dtls_w (st_tls st)))].  (* [comment removed for export] *)

Lemma cf137_cell : forall st m, RTREP st m -> ro_cells asegs m 0x13be31 [C1 (Z_to_bv 8 1)].
Proof.
  intros st m HR. pose proof (rr_consts st m HR) as HC. destruct HC as (_ & _ & _ & CF & _).
  change 0x13be31 with (A_CFLAGS + Z.of_nat 137). pose proof (cflags_byte m 137 CF ltac:(lia)) as HB. exact HB.
Qed.

Lemma tls_cells_of : forall st m, RTREP st m -> tls_cells st m.
Proof.
  intros st m HR. pose proof (rr_link st m HR) as HL. pose proof (rr_consts st m HR) as HC. pose proof (rr_thread st m HR) as HT.
  destruct HT as (_ & _ & _ & _ & _ & _ & _ & _ & T9 & T10 & T11 & T12 & T13).
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K17 & _).
  unfold tls_cells. repeat match goal with |- _ /\ _ => split end.
  - apply (R_link_at m 0xa3d40 0x9be44 HL); vm_compute; reflexivity.
  - apply (R_link_at m 0xa2c60 1 HL); vm_compute; reflexivity.
  - apply (R_link_at m 0xa2c68 0xfffffffffffff800 HL); vm_compute; reflexivity.
  - exact T9.
  - exact T10.
  - apply (R_link_at m 0xa1f70 0x13bda8 HL); vm_compute; reflexivity.
  - eapply cf137_cell; exact HR.
  - apply (R_link_at m 0xa1fd0 0x139d18 HL); vm_compute; reflexivity.
  - exact K17.
  - apply (R_link_at m 0xa2c70 0x8 HL); vm_compute; reflexivity.
  - exact T12.
  - replace (tl_dtls_block (st_tls st) + 24) with (tl_dtls_block (st_tls st) + 16 * A_TLSMOD + 8) by (unfold A_TLSMOD; lia). exact T13.
Qed.

(* [comment removed for export] *)
Lemma fstls_cell : forall st m, RTREP st m -> ro_cells asegs m 0x5dd250 [C8 (Z_to_bv 64 (st_fs st))].
Proof. intros st m HR. destruct (rr_thread st m HR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T11 & _). exact T11. Qed.

Lemma tpage_cells : forall st m, RTREP st m -> exists j1 j2 j3 j4 j5,
  rw_cells asegs m (st_t st) [C8 (Z_to_bv 64 (st_ctx st)); C8 (Z_to_bv 64 (ASTACK_TOP (st_sp0 st))); C8 (Z_to_bv 64 (ASTACK_BOTTOM (st_sp0 st)));
                              CB 16 j1; C1 (Z_to_bv 8 0); CB 7 j2; C8 j3; C8 j4; C8 j5; C8 (Z_to_bv 64 (st_fs st))].
Proof. intros st m HR. destruct (rr_thread st m HR) as (_ & (j1 & j2 & j3 & j4 & j5 & H) & _). exists j1, j2, j3, j4, j5. exact H. Qed.

(* [comment removed for export] *)
Lemma fsobj_cells : forall st m k, RTREP st m -> 0 <= k < 11 ->
  rw_cells asegs m (st_fs st + 8 * k) [C8 (Z_to_bv 64 (fhint st k))]
  /\ rw_cells asegs m (st_fs st + 88) [C8 (Z_to_bv 64 FS_LOG)]
  /\ rw_cells asegs m (st_fs st + 96) [C1 (Z_to_bv 8 0)]
  /\ (forall pos, 0 <= pos < fcap k -> rw_cells asegs m (fflag_addr (st_fs st) k pos) [C1 (Z_to_bv 8 (flag_val st k pos))])
  /\ stk asegs m (st_fs st) (st_fs st + FS_TOTAL)
  /\ stk asegs m (SH (st_fs st + FS_FRAMES_OFF)) (SH (st_fs st + FS_TOTAL)).
Proof.
  intros st m k HR Hk. destruct (rr_fs st m HR) as (V1 & V2 & HINTS & LOG & GC & FLG & _).
  split; [exact (HINTS k Hk)|]. split; [exact LOG|]. split; [exact GC|]. split; [intros pos Hp; exact (FLG k pos Hk Hp)|]. split; [exact V1| exact V2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dtls_range : forall st, RTWF st ->
  oclr (tl_dtls_block (st_tls st) + 24) (tl_dtls_block (st_tls st) + 32) /\ tl_dtls_block (st_tls st) + 32 <= alloc_ceiling /\ 0 < tl_dtls_w (st_tls st) < 2^64.
Proof.
  intros st WF. destruct (wb_dtls_loose st (wf_base_ok st WF)) as (b & k & HIn & H1 & H2).
  pose proof (loose0_range st WF b k HIn) as (O & L1 & L2 & L3). pose proof (wb_dtls_w st (wf_base_ok st WF)).
  split; [apply (oclr_sub _ _ _ _ O); lia| split; [lia| assumption]].
Qed.

Lemma fs_range' : forall st, RTWF st -> ablk (st_fs st) (st_fs st + FS_TOTAL) /\ st_fs st + FS_TOTAL <= alloc_ceiling /\ st_fs st mod 4096 = 0.
Proof. intros st WF. exact (RT_fp.fs_range st WF). Qed.

(* [comment removed for export] *)
Lemma fs_geom1 : fsz 1 = 128 /\ fcap 1 = 8192 /\ fflags_off 1 = 0x5000.
Proof. repeat split; reflexivity. Qed.
Lemma fs_geom2 : fsz 2 = 256 /\ fcap 2 = 4096 /\ fflags_off 2 = 0x7000.
Proof. repeat split; reflexivity. Qed.
Lemma fsz_k : forall k, (k = 1 \/ k = 2) -> fsz k = 128 * k /\ fcap k = 8192 / k /\ fflags_off k = 0x3000 + 0x2000 * k /\ fsz k / 8 = 16 * k.
Proof. intros k [-> | ->]; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lf_count_filter : forall k LF, lf_count k LF = zlen (List.filter (fun fk : fframe => snd fk =? k) LF).
Proof.
  intros k LF. induction LF as [|[F j] LF IH]; [reflexivity|]. cbn [lf_count List.filter snd]. rewrite IH.
  destruct (j =? k); unfold zlen; cbn [length]; lia.
Qed.

Lemma flag_live_In : forall st k pos, flag_live st k pos = true <->
  In (fframe_addr (st_fs st) k pos) (map fst (List.filter (fun fk : fframe => snd fk =? k) (st_lf st))).
Proof.
  intros st k pos. unfold flag_live. rewrite existsb_exists. split.
  - intros ((F & j) & HIn & HB). cbn [fst snd] in HB. apply andb_prop in HB as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
    apply in_map_iff. exists (fframe_addr (st_fs st) k pos, k). split; [reflexivity|]. apply List.filter_In. split; [exact HIn| cbn; apply Z.eqb_refl].
  - intros H. apply in_map_iff in H as ((F & j) & HF & HIn). apply List.filter_In in HIn as [HIn HB]. cbn [fst snd] in HF, HB. subst F.
    exists (fframe_addr (st_fs st) k pos, j). split; [exact HIn|]. cbn [fst snd]. rewrite HB, Z.eqb_refl. reflexivity.
Qed.

Lemma fframe_addr_inj_pos : forall fs k p p', (k = 1 \/ k = 2) -> fframe_addr fs k p = fframe_addr fs k p' -> p = p'.
Proof. intros fs k p p' [-> | ->] E; unfold fframe_addr in E; [change (fsz 1) with 128 in E| change (fsz 2) with 256 in E]; lia. Qed.

Lemma free_slot_exists : forall st k, (k = 1 \/ k = 2) -> lf_count k (st_lf st) < fcap k ->
  exists pos, 0 <= pos < fcap k /\ flag_live st k pos = false.
Proof.
  intros st k Hk HC.
  set (n := Z.to_nat (fcap k)).
  destruct (existsb (fun i => negb (flag_live st k (Z.of_nat i))) (seq 0 n)) eqn:E.
  - apply existsb_exists in E as (i & Hi & HB). apply in_seq in Hi. exists (Z.of_nat i). split; [lia|]. destruct (flag_live st k (Z.of_nat i)); [discriminate| reflexivity].
  - exfalso. pose proof (proj1 (existsb_false_iff _ _) E) as E'. cbv beta in E'.
    set (l := map (fun i => fframe_addr (st_fs st) k (Z.of_nat i)) (seq 0 n)).
    set (Lk := map fst (List.filter (fun fk : fframe => snd fk =? k) (st_lf st))).
    assert (ND : List.NoDup l).
    { unfold l. apply Finite.Injective_map_NoDup_in; [| apply seq_NoDup]. intros a b Ha Hb Eab. apply (fframe_addr_inj_pos _ _ _ _ Hk) in Eab. lia. }
    assert (INCL : incl l Lk).
    { intros x Hx. unfold l in Hx. apply in_map_iff in Hx as (i & <- & Hi). apply flag_live_In.
      pose proof (E' i Hi) as B. destruct (flag_live st k (Z.of_nat i)); [reflexivity| discriminate]. }
    pose proof (List.NoDup_incl_length ND INCL) as L. unfold l, Lk in L. rewrite length_map, length_seq in L.
    rewrite lf_count_filter in HC. unfold zlen in HC. rewrite length_map in L.
    assert (POS : 0 < fcap k) by (destruct Hk as [-> | ->]; cbn; lia). unfold n in L. unfold fframe in *. lia.
Qed.


End CeilWrap.
End RTW_fs_lib.

(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
Module RTW_leaves_thread.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Theorem get_current_thread_proof : get_current_thread_spec.
Proof.
  unfold get_current_thread_spec. intros until lo. intros HR WF MI TP ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (leaf_cells _ _ HR) as (_ & _ & _ & K4 & K5 & _ & _ & _ & _ & K10 & K11 & K12).
  pose proof (ctx_range st WF) as CR. pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in CR, TR. olin CR. olin TR.
  unfold A_GET_CURRENT_THREAD. subst tp. leaf_prep.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *) clear K4 K5.
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *) clear K10.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
Qed.

Theorem get_thread_stats_proof : get_thread_stats_spec.
Proof.
  unfold get_thread_stats_spec. intros until lo. intros HR WF MI TP ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin TR.
  unfold A_GET_THREAD_STATS. subst tp. leaf_prep.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. (* [comment removed for export] *)
  rtrep_high HR WF MU WM.
  call get_current_thread_proof; [exact HR | exact WF | exact MI | reflexivity | rewrite unsigned_lit by lia; exact ST | idtac; lia | rewrite unsigned_lit by lia; lia | ].
  assert (E16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  rewrite E16 in *. clear E16. subst x2. cbv beta delta [wz]. rename PC into ST.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. showpc. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. unfold T_STATS. apply f_equal. lia.
Qed.

Theorem run_malloc_hooks_proof : run_malloc_hooks_spec.
Proof.
  unfold run_malloc_hooks_spec. intros until lo. intros HR MI ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (leaf_cells _ _ HR) as (_ & _ & _ & _ & _ & _ & K7 & _).
  unfold A_RUN_MALLOC_HOOKS. leaf_prep.
  carve_frame 32%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *) showpc.
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. exact I.
Qed.

Theorem run_free_hooks_proof : run_free_hooks_spec.
Proof.
  unfold run_free_hooks_spec. intros until lo. intros HR MI ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (leaf_cells _ _ HR) as (_ & _ & _ & _ & _ & _ & K7 & _).
  unfold A_RUN_FREE_HOOKS. leaf_prep.
  carve_frame 32%nat ST.
  do 4 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *) showpc.
  lstep. lstep. lstep. (* [comment removed for export] *) showpc.
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
Qed.

Theorem set_errno_enomem_proof : set_errno_enomem_spec.
Proof.
  unfold set_errno_enomem_spec. intros until lo. intros MI TP ERR ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AERRNO, AERRNO + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold A_SET_ERRNO_ENOMEM. unfold AERRNO in *. subst tp. leaf_prep.
  change (6148688 - 164) with 6148524 in *.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.


End CeilWrap.
End RTW_leaves_thread.

(* [comment removed for export] *)
Module RTW_leaves_tiny.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac tiny_intro :=
  intros until lo; intros HR MI TP ST CEIL LO;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU; pose proof (wmono_refl asegs m) as WM end;
  pose proof (leaf_cells _ _ HR) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
(* [comment removed for export] *)
Ltac keep_only l :=
  repeat match goal with H : ro_cells _ _ ?a _ |- _ => lazymatch l with context [a] => fail | _ => clear H end end;
  repeat match goal with H : rw_cells _ _ (st_ctx _ + _) _ |- _ => clear H end.

Theorem get_current_pc_proof : get_current_pc_spec.
Proof.
  unfold get_current_pc_spec, tiny_spec. tiny_intro. unfold A_GET_CURRENT_PC. keep_only (@nil Z). leaf_prep.
  lstep. lstep.
  finish. reflexivity.
Qed.

Theorem get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Proof.
  unfold get_malloc_ctx_size_spec, tiny_spec. tiny_intro. unfold A_GET_MALLOC_CTX_SIZE. keep_only [0xaaf7c]. leaf_prep.
  lstep. lstep. fl. lstep. lstep.
  finish. unfold TRACE_MAX_LEN. reflexivity.
Qed.

Theorem asan_inited_proof : asan_inited_spec.
Proof.
  unfold asan_inited_spec, tiny_spec. tiny_intro. unfold A_ASAN_INITED_FN. keep_only [0xaaf58]. leaf_prep.
  lstep. lstep. fl. lstep. lstep. fl. lstep. fl. showpc. lstep.
  finish. reflexivity.
Qed.

Theorem try_asan_init_proof : try_asan_init_spec.
Proof.
  unfold try_asan_init_spec, tiny_spec. tiny_intro. unfold A_TRY_ASAN_INIT. keep_only [0xaaf58]. leaf_prep.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep.
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
Qed.

Theorem can_poison_proof : can_poison_spec.
Proof.
  unfold can_poison_spec, tiny_spec. tiny_intro. unfold A_CAN_POISON_FN. keep_only [0xa9adc]. leaf_prep.
  lstep. lstep. fl. lstep. lstep. fl. lstep.
  finish. reflexivity.
Qed.

Theorem may_return_null_proof : may_return_null_spec.
Proof.
  unfold may_return_null_spec, tiny_spec. tiny_intro. unfold A_MAY_RETURN_NULL_FN. keep_only [0x12c4e1]. leaf_prep.
  lstep. lstep. fl. lstep. fl. lstep.
  finish. reflexivity.
Qed.

Theorem rss_exceeded_proof : rss_exceeded_spec.
Proof.
  unfold rss_exceeded_spec, tiny_spec. tiny_intro. unfold A_RSS_EXCEEDED_FN. keep_only [0x12c4e1]. leaf_prep.
  lstep. lstep. fl. lstep. fl. lstep.
  finish. reflexivity.
Qed.

Theorem lsan_disabled_proof : lsan_disabled_spec.
Proof.
  unfold lsan_disabled_spec, tiny_spec. tiny_intro. specialize (TP eq_refl). subst tp. unfold A_LSAN_DISABLED_FN. keep_only [0xa2bd8; 0x5dd260]. leaf_prep.
  lstep. lstep. fl. clear K9. lstep. fl. lstep. fl. lstep. fl. showpc. lstep.
  finish. reflexivity.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac tiny_intro :=
  intros until lo; intros HR MI TP ST CEIL LO;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU; pose proof (wmono_refl asegs m) as WM end;
  pose proof (leaf_cells _ _ HR) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
Ltac keep_only l :=
  repeat match goal with H : ro_cells _ _ ?a _ |- _ => lazymatch l with context [a] => fail | _ => clear H end end;
  repeat match goal with H : rw_cells _ _ (st_ctx _ + _) _ |- _ => clear H end.
End RTW_leaves_tiny.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_fs_walk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib RTW_leaves_tiny RTW_leaves_thread RTW_fs_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Definition A_TLS_ICPT : Z := 0x483f0.

Lemma tls_icpt_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> RTWF st -> mem_inv asegs m -> tp = wz ATP -> a0 = wz A_FAKESTACK_TLSDESC ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 176 <= bv_unsigned sp ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 176, bv_unsigned sp)] lo m
               (fun a0' _ _ => a0' = wz ATP))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_TLS_ICPT) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HR WF MI TP A0 ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (nelimp (tls_cells_of st m HR) 12%nat; intros K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12).
  hide K1. hide K2. hide K3. hide K4. hide K5. hide K6. hide K7. hide K8. hide K9. hide K10. hide K11. hide K12.
  (nelim (tpage_cells st m HR) 6%nat; intros j1 j2 j3 j4 j5 TPG).
  pose proof (t_range st WF) as TR. pose proof (dtls_range st WF) as DR. unfold KHIGHMEM_BEG, AIMG_HI in TR, DR. olin TR. olin DR.
  unfold A_TLS_ICPT, A_FAKESTACK_TLSDESC in *. subst tp a0. leaf_prep.
  carve_frame 32%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  pose proof HR as HR1. rtrep_high HR1 WF MU WM.
  call try_asan_init_proof; [exact HR1| exact MI| discriminate| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
  after_call. clear HR1.
  assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  rewrite E32 in *.
  recell K1 MU. lstep. lstep. fl. (* [comment removed for export] *) clear K1.
  lstep. lstep. lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof K2 as K2'. recell K2' MU. recell K3 MU.
  lstep. lstep. fl. (* [comment removed for export] *)
  recell K4 MU. lstep. fl. clear K4. (* [comment removed for export] *)
  lstep. fl. clear K2' K3. (* [comment removed for export] *)
  lstep. lstep. fl. (* [comment removed for export] *)
  recell K5 MU. lstep. fl. clear K5. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR as HR1. rtrep_high HR1 WF MU WM.
  call get_current_thread_proof; [exact HR1| exact WF| exact MI| reflexivity| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
  after_call. clear HR1. rewrite E32 in *.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 144%nat ST.
  do 14 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  recell K6 MU. lstep. lstep. fl. clear K6. (* [comment removed for export] *)
  recell K7 MU. lstep. fl. clear K7. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  recell K8 MU. lstep. lstep. fl. clear K8. (* [comment removed for export] *)
  recell K2 MU. lstep. fl. clear K2. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  recell K9 MU. lstep. fl. clear K9. (* [comment removed for export] *)
  recell K10 MU. lstep. fl. clear K10. (* [comment removed for export] *)
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  recell K11 MU. lstep. clear K11. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  recell K12 MU. lstep. clear K12. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 13 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -32).
  (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 4 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
Qed.

Definition A_MEM_TO_SHADOW : Z := 0x3d7b0.

Lemma memtoshadow_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z),
  mts_cells m -> mem_inv asegs m -> a0 = wz p -> (0 <= p <= 0x7fff7fff \/ KHIGHMEM_BEG <= p <= KHIGHMEM_END) ->   (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp) ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [] lo m
               (fun a0' _ _ => a0' = wz (SH p)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_MEM_TO_SHADOW) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HC MI A0 HP ST.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (nelim HC 8%nat; intros K1 K2 K3 K4 K5 K6 K7 K8).
  hide K1. hide K2. hide K3. hide K4. hide K5. hide K6. hide K7. hide K8.
  unfold A_MEM_TO_SHADOW, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END in *. subst a0. leaf_prep.
  recell K1 MU. lstep. lstep. fl. clear K1. (* [comment removed for export] *)
  recell K2 MU. lstep. clear K2. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
  destruct HP as [HP|HP].
  { (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    finish. unfold SH, SHADOW_OFFSET. f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
  lstep. if_lia. (* [comment removed for export] *)
  recell K3 MU. recell K5 MU. lstep. lstep. lstep. lstep. fl. clear K3 K5. (* [comment removed for export] *)
  recell K4 MU. lstep. clear K4. (* [comment removed for export] *)
  recell K6 MU. lstep. clear K6. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  recell K7 MU. lstep. lstep. fl. clear K7. (* [comment removed for export] *)
  recell K8 MU. lstep. clear K8. (* [comment removed for export] *)
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  finish. unfold SH, SHADOW_OFFSET. f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia.
Qed.


(* [comment removed for export] *)
Lemma probe_loop : forall (cn : nat) (c LP FP n MK FL : Z) (fv : Z -> bool) (u : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Q : machine_state -> Prop),
  Z.to_nat c = cn ->
  ((LP = 0x3d518 /\ FP = 0x3d590 /\ n = 8192 /\ MK = 8191) \/ (LP = 0x3d6a8 /\ FP = 0x3d720 /\ n = 4096 /\ MK = 4095)) ->
  0x5ff000 <= FL -> FL + n <= alloc_ceiling ->
  (forall pos, 0 <= pos < n -> rw_cells asegs m (FL + pos) [C1 (Z_to_bv 8 (if fv pos then 1 else 0))]) ->
  0 <= u < 2^64 -> 0 < c <= n ->
  (exists j, 0 <= j < c /\ fv ((u + j) mod n) = false) ->
  (forall (u' c' : Z), 0 <= u' < 2^64 -> 0 < c' <= c -> fv (u' mod n) = false ->
     evt asegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 0) t1 t2 s0 s1 (Z_to_bv 64 c') a1 (Z_to_bv 64 u') (Z_to_bv 64 FL) (Z_to_bv 64 MK)
                          (Z_to_bv 64 (FL + u' mod n)) a6 (Z_to_bv 64 (u' mod n)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 FP) fc None m (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 (Z_to_bv 64 u) (Z_to_bv 64 FL) (Z_to_bv 64 MK) a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 LP) fc None m (seg_rom asegs)).
Proof.
  induction cn as [|cn IH]; intros until Q; intros Hcn HK HFL1 HFL2 FLG HU Hc HEX K; [lia|].
  destruct HK as [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
  - assert (HP : 0 <= u mod 8192 < 8192) by (apply Z.mod_pos_bound; lia).
    destruct (ex_intro (fun q => q = FL + u mod 8192) _ eq_refl) as [q Hq].
    pose proof (FLG (u mod 8192) HP) as CELL. rewrite <- Hq in CELL.
    zstep. (* [comment removed for export] *)
    setreg 17 (Z_to_bv 64 (u mod 8192)) ltac:(f_equal; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; reflexivity).
    zstep. (* [comment removed for export] *)
    setreg 15 (Z_to_bv 64 q) ltac:(f_equal; lia).
    destruct (fv (u mod 8192)) eqn:FV.
    + (nelim HEX 3%nat; intros j Hj HFj).
      assert (Hj0 : j <> 0) by (intros ->; rewrite Z.add_0_r in HFj; congruence).
      zstep. fl. (* [comment removed for export] *)
      zstep. if_lia. (* [comment removed for export] *)
      zstep. zstep. (* [comment removed for export] *)
      setreg 10 (Z_to_bv 64 (c - 1)) ltac:(f_equal; rewrite swrap32_small; lia).
      zstep. if_lia. (* [comment removed for export] *)
      replace (Z_to_bv 64 (u + 1)) with (Z_to_bv 64 ((u + 1) mod 2^64)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); apply Z.mod_mod; lia).
      eapply IH; [lia| left; repeat split| exact HFL1| exact HFL2| exact FLG| apply Z.mod_pos_bound; lia| lia| |].
      * exists (j - 1). split; [lia|].
        assert (E : ((u + 1) mod 2^64 + (j - 1)) mod 8192 = (u + j) mod 8192).
        { pose proof (Z.div_mod (u + 1) (2^64) ltac:(lia)) as D. pose proof (Z.mod_pos_bound (u + 1) (2^64) ltac:(lia)) as B.
          set (qq := (u + 1) / 2^64) in D. set (r := (u + 1) mod 2^64) in *.
          replace (r + (j - 1)) with ((u + j) + (- (qq * 2251799813685248)) * 8192) by lia. apply Z_mod_plus_full. }
        rewrite E. exact HFj.
      * intros u' c' Hu' Hc' HF'. eapply K; [exact Hu'| lia| exact HF'].
    + zstep. fl. (* [comment removed for export] *)
      zstep. if_lia. (* [comment removed for export] *)
      replace q with (FL + u mod 8192) by (symmetry; exact Hq).
      eapply K; [exact HU| lia| exact FV].
  - assert (HP : 0 <= u mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
    destruct (ex_intro (fun q => q = FL + u mod 4096) _ eq_refl) as [q Hq].
    pose proof (FLG (u mod 4096) HP) as CELL. rewrite <- Hq in CELL.
    zstep. (* [comment removed for export] *)
    setreg 17 (Z_to_bv 64 (u mod 4096)) ltac:(f_equal; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; reflexivity).
    zstep. (* [comment removed for export] *)
    setreg 15 (Z_to_bv 64 q) ltac:(f_equal; lia).
    destruct (fv (u mod 4096)) eqn:FV.
    + (nelim HEX 3%nat; intros j Hj HFj).
      assert (Hj0 : j <> 0) by (intros ->; rewrite Z.add_0_r in HFj; congruence).
      zstep. fl. (* [comment removed for export] *)
      zstep. if_lia. (* [comment removed for export] *)
      zstep. zstep. (* [comment removed for export] *)
      setreg 10 (Z_to_bv 64 (c - 1)) ltac:(f_equal; rewrite swrap32_small; lia).
      zstep. if_lia. (* [comment removed for export] *)
      replace (Z_to_bv 64 (u + 1)) with (Z_to_bv 64 ((u + 1) mod 2^64)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); apply Z.mod_mod; lia).
      eapply IH; [lia| right; repeat split| exact HFL1| exact HFL2| exact FLG| apply Z.mod_pos_bound; lia| lia| |].
      * exists (j - 1). split; [lia|].
        assert (E : ((u + 1) mod 2^64 + (j - 1)) mod 4096 = (u + j) mod 4096).
        { pose proof (Z.div_mod (u + 1) (2^64) ltac:(lia)) as D. pose proof (Z.mod_pos_bound (u + 1) (2^64) ltac:(lia)) as B.
          set (qq := (u + 1) / 2^64) in D. set (r := (u + 1) mod 2^64) in *.
          replace (r + (j - 1)) with ((u + j) + (- (qq * 4503599627370496)) * 4096) by lia. apply Z_mod_plus_full. }
        rewrite E. exact HFj.
      * intros u' c' Hu' Hc' HF'. eapply K; [exact Hu'| lia| exact HF'].
    + zstep. fl. (* [comment removed for export] *)
      zstep. if_lia. (* [comment removed for export] *)
      replace q with (FL + u mod 4096) by (symmetry; exact Hq).
      eapply K; [exact HU| lia| exact FV].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
End RTW_fs_walk.

(* [comment removed for export] *)
Module RTW_fs_smk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib RTW_leaves_tiny RTW_leaves_thread RTW_fs_lib RTW_fs_walk OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
(* [comment removed for export] *)
Ltac if_lit := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota end.

(* [comment removed for export] *)
Lemma rw_cells_recells : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  cells_size cs' = cells_size cs -> rw_cells asegs m A cs'.
Proof. intros m A cs cs' [[W B] WR] W' EB ES. split; [split; [exact W'| rewrite EB; exact B]| rewrite ES; exact WR]. Qed.

(* [comment removed for export] *)
Definition smk_W (k lo SP fs pos : Z) : list (Z * Z) :=
  let Fr := fframe_addr fs k pos in let fl := fflag_addr fs k pos in
  [(lo, SP); (fs + 8 * k, fs + 8 * k + 8); (fl, fl + 1); (Fr + 24, Fr + 32); (Fr + fsz k - 8, Fr + fsz k); (SH Fr, SH Fr + fsz k / 8)].

Definition smk_post (k : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (pos u : Z) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (fframe_addr (st_fs st) k pos)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ 0 <= pos < fcap k /\ flag_live st k pos = false /\ 0 <= u
    /\ munch (smk_W k lo (bv_unsigned sp) (st_fs st) pos) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (st_fs st + 8 * k) [C8 (wz u)]
    /\ rw_cells asegs m' (fflag_addr (st_fs st) k pos) [C1 (zb 1)]
    /\ rw_cells asegs m' (fframe_addr (st_fs st) k pos) [CB (Z.to_nat (fsz k - 8)) junk]
    /\ rw_cells asegs m' (fframe_addr (st_fs st) k pos + fsz k - 8) [C8 (wz (fflag_addr (st_fs st) k pos))]
    /\ rw_cells asegs m' (SH (fframe_addr (st_fs st) k pos)) (shcells (repeat 0 (Z.to_nat (fsz k / 8)))).

Lemma stkmalloc1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> RTWF st -> mem_inv asegs m -> tp = wz ATP ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 208 <= bv_unsigned sp ->
  (exists pos, 0 <= pos < fcap 1 /\ flag_live st 1 pos = false) ->
  evt asegs (smk_post 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ASTKMALLOC1) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HR WF MI TP ST CEIL LO FREE.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (fstls_cell st m HR) as K0. hide K0.
  pose proof (mts_cells_of st m HR) as MTS. change (mts_cells m) with (id (mts_cells m)) in MTS.
  (nelimp (fsobj_cells st m 1 HR ltac:(lia)) 6%nat; intros HINT LOG GC FLG VIS1 VIS2).
  pose proof (fs_range' st WF) as FSR. unfold KHIGHMEM_BEG, AIMG_HI, FS_TOTAL in FSR. olin FSR.
  remember (st_fs st) as fs eqn:Hfs.
  unfold FS_TOTAL, FS_FRAMES_OFF, SH, SHADOW_OFFSET in VIS1, VIS2. unfold FS_LOG in LOG. replace (fs + 8 * 1) with (fs + 8) in HINT by lia.
  unfold ASTKMALLOC1 in *. subst tp. leaf_prep.
  carve_frame 32%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  pose proof HR as HR1. rtrep_high HR1 WF MU WM.
  call tls_icpt_walk; [exact HR1| exact WF| exact MI| reflexivity| reflexivity| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
  after_call. clear HR1. unfold ATP.
  assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  rewrite E32 in *.
  recell K0 MU. lstep. clear K0. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 4 lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  do 5 lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 4 lstep. fl. (* [comment removed for export] *)
  do 4 lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  set (h := fhint st 1) in *. set (u := h mod 2^64).
  assert (HU : 0 <= u < 2^64) by (apply Z.mod_pos_bound; lia).
  setreg 12 (Z_to_bv 64 u) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); unfold u; rewrite Z.mod_mod by lia; reflexivity).
  (nelim FREE 3%nat; intros pos0 Hpos0 HF0). change (fcap 1) with 8192 in Hpos0.
  eapply (probe_loop (Z.to_nat 8192) 8192 0x3d518 0x3d590 8192 8191 (fs + 20480) (flag_live st 1) u);
    [reflexivity| left; repeat split| lia| lia| | exact HU| lia| |].
  { intros pos Hp. lazymatch goal with |- rw_cells _ ?mc _ _ =>
      eapply (rw_cells_transport asegs _ m mc); [| exact MU| exact WM| cbn; lia] end.
    pose proof (FLG pos ltac:(change (fcap 1) with 8192; lia)) as C. unfold fflag_addr, flag_val in C. change (fflags_off 1) with 20480 in C. exact C. }
  { exists ((pos0 - u) mod 8192). split; [apply Z.mod_pos_bound; lia|].
    replace ((u + (pos0 - u) mod 8192) mod 8192) with pos0; [exact HF0|].
    rewrite Zplus_mod_idemp_r. replace (u + (pos0 - u)) with pos0 by lia. symmetry. apply Z.mod_small. lia. }
  intros u' c' Hu' Hc' HF'.
  assert (HP : 0 <= u' mod 8192 < 8192) by (apply Z.mod_pos_bound; lia).
  set (pos := u' mod 8192) in *.
  (* [comment removed for export] *)
  do 4 lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (ex_intro (fun q => q = fs + 20480 + pos) _ eq_refl) as [fl Hfl].
  destruct (ex_intro (fun q => q = fs + 1085440 + 128 * pos) _ eq_refl) as [Fr HFr].
  destruct (ex_intro (fun q => q = 2147450880 + Fr / 8) _ eq_refl) as [shF HshF].
  assert (FrA : Fr mod 128 = 0) by (subst Fr; clear -FSR HP; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (FLG pos ltac:(change (fcap 1) with 8192; lia)) as FLC;
    eapply (rw_cells_transport asegs _ m mc) in FLC; [| exact MU| exact WM| unfold fflag_addr; change (fflags_off 1) with 20480; cbn; lia];
    unfold fflag_addr, flag_val in FLC; change (fflags_off 1) with 20480 in FLC; fold pos in FLC; rewrite HF', <- Hfl in FLC;
    (nelim (stk_carve asegs mc Fr (Fr + 128) 128 ltac:(eapply stk_sub; [exact VIS1| lia| lia]) ltac:(lia)) 3%nat; intros _ jf FRM);
    replace (Fr + 128 - Z.of_nat 128) with Fr in FRM by lia;
    apply (rw_cells_split_CB asegs mc Fr [] 128 jf [] [24; 8; 88; 8]%nat) in FRM; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FRM
  end.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (fs + 8, fs + 16); (fl, fl + 1); (Fr + 24, Fr + 32); (Fr + 120, Fr + 128); (shF, shF + 16)] m mc) in MU;
    [| unfold sub_fp; cbn; intros; tauto] end.
  setreg 15 (Z_to_bv 64 fl) ltac:(f_equal; lia).
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 5 lstep. fl. (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 Fr) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia).
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  unhide MTS. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply (mts_cells_munch _ m mc) in MTS; [| exact MU| intros; cbn; lia] end.
  call memtoshadow_walk; [exact MTS| exact MI| reflexivity| unfold KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END; lia| rewrite unsigned_lit by lia; exact ST|].
  after_call. try rewrite E32 in *. unfold SH, SHADOW_OFFSET. rewrite <- HshF.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    (nelim (stk_carve asegs mc shF (shF + 16) 16 ltac:(eapply stk_sub; [exact VIS2| subst shF Fr; clear -FSR HP; Z.div_mod_to_equations; lia| subst shF Fr; clear -FSR HP; Z.div_mod_to_equations; lia]) ltac:(lia)) 3%nat; intros _ js SHC);
    replace (shF + 16 - Z.of_nat 16) with shF in SHC by lia;
    apply (rw_cells_split_CB asegs mc shF [] 16 js [] [8; 8]%nat) in SHC; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in SHC
  end.
  lstep. lstep. (* [comment removed for export] *)
  do 4 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  assert (E1 : fframe_addr (st_fs st) 1 pos = Fr) by (unfold fframe_addr; change (Z.shiftl 1 FS_LOG) with 1048576; change FS_FRAMES_OFF with 36864; change (fsz 1) with 128; rewrite <- Hfs; lia).
  assert (E2 : fflag_addr (st_fs st) 1 pos = fl) by (unfold fflag_addr; change (fflags_off 1) with 20480; rewrite <- Hfs; lia).
  assert (E3 : SH Fr = shF) by (unfold SH, SHADOW_OFFSET; lia).
  setreg 10 (wz (fframe_addr (st_fs st) 1 pos)) ltac:(unfold wz; rewrite E1; reflexivity).
  pose proof (rw_cells_merge asegs m3 Fr [] [CB 24 (firstn 24 jf); C8 sp; CB 88 (firstn 88 (skipn 8 (skipn 24 jf)))] [C8 (Z_to_bv 64 fl)] FRM) as FRM'.
  cbn [app cells_size Cells.csize Nat.add] in FRM'.
  apply evt_done. unfold smk_post.
  nexists 14%nat. exists m3, pos, (u' + 1). eexists.
  split; [reflexivity|].
  split; [change (fcap 1) with 8192; exact HP|]. split; [exact HF'|]. split; [lia|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, smk_W. rewrite E1, E2, E3, <- Hfs. change (fsz 1) with 128. cbn [outside]. intros y Hy. lia. }
  split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [rewrite <- Hfs; replace (fs + 8 * 1) with (fs + 8) by lia; exact HINT|].
  split; [rewrite E2; exact FLC|].
  split; [rewrite E1; change (Z.to_nat (fsz 1 - 8)) with 120%nat; eapply rw_cells_take; exact FRM'|].
  split. { rewrite E1. change (fsz 1) with 128. pose proof (rw_cells_drop _ _ [CB 120 (cells_bytes [CB 24 (firstn 24 jf); C8 sp; CB 88 (firstn 88 (skipn 8 (skipn 24 jf)))])] [C8 (Z_to_bv 64 fl)] FRM') as D. cbn [cells_size Cells.csize Nat.add] in D.
           replace (Fr + 128 - 8) with (Fr + Z.of_nat 120) by lia. rewrite E2. exact D. }
  rewrite E1, E3. eapply rw_cells_recells; [exact SHC| vm_compute; repeat split; exact I| vm_compute; reflexivity| reflexivity].
Qed.

Lemma stkmalloc2_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (lo : Z),
  RTREP st m -> RTWF st -> mem_inv asegs m -> tp = wz ATP ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 208 <= bv_unsigned sp ->
  (exists pos, 0 <= pos < fcap 2 /\ flag_live st 2 pos = false) ->
  evt asegs (smk_post 2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ASTKMALLOC2) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HR WF MI TP ST CEIL LO FREE.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (fstls_cell st m HR) as K0. hide K0.
  pose proof (mts_cells_of st m HR) as MTS. change (mts_cells m) with (id (mts_cells m)) in MTS.
  (nelimp (fsobj_cells st m 2 HR ltac:(lia)) 6%nat; intros HINT LOG GC FLG VIS1 VIS2).
  pose proof (fs_range' st WF) as FSR. unfold KHIGHMEM_BEG, AIMG_HI, FS_TOTAL in FSR. olin FSR.
  remember (st_fs st) as fs eqn:Hfs.
  unfold FS_TOTAL, FS_FRAMES_OFF, SH, SHADOW_OFFSET in VIS1, VIS2. unfold FS_LOG in LOG. replace (fs + 8 * 2) with (fs + 16) in HINT by lia.
  unfold ASTKMALLOC2 in *. subst tp. leaf_prep.
  carve_frame 32%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  pose proof HR as HR1. rtrep_high HR1 WF MU WM.
  call tls_icpt_walk; [exact HR1| exact WF| exact MI| reflexivity| reflexivity| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
  after_call. clear HR1. unfold ATP.
  assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  rewrite E32 in *.
  recell K0 MU. lstep. clear K0. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 4 lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  do 5 lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 4 lstep. fl. (* [comment removed for export] *)
  do 4 lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  set (h := fhint st 2) in *. set (u := h mod 2^64).
  assert (HU : 0 <= u < 2^64) by (apply Z.mod_pos_bound; lia).
  setreg 12 (Z_to_bv 64 u) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); unfold u; rewrite Z.mod_mod by lia; reflexivity).
  (nelim FREE 3%nat; intros pos0 Hpos0 HF0). change (fcap 2) with 4096 in Hpos0.
  eapply (probe_loop (Z.to_nat 4096) 4096 0x3d6a8 0x3d720 4096 4095 (fs + 28672) (flag_live st 2) u);
    [reflexivity| right; repeat split| lia| lia| | exact HU| lia| |].
  { intros pos Hp. lazymatch goal with |- rw_cells _ ?mc _ _ =>
      eapply (rw_cells_transport asegs _ m mc); [| exact MU| exact WM| cbn; lia] end.
    pose proof (FLG pos ltac:(change (fcap 2) with 4096; lia)) as C. unfold fflag_addr, flag_val in C. change (fflags_off 2) with 28672 in C. exact C. }
  { exists ((pos0 - u) mod 4096). split; [apply Z.mod_pos_bound; lia|].
    replace ((u + (pos0 - u) mod 4096) mod 4096) with pos0; [exact HF0|].
    rewrite Zplus_mod_idemp_r. replace (u + (pos0 - u)) with pos0 by lia. symmetry. apply Z.mod_small. lia. }
  intros u' c' Hu' Hc' HF'.
  assert (HP : 0 <= u' mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
  set (pos := u' mod 4096) in *.
  (* [comment removed for export] *)
  do 3 lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (ex_intro (fun q => q = fs + 28672 + pos) _ eq_refl) as [fl Hfl].
  destruct (ex_intro (fun q => q = fs + 2134016 + 256 * pos) _ eq_refl) as [Fr HFr].
  destruct (ex_intro (fun q => q = 2147450880 + Fr / 8) _ eq_refl) as [shF HshF].
  assert (FrA : Fr mod 256 = 0) by (subst Fr; clear -FSR HP; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (FLG pos ltac:(change (fcap 2) with 4096; lia)) as FLC;
    eapply (rw_cells_transport asegs _ m mc) in FLC; [| exact MU| exact WM| unfold fflag_addr; change (fflags_off 2) with 28672; cbn; lia];
    unfold fflag_addr, flag_val in FLC; change (fflags_off 2) with 28672 in FLC; fold pos in FLC; rewrite HF', <- Hfl in FLC;
    (nelim (stk_carve asegs mc Fr (Fr + 256) 256 ltac:(eapply stk_sub; [exact VIS1| lia| lia]) ltac:(lia)) 3%nat; intros _ jf FRM);
    replace (Fr + 256 - Z.of_nat 256) with Fr in FRM by lia;
    apply (rw_cells_split_CB asegs mc Fr [] 256 jf [] [24; 8; 216; 8]%nat) in FRM; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FRM
  end.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (fs + 16, fs + 24); (fl, fl + 1); (Fr + 24, Fr + 32); (Fr + 248, Fr + 256); (shF, shF + 32)] m mc) in MU;
    [| unfold sub_fp; cbn; intros; tauto] end.
  setreg 15 (Z_to_bv 64 fl) ltac:(f_equal; lia).
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 7 lstep. fl. (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 Fr) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  unhide MTS. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => eapply (mts_cells_munch _ m mc) in MTS; [| exact MU| intros; cbn; lia] end.
  call memtoshadow_walk; [exact MTS| exact MI| reflexivity| unfold KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END; lia| rewrite unsigned_lit by lia; exact ST|].
  after_call. try rewrite E32 in *. unfold SH, SHADOW_OFFSET. rewrite <- HshF.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    (nelim (stk_carve asegs mc shF (shF + 32) 32 ltac:(eapply stk_sub; [exact VIS2| subst shF Fr; clear -FSR HP; Z.div_mod_to_equations; lia| subst shF Fr; clear -FSR HP; Z.div_mod_to_equations; lia]) ltac:(lia)) 3%nat; intros _ js SHC);
    replace (shF + 32 - Z.of_nat 32) with shF in SHC by lia;
    apply (rw_cells_split_CB asegs mc shF [] 32 js [] [8; 8; 8; 8]%nat) in SHC; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in SHC
  end.
  do 4 lstep. (* [comment removed for export] *)
  do 4 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  assert (E1 : fframe_addr (st_fs st) 2 pos = Fr) by (unfold fframe_addr; change (Z.shiftl 1 FS_LOG) with 1048576; change FS_FRAMES_OFF with 36864; change (fsz 2) with 256; rewrite <- Hfs; lia).
  assert (E2 : fflag_addr (st_fs st) 2 pos = fl) by (unfold fflag_addr; change (fflags_off 2) with 28672; rewrite <- Hfs; lia).
  assert (E3 : SH Fr = shF) by (unfold SH, SHADOW_OFFSET; lia).
  setreg 10 (wz (fframe_addr (st_fs st) 2 pos)) ltac:(unfold wz; rewrite E1; reflexivity).
  pose proof (rw_cells_merge asegs m3 Fr [] [CB 24 (firstn 24 jf); C8 sp; CB 216 (firstn 216 (skipn 8 (skipn 24 jf)))] [C8 (Z_to_bv 64 fl)] FRM) as FRM'.
  cbn [app cells_size Cells.csize Nat.add] in FRM'.
  apply evt_done. unfold smk_post.
  nexists 14%nat. exists m3, pos, (u' + 1). eexists.
  split; [reflexivity|].
  split; [change (fcap 2) with 4096; exact HP|]. split; [exact HF'|]. split; [lia|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, smk_W. rewrite E1, E2, E3, <- Hfs. change (fsz 2) with 256. cbn [outside]. intros y Hy. lia. }
  split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [rewrite <- Hfs; replace (fs + 8 * 2) with (fs + 16) by lia; exact HINT|].
  split; [rewrite E2; exact FLC|].
  split; [rewrite E1; change (Z.to_nat (fsz 2 - 8)) with 248%nat; eapply rw_cells_take; exact FRM'|].
  split. { rewrite E1. change (fsz 2) with 256. pose proof (rw_cells_drop _ _ [CB 248 (cells_bytes [CB 24 (firstn 24 jf); C8 sp; CB 216 (firstn 216 (skipn 8 (skipn 24 jf)))])] [C8 (Z_to_bv 64 fl)] FRM') as D. cbn [cells_size Cells.csize Nat.add] in D.
           replace (Fr + 256 - 8) with (Fr + Z.of_nat 248) by lia. rewrite E2. exact D. }
  rewrite E1, E3. eapply rw_cells_recells; [exact SHC| vm_compute; repeat split; exact I| vm_compute; reflexivity| reflexivity].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac if_lit := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota end.
End RTW_fs_smk.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_fs_art.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop.RT_artP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_artR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib RTW_fs_lib RTW_fs_smk OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fframe_addr_bounds : forall fs k pos, (k = 1 \/ k = 2) -> 0 <= pos < fcap k ->
  fs + FS_FRAMES_OFF <= fframe_addr fs k pos /\ fframe_addr fs k pos + fsz k <= fs + FS_TOTAL /\ (fframe_addr fs k pos - fs) mod fsz k = 0 /\ 128 <= fsz k <= 256 /\ fsz k / 8 * 8 = fsz k.
Proof.
  intros fs k pos Hk Hp. unfold fframe_addr, FS_FRAMES_OFF, FS_TOTAL. change (Z.shiftl 1 FS_LOG) with 1048576.
  destruct Hk as [-> | ->]; [change (fsz 1) with 128; change (fcap 1) with 8192 in Hp| change (fsz 2) with 256; change (fcap 2) with 4096 in Hp].
  - split; [lia|]. split; [lia|]. split; [| split; [lia| reflexivity]]. replace (fs + (4096 + 2^15) + 1048576 * 1 + 128 * pos - fs) with ((8480 + pos) * 128) by lia. apply Z_mod_mult.
  - split; [lia|]. split; [lia|]. split; [| split; [lia| reflexivity]]. replace (fs + (4096 + 2^15) + 1048576 * 2 + 256 * pos - fs) with ((8336 + pos) * 256) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma fframe_addr_inj : forall fs k pos k' pos', (k = 1 \/ k = 2) -> 0 <= pos < fcap k -> (k' = 1 \/ k' = 2) -> 0 <= pos' < fcap k' ->
  fframe_addr fs k pos = fframe_addr fs k' pos' -> k = k' /\ pos = pos'.
Proof.
  intros fs k pos k' pos' Hk Hp Hk' Hp' E. unfold fframe_addr in E. change (Z.shiftl 1 FS_LOG) with 1048576 in E.
  destruct Hk as [-> | ->]; destruct Hk' as [-> | ->];
    try change (fsz 1) with 128 in E; try change (fsz 2) with 256 in E;
    try change (fcap 1) with 8192 in Hp; try change (fcap 2) with 4096 in Hp; try change (fcap 1) with 8192 in Hp'; try change (fcap 2) with 4096 in Hp'; lia.
Qed.

(* [comment removed for export] *)
Lemma fframes_apart : forall fs k pos k' pos', (k = 1 \/ k = 2) -> 0 <= pos < fcap k -> (k' = 1 \/ k' = 2) -> 0 <= pos' < fcap k' ->
  (k <> k' \/ pos <> pos') ->
  fframe_addr fs k pos + fsz k <= fframe_addr fs k' pos' \/ fframe_addr fs k' pos' + fsz k' <= fframe_addr fs k pos.
Proof.
  intros fs k pos k' pos' Hk Hp Hk' Hp' NE. unfold fframe_addr. change (Z.shiftl 1 FS_LOG) with 1048576.
  destruct Hk as [-> | ->]; destruct Hk' as [-> | ->];
    try change (fsz 1) with 128; try change (fsz 2) with 256;
    try change (fcap 1) with 8192 in Hp; try change (fcap 2) with 4096 in Hp; try change (fcap 1) with 8192 in Hp'; try change (fcap 2) with 4096 in Hp'; lia.
Qed.

(* [comment removed for export] *)
Lemma live_flag : forall st F k, RTWF st -> In (F, k) (st_lf st) -> flag_live st k (fpos st F k) = true /\ F = fframe_addr (st_fs st) k (fpos st F k)
  /\ (k = 1 \/ k = 2) /\ 0 <= fpos st F k < fcap k.
Proof.
  intros st F k WF Hin. (nelim (wff_frame st (wf_fs_ok st WF) F k Hin) 3%nat; intros Hk Hp EF).
  split; [| split; [exact EF| split; [exact Hk| exact Hp]]].
  unfold flag_live. apply existsb_exists. exists (F, k). split; [exact Hin|]. cbn [fst snd]. rewrite Z.eqb_refl, <- EF, Z.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ADD.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool)
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Variables (LB : list (Z * Z)) (LF : list fframe).
Variables (k pos u lo SP : Z) (m m' : word -> option byte).
Let st  := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 LF a18 a19 a20 a21 a22 LB b1 b2 b3 b4 b5.
Let Fr := fframe_addr a15 k pos.
Let fl := fflag_addr a15 k pos.
Let st' := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 (updz a16 k u) ((Fr, k) :: LF) a18 a19 a20 a21 a22 LB b1 b2 b3 b4 b5.
Hypothesis WF : RTWF st.
Hypothesis HR : RTREP st m.
Hypothesis Hk : k = 1 \/ k = 2.
Hypothesis Hpos : 0 <= pos < fcap k.
Hypothesis FREE : flag_live st k pos = false.
Hypothesis Hu : 0 <= u.
Hypothesis HLO : CEIL <= lo.
Hypothesis MU : munch (smk_W k lo SP a15 pos) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis HINT : rw_cells asegs m' (a15 + 8 * k) [W8 u].
Hypothesis FLC : rw_cells asegs m' fl [W1 1].
Hypothesis SFP : rw_cells asegs m' (Fr + fsz k - 8) [W8 fl].

Local Abbreviation fs := a15.
Local Abbreviation W := (smk_W k lo SP a15 pos).

Lemma fsR : ablk fs (fs + FS_TOTAL) /\ fs + FS_TOTAL <= CEIL /\ fs mod 4096 = 0.   (* [comment removed for export] *)
Proof. pose proof (RT_fp.fs_range st WF) as H. cbn [st_fs st] in H. unfold CEIL. exact H. Qed.

Lemma k_lt11 : 0 <= k < 11.
Proof. destruct Hk as [-> | ->]; lia. Qed.

Lemma FrR : fs + FS_FRAMES_OFF <= Fr /\ Fr + fsz k <= fs + FS_TOTAL /\ (Fr - fs) mod fsz k = 0 /\ 128 <= fsz k <= 256 /\ fsz k / 8 * 8 = fsz k.
Proof. exact (fframe_addr_bounds fs k pos Hk Hpos). Qed.

Lemma flR : fs + 4096 <= fl /\ fl + 1 <= fs + 0x9000.
Proof. unfold fl. apply fflag_addr_range; [exact k_lt11| exact Hpos]. Qed.

Lemma Fr_mod8 : Fr mod 8 = 0.
Proof.
  (nelimp FrR 5%nat; intros _ _ M B D). (nelimp fsR 3%nat; intros _ _ M2).
  destruct Hk as [-> | ->]; [change (fsz 1) with 128 in M| change (fsz 2) with 256 in M]; clear -M M2; Z.div_mod_to_equations; lia.
Qed.

Lemma SH_Fr_end : SH (Fr + fsz k) = SH Fr + fsz k / 8.
Proof. (nelimp FrR 5%nat; intros _ _ _ _ F5). pose proof Fr_mod8 as M. unfold SH. clear -F5 M. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma add_disj5 : forall a sz, (a + sz <= lo \/ SP <= a) -> (a + sz <= fs + 8 * k \/ fs + 8 * k + 8 <= a) -> (a + sz <= fl \/ fl + 1 <= a) ->
  (a + sz <= Fr \/ Fr + fsz k <= a) -> (a + sz <= SH Fr \/ SH Fr + fsz k / 8 <= a) -> disjoint_from W a sz.
Proof.
  intros a sz D1 D2 D3 D4 D5. (nelimp FrR 5%nat; intros F1 F2 _ F4 F5).
  unfold smk_W. cbn [disjoint_from]. fold Fr fl. repeat split; lia.
Qed.
Lemma add_disj : forall a sz, (a + sz <= lo \/ SP <= a) -> (a + sz <= fs \/ fs + 0x9000 <= a) -> (a + sz <= Fr \/ Fr + fsz k <= a) ->
  (a + sz <= SH Fr \/ SH Fr + fsz k / 8 <= a) -> disjoint_from W a sz.
Proof.
  intros a sz D1 D2 D3 D4. pose proof flR as [L1 L2]. pose proof k_lt11. apply add_disj5; lia.
Qed.
Lemma add_outside : forall x, ~ (lo <= x < SP) -> ~ (fs <= x < fs + 0x9000) -> ~ (Fr <= x < Fr + fsz k) -> ~ (SH Fr <= x < SH Fr + fsz k / 8) -> outside W x.
Proof.
  intros x D1 D2 D3 D4. (nelimp FrR 5%nat; intros F1 F2 _ F4 F5). pose proof flR as [L1 L2]. pose proof k_lt11.
  unfold smk_W. cbn [outside]. fold Fr fl. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma marks : ablk fs (fs + FS_TOTAL) /\ fs + 0x9000 <= Fr /\ 128 <= fsz k <= 256 /\ Fr + fsz k <= fs + FS_TOTAL /\ fs + FS_TOTAL <= CEIL /\ CEIL <= lo
  /\ 2147450880 <= SH Fr /\ SH Fr + fsz k / 8 <= SH CEIL /\ SH CEIL < KHIGHMEM_BEG.
Proof.
  (nelimp fsR 3%nat; intros R1 R2 _). (nelimp FrR 5%nat; intros F1 F2 _ F4 _). rewrite <- SH_Fr_end.
  pose proof (rt_SH_bounds Fr ltac:(unfold CEIL, FS_FRAMES_OFF in *; blia)) as [B1 _].
  pose proof (rt_SH_mono (Fr + fsz k) (@CEIL ACEIL) ltac:(lia)) as B2. rewrite SH_CEIL in *. unfold FS_FRAMES_OFF in *.
  split; [exact R1|]. unfold KHIGHMEM_BEG, AIMG_HI in *. lia.
Qed.

(* [comment removed for export] *)
Lemma add_Zimg : forall a sz lo' hi', In (lo', hi') ART_STATIC -> lo' <= a -> a + sz <= hi' -> 0 < sz -> disjoint_from W a sz.
Proof.
  intros a sz lo' hi' HS Ha H1 Hsz. (nelimp (static_facts lo' hi' HS) 3%nat; intros _ S2 _). (nelimp marks 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9).
  rewrite SH_CEIL in *. unfold AIMG_HI, KHIGHMEM_BEG, CEIL, FS_TOTAL in *. apply add_disj; blia.
Qed.
Lemma add_Zheap' : forall lo' hi', oclr lo' hi' -> hi' <= CEIL ->
  (forall A n, In (A, n) (st_lb st) -> hi' <= A \/ A + n <= lo') -> framefree st lo' hi' -> disjoint_from W lo' (hi' - lo').
Proof.
  intros lo' hi' H1 H2 _ HF. unfold framefree in HF. cbn [st_fs st] in HF. (nelimp marks 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9).
  rewrite SH_CEIL in *. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, FS_TOTAL in *. apply add_disj; blia.
Qed.
Lemma add_Zsh : forall lo' hi', 0 <= lo' -> lo' <= hi' -> hi' <= CEIL -> lo' mod 8 = 0 -> framefree st lo' hi' ->
  disjoint_from W (SH lo') (SH hi' - SH lo').
Proof.
  intros lo' hi' G0 G1 G2 AL HF. unfold framefree in HF. cbn [st_fs st] in HF. (nelimp marks 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9).
  pose proof (rt_SH_mono hi' CEIL G2) as B2. pose proof (rt_SH_mono lo' hi' G1) as B3. pose proof (rt_SH_bounds lo' ltac:(unfold CEIL in *; lia)) as [B4 _].
  pose proof SH_Fr_end as E.
  assert (D3 : SH hi' <= SH Fr \/ SH (Fr + fsz k) <= SH lo').
  { destruct HF as [HF|HF]; [left; apply rt_SH_mono; lia| right; apply rt_SH_mono; lia]. }
  rewrite SH_CEIL in *. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, FS_TOTAL in *. apply add_disj; blia.
Qed.

(* [comment removed for export] *)
Lemma fpos_new : fpos st' Fr k = pos.
Proof.
  unfold fpos. cbn [st_fs st']. unfold Fr, fframe_addr.
  replace (fs + FS_FRAMES_OFF + Z.shiftl 1 FS_LOG * k + fsz k * pos - (fs + FS_FRAMES_OFF + Z.shiftl 1 FS_LOG * k)) with (pos * fsz k) by lia.
  apply Z.div_mul. destruct Hk as [-> | ->]; discriminate.
Qed.
Lemma fpos_same : forall F j, fpos st' F j = fpos st F j.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Fr_fresh : ~ In Fr (map fst LF).
Proof.
  intros Hin. apply in_map_iff in Hin as ((F' & k') & E & Hin). cbn [fst] in E. subst F'.
  (nelim (live_flag st Fr k' WF Hin) 4%nat; intros LV EF Hk' Hp'). cbn [st_fs st] in EF.
  destruct (fframe_addr_inj fs k pos k' (fpos st Fr k') Hk Hpos Hk' Hp' EF) as [E1 E2]. subst k'. rewrite <- E2, FREE in LV. discriminate.
Qed.

(* [comment removed for export] *)
Lemma old_apart : forall F' k', In (F', k') LF -> Fr + fsz k <= F' \/ F' + fsz k' <= Fr.
Proof.
  intros F' k' Hin. (nelim (live_flag st F' k' WF Hin) 4%nat; intros LV EF Hk' Hp'). cbn [st_fs st] in EF.
  assert (NE : k <> k' \/ pos <> fpos st F' k').
  { destruct (Z.eq_dec k k') as [<-|NK]; [| left; exact NK]. right. intros E. rewrite <- E in LV. rewrite FREE in LV. discriminate. }
  rewrite EF. exact (fframes_apart fs k pos k' (fpos st F' k') Hk Hpos Hk' Hp' NE).
Qed.

(* [comment removed for export] *)
Lemma flag_val_add : forall k' pos', 0 <= k' < 11 -> 0 <= pos' < fcap k' ->
  flag_val st' k' pos' = (if (k' =? k) && (pos' =? pos) then 1 else flag_val st k' pos').
Proof.
  intros k' pos' Hk' Hp'. unfold flag_val, flag_live. cbn [st_lf st_fs st st' existsb fst snd]. fold Fr.
  destruct (Z.eqb_spec k k') as [<-|NK]; cbn [andb].
  - rewrite Z.eqb_refl. cbn [andb]. destruct (Z.eqb_spec pos' pos) as [->|NP].
    + replace (Fr =? fframe_addr fs k pos) with true by (symmetry; apply Z.eqb_eq; reflexivity). reflexivity.
    + destruct (Z.eqb_spec Fr (fframe_addr fs k pos')) as [E|NE]; [| reflexivity].
      exfalso. assert (Hk2 : k = 1 \/ k = 2) by exact Hk.
      destruct (fframe_addr_inj fs k pos k pos' Hk Hpos Hk2 Hp' E) as [_ EP]. exact (NP (eq_sym EP)).
  - replace (k' =? k) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma R_fs_add : R_fs st' m'.
Proof.
  (nelim (rr_fs st m HR) 7%nat; intros V1 V2 HINTS LOG GC FLG SAV). cbn [st_fs st] in *.
  (nelimp marks 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9). pose proof flR as [L1 L2]. pose proof k_lt11 as K11.
  pose proof (wb_len_hints st (wf_base_ok st WF)) as LH. cbn [st_hints st] in LH.
  unfold R_fs. cbn [st_fs st_lf st'].
  split; [eapply RT_fp.visT; [exact WM| exact V1| unfold AIMG_HI, KHIGHMEM_BEG in *; blia]|].
  split; [eapply RT_fp.visT; [exact WM| exact V2| pose proof (rt_SH_bounds (fs + FS_FRAMES_OFF) ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI, FS_FRAMES_OFF, FS_TOTAL in *; blia)); unfold AIMG_HI; lia]|].
  split.
  { intros j Hj. unfold fhint. cbn [st_hints st']. destruct (Z.eq_dec j k) as [->|NE].
    - rewrite nthz_updz_same by (unfold zlen; rewrite LH; cbn; lia). exact HINT.
    - rewrite nthz_updz_other by lia. eapply RT_fp.rwT; [exact MU| exact WM| exact (HINTS j Hj)|].
      rewrite SH_CEIL in *. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. apply add_disj5; cbn; blia. }
  split; [eapply RT_fp.rwT; [exact MU| exact WM| exact LOG| rewrite SH_CEIL in *; unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *; apply add_disj5; cbn; blia]|].
  split; [eapply RT_fp.rwT; [exact MU| exact WM| exact GC| rewrite SH_CEIL in *; unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *; apply add_disj5; cbn; blia]|].
  split.
  { intros k' pos' Hk' Hp'. rewrite (flag_val_add k' pos' Hk' Hp').
    destruct (Z.eqb_spec k' k) as [->|NK]; [destruct (Z.eqb_spec pos' pos) as [->|NP]|]; cbn [andb].
    - exact FLC.
    - eapply RT_fp.rwT; [exact MU| exact WM| exact (FLG k pos' Hk' Hp')|].
      pose proof (fflag_addr_range fs k pos' Hk' Hp') as [Q1 Q2].
      assert (NEQ : fflag_addr fs k pos' <> fl).
      { intros E. destruct (fflag_addr_inj fs k pos' k pos Hk' Hp' Hk' Hpos E) as [_ E2]. exact (NP E2). }
      rewrite SH_CEIL in *. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. apply add_disj5; cbn; first [lia| blia| unfold fl, fflag_addr in *; lia| unfold fl, fflag_addr in *; blia].
    - eapply RT_fp.rwT; [exact MU| exact WM| exact (FLG k' pos' Hk' Hp')|].
      pose proof (fflag_addr_range fs k' pos' Hk' Hp') as [Q1 Q2].
      assert (NEQ : fflag_addr fs k' pos' <> fl).
      { intros E. destruct (fflag_addr_inj fs k' pos' k pos Hk' Hp' K11 Hpos E) as [E1 _]. exact (NK E1). }
      rewrite SH_CEIL in *. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. apply add_disj5; cbn; first [lia| blia| unfold fl, fflag_addr in *; lia| unfold fl, fflag_addr in *; blia]. }
  intros F' k' [E|Hin].
  - injection E as E2 E1. subst F' k'. rewrite fpos_new. exact (proj1 SFP).
  - rewrite fpos_same. eapply RT_fp.roT; [exact MU| exact (SAV F' k' Hin)|].
    pose proof (old_apart F' k' Hin) as AP. (nelimp (frame_range st WF F' k' Hin) 4%nat; intros Hk'' X Y AL). cbn [st_fs st] in X, Y.
    destruct (fsz_12 k' Hk'') as (FZ' & _). assert (128 <= fsz k') by (rewrite FZ'; destruct Hk'' as [-> | ->]; cbn; lia).
    rewrite SH_CEIL in *. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, FS_FRAMES_OFF in *. apply add_disj; cbn; blia.
Qed.

Lemma RTREP_add : RTREP st' m'.
Proof.
  pose proof add_Zimg as ZI. pose proof add_Zheap' as ZH. pose proof add_Zsh as ZS.
  constructor.
  - eapply (RT_fp.T_link W m m' MU); [exact (rr_link st m HR)| eapply W_link; eauto].
  - eapply (RT_fp.T_consts st WF W m m' MU WM); [exact (rr_consts st m HR)| eapply W_consts; eauto].
  - eapply (RT_fp.T_alloc st W m m' MU WM); [exact (rr_alloc st m HR)| eapply W_alloc; eauto].
  - eapply (RT_fp.T_rinfo st WF W m m' MU WM); [exact (rr_rinfo st m HR)| eapply W_rinfo; eauto].
  - eapply (RT_fp.T_regions st WF W m m' MU WM); [exact (rr_regions st m HR)| eapply W_regions; eauto].
  - eapply (RT_fp.T_avail st WF W m m' MU WM); [exact (rr_avail st m HR)| eapply W_avail; eauto].
  - eapply (RT_fp.T_cache st W m m' MU WM); [exact (rr_cache st m HR)| eapply W_cache; eauto].
  - eapply (RT_fp.T_thread st WF W m m' MU WM); [exact (rr_thread st m HR)| eapply W_thread; eauto].
  - eapply (RT_fp.T_live st WF W m m' MU WM); [exact (rr_live st m HR)| eapply W_live; eauto].
  - eapply (RT_fp.T_quar st WF W m m' MU WM); [exact (rr_quar st m HR)| eapply W_quar; eauto].
  - eapply (RT_fp.T_batches st WF W m m' MU WM); [exact (rr_batches st m HR)| eapply W_batches; eauto].
  - eapply (RT_fp.T_ptrarr st WF W m m' MU WM); [exact (rr_ptrarr st m HR)| eapply W_ptrarr; eauto].
  - eapply (RT_fp.T_depot st WF W m m' MU WM); [exact (rr_depot st m HR)| eapply W_depot; eauto].
  - exact R_fs_add.
  - eapply (RT_fp.T_ia W m m' MU WM); [exact (rr_ia st m HR)| eapply W_ia; eauto].
  - eapply (RT_fp.T_lowshadow W m m' MU WM); [exact (rr_lowshadow st m HR)| eapply W_lowshadow; eauto].
Qed.

Lemma RTWF_add : RTWF st'.
Proof.
  pose proof (wb_len_hints st (wf_base_ok st WF)) as LH. cbn [st_hints st] in LH.
  constructor.
  - destruct (wf_base_ok st WF); constructor; try assumption.
    + cbn [st_hints st']. rewrite updz_length. exact LH.
    + intros j. unfold fhint. cbn [st_hints st']. destruct (Z.eq_dec j k) as [->|NE].
      * rewrite nthz_updz_same by (unfold zlen; rewrite LH; pose proof k_lt11; lia). exact Hu.
      * rewrite nthz_updz_other by (lia_on wb_sp0 wb_nres NE). apply (wb_hints j).
  - intros c Hc. destruct (wf_class_ok st WF c Hc); constructor; assumption.
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; assumption.
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - pose proof (wf_fs_ok st WF) as WFF. constructor.
    + cbn [st_lf st' map fst]. constructor; [exact Fr_fresh| exact (wff_nodup st WFF)].
    + intros F j [E|Hin].
      * injection E as E2 E1. subst F j. rewrite fpos_new. split; [exact Hk|]. split; [exact Hpos|]. reflexivity.
      * rewrite fpos_same. exact (wff_frame st WFF F j Hin).
Qed.

Lemma RTMODEL_add : forall mo, RTMODEL st mo -> RTMODEL st' mo.
Proof. intros mo H. exact H. Qed.

Lemma rt_prov_add : rt_prov st' = rt_prov st.
Proof.
  assert (E1 : prov_classes st' = prov_classes st) by reflexivity.
  assert (E2 : prov_nb st' = prov_nb st) by reflexivity.
  assert (E3 : prov_q st' = prov_q st) by reflexivity.
  assert (E4 : prov_ptr st' = prov_ptr st) by reflexivity.
  assert (E5 : prov_live st' = prov_live st) by reflexivity.
  assert (E6 : prov_quar st' = prov_quar st) by reflexivity.
  assert (E7 : prov_depot st' = prov_depot st) by reflexivity.
  assert (E8 : prov_slots st' = prov_slots st) by reflexivity.
  unfold rt_prov. rewrite E1, E2, E3, E4, E5, E6, E7, E8. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Fr_facts : Fr mod fsz k = 0 /\ ablk Fr (Fr + fsz k) /\ Fr + fsz k <= alloc_ceiling.   (* [comment removed for export] *)
Proof.
  (nelimp marks 7%nat; intros M1 M2 M3 M4 M5 M6 _). (nelimp FrR 4%nat; intros _ _ MF _). (nelimp fsR 3%nat; intros _ _ MA). rewrite CEIL_eq.
  (nelimp FrR 3%nat; intros FQ1 FQ2 _). unfold FS_FRAMES_OFF in FQ1.
  split; [| split; [apply (ablk_sub _ _ _ _ M1); lia| lia]]. destruct Hk as [-> | ->]; [change (fsz 1) with 128 in *| change (fsz 2) with 256 in *]; clear -MF MA; Z.div_mod_to_equations; lia.
Qed.

Lemma lb_apart : forall A n, In (A, n) LB -> A + n <= Fr \/ Fr + fsz k <= A.
Proof.
  intros A n Hin. assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  (nelimp (block_geom st WF A n J) 7%nat; intros Gn _ G1 G2 G3 G4 _). unfold usz in G3.
  pose proof (block_framefree st WF A n J) as BF. unfold framefree in BF. cbn [st_fs st] in BF.
  (nelimp marks 5%nat; intros M1 M2 M3 M4 _). lia.
Qed.

(* [comment removed for export] *)
Lemma cli_add : lo <= SP -> cj_pres a1 LB LF SP m m'.
Proof.
  intros HSP a Ha HC. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
  (nelimp marks 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9). pose proof SH_Fr_end as SE.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. cbn [st_sp0 st] in SP0.
  rewrite SH_CEIL in *. unfold KHIGHMEM_BEG, AIMG_HI, FS_TOTAL in *.
  destruct HC as [H|[H|[H|[H|H]]]].
  - (* [comment removed for export] *) apply add_outside; unfold CEIL in *; lia.
  - (* [comment removed for export] *) unfold aclient_image, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI in H. apply add_outside; unfold CEIL in *; blia.
  - (* [comment removed for export] *) (nelim H 4%nat; intros A n Hin HA). pose proof (lb_apart A n Hin) as AP.
    assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
    (nelimp (block_geom st WF A n J) 7%nat; intros Gn _ G1 G2 G3 G4 _). unfold usz in G3.
    pose proof (block_framefree st WF A n J) as BF. unfold framefree in BF. cbn [st_fs st] in BF.
    unfold KHIGHMEM_BEG, AIMG_HI, FS_TOTAL, CEIL in *. apply add_outside; blia.
  - (* [comment removed for export] *) (nelim H 4%nat; intros F' k' Hin HA). pose proof (old_apart F' k' Hin) as AP.
    (nelimp (frame_range st WF F' k' Hin) 4%nat; intros Hk' X Y AL). cbn [st_fs st] in X, Y. unfold FS_FRAMES_OFF, FS_TOTAL in X, Y.
    pose proof (rt_SH_bounds F' ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *; blia)) as [B1 B2].
    pose proof (rt_SH_mono (F' + fsz k') (@CEIL ACEIL) ltac:(unfold CEIL in *; lia)) as B3. rewrite SH_CEIL in B3.
    (nelim (fsz_12 k' Hk') 5%nat; intros FZ' _ _ _ _).
    assert (F8 : 128 <= fsz k' <= 256 /\ fsz k' / 8 * 8 = fsz k') by (rewrite FZ'; destruct Hk' as [-> | ->]; cbn; lia).
    assert (SE' : SH (F' + fsz k') = SH F' + fsz k' / 8) by (unfold SH; clear -AL F8; Z.div_mod_to_equations; lia).
    assert (D : SH Fr + fsz k / 8 <= SH F' \/ SH F' + fsz k' / 8 <= SH Fr).
    { rewrite <- SE, <- SE'. destruct AP as [AP|AP]; [left| right]; apply rt_SH_mono; exact AP. }
    unfold CEIL in *. apply add_outside; (cut_on [M1 M3 M4 M6 SP0 HA Y AL B2 F8 M2 M7 M8 AP Hk' X B1 B3 SE' D] blia).
  - (* [comment removed for export] *) unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H.
    unfold CEIL in *. apply add_outside; blia.
Qed.

(* [comment removed for export] *)
Lemma post_add : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 x11 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (e : word) (SPB B : Z) (mo : Model) (g : lghost) (junk : list byte),
  SP = bv_unsigned sp -> lo <= SP ->
  RTMODEL st mo -> LOK asegs mo -> BINV mo g -> GWIN st m mo g -> FRONTR mo (g_res g) -> QUIET st ->
  0 <= B -> B + rt_prov st <= g_res g -> SPB <= a1 -> SWIN st g ->
  mem_inv asegs m' -> stk asegs m' lo SP -> rw_cells asegs m AERRNO [C4 e] ->
  rw_cells asegs m' Fr [CB (Z.to_nat (fsz k - 8)) junk] ->
  rw_cells asegs m' (SH Fr) (shcells (repeat 0 (Z.to_nat (fsz k / 8)))) ->
  astkmalloc_post ARTd ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a1 SPB LB LF a13 B k lo e m mo g
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz Fr) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom asegs)) mo g.
Proof.
  intros until junk. intros HSPq HSP HM HO HB HG HFR HQ HB0 HB1 HSPB HSW MI' ST' ERR FRM SHC.
  (nelimp marks 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9). (nelimp Fr_facts 3%nat; intros Q1 Q2 Q3).
  unfold astkmalloc_post. nexists 15%nat. exists m', Fr, junk, fl.
  split; [reflexivity|]. split; [exact MI'|]. split; [rewrite <- HSPq; exact ST'|].
  split. { eapply RT_fp.rwT; [exact MU| exact WM| exact ERR|]. unfold AERRNO, ATP. rewrite SH_CEIL in *. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. apply add_disj; cbn; blia. }
  split; [rewrite <- HSPq; apply cli_add; exact HSP|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [exact Q1|]. split; [exact (ablk_img _ _ Q2)|]. split; [exact Q3|].
  split; [exact Fr_fresh|].
  split; [exact lb_apart|].
  split.
  { apply (ARTd_intro st'); [exact RTREP_add| exact RTWF_add| apply RTMODEL_add; exact HM| exact HO| exact HB| | exact HFR| reflexivity| reflexivity| reflexivity| reflexivity| exact HQ| exact HB0| rewrite rt_prov_add; exact HB1| exact HSPB| eapply SWIN_st; [exact HSW| reflexivity]].
    eapply GWIN_st; [eapply GWIN_mem; [exact HG| exact HO| exact WM]|]. intros b Hb. exact Hb. }
  split; [exact FRM|]. split; [exact (proj1 SFP)| exact SHC].
Qed.
End ADD.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem art_stkmalloc1_proof : stkmalloc_lscps_stmt ARTd 1.
Proof.
  unfold stkmalloc_lscps_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo g sp0 SPB LB LF TRS B lo errv.
  intros HART HSPB ST CEIL LO MI TP ERR LFC.
  (nelim HART 17%nat; intros st HR WF HM HO HB HG HFR Hsp0 HLB HLF HTRS HQ HB0 HB1 HSPB' HSW).
  (nelim (free_slot_exists st 1 ltac:(lia) ltac:(rewrite HLF; exact LFC)) 3%nat; intros pos0 Hp0 HF0).
  unfold ASTKMALLOC_STACK in LO. change (if 1 =? 1 then ASTKMALLOC1 else ASTKMALLOC2) with ASTKMALLOC1.
  eapply lscps_mono.
  { apply lscps_evt. eapply stkmalloc1_walk; [exact HR| exact WF| exact MI| exact TP| exact ST| exact CEIL| lia| exists pos0; split; [exact Hp0| exact HF0]]. }
  cbv beta. intros ms' mo' g' nelH_; (nelim nelH_ 3%nat; intros PO -> ->).
  (nelim PO 31%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' pos u junk -> Hpos HF Hu MU WM MI' ST' HINT FLC FRM SFP SHC).
  destruct st as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 c1 c2 c3 c4 c5].
  cbn [st_sp0 st_lb st_lf st_trs st_fs] in *. subst sp0 LB LF TRS.
  eapply post_add; [exact WF| exact HR| lia| exact Hpos| exact HF| exact Hu| rewrite <- CEIL_eq; exact CEIL| exact MU| exact WM
    | exact HINT| exact FLC| exact SFP| reflexivity| lia| exact HM| exact HO| exact HB| exact HG| exact HFR| exact HQ| exact HB0| exact HB1| exact HSPB'| exact HSW
    | exact MI'| exact ST'| exact ERR| exact FRM| exact SHC].
Qed.

Theorem art_stkmalloc2_proof : stkmalloc_lscps_stmt ARTd 2.
Proof.
  unfold stkmalloc_lscps_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo g sp0 SPB LB LF TRS B lo errv.
  intros HART HSPB ST CEIL LO MI TP ERR LFC.
  (nelim HART 17%nat; intros st HR WF HM HO HB HG HFR Hsp0 HLB HLF HTRS HQ HB0 HB1 HSPB' HSW).
  (nelim (free_slot_exists st 2 ltac:(lia) ltac:(rewrite HLF; exact LFC)) 3%nat; intros pos0 Hp0 HF0).
  unfold ASTKMALLOC_STACK in LO. change (if 2 =? 1 then ASTKMALLOC1 else ASTKMALLOC2) with ASTKMALLOC2.
  eapply lscps_mono.
  { apply lscps_evt. eapply stkmalloc2_walk; [exact HR| exact WF| exact MI| exact TP| exact ST| exact CEIL| lia| exists pos0; split; [exact Hp0| exact HF0]]. }
  cbv beta. intros ms' mo' g' nelH_; (nelim nelH_ 3%nat; intros PO -> ->).
  (nelim PO 31%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' pos u junk -> Hpos HF Hu MU WM MI' ST' HINT FLC FRM SFP SHC).
  destruct st as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 c1 c2 c3 c4 c5].
  cbn [st_sp0 st_lb st_lf st_trs st_fs] in *. subst sp0 LB LF TRS.
  eapply post_add; [exact WF| exact HR| lia| exact Hpos| exact HF| exact Hu| rewrite <- CEIL_eq; exact CEIL| exact MU| exact WM
    | exact HINT| exact FLC| exact SFP| reflexivity| lia| exact HM| exact HO| exact HB| exact HG| exact HFR| exact HQ| exact HB0| exact HB1| exact HSPB'| exact HSW
    | exact MI'| exact ST'| exact ERR| exact FRM| exact SHC].
Qed.


End CeilWrap.
End RTW_fs_art.

(* [comment removed for export] *)
Module RTW_unwind_loop.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition agree_on (lo hi : Z) (m m' : mem) : Prop := forall a, lo <= a < hi -> mrd asegs m' (wa a) = mrd asegs m (wa a).
Lemma bytes_at_agree : forall m m' A bs lo hi, bytes_at asegs m A bs -> agree_on lo hi m m' ->
  lo <= A -> A + Z.of_nat (length bs) <= hi -> bytes_at asegs m' A bs.
Proof.
  intros m m' A bs lo hi (H0 & H1 & HB) AG HL HH. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). apply AG. lia.
Qed.
(* [comment removed for export] *)
Definition tb_prefix (ws : list word) (done : list Z) : Prop := firstn (length done) ws = map wz done.

Section UWF.
  (* [comment removed for export] *)
  Variables (raU spE gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (s0v s1v s2v s3v s4v s5v s6v : word).          (* [comment removed for export] *)
  Variables (t0v t1v t2v t3v t4v t5v t6v : word).          (* [comment removed for export] *)
  Variables (m0 me : mem) (S pc0 bp TOP lo ubyte spI : Z) (tr : list Z).
  Hypothesis RS : bv_unsigned spE <= spI /\ spI <= S /\ spI <= bp - 16 /\ (S + BST_SIZE <= bp - 16 \/ TOP <= S) /\ S + BST_SIZE <= 2^64.
  Hypothesis RT : bp < 2^64 /\ TOP + 16 < 2^64 /\ 0 <= pc0 < 2^64.
  Hypothesis RLO : alloc_ceiling <= lo /\ lo + 64 <= bv_unsigned spE.
  Hypothesis RU : ubyte + 1 <= alloc_ceiling /\ 4096 <= ubyte /\ (ubyte + 1 <= AIMG_LO \/ AIMG_HI <= ubyte).   (* [comment removed for export] *)
  Hypothesis TRL : zlen tr <= 30.
  Hypothesis AG0 : agree_on (bp - 16) TOP m0 me.
  (* [comment removed for export] *)
  Definition W : list (Z * Z) := [(lo, spI); (S + 8, S + 12); (S + 16, S + 16 + 8 * zlen tr); (S + 2056, S + 2064); (ubyte, ubyte + 1)].
  Lemma WOUT : forall a, bp - 16 <= a < TOP -> outside W a.
  Proof.
    intros a Ha. pose proof (bv_unsigned_in_range 64 spE) as R. unfold BST_SIZE in RS. idtac.
    pose proof (zlen_nonneg tr). cbn. lia.
  Qed.

  Lemma ag_of_munch : forall mc, munch W me mc -> agree_on (bp - 16) TOP m0 mc.
  Proof.
    intros mc MU a Ha. pose proof (bv_unsigned_in_range 64 spE) as R. unfold bv_modulus in R.
    unfold BST_SIZE in RS.
    unfold mrd. rewrite (MU (wa a)). { apply AG0. exact Ha. }
    rewrite wa_unsigned by lia. apply WOUT. exact Ha.
  Qed.

  #[warnings="-notation-for-abbreviation"] Notation ST_ pc mm prev k f x17 :=
    (MS (mkR raU (Z_to_bv 64 (bv_unsigned spE + -64)) gp tp t0v t1v t2v (Z_to_bv 64 30) (Z_to_bv 64 (TOP + -16)) (Z_to_bv 64 S) (Z_to_bv 64 pc0) (Z_to_bv 64 prev) (Z_to_bv 64 4096)
              (Z_to_bv 64 (S + 16)) (Z_to_bv 64 k) (Z_to_bv 64 f) x17 (Z_to_bv 64 0x139d20) s3v s4v s5v s6v s7 s8 s9 s10 s11 t3v t4v t5v t6v)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma tb_prefix_snoc : forall ws done (v : word), tb_prefix ws done -> (length done < length ws)%nat ->
    tb_prefix (upd ws (length done) v) (done ++ [bv_unsigned v]).
  Proof.
    intros ws done v TB HL. unfold tb_prefix in *. rewrite length_app. cbn [length].
    rewrite (upd_firstn_skipn ws (length done) v HL).
    rewrite firstn_app. rewrite firstn_firstn by lia. replace (Nat.min (length done + 1) (length done)) with (length done) by lia.
    rewrite firstn_length_le by lia. replace (length done + 1 - length done)%nat with 1%nat by lia. cbn [firstn].
    rewrite TB, map_app. cbn [map]. unfold wz. rewrite Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition uinv (mc : mem) (k : Z) (done : list Z) : Prop :=
    exists ws, u64arr asegs mc (S + 16) ws /\ length ws = 255%nat /\ tb_prefix ws done /\ k = zlen done
    /\ rw_cells asegs mc S [C8 (wz (S + 16)); C4 (wz k); C4 (wz 0)]
    /\ rw_cells asegs mc (S + 2056) [C8 (wz bp)]
    /\ rw_cells asegs mc ubyte [C1 (zb 1)]
    /\ rw_cells asegs mc (bv_unsigned spE + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 raU]
    /\ mem_inv asegs mc /\ munch W me mc /\ wmono asegs me mc /\ stk asegs mc lo (bv_unsigned spE + -64).

  (* [comment removed for export] *)
  Definition upost (m' : mem) (tr : list Z) : Prop :=
    exists ws k', u64arr asegs m' (S + 16) ws /\ length ws = 255%nat /\ tb_prefix ws tr /\ k' = zlen tr /\ 1 <= k' <= 30
    /\ rw_cells asegs m' S [C8 (wz (S + 16)); C4 (wz k'); C4 (wz 0)]
    /\ rw_cells asegs m' (S + 2056) [C8 (wz bp)]
    /\ rw_cells asegs m' ubyte [C1 (zb 1)]
    /\ mem_inv asegs m' /\ munch W me m' /\ wmono asegs me m' /\ stk asegs m' lo (bv_unsigned spE).

  Definition uwf_post (tr : list Z) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
      ms' = MS (mkR raU spE gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc raU) fc None m' (seg_rom asegs)
      /\ upost m' tr.

  (* [comment removed for export] *)
  Lemma uwf_exit : forall (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) mc k done,
    uinv mc k done -> 1 <= k <= 30 ->
    evt asegs (uwf_post done)
      (MS (mkR raU (Z_to_bv 64 (bv_unsigned spE + -64)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 S) (Z_to_bv 64 pc0) x12 x13 x14 x15 x16 x17 x18 s3v s4v s5v s6v s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x74e00) fc None mc (seg_rom asegs)).
  Proof.
    intros until done. intros (ws & ARR & LEN & TB & Kd & OBJ & TFB & UNW & FRU & MI & MU & WM & ST) HK.
    pose proof (bv_unsigned_in_range 64 spE) as RSP. unfold bv_modulus in RSP. unfold BST_SIZE in RS. idtac. unfold AIMG_LO, AIMG_HI in RU.
    do 10 zstep.
    release_frame FRU ST (bv_unsigned spE).
    apply evt_done. unfold uwf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. exists ws, k.
    split; [exact ARR|]. split; [exact LEN|]. split; [exact TB|]. split; [exact Kd|]. split; [exact HK|].
    split; [exact OBJ|]. split; [exact TFB|]. split; [exact UNW|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. exact ST.
  Qed.

  Lemma land7_mod8 : forall f, 0 <= f -> Z.land f 7 = f mod 8.
  Proof. intros f Hf. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma uwf_loop : forall tl (prev k f : Z) x17 mc done,
    uwt m0 bp TOP pc0 prev f k tl ->
    bp <= prev < TOP -> 0 <= f < 2^64 -> 1 <= k <= 30 -> done ++ tl = tr ->
    uinv mc k done ->
    evt asegs (uwf_post (done ++ tl)) (ST_ 0x74dec mc prev k f x17).
  Proof.
    intros tl prev k f x17 mc done U. revert x17 mc done. unfold W in *.
    pose proof (bv_unsigned_in_range 64 spE) as RSP. unfold bv_modulus in RSP.
    unfold BST_SIZE in RS. idtac. unfold AIMG_LO, AIMG_HI in RU.
    induction U as [prev f k STOP| prev f k nxt pc1 PF AL FT KM LOF REC LOW | prev f k nxt pc1 tl PF AL FT KM LOF REC HIGH U IH];
      intros x17 mc done BP RF HK TR UI;
      (nelimp UI 13%nat; intros ws ARR LEN TB Kd OBJ TFB UNW FRU MI MU WM ST);
      pose proof (ag_of_munch mc MU) as AG; pose proof (zlen_nonneg tr) as TR0; unfold W in MU.
    - (* [comment removed for export] *)
      unfold TRACE_MAX_LEN in STOP. rewrite app_nil_r.
      zstep. (if_cases K1; zify_cond K1). { eapply uwf_exit; [exact UI| lia]. }
      zstep. (if_cases K2; zify_cond K2). { eapply uwf_exit; [exact UI| lia]. }
      zstep. zstep. zstep. (if_cases K3; zify_cond K3).
      2:{ eapply uwf_exit; [exact UI| lia]. }
      rewrite land7_mod8 in K3 by lia.
      zstep. (if_cases K4; zify_cond K4). { eapply uwf_exit; [exact UI| lia]. }
      exfalso. lia.
    - (* [comment removed for export] *)
      unfold TRACE_MAX_LEN in KM. rewrite app_nil_r.
      zstep. if_lia. zstep. if_lia. zstep. zstep. zstep.
      (if_cases K3; zify_cond K3). 2:{ exfalso. rewrite land7_mod8 in K3 by lia. lia. }
      zstep. if_lia. (* [comment removed for export] *)
      assert (RECc : ro_cells asegs mc (f + -16) [C8 nxt; C8 pc1]).
      { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        eapply (bytes_at_agree m0 mc); [exact REC| exact AG| lia| rewrite length_app, !length_le8; cbn; lia]. }
      zstep. (* [comment removed for export] *)
      zstep. (if_cases K5; zify_cond K5). 2:{ exfalso. lia. }
      eapply uwf_exit; [exact UI| lia].
    - (* [comment removed for export] *)
      unfold TRACE_MAX_LEN in KM.
      zstep. if_lia. zstep. if_lia. zstep. zstep. zstep.
      (if_cases K3; zify_cond K3). 2:{ exfalso. rewrite land7_mod8 in K3 by lia. lia. }
      zstep. if_lia. (* [comment removed for export] *)
      assert (RECc : ro_cells asegs mc (f + -16) [C8 nxt; C8 pc1]).
      { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        eapply (bytes_at_agree m0 mc); [exact REC| exact AG| lia| rewrite length_app, !length_le8; cbn; lia]. }
      zstep. (* [comment removed for export] *)
      zstep. (if_cases K5; zify_cond K5). { exfalso. lia. }
      zstep. (if_cases K6; zify_cond K6).
      + (* [comment removed for export] *)
        replace (bv_unsigned pc1 =? pc0) with true in * by (symmetry; apply Z.eqb_eq; exact K6).
        cbn [app]. rewrite Z.add_0_r in *.
        zstep. (* [comment removed for export] *)
        replace nxt with (Z_to_bv 64 (bv_unsigned nxt)) by (apply Z_to_bv_bv_unsigned).
        eapply IH; [lia| pose proof (bv_unsigned_in_range 64 nxt) as R; unfold bv_modulus in R; cbn in R; lia| lia| exact TR| exact UI].
      + (* [comment removed for export] *)
        replace (bv_unsigned pc1 =? pc0) with false in * by (symmetry; apply Z.eqb_neq; exact K6).
        cbn [app]. cbn [app] in TR.
        assert (TR1 : k + 1 <= zlen tr) by (rewrite <- TR, zlen_app, zlen_cons; pose proof (zlen_nonneg tl); lia).
        zstep. zstep. zstep. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        setreg 17 (Z_to_bv 64 (S + 16 + 8 * k)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
        pose proof (u64arr_store_ok asegs _ (S + 16) ws k (wa (S + 16 + 8 * k)) ARR ltac:(rewrite LEN; lia) eq_refl) as SOK.
        zstep. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
          pose proof (u64arr_write asegs mm (S + 16) ws k pc1 ARR ltac:(rewrite LEN; lia)) as ARR' end.
        store_done.
        zstep. (* [comment removed for export] *)
        replace nxt with (Z_to_bv 64 (bv_unsigned nxt)) by (apply Z_to_bv_bv_unsigned).
        replace (done ++ bv_unsigned pc1 :: tl) with ((done ++ [bv_unsigned pc1]) ++ tl) by (rewrite <- app_assoc; reflexivity).
        eapply IH; [lia| pose proof (bv_unsigned_in_range 64 nxt) as R; unfold bv_modulus in R; cbn in R; lia| lia| rewrite <- app_assoc; exact TR|].
        (* [comment removed for export] *)
        exists (upd ws (Z.to_nat k) pc1).
        split; [exact ARR'|]. split; [rewrite upd_length; exact LEN|].
        split. { replace (Z.to_nat k) with (length done) by (rewrite Kd; unfold zlen; lia). apply tb_prefix_snoc; [exact TB| rewrite LEN; unfold zlen in Kd; lia]. }
        split; [unfold zlen in *; rewrite length_app; cbn [length]; lia|].
        repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Notation STE_ pc mm x13 x14 x15 x16 x17 x18 :=
    (MS (mkR raU spE gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 S) (Z_to_bv 64 pc0) (Z_to_bv 64 bp) x13 x14 x15 x16 x17
              s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3v t4v t5v t6v)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Variables (BOTTOM : Z) (sp0 : Z) (rac s0c : word) (tl : list Z).
  Hypothesis HTOP : TOP = ASTACK_TOP sp0.
  Hypothesis HBOT : BOTTOM = ASTACK_BOTTOM sp0 /\ 0 <= BOTTOM.
  Hypothesis REC0 : bytes_at asegs m0 (bp - 16) (le8 s0c ++ le8 rac).
  Hypothesis RAC : 4096 <= bv_unsigned rac /\ bv_unsigned rac <> pc0.
  Hypothesis UWT : hop1_ok sp0 bp = true -> uwt m0 bp TOP pc0 bp (bv_unsigned s0c) 2 tl.
  Hypothesis HTR : tr = hook_tr pc0 sp0 bp (bv_unsigned rac) tl.

  Lemma uwf_entry : forall mc ws (szj x16 x17 : word),
    u64arr asegs mc (S + 16) ws -> length ws = 255%nat ->
    rw_cells asegs mc S [C8 (wz (S + 16)); C4 szj; C4 (wz 0)] ->
    rw_cells asegs mc (S + 2056) [C8 (wz bp)] ->
    rw_cells asegs mc ubyte [C1 (zb 1)] ->
    ro_cells asegs mc 0xa1f60 [C8 (Z_to_bv 64 0x139d20)] -> ro_cells asegs mc 0x139d20 [C8 (Z_to_bv 64 4096)] ->
    mem_inv asegs mc -> munch W me mc -> wmono asegs me mc -> stk asegs mc lo (bv_unsigned spE) ->
    evt asegs (uwf_post tr) (STE_ 0x74d04 mc (Z_to_bv 64 TOP) (Z_to_bv 64 BOTTOM) (Z_to_bv 64 30) x16 x17 w0).
  Proof.
    intros mc ws szj x16 x17 ARR LEN OBJ TFB UNW GOTC PSC MI MU WM ST.
    pose proof (bv_unsigned_in_range 64 spE) as RSP. unfold bv_modulus in RSP.
    unfold BST_SIZE in RS. idtac. unfold AIMG_LO, AIMG_HI in RU. unfold W in MU.
    pose proof (zlen_nonneg tr) as TR0.
    assert (TR1 : 1 <= zlen tr) by (rewrite HTR; unfold hook_tr; destruct (hop1_ok sp0 bp); unfold zlen; cbn [length]; lia).
    assert (TOPB : 4096 <= TOP /\ BOTTOM < TOP) by (destruct HBOT as [HB1 HB2]; rewrite HTOP, HB1 in *; unfold ASTACK_BOTTOM, ASTACK_TOP, roundup in *; lia).
    carve_frame 64%nat ST.
    do 9 zstep. (* [comment removed for export] *)
    do 4 zstep. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    zstep. zstep. fl. clear GOTC. (* [comment removed for export] *)
    zstep. fl. clear PSC. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (u64arr_store_ok asegs _ (S + 16) ws 0 (wa (S + 16)) ARR ltac:(rewrite LEN; lia) ltac:(f_equal; lia)) as SOK.
    zstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u64arr_write asegs mm (S + 16) ws 0 (Z_to_bv 64 pc0) ARR ltac:(rewrite LEN; lia)) as ARR1;
      replace (S + 16 + 8 * 0) with (S + 16) in ARR1 by lia end.
    store_done.
    assert (TB1 : tb_prefix (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)) [pc0]).
    { unfold tb_prefix. cbn [length map]. destruct ws; [cbn in LEN; lia| reflexivity]. }
    zstep. (if_cases K0; zify_cond K0); [clear K0| exfalso; rewrite Z.shiftr_div_pow2 in K0 by lia; change (2^12) with 4096 in K0; lia].
    zstep. if_lia. (* [comment removed for export] *)
    zstep. (if_cases K1; zify_cond K1).
    { destruct (hop1_ok sp0 bp) eqn:E.
      { exfalso; unfold hop1_ok in E; destruct HBOT as [HB1 HB2]; rewrite <- HTOP, <- HB1 in E.
        rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq in E. lia. }
      rewrite HTR, (hook_tr_ko _ _ _ _ _ E). eapply uwf_exit.
      { exists (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)); split; [exact ARR1|]; split; [rewrite upd_length; assumption|].
        split; [exact TB1|]. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
      unfold zlen; cbn [length]; lia. }
    zstep. zstep. (if_cases K2; zify_cond K2).
    { destruct (hop1_ok sp0 bp) eqn:E.
      { exfalso; unfold hop1_ok in E; destruct HBOT as [HB1 HB2]; rewrite <- HTOP, <- HB1 in E.
        rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq in E. lia. }
      rewrite HTR, (hook_tr_ko _ _ _ _ _ E). eapply uwf_exit.
      { exists (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)); split; [exact ARR1|]; split; [rewrite upd_length; assumption|].
        split; [exact TB1|]. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
      unfold zlen; cbn [length]; lia. }
    zstep. zstep. (if_cases K3; zify_cond K3).
    { rewrite land7_mod8 in K3 by lia. destruct (hop1_ok sp0 bp) eqn:E.
      { exfalso; unfold hop1_ok in E; destruct HBOT as [HB1 HB2]; rewrite <- HTOP, <- HB1 in E.
        rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq in E. lia. }
      rewrite HTR, (hook_tr_ko _ _ _ _ _ E). eapply uwf_exit.
      { exists (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)); split; [exact ARR1|]; split; [rewrite upd_length; assumption|].
        split; [exact TB1|]. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
      unfold zlen; cbn [length]; lia. }
    rewrite land7_mod8 in K3 by lia.
    assert (H1 : hop1_ok sp0 bp = true).
    { unfold hop1_ok. destruct HBOT as [HB1 HB2]. rewrite <- HTOP, <- HB1.
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia. reflexivity. }
    specialize (UWT H1). rewrite HTR. rewrite (hook_tr_ok _ _ _ _ _ H1).
    zstep. zstep. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RECc : ro_cells asegs mm (bp + -16) [C8 s0c; C8 rac]) end.
    { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. replace (bp + -16) with (bp - 16) by lia.
      eapply (bytes_at_agree m0); [exact REC0| apply ag_of_munch; assumption| lia| rewrite length_app, !length_le8; cbn; lia]. }
    zstep. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    zstep. (if_cases K5; zify_cond K5). { exfalso. lia. }
    zstep. zstep. zstep. fl. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    assert (TR2 : 2 <= zlen tr) by (rewrite HTR, (hook_tr_ok _ _ _ _ _ H1); unfold zlen; cbn [length]; pose proof (Zle_0_nat (length tl)); lia).
    pose proof (u64arr_store_ok asegs _ (S + 16) (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)) 1 (wa (S + 24)) ARR1
                  ltac:(rewrite upd_length, LEN; lia) ltac:(f_equal; lia)) as SOK1.
    zstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u64arr_write asegs mm (S + 16) (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)) 1 rac ARR1 ltac:(rewrite upd_length, LEN; lia)) as ARR2;
      replace (S + 16 + 8 * 1) with (S + 24) in ARR2 by lia end.
    store_done.
    zstep. (* [comment removed for export] *)
    replace s0c with (Z_to_bv 64 (bv_unsigned s0c)) by (apply Z_to_bv_bv_unsigned).
    change (pc0 :: bv_unsigned rac :: tl) with ([pc0; bv_unsigned rac] ++ tl).
    eapply uwf_loop; [exact UWT| lia| pose proof (bv_unsigned_in_range 64 s0c) as R; unfold bv_modulus in R; cbn in R; lia| lia
                     | rewrite HTR, (hook_tr_ok _ _ _ _ _ H1); reflexivity|].
    exists (upd (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)) (Z.to_nat 1) rac).
    split; [exact ARR2|]. split; [rewrite !upd_length; exact LEN|].
    split. { change (Z.to_nat 1) with (length [pc0]). apply tb_prefix_snoc; [exact TB1| rewrite upd_length, LEN; cbn; lia]. }
    split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  Qed.
End UWF.


End CeilWrap.
(* [comment removed for export] *)
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
End RTW_unwind_loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
Import RTW_leaves_tiny.
Import RTW_leaves_thread.
Import RTW_unwind_loop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_kitL RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma uwt_len : forall m lo top pc0 prev f k tl, uwt m lo top pc0 prev f k tl -> k <= TRACE_MAX_LEN -> k + zlen tl <= TRACE_MAX_LEN.
Proof.
  intros m lo top pc0 prev f k tl U. induction U; intros Hk.
  - unfold zlen. cbn. lia.
  - unfold zlen. cbn. lia.
  - rewrite zlen_app. destruct (bv_unsigned pc1 =? pc0); unfold zlen in *; cbn [length app] in *; lia.
Qed.

(* [comment removed for export] *)
Lemma stk_of_wr_high : forall m a n, wr_at asegs m a n -> AIMG_HI <= a -> stk asegs m a (a + n).
Proof.
  intros m a n (H0 & H1 & HW) Ha. split; [lia|]. split; [lia|]. intros x Hx.
  pose proof (HW (x - a) ltac:(lia)) as W. replace (a + (x - a)) with x in W by lia. split; [exact W|].
  assert (NS : noseg asegs (wa x)) by (apply noseg_Z; lia).
  pose proof (wview_noseg_some m (wa x) NS W) as Hs. unfold mrd. destruct (m (wa x)) as [b|]; [exists b; reflexivity| congruence].
Qed.

Lemma stk_of_wr_mono : forall m m' a n, wr_at asegs m a n -> wmono asegs m m' -> AIMG_HI <= a -> stk asegs m' a (a + n).
Proof. intros m m' a n WR WM Ha. eapply stk_wmono_noseg; [apply stk_of_wr_high; [exact WR| exact Ha]| exact WM| exact Ha]. Qed.

Lemma c8_of_stk : forall m a, stk asegs m a (a + 8) -> exists v : word, rw_cells asegs m a [C8 v].
Proof. intros m a ST. (nelim ST 3%nat; intros H0 H1 H). apply c8_of_bytes; [lia| lia|]. intros i Hi. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma u64arr_of_stk : forall n m a, stk asegs m a (a + 8 * Z.of_nat n) -> exists ws, length ws = n /\ u64arr asegs m a ws.
Proof.
  induction n as [|n IH]; intros m a ST.
  - exists []. split; [reflexivity|]. (nelim ST 3%nat; intros H0 H1 _). split; [split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia|].
    split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (stk_split asegs m a (a + 8) (a + 8 * Z.of_nat (S n)) ST ltac:(lia)) as [ST1 ST2].
    destruct (c8_of_bytes m a ltac:((nelim ST 3%nat; intros ? ? ?); lia) ltac:((nelim ST 3%nat; intros ? ? ?); lia)
                ltac:(intros i Hi; (nelim ST1 3%nat; intros _ _ H); apply H; lia)) as [v Hv].
    replace (a + 8 * Z.of_nat (S n)) with ((a + 8) + 8 * Z.of_nat n) in ST2 by lia.
    (nelim (IH m (a + 8) ST2) 3%nat; intros ws Hlen Hws). exists (v :: ws). split; [cbn; lia|].
    destruct Hv as [[_ Hb] Hw]. destruct Hws as [Hb2 Hw2]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
    split.
    + cbn [u64s]. apply bytes_at_app. split; [exact Hb|]. rewrite length_le8. replace (a + Z.of_nat 8) with (a + 8) by lia. exact Hb2.
    + cbn [length]. replace (8 * Z.of_nat (S (length ws))) with (8 + 8 * Z.of_nat (length ws)) by lia.
      apply wr_at_app; [lia| lia|]. split. { cbn [cells_size Cells.csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw. } exact Hw2.
Qed.

(* [comment removed for export] *)
Lemma trace_cells_of_u64arr : forall m a ws tr, u64arr asegs m a ws -> tb_prefix ws tr -> (length tr <= length ws)%nat ->
  rw_cells asegs m a (trace_cells tr).
Proof.
  intros m a ws tr [HB HW] TB HL. unfold tb_prefix in TB.
  assert (E : u64s ws = u64s (map wz tr) ++ u64s (skipn (length tr) ws)).
  { rewrite <- (firstn_skipn (length tr) ws) at 1. rewrite u64s_app, TB. reflexivity. }
  rewrite E in HB. apply bytes_at_app in HB. destruct HB as [HB1 _].
  assert (CB_ : cells_bytes (trace_cells tr) = u64s (map wz tr)).
  { unfold trace_cells. clear. induction tr as [|x tr' IH]; [reflexivity|]. cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity. }
  assert (CS : cells_size (trace_cells tr) = (8 * length tr)%nat).
  { unfold trace_cells. clear. induction tr as [|x tr' IH]; [reflexivity|]. cbn [map cells_size Cells.csize length]. rewrite IH. lia. }
  split; [split|].
  - unfold trace_cells. clear. induction tr; cbn; tauto.
  - rewrite CB_. exact HB1.
  - rewrite CS. (nelim HW 3%nat; intros W0 W1 HW). split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
Qed.

(* [comment removed for export] *)
Lemma munch_drop_byte : forall W a m m', munch (W ++ [(a, a + 1)]) m m' -> 0 <= a < 2^64 -> m' (wa a) = m (wa a) -> munch W m m'.
Proof.
  intros W a m m' MU Ha E x Hx. destruct (Z.eq_dec (bv_unsigned x) a) as [EQ|NE].
  - replace x with (wa a); [exact E|]. apply bv_eq. rewrite wa_unsigned by lia. symmetry. exact EQ.
  - apply MU. clear -Hx NE. induction W as [|[lo hi] W IH]; cbn in *; [lia|]. destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma cell1_overlay : forall m a v, rw_cells asegs m a [C1 (zb v)] -> 0 <= a < 2^64 /\ (a < AIMG_LO \/ AIMG_HI <= a) -> m (wa a) = Some (zb v).   (* [comment removed for export] *)
Proof.
  intros m a v [[_ (H0 & H1 & HB)] _] [Ha0 Ha]. cbn [cells_bytes cbytes] in *. rewrite app_nil_r in *. cbn [length] in *.
  specialize (HB 0%nat ltac:(lia)). cbn [nth_error] in HB. rewrite Z.add_0_r in HB.
  unfold mrd in HB. destruct (m (wa a)) as [b|] eqn:E; [congruence|].
  exfalso.
  assert (NS : noseg asegs (wa a)) by (apply noseg_out; assumption). unfold seg_rom in HB.
  rewrite (memory_read_noseg asegs (wa a) 1 NS ltac:(lia)) in HB. discriminate.
Qed.


(* [comment removed for export] *)
Lemma sel_mask_true : forall a b x, a < b -> 0 <= x < 2^64 -> Z.land ((0 - Z.b2z (a <? b)) mod 18446744073709551616) x = x.
Proof.
  intros a b x Hab Hx. rewrite (proj2 (Z.ltb_lt a b) Hab). cbn [Z.b2z].
  change ((0 - 1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma unwind_cells : forall st m, RTREP st m ->
  (exists j1 j2 j3 j4 j5, rw_cells asegs m (st_t st)
      [C8 (wz (st_ctx st)); C8 (wz (ASTACK_TOP (st_sp0 st))); C8 (wz (ASTACK_BOTTOM (st_sp0 st))); CB 16 j1; C1 (zb 0); CB 7 j2; C8 j3; C8 j4; C8 j5; C8 (wz (st_fs st))])
  /\ rw_cells asegs m (st_t st + 3168) [C1 (zb 0)]
  /\ ro_cells asegs m 0xa1f60 [C8 (Z_to_bv 64 0x139d20)]
  /\ ro_cells asegs m 0x139d20 [C8 (Z_to_bv 64 4096)].
Proof.
  intros st m HR. pose proof (rr_thread st m HR) as HT. pose proof (rr_consts st m HR) as HC.
  destruct HT as (_ & (j1 & j2 & j3 & j4 & j5 & T2) & _ & T4 & _).
  (nelim HC 6%nat; intros _ _ _ _ K5 _).
  split; [exists j1, j2, j3, j4, j5; exact T2|].
  split; [unfold T_UNWINDING in T4; exact T4|].
  split; [apply (R_link_at m 0xa1f60 0x139d20 (rr_link st m HR)); vm_compute; reflexivity|].
  exact K5.
Qed.

Section UW.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (g : lghost)
            (st : rtstate) (S pc0 bp : Z) (rac s0c : word) (tl : list Z) (lo : Z).
  Hypothesis HRTS : RTS st m mo g.
  Hypothesis A0 : a0 = wz S. Hypothesis A1 : a1 = wz pc0. Hypothesis A2 : a2 = wz bp. Hypothesis A3 : a3 = wz 0.
  Hypothesis A4 : a4 = wz 1. Hypothesis A5 : a5 = wz TRACE_MAX_LEN. Hypothesis TP : tp = wz ATP.
  Hypothesis OBJ0 : rw_cells asegs m S [C8 (wz (S + 16)); C4 (wz 0); C4 (wz 0)].
  Hypothesis WR : wr_at asegs m S BST_SIZE.
  Hypothesis SPS : bv_unsigned sp <= S.
  Hypothesis SPB : bv_unsigned sp <= bp - 16.
  Hypothesis BPR : bp < 2^64.
  Hypothesis PCR : 0 <= pc0 < 2^64.
  Hypothesis REC0 : bytes_at asegs m (bp - 16) (le8 s0c ++ le8 rac).
  Hypothesis RAC1 : 4096 <= bv_unsigned rac. Hypothesis RAC2 : bv_unsigned rac <> pc0.
  Hypothesis UWT : hop1_ok (st_sp0 st) bp = true -> uwt m bp (ASTACK_TOP (st_sp0 st)) pc0 bp (bv_unsigned s0c) 2 tl.
  Hypothesis DISJ : S + BST_SIZE <= bp - 16 \/ ASTACK_TOP (st_sp0 st) <= S.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis HCEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AUNWIND_STACK.
  Hypothesis MI0 : mem_inv asegs m.

  Let tr := hook_tr pc0 (st_sp0 st) bp (bv_unsigned rac) tl.
  Let TOP := ASTACK_TOP (st_sp0 st).
  Let BOT := ASTACK_BOTTOM (st_sp0 st).

  Lemma unwind_walk :
    evt asegs (unwind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st S bp tr lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz AUNWIND_IMPL) fc None m (seg_rom asegs)).
  Proof.
    (nelimp HRTS 4%nat; intros HR WF HM HG).
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    (* [comment removed for export] *)
    pose proof REC0 as RECb. change (bytes_at asegs m (bp - 16) (le8 s0c ++ le8 rac)) with (id (bytes_at asegs m (bp - 16) (le8 s0c ++ le8 rac))) in RECb.
    clear REC0.
    pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
    pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0.
    assert (HTB : 0 <= BOT /\ BOT + 0x800000 = TOP /\ TOP + 16 < 2^64 /\ 4096 <= TOP).
    { subst BOT TOP. unfold ASTACK_BOTTOM, ASTACK_TOP, roundup. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_bound _ _ _ _ OBJ0) as SB0. (nelimp WR 3%nat; intros WR0 WR1 WRi).
    pose proof (munch_refl (W S lo (st_t st + 3168) (bv_unsigned sp) tr) m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (S + 8, S + 12)] m) as MUhi.
    unfold W in MU.
    destruct (unwind_cells st m HR) as ((j1 & j2 & j3 & j4 & j5 & TPG) & UNW & GOTC & PSC). cbv beta delta [zb wz] in TPG, UNW.
    unfold AUNWIND_IMPL, AUNWIND_STACK, BST_SIZE, TRACE_MAX_LEN in *. subst a0 a1 a2 a3 a4 a5 tp. leaf_prep.
    carve_frame 80%nat ST.
    do 11 lstep. (* [comment removed for export] *)
    do 6 lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    pose proof HR as HR1. rtrep_high HR1 WF MUhi WM.
    call asan_inited_proof; [exact HR1| exact MI| discriminate| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
    after_call.
    assert (E80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    rewrite E80 in *.
    lstep. if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    clear HR1. pose proof HR as HR1. rtrep_high HR1 WF MUhi WM.
    call get_current_thread_proof; [exact HR1| exact WF| exact MI| reflexivity| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
    after_call. rewrite E80 in *. clear HR1.
    lstep. if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    clear MUhi.
    lstep. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep. fl. lstep. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    rewrite sel_mask_true by lia.
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. fl. lstep. lstep. if_lia.
    lstep. lstep. lstep. lstep. lstep.
    rewrite sel_mask_true by lia.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) lstep. if_lia. (* [comment removed for export] *)
    do 8 lstep.
    lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 8 lstep. (* [comment removed for export] *)
    do 4 lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    setreg 6 (Z_to_bv 64 bp) ltac:(f_equal; change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64);
                                     rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with WMc : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_wr_mono m mm S 2064 (conj WR0 (conj WR1 WRi)) WMc ltac:(unfold AIMG_HI; lia)) as SST;
      destruct (c8_of_stk mm (S + 2056) ltac:(eapply stk_sub; [exact SST| lia| lia])) as [tfb0 TFB];
      (nelim (u64arr_of_stk 255 mm (S + 16) ltac:(eapply stk_sub; [exact SST| lia| cbn; lia])) 3%nat; intros ws LEN ARR);
      clear SST end.
    lstep. (* [comment removed for export] *)
    lstep. if_lia. lstep. if_lia. lstep. if_lia. (* [comment removed for export] *)
    do 5 lstep. do 7 lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -80).
    assert (TRL : zlen tr <= 30).
    { subst tr. unfold hook_tr. destruct (Sumbool.sumbool_of_bool (hop1_ok (st_sp0 st) bp)) as [E|E]; rewrite E.
      - pose proof (uwt_len _ _ _ _ _ _ _ _ (UWT E) ltac:(unfold TRACE_MAX_LEN; lia)) as L. unfold TRACE_MAX_LEN in L.
        rewrite !zlen_cons. lia.
      - unfold zlen. cbn. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl (W S lo (st_t st + 3168) (bv_unsigned sp + -80) tr) mm) as MU1;
      pose proof (wmono_refl asegs mm) as WM1;
      assert (AG1 : agree_on (bp - 16) TOP m mm)
        by (intros a Ha; unfold mrd; rewrite (MU (wa a)); [reflexivity|]; rewrite wa_unsigned by lia; cbn; subst TOP; lia)
    end.
    eapply evt_cut.
    { eapply (uwf_entry _ _ gp _ _ _ s9 s10 s11 F fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ S pc0 bp TOP lo (st_t st + 3168) (bv_unsigned sp + -80) tr);
        [ | | | | exact TRL | exact AG1 | reflexivity | | exact RECb | split; [exact RAC1| exact RAC2] | exact UWT | reflexivity
        | exact ARR | exact LEN | exact OBJ0 | exact TFB | exact UNW | exact GOTC | exact PSC | exact MI | exact MU1 | exact WM1 | ].
      - rewrite E80. unfold BST_SIZE. lia.
      - subst TOP. lia.
      - rewrite E80. lia.
      - idtac. unfold AIMG_LO, AIMG_HI. lia.
      - subst BOT. lia.
      - rewrite E80. exact ST. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 18%nat; intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' -> UP).
    (nelim UP 14%nat; intros ws' k' ARR' LEN' TB' K' HK' OBJ' TFB' UNW' MI' MU' WM' ST').
    unfold W in MU'. rewrite E80 in ST'.
    (* [comment removed for export] *)
    lazymatch type of MU' with munch ?W1 ?ma ?mb =>
      lazymatch type of MU with munch ?W0 _ _ =>
      apply (rw_cells_transport asegs W1 ma mb) in FR; [| exact MU'| exact WM'| cbn; lia];
      apply (munch_weaken W1 W0 ma mb) in MU'; [| unfold sub_fp; cbn; intros; lia];
      apply (munch_trans W0 m ma mb MU) in MU' end end.
    apply (wmono_trans asegs m _ _ WM) in WM'.
    clear MI ST TFB ARR LEN UNW OBJ0 GOTC PSC TPG MU WM MU1 WM1 AG1. rename MI' into MI. rename ST' into ST.
    replace (ret_pc (Z_to_bv 64 377676)) with (Z_to_bv 64 377676) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbv beta delta [wz zb] in OBJ', TFB', UNW'.
    lstep. (* [comment removed for export] *)
    do 12 lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold unwind_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI|]. split; [exact ST|].
    split; [| split; [| split]].
    - (* [comment removed for export] *)
      assert (MUd : munch [(lo, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 16 + 8 * zlen tr); (S + 2056, S + 2064)] m m2).
      { eapply munch_drop_byte; [exact MU'| lia|].
        rewrite (cell1_overlay m2 _ 0 UNW' ltac:(unfold AIMG_LO, AIMG_HI; lia)).
        pose proof (rr_thread st m HR) as HT. (nelim HT 5%nat; intros _ _ _ T4 _). unfold T_UNWINDING in T4.
        rewrite (cell1_overlay m _ 0 T4 ltac:(unfold AIMG_LO, AIMG_HI; lia)). reflexivity. }
      eapply (RTREP_high st _ m m2 WF); [| exact MUd| exact WM'| exact HR].
      repeat (constructor; [cbn; lia|]). constructor.
    - subst k'. exact (rw_cells_mid m2 S [C8 (Z_to_bv 64 (S + 16))] [C4 (Z_to_bv 64 (zlen tr))] [C4 (Z_to_bv 64 0)] OBJ').
    - eapply trace_cells_of_u64arr; [exact ARR'| exact TB'| rewrite LEN'; unfold zlen in TRL; lia].
    - exact TFB'.
  Qed.
End UW.

Theorem unwind_proof : unwind_spec.
Proof.
  unfold unwind_spec. intros until lo. intros HRTS A0 A1 A2 A3 A4 A5 TP OBJ WR SPS SPB BPR PCR REC RAC1 RAC2 UWT DISJ ST HCEIL LO MI.
  eapply unwind_walk; eassumption.
Qed.


End CeilWrap.
