(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from R/RDrv_kio.v and R/RYajl_iface.v: rz_fprintf_diag, rz_exit and rz_evt restated over BudgetWit.RzbCfg.rzb_cfg, with the proofs that the stdio trees they run have no allocation node. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes NodesCfg Decode Exec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg TrzLeafCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad StdioBase Stdio Driver RawAlloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_pad RF_stdio_lib RF_syscalls Stdio_iface RF_printf_iface RF_vfprintf RF_fwritex_stderr RF_fwritex_stdout RF_stdio_flush RF_fwrite RF_fprintf RF_vfprintf_stdout RF_stdio_exit R_Exit Printf_model.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RDrv_kio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BudgetWit Require Import RzbCfg ImplRzb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** * The stdio steps of the usage path, over [rzb_cfg]

    The driver's usage path reaches the kernel through two library calls:
    [fprintf(stderr, ...)] for the usage line ([RDrv_kio.rz_fprintf_diag]) and
    [exit(2)] ([RDrv_kio.rz_exit]), each a machine-level [impl] proof of a stdio
    interaction tree given to the [impl]-to-[realizes_cfg] bridge.  This file
    restates the two over [rzb_cfg] through [ImplRzb.impl_trz_rzb_leaf], with
    the released proof text, and proves that their trees have no allocation
    node: [stderr_fprintf] makes [writev] (66) calls only, and the exit tree an
    [ioctl] (29) and [writev] calls to flush stdout, then [exit] (93 or 94).
    [rzb_evt] is [RYajl_iface.rz_evt] over [rzb_cfg]. *)

Local Notation trzN := (trz node (nstep_cfg acfg) nexit minv nsafe).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** ** The stdio trees have no allocation node *)
Section TFS.
Context {St : Type}.

Lemma tfree_writev_loop : forall fuel fd iovs (s : St), tfree (writev_loop fuel fd iovs s).
Proof.
  induction fuel as [|fuel IH]; intros fd iovs s; cbn [writev_loop];
    (apply tfree_mbind; [apply tfree_msys; reflexivity|]); intros k s'; cbv beta;
    (destruct (k =? zlength (zconcat iovs)); [apply tfree_mret|]).
  - apply tfree_munr.
  - apply IH.
Qed.

Lemma tfree_stdio_writev : forall fd buf l (s : St), tfree (stdio_writev fd buf l s).
Proof.
  intros fd buf l s. unfold stdio_writev.
  destruct (WRITEV_MAX <? zlength buf + zlength l); [apply tfree_munr | apply tfree_writev_loop].
Qed.

Lemma tfree_stderr_pieces : forall ps buf (s : St), tfree (stderr_pieces buf ps s).
Proof.
  induction ps as [|p ps IH]; intros buf s; cbn [stderr_pieces].
  - apply tfree_mret.
  - destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p).
    + apply tfree_mbind; [apply tfree_stdio_writev|]. intros a s'. cbv beta. apply IH.
    + apply IH.
Qed.

Lemma tfree_stderr_fprintf : forall ps (s : St), tfree (stderr_fprintf ps s).
Proof.
  intros ps s. unfold stderr_fprintf.
  apply tfree_mbind; [apply tfree_stderr_pieces|]. intros buf s'. cbv beta. apply tfree_stdio_writev.
Qed.

Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.

Lemma tfree_rd_so : forall (s : St), tfree (rd_so get_so s).
Proof.
  intros s. unfold rd_so. apply tfree_mbind; [apply tfree_mget|]. intros a s'. cbv beta. apply tfree_mret.
Qed.

Lemma tfree_upd_so : forall f (s : St), tfree (upd_so get_so set_so f s).
Proof. intros f s. unfold upd_so. apply tfree_mupd. Qed.

Lemma tfree_stdout_stdio_write : forall l (s : St), tfree (stdout_stdio_write get_so set_so l s).
Proof.
  intros l s. unfold stdout_stdio_write.
  apply tfree_mbind; [apply tfree_rd_so|]. intros so s'. cbv beta.
  apply tfree_mbind; [apply tfree_stdio_writev|]. intros a s''. cbv beta. apply tfree_upd_so.
Qed.

Lemma tfree_stdout_writefn : forall l (s : St), tfree (stdout_writefn get_so set_so l s).
Proof.
  intros l s. unfold stdout_writefn.
  apply tfree_mbind; [apply tfree_rd_so|]. intros so s'. cbv beta.
  apply tfree_mbind; [| intros a s''; cbv beta; apply tfree_stdout_stdio_write].
  destruct (so_first so); [| apply tfree_mret].
  apply tfree_mbind; [apply tfree_upd_so|]. intros a s2. cbv beta.
  apply tfree_mbind; [apply tfree_msys; reflexivity|]. intros r s3. cbv beta.
  (* Both branches compute to a [Ret] tree, on which [tfree] is [True]; an [apply]
     here would unify through that reduction and leave its arguments open. *)
  destruct r; exact I.
Qed.

Lemma tfree_stdout_exit_flush : forall (s : St), tfree (stdout_exit_flush get_so set_so s).
Proof.
  intros s. unfold stdout_exit_flush.
  apply tfree_mbind; [apply tfree_rd_so|]. intros so s'. cbv beta.
  destruct (0 <? zlength (so_buf so)); [apply tfree_stdout_writefn | apply tfree_mret].
Qed.
End TFS.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Lemma tfree_exit_model : forall code (s : PState),
  tfree (Driver.exit_model (io_S ps_so set_so_ps) code s).
Proof.
  intros code s. unfold Driver.exit_model.
  change (io_exit (io_S ps_so set_so_ps)) with (stdout_exit_flush ps_so set_so_ps).
  apply tfree_mbind; [apply tfree_stdout_exit_flush|]. intros a s'. cbv beta.
  apply tfree_msys. reflexivity.
Qed.

(** [RDrv_kio.impl_trz_realizes_leafC] over [rzb_cfg]. *)
Lemma impl_trz_rzb_leafC : forall {R} (t : itree node R) Q ms mo (K : R -> Model -> TSet) T,
  impl rsegs (at_node rsegs) t Q ms ->
  trzN t mo K T ->
  tfree t ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> leaf t mo r mo' -> m_halted mo' = None -> minv mo' ->
     rzb_cfg acfg rsegs (mkCfg ms' mo') (K r mo')) ->
  rzb_cfg acfg rsegs (mkCfg ms mo) T.
Proof.
  intros R t Q ms mo K T IM TR TF Hh Hmi HK.
  apply (impl_trz_rzb_leaf acfg rsegs acfg_off t Q ms mo K T IM TR TF Hh Hmi).
  intros r ms' mo' HQ L. apply HK; [exact HQ | apply leafC_of_leaf; exact L].
Qed.

(** [RYajl_iface.rz_evt] over [rzb_cfg]. *)
Lemma rzb_evt : forall (Q : machine_state -> Prop) ms mo (K : TSet),
  evt rsegs Q ms -> m_halted mo = None -> m_vm_lazy mo = [] ->
  (forall ms', Q ms' -> rzb_cfg acfg rsegs (mkCfg ms' mo) K) ->
  rzb_cfg acfg rsegs (mkCfg ms mo) K.
Proof.
  intros Q ms mo K (ms' & Hs & HQ) Hh Hl HK'.
  exact (rzb_msteps_lib_cfg acfg rsegs ms ms' mo K Hh Hl Hs (HK' ms' HQ)).
Qed.

(** [RDrv_kio.rz_fprintf_diag] over [rzb_cfg]. *)
Lemma rzb_fprintf_diag :
  forall (d : diag_msg) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (st : PState) (lo : Z) (canary : word) (K : TSet),
  K [] -> minv mo -> m_halted mo = None ->
  stderr_wfile m ->
  a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FPRINTF_DEPTH -> GLOBALS_TOP <= lo ->
  bv_unsigned sp < 0x800000000000 ->
  ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
  Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) (diag_pieces d) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
     munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm0 fc' ->
     (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
     stk rsegs m' lo (bv_unsigned sp) -> stderr_wfile m' -> ssp_cells m' canary ->
     rzb_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') Ft (ret_pc ra) fc' None m' (seg_rom rsegs)) mo) K) ->
  rzb_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19ba8) fc None m (seg_rom rsegs)) mo)
           (ShapeAlg.t_emit (Wz 2 (concat (diag_pieces d))) K).
Proof.
  intros until K. intros HK Hmi Hh SE A0 DA ST LO GT SP SSP MI FRM HW CONT.
  pose proof (fprintf_diag_proof PState d ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m st lo canary fwritex_stderr_proof stdio_write_flush_proof SE A0 DA ST LO GT SP SSP MI FRM) as IM.
  unfold implM in IM.
  assert (ED : s_diag (St:=PState) d = stderr_fprintf (diag_pieces d)).
  { destruct d; cbn [diag_args] in DA; lazymatch type of DA with False => destruct DA | _ => reflexivity end. }
  rewrite ED in IM.
  apply (impl_trz_rzb_leafC (stderr_fprintf (diag_pieces d) st) _ _ mo (fun _ _ => K) _ IM
           (trz_stderr_fprintf (diag_pieces d) st mo (fun _ _ => K) (conj Hmi Hh) HW (fun _ _ => HK))
           (tfree_stderr_fprintf (diag_pieces d) st) Hh Hmi).
  intros r ms' mo' HQ L _ _. apply (leaf_stderr_fprintf_ok (diag_pieces d) st) in L as [-> ->]; [| exact HW].
  unfold epost in HQ. cbn [fst snd] in HQ. unfold fprintf_diag_post in HQ.
  destruct HQ as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FEQ & ST' & SE' & SSP' & _).
  exact (CONT u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m' MU WM MI' FRM' FEQ ST' SE' SSP').
Qed.

(** [RDrv_kio.rz_exit] over [rzb_cfg]. *)
Lemma rzb_exit : forall (s : PState)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word) (reg : bool) (p3 p4 FJ AJ : list byte),
    stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m 0x34c78 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells rsegs m 0x54fa8 [C4 z64] ->
    rw_cells rsegs m 0x23930 [C8 (Z_to_bv 64 0x23898); C8 (Z_to_bv 64 0x23890)] ->
    rw_cells rsegs m 0x23890 [C8 (Z_to_bv 64 0x13444)] ->
    rw_cells rsegs m 0x24c38 [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m 0x238d8 [C8 (Z_to_bv 64 0x174b0); C8 z64] ->
    rw_cells rsegs m 0x24940 [C8 (Z_to_bv 64 0x24940)] ->
    rw_cells rsegs m 0x54d88 (RX_atexit.atx_cells reg p3 p4 FJ AJ) ->
    rw_cells rsegs m 0x34c44 [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m 0x54fd0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells rsegs m 0x55400 [C8 z64] -> rw_cells rsegs m 0x553f0 [C8 z64] ->
    rw_cells rsegs m 0x24bd8 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells rsegs m 0x24ae8 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (ps_so s) -> stderr_file m ->
    rw_cells rsegs m 0x23928 [C8 (Z_to_bv 64 0x54fb0)] -> rw_cells rsegs m 0x54fb0 [C8 guard] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 0x34d40 -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x56000 <= lo)%Z ->
    (bv_unsigned sp < 0x800000000000)%Z ->
    minv mo -> m_halted mo = None -> zlength (so_buf (ps_so s)) <= STDOUT_BUFSIZ ->
    rzb_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 0x175cc) fc None m (seg_rom rsegs)) mo)
             (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (ps_so s))))
                     (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
Proof.
  intros until AJ. intros ST TDa EXL GF FA FIN GCX DSO ATX FLG LCH OFL SIN SOU SEU SOF SEF GG GU MI TP A0 Ht LO LOLO SPTS Hmi Hh Hb.
  pose proof (R_Exit.exit_spec ps_so set_so_ps stdio_exit_proof_ps s (fun _ _ _ => False)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo code t
                td0 td1 td2 td3 guard cdt thr sec tm1 reg p3 p4 FJ AJ
                ST TDa EXL GF FA FIN GCX DSO ATX FLG LCH OFL SIN SOU SEU SOF SEF GG GU MI TP A0 Ht LO LOLO SPTS) as IM.
  unfold implM in IM.
  apply (impl_trz_rzb_leafC (Driver.exit_model (io_S ps_so set_so_ps) code s) _ _ mo (fun _ _ => t_nil) _ IM);
    [| apply tfree_exit_model | exact Hh | exact Hmi |].
  - unfold Driver.exit_model. change (io_exit (io_S ps_so set_so_ps)) with (stdout_exit_flush ps_so set_so_ps).
    apply (trz_stdout_exit_flush_k ps_so set_so_ps ps_get_set ps_set_set (fun _ => msys (NExit code) dec_exit) s mo _ _ (conj Hmi Hh) Hb).
    + apply trz_exit. exact Hmi.
    + apply t_emit_has_nil.
    + exact ps_set_get.
  - intros r ms' mo' _ L _ _. exfalso. exact (leaf_exit_model_none code s mo r mo' Hb L).
Qed.
End RC__1.
