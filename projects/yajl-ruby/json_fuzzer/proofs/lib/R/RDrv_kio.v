(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation trzN := (trz node (nstep_cfg acfg) nexit minv nsafe).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma leafC_of_leaf : forall {R} (t : itree node R) mo r mo',
  ImplRzCfg.leaf (nstep_cfg acfg) t mo r mo' -> leaf t mo r mo'.
Proof.
  intros R t mo r mo' H. induction H; [constructor | econstructor; eassumption].
Qed.

Lemma impl_trz_realizes_leafC : forall {R} (t : itree node R) Q ms mo (K : R -> Model -> TSet) T,
  impl rsegs (at_node rsegs) t Q ms ->
  trzN t mo K T ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> leaf t mo r mo' -> m_halted mo' = None -> minv mo' ->
     realizes_cfg acfg rsegs (mkCfg ms' mo') (K r mo')) ->
  realizes_cfg acfg rsegs (mkCfg ms mo) T.
Proof.
  intros R t Q ms mo K T IM TR Hh Hmi HK.
  apply (impl_trz_realizes_leaf_cfg acfg node rsegs (at_node rsegs) (nstep_cfg acfg) nexit minv nsafe (nodes_sound_cfg acfg rsegs)
           t Q ms mo K T IM TR Hh Hmi).
  intros r ms' mo' HQ L. apply HK; [exact HQ | apply leafC_of_leaf; exact L].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_msys_of_enode : forall {St A} (n : node) (dec : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
  impl rsegs (at_node rsegs) (enode n dec) (epost Q) ms ->
  impl rsegs (at_node rsegs) (msys n dec s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
  intros St A n dec Q s ms H. unfold msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (dec rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

(* [comment removed for export] *)
Lemma rz_enode : forall {A} n (dec : resp -> option A) (Q : A -> machine_state -> Prop) ms mo (R : A -> Model -> Prop) (K : TSet),
  impl rsegs (at_node rsegs) (enode n dec) (epost Q) ms ->
  minv mo -> m_halted mo = None -> nsafe n mo -> K [] ->
  (exists rsp mo1 evs, nstep_cfg acfg n mo rsp mo1 evs) ->
  (forall rsp mo1 evs, nstep_cfg acfg n mo rsp mo1 evs -> evs = [] /\ exists a, dec rsp = Some a /\ R a mo1) ->
  (forall code mo1, ~ nexit n mo code mo1) ->
  (forall a mo1 ms' rsp evs, nstep_cfg acfg n mo rsp mo1 evs -> R a mo1 -> Q a ms' -> minv mo1 -> m_halted mo1 = None -> realizes_cfg acfg rsegs (mkCfg ms' mo1) K) ->
  realizes_cfg acfg rsegs (mkCfg ms mo) K.
Proof.
  intros A n dec Q ms mo R K IM Hmi Hh Hsafe HK Hex Hall Hnx CONT.
  apply (impl_msys_of_enode n dec Q tt ms) in IM.
  apply (impl_trz_realizes_leafC (msys n dec tt) _ ms mo (fun _ _ => K) K IM); [| exact Hh | exact Hmi |].
  - apply trz_msys_silent; try assumption.
    intros rsp mo1 evs H. destruct (Hall _ _ _ H) as (-> & a & D & _). split; [reflexivity | apply t_eq_refl].
  - intros r ms' mo1 HQ L Hh1 Hmi1. apply leaf_msys in L as (rsp & evs & Hst & ->).
    destruct (Hall _ _ _ Hst) as (_ & a & D & HR). rewrite D in HQ. unfold epost in HQ. cbn [fst snd] in HQ. destruct HQ as [HQ _].
    exact (CONT a mo1 ms' rsp evs Hst HR HQ Hmi1 Hh1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_read : forall fd buf count (Q : read_ans -> machine_state -> Prop) ms mo a mo' (K : TSet),
  impl rsegs (at_node rsegs) (enode (NRead fd buf count) (dec_read buf count)) (epost Q) ms ->
  minv mo -> m_halted mo = None -> 0 < count < 2^64 -> K [] ->
  read_out fd buf count mo = Some (a, mo') ->
  (forall ms' rsp evs, nstep (NRead fd buf count) mo rsp mo' evs -> Q a ms' -> minv mo' -> m_halted mo' = None -> realizes_cfg acfg rsegs (mkCfg ms' mo') K) ->
  realizes_cfg acfg rsegs (mkCfg ms mo) K.
Proof.
  intros fd buf count Q ms mo a mo' K IM Hmi Hh Hc HK RO CONT.
  apply (rz_enode _ _ Q ms mo (fun a1 mo1 => a1 = a /\ mo1 = mo') K IM Hmi Hh I HK).
  - unfold read_out in RO. cbn [nstep_cfg node_off alloc_only_cfg sc_alloc sc_fs negb nstep].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|i w|drd dwr| ]|] eqn:E; try discriminate.
    + destruct (fs_lookup (m_fs mo) p) as [data|] eqn:F; [|discriminate].
      eexists _, _, []. split; [reflexivity|]. split; reflexivity.
    + exists (efferr EISDIR), mo, []. auto.
    + exists (efferr EBADF), mo, []. auto.
  - intros rsp mo1 evs H. assert (Hc' : 0 <= count < 2^64) by lia.
    destruct (nstep_dec_read _ _ _ _ _ _ _ Hc' H) as (-> & a1 & D & Ha). split; [reflexivity|]. exists a1. split; [exact D|].
    unfold read_out in RO.
    destruct a1 as [e|bs].
    + destruct Ha as [-> [[-> He] | [-> He]]]; rewrite He in RO; inversion RO; subst; auto.
    + destruct Ha as (p & off & data & E & F & -> & ->). rewrite E, F in RO. inversion RO; subst; auto.
  - intros code mo1 H. exact H.
  - intros a1 mo1 ms' rsp evs Hst [-> ->] HQ Hmi1 Hh1. exact (CONT ms' rsp evs Hst HQ Hmi1 Hh1).
Qed.

Lemma rz_close : forall fd (Q : sret -> machine_state -> Prop) ms mo (K : TSet),
  impl rsegs (at_node rsegs) (enode (NClose fd) dec_close) (epost Q) ms ->
  minv mo -> m_halted mo = None -> 3 <= fd < 2^32 -> K [] ->
  (forall ms' rsp evs, nstep (NClose fd) mo rsp (snd (close_out fd mo)) evs ->
     Q (fst (close_out fd mo)) ms' -> minv (snd (close_out fd mo)) -> m_halted (snd (close_out fd mo)) = None ->
     realizes_cfg acfg rsegs (mkCfg ms' (snd (close_out fd mo))) K) ->
  realizes_cfg acfg rsegs (mkCfg ms mo) K.
Proof.
  intros fd Q ms mo K IM Hmi Hh Hfd HK CONT.
  apply (rz_enode _ _ Q ms mo (fun a1 mo1 => a1 = fst (close_out fd mo) /\ mo1 = snd (close_out fd mo)) K IM Hmi Hh I HK).
  - unfold close_out. cbn [nstep_cfg node_off alloc_only_cfg sc_alloc sc_fs negb nstep].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:E.
    + exists (eff0 (Z_to_bv 64 0)), (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo), []. repeat split; auto; lia.
    + exists (efferr EBADF), mo, []. repeat split; auto; lia.
  - intros rsp mo1 evs H. destruct (nstep_dec_close _ _ _ _ _ H) as (-> & a & D & Ha). split; [reflexivity|]. exists a. split; [exact D|].
    unfold close_out. destruct a as [e|v].
    + destruct Ha as (-> & -> & E). rewrite E. auto.
    + destruct Ha as (-> & E & ->). destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); [auto | exfalso; apply E; reflexivity].
  - intros code mo1 H. exact H.
  - intros a1 mo1 ms' rsp evs Hst [-> ->] HQ Hmi1 Hh1. exact (CONT ms' rsp evs Hst HQ Hmi1 Hh1).
Qed.

Lemma rz_open_errno : forall path e (Q : sret -> machine_state -> Prop) ms mo (K : TSet),
  impl rsegs (at_node rsegs) (enode (NOpen path) dec_open) (epost Q) ms ->
  minv mo -> m_halted mo = None -> K [] ->
  open_classify path mo = OcErrno e ->
  (forall ms', Q (SErr e) ms' -> realizes_cfg acfg rsegs (mkCfg ms' mo) K) ->
  realizes_cfg acfg rsegs (mkCfg ms mo) K.
Proof.
  intros path e Q ms mo K IM Hmi Hh HK HC CONT.
  assert (He : 1 <= e <= 4095).
  { unfold open_classify in HC. destruct (path_max <=? length path)%nat. { inversion HC. unfold ENAMETOOLONG; lia. }
    destruct path; [inversion HC; unfold ENOENT; lia|]. destruct (path_is_dirref _); [discriminate|].
    destruct (fs_lookup _ _); [discriminate|]. inversion HC. unfold ENOENT; lia. }
  apply (rz_enode _ _ Q ms mo (fun a1 mo1 => a1 = SErr e /\ mo1 = mo) K IM Hmi Hh I HK).
  - exists (efferr e), mo, []. apply nstep_open_iff. rewrite HC. auto.
  - intros rsp mo1 evs H. apply nstep_open_iff in H. rewrite HC in H. destruct H as (-> & -> & ->).
    split; [reflexivity|]. exists (SErr e). unfold dec_open. rewrite dec_plain_err by exact He. auto.
  - intros code mo1 H. exact H.
  - intros a1 mo1 ms' rsp evs _ [-> ->] HQ _ _. exact (CONT ms' HQ).
Qed.

Lemma rz_open_may : forall path ent (Q : sret -> machine_state -> Prop) ms mo (KA KB : TSet),
  impl rsegs (at_node rsegs) (enode (NOpen path) dec_open) (epost Q) ms ->
  minv mo -> m_halted mo = None -> KA [] -> KB [] ->
  open_classify path mo = OcMay ent ->
  let fd := alloc_fd (m_fds mo) in
  fd_lookup (m_fds mo) fd = None -> 3 <= bv_unsigned fd <= 4096 ->
  (forall e ms', In e openat_errnos -> Q (SErr e) ms' -> realizes_cfg acfg rsegs (mkCfg ms' mo) KA) ->
  (forall ms' rsp evs, nstep (NOpen path) mo rsp (with_fds (fd_insert (m_fds mo) fd ent) mo) evs ->
     Q (SVal (bv_unsigned fd)) ms' -> minv (with_fds (fd_insert (m_fds mo) fd ent) mo) ->
     realizes_cfg acfg rsegs (mkCfg ms' (with_fds (fd_insert (m_fds mo) fd ent) mo)) KB) ->
  realizes_cfg acfg rsegs (mkCfg ms mo) (t_alt2 KA KB).
Proof.
  intros path ent Q ms mo KA KB IM Hmi Hh HKA HKB HC fd Hfree Hfd CA CB.
  apply (impl_msys_of_enode (NOpen path) dec_open Q tt ms) in IM.
  apply (impl_trz_realizes_leafC (msys (NOpen path) dec_open tt) _ ms mo
           (fun r mo1 => match r with
                         | Ok (SErr _, _) => KA
                         | Ok (SVal _, _) => KB
                         | Unr => t_nil
                         end) (t_alt2 KA KB) IM); [| exact Hh | exact Hmi |].
  - apply (trz_open_may path ent tt mo _ KA KB Hmi HC Hfree Hfd); [intros; apply t_eq_refl | apply t_eq_refl | exact HKA | exact HKB].
  - intros r ms' mo1 HQ L Hh1 Hmi1. apply leaf_msys in L as (rsp & evs & Hst & ->). pose proof Hst as Hst0.
    apply nstep_open_iff in Hst. rewrite HC in Hst. destruct Hst as [-> [(e & He & -> & ->) | (_ & -> & ->)]].
    + unfold dec_open in HQ |- *. rewrite dec_plain_err in HQ |- * by (apply openat_errnos_range; exact He).
      unfold epost in HQ. cbn [fst snd] in HQ. destruct HQ as [HQ _]. exact (CA e ms' He HQ).
    + fold fd in HQ |- *.
      assert (DV : dec_open (eff0 fd) = Some (SVal (bv_unsigned fd))).
      { unfold dec_open. rewrite <- (Z_to_bv_bv_unsigned fd) at 1.
        apply dec_plain_val; [lia | apply andb_true_intro; split; apply Z.leb_le; lia]. }
      rewrite DV in HQ. rewrite DV.
      unfold epost in HQ. cbn [fst snd] in HQ. destruct HQ as [HQ _]. exact (CB ms' _ _ Hst0 HQ Hmi1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ps_get_set : forall v s, ps_so (set_so_ps v s) = v. Proof. intros v [? ? ? ?]; reflexivity. Qed.
Lemma ps_set_set : forall w v s, set_so_ps v (set_so_ps w s) = set_so_ps v s. Proof. intros w v [? ? ? ?]; reflexivity. Qed.
Lemma ps_set_get : forall s, set_so_ps (ps_so s) s = s. Proof. intros [? ? ? ?]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_fwrite_diag :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (st : PState) (lo : Z) (canary : word) (s : list Z) (K : TSet),
  K [] -> minv mo -> m_halted mo = None ->
  stderr_wfile0 m ->
  bytes_at rsegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
  a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_DEPTH -> GLOBALS_TOP <= lo ->
  bv_unsigned sp < 0x800000000000 ->
  (bv_unsigned a0 + zlength s <= lo \/ (bv_unsigned sp <= bv_unsigned a0 /\ bv_unsigned a0 + zlength s <= 0x800000000000)) ->
  (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
  ssp_cells m canary -> mem_inv rsegs m ->
  zlength s <= WRITEV_MAX ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
     munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     stk rsegs m' lo (bv_unsigned sp) -> stderr_wfile0 m' -> ssp_cells m' canary ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo) K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19d44) fc None m (seg_rom rsegs)) mo)
           (ShapeAlg.t_emit (Wz 2 s) K).
Proof.
  intros until K. intros HK Hmi Hh SE BA FA LEN A1 A2 A3 ST LO GT SPTS D1 D2 SSP MI HW CONT.
  pose proof (fwrite_diag_proof (St:=PState) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m st lo canary s towrite_proof SE BA FA LEN A1 A2 A3 ST LO GT SPTS D1 D2 SSP MI) as IM.
  unfold implM in IM.
  apply (impl_trz_realizes_leafC (stderr_fwrite s st) _ _ mo (fun _ _ => K) _ IM
           (trz_stderr_fwrite s st mo (fun _ _ => K) Hmi HW HK) Hh Hmi).
  intros r ms' mo' HQ L _ _. apply (leaf_stderr_fwrite_ok s st) in L as [-> ->]; [| exact HW].
  unfold epost in HQ. cbn [fst snd] in HQ. unfold fwrite_diag_post in HQ.
  destruct HQ as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & SE' & SSP' & _).
  exact (CONT u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' MU WM MI' ST' SE' SSP').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition diag_pieces (d : diag_msg) : list (list Z) :=
  match d with
  | DUsage s => pieces_usage s | DCannotOpen s => pieces_cannot_open s | DReadError s => pieces_read_error s
  | DTooBig => pieces_too_big | DOom => pieces_oom | DShortHdr => pieces_short_hdr | DCfgOverrun => pieces_cfg_overrun
  end.

Lemma rz_fprintf_diag :
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
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') Ft (ret_pc ra) fc' None m' (seg_rom rsegs)) mo) K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19ba8) fc None m (seg_rom rsegs)) mo)
           (ShapeAlg.t_emit (Wz 2 (concat (diag_pieces d))) K).
Proof.
  intros until K. intros HK Hmi Hh SE A0 DA ST LO GT SP SSP MI FRM HW CONT.
  pose proof (fprintf_diag_proof PState d ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m st lo canary fwritex_stderr_proof stdio_write_flush_proof SE A0 DA ST LO GT SP SSP MI FRM) as IM.
  unfold implM in IM.
  assert (ED : s_diag (St:=PState) d = stderr_fprintf (diag_pieces d)).
  { destruct d; cbn [diag_args] in DA; lazymatch type of DA with False => destruct DA | _ => reflexivity end. }
  rewrite ED in IM.
  apply (impl_trz_realizes_leafC (stderr_fprintf (diag_pieces d) st) _ _ mo (fun _ _ => K) _ IM
           (trz_stderr_fprintf (diag_pieces d) st mo (fun _ _ => K) (conj Hmi Hh) HW (fun _ _ => HK)) Hh Hmi).
  intros r ms' mo' HQ L _ _. apply (leaf_stderr_fprintf_ok (diag_pieces d) st) in L as [-> ->]; [| exact HW].
  unfold epost in HQ. cbn [fst snd] in HQ. unfold fprintf_diag_post in HQ.
  destruct HQ as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FEQ & ST' & SE' & SSP' & _).
  exact (CONT u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m' MU WM MI' FRM' FEQ ST' SE' SSP').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma leaf_exit_model_none : forall code (s : PState) mo r mo',
  zlength (so_buf (ps_so s)) <= STDOUT_BUFSIZ ->
  leaf (Driver.exit_model (io_S ps_so set_so_ps) code s) mo r mo' -> False.
Proof.
  intros code s mo r mo' Hb L. unfold Driver.exit_model in L.
  change (io_exit (io_S ps_so set_so_ps)) with (stdout_exit_flush ps_so set_so_ps) in L.
  apply leaf_mbind_inv in L as (a & mo1 & L1 & L).
  apply (leaf_stdout_exit_flush_ok ps_so set_so_ps ps_get_set ps_set_set) in L1 as [-> ->]; [| exact Hb | exact ps_set_get].
  cbn [fst snd] in L. apply leaf_msys in L as (rsp & evs & Hst & _). exact Hst.
Qed.

Lemma rz_exit : forall (s : PState)
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
    realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
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
  apply (impl_trz_realizes_leafC (Driver.exit_model (io_S ps_so set_so_ps) code s) _ _ mo (fun _ _ => t_nil) _ IM); [| exact Hh | exact Hmi |].
  - unfold Driver.exit_model. change (io_exit (io_S ps_so set_so_ps)) with (stdout_exit_flush ps_so set_so_ps).
    apply (trz_stdout_exit_flush_k ps_so set_so_ps ps_get_set ps_set_set (fun _ => msys (NExit code) dec_exit) s mo _ _ (conj Hmi Hh) Hb).
    + apply trz_exit. exact Hmi.
    + apply t_emit_has_nil.
    + exact ps_set_get.
  - intros r ms' mo' _ L _ _. exfalso. exact (leaf_exit_model_none code s mo r mo' Hb L).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bind_ret_unit_teq {St : Type} : forall (t : itree node (exc (unit * St))),
  teq (ITree.bind node t (fun r => match r with Ok p => Ret (Ok (tt, snd p)) | Unr => Ret Unr end)) t.
Proof.
  induction t as [[|[[] s']] | n k IH]; cbn [ITree.bind snd]; try apply teq_refl.
  constructor. intros x. apply IH.
Qed.

Lemma trz_stdout_vprintf : forall (ps : list (list Z)) (st : PState) mo (K : exc (unit * PState) -> Model -> TSet),
  mok mo -> zlength (so_buf (ps_so st)) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) ps ->
  let st' := set_so_ps (snd (vprintf_pure (ps_so st) ps)) st in
  K (Ok (tt, st')) mo [] ->
  trzN (stdout_vprintf ps_so set_so_ps ps st) mo K (ShapeAlg.t_emit (Wz 1 (fst (vprintf_pure (ps_so st) ps))) (K (Ok (tt, st')) mo)).
Proof.
  intros ps st mo K Hok Hb Hps st' HK.
  eapply trz_teq; [| apply (bind_ret_unit_teq (stdout_vprintf ps_so set_so_ps ps st))].
  change (ITree.bind node (stdout_vprintf ps_so set_so_ps ps st) (fun r => match r with Ok p => Ret (Ok (tt, snd p)) | Unr => Ret Unr end))
    with (mbind (stdout_vprintf ps_so set_so_ps ps) (fun _ => mret tt) st).
  apply (trz_stdout_vprintf_k ps_so set_so_ps ps_get_set ps_set_set ps (fun _ => mret tt) st mo K _ Hok Hb Hps); [| exact HK | exact ps_set_get].
  apply trz_mret.
Qed.

Lemma digits_aux_length : forall fuel base dig x acc, (length (digits_aux fuel base dig x acc) <= fuel + length acc)%nat.
Proof.
  induction fuel as [|fuel IH]; intros base dig x acc; cbn [digits_aux]; [lia|].
  destruct (x =? 0); [cbn; lia|]. etransitivity; [apply IH|]. cbn [length]. lia.
Qed.

Lemma pieces_emit_d_small : forall rc, Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) (pieces_emit_d rc).
Proof.
  intros rc. unfold pieces_emit_d.
  assert (HD : forall z, zlength (dec_digits z) + STDOUT_BUFSIZ <= WRITEV_MAX).
  { intros z. unfold dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v) z []). cbn [length] in H.
    unfold STDOUT_BUFSIZ, WRITEV_MAX, zlength in *. lia. }
  destruct (rc =? 0); [| destruct (rc <? 0)]; repeat constructor; try apply HD;
    unfold zlength, STDOUT_BUFSIZ, WRITEV_MAX; cbn; lia.
Qed.

Lemma rz_emit_printf :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (st : PState) (lo : Z) (canary : word) (rc : Z) (K : TSet),
  K [] -> minv mo -> m_halted mo = None ->
  stdout_file m (ps_so st) ->
  (-2^31 <= rc < 2^31) -> bv_unsigned a1 mod 2^32 = rc mod 2^32 ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
  (bv_unsigned sp < 0x800000000000) ->
  ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
  zlength (so_buf (ps_so st)) <= STDOUT_BUFSIZ ->
  let st' := set_so_ps (snd (vprintf_pure (ps_so st) (pieces_emit_d rc))) st in
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
     munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm0 fc' ->
     (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
     stk rsegs m' lo (bv_unsigned sp) -> stdout_file m' (ps_so st') -> ssp_cells m' canary ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') Ft (ret_pc ra) fc' None m' (seg_rom rsegs)) mo) K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1392c) fc None m (seg_rom rsegs)) mo)
           (ShapeAlg.t_emit (Wz 1 (fst (vprintf_pure (ps_so st) (pieces_emit_d rc)))) K).
Proof.
  intros until K. intros HK Hmi Hh SOF RC ERC ST LO GT SP SSP MI FRM Hb st' CONT.
  pose proof (emit_printf_proof PState ps_so set_so_ps ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m st lo canary rc (fun x so => ps_get_set so x) (fun x so so' => ps_set_set so so' x) fwritex_stdout_proof
                SOF RC ERC ST LO GT SP SSP MI FRM) as IM.
  unfold implM in IM.
  apply (impl_trz_realizes_leafC (stdout_vprintf ps_so set_so_ps (pieces_emit_d rc) st) _ _ mo (fun _ _ => K) _ IM
           (trz_stdout_vprintf (pieces_emit_d rc) st mo (fun _ _ => K) (conj Hmi Hh) Hb (pieces_emit_d_small rc) HK) Hh Hmi).
  intros r ms' mo' HQ L _ _.
  apply (leaf_stdout_vprintf_ok ps_so set_so_ps ps_get_set ps_set_set (pieces_emit_d rc) st) in L as [-> ->];
    [| exact Hb | apply pieces_emit_d_small | exact ps_set_get].
  unfold epost in HQ. cbn [fst snd] in HQ. unfold emit_printf_post in HQ.
  destruct HQ as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FEQ & ST' & SOF' & SSP').
  exact (CONT u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m' MU WM MI' FRM' FEQ ST' SOF' SSP').
Qed.
End RC__1.
