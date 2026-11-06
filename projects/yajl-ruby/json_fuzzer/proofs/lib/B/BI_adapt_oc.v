(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep ITree Nodes NodesCfg Decode SFModel PropExec MState Mem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodes TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel ExecA ITreeA NodesA ImplRzA MonadA TrzNodesA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit B_iface BI_iface BX_file BM_syscalls BX_trz BX_Exit BX_adapt BI_adapt2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma implA_msys_of_enode : forall P {St A} (n : node) (dec : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
  implA bsegs (at_nodeA bsegs) P (enode n dec) (epost Q) ms ->
  implA bsegs (at_nodeA bsegs) P (msys n dec s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof. aceil.
  intros P St A n dec Q s ms H. unfold msys, enode in *. cbn in *.
  eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (dec rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evtA_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

Lemma m_fds_with_fds : forall f mo, m_fds (with_fds f mo) = f.
Proof. aceil. intros f mo; destruct mo; reflexivity. Qed.
Lemma m_fs_with_fds : forall f mo, m_fs (with_fds f mo) = m_fs mo.
Proof. aceil. intros f mo; destruct mo; reflexivity. Qed.
Lemma m_halted_with_fds : forall f mo, m_halted (with_fds f mo) = m_halted mo.
Proof. aceil. intros f mo; destruct mo; reflexivity. Qed.

Section Adapt.
Variable APS : Type.
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> stdout_st.
Variables (aS : APS -> word -> Prop) (aN : APS -> nat) (aEB : APS -> Z).
Variable aalloc_same : APS -> APS -> Prop.
Notation C := ACONSTS.

Hypothesis Hkip : AHK_kip_stmt C APS AHK aS aN aEB.
Hypothesis Hmi : AHK_mem_inv_stmt bsegs APS AHK.
Hypothesis Hvmsame : AHK_vmsame_stmt APS AHK.
Hypothesis Herrno : AHK_icp_errno_stmt APS AHK.
Hypothesis Hexit : AHK_icp_exit_stmt APS AHK SO aS.
Hypothesis Hsame_refl : forall s, aalloc_same s s.

#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation usp sp := (bv_unsigned sp).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aclose_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (fd lo : Z) (K : TSet),
  K [] -> AHK s LB LF m mo -> 3 <= fd < 2^32 ->
  stk bsegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - 160 -> tp = wz (c_tp C) -> a0 = wz fd ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : APS),
     stk bsegs m' lo (usp sp) -> munch [(lo, usp sp); (c_errno C, c_errno C + 4)] m m' -> wmono bsegs m m' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s ->
     m_fs mo' = m_fs mo -> m_fds mo' = m_fds (snd (close_out fd mo)) -> magree (snd (close_out fd mo)) mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_close C)) fc None m (seg_rom bsegs)) mo) K.
Proof. aceil.
  intros until K. intros HK0 HA HFD ST LOC LO HTP HA0 HK.
  cbv beta.
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  destruct (Herrno _ _ _ _ _ HA) as [[errv ERR] EFR].
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  aceil.
  set (P := acc_ok (m_vm_lazy mo) (aS s)).
  assert (ETP : errno_addr tp = 0x5e14ac) by (rewrite HTP; unfold errno_addr; cbn [c_tp ACONSTS]; rewrite unsigned_lit by lia; reflexivity).
  assert (IM : implA bsegs (at_nodeA bsegs) P (enode (NClose fd) dec_close)
            (epost (close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xa3ef0) fc None m (seg_rom bsegs))).
  { eapply (close_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m fd errv lo P); rewrite ?ETP.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia.
    - exact ST.
    - cbn [c_errno ACONSTS] in ERR. exact ERR.
    - exact MI.
    - exact HA0.
    - exact HFD.
    - lia.
    - lia.
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia. lia. }
  eapply (srzA_enode bsegs (aS s) (aN s) (aEB s) P (NClose fd) dec_close _ _ mo
            (fun a mo1 => a = fst (close_out fd mo) /\ mo1 = snd (close_out fd mo)) K IM).
  - left; exact I.
  - split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
  - exact HK0.
  - cbn [nstep]. unfold close_out.
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:E.
    + exists (eff0 (Z_to_bv 64 0)), (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo), []. repeat split; auto; lia.
    + exists (efferr EBADF), mo, []. repeat split; auto; lia.
  - intros rsp mo1 evs H. destruct (nstep_dec_close _ _ _ _ _ H) as (-> & a & D & Ha).
    split; [reflexivity|]. exists a. split; [exact D|]. unfold close_out.
    destruct a as [e|v].
    + destruct Ha as (-> & -> & E). rewrite E. auto.
    + destruct Ha as (-> & NE & ->). destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); [auto | congruence].
  - intros code mo1 H. exact H.
  - intros a mo1 moa ms' [-> ->] PO Heq HKP.
    unfold close_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & ERR').
    rewrite ETP in MU.
    assert (HA1 : AHK s LB LF m' mo).
    { eapply EFR; [exact MU | exact WM | exact MI' |].
      constructor. { left. unfold aclient_write_ok. cbn [fst snd]. left. aceil. lia. }
      constructor. { right. reflexivity. }
      constructor. }
    assert (VS : vm_same mo (snd (close_out fd mo)) /\ minvA (snd (close_out fd mo)) /\ m_halted (snd (close_out fd mo)) = None
                 /\ m_fs (snd (close_out fd mo)) = m_fs mo).
    { unfold close_out. destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); cbn [fst snd].
      - split; [apply vm_same_with_fds|]. split; [apply minvA_remove; [exact Hminv | exact HFD]|].
        rewrite m_halted_with_fds, m_fs_with_fds. auto.
      - split; [apply vm_same_refl|]. auto. }
    destruct VS as (VS1 & VS2 & VS3 & VS4).
    assert (HA2 : AHK s LB LF m' (snd (close_out fd mo))) by (eapply Hvmsame; [exact HA1 | exact VS1 | exact VS2 | exact VS3 | exact VS4]).
    pose proof (mequiv_magree _ _ Heq) as Hag.
    destruct HKP as [[HLIa _] _].
    destruct (Hkip _ _ _ _ _ HA2) as (_ & _ & _ & _ & MAG2).
    pose proof (MAG2 moa Hag HLIa) as HA3.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' moa s).
    + exact ST'.
    + cbn [c_errno ACONSTS]. eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros; lia.
    + exact WM.
    + exact HA3.
    + apply Hsame_refl.
    + reflexivity.
    + rewrite Efs. exact VS4.
    + exact Efds.
    + exact Hag.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aopen_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (pa lo : Z) (path : list byte) (KA KB : TSet),
  KA [] -> KB [] ->
  AHK s LB LF m mo ->
  bytes_at bsegs m pa (path ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) path -> usp sp <= pa -> pa + Z.of_nat (length path) + 1 <= 2^47 ->
  path_has_slash path = false ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None -> 3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096 ->
  stk bsegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - 160 -> tp = wz (c_tp C) ->
  a0 = wz pa -> a1 = wz 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : APS) (e : Z),
     (open_classify path mo = OcErrno e \/ (exists ent, open_classify path mo = OcMay ent /\ In e openat_errnos)) ->
     stk bsegs m' lo (usp sp) -> munch [(lo, usp sp); (c_errno C, c_errno C + 4)] m m' -> wmono bsegs m m' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s ->
     m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (2^64 - 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') KA) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : APS) (ent : FdEntry),
     open_classify path mo = OcMay ent ->
     let fd := alloc_fd (m_fds mo) in
     stk bsegs m' lo (usp sp) -> munch [(lo, usp sp); (c_errno C, c_errno C + 4)] m m' -> wmono bsegs m m' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s ->
     m_fs mo' = m_fs mo -> m_fds mo' = fd_insert (m_fds mo) fd ent -> magree (with_fds (fd_insert (m_fds mo) fd ent) mo) mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 fd a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') KB) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_open C)) fc None m (seg_rom bsegs)) mo)
            (match open_classify path mo with OcErrno _ => KA | _ => t_alt2 KA KB end).
Proof. aceil.
  intros until KB. intros HKA HKB HA SRC NUL QPA PHI PSL FREE FDR ST LOC LO HTP -> HA1z KF KS.
  cbv beta.
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  destruct (Herrno _ _ _ _ _ HA) as [[errv ERR] EFR].
  destruct (Hexit _ _ _ _ _ HA) as (_ & (guard & cdt & thr & sec & tm1 & SS) & _).
  destruct SS as (_ & _ & _ & _ & [GOT SSP]).
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  aceil.
  set (P := acc_ok (m_vm_lazy mo) (aS s)).
  assert (ETP : errno_addr tp = 0x5e14ac) by (rewrite HTP; unfold errno_addr; cbn [c_tp ACONSTS]; rewrite unsigned_lit by lia; reflexivity).
  assert (IM : implA bsegs (at_nodeA bsegs) P (enode (NOpen path) dec_open)
            (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc pa path errv guard lo m))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz pa) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x92b74) fc None m (seg_rom bsegs))).
  { pose proof (open_spec ra sp gp tp t0 t1 t2 s0 s1 (wz pa) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv guard lo P) as SPEC.
    cbv beta in SPEC. rewrite !unsigned_lit in SPEC by lia. rewrite ETP in SPEC. unfold got_ssp, ssp_guard in SPEC.
    apply SPEC; clear SPEC.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia.
    - exact ST.
    - exact SRC.
    - cbn [c_errno ACONSTS] in ERR. exact ERR.
    - exact GOT.
    - exact SSP.
    - exact MI.
    - exact HA1z.
    - exact NUL.
    - exact PSL.
    - lia. - lia. - lia. - lia. - lia. - lia. - lia.
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  assert (FAILK : forall e ms' mo1 moa,
    (open_classify path mo = OcErrno e \/ (exists ent, open_classify path mo = OcMay ent /\ In e openat_errnos)) ->
    open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc pa path errv guard lo m (SErr e) ms' ->
    mo1 = mo -> mequiv mo1 moa -> KIP (aS s) (aN s) (aEB s) P moa -> realizes_cfg acfg bsegs (mkCfg ms' moa) KA).
  { intros e ms' mo1 moa He PO -> Heq HKP. unfold open_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & _).
    rewrite ETP in MU.
    assert (HA1 : AHK s LB LF m' mo).
    { eapply EFR; [exact MU | exact WM | exact MI' |].
      constructor. { left. unfold aclient_write_ok. cbn [fst snd]. left. aceil. lia. }
      constructor. { right. reflexivity. }
      constructor. }
    pose proof (mequiv_magree _ _ Heq) as Hag.
    destruct HKP as [[HLIa _] _].
    destruct (Hkip _ _ _ _ _ HA1) as (_ & _ & _ & _ & MAG1).
    pose proof (MAG1 moa Hag HLIa) as HA3.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    unfold open_ret. replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (2^64 - 1) : word) by (apply Z_to_bv_eqm; reflexivity).
    eapply (KF _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' moa s e He).
    + exact ST'.
    + cbn [c_errno ACONSTS]. eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros; lia.
    + exact WM.
    + exact HA3.
    + apply Hsame_refl.
    + reflexivity.
    + exact Efs.
    + exact Efds.
    + exact Hag. }
  destruct (open_classify path mo) as [e|ent] eqn:OC.
  - (* [comment removed for export] *)
    assert (He : 1 <= e <= 4095).
    { clear -CEILB OC. unfold open_classify in OC. destruct (path_max <=? length path)%nat. { inversion OC. unfold ENAMETOOLONG; lia. }
      destruct path; [inversion OC; unfold ENOENT; lia|]. destruct (path_is_dirref _); [discriminate|].
      destruct (fs_lookup _ _); [discriminate|]. inversion OC. unfold ENOENT; lia. }
    eapply (srzA_enode bsegs (aS s) (aN s) (aEB s) P (NOpen path) dec_open _ _ mo (fun a mo1 => a = SErr e /\ mo1 = mo) KA IM).
    + left; exact I.
    + split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
    + exact HKA.
    + exists (efferr e), mo, []. apply nstep_open_iff. rewrite OC. auto.
    + intros rsp mo1 evs H. apply nstep_open_iff in H. rewrite OC in H. destruct H as (-> & -> & ->).
      split; [reflexivity|]. exists (SErr e). unfold dec_open. rewrite dec_plain_err by exact He. auto.
    + intros code mo1 H. exact H.
    + intros a mo1 moa ms' [-> Emo] PO Heq HKP. exact (FAILK e ms' mo1 moa (or_introl eq_refl) PO Emo Heq HKP).
  - (* [comment removed for export] *)
    set (fd := alloc_fd (m_fds mo)) in *.
    apply (implA_msys_of_enode P (NOpen path) dec_open _ tt) in IM.
    eapply (implA_trzA_srealizes bsegs (aS s) (aN s) (aEB s) P (msys (NOpen path) dec_open tt) _ _ mo mo
             (fun r mo1 => match r with
                           | Ok (SErr _, _) => KA
                           | Ok (SVal _, _) => KB
                           | Unr => t_nil
                           end) (t_alt2 KA KB) IM).
    + apply (trzA_open_may path ent tt mo _ KA KB Hminv OC FREE FDR); [intros; apply t_eq_refl | apply t_eq_refl | exact HKA | exact HKB].
    + apply mequiv_refl.
    + split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
    + intros r ms' mo1 moa HQ L Heq HKP. apply leaf_msys in L as (rsp & evs & Hst & ->). pose proof Hst as Hst0.
      apply nstep_open_iff in Hst. rewrite OC in Hst. destruct Hst as [-> [(e & He & -> & ->) | (_ & -> & ->)]].
      * unfold dec_open in HQ |- *. rewrite dec_plain_err in HQ |- * by (apply openat_errnos_range; exact He).
        unfold epost in HQ. cbn [fst snd] in HQ. destruct HQ as [HQ _].
        exact (FAILK e ms' mo moa (or_intror (ex_intro _ ent (conj eq_refl He))) HQ eq_refl Heq HKP).
      * fold fd in HQ |- *.
        assert (DV : dec_open (eff0 fd) = Some (SVal (bv_unsigned fd))).
        { unfold dec_open. rewrite <- (Z_to_bv_bv_unsigned fd) at 1.
          apply dec_plain_val; [lia | apply andb_true_intro; split; apply Z.leb_le; lia]. }
        rewrite DV in HQ. rewrite DV.
        unfold epost in HQ. cbn [fst snd] in HQ. destruct HQ as [PO _].
        unfold open_post in PO.
        destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & _).
        rewrite ETP in MU.
        assert (HA1 : AHK s LB LF m' mo).
        { eapply EFR; [exact MU | exact WM | exact MI' |].
          constructor. { left. unfold aclient_write_ok. cbn [fst snd]. left. aceil. lia. }
          constructor. { right. reflexivity. }
          constructor. }
        set (mo2 := with_fds (fd_insert (m_fds mo) fd ent) mo) in *.
        assert (VS2 : minvA mo2 /\ m_halted mo2 = None).
        { exact (mokA_step (NOpen path) mo (eff0 fd) mo2 [] (conj Hminv Hh) (or_introl I) Hst0). }
        destruct VS2 as [VS2 VS3].
        assert (HA2 : AHK s LB LF m' mo2).
        { eapply Hvmsame; [exact HA1 | subst mo2; apply vm_same_with_fds | exact VS2 | exact VS3 | subst mo2; apply m_fs_with_fds]. }
        pose proof (mequiv_magree _ _ Heq) as Hag.
        destruct HKP as [[HLIa _] _].
        destruct (Hkip _ _ _ _ _ HA2) as (_ & _ & _ & _ & MAG2).
        pose proof (MAG2 moa Hag HLIa) as HA3.
        pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
        unfold open_ret. rewrite Z_to_bv_bv_unsigned.
        eapply (KS _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' moa s ent eq_refl).
        -- exact ST'.
        -- cbn [c_errno ACONSTS]. eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros; lia.
        -- exact WM.
        -- exact HA3.
        -- apply Hsame_refl.
        -- reflexivity.
        -- rewrite Efs. subst mo2. apply m_fs_with_fds.
        -- rewrite Efds. subst mo2. apply m_fds_with_fds.
        -- exact Hag.
Qed.
End Adapt.
End RC__1.
