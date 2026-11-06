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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep ITree Nodes NodesCfg Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanLayout.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel ITreeA NodesA ImplRzA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BI_globals2 B_iface BI_iface B_iface5x BM_syscalls BI_memtoshadow BI_region_is_poisoned BI_read_icp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma mequiv_magree : forall mo mo', mequiv mo mo' -> magree mo mo'.
Proof. aceil.
  intros [fd1 [maps1 lazy1 mat1] io1 fs1 proc1 lim1 tm1] [fd2 [maps2 lazy2 mat2] io2 fs2 proc2 lim2 tm2] H.
  unfold mequiv, merase, with_vm_backing, m_vmmaps, m_vm_lazy, m_fd, m_io, m_fsys, m_proc, m_lim, m_time in H. cbn in H.
  inversion H; subst.
  exists mat2. unfold with_vm_backing, m_vmmaps, m_vm_lazy, m_fd, m_io, m_fsys, m_proc, m_lim, m_time. cbn. reflexivity.
Qed.

Section Adapt.
Variable APS : Type.
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> StdioBase.stdout_st.
Variables (aS : APS -> word -> Prop) (aN : APS -> nat) (aEB : APS -> Z).
Variable aalloc_same : APS -> APS -> Prop.
Notation C := ACONSTS.
Notation ERRNO := 0x5e14ac%Z (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHK_icp_globals2_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo -> icp_globals2 bsegs m.
Definition AHK_icp_errno_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
    (exists errv, rw_cells bsegs m ERRNO [C4 errv])
    /\ (forall m' W, munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
          Forall (fun iv => aclient_write_ok C LB iv \/ iv = (ERRNO, ERRNO + 4)) W -> AHK s LB LF m' mo).

Hypothesis Hkip : AHK_kip_stmt C APS AHK aS aN aEB.
Hypothesis Hmi : AHK_mem_inv_stmt bsegs APS AHK.
Hypothesis Hblocks : AHK_blocks_stmt C APS AHK.
Hypothesis Hvmsame : AHK_vmsame_stmt APS AHK.
Hypothesis Hglob : AHK_icp_globals_stmt bsegs APS AHK.
Hypothesis Hglob2 : AHK_icp_globals2_stmt.
Hypothesis Herrno : AHK_icp_errno_stmt.
Hypothesis Hbsh : AHK_icp_block_shadow_stmt bsegs APS AHK.
Hypothesis Hreg : AHK_icp_regions_stmt APS AHK aS.
Hypothesis Hsame_refl : forall s, aalloc_same s s.

#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation usp sp := (bv_unsigned sp).

Lemma aread_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo mo1 : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (fd buf count lo : Z) (junk : list byte) (b : ablock) (ans : read_ans) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  In b LB -> ab_addr b <= buf -> buf + count <= ab_addr b + ab_size b -> 0 < count <= 65536 -> 3 <= fd < 2^32 ->
  rw_cells bsegs m buf [CB (Z.to_nat count) junk] ->
  read_out fd buf count mo = Some (ans, mo1) ->
  stk bsegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz fd -> a1 = wz buf -> a2 = wz count ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (res : Z),
     stk bsegs m' lo (usp sp) ->
     match ans with
     | RdErr e => res = 2^64 - 1
     | RdData bs => res = Z.of_nat (length bs) /\ bytes_at bsegs m' buf bs
     end ->
     munch [(lo, usp sp); (buf, buf + count); (ERRNO, ERRNO + 4)] m m' ->
     wmono bsegs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo1 -> magree mo1 mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_read C)) fc None m (seg_rom bsegs)) mo) K.
Proof. aceil.
  intros until K. intros HK0 HA Ib Hb1 Hb2 HCNT HFD DST RO ST LOC LO HTP FRM -> -> -> HK.
  cbv beta. unfold AICP_STACK in LO.
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  destruct (Hblocks _ _ _ _ _ HA) as (RNG & DISJ & _).
  pose proof (RNG _ Ib) as Rb. unfold ablock_range in Rb. cbn [c_img_hi ACONSTS] in Rb.
  pose proof (Hglob _ _ _ _ _ HA) as G. pose proof (Hglob2 _ _ _ _ _ HA) as G2.
  destruct (Herrno _ _ _ _ _ HA) as [[errv ERR] EFR].
  assert (SBR : 2^24 <= C_SB < 2^32) by (unfold C_SB; lia).
  destruct (Hbsh _ _ _ _ _ b buf count HA Ib ltac:(lia) ltac:(lia) ltac:(lia)) as (ws & SW & RC & AMB).
  pose proof (app_mem_shadow_facts _ _ buf count AMB Hb1 ltac:(lia) Hb2) as (RIMB & SLOB & SHIB & _ & SEPB & B47 & Bpos).
  pose proof (SEPB (ab_addr b) (ab_size b) AMB ltac:(lia)) as SEP_BB. clear SEPB AMB.
  destruct (Hreg _ _ _ _ _ HA) as (_ & _ & _ & PB).
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  aceil. unfold C_SB in *.
  set (P := acc_ok (m_vm_lazy mo) (aS s)).
  (* [comment removed for export] *)
  assert (IM : implA bsegs (at_nodeA bsegs) P (enode (NRead fd buf count) (dec_read buf count))
            (epost (read_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc buf count 0x7fff8000 junk ws errv lo m))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz fd) (wz buf) (wz count) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x42fdc) fc None m (seg_rom bsegs))).
  { eapply implA_evtA. { stepA. apply evtA_done. eapply eq_refl. } cbv beta. intros ms' <-.
    eapply (read_icp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fd buf count 0x7fff8000 junk ws errv lo P);
      try reflexivity.
    - exact ST.
    - aceil. lia.
    - lia.
    - exact MI.
    - lia. - lia.
    - exact RIMB.
    - lia.
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia. lia.
    - lia.
    - exact DST.
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia. exact ERR.
    - exact G. - exact G2.
    - exact SW. - exact RC. - lia.
    - pose proof (shw_geom 0x7fff8000 buf count ltac:(lia) ltac:(lia) ltac:(lia)) as GD; cbv zeta in GD.
      intros a k H1 H2. right. eapply pages_budgeted_acc_inS; [exact (PB b buf count Ib Hb1 ltac:(lia) Hb2) | lia | lia | lia | lia].
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia.
      intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. right; right. exists b. split; [exact Ib| lia].
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia. }
  eapply (srzA_enode bsegs (aS s) (aN s) (aEB s) P (NRead fd buf count) (dec_read buf count) _ _ mo
            (fun a moz => read_out fd buf count mo = Some (a, moz)) K IM).
  - left; exact I.
  - split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
  - exact HK0.
  - (* [comment removed for export] *)
    unfold read_out in RO. cbn [nstep].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|i w|drd dwr| ]|] eqn:E; try discriminate.
    + destruct (fs_lookup (m_fs mo) p) as [data|] eqn:FL; [|discriminate].
      eexists _, _, []. split; [reflexivity|]. split; reflexivity.
    + exists (efferr EISDIR), mo, []. auto.
    + exists (efferr EBADF), mo, []. auto.
  - (* [comment removed for export] *)
    intros rsp moz evs Hn. destruct (nstep_dec_read fd buf count mo rsp moz evs ltac:(lia) Hn) as (-> & a & D & Ha).
    split; [reflexivity|]. exists a. split; [exact D|]. unfold read_out in RO |- *.
    destruct a as [e|bs].
    + destruct Ha as (-> & [(-> & E) | (-> & E)]); rewrite E in RO |- *; reflexivity.
    + destruct Ha as (p & off & data & E & FL & -> & ->). rewrite E, FL in RO |- *. reflexivity.
  - intros code moz Hx. exact Hx.
  - (* [comment removed for export] *)
    intros a moz moa ms' RO' PO Heq HKP.
    rewrite RO in RO'. injection RO' as <- <-.
    unfold read_icp_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & ANS & G' & G2' & SW').
    rewrite HTP in MU, ANS. cbn [c_tp ACONSTS] in MU, ANS. rewrite !unsigned_lit in MU by lia. rewrite ?unsigned_lit in ANS by lia.
    (* [comment removed for export] *)
    assert (HA1 : AHK s LB LF m' mo).
    { eapply EFR; [exact MU | exact WM | exact MI' |].
      constructor. { left. unfold aclient_write_ok. cbn [fst snd]. left. aceil. lia. }
      constructor. { left. unfold aclient_write_ok. cbn [fst snd]. right; left. exists b. split; [exact Ib| lia]. }
      constructor. { right. reflexivity. }
      constructor. }
    assert (VS : vm_same mo mo1 /\ minvA mo1 /\ m_halted mo1 = None /\ m_fs mo1 = m_fs mo).
    { unfold read_out in RO.
      destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|i w|drd dwr| ]|] eqn:E; try discriminate.
      - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:FL; [|discriminate]. injection RO as E1 E2. subst.
        split; [apply vm_same_with_fds|]. split; [eapply minvA_update_file; [exact Hminv | exact E]|].
        split; [destruct mo; exact Hh | destruct mo; reflexivity].
      - injection RO as E1 E2; subst. split; [apply vm_same_refl|]. auto.
      - injection RO as E1 E2; subst. split; [apply vm_same_refl|]. auto. }
    destruct VS as (VS1 & VS2 & VS3 & VS4).
    assert (HA2 : AHK s LB LF m' mo1) by (eapply Hvmsame; [exact HA1 | exact VS1 | exact VS2 | exact VS3 | exact VS4]).
    pose proof (mequiv_magree _ _ Heq) as Hag.
    destruct HKP as [[HLIa _] _].
    destruct (Hkip _ _ _ _ _ HA2) as (_ & _ & _ & _ & MAG2).
    pose proof (MAG2 moa Hag HLIa) as HA3.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    destruct ans as [e|bs].
    + destruct ANS as (DST' & ERR' & He). cbn [read_ret].
      replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (2^64 - 1) : word) by (apply Z_to_bv_eqm; reflexivity).
      eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' moa s (2^64 - 1)).
      * exact ST'.
      * reflexivity.
      * eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
      * exact WM. * exact FRM. * exact HA3. * apply Hsame_refl. * reflexivity.
      * rewrite Efs. exact VS4. * exact Efds. * exact Hag.
    + destruct ANS as (DST' & ERR' & Hlen). cbn [read_ret].
      { eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' moa s (Z.of_nat (length bs))).
        * exact ST'.
        * split; [reflexivity|]. pose proof (rw_cells_bytes_at _ _ _ _ DST') as BY. cbn [cells_bytes cbytes] in BY.
          apply bytes_at_app in BY as [BY _]. exact BY.
        * eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
        * exact WM. * exact FRM. * exact HA3. * apply Hsame_refl. * reflexivity.
        * rewrite Efs. exact VS4. * exact Efds. * exact Hag. }
Qed.

Lemma aread_ok : aread_rz_stmt bsegs C APS AHK SO aalloc_same.
Proof. aceil.
  unfold aread_rz_stmt. intros until K. intros HK0 HA Ib Hb1 Hb2 HCNT HFD DST RO ST LOC LO HTP FRM HA0 HA1 HA2 HK.
  eapply aread_rz; try eassumption.
  intros. destruct ans as [e|bs].
  - eapply HK; try eassumption. cbn [c_errno ACONSTS]. split; assumption.
  - eapply HK; try eassumption. cbn [c_errno ACONSTS]. destruct H0 as [E B]. split; [exact E| split; [exact B| assumption]].
Qed.

(* [comment removed for export] *)
Hypothesis Hmss : AHK_icp_musl_statics_shadow_stmt bsegs APS AHK aS.
Hypothesis Hfrs : AHK_frame_rstage_stmt bsegs C APS AHK.

Lemma aread_static_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo mo1 : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (fd buf count lo : Z) (junk : list byte) (ans : read_ans) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  A_RSTAGE <= buf -> buf + count <= A_RSTAGE + A_RSTAGE_LEN -> 0 < count <= 65536 -> 3 <= fd < 2^32 ->
  rw_cells bsegs m buf [CB (Z.to_nat count) junk] ->
  read_out fd buf count mo = Some (ans, mo1) ->
  stk bsegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz fd -> a1 = wz buf -> a2 = wz count ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (res : Z),
     stk bsegs m' lo (usp sp) ->
     match ans with
     | RdErr e => res = 2^64 - 1
     | RdData bs => res = Z.of_nat (length bs) /\ bytes_at bsegs m' buf bs
     end ->
     munch [(lo, usp sp); (buf, buf + count); (ERRNO, ERRNO + 4)] m m' ->
     wmono bsegs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo1 -> magree mo1 mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_read C)) fc None m (seg_rom bsegs)) mo) K.
Proof. aceil.
  intros until K. intros HK0 HA Hb1 Hb2 HCNT HFD DST RO ST LOC LO HTP FRM -> -> -> HK.
  cbv beta. unfold AICP_STACK in LO. unfold A_RSTAGE, A_RSTAGE_LEN in Hb1, Hb2.
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  destruct (Hblocks _ _ _ _ _ HA) as (RNG & DISJ & _).
  pose proof (Hglob _ _ _ _ _ HA) as G. pose proof (Hglob2 _ _ _ _ _ HA) as G2.
  destruct (Herrno _ _ _ _ _ HA) as [[errv ERR] EFR].
  assert (SBR : 2^24 <= C_SB < 2^32) by (unfold C_SB; lia).
  destruct (Hmss _ _ _ _ _ buf count HA ltac:(lia) ltac:(lia) ltac:(lia)) as (ws & SW & RC & PBB).
  pose proof (img_shadow_facts buf count ltac:(lia) ltac:(lia) ltac:(lia)) as (RIMB & SLOB & SHIB & _ & B47 & Bpos).
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  aceil. unfold C_SB in *.
  set (P := acc_ok (m_vm_lazy mo) (aS s)).
  (* [comment removed for export] *)
  assert (IM : implA bsegs (at_nodeA bsegs) P (enode (NRead fd buf count) (dec_read buf count))
            (epost (read_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc buf count 0x7fff8000 junk ws errv lo m))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz fd) (wz buf) (wz count) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x42fdc) fc None m (seg_rom bsegs))).
  { eapply implA_evtA. { stepA. apply evtA_done. eapply eq_refl. } cbv beta. intros ms' <-.
    eapply (read_icp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fd buf count 0x7fff8000 junk ws errv lo P);
      try reflexivity.
    - exact ST.
    - aceil. lia.
    - lia.
    - exact MI.
    - lia. - lia.
    - exact RIMB.
    - lia.
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia. lia.
    - lia.
    - exact DST.
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia. exact ERR.
    - exact G. - exact G2.
    - exact SW. - exact RC. - lia.
    - pose proof (shw_geom 0x7fff8000 buf count ltac:(lia) ltac:(lia) ltac:(lia)) as GD; cbv zeta in GD.
      intros a k H1 H2. right. eapply pages_budgeted_acc_inS; [exact PBB | lia | lia | lia | lia].
    - rewrite HTP. cbn [c_tp ACONSTS]. rewrite unsigned_lit by lia.
      intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia. }
  eapply (srzA_enode bsegs (aS s) (aN s) (aEB s) P (NRead fd buf count) (dec_read buf count) _ _ mo
            (fun a moz => read_out fd buf count mo = Some (a, moz)) K IM).
  - left; exact I.
  - split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
  - exact HK0.
  - (* [comment removed for export] *)
    unfold read_out in RO. cbn [nstep].
    destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|i w|drd dwr| ]|] eqn:E; try discriminate.
    + destruct (fs_lookup (m_fs mo) p) as [data|] eqn:FL; [|discriminate].
      eexists _, _, []. split; [reflexivity|]. split; reflexivity.
    + exists (efferr EISDIR), mo, []. auto.
    + exists (efferr EBADF), mo, []. auto.
  - (* [comment removed for export] *)
    intros rsp moz evs Hn. destruct (nstep_dec_read fd buf count mo rsp moz evs ltac:(lia) Hn) as (-> & a & D & Ha).
    split; [reflexivity|]. exists a. split; [exact D|]. unfold read_out in RO |- *.
    destruct a as [e|bs].
    + destruct Ha as (-> & [(-> & E) | (-> & E)]); rewrite E in RO |- *; reflexivity.
    + destruct Ha as (p & off & data & E & FL & -> & ->). rewrite E, FL in RO |- *. reflexivity.
  - intros code moz Hx. exact Hx.
  - (* [comment removed for export] *)
    intros a moz moa ms' RO' PO Heq HKP.
    rewrite RO in RO'. injection RO' as <- <-.
    unfold read_icp_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & ANS & G' & G2' & SW').
    rewrite HTP in MU, ANS. cbn [c_tp ACONSTS] in MU, ANS. rewrite !unsigned_lit in MU by lia. rewrite ?unsigned_lit in ANS by lia.
    (* [comment removed for export] *)
    assert (HA1 : AHK s LB LF m' mo).
    { eapply Hfrs; [exact HA | exact MU | exact WM |].
      constructor. { left. unfold aclient_write_ok. cbn [fst snd]. left. aceil. lia. }
      constructor. { right; left. unfold rstage_iv, A_RSTAGE, A_RSTAGE_LEN. cbn [fst snd]. lia. }
      constructor. { right; right. reflexivity. }
      constructor. }
    assert (VS : vm_same mo mo1 /\ minvA mo1 /\ m_halted mo1 = None /\ m_fs mo1 = m_fs mo).
    { unfold read_out in RO.
      destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|i w|drd dwr| ]|] eqn:E; try discriminate.
      - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:FL; [|discriminate]. injection RO as E1 E2. subst.
        split; [apply vm_same_with_fds|]. split; [eapply minvA_update_file; [exact Hminv | exact E]|].
        split; [destruct mo; exact Hh | destruct mo; reflexivity].
      - injection RO as E1 E2; subst. split; [apply vm_same_refl|]. auto.
      - injection RO as E1 E2; subst. split; [apply vm_same_refl|]. auto. }
    destruct VS as (VS1 & VS2 & VS3 & VS4).
    assert (HA2 : AHK s LB LF m' mo1) by (eapply Hvmsame; [exact HA1 | exact VS1 | exact VS2 | exact VS3 | exact VS4]).
    pose proof (mequiv_magree _ _ Heq) as Hag.
    destruct HKP as [[HLIa _] _].
    destruct (Hkip _ _ _ _ _ HA2) as (_ & _ & _ & _ & MAG2).
    pose proof (MAG2 moa Hag HLIa) as HA3.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    destruct ans as [e|bs].
    + destruct ANS as (DST' & ERR' & He). cbn [read_ret].
      replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 (2^64 - 1) : word) by (apply Z_to_bv_eqm; reflexivity).
      eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' moa s (2^64 - 1)).
      * exact ST'.
      * reflexivity.
      * eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
      * exact WM. * exact FRM. * exact HA3. * apply Hsame_refl. * reflexivity.
      * rewrite Efs. exact VS4. * exact Efds. * exact Hag.
    + destruct ANS as (DST' & ERR' & Hlen). cbn [read_ret].
      { eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' moa s (Z.of_nat (length bs))).
        * exact ST'.
        * split; [reflexivity|]. pose proof (rw_cells_bytes_at _ _ _ _ DST') as BY. cbn [cells_bytes cbytes] in BY.
          apply bytes_at_app in BY as [BY _]. exact BY.
        * eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
        * exact WM. * exact FRM. * exact HA3. * apply Hsame_refl. * reflexivity.
        * rewrite Efs. exact VS4. * exact Efds. * exact Hag. }
Qed.

Lemma aread_static_ok : aread_static_rz_stmt bsegs C APS AHK SO aalloc_same.
Proof. aceil.
  unfold aread_static_rz_stmt. intros until K. intros HK0 HA Hb1 Hb2 HCNT HFD DST RO ST LOC LO HTP FRM HA0 HA1 HA2 HK.
  eapply aread_static_rz; try eassumption.
  intros. destruct ans as [e|bs].
  - eapply HK; try eassumption. cbn [c_errno ACONSTS]. split; assumption.
  - eapply HK; try eassumption. cbn [c_errno ACONSTS]. destruct H0 as [E B]. split; [exact E| split; [exact B| assumption]].
Qed.
End Adapt.
End RC__1.
