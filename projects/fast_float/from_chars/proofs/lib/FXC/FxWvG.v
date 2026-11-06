(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChain FxChEnt FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv FxChDir.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir.

Module FxOpenNF.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChain FxChEnt FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv FxChDir.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChBrk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDir.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition open_nf (fsm : Fs.Fs) (dirfd : word) (c : cstr_result) (e : Z) : Prop :=
  (dirfd = AT_FDCWD32 /\ exists p, c = CstrOk p /\ path_eqb p [] = false /\ path_has_slash p = false /\ path_is_dirref p = false /\
                                   fs_lookup fsm p = None /\ e = ENOENT) \/
  (c = CstrOk [] /\ e = ENOENT) \/ (c = CstrTooLong /\ e = ENAMETOOLONG).

Section NF.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.
Hypothesis Hfs : sc_fs cfg = true.

#[using="Hfs"] Theorem den_openat_nf : forall model0 E L M ms model (A : TSet) (c0 flags e : Z),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 56 -> arg L 0 = Some c0 -> arg L 2 = Some flags -> Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) open_ignored_flags = 0 ->
  open_nf (m_fs model0) (fd32 (Z_to_bv 64 c0))
    (read_cstr (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E (rget (s_regs L) (rkey a1r)))) e ->
  ranges_avoid (Hof E M model) [(lden E (rget (s_regs L) (rkey a1r)),
                                 cstr_access_len_aux (in_mem (sys_input segs (svc_set ms) (ms_reg ms 17))) (lden E (rget (s_regs L) (rkey a1r))) path_max)] ->
  (forall ms' m'', DEN segs LIMIT model0 mem0 E (ret_post L (lconst (bv_unsigned (errno_ret e)))) M ms' m'' ->
      realizes_cfg segs cfg (mkCfg ms' m'') A) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) A.
Proof. LiaFast.lf_pins (fun (Hfs : LiaFast.U) => LiaFast.u0).
  intros model0 E L M ms model A c0 flags e Hd H7 H0 H2 Hfl Hnf Hav HA.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17) in *.
  assert (Hx8 : x8 = Z_to_bv 64 56) by exact (a7_const segs E L (restrict H ms) ms 56 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 c0) by exact (gpr_const segs E L (restrict H ms) ms 0 c0 Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = lden E (rget (s_regs L) (rkey a1r))) by exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 2 flags Hsd eq_refl ltac:(lia) H2).
  set (i := sys_input segs ms1 x8) in *.
  assert (Hno : bv_unsigned (in_sysno i) = 56%Z) by (unfold i; cbn [in_sysno sys_input]; rewrite Hx8; reflexivity).
  assert (A0 : in_arg i 0 = Z_to_bv 64 c0) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg0).
  assert (A1 : in_arg i 1 = lden E (rget (s_regs L) (rkey a1r))) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg1).
  assert (A2 : in_arg i 2 = Z_to_bv 64 flags) by (unfold i, ms1; rewrite (in_arg_svc segs mem0) by lia; exact Hg2).
  assert (Hfm : m_fs model = m_fs model0) by (destruct Hvmo as (_ & _ & H3' & _); unfold m_fs; rewrite H3'; reflexivity).
  set (pl := lden E (rget (s_regs L) (rkey a1r))) in *.
  set (ci := [(pl, cstr_access_len_aux (in_mem i) pl path_max)]) in *.
  (* [comment removed for export] *)
  assert (Hspo : forall o, syscall_spec i model o <-> record_copyins ci (err_ret e) i model o).
  { intro o. rewrite (syscall_spec_56 i model o Hno). rewrite A0, A1, A2.
    destruct Hnf as [(Hdfd & p & Hc & Hne & Hsl & Hdr & Hlk & ->) | [(Hc & ->) | (Hc & ->)]].
    - rewrite (openat_rd_reduce (fd32 (Z_to_bv 64 c0)) pl (Z_to_bv 64 flags) p i model o Hdfd Hfl Hc Hne Hsl).
      fold ci. unfold openat_read_spec. rewrite Hdr, Hfm, Hlk. reflexivity.
    - exact (openat_empty_reduce (fd32 (Z_to_bv 64 c0)) pl (Z_to_bv 64 flags) i model o Hfl Hc).
    - exact (openat_toolong_reduce (fd32 (Z_to_bv 64 c0)) pl (Z_to_bv 64 flags) i model o Hfl Hc). }
  assert (Hw0 : forall z, lwf (s_next L) (lconst z) = true) by reflexivity.
  assert (HcA : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (ret_ci (errno_ret e) ci))) m'') A).
  { intros m'' Hinv'' Hsb''. apply HA.
    pose proof (den_ret_ci0 segs LIMIT mem0 model0 E L M ms model (lconst (bv_unsigned (errno_ret e))) ci m'' Hd (Hw0 _) Hinv'' Hsb'') as HD.
    rewrite lden_lconst, u64_roundtrip in HD. exact HD. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc segs cfg H (AM model0 E M) ms1 model x8 unit
             (fun _ => ret_ci (errno_ret e) ci) (fun _ => model) (fun _ => []) (fun _ => A) tt (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros []. apply Hspo. apply record_copyins_ok_iff. exists (mkEffect (errno_ret e) [] []). split.
      2:{ unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
          rewrite app_nil_r. reflexivity. }
      apply err_ret_ok_iff. auto.
    + intros eff m' evs Hs. apply Hspo, record_copyins_ok_iff in Hs as (eff0 & Hs & ->).
      apply err_ret_ok_iff in Hs as (-> & -> & ->). exists tt. auto.
    + intros Hs. apply Hspo, record_copyins_unmodeled_iff in Hs. exact (err_ret_unmodeled _ _ _ Hs).
    + intros eff. apply not_spurious_fs; [exact Hfs | exact Hno].
    + intros []. exact Hh.
    + intros []. apply lazy_cover_mkH_app; intros x Hx'; exact Hx'.
    + intros []. exact Hminv.
    + intros []. unfold ret_ci, syscall_effect_accesses; cbn [eff_copyins eff_writes write_accesses]; rewrite app_nil_r; exact Hav.
    + intros [] m'' Hinv'' Hsb''. exact (HcA m'' Hinv'' Hsb'').
  - apply (t_alt_const_nil unit tt A).
    exact (realizes_cfg_nonempty segs cfg _ _ (HcA model Hminv (same_but_materialized_refl _))).
Qed.
End NF.
(* [comment removed for export] *)
End FxOpenNF.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Instance wvg_fx : FPState := fx0.

Section WvG.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="mem0"] Lemma ipa_bound : forall (b : word) (len : word) (bs : list byte) rest left (H : word -> bool),
  bv_unsigned len = Z.of_nat (length bs) -> range_avoids H b (length bs) ->
  ranges_avoid H (iov_prefix_accesses rest (left - word_to_nat_bounded len left)) ->
  ranges_avoid H (iov_prefix_accesses ((b, len) :: rest) left).
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0).
  intros b len bs rest left H Hlen Hav Hr. destruct left as [|k]; [apply ranges_avoid_nil|].
  cbn [iov_prefix_accesses].
  destruct (Nat.eqb (word_to_nat_bounded len (Datatypes.S k)) 0) eqn:Ez.
  - apply Nat.eqb_eq in Ez. rewrite Ez, Nat.sub_0_r in Hr. exact Hr.
  - apply ranges_avoid_cons; [|exact Hr].
    apply (ra_le H b (length bs)); [|exact Hav].
    pose proof (word_to_nat_bounded_eq_min len (Datatypes.S k)) as X.
    rewrite X. unfold word_to_nat. rewrite Hlen, Nat2Z.id. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_writevG2 : forall model0 E L M ms model (K : TSet) (ch : Z) (b0 l0 b1 l1 len : lin) (bs0 bs1 : list byte) (n : Z),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 66 -> arg L 0 = Some ch -> arg L 2 = Some 2 -> (ch = 1 \/ ch = 2) ->
  fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch)) ->
  rdn segs (ms_mem ms) (lden E (argl L 1)) 8 = Some (word_to_le_bytes 8 (lden E b0)) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (argl L 1)) + 8)) 8 = Some (word_to_le_bytes 8 (lden E l0)) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (argl L 1)) + 16)) 8 = Some (word_to_le_bytes 8 (lden E b1)) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (argl L 1)) + 24)) 8 = Some (word_to_le_bytes 8 (lden E l1)) ->
  rdn segs (ms_mem ms) (lden E b0) (length bs0) = Some bs0 ->
  rdn segs (ms_mem ms) (lden E b1) (length bs1) = Some bs1 ->
  bv_unsigned (lden E l0) = Z.of_nat (length bs0) -> bv_unsigned (lden E l1) = Z.of_nat (length bs1) ->
  bv_unsigned (lden E len) = Z.of_nat (length bs0 + length bs1) ->
  (1 <= length bs0 + length bs1)%nat -> Z.of_nat (length bs0 + length bs1) <= n -> n <= 2 ^ 30 ->
  bv_unsigned (lden E (argl L 1)) + 32 <= TASK_SIZE ->
  bv_unsigned (lden E b0) + Z.of_nat (length bs0) <= TASK_SIZE -> bv_unsigned (lden E b1) + Z.of_nat (length bs1) <= TASK_SIZE ->
  range_avoids (Hof E M model) (lden E (argl L 1)) 32 ->
  range_avoids (Hof E M model) (lden E b0) (length bs0) -> range_avoids (Hof E M model) (lden E b1) (length bs1) ->
  lwf (s_next L) len = true -> K [] ->
  (forall E' ms' m'', DEN segs LIMIT model0 mem0 E' (wv_post L len n) M ms' m'' -> agree (s_next L) E E' ->
     1 <= bv_unsigned (E' (s_next L)) <= Z.of_nat (length bs0 + length bs1) ->
     realizes_cfg segs cfg (mkCfg ms' m'') (t_emit (map (WriteEv (Z_to_bv 64 ch)) (skipn (Z.to_nat (bv_unsigned (E' (s_next L)))) (bs0 ++ bs1))) K)) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) (t_emit (map (WriteEv (Z_to_bv 64 ch)) (bs0 ++ bs1)) K).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model K ch b0 l0 b1 l1 len bs0 bs1 n Hd H7 H0 H2 Hch Hfd0 Hi0 Hi1 Hi2 Hi3 Hbuf0 Hbuf1 Hlen0 Hlen1 Hlen
    Hnb Hn Hn30 Hiok Hbok0 Hbok1 Havi Havb0 Havb1 Hwl HK0 Hk.
  set (bs := bs0 ++ bs1) in *.
  assert (Hlbs : length bs = (length bs0 + length bs1)%nat) by (unfold bs; apply length_app).
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (regs := ms_regs ms).
  set (x8 := ms_reg ms 17).
  set (iov := lden E (argl L 1)) in *.
  pose proof (bv_unsigned_in_range _ iov) as Riov. unfold bv_modulus in Riov. change (2 ^ Z.of_N 64) with two64 in Riov.
  assert (Hx8 : x8 = Z_to_bv 64 66) by exact (a7_const segs E L (restrict H ms) ms 66 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 ch) by exact (gpr_const segs E L (restrict H ms) ms 0 ch Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = iov) by exact (gpr_lin_k segs E L (restrict H ms) ms 1 Hsd eq_refl ltac:(lia)).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 2) by exact (gpr_const segs E L (restrict H ms) ms 2 2 Hsd eq_refl ltac:(lia) H2).
  assert (R10 : getr regs 10 = Z_to_bv 64 ch).
  { rewrite <- Hg0. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 0))); [reflexivity|]. exact (getr_gpr ms 0 ltac:(lia)). }
  assert (R11 : getr regs 11 = iov).
  { rewrite <- Hg1. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 1))); [reflexivity|]. exact (getr_gpr ms 1 ltac:(lia)). }
  set (iovs := [(lden E b0, lden E l0); (lden E b1, lden E l1)]).
  set (bss := [bs0; bs1]).
  assert (R12 : getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs))).
  { cbn [length iovs]. change (Z.of_nat 2) with 2%Z. rewrite <- Hg2. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 2))); [reflexivity|]. exact (getr_gpr ms 2 ltac:(lia)). }
  assert (R17 : getr regs 17 = Z_to_bv 64 66) by exact Hx8.
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hch32 : fd32 (getr regs 10) = Z_to_bv 64 ch) by (rewrite R10; apply fd32_id; rewrite u_small64 by (unfold two64; lia); lia).
  assert (Hfd : fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel (Z_to_bv 64 ch))) by (rewrite Hch32, Hfm; exact Hfd0).
  assert (Hw0 : w_is0 (Z_to_bv 64 ch) = false) by (unfold w_is0, bv_eqb; destruct Hch as [->| ->]; reflexivity).
  assert (Hu16 : bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) = bv_unsigned iov + 16) by (apply u64_small; unfold TASK_SIZE, two64 in *; lia).
  pose proof (bv_unsigned_in_range _ (lden E l0)) as Rl0. pose proof (bv_unsigned_in_range _ (lden E l1)) as Rl1.
  assert (Harr : iov_array segs (ms_mem ms) (getr regs 11) iovs).
  { unfold iovs. cbn [iov_array]. rewrite R11. split; [exact Hi0|]. split; [exact Hi1|]. split; [rewrite Hlen0; unfold TASK_SIZE in *; lia|].
    rewrite Hu16. split; [exact Hi2|]. split; [replace (bv_unsigned iov + 16 + 8) with (bv_unsigned iov + 24) by lia; exact Hi3|].
    split; [rewrite Hlen1; unfold TASK_SIZE in *; lia | exact I]. }
  assert (Hbo : iov_bufs_ok iovs).
  { unfold iovs; cbn [iov_bufs_ok]. rewrite Hlen0, Hlen1. split; [lia|]. split; [lia | exact I]. }
  assert (Hbb : iov_bufs segs (ms_mem ms) iovs bss).
  { unfold iovs, bss. cbn [iov_bufs]. split; [|split; [|exact I]].
    - unfold word_to_nat. rewrite Hlen0, Nat2Z.id. exact Hbuf0.
    - unfold word_to_nat. rewrite Hlen1, Nat2Z.id. exact Hbuf1. }
  assert (Htot : iovs_total iovs = Z.of_nat (length bs)) by (unfold iovs; cbn; rewrite Hlen0, Hlen1, Hlbs; lia).
  assert (Hcb : concat bss = bs) by (unfold bss, bs; cbn; rewrite app_nil_r; reflexivity).
  assert (Hiok' : bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE) by (rewrite R11; unfold iovs; cbn [length]; lia).
  pose proof (writev_ch_ok_iff segs regs (ms_pc_val ms) (ms_mem ms) model (Z_to_bv 64 ch) iovs bss) as Hspec.
  pose proof (writev_ch_no_unmodeled segs regs (ms_pc_val ms) (ms_mem ms) model (Z_to_bv 64 ch) iovs bss R17 Hfd Hw0 R12
                ltac:(unfold iovs; cbn; lia) Hiok' Harr Hbo Hbb ltac:(rewrite Htot; lia) ltac:(rewrite Htot; lia)) as Hnu.
  rewrite <- (sys_input_pend segs ms (getr regs 17) Hrom) in Hnu.
  assert (Hx8' : getr regs 17 = x8) by reflexivity. rewrite Hx8' in Hnu.
  set (CA := import_iovecs_accesses (mrb segs (ms_mem ms)) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs)))).
  assert (Hnb' : (1 <= length bs)%nat) by lia.
  set (EF := fun j : wr_index bs => ret_ci (Z_to_bv 64 (Z.of_nat (proj1_sig j))) (CA ++ (iov_prefix_accesses iovs (proj1_sig j) ++ []))).
  assert (Hspr : forall eff m' evs, syscall_spec (sys_input segs ms1 x8) model (Ok eff m' evs) <->
            exists j : wr_index bs, eff = EF j /\ m' = model /\ evs = map (WriteEv (Z_to_bv 64 ch)) (firstn (proj1_sig j) bs)).
  { intros eff m' evs. unfold ms1. rewrite (sys_input_pend segs ms x8 Hrom). fold regs. rewrite <- Hx8'.
    rewrite (Hspec eff m' evs R17 Hfd Hw0 R12 ltac:(unfold iovs; cbn; lia) Hiok' Harr Hbo Hbb ltac:(rewrite Htot; lia) ltac:(rewrite Htot; lia)).
    rewrite Hcb. split.
    - intros (k & Hk' & -> & -> & ->). exists (exist _ k Hk'). unfold EF. cbn [proj1_sig]. auto.
    - intros ([k Hk'] & -> & -> & ->). exists k. unfold EF. cbn [proj1_sig]. auto. }
  assert (HCA : ranges_avoid H CA).
  { unfold CA, import_iovecs_accesses. unfold iovs. cbn [length]. change (Z.of_nat 2) with 2%Z.
    replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 1)) with false by reflexivity.
    replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 0)) with false by reflexivity.
    rewrite u_small64 by (unfold two64; lia). replace (IOV_MAX <? 2)%Z with false by reflexivity.
    destruct (negb (access_okb (getr regs 11) (16 * 2))); [apply ranges_avoid_nil|].
    change (word_to_nat (Z_to_bv 64 2)) with 2%nat. cbn [copy_iovecs_accesses].
    apply ranges_avoid_cons; [rewrite R11; exact (ra_le H iov 32 16 ltac:(lia) Havi)|].
    destruct (read_iovec_entry (mrb segs (ms_mem ms)) (getr regs 11)); try apply ranges_avoid_nil.
    apply ranges_avoid_cons; [|destruct (read_iovec_entry (mrb segs (ms_mem ms)) (getr regs 11 + 16)%bv); apply ranges_avoid_nil].
    rewrite R11. intros kk Hkk. replace (woff (iov + 16)%bv kk) with (woff iov (16 + kk)); [apply Havi; lia|].
    unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite bv_add_unsigned. unfold bv_wrap.
    change (bv_unsigned (16 : word)) with 16. rewrite Zplus_mod_idemp_l. f_equal. lia. }
  assert (Hacc : forall j : wr_index bs, ranges_avoid H (syscall_effect_accesses (EF j))).
  { intros [k Hk']. unfold EF, ret_ci, syscall_effect_accesses. cbn [eff_copyins eff_writes proj1_sig]. rewrite !app_nil_r.
    apply ranges_avoid_app; [exact HCA|].
    unfold iovs. apply (ipa_bound (lden E b0) (lden E l0) bs0 _ k H Hlen0 Havb0).
    apply (ipa_bound (lden E b1) (lden E l1) bs1 [] _ H Hlen1 Havb1).
    assert (E0 : forall x, iov_prefix_accesses [] x = []) by (intros [|x]; reflexivity). rewrite E0. apply ranges_avoid_nil. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc segs cfg H (AM model0 E M) ms1 model x8 (wr_index bs) EF (fun _ => model)
             (fun j => map (WriteEv (Z_to_bv 64 ch)) (firstn (proj1_sig j) bs))
             (fun j => t_emit (map (WriteEv (Z_to_bv 64 ch)) (skipn (proj1_sig j) bs)) K) (wr_full bs Hnb') (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros j. apply Hspr. exists j. auto.
    + intros eff m' evs Hs. apply Hspr in Hs as (j & -> & -> & ->). exists j. auto.
    + exact Hnu.
    + intros eff. apply not_spurious_uninjected. cbn [in_sysno sys_input]. rewrite Hx8. reflexivity.
    + intros _. exact Hh.
    + intros _. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact Hminv.
    + exact Hacc.
    + intros [k Hk'] m'' Hinv'' Hsb''. cbn [proj1_sig].
      set (w := Z_to_bv 64 (Z.of_nat k)).
      assert (Hwu : bv_unsigned w = Z.of_nat k) by (unfold w; apply u_small64; unfold two64; lia).
      pose proof (den_ret_fresh segs LIMIT mem0 model0 E L M ms model w (fun x => [FRange x 1 n; FRange (lsub len x) 0 n])
                    (CA ++ (iov_prefix_accesses iovs k ++ [])) m'' Hd) as HD'.
      assert (HD2 : DEN segs LIMIT model0 mem0 (upd E (s_next L) w) (wv_post L len n) M
                  (advance_past_svc (apply_effect ms1 (EF (exist _ k Hk')))) m'').
      { apply HD'; [|exact Hinv'' | exact Hsb''].
        intros E' Ha'. assert (He : E' (s_next L) = w) by (rewrite <- (Ha' (s_next L) ltac:(lia)); unfold upd; rewrite Pos.eqb_refl; reflexivity).
        assert (Hle : lden E' len = lden E len).
        { rewrite (lden_agree_wf (s_next L) E E' len Hwl); [reflexivity|].
          intros x Hx. rewrite <- (Ha' x ltac:(lia)). unfold upd. destruct (Pos.eqb x (s_next L)) eqn:Ex; [apply Pos.eqb_eq in Ex; lia | reflexivity]. }
        constructor; [|constructor; [|constructor]].
        - cbn [fact_ok]. rewrite lden_lvar, He, Hwu. lia.
        - cbn [fact_ok]. rewrite lden_lsub, lden_lvar, He, Hle. rewrite bv_sub_unsigned, Hwu, Hlen. unfold bv_wrap.
          rewrite Z.mod_small by (change (bv_modulus 64) with two64; unfold two64; lia). lia. }
      eapply rzc_conseq; [apply (Hk (upd E (s_next L) w) _ m'' HD2 (agree_upd _ E w))|].
      * unfold upd. rewrite Pos.eqb_refl. rewrite Hwu. lia.
      * unfold upd. rewrite Pos.eqb_refl. rewrite Hwu, Nat2Z.id. apply t_eq_refl.
  - apply (t_alt_wall (Z_to_bv 64 ch) bs K HK0 Hnb').
Qed.
(* [comment removed for export] *)
Local Abbreviation PEND regs pc mem := (epend regs pc mem (seg_rom segs) (getr regs 17)).
#[using="mem0"] Lemma writev_ch_zero_iff : forall regs pc mem model (ch : word) iovs eff m' evs,
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs mem (getr regs 11) iovs -> iov_bufs_ok iovs -> iovs_total iovs = 0 ->
  let CA := import_iovecs_accesses (mrb segs mem) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs))) in
  (syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model (Ok eff m' evs) <->
   eff = ret_ci (Z_to_bv 64 0) CA /\ m' = model /\ evs = []).
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model ch iovs eff m' evs H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Ht0 CA.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (M0 : in_mem i = mrb segs mem) by reflexivity.
  assert (Hno : bv_unsigned (in_sysno i) = 66%Z) by (cbn [in_sysno i sys_input]; rewrite H17; reflexivity).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  rewrite (syscall_spec_66 i model _ Hno). rewrite A0, A1, A2, H12.
  unfold writev_spec. rewrite bind_input, bind_get_model. rewrite Hfd, Hch. rewrite M0, Hcnt32.
  rewrite record_copyins_ok_iff.
  rewrite (import_iovecs_of_array segs mem iovs (getr regs 11) Hcnt Hiok Harr Hbok). fold CA.
  cbv beta iota zeta. rewrite Hcap, Ht0. cbn [Z.eqb].
  unfold ret_only, pure. split.
  - intros (eff0 & Hs & ->). injection Hs as E1 E2 E3. subst. split; [|split; reflexivity].
    unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros (-> & -> & ->). exists (mkEffect (Z_to_bv 64 0) [] []). split; [reflexivity|].
    unfold with_copyins, ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. rewrite app_nil_r. reflexivity.
Qed.

#[using="mem0"] Lemma writev_ch_zero_no_unmodeled : forall regs pc mem model (ch : word) iovs,
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs mem (getr regs 11) iovs -> iov_bufs_ok iovs -> iovs_total iovs = 0 ->
  ~ syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model Unmodeled.
Proof. LiaFast.lf_pins (fun (mem0 : LiaFast.U) => LiaFast.u0).
  intros regs pc mem model ch iovs H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Ht0.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (M0 : in_mem i = mrb segs mem) by reflexivity.
  assert (Hno : bv_unsigned (in_sysno i) = 66%Z) by (cbn [in_sysno i sys_input]; rewrite H17; reflexivity).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  intros Hs. rewrite (syscall_spec_66 i model _ Hno) in Hs. rewrite A0, A1, A2, H12 in Hs.
  unfold writev_spec in Hs. rewrite bind_input, bind_get_model in Hs. rewrite Hfd, Hch in Hs.
  rewrite M0, Hcnt32 in Hs. apply record_copyins_unmodeled_iff in Hs.
  rewrite (import_iovecs_of_array segs mem iovs (getr regs 11) Hcnt Hiok Harr Hbok) in Hs.
  cbv beta iota zeta in Hs. rewrite Hcap, Ht0 in Hs. cbn [Z.eqb] in Hs.
  unfold ret_only, pure in Hs. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_writev0 : forall model0 E L M ms model (K : TSet) (ch : Z) (b l : lin),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  a7c L = Some 66 -> arg L 0 = Some ch -> arg L 2 = Some 1 -> (ch = 1 \/ ch = 2) ->
  fd_lookup (m_fds model0) (Z_to_bv 64 ch) = Some (FdChannel (Z_to_bv 64 ch)) ->
  rdn segs (ms_mem ms) (lden E (argl L 1)) 8 = Some (word_to_le_bytes 8 (lden E b)) ->
  rdn segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (argl L 1)) + 8)) 8 = Some (word_to_le_bytes 8 (lden E l)) ->
  bv_unsigned (lden E l) = 0 -> bv_unsigned (lden E b) <= TASK_SIZE ->
  bv_unsigned (lden E (argl L 1)) + 16 <= TASK_SIZE -> range_avoids (Hof E M model) (lden E (argl L 1)) 16 ->
  (forall ms' m'', DEN segs LIMIT model0 mem0 E (ret_post L (lconst 0)) M ms' m'' -> realizes_cfg segs cfg (mkCfg ms' m'') K) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E L M ms model K ch b l Hd H7 H0 H2 Hch Hfd0 Hi0 Hi1 Hl0 Hbok Hiok Havi Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (regs := ms_regs ms).
  set (x8 := ms_reg ms 17).
  set (iov := lden E (argl L 1)) in *.
  pose proof (bv_unsigned_in_range _ iov) as Riov. unfold bv_modulus in Riov. change (2 ^ Z.of_N 64) with two64 in Riov.
  assert (Hx8 : x8 = Z_to_bv 64 66) by exact (a7_const segs E L (restrict H ms) ms 66 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 ch) by exact (gpr_const segs E L (restrict H ms) ms 0 ch Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = iov) by exact (gpr_lin_k segs E L (restrict H ms) ms 1 Hsd eq_refl ltac:(lia)).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 1) by exact (gpr_const segs E L (restrict H ms) ms 2 1 Hsd eq_refl ltac:(lia) H2).
  assert (R10 : getr regs 10 = Z_to_bv 64 ch).
  { rewrite <- Hg0. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 0))); [reflexivity|]. exact (getr_gpr ms 0 ltac:(lia)). }
  assert (R11 : getr regs 11 = iov).
  { rewrite <- Hg1. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 1))); [reflexivity|]. exact (getr_gpr ms 1 ltac:(lia)). }
  set (iovs := [(lden E b, lden E l)]).
  assert (R12 : getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs))).
  { cbn [length iovs]. change (Z.of_nat 1) with 1%Z. rewrite <- Hg2. transitivity (getr (ms_regs ms) (Z_to_bv 5 (10 + Z.of_nat 2))); [reflexivity|]. exact (getr_gpr ms 2 ltac:(lia)). }
  assert (R17 : getr regs 17 = Z_to_bv 64 66) by exact Hx8.
  assert (Hfm : m_fds model = m_fds model0) by (destruct Hvmo as (H1' & _); unfold m_fds; rewrite H1'; reflexivity).
  assert (Hch32 : fd32 (getr regs 10) = Z_to_bv 64 ch) by (rewrite R10; apply fd32_id; rewrite u_small64 by (unfold two64; lia); lia).
  assert (Hfd : fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel (Z_to_bv 64 ch))) by (rewrite Hch32, Hfm; exact Hfd0).
  assert (Hw0 : w_is0 (Z_to_bv 64 ch) = false) by (unfold w_is0, bv_eqb; destruct Hch as [->| ->]; reflexivity).
  assert (Harr : iov_array segs (ms_mem ms) (getr regs 11) iovs).
  { unfold iovs. cbn [iov_array]. rewrite R11. split; [exact Hi0|]. split; [exact Hi1|]. split; [rewrite Hl0; lia | exact I]. }
  assert (Hbo : iov_bufs_ok iovs) by (unfold iovs; cbn [iov_bufs_ok]; rewrite Hl0; split; [lia | exact I]).
  assert (Htot : iovs_total iovs = 0) by (unfold iovs; cbn; rewrite Hl0; lia).
  assert (Hiok' : bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE) by (rewrite R11; unfold iovs; cbn [length]; lia).
  pose proof (writev_ch_zero_no_unmodeled regs (ms_pc_val ms) (ms_mem ms) model (Z_to_bv 64 ch) iovs R17 Hfd Hw0 R12
                ltac:(unfold iovs; cbn; lia) Hiok' Harr Hbo Htot) as Hnu.
  rewrite <- (sys_input_pend segs ms (getr regs 17) Hrom) in Hnu.
  assert (Hx8' : getr regs 17 = x8) by reflexivity. rewrite Hx8' in Hnu.
  set (CA := import_iovecs_accesses (mrb segs (ms_mem ms)) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs)))).
  assert (Hspr : forall eff m' evs, syscall_spec (sys_input segs ms1 x8) model (Ok eff m' evs) <->
            eff = ret_ci (Z_to_bv 64 0) CA /\ m' = model /\ evs = []).
  { intros eff m' evs. unfold ms1. rewrite (sys_input_pend segs ms x8 Hrom). fold regs. rewrite <- Hx8'.
    exact (writev_ch_zero_iff regs (ms_pc_val ms) (ms_mem ms) model (Z_to_bv 64 ch) iovs eff m' evs R17 Hfd Hw0 R12
             ltac:(unfold iovs; cbn; lia) Hiok' Harr Hbo Htot). }
  assert (HCA : ranges_avoid H CA).
  { unfold CA, import_iovecs_accesses. unfold iovs. cbn [length]. change (Z.of_nat 1) with 1%Z. rewrite bv_eqb_refl.
    destruct (negb (access_okb (getr regs 11) 16)); [apply ranges_avoid_nil|].
    apply ranges_avoid_cons; [rewrite R11; exact Havi | apply ranges_avoid_nil]. }
  assert (Hwv : lwf (s_next L) (lconst 0) = true) by reflexivity.
  assert (Hcont : forall m'', MInv (AM model0 E M) m'' -> same_but_materialized model m'' ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (ret_ci (Z_to_bv 64 0) CA))) m'') K).
  { intros m'' Hinv'' Hsb''. apply Hk.
    pose proof (den_ret_ci0 segs LIMIT mem0 model0 E L M ms model (lconst 0) CA m'' Hd Hwv Hinv'' Hsb'') as HD.
    rewrite lden_lconst in HD. exact HD. }
  eapply rzc_conseq.
  - apply (rzc_sys_acc segs cfg H (AM model0 E M) ms1 model x8 unit (fun _ => ret_ci (Z_to_bv 64 0) CA) (fun _ => model)
             (fun _ => []) (fun _ => K) tt (A_wf_app _ _ Hawf (A_wf_blobA _)) Hh (svc_set_pending ms)).
    + intros []. apply Hspr. auto.
    + intros eff m' evs Hs. apply Hspr in Hs as (-> & -> & ->). exists tt. auto.
    + exact Hnu.
    + intros eff. apply not_spurious_uninjected. cbn [in_sysno sys_input]. rewrite Hx8. reflexivity.
    + intros _. exact Hh.
    + intros _. apply lazy_cover_mkH_app. intros x Hx'. exact Hx'.
    + intros _. exact Hminv.
    + intros _. unfold ret_ci, syscall_effect_accesses. cbn [eff_copyins eff_writes]. rewrite app_nil_r. exact HCA.
    + intros _ m'' Hinv'' Hsb''. exact (Hcont m'' Hinv'' Hsb'').
  - apply t_alt_const_nil; [exact tt|].
    exact (realizes_cfg_nonempty segs cfg _ _ (Hcont model Hminv (same_but_materialized_refl _))).
Qed.
End WvG.
