(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioLoop. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.LibWritev OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.BoStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.BoStdioWrite_run1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioLoop OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.Bo_code_f34c8_f34f8 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.Bo_code_f3610_f37a8 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.Bo_code_f3bf8_f3d9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.Bo_code_f3fbc_f423c OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.Bo_code_f43a4_f4964 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.Bo_code_edf44_ee420 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStdioWrite_run2.Bo_code_ee7cc_ef130.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.
From Stdlib Require Import FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)


Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].
Section FPGen2.
Context {fx : FPState}.
Variable R : shape_rel RSEGS.


Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0x10a5c8 <= f)%Z -> (f + 232 <= 0x10a7a0)%Z ->
  LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
  sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof.
  intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
  constructor.
  - intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
    unfold mem_sw2. do 3 wout1.
    rewrite (E x) by lia.
    unfold mem_sw1. do 13 wout1. reflexivity.
  - unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    eapply mem_grows_trans; [|exact G].
    unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    apply mem_grows_refl.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
Qed.

Lemma pc_644e4 : v_addi (0xf3694 : word) 4 = (0xf3698 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Lemma mclean_sw1 : forall H mem (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l : word),
  mclean H mem -> hid_off H (su - 112) 112 -> (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  mclean H (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l).
Proof.
  intros H mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l MC AV SUlo SUhi. unfold mem_sw1.
  repeat (apply mclean_wbytes; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm;
                                   eapply hid_off_sub; [exact AV | lia | lia]
                                 | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ]).
  exact MC.
Qed.

Lemma mclean_sw2 : forall H m (f : Z) (bufp bufsz : word),
  mclean H m -> hid_off H f 232 -> (0x10a5c8 <= f)%Z -> (f + 232 <= 0x10a7a0)%Z ->
  mclean H (mem_sw2 m f bufp bufsz).
Proof.
  intros H m f bufp bufsz MC AV Flo Fhi. unfold mem_sw2.
  repeat (apply mclean_wbytes; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm;
                                   eapply hid_off_sub; [exact AV | lia | lia]
                                 | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ]).
  exact MC.
Qed.

Section MAIN.
  Hypothesis HW1 : HYP_writev1_wall_stmt R.
  Hypothesis HW2 : HYP_writev2_wall_stmt R.
  Hypothesis HW0 : HYP_writev1_zero_stmt R.

Theorem both_stdio_write :
  forall (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte)
         regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  H_off_segments RSEGS H -> wx_segs_nowrap RSEGS -> A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  mclean H mem ->
  hid_off H (su - 112) 112 -> hid_off H f 232 ->
  hid_off H wb (Z.of_nat (length pending)) -> hid_off H (bv_unsigned s) (Z.of_nat (length extra)) ->
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0x10a5c8 <= f)%Z -> (f + 232 <= 0x10a7a0)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_halted model = None ->
  (0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem' mdl',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' -> mclean H mem' ->
     MInv A mdl' -> same_but_materialized model mdl' ->
     R (mkCfg (mkst regs' ret (munrestrict H F mem') (seg_rom RSEGS)) mdl') K) ->
  R (mkCfg (mkst regs (0xf360c : word) (munrestrict H F mem) (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
  intros H A F regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
         HH Hwx Awf MI0 Hcov0 MC0 AVfr AVf AVp AVe
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hh WBP WPhi
         LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
  assert (MAX : (0 <= Z.of_nat (length pending) + Z.of_nat (length extra))%Z) by lia.
  assert (MK0 : MOK A model model) by (split; [exact MI0 | apply same_but_materialized_refl]).
  pose proof (rzR R H A F model HH Hwx Awf Hh Hcov0) as rzr.
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }
  (* [comment removed for export] *)
  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x6613c0) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
  assert (MC1 : mclean H mem1) by (subst mem1; apply mclean_sw1; assumption).
  (* [comment removed for export] *)
  assert (HK' : forall regs' m mdl',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m -> MOK A model mdl' ->
     R (mkCfg (mkst regs' ret (munrestrict H F (mem_sw2 m f bufp bufsz)) (seg_rom RSEGS)) mdl') K).
  { intros. match goal with HL : LM _ _ _, HM : MOK _ _ _ |- _ =>
      destruct HM as [HM1 HM2]; apply HK;   (* [comment removed for export] *)
      [ assumption .. | eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | exact HL]
      | apply mclean_sw2; [ | exact AVf | exact Flo | exact Fhi] | exact HM1 | exact HM2 ] end.
    match goal with HL : LM _ _ _ |- _ => destruct HL as [E G] end.
    intros x Hx. pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) (su - 104)) as [L|Ge]; [rewrite (E x) by lia; exact (MC1 x Hx)|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (su - 72)) as [L2|Ge2]; [|rewrite (E x) by lia; exact (MC1 x Hx)].
    exfalso. pose proof (AVfr x ltac:(lia)). congruence. }
  pose proof (finish_nil R su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 H A F model K
                HH Hwx Awf MC1 AVfr SUlo SUhi Flo Fhi Hh Hcov0 Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
  pose proof (loop1 R su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 H A F model K
                HH Hwx Awf HW1 MC1 AVfr SUlo SUhi Flo Fhi FD Hfd Hh Hcov0 Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2 R su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 H A F model K
                HH Hwx Awf HW1 HW2 MC1 AVfr SUlo SUhi Flo Fhi FD Hfd Hh Hcov0 Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  - (* [comment removed for export] *)
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply rzr; [exact MK0 | exact MC0 | exact RUN1 |]; clear RUN1; intros mdlA MKA MCA.
    lazymatch goal with |- sr_rel _ _ (mkCfg (mkst _ _ (munrestrict _ _ ?M) _) _) _ =>
      replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    destruct extra as [|x0 extra'].
    + (* [comment removed for export] *)
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (HW0 H A F regs1 (0xf3694 : word) mem1 mdlA W_f36a0 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K)
                HH Hwx Awf (proj1 MKA) (MOK_cover H A model Hcov0 mdlA MKA) MC1 F_f36a0 E_f36a0
                (MOK_halted A model Hh mdlA MKA) ltac:(rewrite (MOK_fds A model mdlA MKA); exact Hfd) FD
                R17 R10 R11 R12 M88);
        [ | apply hid_off_range_avoids; [u_norm; lia | u_norm; eapply hid_off_sub; [exact AVfr | lia | lia]]
        | u_norm; unfold TASK_SIZE in *; lia | unfold TASK_SIZE in *; lia | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      intros mdlB MIB SBB. pose proof (MOK_next A model mdlA mdlB MKA MIB SBB) as MKB.
      rewrite pc_644e4.
      destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      eapply rzr; [exact MKB | exact MC1 | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
      apply FIN; [|exact LM1|exact MKC].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    + (* [comment removed for export] *)
      eapply (HW1 H A F regs1 (0xf3694 : word) mem1 mdlA W_f36a0 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') K
                HH Hwx Awf (proj1 MKA) (MOK_cover H A model Hcov0 mdlA MKA) MC1 F_f36a0 E_f36a0
                (MOK_halted A model Hh mdlA MKA) ltac:(rewrite (MOK_fds A model mdlA MKA); exact Hfd) FD
                R17 R10 R11 R12 M88);
        [ | | apply hid_off_range_avoids; [u_norm; lia | u_norm; eapply hid_off_sub; [exact AVfr | lia | lia]]
        | | | | | | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. apply hid_off_range_avoids; [lia | exact AVe].
      * u_norm. unfold TASK_SIZE in *. lia.
      * unfold TASK_SIZE in *. lia.
      * cbn [length] in LENE. lia.
      * lia.
      * intros k mdlB K1 K2 MIB SBB. pose proof (MOK_next A model mdlA mdlB MKA MIB SBB) as MKB. rewrite pc_644e4.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           eapply rzr; [exact MKB | exact MC1 | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply FIN; [|exact LM1|exact MKC].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           eapply rzr; [exact MKB | exact MC1 | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
           apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra') mdlC); try lia.
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact MKC.
           ++ exact AVe.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  - (* [comment removed for export] *)
    destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply rzr; [exact MK0 | exact MC0 | exact RUN1 |]; clear RUN1; intros mdlA MKA MCA. fold mem1.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    eapply (HW2 H A F regs1 (0xf3694 : word) mem1 mdlA W_f36a0 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K
              HH Hwx Awf (proj1 MKA) (MOK_cover H A model Hcov0 mdlA MKA) MC1 F_f36a0 E_f36a0
              (MOK_halted A model Hh mdlA MKA) ltac:(rewrite (MOK_fds A model mdlA MKA); exact Hfd) FD
              R17 R10 R11 R12 M104);
      [ | | | | | apply hid_off_range_avoids; [u_norm; lia | u_norm; eapply hid_off_sub; [exact AVfr | lia | lia]]
      | | | | | | | | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia.
      apply hid_off_range_avoids; [u_norm; lia | u_norm; exact AVp].
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. apply hid_off_range_avoids; [lia | exact AVe].
    + u_norm. unfold TASK_SIZE in *. lia.
    + u_norm. unfold TASK_SIZE in *. lia.
    + unfold TASK_SIZE in *. lia.
    + u_norm. unfold TASK_SIZE in *. lia.
    + u_norm. unfold TASK_SIZE in *. lia.
    + intros k mdlB K1 K2 MIB SBB. pose proof (MOK_next A model mdlA mdlB MKA MIB SBB) as MKB.
      rewrite pc_644e4. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        eapply rzr; [exact MKB | exact MC1 | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply FIN; [|exact LM1|exact MKC].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        eapply rzr; [exact MKB | exact MC1 | exact RUN2 |]; clear RUN2; intros mdlC MKC MCC.
        apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra mdlC); try lia.
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact MKC.
        -- u_norm. exact AVp.
        -- exact AVe.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
Qed.
End MAIN.
End FPGen2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
