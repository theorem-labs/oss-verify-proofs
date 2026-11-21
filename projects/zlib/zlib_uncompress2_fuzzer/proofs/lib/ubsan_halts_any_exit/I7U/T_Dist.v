(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S Require S_MatchL S_DistL.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U Require TBase.

Module T_MatchL.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_MatchL.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_MLOOP_T : Z := 95512.
Definition L_MAFTER_T : Z := 95560.
Definition L_SETLEN_T : Z := 95584.

Lemma mem_u32_u8_t {RCa1 : RunCtx}  : forall M a v, mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u8 (run_segments R_segs rc_inp rc_sp rc_mb) M a v.
Proof.
  intros M a v H. unfold mem_u32, mem_u8, mem_is in *.
  pose proof (mem_is_firstn (run_segments R_segs rc_inp rc_sp rc_mb) M a (Z_to_le_bytes 4 v) 1 H ltac:(cbn; lia_std)) as H1.
  cbn [firstn Z_to_le_bytes] in H1. exact H1.
Qed.

Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.

Ltac tstore_arrP fd Ha i HP HPres :=
  lazymatch type of Ha with
  | mem_arr ?k ?segs ?M ?base ?n ?f =>
      let pc := zpc in
      fd pc ltac:(fun F E D =>
        eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm);
      lazymatch goal with
      | |- realizes _ (zcfg _ _ _ (wbytes M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
          apply (mem_arr_upd segs k M base n f a i v) in Ha; [| zlia | zlia];
          (let kn := eval cbv in (Z.to_nat k) in change (Z.to_nat k) with kn in Ha);
          (let HP' := fresh in pose proof (HPres M a v HP ltac:(zlia) ltac:(zlia)) as HP'; clear HP; rename HP' into HP);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia]
                    | idtac "tstore_arrP: mem_arr fact dropped at array store" a; clear H ]
          end;
          zmem_post
      end
  end.

Lemma out_arr_t {RCa1 : RunCtx}  : forall M ob osz, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> 0 <= ob -> 0 <= osz -> ob + osz <= two64 ->
  exists fo, mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo /\ (forall i, 0 <= i < osz -> 0 <= fo i < 256).
Proof.
  intros M ob osz W H1 H2 H3. destruct (mem_wr_arr_exists_R M ob osz W H1 H2 H3) as [fo [A B]].
  exists fo. split; [exact A | intros i _; apply B].
Qed.

Lemma mloop_w_t {RCa1 : RunCtx}  : forall (N : nat) (P : mem -> Prop) Rb l M MD T (ob osz w wn si c m : Z) (fo fw : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA1 = w + si -> zget_l Rb l kS1 = ob + c -> zget_l Rb l kA3 = w + si -> zget_l Rb l kA4 = ob + c ->
  zget_l Rb l kA2 = m ->
  1 <= m -> m <= Z.of_nat N -> m < 2147483648 -> 0 <= si -> si + m <= wn -> 0 <= c -> c + m <= osz ->
  0 < ob -> ob + osz <= 140737488355328 -> 0 < w -> w + wn <= 140737488355328 -> ZSEP (w + wn <= ob \/ ob + osz <= w) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M w wn fw -> (forall i, 0 <= i < wn -> 0 <= fw i < 256) ->
  P M -> (forall M' a v, P M' -> ob <= a -> a + 1 <= ob + osz -> P (wbytes M' (w64 a) (Z_to_le_bytes 1 v))) ->
  (forall R' M' (fo' : Z -> Z),
     zget R' kA1 = w + si + m -> zget R' kS1 = ob + c + m -> zget R' kA5 = ob + c + m -> zget R' kA2 = 0 ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 -> zget R' kRA = zget_l Rb l kRA ->
     zget R' kS10 = zget_l Rb l kS10 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS9 = zget_l Rb l kS9 ->
     zget R' kS3 = zget_l Rb l kS3 -> zget R' kS11 = zget_l Rb l kS11 -> zget R' kA0 = zget_l Rb l kA0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' w wn fw -> P M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MAFTER_T (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MLOOP_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T ob osz w wn si c m fo fw Hh La1 Ls2 La3 La4 La2 Hm1 Hm2 Hm31 Hsi1 Hsi2 Hc1 Hc2
    Hob1 Hob2 Hw1 Hw2 Swob Wob HOB Rfo Hwin Rfw HP HPres K; [lia|].
  zkeys. unfold L_MLOOP_T, L_MAFTER_T in *. pose proof two64_eq as TW64.
  pose proof (Rfw si ltac:(lia)) as Rb0.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  tld1 Hwin si Rfw.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstore_arrP Rfd HOB c HP HPres.
  zstep Rfd.
  pose proof (zfupd_byte fo c (fw si) 0 osz Rfo Rb0) as Rfo1.
  destruct (Z.eq_dec m 1) as [E1|N1].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fw si))) end;
      try zreg; try assumption.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T ob osz w wn (si + 1) (c + 1) (m - 1) (zfupd fo c (fw si)) fw Hh) end;
      try zreg; try assumption; try lia.
    intros R' M' fo' Ma1 Ms2 Ma5 Ma2 E3 E4 E5 E28 E9 E2 E26 E24 E20 E10 E27 E11 Wob' HOB' Rfo' Hwin' HP'.
    eapply (K R' M' fo'); try assumption; try lia.
    all: cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; assumption.
Qed.

Lemma mloop_o_t {RCa1 : RunCtx}  : forall (N : nat) (P : mem -> Prop) Rb l M MD T (ob osz s c m : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA1 = ob + s -> zget_l Rb l kS1 = ob + c -> zget_l Rb l kA3 = ob + s -> zget_l Rb l kA4 = ob + c ->
  zget_l Rb l kA2 = m ->
  1 <= m -> m <= Z.of_nat N -> m < 2147483648 -> 0 <= s -> s <= c -> c + m <= osz ->
  0 < ob -> ob + osz <= 140737488355328 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  P M -> (forall M' a v, P M' -> ob <= a -> a + 1 <= ob + osz -> P (wbytes M' (w64 a) (Z_to_le_bytes 1 v))) ->
  (forall R' M' (fo' : Z -> Z),
     zget R' kA1 = ob + s + m -> zget R' kS1 = ob + c + m -> zget R' kA5 = ob + c + m -> zget R' kA2 = 0 ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 -> zget R' kRA = zget_l Rb l kRA ->
     zget R' kS10 = zget_l Rb l kS10 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS9 = zget_l Rb l kS9 ->
     zget R' kS3 = zget_l Rb l kS3 -> zget R' kS11 = zget_l Rb l kS11 -> zget R' kA0 = zget_l Rb l kA0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     P M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MAFTER_T (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MLOOP_T (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T ob osz s c m fo Hh La1 Ls2 La3 La4 La2 Hm1 Hm2 Hm31 Hs1 Hs2 Hc2
    Hob1 Hob2 Wob HOB Rfo HP HPres K; [lia|].
  zkeys. unfold L_MLOOP_T, L_MAFTER_T in *. pose proof two64_eq as TW64.
  pose proof (Rfo s ltac:(lia)) as Rb0.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  zbr Rfd false.
  tld1 HOB s Rfo.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstore_arrP Rfd HOB c HP HPres.
  zstep Rfd.
  pose proof (zfupd_byte fo c (fo s) 0 osz Rfo Rb0) as Rfo1.
  destruct (Z.eq_dec m 1) as [E1|N1].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fo s))) end;
      try zreg; try assumption.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T ob osz (s + 1) (c + 1) (m - 1) (zfupd fo c (fo s)) Hh) end;
      try zreg; try assumption; try lia.
    intros R' M' fo' Ma1 Ms2 Ma5 Ma2 E3 E4 E5 E28 E9 E2 E26 E24 E20 E10 E27 E11 Wob' HOB' Rfo' HP'.
    eapply (K R' M' fo'); try assumption; try lia.
    all: cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; assumption.
Qed.

Definition PM {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (M0 : mem) (md : Z) (st : ist) (lf cf : Z -> Z) (M : mem) : Prop :=
  s_std cx fin M /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) md /\ st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ s_ret cx st M /\ s_lo cx st M /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf /\
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx).

Lemma PM_store {RCa1 : RunCtx}  : forall cx fin M0 md st lf cf M a v,
  ctx_ok ROMHI_T cx -> PM cx fin M0 md st lf cf M -> c_ob cx <= a -> a + 1 <= c_ob cx + c_osz cx ->
  PM cx fin M0 md st lf cf (wbytes M (w64 a) (Z_to_le_bytes 1 v)).
Proof.
  intros cx fin M0 md st lf cf M a v CX H Ha1 Ha2.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & Hm & SR & RET & SLO & HL & HC & HP0). open_std STD. unfold PM. icx_cbn. cbv [N_LENS N_CODES] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zmem_transport M a (Z_to_le_bytes 1 v).
  split_conj; try assumption; try close_std; try exact HAG.
Qed.
End T_MatchL.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U Require T_DistL.

Module T_Match.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_MatchL.
Import T_MatchL.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_M08 : Z := 95448.
Definition L_M28 : Z := 95480.
Definition L_M30 : Z := 95488.
Definition L_MLEFT0 : Z := 96300.

Definition m_regs (u p q n ob : Z) (K0 : positive -> Z) (cin cout hold bits dput : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -256 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kS2 = u /\ zget R kRA = 16209 /\
  zget R kS10 = q + cin /\ zget R kS7 = n - cin /\ zget R kS9 = hold /\ zget R kS3 = bits /\
  zget R kS1 = ob + cout + dput.
Ltac open_mregs H := unfold m_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS1 kS9 kS4 kS6 kS9 kS7 kS5 kS10 kS11 kS0 kT3 kT4 kT5 kT6] in H; destr_conj H.
Ltac close_mregs := unfold m_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS1 kS9 kS4 kS6 kS9 kS7 kS5 kS10 kS11 kS0 kT3 kT4 kT5 kT6]; split_conj;
                   first [zreg | match goal with |- ?G => idtac "close_mregs FAIL" G; fail end].

Theorem match_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = MATCH -> sinv cx st lf cf ->
  s_regs_disp cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MATCH (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (PR3' : out = osz - cout0) by (destruct PR3 as [E | [_ C]]; [exact E | exfalso; clear - C; cbv [CHECK MATCH] in C; lia]).
  clear PR3. rename PR3' into PR3.
  assert (HMA : 1 <= length /\ length < 65536 /\ offset < 98304)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : MATCH = MATCH -> _ |- _ => exact (H eq_refl) end).
  dand HMA as (HL1 & HL16 & HO17). clear MODE_.
  unfold s_regs_disp, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. destruct SLO as [LFT OUT]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_MATCH, L_M08, L_M28, L_M30, L_MLEFT0, L_MLOOP_T, L_MAFTER_T, L_SETLEN_T, L_DISP, L_LEAVE_LD in *.
  cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  open_K K. clear KRD KRD1 KB0 KB5 KB5B KB1 KL KLL2 KRT.
  zstep Rfd.
  destruct (Z.eq_dec (osz - cout) 0) as [Hleft0 | Hleft].
  { zbr Rfd true.
    clear LFT.
    tstep1 Rfd.
    unfold KLEAVE_LD in KLL. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf cf SI0) end.
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - unfold s_lo; icx_cbn. rewrite Hleft0. split; assumption.
    - sbk.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  zbr Rfd false. clear KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  pose proof CST as CS. unfold i_cst in CS. icx_cbn. dand CS as (_ & _ & _ & _ & _ & _ & C60 & C72 & C7144).
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & _ & _ & Q56 & _).
  unfold WIN in WIN_. icx_cbn. cbv [WIN_SIZE] in WIN_. destruct WIN_ as [WIN0 WIN1].
  assert (Hwh32 : whave <= 32768 /\ wnext <= 32768) by (destruct (Z.eq_dec w 0) as [E|E]; [destruct (WIN0 E) | destruct (WIN1 E)]; lia).
  assert (JA : forall R' M' (copy : Z),
    m_regs u p q n ob K0 cin cout hold bits copy R' -> zget R' kA5 = ob + cout + copy ->
    1 <= copy -> copy <= length -> copy <= osz - cout ->
    PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 MATCH
       (st_upd (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
               MATCH copy (length - copy)) lf cf M' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95560 (zupd R' []) M' MD) T).
  { intros R' M' copy MR G15 Hc1 Hc2 Hc3 HPM. open_mregs MR. cbv [kA5] in G15.
    clear LFT OUT SRET Hmode SREST C12 C24 C64 C68 C92 C96 C100 C104 C112 C120 C124 C128 C132 C136 C140 C144 C60 C72 C7144 Q136 Q56
          HAG ROM Wstk Wp Wob Ww FRM CST HK Hin Hlens Hcodes.
    dand HPM as (STD' & Hm' & SR' & RET' & SLO' & HL' & HC' & HP0'). unfold st_upd in SR', RET', SLO'. icx_cbn.
    pose proof SR' as SR2. unfold st_rest in SR2. icx_cbn. dand SR2 as (_ & _ & _ & _ & C92' & _).
    open_std STD'.
    pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
    dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _).
    fp_frame_from HP0'.
    tstep1 Rfd.
    clear C92'.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    unfold KDISP in KD. zkeys.
    destruct (Z.eq_dec (length - copy) 0) as [E0 | N0].
    + zbr Rfd true.
      zstep Rfd. zlit.
      clear Hm'.
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_upd _ _ lf cf LEN copy (length - copy) SI0 ltac:(left; reflexivity) Hc1 Hc3 ltac:(lia) ltac:(cbn [t_length]; lia) ltac:(right; reflexivity)) as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD Rx Mx _ lf cf SI1 ME1) end.
      * unfold s_regs_disp, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [LEN]; split_conj; zreg.
      * unfold k_mem, st_at, st_upd; icx_cbn; cbv [N_LENS N_CODES LEN]; split_conj; try assumption; try close_std; first [exact HAG | sbk].
    + zbr Rfd false.
      zstep Rfd.
      pose proof (sinv_upd _ _ lf cf MATCH copy (length - copy) SI0 ltac:(left; reflexivity) Hc1 Hc3 ltac:(lia) ltac:(cbn [t_length]; lia)
                    ltac:(left; split; [reflexivity | split; [reflexivity | lia]])) as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD Rx Mx _ lf cf SI1 ME1) end.
      * unfold s_regs_disp, s_fix, s_vars, st_upd; icx_cbn; zkeys; split_conj; zreg.
      * unfold k_mem, st_at, st_upd; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; first [exact HAG | sbk]. }
  assert (J30 : forall R2 (copy : Z) (src : Z + Z),
    m_regs u p q n ob K0 cin cout hold bits 0 R2 ->
    zget R2 kA2 = copy -> zget R2 kA3 = length -> zget R2 kA4 = osz - cout ->
    1 <= copy -> copy <= length -> copy <= osz - cout ->
    match src with
    | inl so => zget R2 kA1 = ob + so /\ 0 <= so /\ so <= cout
    | inr si => zget R2 kA1 = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0
    end ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95488 (zupd R2 []) M MD) T).
  { intros R2 copy src MR Q12 Q13 Q14 Hk1 Hk2 Hk3 HSRC. open_mregs MR. cbv [kA2 kA3 kA4 kA1] in Q12, Q13, Q14, HSRC.
    clear C60 C72 C7144 Q56 Q136.
    assert (Q11 : exists from, zget R2 12 = from) by (eexists; reflexivity). destruct Q11 as [from Q11].
    assert (HS2 : match src with inl so => from = ob + so /\ 0 <= so /\ so <= cout
                                | inr si => from = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0 end)
      by (destruct src; rewrite <- Q11; exact HSRC).
    clear HSRC.
    tstep1 Rfd.
    clear LFT.
    tstep1 Rfd.
    tstep1 Rfd.
    clear C92 SREST.
    tstep1 Rfd.
    destruct (out_arr_t _ ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo).
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    assert (HPM : PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 MATCH
                     (st_upd (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                             MATCH copy (length - copy)) lf cf Mc)
      by (unfold PM, st_upd, s_ret, s_lo, st_rest; icx_cbn; cbv [N_LENS N_CODES];
          replace (osz - (cout + copy)) with (osz - cout - copy) by lia;
          split_conj; try assumption; try close_std; exact HAG) end.
    zstep Rfd.
    zstep Rfd.
    destruct src as [so | si].
    - dand HS2 as (Hfrom & Hso1 & Hso2). subst from.
      lazymatch type of HPM with ?Pm _ => lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (mloop_o_t (Z.to_nat copy) Pm Rx lx Mx MD T ob osz so cout copy fo Hh) end end.
      all: try zreg. all: try lia. all: try assumption.
      { intros MX a v HX Ha1 Ha2. exact (PM_store _ fin M0 MATCH _ lf cf MX a v CX0 HX Ha1 Ha2). }
      intros R9 M9 fo9 E11 E18 E15 E12 E3 E4 E5 E28 E9 E2 E26 E24 E20 E10 E27 E_11 Wob9 HOB9 Rfo9 HPM9.
      zimps.
      eapply (JA R9 M9 copy); try exact HPM9; try lia. all: first [close_mregs | zreg].
    - dand HS2 as (Hfrom & Hsi1 & Hsi2 & Hw0). subst from.
      pose proof Ww as Ww32. rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw0) in Ww32. cbv [WIN_SIZE] in Ww32.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        destruct (out_arr_t Mx w 32768 Ww32 ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fw & HWA & Rfw) end.
      pose proof (sep_w_ob ROMHI_T _ SEP) as SWO. icx_cbn. cbv [WIN_SIZE] in SWO.
      assert (SWO' : ZSEP (w + 32768 <= ob \/ ob + osz <= w)) by (unfold ZSEP; clear - SWO Hw0; lia). clear SWO.
      lazymatch type of HPM with ?Pm _ => lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (mloop_w_t (Z.to_nat copy) Pm Rx lx Mx MD T ob osz w 32768 si cout copy fo fw Hh) end end.
      all: try zreg. all: try lia. all: try assumption.
      { intros MX a v HX Ha1 Ha2. exact (PM_store _ fin M0 MATCH _ lf cf MX a v CX0 HX Ha1 Ha2). }
      intros R9 M9 fo9 E11 E18 E15 E12 E3 E4 E5 E28 E9 E2 E26 E24 E20 E10 E27 E_11 Wob9 HOB9 Rfo9 Hwin9 HPM9.
      zimps.
      eapply (JA R9 M9 copy); try exact HPM9; try lia. all: first [close_mregs | zreg]. }
  assert (J28 : forall R' (copy0 : Z) (src : Z + Z),
    m_regs u p q n ob K0 cin cout hold bits 0 R' ->
    zget R' kA2 = copy0 -> zget R' kA3 = length -> zget R' kA4 = osz - cout ->
    1 <= copy0 -> copy0 <= length ->
    match src with
    | inl so => zget R' kA1 = ob + so /\ 0 <= so /\ so <= cout
    | inr si => zget R' kA1 = w + si /\ 0 <= si /\ si + copy0 <= 32768 /\ w <> 0
    end ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95480 (zupd R' []) M MD) T).
  { intros R' copy0 src MR G12 G13 G14 Hc1 Hc2 HSRC. open_mregs MR. cbv [kA2 kA3 kA4 kA1] in G12, G13, G14, HSRC.
    assert (Q11 : exists from, zget R' 12 = from) by (eexists; reflexivity). destruct Q11 as [from Q11].
    assert (HS2 : forall copy, copy <= copy0 -> match src with inl so => zget R' 12 = ob + so /\ 0 <= so /\ so <= cout
                                | inr si => zget R' 12 = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0 end)
      by (intros copy Hcp; destruct src; [exact HSRC | dand HSRC as (X1 & X2 & X3 & X4); repeat split; try assumption; lia]).
    assert (G11 : zget R' 12 = from) by exact Q11.
    clear HSRC Q11.
    destruct (Z_lt_dec copy0 (osz - cout)) as [Hlt | Hge].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J30 Rx copy0 src) end; try zreg; try lia; try close_mregs.
      cbv [kA1]. pose proof (HS2 copy0 ltac:(lia)) as X. destruct src;
        lazymatch goal with |- ?a = _ /\ ?rest => replace a with from by (symmetry; zreg); rewrite <- G11; exact X end.
    - zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J30 Rx (osz - cout) src) end; try zreg; try lia; try close_mregs.
      cbv [kA1]. pose proof (HS2 (osz - cout) ltac:(lia)) as X. destruct src;
        lazymatch goal with |- ?a = _ /\ ?rest => replace a with from by (symmetry; zreg); rewrite <- G11; exact X end. }
  clear J30 JA.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zsetreg (cout - cout0) ltac:(rewrite ?swrap32_small by lia; lia).
  tstep1 Rfd.
  destruct (Z_lt_dec (cout - cout0) offset) as [Hwin | Hout].
  2: {
    zbr Rfd true.
    zbr Rfd false.
    zstep Rfd. zbool.
    zstep Rfd.
    zstep Rfd.
    zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
    zstep Rfd. zlit.
    zbr Rfd false.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J28 Rx length (inl (cout - offset))) end; try zreg; try lia; try close_mregs.
    all: cbv [kA1]; split; [zreg | lia]. }
  zbr Rfd false.
  tstep1 Rfd.
  tstep1 Rfd.
  destruct (Z_lt_dec whave (offset - (cout - cout0))) as [Hfar | Hok].
  {
    zbr Rfd false.
    zstep Rfd.
    tstep1 Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    clear C12 C24 C64 C68 C92 C96 C100 C104 C112 C120 C124 C128 C132 C136 C140 C144 C60 C72 C7144 Q136 Q56.
    tstep1 Rfd.
    clear Hmode.
    tstep1 Rfd.
    zstep Rfd.
    unfold KDISP in KD. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KD Rx Mx (IST BAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
    - apply (sinv_bad_of _ _ _ _ SI0).
    - pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
      unfold SBase.bad_of in MB. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db
        t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in MB. change (rank MATCH) with 14 in MB. clear - MB. lia.
    - unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
    - unfold k_mem, st_at, s_lo, s_ret; icx_cbn; cbv [N_LENS N_CODES BAD]; split_conj; try assumption; try close_std; try exact HAG; try sbk. }
  zbr Rfd true.
  assert (Hw0 : w <> 0) by (intros E; destruct (WIN0 E); lia).
  dand (WIN1 Hw0) as (Wh1 & Wn1 & Whn). clear WIN0 WIN1.
  rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw0) in C60. cbv [WIN_SIZE] in C60.
  assert (J08 : forall R' (cp si : Z),
    m_regs u p q n ob K0 cin cout hold bits 0 R' ->
    zget R' kA2 = cp -> zget R' kA1 = w + si -> zget R' kA3 = w ->
    1 <= cp -> cp < 98304 -> 0 <= si -> si + cp <= 32768 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95448 (zupd R' []) M MD) T).
  { intros R' cp si MR G12 G11 G13 Hc1 Hc98 Hsi1 Hsi2. open_mregs MR. cbv [kA2 kA1 kA3] in G12, G11, G13.
    zstep Rfd. zbool.
    zstep Rfd. zbool.
    zstep Rfd. zlit.
    zbr Rfd false.
    tstep1 Rfd.
    destruct (Z_lt_dec cp length) as [Hlt | Hge].
    - zbr Rfd true.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J28 Rx cp (inr si)) end; try zreg; try lia; try close_mregs.
      all: cbv [kA1]; split; [zreg | lia].
    - zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J28 Rx length (inr si)) end; try zreg; try lia; try close_mregs.
      all: cbv [kA1]; split; [zreg | lia]. }
  clear J28.
  tstep1 Rfd.
  destruct (Z_lt_dec wnext (offset - (cout - cout0))) as [Hwrap | Hlin].
  - zbr Rfd false.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (J08 Rx (offset - (cout - cout0) - wnext) (32768 - (offset - (cout - cout0) - wnext))) end; try zreg; try lia; close_mregs.
  - zbr Rfd true.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (J08 Rx (offset - (cout - cout0)) (wnext - (offset - (cout - cout0)))) end; try zreg; try lia; close_mregs.
Qed.

Theorem lit_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LIT -> sinv cx st lf cf ->
  s_regs_disp cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LIT (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_ MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  unfold s_regs_disp, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. destruct SLO as [LFT OUT]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_LIT, L_LEAVE_L0, L_LEAVE_LD2, L_REDISP in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  open_K K. clear KD KRD1 KB0 KB5 KB5B KB1 KL KLL KRT.
  zstep Rfd.
  destruct (Z.eq_dec (osz - cout) 0) as [Hleft0 | Hleft].
  { zbr Rfd false.
    zstep Rfd.
    clear LFT.
    tstep1 Rfd.
    unfold KLEAVE_LD2 in KLL2. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL2 Rx Mx _ lf cf SI0) end.
    - unfold s_regs_leave_ld2; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - unfold s_lo; icx_cbn. rewrite Hleft0. split; assumption.
    - sbk.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  zbr Rfd true.
  clear KLL2.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd true.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (_ & _ & _ & _ & C92 & _).
  pose proof (mem_u32_u8_t _ _ _ C92) as B92.
  destruct (out_arr_t _ ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo).
  zstep Rfd.
  clear B92 C92.
  zstep Rfd.
  tstep1 Rfd.
  clear LFT.
  tstep1 Rfd.
  tstore_arr Rfd HOB (cout).
  zstep Rfd. zlit.
  clear Hmode.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  unfold KREDISP in KRD. zkeys.
  pose proof (sinv_upd _ _ lf cf LEN 1 length SI0 ltac:(right; reflexivity) ltac:(lia) ltac:(cbn [c_osz t_cout]; lia) ltac:(lia) ltac:(cbn [t_length]; lia) ltac:(right; reflexivity)) as [SI1 ME1].
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRD Rx Mx _ lf cf SI1 ME1) end.
  - unfold s_regs_redisp, st_upd; icx_cbn; zkeys; split_conj; zreg.
  - unfold s_ret in SRET. unfold k_mem, st_at, st_upd, s_lo, s_ret; icx_cbn; cbv [N_LENS N_CODES LEN].
    replace (osz - (cout + 1)) with (osz - cout - 1) by lia.
    split_conj; try assumption; try close_std; try exact HAG; try exact SREST; try sbk.
Qed.

Theorem arm_MATCH_t {RCa1 : RunCtx}  : arm_stmt L_MATCH MATCH.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply match_t; try eassumption. dand RG as (A & B & _). split; [exact A | exact B].
Qed.

Theorem arm_LIT_t {RCa1 : RunCtx}  : arm_stmt L_LIT LIT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply lit_t; try eassumption. dand RG as (A & B & _). split; [exact A | exact B].
Qed.
End T_Match.

Module T_DistX.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S.S_DistL.
Import T_Match.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.T_DistL.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_DXBODY_T : Z := 95044.
Definition L_DXSM_T : Z := 95240.

Definition x_entry (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\
  zget_l Rb l kS10 = c_q cx + t_cin st /\ zget_l Rb l kA2 = c_n cx - t_cin st /\
  zget_l Rb l kS1 = c_ob cx + t_cout st /\ zget_l Rb l kS9 = t_hold st /\ zget_l Rb l kS3 = t_bits st.

Definition x_regs (u p ob : Z) (K0 : positive -> Z) (cout : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -256 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kS2 = u /\ zget R kRA = 16209 /\ zget R kS1 = ob + cout.
Ltac open_xregs H := unfold x_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS1 kS9 kS4 kS6 kS9 kS7 kS5 kS10 kS11 kS0 kT3 kT4 kT5 kT6] in H; destr_conj H.
Ltac close_xregs := unfold x_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS1 kS9 kS4 kS6 kS9 kS7 kS5 kS10 kS11 kS0 kT3 kT4 kT5 kT6]; split_conj; zreg.
Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS2 kS3 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS1 kS9 kS4 kS6 kS9 kS7 kS5 kS10 kS11 kS0 kT3 kT4 kT5 kT6] in H.

Theorem distext_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DISTEXT -> sinv cx st lf cf ->
  x_entry cx st Rb l -> zget_l Rb l kA4 = t_extra st -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DXBODY_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG La4 KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HDE : extra <= 15 /\ 1 <= length /\ length < 65536 /\ offset < 65536)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : DISTEXT = DISTEXT -> _ |- _ => exact (H eq_refl) end).
  dand HDE as (HX15 & HL1 & HL16 & HO16). clear MODE_.
  unfold x_entry, s_fix in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. destruct SLO as [LFT OUT]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_DXBODY_T, L_DXSM_T, L_DXLOOP_T, L_DXE8_T, L_LVX_XD_T, L_LEAVE_LD2, L_MATCH in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KRD KRD1 KB0 KB5 KB5B KB1 KL KLL KRT.
  prune_rng.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & _ & _ & Q56 & _).
  pose proof SBK as SBK'. dand SBK' as (vb & Hback & Rvb & _ & _). icx_cbn.
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  assert (JSM : forall R' M' (ci H B off : Z),
    x_regs u p ob K0 cout R' ->
    zget R' kA3 = u -> zget R' kA1 = 0 -> zget R' kS10 = q + ci -> zget R' kS7 = n - ci -> zget R' kS9 = H -> zget R' kS3 = B ->
    cin <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits -> 0 <= off -> off < 98304 ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M' ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 8) DISTEXT ->
    st_rest (run_segments R_segs rc_inp rc_sp rc_mb) (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_lo (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95240 (zupd R' []) M' MD) T).
  { intros R' M' ci H B off XR G14 G12 G26 G24 G20 G10 Hc1 Hc2 HB1 HB2 HH1 HH2 HBc HWm Ho1 Ho2 STD' Hm' SR' RET' SLO' HL' HC' HAG'.
    open_xregs XR. kcbv_in G14; kcbv_in G12; kcbv_in G26; kcbv_in G24; kcbv_in G20; kcbv_in G10.
    clear Q136 Q56 Hback ROM Wstk Wp Wob Ww FRM CST HK Hin Hmode SREST SRET LFT OUT Hlens Hcodes HAG SBK.
    open_std STD'. icx_cbn. zkeys.
    zstep Rfd. zlit.
    clear Hm'.
    tstep1 Rfd.
    pose proof (sinv_pull _ _ lf cf ci H B SI0 ltac:(cbn; lia) ltac:(cbn; lia) HB1 HB2 HH1 HH2 HBc ltac:(cbn; lia)) as [SI1 ME1].
    pose proof (sinv_to_match _ _ lf cf off SI1 eq_refl Ho1 Ho2) as [SI2 ME2].
    unfold st_pull, st_dx in SI2, ME2, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI2, ME2, ME1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (match_t _ fin MD T M0 Rx lx Mx
                (IST MATCH last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI2) end.
    - unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [MATCH]; assumption | exact SR' | exact RET' | exact SLO' | exact HAG' | sbk].
    - eapply KALL_mono; [| exact K]. clear - ME1 ME2. cbn [t_mode] in *. lia. }
  assert (JE8 : forall R' (ci H B : Z),
    x_regs u p ob K0 cout R' ->
    zget R' kA3 = q + ci -> zget R' kS7 = n - ci -> zget R' kA1 = B -> zget R' kS9 = H -> zget R' kA4 = extra ->
    cin <= ci -> ci <= n -> extra <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B = bits + 8 * (ci - cin) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95168 (zupd R' []) M MD) T).
  { intros R' ci H B XR G14 G24 G12 G20 G15 Hc1 Hc2 HxB HB40 HH1 HH2 HBc HB.
    open_xregs XR. kcbv_in G14; kcbv_in G24; kcbv_in G12; kcbv_in G20; kcbv_in G15. clear KLL2.
    repeat match goal with H : forall i : Z, _ |- _ => clear H end.
    pose proof SREST as C96. unfold st_rest in C96. icx_cbn. dand C96 as (_ & _ & _ & _ & _ & C96 & _).
    pose proof (pow2_15 extra ltac:(lia)) as HPx.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    tstep1 Rfd.
    clear C96.
    zstep Rfd.
    zstep Rfd.
    clear Hback SBK.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ extra - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    pose proof (land_mask_r H extra ltac:(lia)) as Rbx.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zsetreg (H / 2 ^ extra) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B extra ltac:(lia) ltac:(lia)) as HH'.
    zstep Rfd.
    st_prestore_k st_rest_set96 13%positive SREST.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (JSM Rx Mx ci (H / 2 ^ extra) (B - extra) (offset + Z.land H (2 ^ extra - 1))) end;
      try zreg; try lia; try assumption.
    - close_xregs.
    - close_std.
    - unfold s_lo; icx_cbn; split; assumption. }
  destruct (Z.eq_dec extra 0) as [Hx0 | Hx1].
  { zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JSM Rx Mx cin hold bits offset) end;
      try zreg; try lia; try assumption.
    - close_xregs.
    - close_std.
    - unfold s_lo; icx_cbn; split; assumption. }
  zbr Rfd false.
  destruct (Z_lt_dec bits extra) as [Hneed | Hhave].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (x_loop_d (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n extra cin bits cin bits hold fin Hh) end;
      try zreg; try lia; try eassumption.
    +
      intros R' H' G20 G24 HH1 HH2 HB14 HBn KP. cbv [keptc KS_XDT] in KP. kcbv_in G20; kcbv_in G24. destr_conj KP. zimps.
      eapply (stub_X_t 96200 R' [] M MD T q n cin bits); [left; split; [reflexivity | zreg] | exact Hh | zreg | zreg | lia | lia | lia | lia | lia | lia |].
      intros R9 E26 E10 HK9. cbv [keptc KS_XST] in HK9. kcbv_in E26; kcbv_in E10. destr_conj HK9. zimps.
      pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
      unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
        t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
      unfold KLEAVE_LD2 in KLL2.
      eapply (KLL2 R9 M _ lf cf SI1).
      * unfold s_regs_leave_ld2; icx_cbn; zkeys; split_conj; zreg.
      * close_std.
      * split; [exact Hmode | exact SREST].
      * exact SRET.
      * unfold s_lo; icx_cbn; split; assumption.
      * sbk.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' ci' B' H' G14 G6 G24 G12 G16 G20 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_XDT] in KP.
      kcbv_in G14; kcbv_in G6; kcbv_in G24; kcbv_in G12; kcbv_in G16; kcbv_in G20. destr_conj KP. zimps.
      eapply (JE8 R' ci' H' B'); try assumption; try lia. close_xregs.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JE8 Rx cin hold bits) end; try zreg; try lia.
    close_xregs.
Qed.

Theorem arm_DISTEXT_t {RCa1 : RunCtx}  : arm_stmt L_DISTEXT DISTEXT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SREST as SR0. unfold st_rest in SR0. dand SR0 as (_ & _ & _ & _ & _ & _ & C100 & _).
  dand RG as (FIX & VARS & _). pose proof FIX as FIX0. unfold s_fix in FIX. destr_conj FIX.
  pose proof VARS as VARS0. unfold s_vars in VARS. destr_conj VARS.
  pose proof SI as SI'. dand SI' as (R & _ & _ & Mo).
  assert (HX : 0 <= t_extra st <= 15).
  { assert (Mde : t_mode st = DISTEXT -> t_extra st <= 15 /\ 1 <= t_length st /\ t_length st < 65536 /\ t_offset st < 65536) by mode_get Mo.
    destruct (Mde Hmd) as [A _]. unfold RNG in R. destr_conj R. split; [assumption | exact A]. }
  zkeysb. unfold L_DISTEXT in *.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
    eapply (distext_t cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI) end.
  - unfold x_entry. split; [exact FIX0 | split_conj; zreg].
  - zreg.
  - exact KM0.
  - exact K.
Qed.
End T_DistX.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S Require Import S_MatchL S_DistL.
Import T_MatchL. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U Require Import T_DistL. Import T_DistX.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7U Require Import TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_D11C : Z := 94964.
Definition L_DBAD_T : Z := 95400.

Definition d_entry (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kS2 = c_u cx /\ zget_l Rb l kRA = 16209 /\
  s_vars cx st Rb l.

Ltac mode_getr Mo := clear - Mo; unfold MODE in Mo; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  first [ assumption | match goal with H : ?x = ?x -> _ |- _ => exact (H eq_refl) end ].
Ltac jfin :=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- x_regs _ _ _ _ _ _ => close_xregs
  | |- keptc _ _ _ _ => keptc_closeT
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => first [assumption | lia]
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- mem_u32 _ _ _ _ => assumption
  | |- PM _ _ _ _ _ _ _ _ => first [assumption | idtac]
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- _ => first [assumption | lia]
  end.

Lemma srl_hold_cell : forall hold bits e, 0 <= hold < 2 ^ bits -> 0 <= bits <= 63 -> code_bits e <= bits ->
  Z.shiftr (hold mod 18446744073709551616) ((code_bits e + 256 * code_val e) mod 64) = hold / 2 ^ code_bits e.
Proof.
  intros hold bits e Hh Hb He. pose proof (code_bits_range e). rewrite shamt_cell by lia.
  rewrite <- (Z.mod_small (code_bits e) 64) at 1 by lia. apply (srl_hold hold bits); lia.
Qed.
Lemma land_op15 : forall op, 0 <= op <= 15 -> Z.land op 15 = op.
Proof. intros op H. change 15 with (2 ^ 4 - 1). apply land_ones_id; [lia | change (2 ^ 4) with 16; lia]. Qed.

Ltac zbool0 := zsetreg 0 ltac:(rewrite ?mod_small_u64 by zlia;
  lazymatch goal with |- 0 = Z.b2z ?b' => replace b' with false; [reflexivity | symmetry; first [apply Z.ltb_ge; zlia | apply Z.eqb_neq; zlia]] end).
Ltac zbool1 := zsetreg 1 ltac:(rewrite ?mod_small_u64 by zlia;
  lazymatch goal with |- 1 = Z.b2z ?b' => replace b' with true; [reflexivity | symmetry; first [apply Z.ltb_lt; zlia | apply Z.eqb_eq; zlia]] end).

Theorem dist_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DIST -> sinv cx st lf cf ->
  d_entry cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DIST (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  pose proof KM as KM0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ DIST LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HDI : 1 <= length /\ length < 65536) by mode_getr MODE_. destruct HDI as [HL1 HL16]. clear MODE_.
  unfold d_entry, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. destruct SLO as [LFT OUT]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof SBK as SBK0. dand SBK as (bk & BK & Rbk & _ & Hbk). icx_cbn. specialize (Hbk eq_refl).
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  clear HtL TOKL Cla1 Cla2 Cna ALla Slaob Slap Slap2.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) dc) as da eqn:Eda.
  remember (rdc cf dc) as rdD eqn:ErdD. clear ErdD.
  prune_rng.
  zkeysb. unfold L_DIST, L_D11C, L_DBAD_T, L_DLOOP1_T, L_DL1X_T, L_DLOOP2_T, L_DL2X_T, L_LVX_L1_T, L_LVX_L2_T,
    L_DXBODY_T, L_DISP, L_LEAVE, L_LEAVE_LD2 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KRD KRD1 KB0 KB5 KB5B KB1 KLL KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & _ & _ & Q56 & _).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  pose proof (tab_ok_root _ _ _ _ TOKD) as (Hdb1 & Hnd1 & _).
  pose proof (pow2_15 db ltac:(lia)) as HPdb.
  assert (HPM0 : PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 DIST
            (IST DIST last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf M)
    by (unfold PM, s_lo; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; exact HAG).
  assert (J1C : forall R' M' (ci B H e bk1 : Z),
    x_regs u p ob K0 cout R' ->
    zget R' kS5 = code_bits e -> zget R' kS6 = code_bits e + 256 * code_val e -> zget R' kS10 = q + ci ->
    zget R' kT4 = code_op e -> zget R' kT5 = cellv e -> zget R' kA4 = B -> zget R' kA2 = n - ci -> zget R' kS9 = H ->
    1 <= code_bits e ->
    ((16 <= code_op e < 32 /\ 1 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 32768 /\ code_op e <= 29)
     \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0 /\ Z.land (code_op e) 32 = 0)) ->
    cin <= ci -> ci <= n -> code_bits e <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits ->
    0 <= bk1 -> bk1 <= 192 ->
    PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 DIST
       (IST DIST last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf M' ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 7164) bk1 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 94964 (zupd R' []) M' MD) T).
  { intros R' M' ci B H e bk1 XR G22 G23 G26 G30 G31 G15 G13 G20 Hbe CLS Hc1 Hc2 HbB HB40 HH1 HH2 HBc HWm Hk1 Hk2 HPM' BK1.
    open_xregs XR. kcbv_in G22; kcbv_in G23; kcbv_in G26; kcbv_in G30; kcbv_in G31; kcbv_in G15; kcbv_in G13; kcbv_in G20.
    clear Q136 Q56 HtD KL KLL2 BK SBK0 HPM0 ROM Wstk Wp Wob Ww FRM CST HK Hin Hmode SREST SRET LFT OUT Hlens Hcodes HAG.
    dand HPM' as (STD' & Hm' & SR' & RET' & SLO' & HL' & HC' & HP0'). icx_cbn.
    open_std STD'. fp_frame_from HP0'. zkeys.
    pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
    dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & _ & _ & Q56 & _).
    pose proof (code_op_range e) as Rop. pose proof (code_val_range e) as Rval. pose proof (code_bits_range e) as Rbi.
    pose proof (cellv_range e) as Rcell.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zsetreg 0 ltac:(symmetry; apply bits_and192; lia).
    zbr Rfd false.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zsetreg (H / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold_cell H B); lia).
    pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    tstep1 Rfd.
    zstep Rfd.
    clear BK1.
    tstep1 Rfd.
    pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ code_bits e) (B - code_bits e) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
    destruct CLS as [(Hop16 & Hv1 & Hv32k & Hop29) | (H64 & H16 & H32)].
    2: {
      pose proof (land_range_r (code_op e) 64 ltac:(lia)) as R64.
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      tstep1 Rfd.
      clear Hm'.
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      unfold KDISP in KD. zkeys.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KD Rx Mx (IST BAD last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length offset extra
                              lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
      - apply (sinv_bad_of _ _ _ _ SI1).
      - pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                      (IST DIST last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length offset extra
                           lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
        unfold SBase.bad_of in MB. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
          t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in MB.
        change (rank DIST) with 16 in MB. clear - MB ME1. lia.
      - unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; split_conj; zreg.
      - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES BAD]. split_conj; try assumption; try close_std.
        all: first [exact SR' | exact RET' | exact SLO' | exact HAG | sbk]. }
    pose proof (op_base_tests (code_op e) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    zbr Rfd false.
    zstep Rfd.
    zsetreg (code_val e) ltac:(symmetry; apply cell_shr16).
    zstep Rfd.
    zsetreg (code_op e + -16) ltac:(lia).
    zstep Rfd. zlit.
    st_prestore st_rest_set96 (code_val e) SR'.
    tstep1 Rfd.
    st_prestore_k st_rest_set100 15%positive SR'.
    tstep1 Rfd.
    clear Hm'.
    tstep1 Rfd.
    pose proof (sinv_to_distext _ _ lf cf (code_val e) (code_op e + -16) SI1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI2 ME2].
    unfold st_dx in SI2, ME2. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI2, ME2.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (distext_t _ fin MD T M0 Rx lx Mx
                (IST DISTEXT last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length (code_val e) (code_op e + -16)
                     lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI2) end.
    - unfold x_entry, s_fix; icx_cbn; zkeys; split_conj; zreg.
    - zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [DISTEXT]; assumption | exact SR' | exact RET' | exact SLO' | exact HAG | sbk].
    - eapply KALL_mono; [| exact K]. clear - ME1 ME2. cbn [t_mode] in *. lia. }
  assert (KX1 : forall R' (H' : Z),
    zget R' kS9 = H' -> 0 <= H' -> H' < 2 ^ (bits + 8 * (n - cin)) -> bits + 8 * (n - cin) <= 14 -> bits + 8 * (n - cin) <= 8 * n ->
    x_regs u p ob K0 cout R' -> zget R' kT6 = Z.shiftl (n - cin) 32 -> zget R' kS7 = n - cin -> zget R' kS10 = q + cin -> zget R' kS3 = bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 95976 (zupd R' []) M MD) T).
  { intros R' H' G20 HH1 HH2 HB14 HBn XR G32 G24 G26 G10. open_xregs XR. kcbv_in G20; kcbv_in G32; kcbv_in G24; kcbv_in G26; kcbv_in G10.
    clear J1C KD KLL2.
    pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn.
    eapply (stub_L1_t 95976 R' [] M MD T q n cin bits u ret);
      [left; split; [reflexivity | zreg] | exact Hh | zreg | zreg | zreg | zreg | zreg | lia | lia | lia | lia | lia | lia | lia | lia | exact SRET' | exact Q136 |].
    intros R9 E26 E24 E10 E27 E14 E12 KP. cbv [keptc KS_L1T] in KP. kcbv_in E26; kcbv_in E24; kcbv_in E10; kcbv_in E27; kcbv_in E14; kcbv_in E12.
    destr_conj KP. zimps.
    pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
    unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
    unfold KLEAVE in KL.
    eapply (KL R9 M _ ret lf cf SI1).
    - unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - unfold s_lo; icx_cbn; split; assumption.
    - sbk.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  assert (JL1 : forall R' (ci B H : Z),
    x_regs u p ob K0 cout R' -> zget R' kA1 = da -> zget R' kT4 = 2 ^ db + -1 -> zget R' kA3 = 1 ->
    zget R' kT0 = q + ci -> zget R' kT1 = q + ci -> zget R' kA5 = B -> zget R' kA4 = B ->
    zget R' kA6 = n - ci -> zget R' kA7 = 8 * (n - ci) -> zget R' kA2 = n - ci -> zget R' kS9 = H ->
    zget R' kT5 = cellv (rdD (Z.land (2 ^ db + -1) H)) ->
    zget R' kT2 = code_bits (rdD (Z.land (2 ^ db + -1) H)) + 256 * code_val (rdD (Z.land (2 ^ db + -1) H)) ->
    zget R' kT3 = code_bits (rdD (Z.land (2 ^ db + -1) H)) ->
    cin <= ci -> ci <= n -> B = bits + 8 * (ci - cin) -> B <= 40 -> code_bits (rdD (Z.land (2 ^ db + -1) H)) <= B ->
    0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 94656 (zupd R' []) M MD) T).
  { intros R' ci B H XR G12 G30 G14 G6 G7 G16 G15 G17 G18 G13 G20 G31 G8 G29 Hc1 Hc2 HB HB40 HbB HH1 HH2 HBc.
    open_xregs XR. kcbv_in G12; kcbv_in G30; kcbv_in G14; kcbv_in G6; kcbv_in G7; kcbv_in G16; kcbv_in G15; kcbv_in G17;
    kcbv_in G18; kcbv_in G13; kcbv_in G20; kcbv_in G31; kcbv_in G8; kcbv_in G29.
    clear KX1 KL.
    set (i := Z.land (2 ^ db + -1) H) in *.
    pose proof (land_mask_l' H db ltac:(lia)) as Ri. fold i in Ri.
    pose proof (tab_root_entry DISTS rdD db nd i TOKD Ri) as (Hbits & _ & _ & CASES).
    pose proof (code_op_range (rdD i)) as Rop. pose proof (code_val_range (rdD i)) as Rval. pose proof (cellv_range (rdD i)) as Rcell.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zsetreg (code_op (rdD i)) ltac:(symmetry; apply cell_and255).
    zstep Rfd.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      apply term_ok_DISTS in TM as [Hb1 CLS].
      assert (Hop16 : 16 <= code_op (rdD i)).
      { destruct CLS as [(A & _) | (A64 & _ & _)]; [lia|].
        apply is_linkop_false in NL. pose proof (land_range_r (code_op (rdD i)) 64 ltac:(lia)).
        destruct (Z_lt_dec (code_op (rdD i)) 16); [|lia]. exfalso.
        assert (E : code_op (rdD i) = 0) by lia. rewrite E in A64. apply A64. reflexivity. }
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      subst i.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J1C Rx M ci B H (rdD (Z.land (2 ^ db + -1) H)) bk) end.
      all: jfin.
    -
      rewrite L2 in G29, G8, HbB.
      pose proof (op_link_tests (code_op (rdD i)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      assert (HPm : 1 <= 2 ^ (db + code_op (rdD i)) <= 32768) by (apply pow2_15; lia).
      pose proof (pow2_15 (code_op (rdD i)) ltac:(lia)) as HPlo.
      zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      zsetreg 0 ltac:(symmetry; apply cell_and_e000; lia).
      zbr Rfd false.
      zstep Rfd.
      zsetreg (code_op (rdD i)) ltac:(symmetry; rewrite cell_and15; apply land_op15; lia).
      zstep Rfd.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zsetreg (code_val (rdD i)) ltac:(symmetry; apply cell_shr16).
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zsetreg (2 ^ (db + code_op (rdD i)) - 1) ltac:(symmetry; apply mask_not_sllw; lia).
      set (m2 := 2 ^ (db + code_op (rdD i)) - 1) in *.
      set (v := code_val (rdD i)) in *. set (lo := code_op (rdD i)) in *.
      assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ db < 2 ^ lo).
      { intros Hx. pose proof (land_mask_r Hx (db + lo) ltac:(lia)) as A. fold m2 in A.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
      zstep Rfd.
      pose proof (land_mask_r H (db + lo) ltac:(lia)) as Rm. fold m2 in Rm.
      zstep Rfd.
      zsetreg (Z.land H m2 / 2 ^ db) ltac:(symmetry; apply srlw_small; lia).
      pose proof (JR H) as Rj.
      zstep Rfd.
      zsetreg (v + Z.land H m2 / 2 ^ db) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zsetreg (4 * (v + Z.land H m2 / 2 ^ db)) ltac:(symmetry; apply zext32_shift30; lia).
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd. zbool0.
      zstep Rfd. zlit.
      zbr Rfd false.
      zstep Rfd. zext32.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (d_loop2_t (S (Z.to_nat (n - ci))) Rx lx Mx MD T q n da nd db lo v m2 ci B ci B H fin rdD Hh) end.
      all: jfin.
      +
        intros R5 H' Q20 HH1' HH2' HB29 HBn KP. cbv [keptc KS_D2T] in KP. kcbv_in Q20. destr_conj KP. zimps.
        clear J1C SUB JR. unfold L_LVX_L2_T.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        pose proof (sinv_pull _ _ lf cf n H' (B + 8 * (n - ci)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1' HH2' HBn ltac:(cbn; lia)) as [SI1 _].
        unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
          t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
        unfold KLEAVE_LD2 in KLL2. zkeys.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KLL2 Rx M _ lf cf SI1) end.
        * unfold s_regs_leave_ld2; icx_cbn; zkeys; split_conj; zreg.
        * close_std.
        * split; [exact Hmode | exact SREST].
        * exact SRET.
        * unfold s_lo; icx_cbn; split; assumption.
        * sbk.
        * exact Hlens.
        * exact Hcodes.
        * exact HAG.
      +
        intros R5 ci' B' H' Q26 Q7 Q21 Q10 Q13 Q20 Q31 Q23 Q22 Q24 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_D2T] in KP.
        kcbv_in Q26; kcbv_in Q7; kcbv_in Q21; kcbv_in Q10; kcbv_in Q13; kcbv_in Q20; kcbv_in Q31; kcbv_in Q23; kcbv_in Q22; kcbv_in Q24.
        destr_conj KP. zimps.
        clear KLL2. unfold L_DL2X_T.
        pose proof (JR H') as Rj2.
        set (j2 := Z.land H' m2 / 2 ^ db) in *.
        destruct (SUB _ Rj2) as [NL3 TM3].
        assert (HPB2 : 1 <= 2 ^ B' <= 2 ^ 40) by (split; [pose proof (pow2_pos B' ltac:(lia)); lia | apply pow2_le; lia]).
        pose proof (code_bits_range (rdD (v + j2))) as Rb2. pose proof (code_op_range (rdD (v + j2))) as Rop2.
        pose proof (code_val_range (rdD (v + j2))) as Rval2. pose proof (cellv_range (rdD (v + j2))) as Rcell2.
        zstep Rfd.
        tstep1 Rfd.
        zstep Rfd.
        tstep1 Rfd.
        zbr Rfd false.
        tstep1 Rfd.
        zstep Rfd.
        zsetreg db ltac:(rewrite <- L2; symmetry; apply bits_and31; lia).
        zstep Rfd.
        zsetreg (code_op (rdD (v + j2))) ltac:(symmetry; apply cell_and255).
        zstep Rfd.
        zsetreg (H' / 2 ^ db) ltac:(symmetry; apply (srl_hold H' B'); lia).
        pose proof (hold_shr_bound H' B' db ltac:(lia) ltac:(lia)) as HH2'.
        clear BK.
        pose proof Sdap2 as DSEP; unfold ZSEP in DSEP.
        tstep1 Rfd.
        clear DSEP.
        apply term_ok_DISTS in TM3 as [Hbits3 CLS3].
        subst j2.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (J1C Rx Mx ci' (B' - db) (H' / 2 ^ db) (rdD (v + Z.land H' m2 / 2 ^ db)) (bk + db)) end.
        all: jfin.
        unfold PM, s_lo; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; exact HAG. }
  clear KL KLL2.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn. dand SR0 as (_ & _ & _ & _ & _ & _ & _ & _ & C112 & _ & C124 & _).
  rewrite <- Eda in C112. clear Eda.
  tstep1 Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd.
  clear C112 C124.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 ^ db + -1) ltac:(symmetry; rewrite mask_not_sllw by lia; lia).
  zstep Rfd.
  pose proof (land_mask_l' hold db ltac:(lia)) as Ri0.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land (2 ^ db + -1) hold) TOKD Ri0) as (Hbits0 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land (2 ^ db + -1) hold) ltac:(symmetry; apply shl_2).
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zbool1.
  zstep Rfd. zbool0.
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd. zext32.
  zstep Rfd.
  zsetreg (8 * (n - cin)) ltac:(symmetry; apply zext32_shift29; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (d_loop1_t (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n da nd db (2 ^ db + -1) cin bits cin bits hold fin rdD Hh) end.
  all: jfin.
  - intros R' H' G20 HH1' HH2' HB14 HBn KP. cbv [keptc KS_D1T] in KP. kcbv_in G20. destr_conj KP. zimps.
    eapply (KX1 R' H'). all: jfin.
  - intros R' ci' B' H' G6 G7 G16 G15 G17 G18 G13 G20 G31 G8 G29 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_D1T] in KP.
    kcbv_in G6; kcbv_in G7; kcbv_in G16; kcbv_in G15; kcbv_in G17; kcbv_in G18; kcbv_in G13; kcbv_in G20; kcbv_in G31; kcbv_in G8; kcbv_in G29.
    destr_conj KP. zimps.
    eapply (JL1 R' ci' B' H'). all: jfin.
Qed.

Theorem arm_DIST_t {RCa1 : RunCtx}  : arm_stmt L_DIST DIST.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply dist_t; try eassumption. dand RG as (A & B & _).
  dand A as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  unfold d_entry. split_conj; try assumption.
Qed.
