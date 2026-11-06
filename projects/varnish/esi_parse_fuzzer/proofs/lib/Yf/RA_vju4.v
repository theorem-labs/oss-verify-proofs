(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require ImgA RA_seql.

Module RA_tzg3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)

Definition towrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp buf bufsize CK : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (mode' : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' Fp (snfile z64 (buf + bufsize) buf buf buf bufsize mode' CK).

Lemma towrite_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Fp wend wpos wbase buf bufsize CK : Z) (mode : word),
  a0 = Z_to_bv 64 Fp ->
  rw_cells rsegs m Fp (snfile z64 wend wpos wbase buf bufsize mode CK) ->
  (0 <= buf)%Z -> (0 <= bufsize)%Z -> (buf + bufsize < 2^64)%Z ->
  mem_inv rsegs m ->
  evt rsegs (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp buf bufsize CK m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e830) fc None m (seg_rom rsegs)).
Proof.
  intros until mode. intros -> FL B0 S0 BS MI.
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ FL) as FB. rewrite snfile_size in FB.
  unfold snfile, z64, m1w in FL.
  zs. zs. zs. zs. zs. zs. zs. if_lit.
  zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
  apply evt_done. unfold towrite_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold snfile, z64, m1w. exact FL.
Qed.
End RA_tzg3.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_f93z RA_sjs3.

Module RA_v05d.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require ImgA RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_f93z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_tzg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_f93z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpesd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac low_lemma P ::= RA_f93z.low_lemma_pf P.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= relow_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= relow_all W m m' MU.
Local Ltac icpt_consts_in H ::= unfold STRNLEN_ICPT_STACK, MEMCPY_ICPT_STACK, MEMSET_ICPT_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfdx.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

Definition VF_DEPTH : Z := 5296.   (* [comment removed for export] *)

Definition vfprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo Fp D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (o : list byte) (canary : word)
    (A la : Z) (ZSB : Z) (ZK : nat)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (jd' : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length o))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 5296, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' Fp (snfile z64 0 0 0 (Fp + 255) 0 mode' (Fp + 232))
    /\ rw_cells rsegs m' (Fp + 232) [C8 (Z_to_bv 64 (D + Z.of_nat (length (dl n o)))); C8 (Z_to_bv 64 ((Z.of_nat n - 1) - Z.of_nat (length (dl n o))))]
    /\ rw_cells rsegs m' D [CB n (dl n o ++ Z_to_bv 8 0 :: jd')]
    /\ va_area m' VA slots /\ bytes_at rsegs m' HS hs
    /\ ssp_cells m' canary
    /\ sf2 A la D n HS hs ZSB ZK (bv_unsigned sp - 912) (bv_unsigned sp - 272) m'.

Section VF.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.

  #[using="P2 P1 HOUT HLA nargs"] Lemma vfprintf_sn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte)
      (lo A Fp D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs jd : list byte) (canary : word) (ZSB : Z) (ZK : nat),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    stk rsegs m lo (bv_unsigned sp) -> ro_cells rsegs m A FMT -> ssp_cells m canary ->
    rw_cells rsegs m Fp (snfile z64 0 0 0 (Fp + 255) 0 z64 (Fp + 232)) ->
    rw_cells rsegs m (Fp + 232) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (Z.of_nat n - 1))] ->
    rw_cells rsegs m D [CB n (Z_to_bv 8 0 :: jd)] ->
    va_area m VA slots -> bytes_at rsegs m HS hs -> PRE slots HS hs -> mem_inv rsegs m ->
    sf2 A la D n HS hs ZSB ZK (bv_unsigned sp - 912) (bv_unsigned sp - 272) m ->
    Fp = (bv_unsigned sp + 48)%Z ->      (* [comment removed for export] *)
    (lo <= bv_unsigned sp - VF_DEPTH)%Z -> (alloc_ceiling <= lo)%Z -> (Fp + 304 <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
    (IMG_LO <= A)%Z -> (A + la <= RO_TOP)%Z -> dst_ok D n -> (D + Z.of_nat n <= lo)%Z -> dst_zone D (Z.of_nat n) -> (Z.of_nat n <= 2^31)%Z ->
    (HS + Z.of_nat (length hs) <= lo)%Z -> (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z ->
    evt rsegs (vfprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fp D n VA slots HS hs (OUT slots hs) canary A la ZSB ZK m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ea00) fc None m (seg_rom rsegs)).
  Proof.
    intros until ZK. intros -> -> -> ST HF SSP FL CKC DST VAA HSB HPRE MI SF HFp LO GT VLO VHI ARL ART GD DLO KH N31 HSL HSD.
    destruct SSP as [SSP1 SSP2]. pose proof GD as GD'. pose proof alloc_ceiling_val as CV.
    unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, VF_DEPTH, dst_ok, IMG_LO, IMG_HI, kHighMemBeg_z in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB.
    pose proof (munch_refl [(bv_unsigned sp - 5296, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    unfold va_area in VAA. unfold snfile, z64, m1w in FL.
    carve_frame 368%nat ST.
    zto 0x9ebb0%Z. name_junk FR.
    (* [comment removed for export] *)
    call_lit P1 by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- @eq _ _ _ => reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; unfold PC1_DEPTH, GLOBALS_TOP, RO_TOP in *; lia
      end || match goal with |- ?G => idtac "P1SIDE-FAIL:" G end).
    rename POST into ST.
    zto 0x9ea94%Z. rewrite sx32_zero.
    zto 0x9e830%Z.
    (* [comment removed for export] *)
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL); call_lit towrite_spec by (idtac; first [ reflexivity | eassumption | lia ]).
    rename POST into FL.
    zto 0x9ebb0%Z.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB rsegs _ _ [_;_] 248 _ _ [80; 168]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [APC FR].
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [FR1 FR].
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [BUF FR2].
    cbn [cells_size csize Nat.add] in FR1, BUF, FR2.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in FR1 by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp + -352)%Z in BUF by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FR2 by lia.
    name_junk BUF. name_junk FR2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    assert (CKC' : rw_cells rsegs mq (Fp + 232) [C8 (Z_to_bv 64 (D + Z.of_nat (length (dl n [])))); C8 (Z_to_bv 64 (Z.of_nat n - 1 - Z.of_nat (length (dl n []))))]);
    [ rewrite dl_nil; cbn [length Z.of_nat]; rewrite Z.add_0_r, Z.sub_0_r; exact CKC |];
    assert (DST' : rw_cells rsegs mq D [CB n (dl n [] ++ Z_to_bv 8 0 :: jd)]);
    [ rewrite dl_nil; cbn [app]; exact DST |];
    lazymatch type of FL with rw_cells _ _ _ (snfile _ _ _ _ _ _ ?md _) =>
    assert (FL' : rw_cells rsegs mq Fp (snfile z64 ((bv_unsigned sp + -352) + 80) ((bv_unsigned sp + -352) + Z.of_nat (@length byte [])) (bv_unsigned sp + -352) (bv_unsigned sp + -352) 80 md (Fp + 232)));
    [ cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FL |] end end.
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD. cbn [length] in LD.
    clear CKC DST FL.
    (* [comment removed for export] *)
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC'); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST'); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL'); call_lit P2 by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- sink _ _ _ _ _ _ _ _ => rewrite ?unsigned_lit by lia; eexists _, _; refine (conj _ (conj _ (conj _ (conj _ _))));
           [ eapply rwc_eq; [exact FL' | lia] | exact CKC' | rewrite app_nil_l; exact BUF | exact DST' | lia ]
      | |- rw_cells _ _ _ [C8 _] => rewrite ?unsigned_lit by lia; eapply rwc_eq; [exact APC | lia]
      | |- va_area _ _ _ => exact VAA
      | |- bytes_at _ _ _ _ => eassumption
      | |- PRE _ _ _ => exact HPRE
      | |- dst_ok _ _ => unfold dst_ok, IMG_LO, IMG_HI; exact GD
      | |- sf2 _ _ _ _ _ _ _ _ _ _ _ => rewrite ?unsigned_lit by lia;
            match goal with SF : sf2 _ _ _ _ _ _ _ _ _ _ ?mq |- sf2 _ _ _ _ _ _ _ _ ?zlo ?zhi ?mq =>
              replace zlo with (bv_unsigned sp - 912)%Z by lia; replace zhi with (bv_unsigned sp - 272)%Z by lia; exact SF end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [ reflexivity | f_equal; lia | lia ]
      | |- dst_zone _ _ => first [assumption | eapply dst_zone_sub; [eassumption| lia| lia]]
      | |- _ => rewrite ?unsigned_lit by lia; unfold PC2_DEPTH, GLOBALS_TOP, RO_TOP, IMG_LO, kHighMemBeg_z in *; lia
      end).
    try clear FL'; try clear CKC'; try clear BUF; try clear DST'; try clear VAA; try clear HSB; try clear SSP1; try clear SSP2. rename PC into ST. rename PC3 into VAA. rename PC4 into HSB. destruct PC5 as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2. unfold va_area in VAA.
    (* [comment removed for export] *)
    try match goal with SFo : sf2 _ _ _ _ _ _ _ _ (bv_unsigned sp - 912)%Z _ _ |- _ => clear SFo end. rename POST into SF.
    unpack_sink PC0 FL CKC BUF DST. unfold snfile, z64, m1w, SN_WRITE in FL.
    zto 0x9eb10%Z. zs. br K. clear K.
    zto 0xa1bf8%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    eapply evt_cut; [ eapply (sn_write_sink _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mq Fp (bv_unsigned sp + -352) D n _ _ _ [] 0 0 lo ZSB ZK);
                      try reflexivity | ] end.
    { rewrite ?unsigned_lit by lia. exact ST. }
    { eexists _, _; refine (conj _ (conj _ (conj _ (conj _ _)))); [ unfold snfile, z64, m1w, SN_WRITE; exact FL | exact CKC | exact BUF | exact DST | lia ]. }
    { apply bytes_at_nil. lia. }
    { lia. }
    { unfold sn_layout. rewrite ?unsigned_lit by lia. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | lia | eapply dst_zone_sub; [eassumption| lia| lia]]. }
    { assumption. }
    { match goal with SF : sf2 _ _ _ _ _ _ _ _ ?zlo ?zhi ?mm |- sfx _ _ _ _ _ _ _ ?mm =>
        eapply (sf2_sfx _ _ _ _ _ _ _ _ (bv_unsigned sp + -368));
        [ replace (bv_unsigned sp + -368 - 544)%Z with zlo by lia; replace (bv_unsigned sp + -368 + 96)%Z with zhi by lia; exact SF
        | left; reflexivity | lia ] end. }
    cbv beta. intros ms' P. unfold sn_write_sink_post in P.
    (first [ dex15 P as y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m'; dand7 P as -> MU' WM' MI' ST' SNK' _ | dand22 P as y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m' -> MU' WM' MI' ST' SNK' _ | destruct P as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m' & -> & MU' & WM' & MI' & ST' & SNK' & _) ]).
    rewrite ?unsigned_lit in MU' by lia. rewrite ?unsigned_lit in ST' by lia.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL); lazymatch type of MU' with munch _ ?mq _ => transport_after_call rsegs mq m' MU' WM'; clear MU' WM' end.
    replace (ret_pc (Z_to_bv 64 650024)) with (Z_to_bv 64 650024) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    try clear FL; try clear CKC; try clear BUF; try clear DST.
    rewrite app_nil_r in SNK'. unpack_sink SNK' FL CKC BUF DST. unfold snfile, z64, m1w in FL.
    zto 0x9eb3c%Z.
    (* [comment removed for export] *)
    zs. zs.
    replace (Z.b2z (0 <? (bv_unsigned sp + -352 + Z.of_nat (@length byte [])) mod 18446744073709551616)%Z) with 1%Z.
    2:{ cbn [length Z.of_nat]. rewrite Z.add_0_r, Z.mod_small by lia. replace (0 <? bv_unsigned sp + -352)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    zto 0x9eb50%Z. rewrite sx32_zero.
    zto 0x9eb84%Z. zs. brf Kc. { exfalso. apply Kc. reflexivity. } clear Kc.
    (* [comment removed for export] *)
    lazymatch type of APC2 with _ => idtac end || idtac.
    match goal with A1 : rw_cells _ ?mq (bv_unsigned sp + -368) [C8 ?va], B1 : rw_cells _ ?mq (bv_unsigned sp + -352) [CB 80 ?bb] |- _ =>
      lazymatch type of FR1 with rw_cells _ _ _ ?cs1 => lazymatch type of FR2 with rw_cells _ _ _ ?cs2 =>
      assert (FR : rw_cells rsegs mq (bv_unsigned sp + -368) ([C8 va] ++ cs1 ++ [CB 80 bb] ++ cs2));
      [ apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact A1|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [eapply rwc_eq; [exact FR1|lia]|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [eapply rwc_eq; [exact B1|lia]|]; cbn [cells_size csize Nat.add];
        eapply rwc_eq; [exact FR2|lia]
      | clear A1 FR1 B1 FR2; cbn [app] in FR ] end end end.
    do 9 zs.
    match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
    release_frame FR ST (bv_unsigned sp).
    pose proof (HOUT _ _ _ HPRE) as OL.
    match goal with |- context [Z_to_bv 64 (Z.lor ?a (Z.lor 0 ?b))] =>
      replace (Z.lor a (Z.lor 0 b)) with (Z.of_nat (length (OUT slots hs)));
      [ | rewrite Z.lor_0_l; replace a with 0%Z by reflexivity; rewrite Z.lor_0_l, Z.mod_small by lia; reflexivity ] end.
    apply evt_done. unfold vfprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { unfold snfile, z64, m1w. exact FL. }
    rewrite <- PC1.
    split; [exact CKC|]. split; [exact DST|]. split; [exact VAA|]. split; [exact HSB|]. split; [split; assumption|].
    match goal with SF : sf2 _ _ _ _ _ _ _ _ ?zlo ?zhi ?mm |- sf2 _ _ _ _ _ _ _ _ ?glo ?ghi ?mm =>
      replace glo with zlo by lia; replace ghi with zhi by lia; exact SF end.
  Qed.
End VF.
End RA_v05d.


Module RA_vrre.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require ImgA RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_f93z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_tzg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_f93z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_v05d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpesd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac low_lemma P ::= RA_f93z.low_lemma_pf P.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= relow_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= relow_all W m m' MU.
Local Ltac icpt_consts_in H ::= unfold PCM_STACK, VF_DEPTH in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfdx.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.

Definition VFI_DEPTH : Z := 5344.

(* [comment removed for export] *)
Definition vficpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m
  /\ ro_cells rsegs m 0xa9180 [C8 (Z_to_bv 64 0x146ee8)]
  /\ ro_cells rsegs m 0x146f3c [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xaaf28 [C8 (Z_to_bv 64 0x9ea00)].
Lemma lowP_vficpt_cells : lowP vficpt_cells.
Proof.
  unfold vficpt_cells, asan_inited_cell. repeat (apply lowP_and; [apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia|]).
  apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia.
Qed.

Definition vficpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo Fp D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (o : list byte) (canary : word)
    (A la : Z) (ZSB : Z) (ZK : nat)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (jd' : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length o))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - VFI_DEPTH, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' Fp (snfile z64 0 0 0 (Fp + 255) 0 mode' (Fp + 232))
    /\ rw_cells rsegs m' (Fp + 232) [C8 (Z_to_bv 64 (D + Z.of_nat (length (dl n o)))); C8 (Z_to_bv 64 ((Z.of_nat n - 1) - Z.of_nat (length (dl n o))))]
    /\ rw_cells rsegs m' D [CB n (dl n o ++ Z_to_bv 8 0 :: jd')]
    /\ va_area m' VA slots /\ bytes_at rsegs m' HS hs
    /\ ssp_cells m' canary
    /\ sf2 A la D n HS hs ZSB ZK (bv_unsigned sp - 960) (bv_unsigned sp - 320) m'
    /\ vficpt_cells m'.

Section VFI.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Hypothesis PCM : pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].

  #[using="FBY PCM P2 P1 HOUT HLA fbytes nargs"] Lemma vfprintf_icpt_sn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte)
      (lo A Fp D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs jd : list byte) (canary : word) (ZSB : Z) (ZK : nat),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    stk rsegs m lo (bv_unsigned sp) -> ro_cells rsegs m A FMT -> ssp_cells m canary ->
    rw_cells rsegs m Fp (snfile z64 0 0 0 (Fp + 255) 0 z64 (Fp + 232)) ->
    rw_cells rsegs m (Fp + 232) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (Z.of_nat n - 1))] ->
    rw_cells rsegs m D [CB n (Z_to_bv 8 0 :: jd)] ->
    va_area m VA slots -> bytes_at rsegs m HS hs -> PRE slots HS hs -> SLOTS slots -> mem_inv rsegs m ->
    sf2 A la D n HS hs ZSB ZK (bv_unsigned sp - 960) (bv_unsigned sp - 320) m ->
    vficpt_cells m ->
    Fp = bv_unsigned sp ->
    (lo <= bv_unsigned sp - VFI_DEPTH)%Z -> (alloc_ceiling <= lo)%Z -> (Fp + 304 <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
    (IMG_LO <= A)%Z -> (A + la <= RO_TOP)%Z -> dst_ok D n -> (D + Z.of_nat n <= lo)%Z -> dst_zone D (Z.of_nat n) -> (Z.of_nat n <= 2^31)%Z ->
    (HS + Z.of_nat (length hs) <= lo)%Z -> (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z ->
    evt rsegs (vficpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fp D n VA slots HS hs (OUT slots hs) canary A la ZSB ZK m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x47a30) fc None m (seg_rom rsegs)).
  Proof.
    intros until ZK. intros -> -> -> ST HF SSP FL CKC DST VAA HSB HPRE HSL MI SF VC HFp LO GT VLO VHI ARL ART GD DLO KH N31 HSLO HSD.
    pose proof SSP as [SSP1 SSP2]. pose proof VC as (CI & Gcf & Ccp & Creal). unfold asan_inited_cell in CI.
    unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, VFI_DEPTH, dst_ok, IMG_LO, IMG_HI, kHighMemBeg_z in *.
    pose proof alloc_ceiling_val as CV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB.
    pose proof (munch_refl [(bv_unsigned sp - 5344, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (LFB : (Z.of_nat (length fbytes) + 1 = la)%Z).
    { assert (W : cells_wf FMT) by exact (proj1 HF).
      rewrite <- HLA, <- (cells_bytes_length FMT W), FBY, length_app. cbn [length]. lia. }
    unfold va_area in VAA.
    zs. (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 9 zs.
    (* [comment removed for export] *)
    zs. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => unfold asan_inited_cell; eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zs. brf K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0. cbv in K0. lia. }
    zs. zs. zs. zs. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z. zs.
    zs. brf K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1. cbv in K1. lia. }
    zs. zs. zs. zs.
    (* [comment removed for export] *)
    zs. call_icpt PCM by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ (_ ++ [Z_to_bv 8 0]) => rewrite ?unsigned_lit by lia; rewrite <- FBY; match goal with HFq : ro_cells _ _ A FMT |- _ => exact (proj2 HFq) end
      | |- bytes_at _ _ _ (u64s _) => rewrite ?unsigned_lit by lia; eassumption
      | |- SLOTS _ => exact HSL
      | |- map_cells _ => match goal with SFq : sf2 _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj2 (proj2 (proj2 (proj1 SFq)))) end
      | |- mem_inv _ _ => eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- range_ok _ _ _ => rewrite ?unsigned_lit by lia; rewrite LFB;
            match goal with SFq : sf2 _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (sf2_RA _ _ _ _ _ _ _ _ _ _ _ SFq) end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; reflexivity
      | |- dst_zone _ _ => first [assumption | eapply dst_zone_sub; [eassumption| lia| lia]]
      | |- _ => rewrite ?unsigned_lit by lia; unfold PCM_STACK; lia
      end).
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    zs. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL); call_icpt (vfprintf_sn_spec FMT la nargs PRE OUT HLA HOUT P1 P2) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- rw_cells _ _ _ (snfile _ _ _ _ _ _ _ _) => eassumption
      | |- rw_cells _ _ _ [C8 _; C8 _] => eassumption
      | |- rw_cells _ _ _ [CB _ _] => eassumption
      | |- va_area _ _ _ => unfold va_area; eassumption
      | |- bytes_at _ _ _ _ => eassumption
      | |- PRE _ _ _ => exact HPRE
      | |- dst_ok _ _ => unfold dst_ok, IMG_LO, IMG_HI; exact GD
      | |- sf2 _ _ _ _ _ _ _ _ _ _ _ => rewrite ?unsigned_lit by lia;
            match goal with SFq : sf2 _ _ _ _ _ _ _ _ ?zlo ?zhi ?mm |- sf2 _ _ _ _ _ _ _ _ ?glo ?ghi ?mm =>
              replace glo with zlo by lia; replace ghi with zhi by lia; exact SFq end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [ reflexivity | f_equal; lia | lia ]
      | |- dst_zone _ _ => first [assumption | eapply dst_zone_sub; [eassumption| lia| lia]]
      | |- _ => rewrite ?unsigned_lit by lia; unfold VF_DEPTH, GLOBALS_TOP, RO_TOP, IMG_LO, kHighMemBeg_z in *; lia
      end).
    (* [comment removed for export] *)
    clear SF. rename POST into SF.
    do 5 zs.
    match goal with H : stk _ _ lo _ |- _ => rename H into ST' end.
    release_frame FR ST' (bv_unsigned sp).
    zs.
    first [apply evt_done | idtac]. unfold vficpt_post, VFI_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST'|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|].
    split. { match goal with SFq : sf2 _ _ _ _ _ _ _ _ ?zlo ?zhi ?mm |- sf2 _ _ _ _ _ _ _ _ ?glo ?ghi ?mm =>
               replace glo with zlo by lia; replace ghi with zhi by lia; exact SFq end. }
    split; [unfold asan_inited_cell; assumption|]. split; [assumption|]. split; assumption.
  Qed.
End VFI.
End RA_vrre.


Module RA_vt1z.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require ImgA RA_m7de RA_seql.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_m7de OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_v05d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpesd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac low_lemma P ::= RA_f93z.low_lemma_pf P.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= relow_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= relow_all W m m' MU.
Local Ltac icpt_consts_in H ::= unfold STRNLEN_ICPT_STACK, MEMCPY_ICPT_STACK, MEMSET_ICPT_STACK, VFI_DEPTH in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfdx.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

Definition VSN_DEPTH : Z := 5648.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sfv (A la D : Z) (n : nat) (HS : Z) (hs : list byte) (SB : Z) (K : nat) (zlo zhi : Z) (m : word -> option byte) : Prop :=
  sf2 A la D n HS hs SB K zlo zhi m /\ asan_memset_cells m /\ vficpt_cells m.
Lemma lowP_sfv : forall A la D n HS hs SB K zlo zhi, (0 <= la)%Z -> lowP (sfv A la D n HS hs SB K zlo zhi).
Proof.
  intros. apply lowP_and; [apply lowP_sf2; assumption|]. apply lowP_and; [apply lowP_asan_memset_cells| apply lowP_vficpt_cells].
Qed.
Local Ltac low_lemma P ::= lazymatch P with
  | sfv ?A ?la ?D ?n ?HS ?hs ?SB ?K ?zlo ?zhi => constr:(lowP_sfv A la D n HS hs SB K zlo zhi ltac:(lia))
  | vficpt_cells => constr:(lowP_vficpt_cells)
  | _ => RA_f93z.low_lemma_pf P end.

Lemma sf2_narrow : forall A la D n HS hs SB K zlo zhi zlo' zhi' m,
  sf2 A la D n HS hs SB K zlo zhi m -> (zlo <= zlo')%Z -> (zhi' <= zhi)%Z -> (zlo' <= zhi')%Z -> sf2 A la D n HS hs SB K zlo' zhi' m.
Proof.
  intros until m. intros (C1 & C2 & R1 & R2 & H5 & ZS & ZB & SBL) H1 H2 H3.
  refine (conj C1 (conj C2 (conj R1 (conj R2 (conj H5 (conj ZS (conj _ SBL))))))). eapply zsh_bounds_sub; eassumption.
Qed.

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (o : list byte) (canary : word)
    (A la : Z) (ZSB : Z) (ZK : nat)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jd' : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length o))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 5648, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' D [CB n (firstn (n - 1) o ++ Z_to_bv 8 0 :: jd')]
    /\ va_area m' VA slots /\ bytes_at rsegs m' HS hs
    /\ ssp_cells m' canary
    /\ (Z.of_nat (length o) < 2^31)%Z
    /\ sfv A la D n HS hs ZSB ZK (bv_unsigned sp - 5648) (bv_unsigned sp) m'.

Lemma le8_z64 : le8 z64 = repeat (Z_to_bv 8 0) 8.
Proof. unfold le8, z64. cbn. rewrite ?unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition zfile : list cell :=
  [C4 z64; C4 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64;
   C8 z64; C8 z64; C4 z64; C4 z64; C8 z64; C4 z64; C4 z64; C4 z64; C4 z64; C8 z64;
   C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].
Lemma zfile_bytes : cells_bytes zfile = repeat (Z_to_bv 8 0) 232.
Proof. unfold zfile. cbn [cells_bytes cbytes]. rewrite !le8_z64, !le4_z64. reflexivity. Qed.
Lemma zfile_wf : cells_wf zfile.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit. Qed.
Lemma snfile_wf : forall fl we wp wb bf bs md ck, cells_wf (snfile fl we wp wb bf bs md ck).
Proof. intros. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit. Qed.

Section VSN.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].

  #[using="FBY PCM fbytes P2 P1 HOUT HLA nargs"] Lemma vsnprintf_gen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte)
      (lo A D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs jd : list byte) (canary : word) (ZSB : Z) (ZK : nat),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat n) -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    stk rsegs m lo (bv_unsigned sp) -> ro_cells rsegs m A FMT -> ssp_cells m canary ->
    rw_cells rsegs m D [CB n jd] -> va_area m VA slots -> bytes_at rsegs m HS hs -> PRE slots HS hs -> SLOTS slots ->
    mem_inv rsegs m ->
    sfv A la D n HS hs ZSB ZK (bv_unsigned sp - 5648) (bv_unsigned sp) m ->
    (1 <= n)%nat ->
    (lo <= bv_unsigned sp - VSN_DEPTH)%Z -> (alloc_ceiling <= lo)%Z -> (bv_unsigned sp <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
    (IMG_LO <= A)%Z -> (A + la <= RO_TOP)%Z -> dst_ok D n -> (D + Z.of_nat n <= lo)%Z -> dst_zone D (Z.of_nat n) -> (Z.of_nat n <= 2^31)%Z ->
    (HS + Z.of_nat (length hs) <= lo)%Z -> (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z ->
    evt rsegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D n VA slots HS hs (OUT slots hs) canary A la ZSB ZK m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa1b2c) fc None m (seg_rom rsegs)).
  Proof.
    intros until ZK. intros -> -> -> -> ST HF SSP DST VAA HSB HPRE HSL MI SF N1 LO GT VLO VHI ARL ART GD DLO KH N31 HSLO HSD.
    destruct SSP as [SSP1 SSP2]. pose proof alloc_ceiling_val as CV.
    unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, VSN_DEPTH, dst_ok, IMG_LO, IMG_HI, kHighMemBeg_z in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB.
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
    pose proof (munch_refl [(bv_unsigned sp - 5648, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    unfold va_area in VAA.
    carve_frame 304%nat ST.
    zto 0xa1b60%Z. zs. br K. clear K.
    zto 0xa1b78%Z.
    (* [comment removed for export] *)
    replace (Z.of_nat n <? Z.of_nat n + -1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z.
    replace (Z.land 18446744073709551615 (Z.of_nat n + -1)) with (Z.of_nat n + -1)%Z
      by (rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zto 0x57614%Z.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [FFILE FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -304 + Z.of_nat 232)%Z with (bv_unsigned sp + -72)%Z in FR by lia.
    name_junk FFILE. name_junk FR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut; [ eapply memset_callv with (lo := lo) | post_call_icpt rsegs mq ] end.
    { exact FFILE. } { lia. } { lia. } { lia. } { assumption. }
    { match goal with SFq : sfv _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 (proj2 SFq)) end. }
    { rewrite ?unsigned_lit by lia. eassumption. } { rewrite ?unsigned_lit by lia. lia. } { assumption. }
    { rewrite ?unsigned_lit by lia. lia. }
    { right. match goal with SFq : sfv _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        eapply (sf2_stack_range _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 SFq)); lia end. }
    match goal with H : stk rsegs _ lo _ |- _ => rename H into ST end.
    match goal with H : rw_cells _ _ _ [CB (Z.to_nat 232) _] |- _ =>
      pose proof (rw_cells_recast rsegs _ _ _ zfile H zfile_wf ltac:(rewrite zfile_bytes; reflexivity)) as FL; clear H end.
    unfold zfile, z64 in FL.
    zto 0xa1bb8%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (FL' : rw_cells rsegs mq (bv_unsigned sp + -304) (snfile z64 0 0 0 ((bv_unsigned sp + -304) + 255) 0 z64 ((bv_unsigned sp + -304) + 232))) end.
    { eapply rw_cells_recast; [exact FL | apply snfile_wf |].
      unfold snfile, z64, m1w, SN_WRITE. cbn [cells_bytes cbytes].
      replace (bv_unsigned sp + -304 + 255)%Z with (bv_unsigned sp + -49)%Z by lia.
      replace (bv_unsigned sp + -304 + 232)%Z with (bv_unsigned sp + -72)%Z by lia. reflexivity. }
    clear FL.
    (* [comment removed for export] *)
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA.
    pose proof (u8arr_store_ok rsegs _ _ _ 0 (Z_to_bv 64 D) DA ltac:(rewrite LD; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq _ _) _) =>
          replace (write_to_mem mq (Z_to_bv 64 D) [Z_to_bv 8 0]) with (write_to_mem mq (wa (D + 0)) [Z_to_bv 8 0]) by (unfold wa; f_equal; f_equal; lia) end.
    pose proof (u8arr_write rsegs _ _ _ 0 (Z_to_bv 8 0) DA ltac:(rewrite LD; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LD in DST. clear DA2.
    rewrite upd_firstn_skipn in DST by (rewrite LD; lia). cbn [Z.to_nat firstn app] in DST.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [CKC FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -72 + Z.of_nat 16)%Z with (bv_unsigned sp + -56)%Z in FR by lia.
    zto 0x47a30%Z.
    (* [comment removed for export] *)
    call_icpt (vfprintf_icpt_sn_spec FMT la nargs PRE OUT fbytes SLOTS HLA HOUT P1 P2 PCM FBY) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- rw_cells _ _ _ (snfile _ _ _ _ _ _ _ _) => rewrite ?unsigned_lit by lia; exact FL'
      | |- rw_cells _ _ _ [C8 _; C8 _] => rewrite ?unsigned_lit by lia; eapply rwc_eq; [exact CKC | lia]
      | |- rw_cells _ _ _ [CB _ _] => exact DST
      | |- va_area _ _ _ => exact VAA
      | |- bytes_at _ _ _ _ => eassumption
      | |- PRE _ _ _ => exact HPRE
      | |- SLOTS _ => exact HSL
      | |- dst_ok _ _ => unfold dst_ok, IMG_LO, IMG_HI; exact GD
      | |- sf2 _ _ _ _ _ _ _ _ _ _ _ => rewrite ?unsigned_lit by lia;
            match goal with SFq : sfv _ _ _ _ _ _ _ _ _ _ _ |- _ => eapply (sf2_narrow _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 SFq)); lia end
      | |- vficpt_cells _ => match goal with SFq : sfv _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj2 (proj2 SFq)) end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [ reflexivity | f_equal; lia | lia ]
      | |- dst_zone _ _ => first [assumption | eapply dst_zone_sub; [eassumption| lia| lia]]
      | |- _ => rewrite ?unsigned_lit by lia; unfold VFI_DEPTH, GLOBALS_TOP, RO_TOP, IMG_LO, kHighMemBeg_z in *; lia
      end || match goal with |- ?G => idtac "VFSIDE-FAIL:" G end).
    rename PC into ST. try clear SSP1; try clear SSP2. destruct PC5 as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2.
    (* [comment removed for export] *)
    clear PC6 POST.
    zto 0xa1bd4%Z. zs. brf Kc. { exfalso. apply Kc. reflexivity. } clear Kc.
    (* [comment removed for export] *)
    unfold snfile, z64, m1w, SN_WRITE in PC0.
    lazymatch type of PC0 with rw_cells _ ?mq _ ?cs0 => lazymatch type of PC1 with rw_cells _ _ _ ?cs1 => lazymatch type of FR with rw_cells _ _ _ ?cs2 =>
      assert (FR' : rw_cells rsegs mq (bv_unsigned sp + -304) (cs0 ++ cs1 ++ cs2));
      [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact PC0|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_;_] _)); split; [eapply rwc_eq; [exact PC1|lia]|]; cbn [cells_size csize Nat.add];
        eapply rwc_eq; [exact FR|lia]
      | clear PC0 PC1 FR; cbn [app] in FR'; rename FR' into FR ] end end end.
    do 7 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact PC2|]. split; [exact PC3|]. split; [exact PC4|]. split; [split; assumption|]. split; [apply (HOUT _ _ _ HPRE)|].
    assumption.
  Qed.
End VSN.
End RA_vt1z.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_tzg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_f93z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_v05d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vt1z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpesd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac low_lemma P ::= lazymatch P with
  | sfv ?A ?la ?D ?n ?HS ?hs ?SB ?K ?zlo ?zhi => constr:(lowP_sfv A la D n HS hs SB K zlo zhi ltac:(lia))
  | vficpt_cells => constr:(lowP_vficpt_cells)
  | _ => RA_f93z.low_lemma_pf P end.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= relow_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= relow_all W m m' MU.
Local Ltac icpt_consts_in H ::= unfold PCM_STACK, VSN_DEPTH in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfdx.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].
Ltac brf K := if_cases K; zify_cond K.

Definition VSNPRINTF_ICPT_ENTRY : Z := 0x47a34.
Definition VSNPRINTF_ICPT_STACK : Z := 7808.

(* [comment removed for export] *)
Definition vsnicpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m
  /\ ro_cells rsegs m 0xa9180 [C8 (Z_to_bv 64 0x146ee8)]
  /\ ro_cells rsegs m 0x146f3c [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xaaf30 [C8 (Z_to_bv 64 0xa1b2c)].
Lemma lowP_vsnicpt_cells : lowP vsnicpt_cells.
Proof.
  unfold vsnicpt_cells, asan_inited_cell. repeat (apply lowP_and; [apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia|]).
  apply lowP_ro_cells; cbn; unfold in_zone, kHighMemBeg_z; lia.
Qed.

(* [comment removed for export] *)
Definition sfi (A la D : Z) (n : nat) (HS : Z) (hs : list byte) (SB : Z) (K : nat) (zlo zhi : Z) (m : word -> option byte) : Prop :=
  sfv A la D n HS hs SB K zlo zhi m /\ vsnicpt_cells m.
Lemma lowP_sfi : forall A la D n HS hs SB K zlo zhi, (0 <= la)%Z -> lowP (sfi A la D n HS hs SB K zlo zhi).
Proof. intros. apply lowP_and; [apply lowP_sfv; assumption| apply lowP_vsnicpt_cells]. Qed.
Lemma sfi_map_cells : forall A la D n HS hs SB K zlo zhi m, sfi A la D n HS hs SB K zlo zhi m -> map_cells m.
Proof. intros until m. intros (((C1 & _) & _) & _). exact (proj2 (proj2 (proj2 C1))). Qed.
Lemma sfi_RD : forall A la D n HS hs SB K zlo zhi m, sfi A la D n HS hs SB K zlo zhi m -> range_ok m D (Z.of_nat n).
Proof. intros until m. intros ((S2 & _) & _). exact (sf2_RD _ _ _ _ _ _ _ _ _ _ _ S2). Qed.
Lemma sfv_narrow : forall A la D n HS hs SB K zlo zhi zlo' zhi' m,
  sfv A la D n HS hs SB K zlo zhi m -> (zlo <= zlo')%Z -> (zhi' <= zhi)%Z -> (zlo' <= zhi')%Z -> sfv A la D n HS hs SB K zlo' zhi' m.
Proof. intros until m. intros (S2 & C1 & C2) H1 H2 H3. split; [eapply sf2_narrow; eassumption| split; assumption]. Qed.
Lemma sfi_narrow : forall A la D n HS hs SB K zlo zhi zlo' zhi' m,
  sfi A la D n HS hs SB K zlo zhi m -> (zlo <= zlo')%Z -> (zhi' <= zhi)%Z -> (zlo' <= zhi')%Z -> sfi A la D n HS hs SB K zlo' zhi' m.
Proof. intros until m. intros (S2 & C) H1 H2 H3. split; [eapply sfv_narrow; eassumption| exact C]. Qed.
Local Ltac low_lemma P ::= lazymatch P with
  | sfi ?A ?la ?D ?n ?HS ?hs ?SB ?K ?zlo ?zhi => constr:(lowP_sfi A la D n HS hs SB K zlo zhi ltac:(lia))
  | sfv ?A ?la ?D ?n ?HS ?hs ?SB ?K ?zlo ?zhi => constr:(lowP_sfv A la D n HS hs SB K zlo zhi ltac:(lia))
  | vficpt_cells => constr:(lowP_vficpt_cells)
  | vsnicpt_cells => constr:(lowP_vsnicpt_cells)
  | _ => RA_f93z.low_lemma_pf P end.

Definition vsnicpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (o : list byte) (canary : word)
    (A la : Z) (ZSB : Z) (ZK : nat)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jd' : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length o))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - VSNPRINTF_ICPT_STACK, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' D [CB n (firstn (n - 1) o ++ Z_to_bv 8 0 :: jd')]
    /\ va_area m' VA slots /\ bytes_at rsegs m' HS hs
    /\ ssp_cells m' canary
    /\ (Z.of_nat (length o) < 2^31)%Z
    /\ sfi A la D n HS hs ZSB ZK (bv_unsigned sp - VSNPRINTF_ICPT_STACK) (bv_unsigned sp - 2160) m'.

Section VSNI.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].

  Section S.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
    Variables (lo A D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word) (ZSB : Z) (ZK : nat) (L : Z).
    Notation o := (OUT slots hs).
    Notation POST := (vsnicpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D n VA slots HS hs o canary A la ZSB ZK m).
    Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation FRAME2 m1 va j8 := (rw_cells rsegs m1 (bv_unsigned sp + -96) [C8 va; C8 va; CB 8 j8]).
    Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2160) [CB 2064 fjunk]).
    Hypothesis LOLE : (lo + VSNPRINTF_ICPT_STACK <= bv_unsigned sp)%Z.
    Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
    Hypothesis KH : dst_zone D (Z.of_nat n).   (* [comment removed for export] *)
    Hypothesis DLO : (D + Z.of_nat n <= lo)%Z.
    Hypothesis HSLO : (HS + Z.of_nat (length hs) <= lo)%Z.
    Hypothesis VLO : (bv_unsigned sp <= VA)%Z.
    Hypothesis N1 : (1 <= n)%nat.
    Hypothesis N31 : (Z.of_nat n <= 2^31)%Z.
    Hypothesis L32 : (1 <= L <= Z.of_nat n)%Z.
    Hypothesis OL : (Z.of_nat (length o) + 1 < 2^31)%Z.
    Hypothesis HLA0 : (0 <= la)%Z.

    (* [comment removed for export] *)
    #[using="OL N1 LOLE FMT"] Lemma vi_exit : forall m1 fjunk va j8 jd' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
      mem_inv rsegs m1 -> munch [(bv_unsigned sp - VSNPRINTF_ICPT_STACK, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m m1 -> wmono rsegs m m1 ->
      stk rsegs m1 lo (bv_unsigned sp + -2160) -> FRAME m1 -> FRAME2 m1 va j8 -> FRAMEB m1 fjunk ->
      rw_cells rsegs m1 D [CB n (firstn (n - 1) o ++ Z_to_bv 8 0 :: jd')] -> va_area m1 VA slots -> bytes_at rsegs m1 HS hs ->
      ssp_cells m1 canary -> sfi A la D n HS hs ZSB ZK (bv_unsigned sp - VSNPRINTF_ICPT_STACK) (bv_unsigned sp - 2160) m1 ->
      evt rsegs POST
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
                 (Z_to_bv 64 (Z.of_nat (length o))) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4b000) fc None m1 (seg_rom rsegs)).
    Proof.
      intros until x31. intros MI1 MU1 WM1 ST1 FR1 FR2 FRB1 DST1 VA1 HSB1 SSP1 SF1. unfold VSNPRINTF_ICPT_STACK in *.
      pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
      do 11 zs.
      lazymatch type of FRB1 with rw_cells _ ?mq _ ?c0 => lazymatch type of FR2 with rw_cells _ _ _ ?c1 => lazymatch type of FR1 with rw_cells _ _ _ ?c2 =>
        assert (FR : rw_cells rsegs mq (bv_unsigned sp + -2160) (c0 ++ c1 ++ c2));
        [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FRB1|]; cbn [cells_size csize Nat.add];
          apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [eapply rwc_eq; [exact FR2| lia]|]; cbn [cells_size csize Nat.add];
          eapply rwc_eq; [exact FR1| lia]
        | clear FRB1 FR2 FR1; cbn [app] in FR ] end end end.
      release_frame FR ST1 (bv_unsigned sp).
      zs.
      first [apply evt_done | idtac]. unfold vsnicpt_post, VSNPRINTF_ICPT_STACK. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [assumption|]. split; [exact ST1|].
      split; [exact DST1|]. split; [exact VA1|]. split; [exact HSB1|]. split; [exact SSP1|]. split; [lia|]. exact SF1.
    Qed.

    Section Phase.
      Variables (m1 : word -> option byte) (fjunk jd' : list byte) (va : word) (j8 : list byte).
      Variables (ng : nat) (lastb : Z) (w1 w2 : word).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - VSNPRINTF_ICPT_STACK, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2160).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FR2 : FRAME2 m1 va j8.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis DST1 : rw_cells rsegs m1 D [CB n (firstn (n - 1) o ++ Z_to_bv 8 0 :: jd')].
      Hypothesis VA1 : va_area m1 VA slots.
      Hypothesis HSB1 : bytes_at rsegs m1 HS hs.
      Hypothesis SSP1 : ssp_cells m1 canary.
      Hypothesis SF1 : sfi A la D n HS hs ZSB ZK (bv_unsigned sp - VSNPRINTF_ICPT_STACK) (bv_unsigned sp - 2160) m1.
      Hypothesis Gsh : ro_cells rsegs m1 0xa9190 [C8 (Z_to_bv 64 0xb53b8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa9198 [C8 (Z_to_bv 64 0xb60a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb60a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa91a0 [C8 (Z_to_bv 64 0xb60b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb60b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa91a8 [C8 (Z_to_bv 64 0xb60a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb60a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis IR : inmem_range D L.
      Hypothesis NG : ((D + L - 1) / 8 - D / 8 = Z.of_nat ng)%Z.
      Hypothesis SH1 : bytes_at rsegs m1 (D / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
      Hypothesis QB1 : bytes_at rsegs m1 (sha D - sha D mod 8) (le8 w1).
      Hypothesis QB2 : bytes_at rsegs m1 (sha (D + L + -1) - sha (D + L + -1) mod 8) (le8 w2).
      Notation RES := (Z.of_nat (length o)).

      Section Slow.
        Variables (sf sl : Z) (x1 x5 x6 x7 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : word).
        Hypothesis ESF : (sf = D / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.
        Notation AT pc x11 x13 x14 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp (Z_to_bv 64 L)
                   (Z_to_bv 64 RES) x11 (Z_to_bv 64 sl) x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 (Z.of_nat n)) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        #[using="SF1 SSP1 HSB1 VA1 DST1 FRB1 FR2 FR1 ST1 WM1 MU1 MI1 ng j8 va jd' fjunk OL N1 LOLE FMT"] Lemma vi_slow_end : forall x11 x14, (lastb = 0 \/ ((D + L - 1) mod 8 < lastb <= 7))%Z -> evt rsegs POST (AT 0x4b130 x11 (Z_to_bv 64 0) x14).
        Proof.
          intros x11 x14 LB. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. unfold VSNPRINTF_ICPT_STACK in *.
          zs. zs. brf Kb; try (deadK Kb).
          eapply vi_exit; try eassumption.
        Qed.

        #[using="ESL ESF SH1 SF1 SSP1 HSB1 VA1 DST1 FRB1 FR2 FR1 ST1 WM1 MU1 MI1 j8 va jd' fjunk OL N1 LOLE FMT"] Lemma vi_slow_loop : forall (cc : nat) (j : Z) x11 x14,
          (lastb = 0 \/ ((D + L - 1) mod 8 < lastb <= 7))%Z ->
          Z.to_nat (Z.of_nat ng - j) = cc -> (0 <= j < Z.of_nat ng)%Z -> x11 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x4b120 x11 (Z_to_bv 64 0) x14).
        Proof.
          induction cc as [|cc IH]; intros j x11 x14 LB Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (D / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zs. zs.
          zs. brf Kb.
          - apply (IH (j + 1)%Z); [exact LB|lia|lia|f_equal; lia].
          - apply vi_slow_end. exact LB.
        Qed.
      End Slow.

      (* [comment removed for export] *)
      #[using="QB2 QB1 SH1 NG IR Che Ghe Cme Gme Cmb Gmb Csh Gsh SF1 SSP1 HSB1 VA1 DST1 FRB1 FR2 FR1 ST1 WM1 MU1 MI1 w2 w1 ng j8 va jd' fjunk HLA0 OL L32 N31 N1 VLO HSLO DLO CEIL LOLE FMT Clg"] Lemma vi_phase : forall (xs1 : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
        xs1 = Z_to_bv 64 L -> (lastb = 0 \/ ((D + L - 1) mod 8 < lastb <= 7))%Z ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp xs1
                   (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 (Z.of_nat n)) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x4afb8) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros -> LB. unfold VSNPRINTF_ICPT_STACK in *.
        pose proof LOLE as LOLE'. pose proof MU1 as MU. pose proof WM1 as WM. pose proof MI1 as MIq. pose proof ST1 as ST'.
        pose proof VA1 as VA'. unfold va_area in VA'. pose proof SSP1 as [SSPa SSPb]. unfold GOT_SSP, SSP_GUARD in SSPa, SSPb. pose proof HSB1 as HSB'.
        pose proof (bytes_at_bound _ _ _ _ HSB') as HSBB. pose proof (bytes_at_bound _ _ _ _ VA') as VAB.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        assert (AF : (0 <= D /\ D + L + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
        assert (QH1 : (sha D - sha D mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (D + L + -1) - sha (D + L + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SH1 as SH. remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
        assert (SHhi : (D / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QB1 as QB1'. pose proof QB2 as QB2'.
        zs. zs.
        zs. brf K2.
        - (* [comment removed for export] *)
          zs. brf K3. 2:{ exfalso. lia. }
          zs. zs. zs.
          zs. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST'
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IR
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ng, lastb; subst sbs; split; [exact NG| split; [exact SH| exact LB]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          zs. zs.
          zs. brf K4; try (deadK K4).
          subst sbs. eapply vi_exit; try eassumption.
          all: first [ match goal with H : bytes_at _ _ VA _ |- va_area _ VA _ => exact H end | split; assumption | idtac ].
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr D 3 <= D)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (D + L + -1) 3 <= D + L - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 11 zs.
          pose proof (qc_read _ _ _ QB1' ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2' ltac:(lia)) as RD2.
          zs. zs. zs.
          zs. brf K7.
          + subst sbs.
            assert (LBR : (0 <= lastb < 128)%Z) by lia.
            pose proof (u8ro_read rsegs _ (D / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (D + L + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zs. rewrite sxb_small by lia.
            zs. zs. zs. zs. zs.
            rewrite (poisoned_last_zero (D + L + -1) lastb) by
              (first [lia | destruct LB as [LB0|LB1]; [left; exact LB0| right; replace (D + L + -1)%Z with (D + L - 1)%Z by lia; lia]]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + D / 8)%Z). set (sl := (2147450880 + (D + L + -1) / 8)%Z).
            assert (ESF : (sf = D / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl.
            zs. brf K8.
            * eapply vi_slow_end; eassumption.
            * eapply vi_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs. eapply vi_exit; try eassumption.
            all: first [ match goal with H : bytes_at _ _ VA _ |- va_area _ VA _ => exact H end | split; assumption | idtac ].
      Qed.
    End Phase.
  End S.

  #[using="FBY PCM fbytes P2 P1 HOUT1 HOUT HLA nargs"] Lemma vsnprintf_icpt_gen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte)
      (lo A D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs jd : list byte) (canary : word) (ZSB : Z) (ZK : nat),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat n) -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    stk rsegs m lo (bv_unsigned sp) -> ro_cells rsegs m A FMT -> ssp_cells m canary ->
    rw_cells rsegs m D [CB n jd] -> va_area m VA slots -> bytes_at rsegs m HS hs -> PRE slots HS hs -> SLOTS slots ->
    mem_inv rsegs m ->
    sfi A la D n HS hs ZSB ZK (bv_unsigned sp - VSNPRINTF_ICPT_STACK) (bv_unsigned sp) m ->
    (1 <= n)%nat ->
    (lo <= bv_unsigned sp - VSNPRINTF_ICPT_STACK)%Z -> (alloc_ceiling <= lo)%Z -> (bv_unsigned sp <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
    (IMG_LO <= A)%Z -> (A + la <= RO_TOP)%Z -> dst_ok D n -> (D + Z.of_nat n <= lo)%Z -> dst_zone D (Z.of_nat n) -> (Z.of_nat n <= 2^31)%Z ->
    (HS + Z.of_nat (length hs) <= lo)%Z -> (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z ->
    evt rsegs (vsnicpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D n VA slots HS hs (OUT slots hs) canary A la ZSB ZK m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF_ICPT_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    intros until ZK. intros -> -> -> -> ST HF SSP DST VAA HSB HPRE HSL MI SF N1 LO GT VLO VHI ARL ART GD DLO KH N31 HSLO HSD.
    pose proof SSP as [SSP1 SSP2]. pose proof SF as (_ & (CI & Gcf & Ccp & Creal)). unfold asan_inited_cell in CI.
    unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, VSNPRINTF_ICPT_STACK, VSNPRINTF_ICPT_ENTRY, dst_ok, IMG_LO, IMG_HI, kHighMemBeg_z in *.
    pose proof alloc_ceiling_val as CV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB.
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
    pose proof (munch_refl [(bv_unsigned sp - 7808, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (HLA0 : (0 <= la)%Z) by lia.
    assert (LFB : (Z.of_nat (length fbytes) + 1 = la)%Z).
    { assert (W : cells_wf FMT) by exact (proj1 HF).
      rewrite <- HLA, <- (cells_bytes_length FMT W), FBY, length_app. cbn [length]. lia. }
    pose proof (HOUT1 _ _ _ HPRE) as OL.
    unfold va_area in VAA.
    zs. (* [comment removed for export] *)
    carve_frame 72%nat ST. carve_frame 24%nat ST. carve_frame 2064%nat ST.
    do 17 zs.
    (* [comment removed for export] *)
    zs. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => unfold asan_inited_cell; eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zs. brf K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0. cbv in K0. lia. }
    zs. zs. zs. zs. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z. zs.
    zs. brf K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1. cbv in K1. lia. }
    zs. zs. zs. zs.
    (* [comment removed for export] *)
    zs. call_icpt PCM by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ (_ ++ [Z_to_bv 8 0]) => rewrite ?unsigned_lit by lia; rewrite <- FBY; match goal with HFq : ro_cells _ _ A FMT |- _ => exact (proj2 HFq) end
      | |- bytes_at _ _ _ (u64s _) => rewrite ?unsigned_lit by lia; eassumption
      | |- SLOTS _ => exact HSL
      | |- map_cells _ => match goal with SFq : sfi _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (sfi_map_cells _ _ _ _ _ _ _ _ _ _ _ SFq) end
      | |- mem_inv _ _ => eassumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- range_ok _ _ _ => rewrite ?unsigned_lit by lia; rewrite LFB;
            match goal with SFq : sfi _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (sf2_RA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj1 SFq))) end
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; reflexivity
      | |- dst_zone _ _ => first [assumption | eapply dst_zone_sub; [eassumption| lia| lia]]
      | |- _ => rewrite ?unsigned_lit by lia; unfold PCM_STACK; lia
      end).
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs.
    zs. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); call_icpt (vsnprintf_gen_spec FMT la nargs PRE OUT HLA HOUT P1 P2 fbytes SLOTS PCM FBY) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- rw_cells _ _ _ [CB _ _] => eassumption
      | |- va_area _ _ _ => unfold va_area; eassumption
      | |- bytes_at _ _ _ _ => eassumption
      | |- PRE _ _ _ => exact HPRE
      | |- SLOTS _ => exact HSL
      | |- dst_ok _ _ => unfold dst_ok, IMG_LO, IMG_HI; exact GD
      | |- sfv _ _ _ _ _ _ _ _ _ _ _ => rewrite ?unsigned_lit by lia;
            match goal with SFq : sfi _ _ _ _ _ _ _ _ _ _ _ |- _ => eapply (sfv_narrow _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 SFq)); lia end
      | |- le _ _ => exact N1
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [ reflexivity | f_equal; lia | lia ]
      | |- dst_zone _ _ => first [assumption | eapply dst_zone_sub; [eassumption| lia| lia]]
      | |- _ => rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, RO_TOP, IMG_LO, kHighMemBeg_z in *; lia
      end || match goal with |- ?G => idtac "VSNSIDE-FAIL:" G end).
    clear POST.
    match goal with SFq : sfi _ _ _ _ _ _ _ _ _ _ ?mq |- _ =>
      pose proof (sfi_narrow _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp - 7808) (bv_unsigned sp - 2160) _ SFq ltac:(lia) ltac:(lia) ltac:(lia)) as SFN;
      pose proof (sfi_RD _ _ _ _ _ _ _ _ _ _ _ SFq) as RD; pose proof (sfi_map_cells _ _ _ _ _ _ _ _ _ _ _ SFq) as MC; clear SFq end.
    open_map_cells MC.
    match goal with H : ssp_cells ?mq canary |- _ => pose proof H as [SSPa SSPb]; unfold GOT_SSP, SSP_GUARD in SSPa, SSPb end.
    match goal with H : va_area ?mq VA slots |- _ => pose proof H as VA'; unfold va_area in VA' end.
    (* [comment removed for export] *)
    zs. brf K2. all: try (exfalso; rewrite ?signed_small in K2 by lia; lia).
    zs. unfold sx32 || idtac.
    match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?z)] => rewrite (swrap32_id z) by lia | _ => idtac end.
    zs.
    (* [comment removed for export] *)
    assert (PH : forall L xs1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 mq,
      (1 <= L <= Z.of_nat n)%Z -> xs1 = Z_to_bv 64 L ->
      forall (MIq : mem_inv rsegs mq) (MUq : munch [(bv_unsigned sp - 7808, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m mq) (WMq : wmono rsegs m mq)
             (STq : stk rsegs mq lo (bv_unsigned sp + -2160))
             (FRq : rw_cells rsegs mq (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
             (FR0q : rw_cells rsegs mq (bv_unsigned sp + -96) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 (skipn 16 junk0)])
             (FR1q : rw_cells rsegs mq (bv_unsigned sp + -2160) [CB 2064 junk1])
             (DSTq : rw_cells rsegs mq D [CB n (firstn (n - 1) (OUT slots hs) ++ Z_to_bv 8 0 :: x43)])
             (VAq : va_area mq VA slots) (HSq : bytes_at rsegs mq HS hs) (SSq : ssp_cells mq canary)
             (SFq : sfi A la D n HS hs ZSB ZK (bv_unsigned sp - 7808) (bv_unsigned sp - 2160) mq),
      evt rsegs (vsnicpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D n VA slots HS hs (OUT slots hs) canary A la ZSB ZK m)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp xs1
                   (Z_to_bv 64 (Z.of_nat (length (OUT slots hs)))) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 (Z.of_nat n)) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x4afb8) fc None mq (seg_rom rsegs))).
    { intros until mq. intros HL -> MIq MUq WMq STq FRq FR0q FR1q DSTq VAq HSq SSq SFq.
      pose proof (sfi_RD _ _ _ _ _ _ _ _ _ _ _ SFq) as RDq. pose proof (sfi_map_cells _ _ _ _ _ _ _ _ _ _ _ SFq) as MCq. open_map_cells MCq.
      pose proof (range_ok_prefix _ _ _ L RDq ltac:(lia)) as (IR & (ng & lastb & NG & SH & LB) & QW1 & QW2).
      assert (AF : (0 <= D /\ D + L + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
      destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
      destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
      replace (D + L - 1)%Z with (D + L + -1)%Z in QB2 by lia.
      eapply (vi_phase ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A D n VA slots HS hs canary ZSB ZK L);
        unfold VSNPRINTF_ICPT_STACK; try eassumption; try reflexivity; try lia; try (eapply dst_zone_sub; [eassumption| lia| lia]). }
    zs. brf K3.
    - (* [comment removed for export] *)
      zs. zs. rewrite zb_lxor_ones by lia. zs. zs.
      zs. brf K4. (* [comment removed for export] *)
      all: try (exfalso; pose proof (sfi_RD _ _ _ _ _ _ _ _ _ _ _ SFN) as RDq; destruct RDq as (IRn & _); unfold inmem_range in IRn; lia).
      eapply (PH (Z.of_nat (length (OUT slots hs)) + 1)%Z); try eassumption; try lia. reflexivity.
    - (* [comment removed for export] *)
      zs. rewrite zb_lxor_ones by lia. zs. zs.
      zs. brf K4.
      all: try (exfalso; pose proof (sfi_RD _ _ _ _ _ _ _ _ _ _ _ SFN) as RDq; destruct RDq as (IRn & _); unfold inmem_range in IRn; lia).
      eapply (PH (Z.of_nat n)); try eassumption; try lia. reflexivity.
  Qed.
End VSNI.
