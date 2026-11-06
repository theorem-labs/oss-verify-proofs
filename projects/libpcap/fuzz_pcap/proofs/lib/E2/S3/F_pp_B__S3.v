(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_E.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_pp_B__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_pp_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac bd_F := try lstep; bfalse.
Local Ltac bd_T := try lstep; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Definition pflog_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt ssegs (ppost c (c_len0 c) (swap_pflog_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16100) (c_fc c) None m (seg_rom ssegs)).
Section Sz1.
Variables c : ltac2:(SecDiet.SzSec.tyM 'pflog_spec__stmt "v" @c).
#[using="Type"] Lemma pflog_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pflog_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pp_init WF I.
  unfold swap_pflog_header. cbn [h_caplen h_len].
  lstep. rewrite sx32_small by lia. lstep.
  gsplit_TF (c_caplen c) 48%Z.
  lstep. gsplit_TF (c_len0 c) 48%Z.
  rd1 0%Z. lstep. gsplit_TF constr:(get_u8 d 0) 48%Z.
  rd4 44%Z. do 12 lstep. st4 44%Z.
  gsplit_TF (c_caplen c) 52%Z. gsplit_TF (c_len0 c) 52%Z. lstep. gsplit_TF constr:(get_u8 d 0) 52%Z.
  rd4 48%Z. do 12 lstep. st4 48%Z.
  gsplit_TF (c_caplen c) 56%Z. gsplit_TF (c_len0 c) 56%Z. lstep. gsplit_TF constr:(get_u8 d 0) 56%Z.
  rd4 52%Z. do 12 lstep. st4 52%Z.
  gsplit_TF (c_caplen c) 60%Z. gsplit_TF (c_len0 c) 60%Z. lstep. gsplit_TF constr:(get_u8 d 0) 60%Z.
  rd4 56%Z. do 11 lstep. st4 56%Z.
  epilog.
Qed.
End Sz1.
Lemma pflog_spec : ltac:(let t := eval cbv delta [pflog_spec__stmt] in pflog_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'pflog_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sll_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt ssegs (ppost c (c_len0 c) (swap_linux_sll_socketcan_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x15cb4) (c_fc c) None m (seg_rom ssegs)).
Section Sz2.
Variables c : ltac2:(SecDiet.SzSec.tyM 'sll_spec__stmt "v" @c).
#[using="Type"] Lemma sll_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sll_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pp_init WF I.
  unfold swap_linux_sll_socketcan_header, swap_socketcan_header. cbn [h_caplen h_len].
  unfold LINUX_SLL_P_CAN, LINUX_SLL_P_CANFD, LINUX_SLL_P_CANXL.
  lstep. rewrite sx32_small by lia. lstep.
  gsplit_TF (c_caplen c) 16%Z.
  lstep. gsplit_TF (c_len0 c) 16%Z.
  rd1 14%Z. rd1 15%Z. do 7 lstep.
  rewrite lor_be16 by lia. unfold get_be16. replace (14 + 1)%Z with 15%Z by reflexivity.
  rewrite swrap_of_sx32 by lia. rewrite (swrap32_small (c_caplen c + -16)) by lia.
  set (p := (get_u8 d 14 * 256 + get_u8 d 15)%Z) in *. assert (RP : (0 <= p < 65536)%Z) by (subst p; lia).
  rewrite (ltu_minus12 p) by lia.
  destruct ((p =? 12) || (p =? 13))%Z eqn:E12; cbn [negb orb].
  - (* [comment removed for export] *)
    lstep. gsplit_TF (c_caplen c - 16)%Z 4%Z. gsplit_TF (c_len0 c - 16)%Z 4%Z.
    rd4 16%Z. do 11 lstep. st4 16%Z. epilog.
  - lstep. esplit_FT p 14%Z. 2:{ epilog. }
    lstep. gsplit_TF (c_caplen c - 16)%Z 4%Z. gsplit_TF (c_len0 c - 16)%Z 4%Z.
    rd4 16%Z. do 12 lstep. st4 16%Z.
    gsplit_TF (c_caplen c - 16)%Z 8%Z. gsplit_TF (c_len0 c - 16)%Z 8%Z.
    rd2 22%Z. do 4 lstep. st2 22%Z.
    gsplit_TF (c_caplen c - 16)%Z 12%Z. gsplit_TF (c_len0 c - 16)%Z 12%Z.
    rd4 24%Z. do 11 lstep. st4 24%Z. epilog.
Qed.
End Sz2.
Lemma sll_spec : ltac:(let t := eval cbv delta [sll_spec__stmt] in sll_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'sll_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sll2_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt ssegs (ppost c (c_len0 c) (swap_linux_sll2_socketcan_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x15c24) (c_fc c) None m (seg_rom ssegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'sll2_spec__stmt "v" @c).
#[using="Type"] Lemma sll2_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sll2_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pp_init WF I.
  unfold swap_linux_sll2_socketcan_header, swap_socketcan_header. cbn [h_caplen h_len].
  unfold LINUX_SLL_P_CAN, LINUX_SLL_P_CANFD, LINUX_SLL_P_CANXL.
  lstep. rewrite sx32_small by lia. lstep.
  gsplit_TF (c_caplen c) 20%Z.
  lstep. gsplit_TF (c_len0 c) 20%Z.
  rd1 0%Z. rd1 1%Z. do 7 lstep.
  rewrite lor_be16 by lia. unfold get_be16. replace (0 + 1)%Z with 1%Z by reflexivity.
  rewrite swrap_of_sx32 by lia. rewrite (swrap32_small (c_caplen c + -20)) by lia.
  set (p := (get_u8 d 0 * 256 + get_u8 d 1)%Z) in *. assert (RP : (0 <= p < 65536)%Z) by (subst p; lia).
  rewrite (ltu_minus12 p) by lia.
  destruct ((p =? 12) || (p =? 13))%Z eqn:E12; cbn [negb orb].
  - (* [comment removed for export] *)
    lstep. gsplit_TF (c_caplen c - 20)%Z 4%Z. gsplit_TF (c_len0 c - 20)%Z 4%Z.
    rd4 20%Z. do 11 lstep. st4 20%Z. epilog.
  - lstep. esplit_FT p 14%Z. 2:{ epilog. }
    lstep. gsplit_TF (c_caplen c - 20)%Z 4%Z. gsplit_TF (c_len0 c - 20)%Z 4%Z.
    rd4 20%Z. do 12 lstep. st4 20%Z.
    gsplit_TF (c_caplen c - 20)%Z 8%Z. gsplit_TF (c_len0 c - 20)%Z 8%Z.
    rd2 26%Z. do 4 lstep. st2 26%Z.
    gsplit_TF (c_caplen c - 20)%Z 12%Z. gsplit_TF (c_len0 c - 20)%Z 12%Z.
    rd4 28%Z. do 11 lstep. st4 28%Z. epilog.
Qed.
End Sz3.
Lemma sll2_spec : ltac:(let t := eval cbv delta [sll2_spec__stmt] in sll2_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'sll2_spec__body "v"). Qed.
End F_pp_B.

(* [comment removed for export] *)
Module F_pp_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.add (Z.modulo (Z.shiftl _ (4)%Z) (18446744073709551616)%Z) (64)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ _) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl _ (4)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.sub _ (16)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (get_le32 _ _) (65280)%Z) (40)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.shiftr (bv_wrap _ (get_le32 _ _)) (24)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (56)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (32)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac run_stop :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 88560%Z => fail
    | 88600%Z => fail
    | 88716%Z => fail
    | 88780%Z => fail
    | 88840%Z => fail
    | 88892%Z => fail
    | 88952%Z => fail
    | 89016%Z => fail
    | 89072%Z => fail
    | 91580%Z => fail
    | _ => idtac
    end
  | |- _ => idtac
  end.
Local Ltac run ::= repeat (run_stop; lstep); try rewrite (sx32_small (c_caplen _)) by lia.
Definition usb_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt ssegs (ppost c (c_len0 c) (swap_linux_usb_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d false))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x15978) (c_fc c) None m (seg_rom ssegs)).
Section Sz1.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usb_spec__stmt "v" @c).
#[using="Type"] Lemma usb_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usb_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pp_init WF I.
  unfold swap_linux_usb_header. cbn [h_caplen h_len]. unfold URB_ISOCHRONOUS.
  run. gsplit (c_caplen c) 8%Z.
  rd4 0%Z. rd4 4%Z. run. st8 0%Z.
  run. gsplit (c_caplen c) 14%Z.
  rd2 12%Z. run. st2 12%Z.
  gsplit (c_caplen c) 24%Z.
  rd4 16%Z. rd4 20%Z. run. st8 16%Z.
  run. gsplit (c_caplen c) 28%Z.
  rd4 24%Z. run. st4 24%Z.
  gsplit (c_caplen c) 32%Z.
  rd4 28%Z. run. st4 28%Z.
  gsplit (c_caplen c) 36%Z.
  rd4 32%Z. run. st4 32%Z.
  gsplit (c_caplen c) 40%Z.
  rd4 36%Z. run. st4 36%Z.
  (* [comment removed for export] *)
  destruct (Z.ltb_spec (c_caplen c) 44) as [C44|C44].
  { bdecide. destruct (get_u8 _ 9 =? 0); epilog. }
  bdecide.
  rd1 9%Z. lazymatch goal with |- context [get_u8 ?dd 9 =? 0] => esplit (get_u8 dd 9) 0%Z end.
  2:{ epilog. }
  rd4 40%Z. run. st4 40%Z.
  run. gsplit (c_caplen c) 48%Z.
  rd4 44%Z. run. st4 44%Z. epilog.
Qed.
End Sz1.
Lemma usb_spec : ltac:(let t := eval cbv delta [usb_spec__stmt] in usb_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usb_spec__body "v"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition leaf_post (c : ppctx) (ra t0 t1 t2 s0 s1 s2 t3 t4 t5 t6 : word) (m : mem) (res : Z) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_swrap 32 res)) a1 a2 a3 a4 a5 a6 a7 s2
                  (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
             (c_F c) (ret_pc ra) (c_fc c) None m (seg_rom ssegs).

Definition leaf_fin__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m nd pre,
  a2 = Z_to_bv 64 nd -> a3 = Z_to_bv 64 (bv_swrap 32 pre) -> (0 <= nd < 2^32)%Z -> (0 <= pre < 2^32)%Z ->
  evt ssegs (leaf_post c ra t0 t1 t2 s0 s1 s2 t3 t4 t5 t6 m (u_int_sum (iso_pseudo_header_len nd) pre))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16600) (c_fc c) None m (seg_rom ssegs)).
Section Sz2.
Variables c : ltac2:(SecDiet.SzSec.tyM 'leaf_fin__stmt "v" @c).
#[using="Type"] Lemma leaf_fin__body : ltac2:(SecDiet.SzSec.bodyP 'leaf_fin__stmt "v").
Proof.
  intros WF; intros until pre; intros -> -> ND PR.
  run. rewrite !swrap32_add_mod64_l, !swrap32_add_mod64_r. rewrite sat_idiom.
  replace ((Z.shiftl nd 4 mod 18446744073709551616 + 64) mod 2^32)%Z with (iso_pseudo_header_len nd)
    by (unfold iso_pseudo_header_len, u32; rewrite Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small pre) by lia.
  apply evt_done. unfold leaf_post. repeat eexists; try (cbv delta [mkR]; reflexivity).
Qed.
End Sz2.
Lemma leaf_fin : ltac:(let t := eval cbv delta [leaf_fin__stmt] in leaf_fin__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'leaf_fin__body "v"). Qed.

Lemma iso_data_len_loop_exit : forall f nd j bl pre d,
  (j <? nd) && (16 <=? bl) = false -> iso_data_len_loop f nd j bl pre d = pre.
Proof. intros [|f] nd j bl pre d H; cbn [iso_data_len_loop]; [reflexivity|]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Ltac rf_norm := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?Z.add_0_r.

(* [comment removed for export] *)
Definition leaf_loop__stmt : Prop := forall c, ppwf c -> forall (f : nat) (j pre : Z),
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d hlen,
  ppinv c m d hlen ->
  let nd := get_le32 d 60 in let bl := (c_caplen c - 64 - 16 * j)%Z in
  (Z.of_nat f >= nd - j)%Z -> (0 <= j < nd)%Z -> (16 <= bl)%Z -> (0 <= pre < 2^32)%Z -> (64 <= c_caplen c)%Z ->
  a0 = Z_to_bv 64 (j + 1) -> a1 = Z_to_bv 64 (c_DA c + (72 + 16 * j)) -> a2 = Z_to_bv 64 nd ->
  a3 = Z_to_bv 64 (bv_swrap 32 pre) -> a4 = Z_to_bv 64 15 -> a6 = Z_to_bv 64 (bv_swrap 32 (bl - 16)) ->
  evt ssegs (leaf_post c ra t0 t1 t2 s0 s1 s2 t3 t4 t5 t6 m (u_int_sum (iso_pseudo_header_len nd) (iso_data_len_loop f nd j bl pre d)))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x165bc) (c_fc c) None m (seg_rom ssegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'leaf_loop__stmt "vhk" @c).
Lemma leaf_loop__body : ltac2:(SecDiet.SzSec.bodyP 'leaf_loop__stmt "vhk").
Proof using.
  intros f WF.
 induction f as [|f IH]; intros j pre; intros until hlen; intros I nd bl FU J BL PR C64 -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof I as I'. pose proof WF as WF'. pp_init WF I.
  assert (ND : (0 <= nd < 2^32)%Z) by (subst nd; apply get_le32_range; exact ZR).
  assert (BLE : bl = (c_caplen c - 64 - 16 * j)%Z) by reflexivity. clearbody bl.
  cbn [iso_data_len_loop].
  replace (j <? nd) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (16 <=? bl) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  replace (64 + 16 * j + 8)%Z with (72 + 16 * j)%Z by lia. replace (64 + 16 * j + 4)%Z with (68 + 16 * j)%Z by lia.
  rd4 (72 + 16 * j)%Z. run.
  (* [comment removed for export] *)
  match goal with |- context [iso_data_len_loop f nd (j + 1) (bl - 16) ?p d] => set (pre' := p) end.
  assert (PR' : (0 <= pre' < 2^32)%Z).
  { pose proof (get_le32_range d (68 + 16 * j) ZR). subst pre'. destruct (negb _); [|lia]. destruct (pre <? _); [apply u_int_sum_range; lia | lia]. }
  (* [comment removed for export] *)
  assert (BOT : forall a5' a6' a7',
    a5' = Z_to_bv 64 (bv_swrap 32 (bl - 16)) ->
    evt ssegs (leaf_post c ra t0 t1 t2 s0 s1 s2 t3 t4 t5 t6 m (u_int_sum (iso_pseudo_header_len nd) (iso_data_len_loop f nd (j + 1) (bl - 16) pre' d)))
      (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 (Z_to_bv 64 (j + 1)) (Z_to_bv 64 (c_DA c + (72 + 16 * j))) (Z_to_bv 64 nd)
               (Z_to_bv 64 (bv_swrap 32 pre')) (Z_to_bv 64 15) a5' a6' a7' s2
               (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
          (c_F c) (Z_to_bv 64 0x165ec) (c_fc c) None m (seg_rom ssegs))).
  { intros a5' a6' a7' ->.
    destruct (Z.ltb_spec (j + 1) nd) as [JN|JN].
    - bdecide. run. rf_norm.
      destruct (Z.leb_spec 16 (bl - 16)) as [B2|B2].
      + (try lstep; btrue).
        replace (bl - 16)%Z with (c_caplen c - 64 - 16 * (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z pre'); fastfirst (first [ noevar_assumption |exact I' | reflexivity | (f_equal; lia) | (do 2 f_equal; lia) | lia]).
      + (try lstep; bfalse). rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        eapply leaf_fin; fastfirst (first [ noevar_assumption |exact WF' | reflexivity | lia]).
    - (try lstep; btrue). rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; left; apply Z.ltb_ge; lia).
      eapply leaf_fin; fastfirst (first [ noevar_assumption |exact WF' | reflexivity | lia]). }
  destruct (Z.eqb_spec (get_le32 d (72 + 16 * j)) 0) as [DZ|DZ]; cbn [negb] in pre'.
  - (try lstep; btrue). subst pre'. apply BOT. reflexivity.
  - (try lstep; bfalse). rd4 (68 + 16 * j)%Z. run. rf_norm. rewrite sat_idiom. rewrite !(Z.mod_small _ (2^32)) by lia.
    set (de := u_int_sum (get_le32 d (68 + 16 * j)) (get_le32 d (72 + 16 * j))) in *.
    assert (DE : (0 <= de < 2^32)%Z) by (subst de; apply u_int_sum_range; lia).
    destruct (Z.ltb_spec pre de) as [LT|LT].
    + (try lstep; btrue). lstep. subst pre'. apply BOT. reflexivity.
    + bdecide. do 2 lstep. subst pre'. apply BOT. reflexivity.
Qed.
End Sz4.
Lemma leaf_loop : ltac:(let t := eval cbv delta [leaf_loop__stmt] in leaf_loop__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'leaf_loop__body "vhk"). Qed.


Definition leaf_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d hlen,
  ppinv c m d hlen ->
  a0 = Z_to_bv 64 (c_caplen c) -> a1 = Z_to_bv 64 (c_DA c) -> (64 <= c_caplen c)%Z ->
  evt ssegs (leaf_post c ra t0 t1 t2 s0 s1 s2 t3 t4 t5 t6 m
               (incoming_isochronous_transfer_completed_len (mkHdr 0 0 (c_caplen c) hlen) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16590) (c_fc c) None m (seg_rom ssegs)).
Section Sz5.
Variables c : ltac2:(SecDiet.SzSec.tyM 'leaf_spec__stmt "v" @c).
Lemma leaf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'leaf_spec__stmt "v").
Proof using.
  intros WF; intros until hlen; intros I -> -> C64.
 pose proof I as I'. pose proof WF as WF'. pp_init WF I.
  unfold incoming_isochronous_transfer_completed_len. cbn [h_caplen].
  pose proof (get_le32_range d 60 ZR) as ND.
  rd4 60%Z. run.
  destruct (Z.eqb_spec (get_le32 d 60) 0) as [Z0|Z0].
  - bdecide. rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; left; apply Z.ltb_ge; lia).
    eapply (@leaf_fin c WF') with (nd := get_le32 d 60) (pre := 0%Z); fastfirst (first [ noevar_assumption |reflexivity | lia]).
  - bdecide. run.
    destruct (Z.leb_spec 16 (c_caplen c - 64)) as [B|B].
    + bdecide. run.
      replace (c_caplen c - 64)%Z with (c_caplen c - 64 - 16 * 0)%Z by lia.
      eapply (leaf_loop c WF' (Z.to_nat (get_le32 d 60 + 1)) 0%Z 0%Z);
        fastfirst (first [ noevar_assumption |exact I' | reflexivity | (f_equal; lia) | (do 2 f_equal; lia) | lia]).
    + (try lstep; btrue). rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
      eapply (@leaf_fin c WF') with (nd := get_le32 d 60) (pre := 0%Z); fastfirst (first [ noevar_assumption |reflexivity | lia]).
Qed.
End Sz5.
Lemma leaf_spec : ltac:(let t := eval cbv delta [leaf_spec__stmt] in leaf_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'leaf_spec__body "v"). Qed.

Lemma iso_data_len_loop_range : forall f nd j bl pre d,
  (0 <= pre < 2^32)%Z -> Forall (fun x => 0 <= x < 256)%Z d -> (0 <= iso_data_len_loop f nd j bl pre d < 2^32)%Z.
Proof.
  induction f as [|f IH]; intros nd j bl pre d PR ZR; cbn [iso_data_len_loop]; [lia|].
  destruct (_ && _); [|lia]. apply IH; [|exact ZR].
  destruct (negb _); [|lia].
  pose proof (u_int_sum_range (get_le32 d (64 + 16 * j + 4)) (get_le32 d (64 + 16 * j + 8))
                (get_le32_range d _ ZR) (get_le32_range d _ ZR)).
  destruct (pre <? _); lia.
Qed.
Lemma isolen_range : forall h d, (64 <= h_caplen h)%Z -> Forall (fun x => 0 <= x < 256)%Z d ->
  (0 <= incoming_isochronous_transfer_completed_len h d < 2^32)%Z.
Proof.
  intros h d HC ZR. unfold incoming_isochronous_transfer_completed_len. apply u_int_sum_range.
  - unfold iso_pseudo_header_len, u32. apply Z.mod_pos_bound. lia.
  - apply iso_data_len_loop_range; [lia | exact ZR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fixup_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  s0 = Z_to_bv 64 (c_caplen c) -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> (64 <= c_caplen c)%Z ->
  evt ssegs (ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) d)) d)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x162f4) (c_fc c) None m (seg_rom ssegs)).
Section Sz8.
Variables c : ltac2:(SecDiet.SzSec.tyM 'fixup_spec__stmt "v" @c).
#[using="Type"] Lemma fixup_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fixup_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> -> C64.
 pose proof I as I'. pose proof WF as WF'. pp_init WF I.
  unfold fixup_usb_mmapped_len. cbn [h_caplen h_len h_sec h_usec]. unfold USB_MAXDESC, URB_ISOCHRONOUS, URB_COMPLETE, URB_TRANSFER_IN.
  replace (c_caplen c <? 64) with false by (symmetry; apply Z.ltb_ge; lia). simpl_if.
  pose proof (get_le32_range d 60 ZR) as ND.
  rd4 60%Z. run. set (nd := get_le32 d 60) in *.
  destruct (Z.ltb_spec 128 nd) as [N128|N128]. { (try lstep; btrue). cbn [h_len]. epilog. }
  (try lstep; bfalse). rewrite (sx32_small nd) by lia.
  rd1 15%Z. run. destruct (Z.eqb_spec (get_u8 d 15) 0) as [DF|DF]; cycle 1. { (try lstep; btrue). cbn [andb h_len]. epilog. }
  bdecide. cbn [andb].
  rd1 9%Z. run. destruct (Z.eqb_spec (get_u8 d 9) 0) as [TT|TT]; cycle 1. { (try lstep; btrue). cbn [andb h_len]. epilog. }
  bdecide. cbn [andb].
  rd1 8%Z. run. destruct (Z.eqb_spec (get_u8 d 8) 67) as [ET|ET]; cycle 1. { (try lstep; btrue). cbn [andb h_len]. epilog. }
  bdecide. cbn [andb].
  rd1 10%Z. rewrite land_128 by lia. destruct (Z.ltb_spec (get_u8 d 10) 128) as [EP|EP]; simpl_if.
  { run. (try lstep; btrue). cbn [andb negb Z.eqb h_len]. epilog. }
  run. bdecide. cbn [andb negb Z.eqb Pos.eqb].
  pose proof (get_le32_range d 32 ZR) as UR.
  rd4 32%Z. run. rf_norm. rewrite ?Z.shiftl_mul_pow2 by lia.
  unfold iso_pseudo_header_len. unfold u32.
  match goal with |- context [c_len0 c =? ?x] => destruct (Z.eqb_spec (c_len0 c) x) as [LE|LE] end; cycle 1.
  { (try lstep; btrue). cbn [h_len]. epilog. }
  (try lstep; bfalse). simpl_if.
  run. destruct (Z.ltb_spec (c_caplen c) ((64 + nd * 16) mod 4294967296)) as [CH|CH]. { (try lstep; btrue). cbn [h_len]. epilog. }
  (try lstep; bfalse). do 4 lstep.
  eapply evt_cut; [eapply (leaf_spec c WF'); fastfirst (first [ noevar_assumption |exact I' | reflexivity | lia]) |].
  intros ms' PO; destruct PO as (? & ? & ? & ? & ? & ? & ? & ->).
  replace (ret_pc (Z_to_bv 64 0x16350)) with (Z_to_bv 64 0x16350) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  cbn [h_caplen].
  pose proof (isolen_range (mkHdr 0 0 (c_caplen c) (c_len0 c)) d ltac:(cbn [h_caplen]; lia) ZR) as LR.
  set (LEN := incoming_isochronous_transfer_completed_len _ d) in *.
  run. destruct (Z.leb_spec (c_caplen c) LEN) as [CL|CL]; cbn [h_len h_caplen h_sec h_usec].
  - (try lstep; btrue). run. (try lstep; btrue). run. bdecide.
    replace (LEN <? c_caplen c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [h_len].
    run.
    lazymatch goal with H : rw_cells _ ?m' (c_HA c) [?a; ?b; ?e; C4 ?v] |- _ =>
      pose proof (rw_cells_ext ssegs m' (c_HA c) [a; b; e; C4 v] [a; b; e; C4 (Z_to_bv 64 LEN)]
         ltac:(cbn [cells_bytes cbytes]; rewrite ?le4_swrap; reflexivity) eq_refl ltac:(cbn; tauto) H) as HDR';
      clear H end.
    pp_ret.
  - bdecide. run. bdecide.
    destruct (Z.ltb_spec (c_len0 c) (c_caplen c)) as [LL|LL]; cbn [h_len].
    + bdecide. run. (try lstep; btrue). run. pp_ret.
    + (try lstep; btrue). epilog.
Qed.
End Sz8.
Lemma fixup_spec : ltac:(let t := eval cbv delta [fixup_spec__stmt] in fixup_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'fixup_spec__body "v"). Qed.


(* [comment removed for export] *)
Definition fixup_spec'__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a0 = Z_to_bv 64 220 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt ssegs (ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) d)) d)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x162e0) (c_fc c) None m (seg_rom ssegs)).
Section Sz9.
Variables c : ltac2:(SecDiet.SzSec.tyM 'fixup_spec'__stmt "v" @c).
#[using="Type"] Lemma fixup_spec'__body : ltac2:(SecDiet.SzSec.bodyP 'fixup_spec'__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pose proof I as I'. pose proof WF as WF'. pp_init WF I.
  run. bdecide. run.
  destruct (Z.ltb_spec (c_caplen c) 64) as [C64|C64].
  { bdecide. unfold fixup_usb_mmapped_len. cbn [h_caplen h_len].
    replace (c_caplen c <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [h_len]. epilog. }
  bdecide. eapply fixup_spec; fastfirst (first [ noevar_assumption |exact WF' | exact I' | reflexivity | lia]).
Qed.
End Sz9.
Lemma fixup_spec' : ltac:(let t := eval cbv delta [fixup_spec'__stmt] in fixup_spec'__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'fixup_spec'__body "v"). Qed.
End F_pp_C.

(* [comment removed for export] *)
Module F_pp_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_B__S3.F_pp_C.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl (Z.land (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.add (Z.add (64)%Z (Z.mul (16)%Z _)) (20)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.shiftl (get_le32 _ _) (24)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (get_le32 _ _) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (56)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (get_le32 _ _) (65280)%Z) (40)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (32)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.shiftr (bv_wrap _ (get_le32 _ _)) (24)%Z)) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac run_stop :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 89532%Z => fail
    | 89572%Z => fail
    | 89688%Z => fail
    | 89752%Z => fail
    | 89812%Z => fail
    | 89864%Z => fail
    | 89924%Z => fail
    | 89992%Z => fail
    | 90044%Z => fail
    | 90104%Z => fail
    | 90152%Z => fail
    | 90192%Z => fail
    | 90240%Z => fail
    | 90292%Z => fail
    | 90340%Z => fail
    | 91460%Z => fail
    | 91516%Z => fail
    | _ => idtac
    end
  | |- _ => idtac
  end.
Local Ltac run ::= repeat (run_stop; lstep); try rewrite (sx32_small (c_caplen _)) by lia.
Lemma swap_usb_isodescs_S : forall f nd cap i desc off d,
  swap_usb_isodescs (S f) nd cap i desc off d =
  if i <? nd then
    if cap <? off + 4 then d
    else if cap <? off + 4 + 4 then swap_field 4 desc d
    else if cap <? off + 4 + 4 + 4 then swap_field 4 (desc + 4) (swap_field 4 desc d)
    else swap_usb_isodescs f nd cap (i + 1) (desc + 16) (off + 4 + 4 + 4 + 4)
           (swap_field 4 (desc + 8) (swap_field 4 (desc + 4) (swap_field 4 desc d)))
  else d.
Proof. reflexivity. Qed.
Lemma swap_usb_isodescs_exit : forall f nd cap i desc off d,
  ((i <? nd) = false \/ (cap <? off + 4) = true) -> swap_usb_isodescs f nd cap i desc off d = d.
Proof. intros [|f] nd cap i desc off d H; [reflexivity|]. rewrite swap_usb_isodescs_S. destruct H as [-> | ->]; [reflexivity|]. destruct (i <? nd); reflexivity. Qed.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
Ltac wordeq := fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) ]).

Definition isoloop_spec__stmt : Prop := forall c, ppwf c -> forall (f : nat) (i : Z),
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d (nd : Z),
  ppinv c m d (c_len0 c) ->
  (16 * Z.of_nat f >= c_caplen c - (64 + 16 * i) + 12)%Z ->
  (0 <= i < nd)%Z -> (64 + 16 * i + 4 <= c_caplen c)%Z -> (0 <= nd < 2^32)%Z ->
  a0 = Z_to_bv 64 220 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) -> s0 = Z_to_bv 64 (c_caplen c) ->
  a1 = Z_to_bv 64 (c_DA c + (64 + 16 * i)) -> a5 = Z_to_bv 64 (i + 1) -> t0 = Z_to_bv 64 (bv_swrap 32 (64 + 16 * i + 20)) ->
  a4 = sx32 (Z_to_bv 64 nd) -> a6 = Z_to_bv 64 65280 ->
  evt ssegs (let D := swap_usb_isodescs f nd (c_caplen c) i (64 + 16 * i) (64 + 16 * i) d in
             ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) D)) D)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16050) (c_fc c) None m (seg_rom ssegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'isoloop_spec__stmt "vhk" @c).
#[using="Type"] Lemma isoloop_spec__body : ltac2:(SecDiet.SzSec.bodyP 'isoloop_spec__stmt "vhk").
Proof.
  intros f WF.
 induction f as [|f IH]; intros i; intros until nd; intros I FU IR CI ND -> -> -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof WF as WF'. pp_init WF I. cbv zeta.
  rewrite swap_usb_isodescs_S.
  replace (i <? nd) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (c_caplen c <? 64 + 16 * i + 4) with false by (symmetry; apply Z.ltb_ge; lia). simpl_if.
  rd4 (64 + 16 * i)%Z. run. st4 (64 + 16 * i)%Z.
  run. rf_norm. destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 8)) as [C1|C1].
  { (try lstep; btrue). simpl_if. eapply fixup_spec'; first [exact WF' | close_inv | reflexivity]. }
  bdecide. simpl_if.
  rd4 (64 + 16 * i + 4)%Z. run. st4 (64 + 16 * i + 4)%Z.
  run. rf_norm. destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 12)) as [C2|C2].
  { (try lstep; btrue). simpl_if. eapply fixup_spec'; first [exact WF' | close_inv | reflexivity]. }
  bdecide. simpl_if.
  rd4 (64 + 16 * i + 8)%Z. run. st4 (64 + 16 * i + 8)%Z.
  run. destruct (Z.ltb_spec (i + 1) nd) as [IN|IN]; cycle 1.
  { (try lstep; btrue). rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia).
    eapply fixup_spec'; first [exact WF' | close_inv | reflexivity]. }
  bdecide. run. rf_norm.
  destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 20)) as [C5|C5].
  { bdecide. lstep. rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia).
    eapply fixup_spec'; first [exact WF' | close_inv | reflexivity]. }
  (try lstep; btrue).
  replace (64 + 16 * i + 16)%Z with (64 + 16 * (i + 1))%Z by lia.
  eapply (IH (i + 1)%Z); fastfirst (first [ noevar_assumption |close_inv | wordeq | lia]).
Qed.
End Sz3.
Lemma isoloop_spec : ltac:(let t := eval cbv delta [isoloop_spec__stmt] in isoloop_spec__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'isoloop_spec__body "vhk"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac gsplitF FX x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bdecide; cbn [orb andb negb]; rewrite FX by lia; epilog | bdecide; cbn [orb andb negb]].

(* [comment removed for export] *)
Ltac usbmm_tail FX c :=
  rd4 48%Z; run; st4 48%Z; gsplitF FX (c_caplen c) 56%Z;
  rd4 52%Z; run; st4 52%Z; gsplitF FX (c_caplen c) 60%Z;
  rd4 56%Z; run; st4 56%Z; gsplitF FX (c_caplen c) 64%Z;
  rd4 60%Z; run; name4 60%Z; st4 60%Z; fix_u8_all 9%Z;
  lazymatch goal with Hd : ?dn = swap_field 4 60 ?dold, EW : zslice 60 4 ?dold' = [?y0; ?y1; ?y2; ?y3] |- _ =>
    let ND := fresh "ND" in
    assert (ND : get_le32 dn 60 = (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z)
      by (rewrite Hd; unfold swap_field; rewrite EW; cbn [rev app]; apply get_le32_write_same; lia);
    rewrite ND;
    let EX := fresh "EX" in pose proof (get_le32_of_slice _ _ _ _ _ _ EW) as EX;
    match goal with |- context [Z_to_bv 64 ?E] =>
      lazymatch E with context [get_le32 dold 60] =>
        lazymatch E with Z.lor (Z.lor _ _) _ =>
          replace (Z_to_bv 64 E) with (sx32 (Z_to_bv 64 (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z))
            by (rewrite <- (Z_to_bv_bv_unsigned (sx32 _)); f_equal;
                replace (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z with (le_of_bytes [y3; y2; y1; y0]) by (cbn; lia);
                unfold get_le32; rewrite EW; repeat lanes_step; fastfirst (first [reflexivity | cbn [le_of_bytes]; lia]))
        end end end;
    let NDR := fresh "NDR" in
    assert (NDR : (0 <= y3 + 256 * y2 + 65536 * y1 + 16777216 * y0 < 2^32)%Z) by lia;
    set (nd := (y3 + 256 * y2 + 65536 * y1 + 16777216 * y0)%Z) in *
  end.

Definition usbmm_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a0 = Z_to_bv 64 220 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt ssegs (let D := swap_linux_usb_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d true in
             ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) D)) D)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x15d44) (c_fc c) None m (seg_rom ssegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usbmm_spec__stmt "v" @c).
#[using="Type"] Lemma usbmm_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usbmm_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pose proof WF as WF'. pp_init WF I. cbv zeta.
  (* [comment removed for export] *)
  assert (FX : forall D, (c_caplen c < 64)%Z ->
            h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) D) = c_len0 c).
  { intros D HD. unfold fixup_usb_mmapped_len. cbn [h_caplen]. replace (c_caplen c <? 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  unfold swap_linux_usb_header. cbn [h_caplen h_len]. unfold URB_ISOCHRONOUS.
  run. gsplitF FX (c_caplen c) 8%Z.
  rd4 0%Z. rd4 4%Z. run. st8 0%Z.
  run. gsplitF FX (c_caplen c) 14%Z.
  rd2 12%Z. run. st2 12%Z.
  gsplitF FX (c_caplen c) 24%Z.
  rd4 16%Z. rd4 20%Z. run. st8 16%Z.
  run. gsplitF FX (c_caplen c) 28%Z.
  rd4 24%Z. run. st4 24%Z.
  gsplitF FX (c_caplen c) 32%Z.
  rd4 28%Z. run. st4 28%Z.
  gsplitF FX (c_caplen c) 36%Z.
  rd4 32%Z. run. st4 32%Z.
  gsplitF FX (c_caplen c) 40%Z.
  rd4 36%Z. rd1 9%Z. run. st4 36%Z. fix_u8_all 9%Z.
  lazymatch goal with |- context [get_u8 ?dd 9 =? 0] => esplit (get_u8 dd 9) 0%Z end.
  - (* [comment removed for export] *)
    run. gsplitF FX (c_caplen c) 44%Z.
    rd4 40%Z. run. st4 40%Z. run. gsplitF FX (c_caplen c) 48%Z.
    rd4 44%Z. run. st4 44%Z. run. gsplitF FX (c_caplen c) 52%Z.
    usbmm_tail FX c.
    match goal with H : get_u8 _ 9 = 0%Z |- _ => rewrite (proj2 (Z.eqb_eq _ _) H) end. simpl_if.
    bdecide. run.
    destruct (Z.ltb_spec (c_caplen c) 68) as [C68|C68].
    { (try lstep; btrue). rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia).
      eapply fixup_spec; fastfirst (first [ noevar_assumption |exact WF' | close_inv | reflexivity | lia]). }
    bdecide. run.
    destruct (Z.eqb_spec nd 0) as [N0|N0].
    { (try lstep; btrue). rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia).
      eapply fixup_spec; fastfirst (first [ noevar_assumption |exact WF' | close_inv | reflexivity | lia]). }
    (try lstep; bfalse). run.
    eapply (isoloop_spec c WF' (Z.to_nat (c_caplen c / 16 + 2)) 0%Z); fastfirst (first [ noevar_assumption |close_inv | wordeq | fail]).
  - (* [comment removed for export] *)
    run. gsplitF FX (c_caplen c) 52%Z.
    usbmm_tail FX c.
    match goal with H : get_u8 _ 9 <> 0%Z |- _ => rewrite (proj2 (Z.eqb_neq _ _) H) end. simpl_if.
    (try lstep; btrue). eapply fixup_spec; fastfirst (first [ noevar_assumption |exact WF' | close_inv | reflexivity | lia]).
Qed.
End Sz4.
Lemma usbmm_spec : ltac:(let t := eval cbv delta [usbmm_spec__stmt] in usbmm_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usbmm_spec__body "v"). Qed.

End F_pp_D.

(* [comment removed for export] *)
Module F_pp_main.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_E. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_B__S3.F_pp_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_B__S3.F_pp_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_B__S3.F_pp_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_E.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac bd_F := try lstep; bfalse.
Local Ltac bd_T := try lstep; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Lemma h_caplen_fixup : forall h d, h_caplen (fixup_usb_mmapped_len h d) = h_caplen h.
Proof.
  intros h d. unfold fixup_usb_mmapped_len.
  destruct (_ <? 64); [reflexivity|]. destruct (_ <? _); [reflexivity|].
  destruct (_ && _); [|reflexivity]. destruct (_ <? _); [reflexivity|].
  destruct (_ <=? _); destruct (_ <? _); reflexivity.
Qed.

Lemma h_len_fixup_irrel : forall a b a' b' c l d,
  h_len (fixup_usb_mmapped_len (mkHdr a b c l) d) = h_len (fixup_usb_mmapped_len (mkHdr a' b' c l) d).
Proof.
  intros. unfold fixup_usb_mmapped_len. cbn [h_caplen h_len h_sec h_usec].
  destruct (_ <? 64); [reflexivity|]. destruct (_ <? _); [reflexivity|].
  destruct (_ && _); [|reflexivity]. destruct (_ <? _); [reflexivity|].
  unfold incoming_isochronous_transfer_completed_len. cbn [h_caplen].
  destruct (_ <=? _); cbn [h_len h_caplen h_sec h_usec]; destruct (_ <? _); reflexivity.
Qed.

(* [comment removed for export] *)
Ltac pp_model := unfold pcapint_post_process, swap_pseudo_headers, DLT_PFLOG, DLT_LINUX_SLL, DLT_LINUX_SLL2,
                        DLT_USB_LINUX, DLT_USB_LINUX_MMAPPED, DLT_NFLOG; cbn [Z.eqb Pos.eqb].
(* [comment removed for export] *)
Ltac pp_model_other := unfold pcapint_post_process, swap_pseudo_headers, DLT_PFLOG, DLT_LINUX_SLL, DLT_LINUX_SLL2,
                        DLT_USB_LINUX, DLT_USB_LINUX_MMAPPED, DLT_NFLOG;
  repeat match goal with |- context [?l =? ?k] => replace (l =? k) with false by (symmetry; apply Z.eqb_neq; lia) end;
  cbv iota.

(* [comment removed for export] *)
Ltac pp_init' := lazymatch goal with I : ppinv ?c ?m ?d ?h |- _ =>
  repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
                       | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
                       | H : wr_at _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
                       | H : length _ = _ |- _ => clear H end;
  open_inv I; unfold c in *;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo] in * end.

Ltac pp_ret' :=
  lazymatch goal with FR : rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _], ST : stk _ _ _ (bv_unsigned ?spv + -32) |- _ =>
    release_frame FR ST (bv_unsigned spv) end;
  apply evt_done; unfold ppost;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo FOOT];
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- zarr _ _ _ => split; [|split]; hyp_by_addr
  | |- _ => first [hyp_by_addr | assumption]
  end.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].

Theorem post_process_proof : post_process_stmt.
Proof.
  unfold post_process_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HA DA ws wu linktype swapped hdr d lo.
  intros ST LO HDR ZA MI -> -> -> -> LT CAP LEN HL SEP1 SEP2 SEP3 AL1 AL2 B1 B2 NZH NZD.
  destruct hdr as [hs hu caplen len0]. cbn [h_caplen h_len] in *. unfold PP_FRAME, PP_ENTRY in *.
  set (c := mkPP sp gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HA DA ws wu caplen len0 (length d) lo).
  pose proof (zarr_bound _ _ _ ZA) as DB. pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB.
  assert (WF : ppwf c) by (unfold ppwf; cbn; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct ZA as (ZB & ZW & ZR).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (HA + 20, HA + 24); (DA, DA + caplen)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  unfold pkthdr_cells in HDR. cbn [h_caplen h_len] in HDR.
  pose proof (zbytes_length d) as LZ.
  carve_frame 32%nat ST.
  do 5 lstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (I : ppinv c m1 d len0) by close_inv end.
  (* [comment removed for export] *)
  assert (K : forall hdr' d' ms', h_caplen hdr' = caplen ->
            pcapint_post_process linktype swapped (mkHdr hs hu caplen len0) d = (hdr', d') ->
            ppost c (h_len hdr') d' ms' ->
            post_process_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HA DA ws wu linktype swapped
              (mkHdr hs hu caplen len0) d lo m ms').
  { intros hdr' d' ms' HC PP P.
    destruct P as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & m' & -> & -> & -> & -> & P).
    destruct P as (MU' & WM' & MI' & ST' & HDR' & ZA').
    unfold post_process_post. rewrite PP. cbn [fst snd h_caplen]. unfold PP_FRAME, pkthdr_cells. rewrite HC.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. }
  (* [comment removed for export] *)
  Ltac branch HDR' D' HL BR K :=
    lazymatch goal with I : ppinv ?c _ _ _ |- _ => apply (evt_mono ssegs (ppost c HL D')) end;
    [ BR
    | let ms' := fresh "ms'" in let Pm := fresh "Pm" in
      intros ms' Pm; eapply (K HDR' D'); [ | | first [exact Pm | erewrite (h_len_fixup_irrel _ _ 0 0); exact Pm] ] ].
  destruct swapped; cbn [Z.b2z].
  - (* [comment removed for export] *)
    bd_F. run.
    destruct (Z.ltb_spec 219 linktype) as [GT|LE].
    + bd_T. run. destruct (Z.eqb_spec linktype 220) as [->|N220].
      * bd_T.
        set (D := swap_linux_usb_header (mkHdr 0 0 caplen len0) d true).
        branch (fixup_usb_mmapped_len (mkHdr hs hu caplen len0) D) D (h_len (fixup_usb_mmapped_len (mkHdr 0 0 caplen len0) D))
               ltac:(eapply (usbmm_spec c WF); first [exact I | reflexivity]) K.
        { apply h_caplen_fixup. } { pp_model. reflexivity. } 
      * bd_F. run. destruct (Z.eqb_spec linktype 239) as [->|N239].
        -- bd_T.
           branch (mkHdr hs hu caplen len0) (swap_nflog_header (mkHdr 0 0 caplen len0) d) len0
                  ltac:(eapply (nflog_spec c WF); first [exact I | reflexivity]) K.
           { reflexivity. } { pp_model. reflexivity. }
        -- bd_F. run. destruct (Z.eqb_spec linktype 276) as [->|N276].
           ++ bd_F.
              branch (mkHdr hs hu caplen len0) (swap_linux_sll2_socketcan_header (mkHdr 0 0 caplen len0) d) len0
                     ltac:(eapply (sll2_spec c WF); first [exact I | reflexivity]) K.
              { reflexivity. } { pp_model. reflexivity. }
           ++ bd_T.
              branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
              { reflexivity. } { pp_model_other. reflexivity. }
    + bd_F. run. destruct (Z.eqb_spec linktype 113) as [->|N113].
      * bd_T.
        branch (mkHdr hs hu caplen len0) (swap_linux_sll_socketcan_header (mkHdr 0 0 caplen len0) d) len0
               ltac:(eapply (sll_spec c WF); first [exact I | reflexivity]) K.
        { reflexivity. } { pp_model. reflexivity. }
      * bd_F. run. destruct (Z.eqb_spec linktype 117) as [->|N117].
        -- bd_T.
           branch (mkHdr hs hu caplen len0) (swap_pflog_header (mkHdr 0 0 caplen len0) d) len0
                  ltac:(eapply (pflog_spec c WF); first [exact I | reflexivity]) K.
           { reflexivity. } { pp_model. reflexivity. }
        -- bd_F. run. destruct (Z.eqb_spec linktype 189) as [->|N189].
           ++ bd_F.
              branch (mkHdr hs hu caplen len0) (swap_linux_usb_header (mkHdr 0 0 caplen len0) d false) len0
                     ltac:(eapply (usb_spec c WF); first [exact I | reflexivity]) K.
              { reflexivity. } { pp_model. reflexivity. }
           ++ bd_T.
              branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
              { reflexivity. } { pp_model_other. reflexivity. }
  - (* [comment removed for export] *)
    bd_T. destruct (Z.eqb_spec linktype 220) as [->|N220].
    + branch (fixup_usb_mmapped_len (mkHdr hs hu caplen len0) d) d (h_len (fixup_usb_mmapped_len (mkHdr 0 0 caplen len0) d))
             ltac:(eapply (fixup_spec' c WF); first [exact I | reflexivity]) K.
      { apply h_caplen_fixup. } { pp_model. reflexivity. }
    + run. bd_T.
      branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
      { reflexivity. } { pp_model_other. reflexivity. }
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_pp_B__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_pp_B__U3.F_pp_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_pp_B__U3.F_pp_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_pp_B__U3.F_pp_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_pp_B__U3.F_pp_E.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma h_caplen_fixup : forall h d, h_caplen (fixup_usb_mmapped_len h d) = h_caplen h.
Proof.
  intros h d. unfold fixup_usb_mmapped_len.
  destruct (_ <? 64); [reflexivity|]. destruct (_ <? _); [reflexivity|].
  destruct (_ && _); [|reflexivity]. destruct (_ <? _); [reflexivity|].
  destruct (_ <=? _); destruct (_ <? _); reflexivity.
Qed.

Lemma h_len_fixup_irrel : forall a b a' b' c l d,
  h_len (fixup_usb_mmapped_len (mkHdr a b c l) d) = h_len (fixup_usb_mmapped_len (mkHdr a' b' c l) d).
Proof.
  intros. unfold fixup_usb_mmapped_len. cbn [h_caplen h_len h_sec h_usec].
  destruct (_ <? 64); [reflexivity|]. destruct (_ <? _); [reflexivity|].
  destruct (_ && _); [|reflexivity]. destruct (_ <? _); [reflexivity|].
  unfold incoming_isochronous_transfer_completed_len. cbn [h_caplen].
  destruct (_ <=? _); cbn [h_len h_caplen h_sec h_usec]; destruct (_ <? _); reflexivity.
Qed.

(* [comment removed for export] *)
Ltac pp_model := unfold pcapint_post_process, swap_pseudo_headers, DLT_PFLOG, DLT_LINUX_SLL, DLT_LINUX_SLL2,
                        DLT_USB_LINUX, DLT_USB_LINUX_MMAPPED, DLT_NFLOG; cbn [Z.eqb Pos.eqb].
(* [comment removed for export] *)
Ltac pp_model_other := unfold pcapint_post_process, swap_pseudo_headers, DLT_PFLOG, DLT_LINUX_SLL, DLT_LINUX_SLL2,
                        DLT_USB_LINUX, DLT_USB_LINUX_MMAPPED, DLT_NFLOG;
  repeat match goal with |- context [?l =? ?k] => replace (l =? k) with false by (symmetry; apply Z.eqb_neq; lia) end;
  cbv iota.

(* [comment removed for export] *)
Ltac pp_init' := lazymatch goal with I : ppinv ?c ?m ?d ?h |- _ =>
  repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
                       | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
                       | H : wr_at _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
                       | H : length _ = _ |- _ => clear H end;
  open_inv I; unfold c in *;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo c_junk] in * end.

Ltac pp_ret' :=
  lazymatch goal with FR : rw_cells _ _ _ [CB 8 _; C8 _; C8 _; C8 _], ST : stk _ _ _ (bv_unsigned ?spv + -32) |- _ =>
    release_frame FR ST (bv_unsigned spv) end;
  apply evt_done; unfold ppost;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo c_junk FOOT];
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- zarr _ _ _ => split; [|split]; hyp_by_addr
  | |- _ => first [hyp_by_addr | assumption]
  end.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].

Theorem post_process_proof : post_process_stmt.
Proof.
  unfold post_process_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HA DA ws wu linktype swapped hdr d lo.
  intros ST LO HDR ZA MI -> -> -> -> LT CAP LEN HL SEP1 SEP2 SEP3 AL1 AL2 B1 B2 NZH NZD.
  destruct hdr as [hs hu caplen len0]. cbn [h_caplen h_len] in *. unfold PP_FRAME, PP_ENTRY in *.
  pose proof (zarr_bound _ _ _ ZA) as DB. pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct ZA as (ZB & ZW & ZR).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (HA + 20, HA + 24); (DA, DA + caplen)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold pkthdr_cells in HDR. cbn [h_caplen h_len] in HDR.
  pose proof (zbytes_length d) as LZ.
  carve_frame 32%nat ST.
  do 4 lstep.
  (* [comment removed for export] *)
  lazymatch goal with FR : rw_cells _ ?m1 _ [CB 8 ?jk; C8 _; C8 _; C8 _] |- _ =>
    set (c := mkPP sp gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HA DA ws wu caplen len0 (length d) lo jk);
    assert (WF : ppwf c) by (unfold ppwf; cbn; lia);
    assert (I : ppinv c m1 d len0) by close_inv end.
  (* [comment removed for export] *)
  assert (K : forall hdr' d' ms', h_caplen hdr' = caplen ->
            pcapint_post_process linktype swapped (mkHdr hs hu caplen len0) d = (hdr', d') ->
            ppost c (h_len hdr') d' ms' ->
            post_process_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HA DA ws wu linktype swapped
              (mkHdr hs hu caplen len0) d lo m ms').
  { intros hdr' d' ms' HC PP P.
    destruct P as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & m' & -> & -> & -> & -> & P).
    destruct P as (MU' & WM' & MI' & ST' & HDR' & ZA').
    unfold post_process_post. rewrite PP. cbn [fst snd h_caplen]. unfold PP_FRAME, pkthdr_cells. rewrite HC.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. }
  (* [comment removed for export] *)
  Ltac branch HDR' D' HL BR K :=
    lazymatch goal with I : ppinv ?c _ _ _ |- _ => apply (evt_mono usegs (ppost c HL D')) end;
    [ BR
    | let ms' := fresh "ms'" in let Pm := fresh "Pm" in
      intros ms' Pm; eapply (K HDR' D'); [ | | first [exact Pm | erewrite (h_len_fixup_irrel _ _ 0 0); exact Pm] ] ].
  destruct swapped; cbn [Z.b2z].
  - (* [comment removed for export] *)
    bd_F. run.
    destruct (Z.ltb_spec 219 linktype) as [GT|LE].
    + bd_T. run. destruct (Z.eqb_spec linktype 220) as [->|N220].
      * bd_T.
        set (D := swap_linux_usb_header (mkHdr 0 0 caplen len0) d true).
        branch (fixup_usb_mmapped_len (mkHdr hs hu caplen len0) D) D (h_len (fixup_usb_mmapped_len (mkHdr 0 0 caplen len0) D))
               ltac:(eapply (usbmm_spec c WF); first [exact I | reflexivity]) K.
        { apply h_caplen_fixup. } { pp_model. reflexivity. } 
      * bd_F. run. destruct (Z.eqb_spec linktype 239) as [->|N239].
        -- bd_T.
           branch (mkHdr hs hu caplen len0) (swap_nflog_header (mkHdr 0 0 caplen len0) d) len0
                  ltac:(eapply (nflog_spec c WF); first [exact I | reflexivity]) K.
           { reflexivity. } { pp_model. reflexivity. }
        -- bd_F. run. destruct (Z.eqb_spec linktype 276) as [->|N276].
           ++ bd_F.
              branch (mkHdr hs hu caplen len0) (swap_linux_sll2_socketcan_header (mkHdr 0 0 caplen len0) d) len0
                     ltac:(eapply (sll2_spec c WF); first [exact I | reflexivity]) K.
              { reflexivity. } { pp_model. reflexivity. }
           ++ bd_T.
              branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 4 lstep; repeat lstep; pp_ret') K.
              { reflexivity. } { pp_model_other. reflexivity. }
    + bd_F. run. destruct (Z.eqb_spec linktype 113) as [->|N113].
      * bd_T.
        branch (mkHdr hs hu caplen len0) (swap_linux_sll_socketcan_header (mkHdr 0 0 caplen len0) d) len0
               ltac:(eapply (sll_spec c WF); first [exact I | reflexivity]) K.
        { reflexivity. } { pp_model. reflexivity. }
      * bd_F. run. destruct (Z.eqb_spec linktype 117) as [->|N117].
        -- bd_T.
           branch (mkHdr hs hu caplen len0) (swap_pflog_header (mkHdr 0 0 caplen len0) d) len0
                  ltac:(eapply (pflog_spec c WF); first [exact I | reflexivity]) K.
           { reflexivity. } { pp_model. reflexivity. }
        -- bd_F. run. destruct (Z.eqb_spec linktype 189) as [->|N189].
           ++ bd_F.
              branch (mkHdr hs hu caplen len0) (swap_linux_usb_header (mkHdr 0 0 caplen len0) d false) len0
                     ltac:(eapply (usb_spec c WF); first [exact I | reflexivity]) K.
              { reflexivity. } { pp_model. reflexivity. }
           ++ bd_T.
              branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 4 lstep; repeat lstep; pp_ret') K.
              { reflexivity. } { pp_model_other. reflexivity. }
  - (* [comment removed for export] *)
    bd_T. run. destruct (Z.eqb_spec linktype 220) as [->|N220].
    + bd_F.
      branch (fixup_usb_mmapped_len (mkHdr hs hu caplen len0) d) d (h_len (fixup_usb_mmapped_len (mkHdr 0 0 caplen len0) d))
             ltac:(eapply (fixup_spec c WF); first [exact I | reflexivity]) K.
      { apply h_caplen_fixup. } { pp_model. reflexivity. }
    + bd_T.
      branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 4 lstep; repeat lstep; pp_ret') K.
      { reflexivity. } { pp_model_other. reflexivity. }
Qed.
End TwB.
End F_pp_main.
