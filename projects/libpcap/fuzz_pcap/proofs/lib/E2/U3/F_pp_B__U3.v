(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_pp_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl (Z.land (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le16 _ _) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_u8 _ _) (8)%Z) => fail   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rf_norm' := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?swrap32_sub_mod64_l, ?Z.add_0_r.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac bd_F := try lstep; try untrap; bfalse.
Local Ltac bd_T := try lstep; try untrap; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
(* [comment removed for export] *)
Local Ltac run_stop :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 90180%Z => fail
    | 90200%Z => fail
    | 90532%Z => fail
    | 90604%Z => fail
    | 90676%Z => fail
    | 90744%Z => fail
    | 91208%Z => fail
    | 91240%Z => fail
    | 91300%Z => fail
    | 91396%Z => fail
    | 91428%Z => fail
    | 91488%Z => fail
    | _ => idtac
    end
  | |- _ => idtac
  end.
Local Ltac run ::= repeat (run_stop; lstep); try rewrite (sx32_small (c_caplen _)) by lia.
Definition pflog_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt usegs (ppost c (c_len0 c) (swap_pflog_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16138) (c_fc c) None m (seg_rom usegs)).
Section Sz1.
Variables c : ltac2:(SecDiet.SzSec.tyM 'pflog_spec__stmt "v" @c).
#[using="Type"] Lemma pflog_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pflog_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pp_init WF I.
  unfold swap_pflog_header. cbn [h_caplen h_len].
  run. bd_F. run. bd_F. run. gsplit_TF (c_caplen c) 48%Z. run. gsplit_TF (c_len0 c) 48%Z. run. bd_F. run. bd_F.
  rd1 0%Z. run. gsplit_TF constr:(get_u8 d 0) 48%Z.
  rd4 44%Z. run. st4 44%Z.
  gsplit_TF (c_caplen c) 52%Z. gsplit_TF (c_len0 c) 52%Z. run. gsplit_TF constr:(get_u8 d 0) 52%Z.
  rd4 48%Z. run. st4 48%Z.
  gsplit_TF (c_caplen c) 56%Z. gsplit_TF (c_len0 c) 56%Z. run. gsplit_TF constr:(get_u8 d 0) 56%Z.
  rd4 52%Z. run. st4 52%Z.
  gsplit_TF (c_caplen c) 60%Z. gsplit_TF (c_len0 c) 60%Z. run. gsplit_TF constr:(get_u8 d 0) 60%Z.
  rd4 56%Z. run. st4 56%Z.
  epilog.
Qed.
End Sz1.
Lemma pflog_spec : ltac:(let t := eval cbv delta [pflog_spec__stmt] in pflog_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'pflog_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sll_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt usegs (ppost c (c_len0 c) (swap_linux_sll_socketcan_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x1605c) (c_fc c) None m (seg_rom usegs)).
Section Sz2.
Variables c : ltac2:(SecDiet.SzSec.tyM 'sll_spec__stmt "v" @c).
#[using="Type"] Lemma sll_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sll_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pp_init WF I.
  unfold swap_linux_sll_socketcan_header, swap_socketcan_header. cbn [h_caplen h_len].
  unfold LINUX_SLL_P_CAN, LINUX_SLL_P_CANFD, LINUX_SLL_P_CANXL.
  run. bd_F. run. bd_F. run. gsplit_TF (c_caplen c) 16%Z. run. gsplit_TF (c_len0 c) 16%Z.
  run. bd_F. run. bd_F. run. bd_F.
  rd1 14%Z. rd1 15%Z. run.
  rewrite lor_be16 by lia. unfold get_be16. replace (14 + 1)%Z with 15%Z by reflexivity.
  rf_norm'. rewrite (swrap32_small (c_caplen c + -16)) by lia.
  set (p := (get_u8 d 14 * 256 + get_u8 d 15)%Z) in *. assert (RP : (0 <= p < 65536)%Z) by (subst p; lia).
  rewrite (ltu_minus12 p) by lia.
  destruct ((p =? 12) || (p =? 13))%Z eqn:E12; cbn [negb orb].
  - (* [comment removed for export] *)
    run. gsplit_TF (c_caplen c - 16)%Z 4%Z. gsplit_TF (c_len0 c - 16)%Z 4%Z. run. bd_F.
    rd4 16%Z. run. st4 16%Z. epilog.
  - run. esplit_FT p 14%Z. 2:{ epilog. }
    run. gsplit_TF (c_caplen c - 16)%Z 4%Z. gsplit_TF (c_len0 c - 16)%Z 4%Z. run. bd_F.
    rd4 16%Z. run. st4 16%Z.
    gsplit_TF (c_caplen c - 16)%Z 8%Z. gsplit_TF (c_len0 c - 16)%Z 8%Z.
    rd2 22%Z. run. st2 22%Z.
    gsplit_TF (c_caplen c - 16)%Z 12%Z. gsplit_TF (c_len0 c - 16)%Z 12%Z.
    rd4 24%Z. run. st4 24%Z. epilog.
Qed.
End Sz2.
Lemma sll_spec : ltac:(let t := eval cbv delta [sll_spec__stmt] in sll_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'sll_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sll2_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt usegs (ppost c (c_len0 c) (swap_linux_sll2_socketcan_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x15fb0) (c_fc c) None m (seg_rom usegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'sll2_spec__stmt "v" @c).
#[using="Type"] Lemma sll2_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sll2_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pp_init WF I.
  unfold swap_linux_sll2_socketcan_header, swap_socketcan_header. cbn [h_caplen h_len].
  unfold LINUX_SLL_P_CAN, LINUX_SLL_P_CANFD, LINUX_SLL_P_CANXL.
  run. bd_F. run. bd_F. run. gsplit_TF (c_caplen c) 20%Z. run. gsplit_TF (c_len0 c) 20%Z.
  run. bd_F. run. bd_F. run. bd_F.
  rd1 0%Z. rd1 1%Z. run.
  rewrite lor_be16 by lia. unfold get_be16. replace (0 + 1)%Z with 1%Z by reflexivity.
  rf_norm'. rewrite (swrap32_small (c_caplen c + -20)) by lia.
  set (p := (get_u8 d 0 * 256 + get_u8 d 1)%Z) in *. assert (RP : (0 <= p < 65536)%Z) by (subst p; lia).
  rewrite (ltu_minus12 p) by lia.
  destruct ((p =? 12) || (p =? 13))%Z eqn:E12; cbn [negb orb].
  - run. gsplit_TF (c_caplen c - 20)%Z 4%Z. gsplit_TF (c_len0 c - 20)%Z 4%Z.
    rd4 20%Z. run. st4 20%Z. epilog.
  - run. esplit_FT p 14%Z. 2:{ epilog. }
    run. gsplit_TF (c_caplen c - 20)%Z 4%Z. gsplit_TF (c_len0 c - 20)%Z 4%Z.
    rd4 20%Z. run. st4 20%Z.
    gsplit_TF (c_caplen c - 20)%Z 8%Z. gsplit_TF (c_len0 c - 20)%Z 8%Z.
    rd2 26%Z. run. st2 26%Z.
    gsplit_TF (c_caplen c - 20)%Z 12%Z. gsplit_TF (c_len0 c - 20)%Z 12%Z.
    rd4 28%Z. run. st4 28%Z. epilog.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl (Z.land (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv _ (get_le32 _ _)))) (24)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.shiftl (get_le32 _ _) (24)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (get_le32 _ _) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.add (Z.add (64)%Z (Z.mul (16)%Z _)) (20)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (32)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (get_le32 _ _) (65280)%Z) (40)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (get_le32 _ _) (56)%Z) => fail   (* [comment removed for export] *)
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
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rf_norm := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?swrap32_sub_mod64_l, ?Z.add_0_r.
Ltac wordeq := fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac bd_F := try lstep; try untrap; bfalse.
Local Ltac bd_T := try lstep; try untrap; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
(* [comment removed for export] *)
Local Ltac run_stop :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 91884%Z => fail
    | 91924%Z => fail
    | 92040%Z => fail
    | 92104%Z => fail
    | 92164%Z => fail
    | 92216%Z => fail
    | 92276%Z => fail
    | 92352%Z => fail
    | 92404%Z => fail
    | 92464%Z => fail
    | 92512%Z => fail
    | 92564%Z => fail
    | 92612%Z => fail
    | 92664%Z => fail
    | 92712%Z => fail
    | 92800%Z => fail
    | 92856%Z => fail
    | _ => idtac
    end
  | |- _ => idtac
  end.
Local Ltac run ::= repeat (run_stop; lstep); try rewrite (sx32_small (c_caplen _)) by lia.
Definition uhinv (c : ppctx) (m0 m : mem) (d : list Z) (hlen : Z) : Prop :=
  rw_cells usegs m (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
  /\ bytes_at usegs m (c_DA c) (zbytes d) /\ wr_at usegs m (c_DA c) (Z.of_nat (length d))
  /\ Forall (fun x => 0 <= x < 256)%Z d /\ length d = c_N c
  /\ mem_inv usegs m /\ munch [(c_DA c, c_DA c + c_caplen c)]%Z m0 m /\ wmono usegs m0 m.

Definition uhpost (c : ppctx) (m0 : mem) (ra sp s0 s1 s2 : word) (hlen : Z) (d : list Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
                  (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
             (c_F c) (ret_pc ra) (c_fc c) None m' (seg_rom usegs)
    /\ munch [(c_DA c, c_DA c + c_caplen c)]%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (c_HA c) [C8 (c_ws c); C8 (c_wu c); C4 (Z_to_bv 64 (c_caplen c)); C4 (Z_to_bv 64 hlen)]
    /\ zarr m' (c_DA c) d /\ length d = c_N c.

(* [comment removed for export] *)
Definition uhwf (c : ppctx) : Prop :=
  (0 <= c_caplen c <= Z.of_nat (c_N c))%Z /\ (Z.of_nat (c_N c) < 2^31)%Z
  /\ (c_HA c + 24 <= c_DA c \/ c_DA c + Z.of_nat (c_N c) <= c_HA c)%Z
  /\ (0 <= c_DA c /\ c_DA c + Z.of_nat (c_N c) <= 2^47)%Z /\ (0 <= c_HA c /\ c_HA c + 24 <= 2^47)%Z
  /\ (c_HA c mod 8 = 0)%Z /\ (c_DA c mod 4 = 0)%Z /\ (0 < c_HA c)%Z /\ (0 < c_DA c)%Z.
Lemma uhwf_of_ppwf : forall c, ppwf c -> uhwf c.
Proof. intros c WF. unfold ppwf in WF. unfold uhwf. tauto. Qed.

Ltac uh_init WF I :=
  destruct WF as (CAP & NB & SEP2 & DB & HB & ALH & ALD & NZH & NZD);
  destruct I as (HDR & ZB & ZW & ZR & LD & MI & MU & WM);
  lazymatch type of ZB with bytes_at _ _ _ (zbytes ?d) =>
    let LZ := fresh "LZ" in pose proof (zbytes_length d) as LZ; rewrite LD in LZ end.
Ltac close_uh := unfold uhinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
(* [comment removed for export] *)
Ltac uh_ret :=
  repeat lstep;
  apply evt_done; unfold uhpost;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo c_junk];
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- zarr _ _ _ => split; [|split]; hyp_by_addr
  | |- _ => first [hyp_by_addr | assumption]
  end.
Ltac close_uh0 := unfold uhinv; repeat match goal with |- _ /\ _ => split end;
  first [hyp_by_addr | assumption | reflexivity | apply munch_refl | apply wmono_refl].
Ltac gsplitU x k :=
  let C := fresh "Hc" in
  destruct (Z.ltb_spec x k) as [C|C]; [bdecide; cbn [orb andb negb]; uh_ret | bdecide; cbn [orb andb negb]].

Local Ltac gsplitU_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; uh_ret | bd_T; cbn [orb andb negb]].
Local Ltac gsplitU_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_F; cbn [orb andb negb]].
Local Ltac gsplitU_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; uh_ret | bd_T; cbn [orb andb negb]].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Definition uiso_spec__stmt : Prop := forall c, uhwf c -> forall (f : nat) (i : Z),
  forall (ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m0 m d (nd hlen : Z),
  uhinv c m0 m d hlen ->
  (16 * Z.of_nat f >= c_caplen c - (64 + 16 * i) + 12)%Z ->
  (0 <= i < nd)%Z -> (64 + 16 * i + 4 <= c_caplen c)%Z -> (0 <= nd < 2^32)%Z ->
  a0 = Z_to_bv 64 (c_caplen c) -> a1 = Z_to_bv 64 (c_DA c + (64 + 16 * i)) -> a3 = Z_to_bv 64 (i + 1) ->
  a7 = Z_to_bv 64 (bv_swrap 32 (64 + 16 * i + 20)) -> a2 = sx32 (Z_to_bv 64 nd) -> a4 = Z_to_bv 64 65280 -> a5 = Z_to_bv 64 (-17) ->
  evt usegs (uhpost c m0 ra sp s0 s1 s2 hlen (swap_usb_isodescs f nd (c_caplen c) i (64 + 16 * i) (64 + 16 * i) d))
    (MS (mkR ra sp (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16994) (c_fc c) None m (seg_rom usegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'uiso_spec__stmt "vhk" @c).
Lemma uiso_spec__body : ltac2:(SecDiet.SzSec.bodyP 'uiso_spec__stmt "vhk").
Proof using.
  intros f WF.
 induction f as [|f IH]; intros i; intros until hlen; intros I FU IR CI ND -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof WF as WF'. uh_init WF I.
  rewrite swap_usb_isodescs_S.
  replace (i <? nd) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (c_caplen c <? 64 + 16 * i + 4) with false by (symmetry; apply Z.ltb_ge; lia). simpl_if.
  rd4 (64 + 16 * i)%Z. run. st4 (64 + 16 * i)%Z.
  run. rf_norm. destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 8)) as [C1|C1].
  { (try lstep; try untrap; btrue). simpl_if. uh_ret. }
  bd_F. simpl_if.
  rd4 (64 + 16 * i + 4)%Z. run. st4 (64 + 16 * i + 4)%Z.
  run. rf_norm. destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 12)) as [C2|C2].
  { (try lstep; try untrap; btrue). simpl_if. uh_ret. }
  bd_F. simpl_if.
  rd4 (64 + 16 * i + 8)%Z. run. st4 (64 + 16 * i + 8)%Z.
  run. (try lstep; try untrap; bfalse). (* [comment removed for export] *)
  run. destruct (Z.ltb_spec (i + 1) nd) as [IN|IN]; cycle 1.
  { (try lstep; try untrap; btrue). rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia). uh_ret. }
  (try lstep; try untrap; bfalse). run. rf_norm.
  destruct (Z.ltb_spec (c_caplen c) (64 + 16 * i + 20)) as [C5|C5].
  { (try lstep; try untrap; bfalse). lstep. rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia). uh_ret. }
  (try lstep; try untrap; btrue).
  replace (64 + 16 * i + 16)%Z with (64 + 16 * (i + 1))%Z by lia.
  eapply (IH (i + 1)%Z); fastfirst (first [ noevar_assumption |close_uh | wordeq | lia]).
Qed.
End Sz4.
Lemma uiso_spec : ltac:(let t := eval cbv delta [uiso_spec__stmt] in uiso_spec__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'uiso_spec__body "vhk"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac uh_tail c :=
  run; gsplitU (c_caplen c) 52%Z;
  rd4 48%Z; run; st4 48%Z; gsplitU (c_caplen c) 56%Z;
  rd4 52%Z; run; st4 52%Z; gsplitU (c_caplen c) 60%Z;
  rd4 56%Z; run; st4 56%Z; gsplitU (c_caplen c) 64%Z;
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
Local Ltac uh_tail__c1 c :=
  run; gsplitU_TF (c_caplen c) 52%Z;
  rd4 48%Z; run; st4 48%Z; gsplitU_TF (c_caplen c) 56%Z;
  rd4 52%Z; run; st4 52%Z; gsplitU_TF (c_caplen c) 60%Z;
  rd4 56%Z; run; st4 56%Z; gsplitU_TF (c_caplen c) 64%Z;
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
Local Ltac uh_tail__c2 c :=
  run; gsplitU_TF (c_caplen c) 52%Z;
  rd4 48%Z; run; st4 48%Z; gsplitU_TF (c_caplen c) 56%Z;
  rd4 52%Z; run; st4 52%Z; gsplitU_TF (c_caplen c) 60%Z;
  rd4 56%Z; run; st4 56%Z; gsplitU_TF (c_caplen c) 64%Z;
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

(* [comment removed for export] *)
Ltac uh_loop c WF' :=
  match goal with H : get_u8 _ 9 = 0%Z |- _ => rewrite (proj2 (Z.eqb_eq _ _) H) end; simpl_if;
  bdecide; run; bdecide; run;
  lazymatch goal with nd := ?ndv : Z |- _ =>
  destruct (Z.eqb_spec nd 0) as [N0|N0];
  [ bdecide; rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia); uh_ret
  | bdecide; run;
    destruct (Z.ltb_spec (c_caplen c) 68) as [C68|C68];
    [ bdecide; rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia); uh_ret
    | bdecide; run;
      eapply (uiso_spec c WF' (Z.to_nat (c_caplen c / 16 + 2)) 0%Z); fastfirst (first [ noevar_assumption |close_uh | wordeq | lia]) ] ] end.
Local Ltac uh_loop__c1 c WF' :=
  match goal with H : get_u8 _ 9 = 0%Z |- _ => rewrite (proj2 (Z.eqb_eq _ _) H) end; simpl_if;
  bd_F; run; bd_F; run;
  lazymatch goal with nd := ?ndv : Z |- _ =>
  destruct (Z.eqb_spec nd 0) as [N0|N0];
  [ bd_T; rewrite swap_usb_isodescs_exit by (left; apply Z.ltb_ge; lia); uh_ret
  | bd_F; run;
    destruct (Z.ltb_spec (c_caplen c) 68) as [C68|C68];
    [ bd_T; rewrite swap_usb_isodescs_exit by (right; apply Z.ltb_lt; lia); uh_ret
    | bd_F; run;
      eapply (uiso_spec c WF' (Z.to_nat (c_caplen c / 16 + 2)) 0%Z); fastfirst (first [ noevar_assumption |close_uh | wordeq | lia]) ] ] end.

Definition usbhdr_spec__stmt : Prop := forall c, uhwf c -> forall (hl : bool)
  (ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m0 m d hlen,
  uhinv c m0 m d hlen ->
  a0 = Z_to_bv 64 (c_HA c) -> a1 = Z_to_bv 64 (c_DA c) -> a2 = Z_to_bv 64 (Z.b2z hl) ->
  evt usegs (uhpost c m0 ra sp s0 s1 s2 hlen (swap_linux_usb_header (mkHdr 0 0 (c_caplen c) hlen) d hl))
    (MS (mkR ra sp (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x1665c) (c_fc c) None m (seg_rom usegs)).
Section Sz5.
Variables c hl : ltac2:(SecDiet.SzSec.tyM 'usbhdr_spec__stmt "vhv" @c).
#[using="Type"] Lemma usbhdr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usbhdr_spec__stmt "vhv").
Proof.
  intros WF; intros until hlen; intros I -> -> ->.
 pose proof WF as WF'. uh_init WF I.
  unfold swap_linux_usb_header. cbn [h_caplen h_len]. unfold URB_ISOCHRONOUS.
  run. bd_F. run. bd_F.
  run. gsplitU_TF (c_caplen c) 8%Z.
  run. bd_F. run. bd_F.
  rd4 0%Z. rd4 4%Z. run. st8 0%Z.
  run. gsplitU_TF (c_caplen c) 14%Z.
  rd2 12%Z. run. st2 12%Z.
  gsplitU_TF (c_caplen c) 24%Z.
  rd4 16%Z. rd4 20%Z. run. st8 16%Z.
  run. gsplitU_TF (c_caplen c) 28%Z.
  rd4 24%Z. run. st4 24%Z. gsplitU_TF (c_caplen c) 32%Z.
  rd4 28%Z. run. st4 28%Z. gsplitU_TF (c_caplen c) 36%Z.
  rd4 32%Z. run. st4 32%Z. gsplitU_TF (c_caplen c) 40%Z.
  rd4 36%Z. rd1 9%Z. run. st4 36%Z. fix_u8_all 9%Z.
  lazymatch goal with |- context [get_u8 ?dd 9 =? 0] => esplit_TF (get_u8 dd 9) 0%Z end.
  - (* [comment removed for export] *)
    run. gsplitU_TF (c_caplen c) 44%Z.
    rd4 40%Z. run. st4 40%Z. run. gsplitU_TF (c_caplen c) 48%Z.
    rd4 44%Z. run. st4 44%Z. run.
    destruct hl; cbn [Z.b2z] in *.
    + (try lstep; try untrap; btrue). uh_tail__c1 c. uh_loop__c1 c WF'.
    + bd_F. uh_ret.
  - run. destruct hl; cbn [Z.b2z] in *.
    + bd_F. uh_tail__c2 c.
      match goal with H : get_u8 _ 9 <> 0%Z |- _ => rewrite (proj2 (Z.eqb_neq _ _) H) end. simpl_if.
      (try lstep; try untrap; btrue). uh_ret.
    + (try lstep; try untrap; btrue). uh_ret.
Qed.
End Sz5.
Lemma usbhdr_spec : ltac:(let t := eval cbv delta [usbhdr_spec__stmt] in usbhdr_spec__stmt in exact t).
Proof. intros c WF hl. ltac2:(SecDiet.SzSec.closeP 'usbhdr_spec__body "vhv"). Qed.
End F_pp_C.

(* [comment removed for export] *)
Module F_pp_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_pp_B__U3.F_pp_C.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rf_norm := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?swrap32_sub_mod64_l, ?Z.add_0_r.
Ltac wordeq := fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) ]).
Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].

(* [comment removed for export] *)
Lemma bytes_at_mrd : forall segs m a (bs : list byte) x, bytes_at segs m a bs ->
  (a <= x < a + Z.of_nat (length bs))%Z -> exists b, mrd segs m (wa x) = Some b.
Proof.
  intros segs m a bs x (H0 & H1 & H) Hx.
  specialize (H (Z.to_nat (x - a)) ltac:(lia)). rewrite Z2Nat.id in H by lia.
  replace (a + (x - a))%Z with x in H by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E; [exists b; exact H|].
  apply nth_error_None in E. lia.
Qed.
Lemma stk_transport_mrd : forall segs W m m' lo hi,
  stk segs m lo hi -> munch W m m' -> wmono segs m m' ->
  (forall x, (lo <= x < hi)%Z -> outside W x \/ exists b, mrd segs m' (wa x) = Some b) ->
  stk segs m' lo hi.
Proof.
  intros segs W m m' lo hi (H1 & H2 & H) Hm Hw Hcase. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hcase a Ha) as [Ho | (b' & Hb')].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exists b'. exact Hb'.
Qed.

(* [comment removed for export] *)
Tactic Notation "call_usbhdr" uconstr(SPEC) :=
  lazymatch goal with ST : stk usegs ?m ?lo ?hi |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply SPEC; [ close_uh0 | reflexivity | reflexivity | reflexivity ] | ];
    let ms' := fresh "ms'" in let PO := fresh "POST" in
    intros ms' PO; destruct_exs PO;
    let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in
    destruct PO as (E & MUc & WMc & PO); subst ms';
    lazymatch type of MUc with munch _ _ ?m' =>
      let ST' := fresh "ST" in
      assert (ST' : stk usegs m' lo hi);
      [ destruct PO as (_ & _ & (ZBc & _ & _) & LDc);
        eapply (stk_transport_mrd usegs _ _ _ _ _ ST MUc WMc);
        let x := fresh "x" in let Hx := fresh "Hx" in
        intros x Hx; cbn [outside];
        lazymatch type of ZBc with bytes_at _ _ ?A (zbytes ?D) =>
          destruct (Z_lt_le_dec x A); [left; lia|];
          destruct (Z_lt_le_dec x (A + Z.of_nat (length D))%Z);
            [right; eapply (bytes_at_mrd usegs _ _ _ _ ZBc); rewrite zbytes_length; lia | left; lia] end
      | clear ST; transport_after_call usegs m m' MUc WMc; clear MUc WMc;
        try match goal with H : mem_inv usegs m |- _ => clear H end;
        destruct PO as (?MI & ?HDRc & (?ZBc & ?ZWc & ?ZRc) & ?LDc) ] end
  end;
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition leaf_post (c : ppctx) (ra t2 s0 s1 t3 t4 t5 t6 : word) (m : mem) (res : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_swrap 32 res)) a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
                  (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
             (c_F c) (ret_pc ra) (c_fc c) None m (seg_rom usegs).

Definition leaf_fin__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m nd pre,
  a2 = Z_to_bv 64 nd -> a3 = Z_to_bv 64 (bv_swrap 32 pre) -> (0 <= nd < 2^32)%Z -> (0 <= pre < 2^32)%Z ->
  evt usegs (leaf_post c ra t2 s0 s1 t3 t4 t5 t6 m (u_int_sum (iso_pseudo_header_len nd) pre))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x1663c) (c_fc c) None m (seg_rom usegs)).
Section Sz3.
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
End Sz3.
Lemma leaf_fin : ltac:(let t := eval cbv delta [leaf_fin__stmt] in leaf_fin__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'leaf_fin__body "v"). Qed.

Lemma iso_data_len_loop_exit : forall f nd j bl pre d,
  (j <? nd) && (16 <=? bl) = false -> iso_data_len_loop f nd j bl pre d = pre.
Proof. intros [|f] nd j bl pre d H; cbn [iso_data_len_loop]; [reflexivity|]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Definition leaf_loop__stmt : Prop := forall c, ppwf c -> forall (f : nat) (j pre : Z),
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d hlen,
  ppinv c m d hlen ->
  let nd := get_le32 d 60 in let bl := (c_caplen c - 64 - 16 * j)%Z in
  (Z.of_nat f >= nd - j)%Z -> (0 <= j < nd)%Z -> (16 <= bl)%Z -> (0 <= pre < 2^32)%Z -> (64 <= c_caplen c)%Z -> (nd <= 128)%Z ->
  a4 = Z_to_bv 64 (j + 1) -> a1 = Z_to_bv 64 (c_DA c + (72 + 16 * j)) -> a2 = Z_to_bv 64 nd ->
  a3 = Z_to_bv 64 (bv_swrap 32 pre) -> a5 = Z_to_bv 64 15 -> t0 = Z_to_bv 64 (bv_swrap 32 (bl - 16)) ->
  a6 = Z_to_bv 64 (c_DA c + (64 + 16 * j)) -> a0 = Z_to_bv 64 (c_DA c + 64) ->
  evt usegs (leaf_post c ra t2 s0 s1 t3 t4 t5 t6 m (u_int_sum (iso_pseudo_header_len nd) (iso_data_len_loop f nd j bl pre d)))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x165ec) (c_fc c) None m (seg_rom usegs)).
Section Sz5.
Variables c : ltac2:(SecDiet.SzSec.tyM 'leaf_loop__stmt "vhk" @c).
Lemma leaf_loop__body : ltac2:(SecDiet.SzSec.bodyP 'leaf_loop__stmt "vhk").
Proof using.
  intros f WF.
 induction f as [|f IH]; intros j pre; intros until hlen; intros I nd bl FU J BL PR C64 N128 -> -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof I as I'. pose proof WF as WF'. pp_init WF I.
  assert (ND : (0 <= nd < 2^32)%Z) by (subst nd; apply get_le32_range; exact ZR).
  assert (BLE : bl = (c_caplen c - 64 - 16 * j)%Z) by reflexivity. clearbody bl.
  cbn [iso_data_len_loop].
  replace (j <? nd) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (16 <=? bl) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  replace (64 + 16 * j + 8)%Z with (72 + 16 * j)%Z by lia. replace (64 + 16 * j + 4)%Z with (68 + 16 * j)%Z by lia.
  run. bdecide. (* [comment removed for export] *)
  run. rd4 (72 + 16 * j)%Z. run.
  match goal with |- context [iso_data_len_loop f nd (j + 1) (bl - 16) ?p d] => set (pre' := p) end.
  assert (PR' : (0 <= pre' < 2^32)%Z).
  { pose proof (get_le32_range d (68 + 16 * j) ZR). subst pre'. destruct (negb _); [|lia]. destruct (pre <? _); [apply u_int_sum_range; lia | lia]. }
  assert (BOT : forall t0' t1',
    evt usegs (leaf_post c ra t2 s0 s1 t3 t4 t5 t6 m (u_int_sum (iso_pseudo_header_len nd) (iso_data_len_loop f nd (j + 1) (bl - 16) pre' d)))
      (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0' t1' t2 s0 s1 (Z_to_bv 64 (c_DA c + 64)) (Z_to_bv 64 (c_DA c + (72 + 16 * j))) (Z_to_bv 64 nd)
               (Z_to_bv 64 (bv_swrap 32 pre')) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 15) (Z_to_bv 64 (c_DA c + (64 + 16 * j)))
               (Z_to_bv 64 (bv_swrap 32 (bl - 16))) (c_s2 c)
               (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
          (c_F c) (Z_to_bv 64 0x16624) (c_fc c) None m (seg_rom usegs))).
  { intros t0' t1'.
    destruct (Z.ltb_spec (j + 1) nd) as [JN|JN].
    - bdecide. run. rf_norm.
      destruct (Z.leb_spec 16 (bl - 16)) as [B2|B2].
      + (try lstep; try untrap; btrue).
        replace (bl - 16)%Z with (c_caplen c - 64 - 16 * (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z pre'); fastfirst (first [ noevar_assumption |exact I' | wordeq | lia]).
      + (try lstep; try untrap; bfalse). rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        eapply leaf_fin; fastfirst (first [ noevar_assumption |exact WF' | reflexivity | lia]).
    - (try lstep; try untrap; btrue). rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; left; apply Z.ltb_ge; lia).
      eapply leaf_fin; fastfirst (first [ noevar_assumption |exact WF' | reflexivity | lia]). }
  destruct (Z.eqb_spec (get_le32 d (72 + 16 * j)) 0) as [DZ|DZ]; cbn [negb] in pre'.
  - (try lstep; try untrap; btrue). subst pre'. apply BOT.
  - (try lstep; try untrap; bfalse). run. bdecide. rd4 (68 + 16 * j)%Z. run. rf_norm. rewrite sat_idiom. rewrite !(Z.mod_small _ (2^32)) by lia.
    set (de := u_int_sum (get_le32 d (68 + 16 * j)) (get_le32 d (72 + 16 * j))) in *.
    assert (DE : (0 <= de < 2^32)%Z) by (subst de; apply u_int_sum_range; lia).
    destruct (Z.ltb_spec pre de) as [LT|LT].
    + (try lstep; try untrap; btrue). lstep. subst pre'. apply BOT.
    + (try lstep; try untrap; bfalse). do 2 lstep. subst pre'. apply BOT.
Qed.
End Sz5.
Lemma leaf_loop : ltac:(let t := eval cbv delta [leaf_loop__stmt] in leaf_loop__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'leaf_loop__body "vhk"). Qed.

Definition leaf_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d hlen,
  ppinv c m d hlen ->
  a0 = Z_to_bv 64 (c_HA c) -> a1 = Z_to_bv 64 (c_DA c) -> (64 <= c_caplen c)%Z -> (get_le32 d 60 <= 128)%Z ->
  evt usegs (leaf_post c ra t2 s0 s1 t3 t4 t5 t6 m
               (incoming_isochronous_transfer_completed_len (mkHdr 0 0 (c_caplen c) hlen) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x1659c) (c_fc c) None m (seg_rom usegs)).
Section Sz6.
Variables c : ltac2:(SecDiet.SzSec.tyM 'leaf_spec__stmt "v" @c).
Lemma leaf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'leaf_spec__stmt "v").
Proof using.
  intros WF; intros until hlen; intros I -> -> C64 N128.
 pose proof I as I'. pose proof WF as WF'. pp_init WF I.
  unfold incoming_isochronous_transfer_completed_len. cbn [h_caplen].
  pose proof (get_le32_range d 60 ZR) as ND.
  run. bdecide. run. bdecide. run. bdecide.
  rd4 60%Z. run. rewrite (sx32_small (get_le32 d 60)) by lia.
  destruct (Z.eqb_spec (get_le32 d 60) 0) as [Z0|Z0].
  - (try lstep; try untrap; btrue). rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; left; apply Z.ltb_ge; lia).
    eapply (@leaf_fin c WF') with (nd := get_le32 d 60) (pre := 0%Z); fastfirst (first [ noevar_assumption |reflexivity | lia]).
  - bdecide. run. rf_norm. rewrite ?(unsigned_lit (c_caplen c)) by lia.
    destruct (Z.leb_spec 16 (c_caplen c - 64)) as [B|B].
    + bdecide. do 7 lstep. rf_norm. rewrite ?(unsigned_lit (c_caplen c)) by lia.
      replace (c_caplen c - 64)%Z with (c_caplen c - 64 - 16 * 0)%Z by lia.
      eapply (leaf_loop c WF' (Z.to_nat (get_le32 d 60 + 1)) 0%Z 0%Z);
        fastfirst (first [ noevar_assumption |exact I' | reflexivity | (f_equal; lia) | (do 2 f_equal; lia) | lia]).
    + (try lstep; try untrap; btrue). rewrite iso_data_len_loop_exit by (apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
      eapply (@leaf_fin c WF') with (nd := get_le32 d 60) (pre := 0%Z); fastfirst (first [ noevar_assumption |reflexivity | lia]).
Qed.
End Sz6.
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
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt usegs (ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) d)) d)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16364) (c_fc c) None m (seg_rom usegs)).
Section Sz9.
Variables c : ltac2:(SecDiet.SzSec.tyM 'fixup_spec__stmt "v" @c).
#[using="Type"] Lemma fixup_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fixup_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pose proof I as I'. pose proof WF as WF'. pp_init WF I.
  unfold fixup_usb_mmapped_len. cbn [h_caplen h_len h_sec h_usec]. unfold USB_MAXDESC, URB_ISOCHRONOUS, URB_COMPLETE, URB_TRANSFER_IN.
  run. bdecide. run. bdecide.
  run. destruct (Z.ltb_spec (c_caplen c) 64) as [C64|C64]. { bdecide. cbn [h_len]. epilog. } bdecide.
  run. bdecide. run. bdecide.
  pose proof (get_le32_range d 60 ZR) as ND.
  rd4 60%Z. run.
  destruct (Z.ltb_spec 128 (get_le32 d 60)) as [N128|N128]. { (try lstep; try untrap; btrue). cbn [h_len]. epilog. }
  (try lstep; try untrap; bfalse). rewrite (sx32_small (get_le32 d 60)) by lia.
  rd1 15%Z. run. destruct (Z.eqb_spec (get_u8 d 15) 0) as [DF|DF]; cycle 1. { (try lstep; try untrap; btrue). cbn [andb h_len]. epilog. }
  bdecide. cbn [andb].
  rd1 9%Z. run. destruct (Z.eqb_spec (get_u8 d 9) 0) as [TT|TT]; cycle 1. { (try lstep; try untrap; btrue). cbn [andb h_len]. epilog. }
  bdecide. cbn [andb].
  rd1 8%Z. run. destruct (Z.eqb_spec (get_u8 d 8) 67) as [ET|ET]; cycle 1. { (try lstep; try untrap; btrue). cbn [andb h_len]. epilog. }
  bdecide. cbn [andb].
  rd1 10%Z. rewrite land_128 by lia. destruct (Z.ltb_spec (get_u8 d 10) 128) as [EP|EP]; simpl_if.
  { run. (try lstep; try untrap; btrue). cbn [andb negb Z.eqb h_len]. epilog. }
  run. bdecide. cbn [andb negb Z.eqb Pos.eqb].
  run. rf_norm. rewrite ?Z.shiftl_mul_pow2 by lia.
  unfold iso_pseudo_header_len. unfold u32. change (2 ^ 32)%Z with 4294967296%Z.
  destruct (Z.ltb_spec (c_caplen c) ((64 + get_le32 d 60 * 16) mod 4294967296)) as [CH|CH].
  { (try lstep; try untrap; btrue). match goal with |- context [c_len0 c =? ?x] => destruct (c_len0 c =? x) end; simpl_if; cbn [h_len]; epilog. }
  (try lstep; try untrap; bfalse).
  pose proof (get_le32_range d 32 ZR) as UR.
  rd4 32%Z. run. rf_norm.
  match goal with |- context [c_len0 c =? ?x] => destruct (Z.eqb_spec (c_len0 c) x) as [LE|LE] end; cycle 1.
  { (try lstep; try untrap; btrue). cbn [h_len]. epilog. }
  (try lstep; try untrap; bfalse). simpl_if.
  do 4 lstep.
  eapply evt_cut; [eapply (leaf_spec c WF'); fastfirst (first [ noevar_assumption |exact I' | reflexivity | lia]) |].
  intros ms' PO; destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  replace (ret_pc (Z_to_bv 64 0x163e4)) with (Z_to_bv 64 0x163e4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  cbn [h_caplen].
  pose proof (isolen_range (mkHdr 0 0 (c_caplen c) (c_len0 c)) d ltac:(cbn [h_caplen]; lia) ZR) as LR.
  set (LEN := incoming_isochronous_transfer_completed_len _ d) in *.
  run. destruct (Z.leb_spec (c_caplen c) LEN) as [CL|CL]; cbn [h_len h_caplen h_sec h_usec].
  - (try lstep; try untrap; btrue). run. (try lstep; try untrap; btrue).
    replace (LEN <? c_caplen c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [h_len].
    run.
    lazymatch goal with H : rw_cells _ ?m' (c_HA c) [?a; ?b; ?e; C4 ?v] |- _ =>
      pose proof (rw_cells_ext usegs m' (c_HA c) [a; b; e; C4 v] [a; b; e; C4 (Z_to_bv 64 LEN)]
         ltac:(cbn [cells_bytes cbytes]; rewrite ?le4_swrap; reflexivity) eq_refl ltac:(cbn; tauto) H) as HDR';
      clear H end.
    pp_ret.
  - bdecide. run.
    destruct (Z.ltb_spec (c_len0 c) (c_caplen c)) as [LL|LL]; cbn [h_len].
    + bdecide. run. pp_ret.
    + (try lstep; try untrap; btrue). epilog.
Qed.
End Sz9.
Lemma fixup_spec : ltac:(let t := eval cbv delta [fixup_spec__stmt] in fixup_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'fixup_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usb_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt usegs (ppost c (c_len0 c) (swap_linux_usb_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d false))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x15f78) (c_fc c) None m (seg_rom usegs)).
Section Sz10.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usb_spec__stmt "v" @c).
#[using="Type"] Lemma usb_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usb_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pose proof WF as WF'. pp_init WF I.
  do 8 lstep.
  lazymatch goal with FR : rw_cells _ _ _ [CB 8 _; C8 _; C8 _; C8 _], ST : stk _ _ _ (bv_unsigned ?spv + -32) |- _ =>
    release_frame FR ST (bv_unsigned spv) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call_usbhdr (usbhdr_spec c (uhwf_of_ppwf c WF') false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm d (c_len0 c)) end.
  apply evt_done. unfold ppost.
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo c_junk FOOT].
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end;
  first [hyp_by_addr | assumption | (split; [|split]; hyp_by_addr)].
Qed.
End Sz10.
Lemma usb_spec : ltac:(let t := eval cbv delta [usb_spec__stmt] in usb_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usb_spec__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usbmm_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt usegs (let D := swap_linux_usb_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d true in
             ppost c (h_len (fixup_usb_mmapped_len (mkHdr 0 0 (c_caplen c) (c_len0 c)) D)) D)
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16114) (c_fc c) None m (seg_rom usegs)).
Section Sz11.
Variables c : ltac2:(SecDiet.SzSec.tyM 'usbmm_spec__stmt "v" @c).
#[using="Type"] Lemma usbmm_spec__body : ltac2:(SecDiet.SzSec.bodyP 'usbmm_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> ->.
 pose proof WF as WF'. pp_init WF I. cbv zeta.
  do 6 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call_usbhdr (usbhdr_spec c (uhwf_of_ppwf c WF') true _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm d (c_len0 c)) end.
  do 3 lstep.
  eapply fixup_spec; first [exact WF' | close_inv | reflexivity].
Qed.
End Sz11.
Lemma usbmm_spec : ltac:(let t := eval cbv delta [usbmm_spec__stmt] in usbmm_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'usbmm_spec__body "v"). Qed.
End F_pp_D.

(* [comment removed for export] *)
Module F_pp_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
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
Local Ltac bd_F := try lstep; try untrap; bfalse.
Local Ltac bd_T := try lstep; try untrap; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Lemma swap_nflog_tlvs_S : forall f cap len p d,
  swap_nflog_tlvs (S f) cap len p d =
  (if cap <? 4 then d else
  let d2 := swap_field 2 p (swap_field 2 (p + 2) d) in
  let size := get_le16 d2 p in
  let size' := if size mod 4 =? 0 then size else size + (4 - size mod 4) in
  if size' <? 4 then d2 else if (cap <? size') || (len <? size') then d2
  else swap_nflog_tlvs f (cap - size') (len - size') (p + size') d2)%Z.
Proof. reflexivity. Qed.
Lemma swap_nflog_tlvs_exit : forall f cap len p d, (cap < 4)%Z -> swap_nflog_tlvs f cap len p d = d.
Proof. intros [|f] cap len p d H; [reflexivity|]. rewrite swap_nflog_tlvs_S. replace (cap <? 4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
Ltac wordeq := fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) ]).
Ltac rf_norm := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?swrap32_sub_mod64_l, ?Z.add_0_r.
(* [comment removed for export] *)
Ltac nf_exit := run; bdecide; epilog.
Local Ltac nf_exit__c1 := run; bd_T; epilog.
Local Ltac nf_exit__c2 := run; bd_T; epilog.
Local Ltac nf_exit__c3 := run; bd_T; epilog.
Local Ltac nf_exit__c4 := run; bd_T; epilog.

Definition nflog_loop__stmt : Prop := forall c, ppwf c -> forall (f : nat) (capc lenc p : Z),
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  (4 * Z.of_nat f >= capc + 4)%Z -> (4 <= capc)%Z -> (p + capc = c_caplen c)%Z -> (4 <= p)%Z -> (0 <= lenc < 2^32)%Z -> (p mod 4 = 0)%Z ->
  a0 = Z_to_bv 64 239 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  a1 = Z_to_bv 64 capc -> a6 = Z_to_bv 64 (c_DA c + p) -> a5 = Z_to_bv 64 (bv_swrap 32 lenc) ->
  a4 = Z_to_bv 64 4 -> a7 = Z_to_bv 64 65532 -> t0 = Z_to_bv 64 3 ->
  evt usegs (ppost c (c_len0 c) (swap_nflog_tlvs f capc lenc p d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x162ec) (c_fc c) None m (seg_rom usegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'nflog_loop__stmt "vhk" @c).
#[using="Type"] Lemma nflog_loop__body : ltac2:(SecDiet.SzSec.bodyP 'nflog_loop__stmt "vhk").
Proof.
  intros f WF.
 induction f as [|f IH]; intros capc lenc p; intros until d; intros I FU C4p PC P4 LR PM4 -> -> -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof WF as WF'. pp_init WF I.
  rewrite swap_nflog_tlvs_S. replace (capc <? 4) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta. simpl_if.
  set (d2 := swap_field 2 p (swap_field 2 (p + 2) d)).
  set (size := get_le16 d2 p).
  set (size' := if (size mod 4 =? 0)%Z then size else (size + (4 - size mod 4))%Z).
  run. bd_F.
  rd2 (p + 2)%Z. rd2 p. run.
  name2 p. name2 (p + 2)%Z.
  lazymatch goal with EWa : zslice p 2 d = [?y0; ?y1], EWb : zslice (p + 2) 2 d = [?y2; ?y3] |- _ =>
    sh_lanes p [y1; y0]; sh_lanes (p + 2)%Z [y3; y2];
    (* [comment removed for export] *)
    let E := fresh "E" in
    assert (E : buf_write_at (p + 2) [y3; y2] (buf_write_at p [y1; y0] d) = d2)
      by (subst d2; apply (tlv_pair p (p + 2) d y0 y1 y2 y3); [lia | lia | reflexivity | exact EWa | exact EWb]);
    assert (SZ : size = (y1 + 256 * y0)%Z)
      by (subst size; rewrite <- E; apply (tlv_pair_size p (p + 2) d y0 y1 y2 y3); lia);
    rewrite E in *; clear E; clearbody d2;
    (* [comment removed for export] *)
    rewrite (get_le16_of_slice _ _ _ _ EWa); rewrite swap16_val by lia;
    (* [comment removed for export] *)
    replace size' with (if ((y1 + 256 * y0) mod 4 =? 0)%Z then (y1 + 256 * y0)%Z else (y1 + 256 * y0 + (4 - (y1 + 256 * y0) mod 4))%Z)
      by (subst size' size; rewrite SZ; reflexivity);
    clear size' size SZ;
    set (sw := (y1 + 256 * y0)%Z) in *;
    assert (SW : (0 <= sw < 65536)%Z) by lia;
    rewrite land_3 by lia;
    replace ((sw + 65536 * y1) mod 4)%Z with (sw mod 4)%Z by zlia
  end.
  (* [comment removed for export] *)
  assert (CONT : forall (t1' t2' t3' : word) (sz : Z), (0 <= sz < 2^32)%Z -> (sz mod 4 = 0)%Z -> t1' = Z_to_bv 64 sz ->
    evt usegs (ppost c (c_len0 c)
                (if sz <? 4 then d2 else if (capc <? sz) || (lenc <? sz) then d2
                 else swap_nflog_tlvs f (capc - sz) (lenc - sz) (p + sz) d2))
      (MS (mkR ra (SPM c) (c_gp c) (c_tp c) (Z_to_bv 64 3) t1' t2' s0 s1 (Z_to_bv 64 239) (Z_to_bv 64 capc)
               (Z_to_bv 64 (c_HA c)) (Z_to_bv 64 (c_DA c)) (Z_to_bv 64 4) (Z_to_bv 64 (bv_swrap 32 lenc))
               (Z_to_bv 64 (c_DA c + p)) (Z_to_bv 64 65532) (c_s2 c)
               (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3' t4 t5 t6)
          (c_F c) (Z_to_bv 64 0x16338) (c_fc c) None m (seg_rom usegs))).
  { intros t1' t2' t3' sz SZR SZ4 ->.
    run. destruct (Z.ltb_spec sz 4) as [S4|S4]. { bd_T. nf_exit__c1. } bd_F.
    run. destruct (Z.ltb_spec capc sz) as [S5|S5]. { bd_T. cbn [orb]. nf_exit__c2. } bd_F. cbn [orb].
    run. destruct (Z.ltb_spec lenc sz) as [S6|S6]. { bd_T. nf_exit__c3. } bd_F.
    run. bd_F.
    run. rf_norm.
    destruct (Z.ltb_spec 3 (capc - sz)) as [S7|S7]; cycle 1.
    { bd_F. rewrite swap_nflog_tlvs_exit by lia. nf_exit__c4. }
    bd_T. eapply (IH (capc - sz)%Z (lenc - sz)%Z (p + sz)%Z); fastfirst (first [ noevar_assumption |close_inv | wordeq | lia | zlia]). }
  destruct (Z.eqb_spec (sw mod 4) 0) as [M0|M0]; simpl_if.
  - bd_T. do 2 lstep.
    match goal with |- context [((sw + 65536 * ?y) mod 65536)%Z] =>
      replace ((sw + 65536 * y) mod 65536)%Z with sw by zlia end.
    eapply (CONT _ _ _ sw); [lia | zlia | reflexivity].
  - bd_F. lstep. rewrite land_65532 by lia.
    match goal with |- context [((sw + 65536 * ?y) mod 65536 - (sw + 65536 * ?y) mod 4)%Z] =>
      replace ((sw + 65536 * y) mod 65536 - (sw + 65536 * y) mod 4)%Z with (sw - sw mod 4)%Z by zlia end.
    do 2 lstep.
    eapply (CONT _ _ _ (sw + (4 - sw mod 4))%Z); [zlia | zlia | wordeq].
Qed.
End Sz3.
Lemma nflog_loop : ltac:(let t := eval cbv delta [nflog_loop__stmt] in nflog_loop__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'nflog_loop__body "vhk"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nflog_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a0 = Z_to_bv 64 239 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt usegs (ppost c (c_len0 c) (swap_nflog_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (c_s2 c)
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16290) (c_fc c) None m (seg_rom usegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'nflog_spec__stmt "v" @c).
#[using="Type"] Lemma nflog_spec__body : ltac2:(SecDiet.SzSec.bodyP 'nflog_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pose proof WF as WF'. pp_init WF I.
  unfold swap_nflog_header. cbn [h_caplen h_len].
  run. bd_F. run. bd_F.
  run. gsplit_TF (c_caplen c) 4%Z.
  run. gsplit_TF (c_len0 c) 4%Z.
  run. bd_F. run. bd_F.
  rd1 1%Z. run.
  destruct (Z.eqb_spec (get_u8 d 1) 0) as [V0|V0]; cycle 1.
  { bd_T. cbn [negb]. epilog. }
  bd_F. cbn [negb]. run. bd_F. run. rf_norm. rewrite (swrap32_small (c_caplen c + -4)) by lia.
  destruct (Z.ltb_spec (c_caplen c - 4) 4) as [C8'|C8'].
  { bd_T. rewrite swap_nflog_tlvs_exit by lia. epilog. }
  bd_F. do 5 lstep. rf_norm.
  eapply (nflog_loop c WF' (Z.to_nat (c_caplen c / 4 + 1)) (c_caplen c - 4)%Z (c_len0 c - 4)%Z 4%Z);
    fastfirst (first [ noevar_assumption |close_inv | wordeq | lia | zlia]).
Qed.
End Sz4.
Lemma nflog_spec : ltac:(let t := eval cbv delta [nflog_spec__stmt] in nflog_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'nflog_spec__body "v"). Qed.
End F_pp_E.
