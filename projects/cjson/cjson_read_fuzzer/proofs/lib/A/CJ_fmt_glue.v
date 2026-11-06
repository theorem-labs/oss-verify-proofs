(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_fmt_iface.
Module ICPT_fmt_iface2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface.

Section CeilWrap.
Context {ACEIL : Ceil}.

Definition asprintf_pre_b (m : word -> option byte) (sp : word) (D : Z) (dn : nat) (lo : Z) (canary : word) (fc : bv 32) : Prop :=
  fmt_cells m /\ MRT m /\ lowsh_at m /\ mem_inv asegs m /\ frm0 fc /\ assp_cells m canary
  /\ stk asegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo + AFMT_STACK <= bv_unsigned sp
  /\ bv_unsigned sp + 64 <= 2^47 - 1
  /\ (D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D)
  /\ (AIMG_HI <= D /\ app_range D (Z.of_nat dn))
  /\ shadow_ok m D (Z.of_nat dn).

Lemma asprintf_pre_b_of_high : forall m sp D dn lo canary fc, asprintf_pre m sp D dn lo canary fc -> asprintf_pre_b m sp D dn lo canary fc.
Proof.
  unfold asprintf_pre, asprintf_pre_b. intros m sp D dn lo canary fc (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  repeat (split; [assumption|]). split; [| exact H13]. split; [| right; exact H12].
  unfold highmem_range, KHIGHMEM_BEG, AIMG_HI in *. lia.
Qed.

Definition asprintf_d_stmt_b : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word)
         (i : Z) (o : list Z) (r : Z),
    rw_cells asegs m D [CB dn junkd] ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 A_FMT_d ->
    bv_unsigned a2 mod 2^32 = i mod 2^32 -> (-2^31 <= i < 2^31) ->
    fmt_d i = Some (o, r) -> (length o < dn)%nat -> (Z.of_nat dn < 2^31) ->
    asprintf_pre_b m sp D dn lo canary fc ->
    shadow_ok m A_FMT_d 3 ->
    evt asegs (asprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASPRINTF_T) fc None m (seg_rom asegs)).

Definition asprintf_g_stmt_b (prec : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word)
         (o : list Z) (r : Z),
    FMT_G_RET -> FMT_G_LEN25 ->
    rw_cells asegs m D [CB dn junkd] ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (if prec =? 15 then A_FMT_g15 else A_FMT_g17) -> (prec = 15 \/ prec = 17) ->
    fmt_g (bv_unsigned a2) prec = Some (o, r) ->
    fmt_fp_facts (f128_of_d (bv_unsigned a2)) 0 prec CHR_g ->
    (length o < dn)%nat -> (Z.of_nat dn < 2^31) ->
    asprintf_pre_b m sp D dn lo canary fc ->
    shadow_ok m (if prec =? 15 then A_FMT_g15 else A_FMT_g17) 7 ->
    evt asegs (asprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASPRINTF_T) fc None m (seg_rom asegs)).

Definition asprintf_u04x_stmt_b : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word) (c : Z),
    rw_cells asegs m D [CB dn junkd] ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 A_FMT_u04x ->
    bv_unsigned a2 mod 2^32 = c -> (0 <= c < 256) ->
    (6 <= dn)%nat -> (Z.of_nat dn < 2^31) ->
    asprintf_pre_b m sp D dn lo canary fc ->
    shadow_ok m A_FMT_u04x 6 ->
    evt asegs (asprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd 5 (117 :: hex4_lower c) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASPRINTF_T) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition asscanf_lg_stmt_b : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
    let usp := bv_unsigned sp in
    fmt_cells m -> MRT m -> lowsh_at m -> mem_inv asegs m -> frm0 fc -> assp_cells m canary -> rw_cells asegs m AERRNO [C4 ev] ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 A_FMT_lg -> a2 = Z_to_bv 64 PD ->
    bytes_at asegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
    (T + zlength txt) mod 8 = 0 -> zlength txt <= 256 ->
    rw_cells asegs m PD [C8 djunk] ->
    scan_sscanf_lg txt = Some (r, res) ->
    stk asegs m lo usp -> alloc_ceiling <= lo -> lo + AFMT_STACK <= usp -> usp + 8 <= 2^47 ->
    (T + zlength txt <= lo \/ usp <= T) -> (PD + 8 <= lo \/ usp <= PD) -> (PD + 8 <= T \/ T + zlength txt <= PD) ->
    4096 <= T -> 0x5ff000 <= T -> T + 2^41 <= 2^63 -> (AIMG_HI <= PD /\ sclr PD 8) -> PD + 8 <= 2^63 ->
    app_range T (zlength txt) -> shadow_ok m T (zlength pre + 1) -> app_range PD 8 -> shadow_ok m PD 8 ->
    evt asegs (asscanf_lg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASSCANF_T) fc None m (seg_rom asegs)).

End CeilWrap.
End ICPT_fmt_iface2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data RT_kit RT_rep RT_art CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl ICPT_pcdefs ICPT_fmt_iface.
Import ICPT_fmt_iface2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma artcells_fmt : forall m, ARTCELLS m -> icpt_cells m /\ fmt_cells m /\ icpt_cells2 m.
Proof.
  intros m H. unfold ARTCELLS in H. unfold A_MUSL_MEMCPY, A_MUSL_MEMSET, A_MUSL_STRLEN in *.
  decompose [and ex] H; clear H.
  unfold fmt_cells, icpt_cells2, icpt_cells, shbase_cells, ro_cells.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lowsh_buf_zero : forallb (fun k => Z.eqb (alowsh (SBZ_LO + Z.of_nat k)) 0) (seq 0 152) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lowsh_bufsh : forall m, lowsh_at m -> sh_zero m SBUF_LO SBUF_HI.
Proof.
  intros m L a Ha.
  assert (R : SBZ_LO <= SH a < SBZ_HI).
  { rewrite <- SBZ_LO_eq, <- SBZ_HI_eq. unfold SH, SBUF_LO, SBUF_HI in *. Z.div_mod_to_equations. lia. }
  unfold SBZ_LO, SBZ_HI in R.
  pose proof (L (SH a) ltac:(change (SH AIMG_LO) with 2147459072; change (SH AIMG_HI) with 2148236800; lia)) as C.
  assert (Z0 : alowsh (SH a) = 0).
  { pose proof lowsh_buf_zero as FB. rewrite forallb_forall in FB. unfold SBZ_LO in FB.
    specialize (FB (Z.to_nat (SH a - 2148236064)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in FB by lia.
    replace (2148236064 + (SH a - 2148236064)) with (SH a) in FB by lia. apply Z.eqb_eq. exact FB. }
  rewrite Z0 in C. apply (rw_cell1_shb m a 0 C). unfold SBUF_LO, SBUF_HI in Ha. lia.
Qed.

Lemma lowsh_MRT : forall m, icpt_cells m -> icpt_cells2 m -> sh_zero m alloc_ceiling (2^47) -> lowsh_at m -> MRT m.
Proof.
  intros m IC IC2 SSZ HL. unfold MRT. split; [exact IC|]. split; [split; [exact SSZ| apply lowsh_bufsh; exact HL]|].
  split; [exact (lowshadow_musl_lits m HL)| exact IC2].
Qed.

(* [comment removed for export] *)
Lemma lowsh_fmt_lits : forall m, lowsh_at m ->
  shadow_ok m A_FMT_d 3 /\ shadow_ok m A_FMT_g15 7 /\ shadow_ok m A_FMT_lg 4 /\ shadow_ok m A_FMT_g17 7
  /\ shadow_ok m 0x212a0 3 /\ shadow_ok m A_FMT_u04x 6.
Proof.
  intros m HL. unfold A_FMT_d, A_FMT_g15, A_FMT_lg, A_FMT_g17, A_FMT_u04x.
  repeat split; (apply lowsh_shadow_ok; [exact HL| unfold AIMG_LO; lia| lia| unfold AIMG_HI; lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma got_ssp_image :
  forallb (fun i => match wview asegs (fun _ => None) (wa (AGOT_SSP + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma got_ssp_rw : forall m, cells_at asegs m AGOT_SSP [C8 (wz ASSP)] -> rw_cells asegs m AGOT_SSP [C8 (wz ASSP)].
Proof.
  intros m H. split; [exact H|]. cbn [cells_size Cells.csize Nat.add]. unfold AGOT_SSP, wr_at. split; [lia|]. split; [lia|].
  intros i Hi. pose proof got_ssp_image as G. rewrite forallb_forall in G.
  specialize (G (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in G by lia. unfold AGOT_SSP in G.
  rewrite wview_empty. destruct (m (wa (666632 + i))); [discriminate|].
  destruct (wview asegs (fun _ => None) (wa (666632 + i))); [discriminate| discriminate G].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section FromART.
  Variable AI : art_iface.

  Lemma art_fmt_facts : forall sp0 SPB LB LF TRS BB m mo g,
    ART AI sp0 SPB LB LF TRS BB m mo g -> sh_zero m alloc_ceiling (2^47) ->
    fmt_cells m /\ MRT m /\ lowsh_at m /\ exists canary : word, assp_cells m canary.
  Proof.
    intros until g. intros HL SSZ.
    destruct (artcells_fmt m (art_rtcells AI _ _ _ _ _ _ _ _ _ HL)) as (IC & FC & IC2).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HL) as LOW. change (lowsh_at m) in LOW.
    split; [exact FC|]. split; [apply lowsh_MRT; assumption|]. split; [exact LOW|].
    destruct (art_ssp AI _ _ _ _ _ _ _ _ _ HL) as [G _]. destruct (ssp_cell m) as [canary C].
    exists canary. split; [apply got_ssp_rw; exact G| exact C].
  Qed.

  Lemma art_fmt_lits : forall sp0 SPB LB LF TRS BB m mo g,
    ART AI sp0 SPB LB LF TRS BB m mo g ->
    shadow_ok m A_FMT_d 3 /\ shadow_ok m A_FMT_g15 7 /\ shadow_ok m A_FMT_lg 4 /\ shadow_ok m A_FMT_g17 7
    /\ shadow_ok m 0x212a0 3 /\ shadow_ok m A_FMT_u04x 6.
  Proof. intros until g. intros HL. apply lowsh_fmt_lits. exact (art_lowshadow AI _ _ _ _ _ _ _ _ _ HL). Qed.

  (* [comment removed for export] *)
  Lemma art_icpt_cells' : forall sp0 SPB LB LF TRS BB m mo g, ART AI sp0 SPB LB LF TRS BB m mo g -> icpt_cells m.
  Proof. intros until g. intros HL. exact (proj1 (artcells_fmt m (art_rtcells AI _ _ _ _ _ _ _ _ _ HL))). Qed.
End FromART.


End CeilWrap.
