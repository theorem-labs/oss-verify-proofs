(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 978 of its 993 lines of code are new or changed and 233 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB_case56F.v is the re-based copy of lib/B/Prog/reac_box_model_block_case56F.v at 20372bbcc3a
   (source sha256 eab41c74b27c6c86c3a14d1fce53bd2e6e41ba040c888dddab44995708f6a0a8) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: nothing. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  C_reac_box_model_blockRB C_reac_box_model_blockRBF C_reac_box_model_blockRB_case56.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on reac_box_model_block_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c_on asan_stack_malloc_cF_on asan_memset_c_on asan_memset_cF_on
  asan_memcpy_c_on asan_memcpy_cF_on sh_word_on C_reac_box_model_blockOnHB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import name_field_c_on.
Import ListNotations.
Open Scope Z_scope.

(* Local copy of C_reac_box_model_blockRB.v:228's store hook: that file made it Local (a Theorem Labs lane; generator owner a Theorem Labs lane stopped, a Theorem Labs lane audits). *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* The footprint twin of C_reac_box_model_blockRB_case56.v (image B, asan-ubsan; route 2): the cases b = 5 and b = 6 of
   reac_box_model_block as ExecF.evtF runs under a footprint RNG, by the scripts of the plain file over StepF's
   step.  Every lemma of the plain file that does not mention evt is reused from there (the Local Abbreviations
   below apply it to this Section's variables); the nine that mention evt are restated here with the suffix F and
   the same premises.  The new goals are the rng premises of the footprint forms of name_field, __asan_memcpy and
   dt1_head, closed from the facts `mbF_open HRNG` unpacks (the window, [RT_LO, RT_HI) in the image, the row, the
   name and the output block, each with its shadow cover), and the access side goals StepF's step closes from the
   same facts.  Two additions to the plain scripts serve them: each proof specializes the guarded row and output
   block facts (RROW, ROUT) at p <> 0 and o <> 0, and c56_call_nfF's name witness nb' also records
   rname row <> 0 -> nb' = nb, the name the rng facts of RNM speak of. *)

(* The byte stores of these cases write a register value, so the cell of a 1-byte store is read off le1 (as in the
   plain file). *)
Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?bb] => constr:(C1 bb)
  | le1 (zxb ?bb) => constr:(C1 bb)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(* The two hooks of C_reac_box_model_blockRBF.v (Local there, so copied here verbatim). *)
Ltac mbF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac mbF_store_opt :=
  try mbF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= mbF_store_opt.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mbF_acc_hint.

Section c56F_S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint).
  Hypothesis HSM : asan_stack_malloc_0_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  Hypothesis HMS : asan_memset_contract_F_on.
  Hypothesis HMC : asan_memcpy_contract_F_on.
  Hypothesis HBD : build_dt1_single_contract_F_on.
  Hypothesis HDH : dt1_head_contract_F_on.
  Hypothesis HNF : name_field_contract_F_on.

  (* The release continuation at 0x86e14 (rel_stmt of mbb-interface-pin.md, verbatim). *)
  Hypothesis Hrel : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
       (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
  FK FS A fr f spc j n w56 ->
  ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
  BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
     (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
  (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
  evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
    (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
            (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).
  Hypothesis HRNG : mbF_rng RNG m sp tp p b o FS row nb.

  (* The arithmetic hygiene of the plain file (c56_sc, c56_ar, c56_lia, c56_hide, c56_show), restated for this
     Section: c56_sc also drops HRNG and the guarded facts of `mbF_open HRNG` (RROW, ROUT, RJ4, RJ3, RNM: an
     implication whose conclusion holds a shcov; RTLS: the one that names fp_tls), and it keeps Hoff, which
     mbF_acc_hint needs to put a shadow address X / 8 + off in the form X / 8 + ASAN_K of the covers. *)
  Ltac c56_sc :=
    try clear Hrel; try clear HNF; try clear HDH; try clear HBD; try clear HMC; try clear HMS;
    try clear NDJ; try clear AJ2; try clear AJ1; try clear AO; try clear ANB; try clear AP;
    try clear HO; try clear HN; try clear HP; try clear TLS0; try clear FP0; try clear AW0;
    try clear SR0; try clear AC0; try clear MI0; try clear ST0; try clear HS16; try clear HA;
    try clear HSM; try clear HRNG;
    repeat match goal with
    | H : _ -> ?B |- _ => lazymatch B with context [shcov _ _ _] => clear H end
    | H : forall _ : word, _ |- _ => lazymatch type of H with context [fp_tls _ _ _ _ _ _ _] => clear H end
    end.
  Ltac c56_ar :=
    c56_sc;
    repeat match goal with
    | H : forall _ : word -> option byte, _ |- _ => clear H
    | H : forall _ : word, _ |- _ => clear H
    | H : forall _ : Z, _ |- _ => clear H
    | H : forall _ : nat, _ |- _ => clear H
    | H : forall _ : list byte, _ |- _ => clear H
    | H : BI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
    | H : rw_cells _ _ _ _ |- _ => clear H
    | H : ro_cells _ _ _ _ |- _ => clear H
    | H : bytes_at _ _ _ _ |- _ => clear H
    | H : stk _ _ _ _ |- _ => clear H
    | H : munch _ _ _ |- _ => clear H
    | H : wmono _ _ _ |- _ => clear H
    | H : rd_mono _ _ |- _ => clear H
    | H : addressable _ _ _ |- _ => clear H
    | H : asan_cells _ |- _ => clear H
    | H : shadow_rw _ |- _ => clear H
    | H : mem_inv _ _ |- _ => clear H
    | H : fp_dj _ _ |- _ => clear H
    | H : name_ok _ |- _ => clear H
    | H : ov_read_bytes _ _ _ _ = _ |- _ => clear H
    | H : store_ok _ _ _ _ = _ |- _ => clear H
    end.
  Ltac c56_lia := c56_ar; lia.
  Ltac c56_hide H := let T := type of H in change (c56_box T) in H.
  Ltac c56_show H := unfold c56_box in H.

  (* The lemmas of C_reac_box_model_blockRB_case56.v that do not mention evt, at this Section's variables (the plain
     names, so the scripts below are the plain ones; c56_W is used with its explicit arguments sp o FS). *)
  Local Abbreviation c56_Wu := (C_reac_box_model_blockRB_case56.c56_Wu sp p o FS).
  Local Abbreviation c56_geoA := (C_reac_box_model_blockRB_case56.c56_geoA sp tp m p b o FS off A
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro).
  Local Abbreviation c56_geoP := (C_reac_box_model_blockRB_case56.c56_geoP sp m p o row HP AP).
  Local Abbreviation c56_geoO := (C_reac_box_model_blockRB_case56.c56_geoO sp tp m p b o FS ob FP0 Rp Rb Ro HO AO).
  Local Abbreviation c56_frpos := (C_reac_box_model_blockRB_case56.c56_frpos sp tp m p b o FS off A
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro).
  Local Abbreviation c56_o_fr_iv := (C_reac_box_model_blockRB_case56.c56_o_fr_iv sp tp m p b o FS off A ob
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HO AO).
  Local Abbreviation c56_rt := (C_reac_box_model_blockRB_case56.c56_rt ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m
    p b o FS A row nb ob HA HS16 ST0 AC0 SR0 HHM HAE FP0 Rp Rb Ro HP HO AO).
  Local Abbreviation c56_rowb := (C_reac_box_model_blockRB_case56.c56_rowb sp tp m p b o FS off A row
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP AP).
  Local Abbreviation c56_addr_buf := (C_reac_box_model_blockRB_case56.c56_addr_buf sp tp m p b o FS off A row nb
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP AO).
  Local Abbreviation c56_addr_p := (C_reac_box_model_blockRB_case56.c56_addr_p sp tp m p b o FS off A row
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HP AP AO).
  Local Abbreviation c56_addr_o := (C_reac_box_model_blockRB_case56.c56_addr_o sp tp m p b o FS off A ob
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HO AO).
  Local Abbreviation c56_dj4 := (C_reac_box_model_blockRB_case56.c56_dj4 p b o FS Rp Rb Ro).
  Local Abbreviation c56_out_nm := (C_reac_box_model_blockRB_case56.c56_out_nm sp tp m p b o FS off A row nb
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro HN ANB NDJ).
  Local Abbreviation c56_addr_keep := (C_reac_box_model_blockRB_case56.c56_addr_keep sp tp m p b o FS off A
    Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 Rp Rb Ro AO).
  Local Abbreviation c56_fr_apart := (C_reac_box_model_blockRB_case56.c56_fr_apart sp p b o FS A HA HS16 Rp Rb Ro).
  Local Abbreviation c56_bi_call := (C_reac_box_model_blockRB_case56.c56_bi_call ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
    m o FS).
  Local Abbreviation c56_app_win := (C_reac_box_model_blockRB_case56.c56_app_win sp tp m p o FS FP0).
  Local Abbreviation c56_chk := (C_reac_box_model_blockRB_case56.c56_chk off Hoff).

  Lemma c56_call_nfF : forall (k ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (WB OB : list byte)
      (x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> 35 <= k -> k + 16 <= 72 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35) [CB 37 (upd_bytes WB (Z.to_nat (k - 35)) (nmr row nb))] ->
       rw_cells rsegs mc' o [CB 32 OB] ->
       bytes_at rsegs mc' (A + k) (nmr row nb) -> length (nmr row nb) = 16%nat ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22
                  (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 p) (Z_to_bv 64 (A + k)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 f) (Z_to_bv 64 o)
               (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 NAME_FIELD) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros k ret fr f spc j n w56 mc WB OB x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp0 Ho0 B56 Hh Hret Hk1 Hk2 HK HB HWB HOB K.
    destruct (RROW Hp0) as (RROWr & RROWc & RROWs & RROWk).
    pose proof c56_p64 as P64.
    destruct (c56_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c56_geoP Hp0) as (Hp8 & Hrow & HpA & Dps & Dpo & Papp).
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c56_frpos fr f spc j n w56 HK) as FKp.
    pose proof (c56_o_fr_iv Ho0 fr f spc j n w56 HK) as Dofr.
    assert (SPC1 : A - 64 <= spc <= A) by (clear -FKp; destruct FKp as [(E & _) | (E & _)]; lia).
    c56_hide Fsp. c56_hide FKp. c56_hide Dps. c56_hide Dpo. c56_hide Dos. c56_hide Drt.
    c56_hide Dofs. c56_hide DofsF. c56_hide Dofr.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    destruct (c56_rt fr f spc j n w56 mc HK Hp0 Ho0 HB) as (AC & SW & ST).
    pose proof (c56_rowb Hp0 Ho0 fr f spc j n w56 mc HK MU) as HRB.
    pose proof (c56_addr_buf Ho0 fr f spc j n w56 mc HK MU) as AWB.
    pose proof (c56_addr_p Hp0 Ho0 fr f spc j n w56 mc HK MU) as APm.
    pose proof (rs_rw64_range row 280) as RN.
    assert (Up : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; c56_lia).
    assert (Uspc : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; c56_lia).
    assert (Uak : bv_unsigned (Z_to_bv 64 (A + k)) = A + k) by (apply unsigned_lit; c56_lia).
    assert (UN : bv_unsigned (Z_to_bv 64 (rname row)) = rname row)
      by (apply unsigned_lit; unfold rname; c56_lia).
    assert (STc : stk rsegs mc (spc - 2240) spc).
    { destruct (stk_split rsegs mc _ spc _ ST ltac:(c56_lia)) as [S1 _].
      destruct (stk_split rsegs mc _ (spc - 2240) _ S1 ltac:(c56_lia)) as [_ S2]. exact S2. }
    assert (HN8 : bytes_at rsegs mc (p + 280) (le8 (Z_to_bv 64 (rname row)))).
    { unfold rname. rewrite rs_le8 by (c56_ar; lia).
      exact (bytes_at_sub rsegs mc p row 280 8 HRB ltac:(c56_ar; lia)). }
    assert (HNB : exists nb' : list byte,
      ((rname row = 0 /\ nb' = []) \/
       (rname row <> 0 /\ name_ok nb' /\ rname row + Z.of_nat (length nb') <= 2^64 /\
        bytes_at rsegs mc (rname row) nb')) /\
      (spc <= rname row \/ rname row + Z.of_nat (length nb') <= spc - 2240) /\
      (A + k + 16 <= rname row \/ rname row + Z.of_nat (length nb') <= A + k) /\
      addressable mc (rname row) (Z.of_nat (length nb')) /\ nmf nb' = nmr row nb /\ (rname row <> 0 -> nb' = nb)).
    { unfold nmr. destruct (Z.eqb_spec (rname row) 0) as [Z0|NZ].
      - exists []. cbn [length Z.of_nat].
        split; [left; split; [exact Z0 | reflexivity]|].
        split; [c56_lia|]. split; [c56_lia|].
        split; [|split; [reflexivity | intros Hc; exfalso; exact (Hc Z0)]].
        split; [c56_lia|]. split; [c56_lia|].
        split; [unfold APPMEM_END; c56_lia|]. intros i Hi. c56_lia.
      - exists nb. destruct (HN Hp0 B56 Hh NZ) as (OK & HB2 & Dns & Dno).
        pose proof (ANB Hp0 B56 Hh NZ) as ANa.
        pose proof (bytes_at_bound rsegs m (rname row) nb HB2) as BB.
        destruct (c56_dj4 (rname row) (Z.of_nat (length nb)) (NDJ Hp0 B56 Hh NZ)) as (_ & _ & DF).
        split.
        { right. split; [exact NZ|]. split; [exact OK|]. split; [c56_lia|].
          eapply fl_bytes; [exact HB2 | exact MU|].
          intros x Hx. exact (c56_out_nm Hp0 Ho0 B56 Hh NZ fr f spc j n w56 x HK Hx). }
        split; [c56_lia|]. split; [c56_lia|]. split; [|split; [reflexivity | intros _; reflexivity]].
        apply (c56_addr_keep Ho0 fr f spc j n w56 mc (rname row) (Z.of_nat (length nb)) HK MU ANa).
        exact (c56_fr_apart fr f spc j n w56 (rname row) (Z.of_nat (length nb)) HK Dns DF). }
    destruct HNB as (nb' & HNB & DN1 & DN2 & ANm & ENM & ENB).
    assert (LN : length (nmr row nb) = 16%nat).
    { rewrite <- ENM. apply mb_nmf_len.
      destruct HNB as [(_ & E)|(_ & (OKl & _) & _)]; [subst nb'; cbn [length]; lia | c56_lia]. }
    c56_hide HNB. c56_hide DN1. c56_hide DN2.
    pose proof (rs_rw_sub rsegs mc (A + 35) 37 WB (Z.to_nat (k - 35)) 16 HWB ltac:(c56_lia)) as HSLOT.
    assert (ESL : A + 35 + Z.of_nat (Z.to_nat (k - 35)) = A + k) by c56_lia.
    rewrite ESL in HSLOT.
    pose proof HNF as HNF0. unfold name_field_contract_F_on, name_field_post_on, NAME_FIELD_K in HNF0.
    eapply evtF_cut.
    { eapply HNF0 with (name := Z_to_bv 64 (rname row)) (nb := nb')
        (junk := firstn 16 (skipn (Z.to_nat (k - 35)) WB));
      rewrite ?Up, ?Uspc, ?Uak, ?UN.
      - exact STc.
      - c56_lia.
      - exact Hp8.
      - c56_lia.
      - exact HN8.
      - c56_lia.
      - exact HSLOT.
      - exact HNB.
      - c56_show Dps; c56_lia.
      - exact DN1.
      - c56_lia.
      - c56_show Dps; c56_lia.
      - exact DN2.
      - exact MI.
      - exact AC.
      - (* route (C), HD site 7: name_field's region is the word cover of the buffer [A + k, A + k + 16), in the
           window (R's 1st disjunct); SW is the run's region at mc (c56_rt) *)
        apply (shadow_rw_on_mono (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) _ mc);
          [|exact SW].
        intros a Ha. unfold name_field_shadow_R in Ha. rewrite ?Uak in Ha.
        apply (mbHB_R_win (bv_unsigned sp) FS p b o row nb (A + k) 16 a); [lia | c56_lia | c56_lia | exact Ha].
      - unfold HIGHMEM_BEG; c56_lia.
      - unfold APPMEM_END; c56_lia.
      - exact (acl_addr_sub mc p 296 (p + 280) 8 APm ltac:(c56_lia) ltac:(c56_lia) ltac:(c56_lia)).
      - exact ANm.
      - exact (acl_addr_sub mc (A + 35) 37 (A + k) 16 AWB ltac:(c56_lia) ltac:(c56_lia) ltac:(c56_lia)).
      - apply c56_app_win. c56_lia.
      - right. unfold RT_HI; c56_lia.
      (* the regions of the call, in name_field_contract_F's order (40a1a45d985) *)
      - exact RBY.
      - eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia].
      - eapply rng_sub; [exact RWIN | c56_lia | c56_lia].
      - unfold shadow_addr; try unfold NAME_FIELD_K. apply (KWIN (spc - 2240) (spc - 32 - 1)); c56_lia.
      - eapply rng_sub; [exact RROWr | c56_lia | c56_lia].
      - unfold shadow_addr. apply (RROWc (p + 280)). c56_lia.
      - intros HnZ. rewrite (ENB HnZ). exact (proj1 (RNM Hp0 B56 Hh HnZ)).
      - intros HnZ. rewrite (ENB HnZ). destruct (RNM Hp0 B56 Hh HnZ) as (_ & _ & RNMs & _).
        destruct (HN Hp0 B56 Hh HnZ) as ((OKl & _) & _). unfold shadow_addr.
        eapply rng_sub; [apply (RNMs (rname row) (rname row + Z.of_nat (length nb) - 1)) | |]; c56_lia.
      - eapply rng_sub; [exact RWIN | c56_lia | c56_lia].
      - unfold shadow_addr. apply (KWIN (A + k) (A + k + 16 - 1)); c56_lia. }
    intros ms' PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & mc'
                    & Ems & HBN & MU2 & WM2 & MI2 & ST2 & AC2 & SW2).
    subst ms'. rewrite Hret.
    rewrite Uak in HBN, MU2. rewrite Uspc in MU2, ST2. rewrite ENM in HBN.
    assert (RM2 : rd_mono mc mc').
    { apply (rd_mono_list _ _ _ MU2).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; intros y Hy.
      - exact (rd_of_stk mc' (spc - 2240) spc ST2 y Hy).
      - exact (acl_bytes_rd mc' (A + k) (nmr row nb) y HBN ltac:(rewrite LN; cbn [Z.of_nat]; c56_lia)). }
    assert (HB2 : BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc').
    { eapply (c56_bi_call fr j n w56 mc mc' _ HB MU2 WM2 RM2 MI2).
      - intros x Hx. unfold c56_W, Wf in Hx. cbn [app outside fst snd] in Hx.
        destruct Hx as (Hw & _). cbn [outside fst snd].
        split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. c56_show FKp. split; [c56_lia|]. split; [c56_lia | exact I]. }
    assert (HWB2 : rw_cells rsegs mc' (A + 35) [CB 37 (upd_bytes WB (Z.to_nat (k - 35)) (nmr row nb))]).
    { eapply (mb_upd rsegs mc mc' (A + 35) 37 WB (Z.to_nat (k - 35)) 16 (nmr row nb) _ HWB
                ltac:(c56_lia) MU2 WM2).
      - cbn [disjoint_from]. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. split; [c56_lia|]. split; [c56_lia | exact I].
      - rewrite ESL. exact HBN.
      - exact LN. }
    assert (HOB2 : rw_cells rsegs mc' o [CB 32 OB]).
    { eapply (rw_cells_transport rsegs _ mc mc' o _ HOB MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add].
      c56_show Dos. split; [c56_lia|]. split; [c56_lia | exact I]. }
    exact (K mc' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HB2 HWB2 HOB2 HBN LN).
  Qed.

  (* asan_memcpy (o + kd, A + ks, N) at 0x52164: N bytes of the window's buffer into the output block. *)
  Lemma c56_call_mcoF : forall (kd ks N ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (WB OB : list byte) (x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
    0 <= kd -> kd + 8 <= 32 -> kd + N <= 32 -> 35 <= ks -> ks + N <= 72 -> 0 <= N ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35) [CB 37 WB] ->
       rw_cells rsegs mc' o
         [CB 32 (upd_bytes OB (Z.to_nat kd) (firstn (Z.to_nat N) (skipn (Z.to_nat (ks - 35)) WB)))] ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (o + kd)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o)
                  (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                  y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (o + kd)) (Z_to_bv 64 (A + ks)) (Z_to_bv 64 N) x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros kd ks N ret fr f spc j n w56 mc WB OB x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp0 Ho0 Hret Hkd0 Hkd8 HkdN Hks1 Hks2 HN0 HK HB HWB HOB K.
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    pose proof c56_p64 as P64. assert (P40 : 72 < 2^40) by (vm_compute; reflexivity).
    destruct (c56_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c56_frpos fr f spc j n w56 HK) as FKp.
    pose proof (c56_o_fr_iv Ho0 fr f spc j n w56 HK) as Dofr.
    assert (SPC1 : A - 64 <= spc <= A) by (clear -FKp; destruct FKp as [(E & _) | (E & _)]; lia).
    c56_hide Fsp. c56_hide FKp. c56_hide Dos. c56_hide Drt. c56_hide Dofs. c56_hide DofsF. c56_hide Dofr.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    destruct (c56_rt fr f spc j n w56 mc HK Hp0 Ho0 HB) as (AC & SW & ST).
    pose proof (c56_addr_buf Ho0 fr f spc j n w56 mc HK MU) as AWB.
    pose proof (c56_addr_o Ho0 fr f spc j n w56 mc HK MU) as AOm.
    assert (Uspc : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; c56_lia).
    assert (Uod : bv_unsigned (Z_to_bv 64 (o + kd)) = o + kd) by (apply unsigned_lit; c56_lia).
    assert (Uas : bv_unsigned (Z_to_bv 64 (A + ks)) = A + ks) by (apply unsigned_lit; c56_lia).
    assert (UN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; c56_lia).
    pose proof HWB as HWB0. destruct HWB0 as [[[LWB _] _] _]. cbn [cell_wf] in LWB.
    remember (firstn (Z.to_nat N) (skipn (Z.to_nat (ks - 35)) WB)) as src eqn:Esrc.
    assert (LS : length src = Z.to_nat N) by (subst src; rewrite length_firstn, length_skipn; c56_lia).
    pose proof (rs_rw_sub rsegs mc (A + 35) 37 WB (Z.to_nat (ks - 35)) (Z.to_nat N) HWB ltac:(c56_lia)) as HSRC.
    assert (ES : A + 35 + Z.of_nat (Z.to_nat (ks - 35)) = A + ks) by c56_lia.
    rewrite ES, <- Esrc in HSRC.
    pose proof (rs_rw_sub rsegs mc o 32 OB (Z.to_nat kd) (Z.to_nat N) HOB ltac:(c56_lia)) as HDST.
    assert (ED : o + Z.of_nat (Z.to_nat kd) = o + kd) by c56_lia.
    rewrite ED in HDST.
    assert (STc : stk rsegs mc (bv_unsigned sp - 4272) spc)
      by (exact (proj1 (stk_split rsegs mc _ spc _ ST ltac:(c56_lia)))).
    pose proof HMC as HMC0. unfold asan_memcpy_contract_F_on, ASAN_MEMCPY_K in HMC0. cbv zeta in HMC0.
    eapply evtF_cut.
    { eapply HMC0 with (src := src) (junk := firstn (Z.to_nat N) (skipn (Z.to_nat kd) OB))
        (lo := bv_unsigned sp - 4272);
      rewrite ?Uspc, ?Uod, ?Uas, ?UN.
      - exact (mb_rw1 _ _ _ _ _ HSRC).
      - exact LS.
      - exact HDST.
      - c56_show Dos; c56_lia.
      - c56_lia.
      - exact (acl_addr_sub mc (A + 35) 37 (A + ks) N AWB ltac:(c56_lia) ltac:(c56_lia) ltac:(c56_lia)).
      - exact (acl_addr_sub mc o 32 (o + kd) N AOm ltac:(c56_lia) ltac:(c56_lia) ltac:(c56_lia)).
      - right. apply c56_app_win. c56_lia.
      - right. destruct (Z.eq_dec (kd + N) 32) as [E|E].
        + replace (o + kd + N) with (o + 32) by c56_lia. exact Hoapp.
        + replace (o + kd + N) with (o + (kd + N)) by c56_lia. apply Oapp. c56_lia.
      - right. split; [apply c56_app_win; c56_lia|].
        replace (o + kd + 7) with (o + (kd + 7)) by c56_lia. apply Oapp. c56_lia.
      - c56_show Drt; c56_lia.
      - c56_show Dos; c56_lia.
      - c56_lia.
      - exact STc.
      - c56_lia.
      - exact HHM.
      - unfold APPMEM_END; c56_lia.
      - exact AC.
      - apply (mbHB_cpy _ mc (o + kd) (A + ks) N SW); [c56_lia | c56_lia | c56_lia | |].
        + intros a Ha.
          apply (mbHB_R_win (bv_unsigned sp) FS p b o row nb (A + ks) N a);
            [c56_lia | c56_lia | c56_lia | exact Ha].
        + intros a Ha.
          apply (mbHB_R_o (bv_unsigned sp) FS p b o row nb (o + kd) N a);
            [c56_lia | exact Ho0 | c56_lia | c56_lia | exact Ha].
      - exact MI.
      (* the regions of the call, in a Theorem Labs lane's order *)
      - exact RBY.
      - eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia].
      - eapply rng_sub; [exact RWIN | c56_lia | c56_lia].
      - eapply rng_sub; [exact ROUTr | c56_lia | c56_lia].
      - eapply rng_sub; [exact RWIN | c56_lia | c56_lia].
      - apply (mbF_shw RNG o 32 (o + kd) N ROUTk); c56_lia.
      - apply (mbF_shw RNG (bv_unsigned sp - 4272) 4272 (A + ks) N KWIN); c56_lia.
      - apply (mbF_shw RNG (bv_unsigned sp - 4272) 4272 _ 2224 KWIN); c56_lia. }
    intros ms' PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & mc'
                    & Ems & MU2 & WM2 & MI2 & ST2 & RW2 & SB2 & AC2 & SW2).
    subst ms'. rewrite Hret. clear SB2.
    rewrite Uod, UN, Uspc in MU2. rewrite Uod, UN in RW2. rewrite Uspc in ST2.
    unfold ASAN_MEMCPY_K in MU2.
    pose proof (mb_rw1 _ _ _ _ _ RW2) as HBY.
    assert (RM2 : rd_mono mc mc').
    { apply (rd_mono_list _ _ _ MU2).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; intros y Hy.
      - exact (acl_bytes_rd mc' (o + kd) src y HBY ltac:(rewrite LS; c56_lia)).
      - exact (rd_of_stk mc' (bv_unsigned sp - 4272) spc ST2 y ltac:(clear -Hy SPC1 HAlo; lia)). }
    assert (HB2 : BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc').
    { eapply (c56_bi_call fr j n w56 mc mc' _ HB MU2 WM2 RM2 MI2).
      - intros x Hx. unfold c56_W, Wf in Hx. cbn [app outside fst snd] in Hx.
        destruct Hx as (Hw & _ & _ & _ & _ & Ho & _). cbn [outside fst snd].
        split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. c56_show Dos. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. c56_show Dofs. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. c56_show Dofr. c56_show FKp. split; [c56_lia|]. split; [c56_lia | exact I]. }
    assert (HOB2 : rw_cells rsegs mc' o [CB 32 (upd_bytes OB (Z.to_nat kd) src)]).
    { eapply (mb_upd rsegs mc mc' o 32 OB (Z.to_nat kd) (Z.to_nat N) src _ HOB ltac:(c56_lia) MU2 WM2).
      - cbn [disjoint_from]. c56_show Dos. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. c56_show Dos. split; [c56_lia|]. split; [c56_lia | exact I].
      - rewrite ED. exact HBY.
      - exact LS. }
    assert (HWB2 : rw_cells rsegs mc' (A + 35) [CB 37 WB]).
    { eapply (rw_cells_transport rsegs _ mc mc' (A + 35) _ HWB MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add].
      c56_show Dos. split; [c56_lia|]. split; [c56_lia | exact I]. }
    subst src.
    exact (K mc' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HB2 HWB2 HOB2).
  Qed.

  (* asan_memcpy (A + kd, A + ks, N) at 0x52164: N bytes of the window's buffer to a lower place of it. *)
  Lemma c56_call_mcfF : forall (kd ks N ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (WB OB : list byte) (x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
    35 <= kd -> kd + N <= ks -> ks + N <= 72 -> 0 <= N ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35)
         [CB 37 (upd_bytes WB (Z.to_nat (kd - 35)) (firstn (Z.to_nat N) (skipn (Z.to_nat (ks - 35)) WB)))] ->
       rw_cells rsegs mc' o [CB 32 OB] ->
       evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (A + kd)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o)
                  (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                  y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (A + kd)) (Z_to_bv 64 (A + ks)) (Z_to_bv 64 N) x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros kd ks N ret fr f spc j n w56 mc WB OB x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp0 Ho0 Hret Hkd1 HkdN Hks2 HN0 HK HB HWB HOB K.
    pose proof c56_p64 as P64. assert (P40 : 72 < 2^40) by (vm_compute; reflexivity).
    destruct (c56_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c56_frpos fr f spc j n w56 HK) as FKp.
    assert (SPC1 : A - 64 <= spc <= A) by (clear -FKp; destruct FKp as [(E & _) | (E & _)]; lia).
    c56_hide Fsp. c56_hide FKp. c56_hide Dos. c56_hide Drt. c56_hide Dofs. c56_hide DofsF.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    destruct (c56_rt fr f spc j n w56 mc HK Hp0 Ho0 HB) as (AC & SW & ST).
    pose proof (c56_addr_buf Ho0 fr f spc j n w56 mc HK MU) as AWB.
    assert (Uspc : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; c56_lia).
    assert (Uad : bv_unsigned (Z_to_bv 64 (A + kd)) = A + kd) by (apply unsigned_lit; c56_lia).
    assert (Uas : bv_unsigned (Z_to_bv 64 (A + ks)) = A + ks) by (apply unsigned_lit; c56_lia).
    assert (UN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; c56_lia).
    pose proof HWB as HWB0. destruct HWB0 as [[[LWB _] _] _]. cbn [cell_wf] in LWB.
    remember (firstn (Z.to_nat N) (skipn (Z.to_nat (ks - 35)) WB)) as src eqn:Esrc.
    assert (LS : length src = Z.to_nat N) by (subst src; rewrite length_firstn, length_skipn; c56_lia).
    pose proof (rs_rw_sub rsegs mc (A + 35) 37 WB (Z.to_nat (ks - 35)) (Z.to_nat N) HWB ltac:(c56_lia)) as HSRC.
    assert (ES : A + 35 + Z.of_nat (Z.to_nat (ks - 35)) = A + ks) by c56_lia.
    rewrite ES, <- Esrc in HSRC.
    pose proof (rs_rw_sub rsegs mc (A + 35) 37 WB (Z.to_nat (kd - 35)) (Z.to_nat N) HWB ltac:(c56_lia)) as HDST.
    assert (ED : A + 35 + Z.of_nat (Z.to_nat (kd - 35)) = A + kd) by c56_lia.
    rewrite ED in HDST.
    assert (STc : stk rsegs mc (bv_unsigned sp - 4272) spc)
      by (exact (proj1 (stk_split rsegs mc _ spc _ ST ltac:(c56_lia)))).
    pose proof HMC as HMC0. unfold asan_memcpy_contract_F_on, ASAN_MEMCPY_K in HMC0. cbv zeta in HMC0.
    eapply evtF_cut.
    { eapply HMC0 with (src := src) (junk := firstn (Z.to_nat N) (skipn (Z.to_nat (kd - 35)) WB))
        (lo := bv_unsigned sp - 4272);
      rewrite ?Uspc, ?Uad, ?Uas, ?UN.
      - exact (mb_rw1 _ _ _ _ _ HSRC).
      - exact LS.
      - exact HDST.
      - c56_lia.
      - c56_lia.
      - exact (acl_addr_sub mc (A + 35) 37 (A + ks) N AWB ltac:(c56_lia) ltac:(c56_lia) ltac:(c56_lia)).
      - exact (acl_addr_sub mc (A + 35) 37 (A + kd) N AWB ltac:(c56_lia) ltac:(c56_lia) ltac:(c56_lia)).
      - right. apply c56_app_win. c56_lia.
      - right. apply c56_app_win. c56_lia.
      - right. split; apply c56_app_win; c56_lia.
      - right. unfold RT_HI; c56_lia.
      - c56_lia.
      - c56_lia.
      - exact STc.
      - c56_lia.
      - exact HHM.
      - unfold APPMEM_END; c56_lia.
      - exact AC.
      - apply (mbHB_cpy _ mc (A + kd) (A + ks) N SW); [c56_lia | c56_lia | c56_lia | |].
        + intros a Ha.
          apply (mbHB_R_win (bv_unsigned sp) FS p b o row nb (A + ks) N a);
            [c56_lia | c56_lia | c56_lia | exact Ha].
        + intros a Ha.
          apply (mbHB_R_win (bv_unsigned sp) FS p b o row nb (A + kd) N a);
            [c56_lia | c56_lia | c56_lia | exact Ha].
      - exact MI.
      (* the regions of the call, in a Theorem Labs lane's order *)
      - exact RBY.
      - eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia].
      - eapply rng_sub; [exact RWIN | c56_lia | c56_lia].
      - eapply rng_sub; [exact RWIN | c56_lia | c56_lia].
      - eapply rng_sub; [exact RWIN | c56_lia | c56_lia].
      - apply (mbF_shw RNG (bv_unsigned sp - 4272) 4272 (A + kd) N KWIN); c56_lia.
      - apply (mbF_shw RNG (bv_unsigned sp - 4272) 4272 (A + ks) N KWIN); c56_lia.
      - apply (mbF_shw RNG (bv_unsigned sp - 4272) 4272 _ 2224 KWIN); c56_lia. }
    intros ms' PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & mc'
                    & Ems & MU2 & WM2 & MI2 & ST2 & RW2 & SB2 & AC2 & SW2).
    subst ms'. rewrite Hret. clear SB2.
    rewrite Uad, UN, Uspc in MU2. rewrite Uad, UN in RW2. rewrite Uspc in ST2.
    unfold ASAN_MEMCPY_K in MU2.
    pose proof (mb_rw1 _ _ _ _ _ RW2) as HBY.
    assert (RM2 : rd_mono mc mc').
    { apply (rd_mono_list _ _ _ MU2).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; intros y Hy.
      - exact (acl_bytes_rd mc' (A + kd) src y HBY ltac:(rewrite LS; c56_lia)).
      - exact (rd_of_stk mc' (bv_unsigned sp - 4272) spc ST2 y ltac:(clear -Hy SPC1 HAlo; lia)). }
    assert (HB2 : BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc').
    { eapply (c56_bi_call fr j n w56 mc mc' _ HB MU2 WM2 RM2 MI2).
      - intros x Hx. unfold c56_W, Wf in Hx. cbn [app outside fst snd] in Hx.
        destruct Hx as (Hw & _). cbn [outside fst snd].
        split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. c56_show FKp. split; [c56_lia|]. split; [c56_lia | exact I]. }
    assert (HWB2 : rw_cells rsegs mc' (A + 35) [CB 37 (upd_bytes WB (Z.to_nat (kd - 35)) src)]).
    { eapply (mb_upd rsegs mc mc' (A + 35) 37 WB (Z.to_nat (kd - 35)) (Z.to_nat N) src _ HWB
                ltac:(c56_lia) MU2 WM2).
      - cbn [disjoint_from]. split; [c56_lia|]. split; [c56_lia | exact I].
      - cbn [disjoint_from]. split; [c56_lia|]. split; [c56_lia | exact I].
      - rewrite ED. exact HBY.
      - exact LS. }
    assert (HOB2 : rw_cells rsegs mc' o [CB 32 OB]).
    { eapply (rw_cells_transport rsegs _ mc mc' o _ HOB MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add].
      c56_show Dos. split; [c56_lia|]. split; [c56_lia | exact I]. }
    subst src.
    exact (K mc' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HB2 HWB2 HOB2).
  Qed.

  (* ---- the output block's check byte and the release ---- *)

  (* 0x86e08: the check byte (- sum) mod 256 stored at o + 31 (its shadow check passed), the return value 1, and
     the release at 0x86e14. *)
  Lemma c56_st31F : forall (X : list byte) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> length X = 32%nat ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (o + 31)) (Z_to_bv 64 (psum X 31)) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86e08) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros X fr f spc j n w56 mc x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp0 Ho0 LX ES Er HK HB HOc.
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    pose proof Hrel as REL. pose proof (c56_Wu Hp0 Ho0 fr j n) as EW.
    pose proof c56_p64 as P64.
    destruct (c56_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c56_o_fr_iv Ho0 fr f spc j n w56 HK) as Dofr.
    pose proof (psum_range X 31) as PR.
    destruct HB as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    unfold SAVES in SV.
    unfold c56_W, Wf in MU. cbn [app] in MU.
    clear Fsp Drt DofsF Oapp.
    c56_sc.
    step. step. step.
    destruct HOc as [[_ HBo] _]. cbn [cells_bytes cbytes app] in HBo.
    assert (Epo : (p =? 0) || (o =? 0) = false)
      by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
    eapply (REL fr f spc j n w56 _ 1); [exact HK | | | ].
    - rewrite Epo. symmetry. exact Er.
    - rewrite EW. split; [unfold c56_W, Wf; exact MU|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [eexists; eassumption | assumption].
    - rewrite Epo. rewrite <- ES. unfold withchk, chk. rewrite rs_psum_firstn by lia.
      rewrite <- c56_neg8. exact HBo.
  Qed.

  (* 0x86dc4 (after loop5): the shadow check of o + 31 in its beqz form, then 0x86e08. *)
  Lemma c56_tail5F : forall (X : list byte) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> length X = 32%nat ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 (Z_to_bv 64 (psum X 31)) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86dc4) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros X fr f spc j n w56 mc x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp0 Ho0 LX ES Er HK HB HOc.
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    pose proof c56_st31F as ST31.
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof HB as HB'. destruct HB' as (MU & _).
    pose proof (c56_addr_o Ho0 fr f spc j n w56 mc HK MU) as AOm. clear MU.
    assert (RX : 0 <= o + 31 < 2^64) by c56_lia.
    pose proof (c56_chk mc o 32 31 1 (o + 31) AOm ltac:(c56_lia) ltac:(c56_lia) ltac:(c56_lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 31) 8 eq_refl); c56_lia) eq_refl) as SH.
    clear AOm Dos Drt Dofs DofsF Oapp.
    c56_sc.
    step. step. nf.
    step.
    destruct SH as (k & RK & OK & KR).
    pre_sr (o + 31) RX. steps_until_if. clear RK.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia).
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbv iota.
    - eapply ST31; eassumption.
    - step. rewrite ?(unsigned_lit (o + 31)) by (clear -RX; lia). rewrite rc_land7.
      step.
      pose proof (Z.mod_pos_bound (o + 31) 8 eq_refl) as MB.
      rewrite (rc_lts_signed ((o + 31) mod 8) (bv_signed k)) by (clear -MB KR; lia).
      replace ((o + 31) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]).
      cbv iota.
      eapply ST31; eassumption.
  Qed.

  (* 0x86dec (after loop6): the shadow check of o + 31 in its bnez form, then 0x86e08. *)
  Lemma c56_tail6F : forall (X : list byte) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> length X = 32%nat ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 (Z_to_bv 64 (psum X 31)) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86dec) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros X fr f spc j n w56 mc x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp0 Ho0 LX ES Er HK HB HOc.
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    pose proof c56_st31F as ST31.
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof HB as HB'. destruct HB' as (MU & _).
    pose proof (c56_addr_o Ho0 fr f spc j n w56 mc HK MU) as AOm. clear MU.
    assert (RX : 0 <= o + 31 < 2^64) by c56_lia.
    pose proof (c56_chk mc o 32 31 1 (o + 31) AOm ltac:(c56_lia) ltac:(c56_lia) ltac:(c56_lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 31) 8 eq_refl); c56_lia) eq_refl) as SH.
    clear AOm Dos Drt Dofs DofsF Oapp.
    c56_sc.
    step. step. nf.
    step.
    chk_core (o + 31) RX (Z_to_bv 5 13) SH pre_sr no_extra.
    eapply ST31; eassumption.
  Qed.

  (* The outer byte sum of build_ident_first over the output block, at 0x86aec; each load of o has its shadow
     check. *)
  Lemma c56_loop5F : forall (kk i : nat) (X : list byte) (a3w : word) (fr f spc j n : Z) (w56 : word)
      (mc : word -> option byte) (x1 x5 x6 x7 x10 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (i + kk = 31)%nat -> (0 < kk)%nat -> length X = 32%nat ->
    bv_unsigned a3w = 18446744073709551615 - o ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat i)) a3w (Z_to_bv 64 31) x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86aec) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    induction kk as [|kk IH]; intros i X a3w fr f spc j n w56 mc x1 x5 x6 x7 x10 x15 x16 x17 x21 x22
      x28 x29 x30 x31 Hp0 Ho0 Hik Hk LX H3 ES Er HK HB HOc; [c56_lia|].
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    pose proof c56_tail5F as T5.
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof HB as HB'. destruct HB' as (MU & _).
    pose proof (c56_addr_o Ho0 fr f spc j n w56 mc HK MU) as AOm. clear MU.
    pose proof (rd_byte rsegs mc o X i (mb_rw1 _ _ _ _ _ HOc) ltac:(c56_lia)) as RD.
    pose proof (psum_range X i) as PR.
    assert (RX : 0 <= o + Z.of_nat i < 2^64) by c56_lia.
    pose proof (c56_chk mc o 32 (Z.of_nat i) 1 (o + Z.of_nat i) AOm ltac:(c56_lia) ltac:(c56_lia)
                  ltac:(c56_lia) ltac:(pose proof (Z.mod_pos_bound (o + Z.of_nat i) 8 eq_refl); c56_lia)
                  eq_refl) as SH.
    clear AOm Dos Drt Dofs DofsF Oapp.
    c56_sc.
    step. nf.
    step.
    chk_core (o + Z.of_nat i) RX (Z_to_bv 5 16) SH pre_sr no_extra.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 31) by lia.
    destruct kk as [|kk].
    - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
      step. replace (S i) with 31%nat by lia.
      eapply T5; eassumption.
    - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      eapply (IH (S i)); first [lia | eassumption].
  Qed.

  (* The outer byte sum of build_ident_last over the output block, at 0x86d84. *)
  Lemma c56_loop6F : forall (kk i : nat) (X : list byte) (a3w : word) (fr f spc j n : Z) (w56 : word)
      (mc : word -> option byte) (x1 x5 x6 x7 x10 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (i + kk = 31)%nat -> (0 < kk)%nat -> length X = 32%nat ->
    bv_unsigned a3w = 18446744073709551615 - o ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat i)) a3w (Z_to_bv 64 31) x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86d84) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    induction kk as [|kk IH]; intros i X a3w fr f spc j n w56 mc x1 x5 x6 x7 x10 x15 x16 x17 x21 x22
      x28 x29 x30 x31 Hp0 Ho0 Hik Hk LX H3 ES Er HK HB HOc; [c56_lia|].
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    pose proof c56_tail6F as T6.
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof HB as HB'. destruct HB' as (MU & _).
    pose proof (c56_addr_o Ho0 fr f spc j n w56 mc HK MU) as AOm. clear MU.
    pose proof (rd_byte rsegs mc o X i (mb_rw1 _ _ _ _ _ HOc) ltac:(c56_lia)) as RD.
    pose proof (psum_range X i) as PR.
    assert (RX : 0 <= o + Z.of_nat i < 2^64) by c56_lia.
    pose proof (c56_chk mc o 32 (Z.of_nat i) 1 (o + Z.of_nat i) AOm ltac:(c56_lia) ltac:(c56_lia)
                  ltac:(c56_lia) ltac:(pose proof (Z.mod_pos_bound (o + Z.of_nat i) 8 eq_refl); c56_lia)
                  eq_refl) as SH.
    clear AOm Dos Drt Dofs DofsF Oapp.
    c56_sc.
    step. nf.
    step.
    chk_core (o + Z.of_nat i) RX (Z_to_bv 5 16) SH pre_sr no_extra.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 31) by lia.
    destruct kk as [|kk].
    - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
      step. replace (S i) with 31%nat by lia.
      eapply T6; eassumption.
    - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      eapply (IH (S i)); first [lia | eassumption].
  Qed.

  (* ---- b = 5 ---- *)

  (* 0x86a5c: name_field into the window's buffer at A + 35, dt1_head's 20 header bytes into o, the flag byte at
     o + 20, the first 10 name bytes at o + 21, then the outer sum and the release. *)
  Lemma c56_case5F : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 5 -> p <> 0 -> o <> 0 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p)
               (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x86a5c) fc None mc (seg_rom rsegs)).
  Proof.
    mbF_open HRNG.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      Hb Hp0 Ho0 HK HB HOc.
    destruct (ROUT Hp0 Ho0) as (ROUTr & ROUTc & ROUTs & ROUTk).
    destruct (RROW Hp0) as (RROWr & RROWc & RROWs & RROWk).
    clear RROW ROUT RJ4 RJ3 RNM RTLS.
    pose proof c56_call_nfF as CNF. pose proof c56_call_mcoF as CMC. pose proof c56_loop5F as L5.
    pose proof Hrel as REL. pose proof (c56_Wu Hp0 Ho0 fr j n) as EW.
    pose proof c56_chk as CHK. pose proof c56_bi_call as BIC. pose proof c56_rt as RT.
    pose proof c56_addr_o as AO1. pose proof c56_addr_buf as AB1. pose proof c56_rowb as ROWB.
    pose proof c56_app_win as APW.
    pose proof HDH as DH0. unfold dt1_head_contract_F_on, DT1_HEAD_FRAME in DH0.
    pose proof c56_p64 as P64.
    destruct (c56_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c56_geoP Hp0) as (Hp8 & Hrow & HpA & Dps & Dpo & Papp).
    destruct (c56_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c56_frpos fr f spc j n w56 HK) as FKp.
    pose proof (c56_o_fr_iv Ho0 fr f spc j n w56 HK) as Dofr.
    assert (SPC1 : A - 64 <= spc <= A) by (clear -FKp; destruct FKp as [(E & _) | (E & _)]; lia).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    destruct (RT fr f spc j n w56 mc HK Hp0 Ho0 HB) as (AC & SW & ST).
    pose proof (ROWB Hp0 Ho0 fr f spc j n w56 mc HK MU) as HRB.
    pose proof (rs_rd4 rsegs mc p row 56 HRB ltac:(clear -Hrow; lia)) as RD56.
    change (Z.of_nat 56) with 56 in RD56.
    pose proof (rs_rw32_range row 56) as Rh.
    pose proof (AO1 Ho0 fr f spc j n w56 mc HK MU) as AOm.
    pose proof (c56_addr_p Hp0 Ho0 fr f spc j n w56 mc HK MU) as APm.
    (* the window's scratch buffer *)
    destruct (stk_split rsegs mc _ (A + 72) _ ST ltac:(clear -HAlo HAhi; lia)) as [STb _].
    destruct (stk_carve rsegs mc _ (A + 72) 37%nat STb ltac:(clear -HAlo HAhi HM1; cbn [Z.of_nat]; lia))
      as [_ [WB HWB]].
    replace (A + 72 - Z.of_nat 37) with (A + 35) in HWB by (cbn [Z.of_nat]; lia).
    assert (HOapp : forall x, bv_unsigned sp - 4272 <= x < bv_unsigned sp \/ o <= x < o + 32 -> app_mem x).
    { intros x [Hx|Hx]; [apply APW; exact Hx | replace x with (o + (x - o)) by lia; apply Oapp; lia]. }
    unfold c56_W, Wf in MU. cbn [app] in MU. unfold SAVES in SV.
    clear Fsp HB ST STb ROWB AB1.
    c56_hide Dps. c56_hide Dpo. c56_hide DofsF. c56_hide Drt.
    c56_sc.
    (* 0x86a5c: p is 8-aligned, so the alignment branch is not taken *)
    step. step.
    replace (Z.land (bv_unsigned (Z_to_bv 64 p)) 7) with 0
      by (rewrite unsigned_lit by lia; rewrite rc_land7; rewrite Hp8; reflexivity).
    nf.
    (* the instrumented check of the 4 bytes at p + 56 *)
    step.
    assert (RX56 : 0 <= p + 56 < 2^64) by lia.
    pose proof (CHK mc p 296 56 4 (p + 56) APm ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound p 8 eq_refl); Z.div_mod_to_equations; lia) eq_refl) as SH56.
    chk_core (p + 56) RX56 (Z_to_bv 5 12) SH56 pre_sr add1.
    step. step.
    rewrite mb_sx32_eq0 by lia.
    destruct (Z.eqb_spec (rw32 row 56) 0) as [H0|H0]; cbv iota.
    { (* has row = 0: the block stays zero and the return value is 0 *)
      step. step.
      assert (Epo : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      eapply (REL fr f spc j n w56 _ 0); [exact HK | | | ].
      - rewrite Epo, Hb, mb_rc5. unfold has. rewrite H0. reflexivity.
      - rewrite EW. split; [unfold c56_W, Wf; exact MU|].
        split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [eexists; eassumption | assumption].
      - rewrite Epo, Hb, mb_synth5. unfold has. rewrite H0.
        exact (mb_rw1 _ _ _ _ _ HOc). }
    (* name_field (p, A + 35) *)
    step. step. step.
    eapply (CNF 35 0x86a8c fr f spc j n w56 mc WB (zeros 32));
      [exact Hp0 | exact Ho0 | left; exact Hb | unfold has; exact H0
      | apply ret_pc_even; [lia | reflexivity] | lia | lia | exact HK | | exact HWB | exact HOc |].
    { split; [unfold c56_W, Wf; exact MU|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption]. }
    intros mc2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HB2 HWB2 HOB2 HNM LN.
    (* dt1_head (o, 1, 22, 4096) *)
    do 5 step.
    pose proof HB2 as HB2'. destruct HB2' as (MU2 & WM2 & RM2 & MI2 & SV2 & (hh2 & HH2) & F562).
    destruct (RT fr f spc j n w56 mc2 HK Hp0 Ho0 HB2) as (AC2 & SW2 & ST2).
    pose proof (AO1 Ho0 fr f spc j n w56 mc2 HK MU2) as AOm2.
    pose proof HOB2 as HOB2'. destruct HOB2' as [_ WO2]. cbn [cells_size csize Nat.add] in WO2.
    eapply evtF_cut.
    { eapply DH0 with (RNG := RNG) (sp := Z_to_bv 64 spc) (lo := bv_unsigned sp - 4272);
      rewrite ?(unsigned_lit spc) by lia; rewrite ?(unsigned_lit o) by lia.
      - lia.
      - apply (wr_at_prefix _ _ _ 32); [exact WO2 | lia].
      - exact (proj1 (stk_split rsegs mc2 _ spc _ ST2 ltac:(lia))).
      - lia.
      - lia.
      - exact AC2.
      (* route (C), HD site 10: dt1_head_contract_F_on has no shadow premise (dt1_head reads its shadow through
         addressable and stores none) *)
      - exact (acl_addr_sub mc2 o 32 o 20 AOm2 ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros x Hx. cbn [outside fst snd]. unfold GOT_CELL_K, CELL_K in Hx.
        assert (Hnot : ~ (bv_unsigned sp - 4272 <= x < bv_unsigned sp) /\ ~ (o <= x < o + 20)).
        { destruct Hx as [Hx|[Hx|Hx]].
          - c56_show Drt. split; [unfold RT_LO, RT_HI in Drt; lia | unfold RT_LO, RT_HI in Drt; lia].
          - c56_show Drt. split; [unfold RT_LO, RT_HI in Drt; lia | unfold RT_LO, RT_HI in Drt; lia].
          - split; intros Hin; exact (acl_app_not_shadow x (HOapp x ltac:(lia)) Hx). }
        destruct Hnot as [N1 N2]. split; [lia|]. split; [lia | exact I].
      - eapply rng_sub; [exact RWIN | lia | lia].
      - eapply rng_sub; [exact RIMG | unfold RT_LO; lia | unfold RT_LO, RT_HI; lia].
      - eapply rng_sub; [exact ROUTr | lia | lia].
      - apply (ROUTs o (o + 19)); lia. }
    intros ms3 PO3.
    destruct PO3 as (z10 & z11 & z12 & z14 & z15 & z16 & z17 & mc3 & Ems3 & HB3 & MU3 & WM3 & MI3' & ST3).
    subst ms3. specialize (MI3' MI2).
    rewrite ?(unsigned_lit spc) in MU3, ST3 by lia. rewrite ?(unsigned_lit o) in HB3, MU3 by lia.
    cbn [bv_unsigned] in HB3.
    replace (ret_pc (Z_to_bv 64 0x86aa0)) with (Z_to_bv 64 0x86aa0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (RM3 : rd_mono mc2 mc3).
    { apply (rd_mono_list _ _ _ MU3).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; intros y Hy.
      - exact (rd_of_stk mc3 (bv_unsigned sp - 4272) spc ST3 y ltac:(clear -Hy SPC1 HAlo; lia)).
      - exact (acl_bytes_rd mc3 o _ y HB3 ltac:(clear -Hy; cbn [dt1_bytes map length Z.of_nat]; lia)). }
    assert (HB3' : BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c56_W sp o FS fr j n) fr w56 mc3).
    { eapply (BIC fr j n w56 mc2 mc3 _ HB2 MU3 WM3 RM3 MI3').
      - intros x Hx. unfold c56_W, Wf in Hx. cbn [app outside fst snd] in Hx.
        destruct Hx as (Hw & _ & _ & _ & _ & Ho & _). cbn [outside fst snd].
        split; [lia|]. split; [lia | exact I].
      - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
      - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
      - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
    assert (HOB3 : rw_cells rsegs mc3 o [CB 32 (upd_bytes (zeros 32) 0 (dt1_bytes 1 22 4096))]).
    { eapply (mb_upd rsegs mc2 mc3 o 32 (zeros 32) 0 20 _ _ HOB2 ltac:(lia) MU3 WM3).
      - cbn [disjoint_from Z.of_nat]. split; [lia|]. split; [lia | exact I].
      - cbn [disjoint_from Z.of_nat]. split; [lia|]. split; [lia | exact I].
      - cbn [Z.of_nat]. rewrite Z.add_0_r. exact HB3.
      - reflexivity. }
    assert (HWB3 : rw_cells rsegs mc3 (A + 35) [CB 37 (upd_bytes WB 0 (nmr row nb))]).
    { eapply (rw_cells_transport rsegs _ mc2 mc3 (A + 35) _ HWB2 MU3 WM3).
      cbn [disjoint_from cells_size csize Nat.add]. split; [lia|]. split; [lia | exact I]. }
    clear HB2 HWB2 HOB2 MU2 WM2 RM2 MI2 SV2 HH2 F562 AC2 SW2 ST2 AOm2 WO2 HB3 MU3 WM3 MI3' ST3 RM3.
    (* the instrumented check of o + 20 and the flag byte *)
    pose proof HB3' as HB3''. destruct HB3'' as (MU4 & WM4 & RM4 & MI4 & SV4 & (hh4 & HH4) & F564).
    unfold c56_W, Wf in MU4. cbn [app] in MU4. unfold SAVES in SV4.
    pose proof (AO1 Ho0 fr f spc j n w56 mc3 HK MU4) as AOm3.
    assert (RX20 : 0 <= o + 20 < 2^64) by lia.
    pose proof (CHK mc3 o 32 20 1 (o + 20) AOm3 ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 20) 8 eq_refl); lia) eq_refl) as SH20.
    step. step. nf.
    step.
    chk_core (o + 20) RX20 (Z_to_bv 5 12) SH20 pre_sr no_extra.
    step. step. step.
    step. nf.
    (* asan_memcpy (o + 21, A + 35, 10) *)
    step. step. step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with HH : rw_cells rsegs mm o ?cs |- _ =>
        pose proof (rs_rw_take rsegs mm o cs 3 HH) as HOB4 end end.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HOB4.
    eapply (CMC 21 35 10 0x86adc fr f spc j n w56 _ (upd_bytes WB 0 (nmr row nb)) _);
      [exact Hp0 | exact Ho0 | apply ret_pc_even; [lia | reflexivity]
      | lia | lia | lia | lia | lia | lia | exact HK | | | exact HOB4 |].
    { split; [unfold c56_W, Wf; exact MU4|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption]. }
    { exact HWB3. }
    intros mc5 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 HB5 HWB5 HOB5.
    (* the outer sum *)
    step. step. step. step.
    pose proof HOB5 as HOB5c. destruct HOB5c as [[Hwf5 _] _]. cbn [cells_wf cell_wf] in Hwf5.
    destruct Hwf5 as [LX5 _].
    match type of HOB5 with rw_cells _ _ _ [CB 32 ?X5] =>
      eapply (L5 31%nat 0%nat X5 _ fr f spc j n w56 _);
        [exact Hp0 | exact Ho0 | lia | lia | exact LX5 | | | | exact HK | exact HB5 | exact HOB5] end.
    - pose proof (zr_word (Z_to_bv 64 o)) as Ruo. unfold inr64 in Ruo.
      rewrite zb_lxor_ones by exact Ruo. rewrite (unsigned_lit o) by lia. rewrite unsigned_lit by lia. reflexivity.
    - rewrite Hb, mb_synth5. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
      unfold idf. f_equal.
      assert (ENM10 : firstn (Z.to_nat 10) (skipn (Z.to_nat (35 - 35)) (upd_bytes WB 0 (nmr row nb)))
                      = firstn 10 (nmr row nb)).
      { replace (Z.to_nat (35 - 35)) with 0%nat by reflexivity.
        replace (Z.to_nat 10) with 10%nat by reflexivity.
        rewrite c56_skip0. apply c56_fu0. rewrite LN. lia. }
      rewrite ENM10.
      rewrite mb_first_upd by first [reflexivity | rewrite length_firstn, LN; reflexivity].
      unfold idf31. f_equal.
      cbn [firstn skipn app upd_bytes zeros repeat dt1_bytes map length Nat.add Nat.sub Z.to_nat].
      mb_bytes.
    - rewrite Hb, mb_rc5. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
  Qed.
End c56F_S.
