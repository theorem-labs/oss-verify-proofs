(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxImg FxPlan FxLoop FxFrame FxDrv FxCall FxWork.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition XQ := lvar 30. Definition LEN := lvar 31.
Definition XA : lin := lscale 8 XQ. Definition XS : lin := ladd XQ (lconst SHB).
(* [comment removed for export] *)
Definition SLOT5 : lin := ladd (fsc AR5) (lscale 2048 P5).
Definition FLB5 : lin := ladd (fsc FL5) P5.
Definition SHSLOT5 : lin := ladd (fsh AR5) (lscale 256 P5).
Definition fks5_facts : list fact := [FRange P5 0 511; FMod (lsub H5 P5) 9 0].
(* [comment removed for export] *)
Definition slot5_shadow (zero : bool) : region :=
  if zero then track (RG SHSLOT5 (lconst 256) RW TEmpty) 0 (List.repeat (BK 0) 256) else RG SHSLOT5 (lconst 256) RW TEmpty.
(* [comment removed for export] *)
Definition fks5_lm : list region :=
  [ track (RGz (fsc 40) 8 RW TEmpty) 0 (bv8 H5);                               (* [comment removed for export] *)
    RG (fsc FL5) P5 RZ TEmpty;                                                 (* [comment removed for export] *)
    RG FLB5 (lconst 1) RZ TEmpty;                                              (* [comment removed for export] *)
    RG (ladd (fsc (FL5 + 1)) P5) (laddc (lscale (-1) P5) 511) RZ TEmpty;       (* [comment removed for export] *)
    RG SLOT5 (lconst 2048) RW TEmpty;                                          (* [comment removed for export] *)
    RG (laddc SHSLOT5 (-8)) (lconst 8) RT TEmpty;                              (* [comment removed for export] *)
    slot5_shadow false ].                                                      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_tsd_c : region := RG (lconst 0xe4620) (lconst 8) RT (put_bytes (put_bytes TEmpty 0 [BK 1]) 4 (bkn 4 0)).   (* [comment removed for export] *)
Definition rt_rgs_c : list region :=
  (* [comment removed for export] *)
  rt_tsd_c :: List.map (fun R => RG (rg_base R) (rg_size R) RT (rg_cont R)) (firstn 5 (skipn 1 rt_rgs) ++ [rt_tp0] ++ firstn 1 (skipn 7 rt_rgs)) ++
  [ track (RGz (laddc CTX 152) 8 RT TEmpty) 0 (bv8 THR);
    track (RGz (laddc THR 48) 16 RT TEmpty) 0 (bv8 TLSB ++ bv8 TLSE);
    track (RGz (laddc BLK 24) 8 RT TEmpty) 0 (bv8 BEG) ].
Definition sb_uar_c : region := RG (rg_base sb_uar) (rg_size sb_uar) RT (rg_cont sb_uar).
Definition fs_hdr_c : region := track (RGz (fsc 88) 9 RT TEmpty) 0 (bk8 20 ++ [BK 0]).
(* [comment removed for export] *)
Definition xsh_c : region := RG XS (lconst 63) RT (put_bytes TEmpty 0 (List.repeat (BK 0) 63)).
Definition pow5tabsh_c : region := RG (lconst (SHB + 0x4a68)) (lconst 32) RT (put_bytes TEmpty 0 (List.repeat (BK 0) 32)).

(* [comment removed for export] *)
Definition SM5_R0 : tree lin := rsets (regs_pat 31 TEmpty) [(1, RA); (2, SP); (4, lconst TPV)].
Definition SM5_RGS (post : bool) : list region :=
  [ RG SWB SWS RW TEmpty;                                                      (* [comment removed for export] *)
    track (RGz (fsc 40) 8 RW TEmpty) 0 (bv8 (if post then laddc H5 1 else H5));   (* [comment removed for export] *)
    RG (fsc FL5) P5 RZ TEmpty;                                                 (* [comment removed for export] *)
    track (RG FLB5 (lconst 1) RZ TEmpty) 0 (if post then [BK 1] else []);      (* [comment removed for export] *)
    RG (ladd (fsc (FL5 + 1)) P5) (laddc (lscale (-1) P5) 511) RZ TEmpty;       (* [comment removed for export] *)
    RG SLOT5 (lconst 2048) RW (if post then put_bytes (put_bytes TEmpty 24 (bv8 SP)) 2040 (bv8 FLB5) else TEmpty) ]  (* [comment removed for export] *)
  ++ [slot5_shadow post]                                                       (* [comment removed for export] *)
  ++ [fs_hdr_c; sb_uar_c] ++ rt_rgs_c ++ relro_rgs.                                  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition rt_out (need : Z) : list fact := List.flat_map (fun '(X, n) => [FRange (lsub X SP) 0 (2 ^ 64 - need - n)]) [(CTX, 160); (THR, 80); (BLK, 32)].
Definition SM5_F : list fact := FMod RA 1 0 :: fks5_facts ++ rt_facts ++ stack_facts 208 ++ rt_out 208.
Definition SM5_P0 : sst := SST 0x4af40 SM5_R0 (SM5_RGS false) SM5_F 200 RNone.
(* [comment removed for export] *)
Definition SM5_Q : sst := SST 0 (rset (regs_keep SM5_R0 31 200 TEmpty) (rk 10) SLOT5) (SM5_RGS true) SM5_F 240 RNone.
Definition SM5_QK : list positive := [rk 10].
Lemma SM5_wf : state_wf SM5_P0 = true /\ state_wf SM5_Q = true /\ shape_eqb (s_rgs SM5_P0) (s_rgs SM5_Q) = true.
Proof. vm_compute. repeat split. Qed.

(* [comment removed for export] *)
Definition LM_R0 : tree lin := rsets (regs_pat 31 TEmpty) [(10, XA); (11, lconst 0x25340); (12, lconst 5); (1, RA); (2, SP); (4, lconst TPV)].
Definition LM_RGS : list region :=
  [ RGz (laddc SP (-2528)) 2528 RW TEmpty;                                     (* [comment removed for export] *)
    RG XA (lconst 496) RW TEmpty;                                              (* [comment removed for export] *)
    track (RG (laddc XA 496) (lconst 2) RW TEmpty) 0 [BV LEN 0; BV LEN 1];     (* [comment removed for export] *)
    xsh_c;                                                                     (* [comment removed for export] *)
    RG (laddc XS (-8)) (lconst 8) RT TEmpty;                                   (* [comment removed for export] *)
    RG (laddc XS 63) (lconst 8) RT TEmpty;                                     (* [comment removed for export] *)
    RGz (lconst 0x10000) 0x2e000 RO TEmpty;                                    (* [comment removed for export] *)
    pow5tabsh_c ]                                                              (* [comment removed for export] *)
  ++ fks5_lm                                                                   (* [comment removed for export] *)
  ++ [fs_hdr_c; sb_uar_c] ++ rt_rgs_c ++ relro_rgs.                                  (* [comment removed for export] *)
Definition LM_F (c : Z) : list fact :=
  [ FMod SP 5 c; FRange (laddc SP (-2528)) KHI (KTOP - 2528); FMod RA 1 0;
    FRange LEN 0 56;
    FRange (lsub XA (fsc AR4)) 0 (2 ^ 20 - 632);                                (* [comment removed for export] *)
    FRange (lsub XS (fsh AR4)) 0 (2 ^ 17 - 63 - 16);                            (* [comment removed for export] *)
    FRange (lsub (laddc SP (-2528)) (laddc FS 0xb09000)) 0 KTOP ]               (* [comment removed for export] *)
  ++ fks5_facts ++ rt_facts
  ++ List.flat_map (fun '(X, n) => [FRange (lsub X SP) 0 (2 ^ 64 - 2528 - n)]) [(CTX, 160); (THR, 80); (BLK, 32)]
  (* [comment removed for export] *)
  ++ List.flat_map (fun '(X, n) => List.map (fun '(o, need) => FRange (lsub X (laddc SP (- o))) 0 (2 ^ 64 - need - n))
                                            [(224 + c, 208); (224 + c, 16); (224 + c, 2224); (304 + c, 2208)])
                   [(CTX, 160); (THR, 80); (BLK, 32)].
Definition LM_P0 (c : Z) : sst := SST 0x96b2c LM_R0 LM_RGS (LM_F c) 200 RNone.
Lemma LM_wf : state_wf (LM_P0 0) = true /\ state_wf (LM_P0 16) = true.
Proof. vm_compute. repeat split. Qed.

(* [comment removed for export] *)
Definition SF5_R0 : tree lin := rsets (regs_pat 31 TEmpty) [(1, RA); (2, SP); (4, lconst TPV); (10, SLOT5); (11, lconst 1184)].
Definition SF5_RGS (post : bool) : list region :=
  [ RG SWB SWS RW TEmpty;                                                      (* [comment removed for export] *)
    RG SLOT5 (lconst 2048) RW (if post then TEmpty else put_bytes TEmpty 2040 (bv8 FLB5));   (* [comment removed for export] *)
    track (RG FLB5 (lconst 1) RZ TEmpty) 0 (if post then [BK 0] else [BK 1]);  (* [comment removed for export] *)
    if post then track (RG SHSLOT5 (lconst 256) RW TEmpty) 0 (List.repeat (BK 245) 256) else RG SHSLOT5 (lconst 256) RW TEmpty;  (* [comment removed for export] *)
    RGz (lconst 0x10000) 0x2e000 RO TEmpty;                                    (* [comment removed for export] *)
    sb_uar_c ]                                                                   (* [comment removed for export] *)
  ++ rt_rgs_c ++ relro_rgs.                                                      (* [comment removed for export] *)
Definition SF5_F : list fact := FMod RA 1 0 :: fks5_facts ++ rt_facts ++ stack_facts 16 ++ rt_out 16.
Definition SF5_P0 : sst := SST 0x4b14c SF5_R0 (SF5_RGS false) SF5_F 200 RNone.
Definition SF5_Q : sst := SST 0 (regs_keep SF5_R0 31 200 TEmpty) (SF5_RGS true) SF5_F 240 RNone.
Lemma SF5_wf : state_wf SF5_P0 = true /\ state_wf SF5_Q = true /\ shape_eqb (s_rgs SF5_P0) (s_rgs SF5_Q) = true.
Proof. vm_compute. repeat split. Qed.

(* [comment removed for export] *)
Definition MCD := lvar 33. Definition MCN := lvar 34. Definition MCW := lvar 35. Definition MCS := lvar 36.
Definition x_facts : list fact :=
  [ FRange (lsub XA (fsc AR4)) 0 (2 ^ 20 - 632); FRange (lsub XS (fsh AR4)) 0 (2 ^ 17 - 63 - 16) ].
(* [comment removed for export] *)
Definition MCA_R0 : tree lin := rsets (regs_pat 31 TEmpty) [(1, RA); (2, SP); (4, lconst TPV); (10, MCD); (11, XA); (12, lscale 8 MCN)].
Definition MCA_RGS (post : bool) : list region :=
  [ RG SWB SWS RW TEmpty;                                                      (* [comment removed for export] *)
    RG MCD (lconst 496) RW TEmpty;                                             (* [comment removed for export] *)
    RG XA (lconst 496) RW TEmpty;                                              (* [comment removed for export] *)
    RG MCW (lconst 8) RT TEmpty;                                               (* [comment removed for export] *)
    track (RG (laddc MCW 8) (lconst 256) RW TEmpty) 4 (List.repeat (BK 0) 63); (* [comment removed for export] *)
    RG (laddc XS (-8)) (lconst 8) RT TEmpty; xsh_c; RG (laddc XS 63) (lconst 8) RT TEmpty;   (* [comment removed for export] *)
    sb_uar_c ]                                                                   (* [comment removed for export] *)
  ++ rt_rgs_c ++ relro_rgs.                                                      (* [comment removed for export] *)
Definition MCA_F : list fact :=
  [ FMod RA 1 0; FRange MCN 0 62; FMod MCD 3 0; FRange (lsub (lscale 8 (laddc MCW (12 - SHB))) MCD) 0 0;
    FRange (lsub MCD (fsc AR5)) 32 (2 ^ 20 - 2048 + 32); FRange (lsub (laddc MCW 8) (fsh AR5)) 0 (2 ^ 17 - 256) ] ++ x_facts ++ rt_facts ++ stack_facts 2224 ++ rt_out 2224.
Definition MCA_P0 : sst := SST 0x601b4 MCA_R0 (MCA_RGS false) MCA_F 200 RNone.
Definition MCA_Q : sst := SST 0 (rset (regs_keep MCA_R0 31 200 TEmpty) (rk 10) MCD) (MCA_RGS true) MCA_F 240 RNone.
(* [comment removed for export] *)
Definition MCB_R0 : tree lin := rsets (regs_pat 31 TEmpty) [(1, RA); (2, SP); (4, lconst TPV); (10, MCD); (11, MCS); (12, lscale 8 MCN)].
Definition MCB_RGS (post : bool) : list region :=
  [ RG SWB SWS RW TEmpty;                                                      (* [comment removed for export] *)
    RG MCD (lconst 496) RW TEmpty;                                             (* [comment removed for export] *)
    RG MCS (lconst 496) RW TEmpty;                                             (* [comment removed for export] *)
    RG MCW (lconst 8) RT TEmpty;                                               (* [comment removed for export] *)
    track (track (RG (laddc MCW 8) (lconst 256) RW TEmpty) 4 (List.repeat (BK 0) 63)) 76 (List.repeat (BK 0) 63);  (* [comment removed for export] *)
    sb_uar_c ]                                                                   (* [comment removed for export] *)
  ++ rt_rgs_c ++ relro_rgs.                                                      (* [comment removed for export] *)
Definition MCB_F : list fact :=
  [ FMod RA 1 0; FRange MCN 0 62; FMod MCS 3 0; FRange (lsub (lscale 8 (laddc MCW (12 - SHB))) MCS) 0 0; FRange (lsub MCD MCS) 576 576;
    FRange (lsub MCS (fsc AR5)) 32 (2 ^ 20 - 2048 + 32); FRange (lsub (laddc MCW 8) (fsh AR5)) 0 (2 ^ 17 - 256) ] ++ rt_facts ++ stack_facts 2224 ++ rt_out 2224.
Definition MCB_P0 : sst := SST 0x601b4 MCB_R0 (MCB_RGS false) MCB_F 200 RNone.
Definition MCB_Q : sst := SST 0 (rset (regs_keep MCB_R0 31 200 TEmpty) (rk 10) MCD) (MCB_RGS true) MCB_F 240 RNone.
Definition MC_QK : list positive := [rk 10].
Lemma MC_wf : state_wf MCA_P0 = true /\ state_wf MCA_Q = true /\ state_wf MCB_P0 = true /\ state_wf MCB_Q = true.
Proof. vm_compute. repeat split. Qed.

(* [comment removed for export] *)
Definition MSD := lvar 37. Definition MSN := lvar 38.
Definition MSX_R0 : tree lin := rsets (regs_pat 31 TEmpty) [(1, RA); (2, SP); (4, lconst TPV); (10, MSD); (11, lconst 0); (12, lscale 8 MSN)].
Definition MSX_RGS : list region :=
  [ RG SWB SWS RW TEmpty;                                                      (* [comment removed for export] *)
    RG XA (lconst 496) RW TEmpty;                                              (* [comment removed for export] *)
    RG (laddc XS (-8)) (lconst 8) RT TEmpty; xsh_c; RG (laddc XS 63) (lconst 8) RT TEmpty;   (* [comment removed for export] *)
    sb_uar_c ]                                                                   (* [comment removed for export] *)
  ++ rt_rgs_c ++ relro_rgs.                                                      (* [comment removed for export] *)
Definition MSX_F : list fact :=
  [ FMod RA 1 0; FRange MSN 1 62; FMod MSD 3 0; FRange (lsub MSD XA) 0 488; FRange (lsub (laddc XA 496) (ladd MSD (lscale 8 MSN))) 0 488 ]
  ++ x_facts ++ rt_facts ++ stack_facts 2208 ++ rt_out 2208.
Definition MSX_P0 : sst := SST 0x60650 MSX_R0 MSX_RGS MSX_F 200 RNone.
Definition MSX_Q : sst := SST 0 (rset (regs_keep MSX_R0 31 200 TEmpty) (rk 10) MSD) MSX_RGS MSX_F 240 RNone.
Lemma MSX_wf : state_wf MSX_P0 = true /\ state_wf MSX_Q = true.
Proof. vm_compute. repeat split. Qed.

(* [comment removed for export] *)
Definition L0V := lvar 235.
Fixpoint fresh_pat (k : nat) (n : positive) (acc : tree lin) : tree lin :=
  match k with O => acc | S k' => fresh_pat k' n (tset (Pos.of_succ_nat k) (lvar (n + Pos.of_nat k)) acc) end.
Definition LM_S1 (c : Z) : lin := laddc SP (-224 - c).
(* [comment removed for export] *)
Definition LM_SAVED : list (Z * lin) :=
  [(2520, RA); (2512, lvar 108); (2504, lvar 109)] ++ List.map (fun k => (2528 - 32 - 8 * (Z.of_nat k), lvar (Pos.of_nat (118 + k)))) (seq 0 10).
Definition LM_STK (c : Z) : tree bval :=
  List.fold_left (fun t '(o, l) => put_bytes t o (bv8 l)) (LM_SAVED ++ [(2344 - c, SLOT5); (2352 - c, SLOT5)]) TEmpty.
Definition LM_RGS_T (c : Z) (limbs : rkind) (post : bool) : list region :=
  [ RG (laddc SP (-2528)) (lconst 2528) RW (if post then TEmpty else LM_STK c);   (* [comment removed for export] *)
    RG XA (lconst 496) limbs TEmpty;                                           (* [comment removed for export] *)
    track (RG (laddc XA 496) (lconst 2) RW TEmpty) 0 [BV L0V 0; BV L0V 1];     (* [comment removed for export] *)
    xsh_c;                                                                     (* [comment removed for export] *)
    RG (laddc XS (-8)) (lconst 8) RT TEmpty;                                   (* [comment removed for export] *)
    RG (laddc XS 63) (lconst 8) RT TEmpty;                                     (* [comment removed for export] *)
    RGz (lconst 0x10000) 0x2e000 RO TEmpty;                                    (* [comment removed for export] *)
    pow5tabsh_c;                                                               (* [comment removed for export] *)
    (if post then RGz (fsc 40) 8 RW TEmpty else track (RGz (fsc 40) 8 RW TEmpty) 0 (bv8 (laddc H5 1)));   (* [comment removed for export] *)
    RG (fsc FL5) P5 RZ TEmpty;                                                 (* [comment removed for export] *)
    (if post then RG FLB5 (lconst 1) RZ TEmpty else track (RG FLB5 (lconst 1) RZ TEmpty) 0 [BK 1]);   (* [comment removed for export] *)
    RG (ladd (fsc (FL5 + 1)) P5) (laddc (lscale (-1) P5) 511) RZ TEmpty;       (* [comment removed for export] *)
    RG SLOT5 (lconst 2048) RW (if post then TEmpty else put_bytes TEmpty 2040 (bv8 FLB5));   (* [comment removed for export] *)
    RG (laddc SHSLOT5 (-8)) (lconst 8) RT TEmpty;                              (* [comment removed for export] *)
    slot5_shadow false ]                                                       (* [comment removed for export] *)
  ++ [fs_hdr_c; sb_uar_c] ++ rt_rgs_c ++ relro_rgs.                                  (* [comment removed for export] *)
Definition LM_FQ (c : Z) : list fact := LM_F c ++ [FRange L0V 0 62; FRange (lsub L0V LEN) 0 6].
(* [comment removed for export] *)
Definition LM_FE (c : Z) : list fact := LM_F c ++ [FRange L0V 0 62].
Definition LM_TQ_R (c : Z) : tree lin :=
  rsets (fresh_pat 31 200 TEmpty) [(2, LM_S1 c); (3, lvar 103); (4, lconst TPV); (8, SP); (9, LM_S1 c); (19, SHSLOT5); (20, XA);
                                   (22, laddc XS 62); (23, laddc XA 496); (26, lconst SHB)].
Definition LM_TAIL_Q (c : Z) : sst := SST 0x973c8 (LM_TQ_R c) (LM_RGS_T c RW false) (LM_FQ c) 240 RNone.
(* [comment removed for export] *)
Definition LM_EPI_P0 (c : Z) : sst := SST 0x97540 (rset (LM_TQ_R c) (rk 21) (lconst 1)) (LM_RGS_T c RT false) (LM_FE c) 240 RNone.
(* [comment removed for export] *)
Definition LM_Q_R : tree lin := rset (regs_keep LM_R0 31 250 TEmpty) (rk 10) (lconst 1).
Definition LM_Q (c : Z) : sst := SST 0 LM_Q_R (LM_RGS_T c RT true) (LM_FE c) 290 RNone.
Lemma LMT_wf : state_wf (LM_TAIL_Q 0) = true /\ state_wf (LM_TAIL_Q 16) = true /\ state_wf (LM_EPI_P0 0) = true /\ state_wf (LM_EPI_P0 16) = true /\
  state_wf (LM_Q 0) = true /\ state_wf (LM_Q 16) = true.
Proof. vm_compute. repeat split. Qed.
