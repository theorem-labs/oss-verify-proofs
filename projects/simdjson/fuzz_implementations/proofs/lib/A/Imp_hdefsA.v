(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit
     Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_pid1A Atp_pidiA Pj_defsA Pj_hdefsA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Export Imp_hdefs0A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition IMP_LFTOI_A : Z := 0xb4bd8.
Definition IMP_SM5_A : Z := 0x6a9b4.
Definition IMP_SMRET_A : Z := 0xb4c4c.
Definition IMP_SSF8_A : Z := 0x881fc.
Definition IMP_SS00_A : Z := 0x880dc.
Definition IMP_BODY_A : Z := 0xb4e44.
Definition IMP_CTORS_A : Z := 0xb4eac.
Definition IMP_AMEMCPY_A : Z := 0x8456c.
Definition IMP_COPY_A : Z := 0xb4f34.
Definition IMP_LOOP_A : Z := 0xb4fb8.
Definition IMP_GETACT_A : Z := 0xbf768.
Definition IMP_GETACT_RET_A : Z := 0xb4fc8.
Definition IMP_PARSE_A : Z := 0xb6c30.
Definition IMP_PARSE_RET_A : Z := 0xb5000.
Definition IMP_OKARM_A : Z := 0xb501c.
Definition IMP_OKARM_END_A : Z := 0xb5320.
Definition IMP_AFTER_A : Z := 0xb532c.
Definition IMP_DTORS_A : Z := 0xb53fc.
Definition IMP_PDTOR_A : Z := 0xb6abc.
Definition IMP_EXIT_A : Z := 0xb543c.
Definition IMP_SF5_A : Z := 0x6abc0.
Definition IMP_FIRST_A : Z := 0xb54b8.
Definition IMP_ATCXA_A : Z := 0x6fd24.
Definition IMP_OSS_CTOR_A : Z := 0xb56ac.
Definition IMP_APPEND_A : Z := 0xb7434.
Definition IMP_PUT_A : Z := 0xbc7d8.
Definition IMP_STR_A : Z := 0x113564.
Definition IMP_LOC_DTOR_A : Z := 0x1390dc.
Definition IMP_BO_DTOR_A : Z := 0x112dc4.
Definition IMP_IOS_DTOR_A : Z := 0x112960.
Definition IMP_GOT_VTT_A : Z := 0x172dd0.
Definition IMP_HDR_DESC_A : Z := 0x18fda.
Definition IMP_MAGIC0 : Z := 0x41b58ab3.
Definition IMP_MAGIC1 : Z := 0x45e0360e.
Definition IMP_FAKE_A : Z := 1248.

Definition IMP_SB_OFF : Z := 32.
Definition IMP_IMPLS_OFF : Z := 160.
Definition IMP_DOC_OFF : Z := 192.
Definition IMP_ELEM_OFF : Z := 248.
Definition IMP_OUT_OFF : Z := 272.
Definition IMP_OSS_OFF : Z := 832.
Definition IMP_TMP_OFF : Z := 1168.
Definition IMP_SRET_OFF : Z := 192.

Definition imp_savedA (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma imp_savedA_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11, cells_size (imp_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. intros. reflexivity. Qed.

Definition imp_locals (F S1sh szw dw : Z) : list cell :=
  [C8 (Z_to_bv 64 (F + 832 + 112)); C8 (Z_to_bv 64 (F + 832 + 16)); C8 (Z_to_bv 64 (F + 832 + 8)); C8 (Z_to_bv 64 (S1sh + 12));
   C8 (Z_to_bv 64 szw); C8 (Z_to_bv 64 (F + 32)); C8 (Z_to_bv 64 dw); C8 (Z_to_bv 64 (F + 1168)); C8 (Z_to_bv 64 (F + 160))].
Lemma imp_locals_size : forall F sh szw dw, cells_size (imp_locals F sh szw dw) = 72%nat.
Proof. intros. reflexivity. Qed.

Definition out_shortA (b0 : byte) (j23 : list byte) : list cell := [C1 b0; CB 23 j23].
Definition out_longA (SZ L DATA : Z) : list cell := [C8 (Z_to_bv 64 (SZ + 1)); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 DATA)].

Definition imp_outA (m : mem) (F : Z) (ocp : option (Z * Z)) : Prop :=
  match ocp with
  | None => exists (b0 : byte) j23, rw_cells asegs m (F + 272) (out_shortA b0 j23) /\ Z.land (bv_unsigned b0) 1 = 0
  | Some (DATA, SZ) => exists L, rw_cells asegs m (F + 272) (out_longA SZ L DATA) /\ Z.land (SZ + 1) 1 = 1 /\ 0 < SZ < 2^32 /\ 0 < DATA /\ DATA mod 16 = 0 /\ 0 <= L <= SZ
  end.
Definition ocp_chunks (ocp : option (Z * Z)) : list (Z * Z) := match ocp with Some c => [c] | None => [] end.

Definition imp_sh (sb os tmp : Z) : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 sb) 11 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 0) 68 ++ repeat (Z_to_bv 8 (-14)) 16
  ++ repeat (Z_to_bv 8 os) 33 ++ repeat (Z_to_bv 8 (-14)) 9 ++ repeat (Z_to_bv 8 tmp) 3 ++ repeat (Z_to_bv 8 (-13)) 7.
Definition imp_sh_pro : list byte := imp_sh (-8) (-8) (-8).
Lemma imp_sh_length : forall a b c, length (imp_sh a b c) = 156%nat.
Proof. intros. reflexivity. Qed.

Definition imp_regsA (pc : Z) (ra : word) (S1 : Z) (gp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (F : Z) (s4 s5 s7 s10 s11 : word)
    (t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 S1) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad F)) s4 s5 (Z_to_bv 64 (F + 160)) s7 (Z_to_bv 64 SHB) (Z_to_bv 64 (F + 832)) s10 s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 pc) fc None m (seg_rom asegs).
