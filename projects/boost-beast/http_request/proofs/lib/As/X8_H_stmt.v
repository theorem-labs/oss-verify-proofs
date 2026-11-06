(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     X8Kit X8SRKit AXFuzz_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_HZ_A1      : Z := 0xa3a1c.   (* [comment removed for export] *)
Definition P_HZ_RET_MS1 : Z := 0xa3a2c.   (* [comment removed for export] *)
Definition P_HZ_RET_MS2 : Z := 0xa3a3c.   (* [comment removed for export] *)
Definition P_HZ_RET_NEW : Z := 0xa3a70.   (* [comment removed for export] *)
Definition P_HZ_RET_REG : Z := 0xa3aa4.   (* [comment removed for export] *)
Definition P_HZ_RET_MAK : Z := 0xa3ad0.   (* [comment removed for export] *)
Definition P_HZ_RET_SCH : Z := 0xa3aec.   (* [comment removed for export] *)
Definition P_HZ_RET_SCT : Z := 0xa3b04.   (* [comment removed for export] *)
Definition P_HZ_RET_CLR : Z := 0xa3b0c.   (* [comment removed for export] *)
Definition P_HZ_RET_SRO : Z := 0xa3d34.   (* [comment removed for export] *)
Definition P_HZ_RET_PDT : Z := 0xa3d3c.   (* [comment removed for export] *)
Definition P_HZ_RET_SDT : Z := 0xa3df8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition HZ_MAGIC : Z := 0x41b58ab3.    (* [comment removed for export] *)
Definition HZ_DESCR : Z := 0x219c2.       (* [comment removed for export] *)
Definition HZ_RETIRED : Z := 0x45e0360e.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition O_HZ_MAKER : Z := 32.  Definition O_HZ_EC : Z := 64.  Definition O_HZ_IOC : Z := 128.  Definition O_HZ_PARSER : Z := 192.
(* [comment removed for export] *)
Definition O_HZ_FFPARK : Z := 8.  Definition O_HZ_TMP : Z := 16.  Definition O_HZ_STREAM : Z := 16.  Definition O_HZ_FBUF : Z := 48.

(* [comment removed for export] *)
Definition hz_saved (s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition hz_sh0 : list cell :=
  [CB 4 (poison_bytes 4 0xf1); CB 2 (poison_bytes 2 0xf8); CB 2 (poison_bytes 2 0xf2); CB 3 (poison_bytes 3 0);
   CB 5 (poison_bytes 5 0xf2); CB 3 (poison_bytes 3 0xf8); CB 5 (poison_bytes 5 0xf2); CB 44 (poison_bytes 44 0xf8);
   CB 8 (poison_bytes 8 0xf3); CB 52 (poison_bytes 52 0)].


(* [comment removed for export] *)
Definition AVP_CFGMAKER : Z := 0x115bf0.

(* [comment removed for export] *)
Definition hz_sh1 : list cell :=
  [CB 4 (poison_bytes 4 0xf1); CB 2 (poison_bytes 2 0); CB 2 (poison_bytes 2 0xf2); CB 3 (poison_bytes 3 0);
   CB 5 (poison_bytes 5 0xf2); CB 3 (poison_bytes 3 0); CB 5 (poison_bytes 5 0xf2); CB 44 (poison_bytes 44 0xf8);
   CB 8 (poison_bytes 8 0xf3); CB 52 (poison_bytes 52 0)].

(* [comment removed for export] *)
Definition hz_sh2 : list cell :=
  [CB 4 (poison_bytes 4 0xf1); CB 2 (poison_bytes 2 0xf8); CB 2 (poison_bytes 2 0xf2); CB 3 (poison_bytes 3 0);
   CB 5 (poison_bytes 5 0xf2); CB 3 (poison_bytes 3 0); CB 5 (poison_bytes 5 0xf2); CB 44 (poison_bytes 44 0xf8);
   CB 8 (poison_bytes 8 0xf3); CB 52 (poison_bytes 52 0)].

(* [comment removed for export] *)
Definition hz_frm (mk : list cell) (j16 : list byte) (ec : list cell) (j40 : list byte) (ioc : list cell) (j40b : list byte)
    (pr : list cell) (j480 : list byte) : list cell :=
  mk ++ [CB 16 j16] ++ ec ++ [CB 40 j40] ++ ioc ++ [CB 40 j40b] ++ pr ++ [CB 480 j480].

(* [comment removed for export] *)
Definition hz_hdr (spa : Z) : list cell := [C8 (Z_to_bv 64 HZ_MAGIC); C8 (Z_to_bv 64 HZ_DESCR); C8 (Z_to_bv 64 P_AFUZZ_ENTRY); C8 (Z_to_bv 64 spa)].

(* [comment removed for export] *)
Definition hz_A1_W (lo spa ff : Z) : list (Z * Z) :=
  [(lo, spa); (spa + 48, spa + 96); (ff + 32, ff + 48); (ff + 64, ff + 88);
   (Z.shiftr ff 3 + 2147450880 + 4, Z.shiftr ff 3 + 2147450880 + 6); (Z.shiftr ff 3 + 2147450880 + 16, Z.shiftr ff 3 + 2147450880 + 19)]%Z.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition fr4_XS (ff fp : Z) : list (Z * Z) := [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 1024); (sh ff, sh ff + 128)]%Z.

  Lemma fr4_XS_scratch : asan_rt_hyps H -> forall LF ff fp, fresh_frame H LF 4 ff fp -> Forall (fs_scratch H LF) (fr4_XS ff fp).
  Proof.
    intros HH LF ff fp FF. pose proof (fs_scratch_of_fresh H _ _ _ _ FF) as FX. unfold fr4_XS.
    rewrite fsz_4, fshn_4 in FX. exact FX.
  Qed.

End HCW.
