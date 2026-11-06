(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.hashtable.images Require Import Plain.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  StartupTac H0_code_26b000_26c000 H0_code_277000_278000 H0_code_27a000_27b000 H0_code_dd000_de000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
  rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof. intros; subst; reflexivity. Qed.

(* [comment removed for export] *)
Definition direrr_kept : list reg := [3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

(* [comment removed for export] *)
Lemma direrr_walk : forall regs mem rom (sp0 s0v : word),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  getr regs 1 = Z_to_bv 64 0x27ab74 ->
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 144) ->
  getr regs 4 = Z_to_bv 64 0x2ebf58 ->
  getr regs 8 = s0v ->
  getr regs 10 = errno_ret EISDIR ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd1a0)) ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = true ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 144)) 8 = true ->
  store_ok RSEGS mem (Z_to_bv 64 0x2ebeb4) 4 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x277638 : word) mem rom)
                 (mkst regs' (0xdd2f4 : word)
                    (wbytes (wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0xdd1a0)))
                                    (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 s0v))
                            (Z_to_bv 64 0x2ebeb4) (word_to_le_bytes 4 (Z_to_bv 64 21))) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 18446744073709551615
    /\ (forall r, In r direrr_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 s0v Hsp H1 H2 H4 H8 H10 Hra SOK136 SOK144 SOKerr.
  pose proof (u64_range sp0) as Hsp'.
  assert (H10' : getr regs 10 = Z_to_bv 64 18446744073709551595) by (rewrite H10; apply bv_eq; reflexivity). clear H10.
  eexists. split.
  - stepret F_2775f4 D_2775f4 (0x27ab74 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
    ld_step F_27ab30 D_27ab30 (word_to_le_bytes 8 (Z_to_bv 64 0xdd1a0)) (Z_to_bv 64 0xdd1a0)
      ltac:(eapply rdn_addr; [exact Hra | f_equal; lia]) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    sv F_27ab34 D_27ab34 (Z_to_bv 64 (bv_unsigned sp0 - 128)).  (* [comment removed for export] *)
    sn F_27ab38 D_27ab38.  (* [comment removed for export] *)
    sn F_26bd58 D_26bd58.  (* [comment removed for export] *)
    sn F_26bd5c D_26bd5c.  (* [comment removed for export] *)
    stepb_ft F_26bd60 D_26bd60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sv F_26bd64 D_26bd64 (Z_to_bv 64 (bv_unsigned sp0 - 144)).  (* [comment removed for export] *)
    stw F_26bd68 D_26bd68 (Z_to_bv 64 (bv_unsigned sp0 - 136)) (Z_to_bv 64 0xdd1a0) ltac:(store_ok_peel; exact SOK136).  (* [comment removed for export] *)
    stw F_26bd6c D_26bd6c (Z_to_bv 64 (bv_unsigned sp0 - 144)) s0v ltac:(store_ok_peel; exact SOK144).  (* [comment removed for export] *)
    sn F_26bd70 D_26bd70.  (* [comment removed for export] *)
    sn F_26bd74 D_26bd74.  (* [comment removed for export] *)
    sn F_26b960 D_26b960.  (* [comment removed for export] *)
    sn F_26b964 D_26b964.  (* [comment removed for export] *)
    stepret F_26b968 D_26b968 (0x26bdbc : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
    stw F_26bd78 D_26bd78 (Z_to_bv 64 0x2ebeb4) (Z_to_bv 64 21) ltac:(store_ok_peel; exact SOKerr).  (* [comment removed for export] *)
    sn F_26bd7c D_26bd7c.  (* [comment removed for export] *)
    ld_step F_26bd80 D_26bd80 (word_to_le_bytes 8 (Z_to_bv 64 0xdd1a0)) (Z_to_bv 64 0xdd1a0) ltac:(rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    ld_step F_26bd84 D_26bd84 (word_to_le_bytes 8 s0v) s0v ltac:(rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
    sv F_26bd88 D_26bd88 (Z_to_bv 64 (bv_unsigned sp0 - 128)).  (* [comment removed for export] *)
    stepret F_26bd8c D_26bd8c (0xdd1a0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
    stepb_tk F_dd150 D_dd150 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    apply mst_refl.
  - split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr; cbv [direrr_kept In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; exact H8 | symmetry; exact H4] |]); destruct Hr.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
