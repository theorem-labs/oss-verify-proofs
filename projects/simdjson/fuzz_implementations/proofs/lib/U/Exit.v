(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Imp_ios_defs.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation usegs := Image.usegs.

Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells usegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells usegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells usegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x115d28 0 2 mode 0xffffffff tail).

Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0xe3220); (RSTDOUT_BUF, 0x116538)]%Z m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = []
      /\ stderr_file m'
      /\ rw_cells usegs m' 0xe1b58 [C8 (Z_to_bv 64 0x1157b8)] /\ rw_cells usegs m' 0x1157b8 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk usegs m lo (bv_unsigned sp) ->
      rw_cells usegs m 0x1157d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      rw_cells usegs m 0x115d18 [C8 z64] ->
      rw_cells usegs m 0xe3130 [C8 z64] ->
      rw_cells usegs m 0xe3220 [C8 (Z_to_bv 64 RSTDOUT)] ->
      rw_cells usegs m 0xe3040 [C8 (Z_to_bv 64 RSTDERR)] ->
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells usegs m 0xe1b58 [C8 (Z_to_bv 64 0x1157b8)] -> rw_cells usegs m 0x1157b8 [C8 guard] ->
      mem_inv usegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x117000 <= lo)%Z ->
      implM usegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xca408) fc None m (seg_rom usegs)).
End StdioExitStatement.

Definition RAEX_CALL : Z := 0xc4c94.
Definition RAEF_GUARD : Z := 0x3ebb4.
Definition AEX : Z := 0x115590.
Definition X_IOSDTOR : Z := 0x86ec8.
Definition X_VECDTOR : Z := 0x3ee38.
Definition AEX_IOS : Z := 0xf35e8.
Definition AEX_VEC_OBJ : Z := 0xf32d8.
Definition RLATCH : Z := 0xf32a0.
Definition RINCB : Z := 0xf32a4.

Definition aex_tbl (m : word -> option byte) (n : Z) : Prop :=
  rw_cells usegs m AEX [C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m (AEX + 4) [C4 z64; C4 (Z_to_bv 64 n)]
  /\ rw_cells usegs m (AEX + 16) [C8 (Z_to_bv 64 (AEX + 24)); C8 z64;
                                   C8 (Z_to_bv 64 X_IOSDTOR);
                                   C8 (Z_to_bv 64 (if (n <=? 1)%Z then 0 else RAEX_CALL));
                                   C8 (Z_to_bv 64 (if (n <=? 2)%Z then 0 else X_VECDTOR))]
  /\ rw_cells usegs m (AEX + 288) [C8 (Z_to_bv 64 AEX_IOS);
                                   C8 (Z_to_bv 64 (if (n <=? 1)%Z then 0 else RAEF_GUARD));
                                   C8 (Z_to_bv 64 (if (n <=? 2)%Z then 0 else AEX_VEC_OBJ))].

Definition aex_cells (m : word -> option byte) (k : Z) : Prop :=
  aex_tbl m (1 + 2 * k)
  /\ rw_cells usegs m RLATCH [C1 (Z_to_bv 8 k)]
  /\ rw_cells usegs m RINCB [C1 (Z_to_bv 8 0)].
Definition aex_inv (m : word -> option byte) : Prop := exists k, (0 <= k <= 1)%Z /\ aex_cells m k.

Definition aex_mid (m : word -> option byte) : Prop :=
  aex_tbl m 2 /\ rw_cells usegs m RLATCH [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m RINCB [C1 (Z_to_bv 8 1)].

Definition aex_tbl_addr (a : Z) : Prop := (AEX <= a < AEX + 312)%Z.

Lemma aex_tbl_agree : forall P m m' n, agree_on' P m m' -> (forall a, aex_tbl_addr a -> P a) -> aex_tbl m n -> aex_tbl m' n.
Proof.
  intros P m m' n AG HP (X1 & X2 & X3 & X4). unfold aex_tbl_addr, AEX in HP.
  split; [eapply rw_cells_agree'; [exact AG| exact X1|]; intros a Ha; apply HP; cbn in Ha; unfold AEX in Ha; lia|].
  split; [eapply rw_cells_agree'; [exact AG| exact X2|]; intros a Ha; apply HP; cbn in Ha; unfold AEX in Ha; lia|].
  split; [eapply rw_cells_agree'; [exact AG| exact X3|]; intros a Ha; apply HP; cbn in Ha; unfold AEX in Ha; lia|].
  eapply rw_cells_agree'; [exact AG| exact X4|]; intros a Ha; apply HP; cbn in Ha; unfold AEX in Ha; lia.
Qed.

Lemma aex_tbl_transport : forall W m m' n, aex_tbl m n -> munch W m m' -> wmono usegs m m' -> (forall a, aex_tbl_addr a -> outside W a) -> aex_tbl m' n.
Proof. intros W m m' n H MU WM HW. eapply aex_tbl_agree; [apply (agree_on'_of_munch W m m' MU WM)| exact HW| exact H]. Qed.

Ltac lock_ret := steps_to 0xd66c4%Z; lstep; change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word); lstep; if_true; lstep.

Ltac unlock_ret := lstep; replace (sx32 z64) with z64 by (vm_compute; reflexivity); lstep; if_false; lstep.

Lemma impl_msys_of_enode : forall segs {St A} (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
  impl segs (at_node segs) (enode n pl) (epost Q) ms ->
  impl segs (at_node segs) (Monad.msys n pl s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
  intros segs St A n pl Q s ms H. unfold Monad.msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.
