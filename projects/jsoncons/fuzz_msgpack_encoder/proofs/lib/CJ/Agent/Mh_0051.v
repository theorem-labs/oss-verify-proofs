(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes SysStep. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require RunP.
Module F_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes SysStep. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.SysStep.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition asegs := Plain.Plain_loaded_segments.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells asegs m' B [CB n junk]
                    /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (bs : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (n : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv]
    /\ bytes_at asegs m' B bs
    /\ n = Z.of_nat (length bs).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition close_ret (a : sret) : word :=
  match a with
  | SVal _ => Z_to_bv 64 0
  | SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
  end.
Definition close_errno (a : sret) (errv : word) : word :=
  match a with
  | SVal _ => errv
  | SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
  end.

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (close_errno a errv)].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at asegs m' P (path ++ [Z_to_bv 8 0])
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.
End CEIL_WRAP_1.

(* [comment removed for export] *)

End F_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes SysStep Decode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes SysStep Decode. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.SysStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Decode.
(* [comment removed for export] *)
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0051.F_syscalls.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac transport_zeros segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
      clear H
  end.

Ltac transport_unmaps segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
  | H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
  end.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_F_mm_syscalls () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2CJ3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z9land_specC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z9land_onesc79OSSVerify5KrLib2CJ5Agent7Mh_0051=F_mm_syscallsAland_ldiff_distr'C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC35stdpp7tactics<f_equal_helpK47Corelib4Init5Logic3and01C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState<unsigned_litC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ5Agent7Mh_0051=F_mm_syscalls:land_m4096C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Lemma mmap_len_ge : forall len, (len <= mmap_len len)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_F_mm_syscalls ()) ["CEIL_WRAP_1"] "h02H0h14__p1h24__x1h34__x2h44__x3h51Hh62H1h72H2h82H3h97__arithh:4__ffh;8__varmaph<5__with=3lenh>1qh?1rp;1p;2p;3p;4p;6p;7p;8g0000j18Tg000Uj1BTg0013j20Tg001Pj21Tg001mj2YTg002Nj33Tg002hj1STg003Aj2<Tg003^j2>Tg004;j25Tg004[j2ITg005Bj24Tg005^j22Tg006:j27Tg006Uj2_Tg007<j2XTg007bj2WTg008Hj2VTg008ij2ETg009Cj1DTg009bj2?Tg00:Kj3CTg00;4j2RTg00;`j1QTg00<@j3PTg00<`j1OTg00=@j2ATg00=^j4NTg00><j1MTg00>Zj1LTg00?Ej6KTg00?ij1JTg00@Nj2=Tg00A1j2;Tg00ATj49Tg00B?j7HTg00Bcj1TTg00CEj6UTg00Cij3GTg00DLj3bTg00Doj3FTg00ERj2aTg00F4j2`Tg00F`j3^Tg00G?j4ZTg00H1j1[Tg00Hlj7\Tg00IPj8]Tf0R0#8#8p=6f1R1g00J4R2g00JSR3P3g00K3R4P0g00KSF\p=:f3R5P2P3P3P4f2R6P1P0G]p=@g00L3R7g00LQR8#8R9#8#6#6#6#6#6#BR:,00%B8R;'1/Y:g00M6R<937:R=#S101:/1;R>1<>:,>:15>:'0537[1I>:14<:R>106:/1;R?/5:R@,2<14@:'7[1_?:14:<105:/1;R@/5:RA,4:12A<'7[1X@:f4R@/0:/1;RA/<:=37<\=1WA:f5RA/0:/1;RB/5:=37B\=1<B:P7f6/0:/1;/5:P7PAg00MT1V<:'EP>eO112<0140:'7p-0R>g00N:RBg00NfRC#DRD#D,?71?7D1?7C5C75C7g00OE'R%QB3P%OBP71A76P11A75CN%M7%L7RBPBP2P3P3P4PBP2P3P3P4PAEKP7%J8,=7RAg00P11;7:RCC9,:BFH%T3RDPBPBPBP2P3P3P4P7PCg00PXR31;7<C9,:BEUPDP71=78R8=G7C1;7;5b7P31=79R99F7C=G7AC9,:BC@PDP7P8g00Q?AF79CC9,:BC@C@1aB4P0P6g00QfRBg00RFR4'E1`06=3B4dA^7<1CZb:b;b<X27X37X47W1146:,75g00Rf\=1>:5/0@937?[1>5:,26[[^27^37^47^1>P012<6P6P5f9P1f8O6b9b0b?b>b8b7b6b0b5%[0,20eW=o"). Qed.
Lemma mmap_len_nonneg : forall len, (0 <= len)%Z -> (0 <= mmap_len len)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_F_mm_syscalls ()) ["CEIL_WRAP_1"] "h02H1h14__p1h24__x1h34__x2h44__x3h52H0h62H2h72H3h82H4h97__arithh:4__ffh;8__varmaph<5__with=3lenh>1qh?1rp;1p;2p;3p;4p;6p;7p;8g0000j1=Tg000Uj1DTg0013j20Tg001Pj21Tg001mj2XTg002Nj32Tg002hj1TTg003Aj2?Tg003^j2ATg004;j28Tg004[j2ITg005Bj23Tg006:j2<Tg006Uj2^Tg005^j2FTg007<j2ZTg007bj2YTg008Hj2WTg008ij2ETg009bj2:Tg00SCj2VTg00Slj3UTg009Cj19Tg00:Kj3BTg00;4j2STg00TUj2RTg00;`j1OTg00<@j3NTg00<`j1MTg00=@j2CTg00=^j4LTg00><j1KTg00>Zj1JTg00?Ej6PTg00?ij1QTg00@Nj2>Tg00A1j2@Tg00ATj45Tg00B?j7fTg00Bcj1eTg00CEj6dTg00Cij3HTg00DLj3cTg00Doj3GTg00ERj2]Tg00F4j2\Tg00F`j3[Tg00G?j4_Tg00H1j1`Tg00Hlj7aTg00IPj8bTg00M6R0f0R1'Fp=4%=1#=p=6f1R2g00J4R3g00JSR4P4g00K3R5P1g00KSFap=7f3R6P3P4P4P5f2R7P2P1Gbp=;g00L3R8%41R9g00LQR:#=R;#=#6#6#6#6#6#DR<,02%D:R='1/X<A28<0R>#T107</1=R?1??<,A<18?<'0528[1I?<130<R?106</1=R@/8<RA#413A<'<[1^@<13<0f4RA/0</1=RB/8<RC,3<1FC0'<[1ZB<f5RB/0</1=RC/?<=280\>1YC<f6/0</1=RC/8<=28C\>1?C<P8f7/0</1=/8<P8PBg00MT1W0<'EP?eO1131<,<9p-0R9g00N:R?g00NfRC,:8RD1V8<=U8D%9C#9RC#9RD#9,:81:8D1:8C5B85B85B8g00OE'S'R%O?3N%M?P81C87P21C86CL%K8%J8R?P?P3P4P4P5P?P3P4P4P5PBEPP8%Q:,>8RBg00P11@8<RCC5,7?Ff%e4RDP?P?P?P3P4P4P5P8PCg00PXR41@80R3C5,7?EdPDP81>8;R;=H8C1@8=5c8P41>8:R:9G8C=H8BC5,7?C;PDP?P8P3g00Q?RBP;C5,7?PDP8P3PBAG8:CC5,7?C;C;C;1]?5P1P7g00QfR?g00RFR5'E1\17=2?5dA[802C_b:b;b<X28X38X48W1137<,<6g00Rf\>1A<7/0A928@[%461A6<#4[[[^28^38^48^19P1%47P7f:P6P2f8f9O7b9b0b?b>b8b7b6b0b5%`2#4eUW=o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_ret (a : range_ans) : word :=
  match a with RgErr _ => Z_to_bv 64 (-1) | RgDone _ => Z_to_bv 64 0 end.
Definition rg_errno (a : range_ans) (errv : word) : word :=
  match a with RgErr e => Z_to_bv 64 e | RgDone _ => errv end.

(* [comment removed for export] *)
Definition munmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono asegs m m' end)
    /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_aligned : forall len, (len mod 4096 = 0)%Z -> mmap_len len = len.
Proof.
ltac2:(KReplay.run1 (kr_t_F_mm_syscalls ()) ["CEIL_WRAP_1"] "h02H1h12H6h24__x1h34__x2h44__x3h54__x4h64__x5h72H0h82H2h92H3h:2H4h;2H5h<2H7h=2H8h>2H9h?7__arithh@4__ffhA8__varmaphB5__withC3lenhD1qhE2q0hF1rhG2r0p;1p;2p;3p;4p;6p;7p;8g0000j1CTg000Uj1OTg004;j22Tg0013j21Tg001Pj27Tg001mj2QTg002hj1`Tg003Aj29Tg003^j2=Tg004[j2KTg005Bj23Tg005^j28Tg006:j26Tg006Uj2UTg007<j2TTg007bj2RTg008Hj2cTg008ij2STg009Cj1:Tg009bj2PTg00SCj2_Tg00Slj3^Tg00UAj1]Tg00U_j2\Tg00V@j3>Tg00;4j2NTg00TUj2DTg00;`j1[Tg00<@j3MTg00<`j1ZTg00=@j2LTg00Vij1YTg00=^j4FTg00><j1XTg00>Zj1WTg00A1j2JTg00CEj6mTg00Bcj1lTg00@Nj2?Tg00?ij1VTg00Doj3ITg00Cij3ETg00ATj4HTg00B?j7kTg00DLj3jTg00ERj2iTg00F4j2hTg002Nj3GTg00F`j3dTg00G?j4eTg00H1j1bTg00:Kj3fTg00Hlj7gTg00IPj8aTf0R0#C#Cp=Ag00L3R1g00M6R27G0p=@f1R3=G10p=41P10p=;Af130p=0P1P3g00PXP0CHp=BP3g00J4R4g00JSR5P5g00K3R6P0g00KSFgp=5f3R7P4P5P5P6f2R8P3P0Gap=<g00LQR9#CR:#CR;#A#A#A#A#A#OR<,20#@113<%O9R='7/Q<%@<R>#`R?118</7=R@19@<,=<12@<'1'4[1K@<132<R@117</7=RA/2<RB,8213B<'6[1UA<13<2RAf4RB/1</7=RC/2<RD,3<18D2'6[1TC<f5RD/1</7=RE/9<#@\>1RE<f6RE/1</7=RF/2</4F\>19F<P1f7/1</7=/2<P1f8RF/Q<f9RG19G<,=<12G<'1'4\?1KG<f:R?/2<RH,8213H<'6\@1U?<f;RH/2<RI,3<18I2'6\A1TH<f<RA/9<#@\>1RA<f=RA/2</4A\>19A<P1f>/2<P1PDg00MT1c2<'SP@eR@O11820130<'6PAP@O1182F13F<'6g00N:RFg00NfR@#:RA#:RI#:RJ#:RK#:RL#;RM%;ARA1P1@R@'0RN'01_1<=^1@%]9,\1RO%:L#;RL5>1%;K%;JRJ%;IRI9>1O'0'0'0'0g00OERK'N'DA>1OMA>1OA/0@'0A>1OJ/0I,0M,0L1NNK'D'D%[F5MF3M%ZFP1P11L1BP8%Y1RFCFP3P11L1DP7PFCFCF%X1%W1RFPFPFP4P5P5P61J1<RK1J12RN'B,5FEmRL%l5RM1?1:RI%V:,?19I1K%V9,?1R:5E1'B,5FC<PMPFPFP4P5P5P6P1PNg00Q?1?1;R;CH,5FP1P;g00P1PKCH,5FFkPMPFPFPLPMAE1IK1J1=5j11?19R99I1K=E1;'B,5FC<PMPF1B:N,5FPMAI19K/BI,5FC<C<C<C<1iF6P0P8g00QfRFg00RFR6'S1h08=GF6dAd123Ceb@bAbBX21X31X41X51X61g00Rf\>R>1=<D/17,48[182B13B<'61=<7/1E,4C\>%@D1=B</4D[[[[^21^31^41^51^61P0PBP?P7fBPHPGP3f@fAO9b?b0b1bGbEb>b=b<b1b;bFbDb:b9b8b0b7%b3/43eUXC1o"). Qed.

Lemma land_ldiff_distr' x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof.
ltac2:(KReplay.run1 (kr_t_F_mm_syscalls ()) ["CEIL_WRAP_1"] "p'0h02b0h11bi001bh21ah31xh42Hnh51np;2p;1p;3p;6g00WGj25Tg00Wfj26Tg005^j2=Tg00XDj21Tg00Xej20Tg00YCj14Tg00Yaj39Tg00ZDj67Tg00Zbj3:Tg00[Fj3?Tg002Nj38Tg008ij2>Tg00QfR0f1R1f0R238p=;f2R3/01=802p=210129803p=<1012,>0p=3g00L3R41512,631631/52g00M6/=2P0f4R5/11R6f3R7/53R8/11R9'0f5R:/65/57/13R;,;2X10P01171R<1131#4R='011:3R>?22;X10P01657R;/11R?/0=1153R=1173#4R@'0,0>R>/;2X10P0106<A<>2@X10P6P0P011:7R61157R>#4R@'01026/0@522P2P=P0P0g00RFR@11:5#4R:,02R610@2/0:32P2P>P0P0%42R<,0@RA10@@RB/0<52@P2%4@RC,3Bg00[iRD#4RE,3Bn0110000020000b0P>P0P010D<RB10@DRF/0<52@P213FC13FEn0110000020000b0n0110000020000b0P=P0P010D2/0:92D6P2P>P0P010D@R@/0<92DAP213@C13@En0110000020000b0P>P0P010DDR0/0<92DBP2130C130En0110000020000b0n0110000020000b0n0110000020000b0P?A9571E715;3/11A:;31E7P9A:731E71658/11A9581E7W4X543?X14X24X34P3P1P2O3X14X24W3o"). Qed.

Lemma land_m4096 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x - x mod 4096)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_F_mm_syscalls ()) ["CEIL_WRAP_1"] "h06__sat1h16__sat0h27__arithh34__ffh48__varmaph55__with64__x1h71zh81Hh92H0h:2Hah;4__p1h<4__x2h=4__x3h>1ah?1xh@1EhA2H1hB2H2hC2H3hD2H4hE2HxhF6__sat2hG6__sat3hH2zhp&0p;1p;2p;3p;4p;6p;7p;8g0000j15Tg000Uj1=Tg00\Ij2STg005Bj23Tg006:j2:Tg00\fj1QTg00?ij11Tg00WGj2@Tg008ij2CTg00Wfj2ITg004;j24Tg001Pj2GTg00]Dj2pTg00]dj2kTg003^j27Tg003Aj28Tg001mj2OTg002Nj3?Tg002hj1cTg0013j2JTg00^Dj2`Tg00_5j2_Tg00_fj2^Tg00`Nj3]Tg004[j2\Tg006Uj2[Tg005^j2MTg007<j2ZTg007bj2YTg00a2j2XTg008Hj2LTg00UAj1VTg00U_j2UTg009Cj1KTg009bj2TTg00V@k303Tg00:Kk302Tg00;4k201Tg00;`k100Tg00<@j3~Tg00<`j1xTg00=@j2DTg00=^j4wTg00><j1sTg00>Zj1rTg00A1j2>Tg00CEj6qTg00Bcj1oTg00@Nj2HTg00Doj3RTg00Cij3jTg00?Ej6iTg00DLj3lTg00ERj2hTg00F4j2mTg00F`j3nTg00G?j4gTg00Vij1fTg00b1j3eTg00bZj3dTg00cCj3tTg00cij1uTg00dGj3vTg00ATj4ETg00djj3bTg00eMj3aTg00f0j3yTg00Hlj7zTg00IPj8{Tg00B?j7|Tg00ZDj6}Tg00M6R0f0R1'Mp=0%51#5#5#5p=<%51#5p=N%11#1p=W%11#1#1#1#1#1#1#1p=;g00L3R2f1R3;?1p=2P2P3g00PXP1CEp=FP3g00J4R4g00JSR5P5g00K3R6P1g00KSFzp=6f3R7P4P5P5P6f2R8P3P1G{p=BP2P3g00Q?P1CEp=AP8P4P5P5P6P3P1F|p=PP2f4R9P7P8P3P1E}p=9%01g00LQR:#5R;#=R<%5;#<R=#=R>'SR?,31':R@%Q>RA%1:RB#N#=RC#QRD'@RE,C2%WB#;#;#;#;#;#;#<#<#<#=RF/2EPE1I71%N=#<#=RG,47RH,G7RI'2X721I8ARJ/@D121IX72RK148?RL1@1D/2IX72RMP8PM1p8CRM/kCRNPK1S<CRO,7MPK188O171O/2IX721O8GA?2G0RI#cRO187G,7G/JH,27[1`7G%07%0GRHf5RK/4G#0[[1_9G%09f6RP/8G#0\H[1^<>RH130<RQ%0>RR130?[RS[RT%0<RUg00gERVA]<>3UW:RW%0?RX\V^:URYf7/OGf8RZ18ZG,7G14ZG'J'2\O1\ZG130GRZf9RO/4GR[#013[G':[1[OG13G0f:R[/4GR\,3G1M\0':[1Z[Gf;R\/8G=?20\I1Y\Gf<R\/4G/2\\Ig00ga1X\GR\eP\P9g00MTR\1L0G'CPZeO1f=RZ/4GR]#013]G':P3PVPOP1P3O2X>UPX^>UP[1L0<,C\PQeRQO1PSp-0R\g00N:RU%V:,U2g00NfRX#K#K,T260321T2X6022g00OE+01&00URX3~%xURUP21D28P31D27Cw%s2RO%r2RVPVPVP4P5P5P61>2GR^1>20R_'F,6VEq%o5R`1H2;R;1H2:R:9R2^1H2BRB5j2'F,6VCBP`PV1A_;,6VPVP4P5P5P6PKEi5PVP`AR2:^Al2;B'F,6VCBCB1hV6R6P1P8g00QfRBg00RFR;'C1m18=?B;dAn203CgR0b3b4b5X62X<2X=2W;g00Rf\I17G3/J7,28[%08/:9178G1G79'2[[^62^<2^=2^;\P1fBR\/3?14\GP\18\GP[fAO6b2b0b1bHb918ZG/7G1GZ]'2ebDbCbBbAb9b8b1b0bFbGb8PMPHPTPWPYP3PQO1RQPSPXPU%f2R]PO1>2C,A_,6VP6P0b3b4b5%0CP1b2b0b1b0RZ9e8CD9PNAdMCZD91@8DAt8CZD9PLPHPTPWPYPQPSPXPU1D23POPV1A_:,6VP2P:g00P11>2<%u=5v2CE,6V5PVR=P`P=CBP6P0b3b4b5X62%03133?':\@^62P1PPPKO2b2b0b1b09b8?D9PJPHPTPWPYPQPSPXPUP]PO1>2>,A_,6VP6P0b3b4b5PRP1b2b0b1b09a8>D91I8EAy8ADD9PFP1D9b@WEX?2P1O1X?2o"). Qed.

(* [comment removed for export] *)
Lemma mprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 A)) 18446744073709547520) = Z_to_bv 64 A
  /\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + (4095 + L)))) 18446744073709547520))
                 - bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 A)) 18446744073709547520))) = Z_to_bv 64 L.
Proof.
ltac2:(KReplay.run1 (kr_t_F_mm_syscalls ()) ["CEIL_WRAP_1"] "h04__x1h14__x2h26__sat3h31zh47__arithh54__ffh66__sat4h76__sat5h88__varmaph95__with:6__sat1h;6__sat2h<6__sat6h=6__sat7h>2H0h?3H10h@2H5hA2HahB7__sat15hC4__x3hD4__x4hE4__x5hF4__x6hG4__x7hH4__x8hI1AhJ2A0hK1BhL2E1hM2E2hN1HhO2H1hP3H11hQ3H12hR3H13hS2H2hT2H3hU2H4hV2H6hW2H7hX2H8hY2H9hZ2HAh[2HLh\1Lh]2L0h^7__sat14h_1qh`2q0ha2q1hb1rhc2r0hd2r1p%0p&0p;1p;2p;3p;4p;6p;8p;7g0000j1JTg000Uj1QTg004;j21Tg0013j20Tg00\Ik201Tg005^j2FTg00cij1tTg00h=j1qTg00?ij17Tg00Wfj2MTg00h`j22j1|Tg002Nj36Tg00iFj24Tg001Pj25Tg00^Dj3_j2xTg00_fk203Tg005Bj2<Tg00`Nj3~Tg008Hj2iTg008ij2PTg00;`j1vTg00<`j1uTg00=@j2OTg00Vij1sTg00><j1pTg00>Zj1oTg00A1j2UTg00Bcj1nTg00@Nj2hTg00DLj3ZTg00ERk20<Tg00F4k20;Tg00F`k30:Tg00G?k409Tg001mj2gTg002hk108Tg003Aj2;Tg003^j2STg004[j2cTg006Uj2aTg006:j2LTg007<j2`Tg007bj2dTg00UAk105Tg00U_k204Tg009Cj1BTg00V@j3RTg009bj2kTg00;4j2[Tg00TUj2jTg00<@j3^Tg00CEk600Tg00Doj3\Tg00j0j8wTg00jMj4yTg00dGj3zTg00jhj2VTg00koj2lTg00=^k402Tg00ATj4]Tg00Hlj7bTg00IPj8eTg00:Kj3fTg00Cik306Tg00B?k707Tg00ZDj6rTf0R0#J#Jp=:g00L3R1g00M6R2760p=D1F20p=8%70#7#7#7#7#7#7#7p=Kf5R3f4R4f3R5f2R6f1R7'5'2;60'Lp=A1570,26p=mP1P6P7P0H02p=EP6g00J4R8g00JSR9P9g00K3R:P1P7g00Q?P0C]g00KSR;Fbp=>1h10p=HP5P8P9P9P:P6P7P0Gep=CP6P8P9P9P:P1P7g00PXP0C]P;Fbp=9f6R<P8P9P9P:P3P4P5P8P9P9P:P6P7P0GeGep=GA6170p=31F261<70'Lp==1k10p=IAf170p=TAf1709f16p=NB06170p=?P1P7g00P1P0C]p=YP7P8P9P9P:P0P;Fbp=WP6P8P9P9P:P7P0K07p=X1267=650p=}1<70,L6p={P1P4P5P6P7P0Erp=@g00LQR;#JR=#JS00#JS01#J#:R>#:#:#:#QR?,17#DS02Q02%85R@1034/0?%Q=RA%Q>RB+01RC'FP<%t>R>#qRD%7;RE#7S03#7#KRF#K#K#K#K#K#:#:#:#:#:#:#QRG,M0,2>RHf7RI,2>RJ36PDP>%QFRF/0<,0IRK,2>,4>/MG,2>,4>14>HRH12><RLEAX3110F3S04,0<RM1MIG,2>RN=6DJPDP>PH14>NPLEAX3111<?,5<RN12>0RH=6DJPDP>1MKG,2>,4>14>HROPLEAX3111M?,5M11I?RP9m>IRQ=6DJPDP>PO14>QPLEAX31A_<?6S05%8?RQ%8P[S06203ABRP1<2ARR%8B1<2C[RS[RT%8ARUg00gERVA~AB7UWARB%8C\V^AURUf8RV?_?4RWf9RX/1?#8\QRYP6g00MTRZ1i2A'PPReRRO1R[PSg00N:R\#vR]%u\R^1O16S07%s1R_7E7R`%p1Ra%o1RbPb1U12Rc1U1?Rd5>b%n9Re%H=Rf9>bcS08CCPePbA9bfcPe1h1;Rg=Z1f=9bgFG20<b:RhP0P6g00QfRig00RFRj'P20;06=6ijdB0:127H09Rjb5b8b9X01X11%86Ri\Q%D61565/36[[^01^11P0f<Rk/1?RlPkP3f:RmO4b4b2b:b;b2b613N<1gK?%D?RN$08Rn10FIRo,0VRp1;p?,S?11p?S09'0'3[1cp?1<2?Rq10FV,0XRr/1?Rs?=s?[1ar?1<?2Rt10FX,0mRu/1?Rv,<?1Fv2'L[1`u?f;Ru10Fm'0Rv/;?#D\N1dv?10Fu,0kRw/1?/3w\N1;w?P1f=Rw10Fk'0/1?P1f>Rx/g?f?Ry1;y?,S?11y?'0'3\n1cy?f@Rz/1?R{?={?\q1az?fAR{/1?R|,<?1F|2'L\t1`{?fBR{/;?#D\N1d{?fCR{/1?/3{\N1;{?P1fDR{/1?P11g{?fER|1;|?,S?11|?'0'3\n1c|?fFRn/1?R}?=}?\q1an?fGR}/1?R~,<?1F~2'L\t1`}?fHR}/;?#D\N1d}?fIR}/1?/3}\N1;}?P1fJ/1?P1P31i2?,PZPqeRqO1A=00?PwPqO1A=VV?P|PqO1A=zz?PPPTPBPUP7PRO1PS&05;-041R;g00NfRR#BRz#BRq#BRZ#BR2#B#BR}#BRt#IR~5R1%I}R}9R1;%IZRZ%IqRq%IzRz9R1;1k1RRR'T3N3N%Bt#I%I29R1;AR1;Z/Tq5N}7N~1TzRRzg00OER~'['j'j=^\]P^1O1V?E4_1O1<7E61O131O1I7E57E7PaPbPbPbP8P9P9P:A9bdcJ00R:PeQ01#H9\1d%7=#HR='?99bfCCPePbPbP:PeQ03#H9\1dQ00#HR9'?99bgCCPePb%HER89>bc1Y8d,Wb5XbPePbPbP:Pe1U1F/?f,?gR:%JE#H9\1d/?859bCCPePbAZ1g9=9bgPePbA9b=cPeAZ1:81?gfR859bFGFGFGPhPjb5b8b9X01X11XC1XD1XE1XF1XG1XH1g00Rf\NRN1S?V/03,36[R3A=44?Q04,041S?X/0<'3\N154I/34%DX10<o/5V10<I'3[[[[\3[^01^11^C1^D1^E1^F1^G1^H1P0PVPyPnPIPxP|fRfSPwP{P4fKfLfPO>b4bBb^bBb>b@b?bdbabRbQbPb?bYbcb`bXbWbVb@bUbbb_bTbSbOb>bN11K?,5K10I<'3PV12>XRK96DHPDP>Am>rs,4>PO12>VRsEAX3110VIRHA6DKKR{PDP>PO14>KRKPsEAX31PHP{PDP>P0PKPsEAX31PVP{PDP>10XVP0PsEAX31A6DssPDP>15HVR{PJC}1PDsP1PD%|>RJPJP{PIPD\1/PJPWPY1xr?RJ%8r11v?#8\Q[RvPPPTPBPUA_u?IRr%8l\QRQP[PSP]P^P`PaAZ18g=9bfPhPjb5b8b9X01X111007Rf/50/37^01^11P0PxPyO2b4b7b2b6b7b<b=GwCy14>sPWPYPJPvPPPTPBPUPrPQP[PSANZqR/[~=^\]P^Q07?E6_?E7_PaPb1?g9/?d1U1A=z1>RA5>bPePbA>bc9PePbA>bcgR9Pe1YgA,Wb9Xb9CCFGPhPjb5b8b9X01X11Rg10f?/FCRfA{@5C\i\i[^01^11R_P0PxPyPXPmPuO5Rmb4b7b2b6b7b<b=,VVD@12>H,4>PWPYPJPvPPPTPBPUPrPQP[PS1Tqz/[~=^\]R]P^P`PaPb1?8d=>bARdPePbQ08PePbP9PeA>bc81Y8A,Wb5XbCCFGPhPjb5b8b9X01X111054R8?=8C\i\i\f^01^11Pmb4b7b2b6b7b<b=,VHD@Q09,5pP0D@11V?,5VP7D@bMbL1MMGQ05Q06PPPTPBPUPWPYP[PSP]P^P`PaPbPdPePbQ08PePbP9PeA>bc:1Y:A,Wb5XbCCFGPhPjb5b8b9X01X1110F4,05R5?=5C\i\i\f^01^11P0PuPkP<PIPVO5RVb4b2b:b;b2b6RI,lMD@1M<GQ05Q06PPPTPBPUPWPYP[PSPgP_PVb4b2b:b;b2b6RV,l<D@12>M,4>1VMID@14>L1V<VD@WKX]@WJW[WZX\1XI1o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_fix_errno (e : Z) : Z := if (e =? 1)%Z then 12%Z else e.

(* [comment removed for export] *)
Definition mmap_raw (isnone : bool) (x len : Z) (m : word -> option byte) : word -> option byte :=
  if isnone then apply_unmaps m [(wa x, Z_to_bv 64 (mmap_len len))]
  else apply_zeros m [(wa x, Z_to_bv 64 (mmap_len len))].

(* [comment removed for export] *)
Definition mmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp)
        /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z
    | MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m2
        /\ wmono asegs m m2 /\ mem_inv asegs m2
        /\ stk asegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
        /\ rw_cells asegs m2 (errno_addr tp) [C4 errv]
        /\ mmap_addr_ok len avoid x = true
    end.

(* [comment removed for export] *)
End CEIL_WRAP_1.


Ltac mmap_err_finish MU WM :=
  intros ms' PO; cbv beta in PO; unfold sysret_post, sysret_val, sysret_errno in PO; rewrite errno_of_errno_ret in PO by lia;
  destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU' & WM' & MI' & ST' & ERR');
  unfold mmap_anon_post, mmap_fix_errno;
  first [ replace (_ =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia)
        | replace (_ =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia) ]; cbv iota;
  do 15 eexists; split; [reflexivity|];
  split; [ eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU']; intros y; cbn; lia |];
  split; [ eapply wmono_trans; [exact WM | exact WM'] |];
  split; [exact MI'|]; split; [exact ST'|]; split; [exact ERR'|]; lia.

(* [comment removed for export] *)
Ltac sys_nret_raw :=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fixed_shape (A L : Z) (r : word) (u : bool) : resp :=
  if u then mkEffectU r [] [] [(wa A, Z_to_bv 64 (mmap_len L))] [] [] else mkEffectU r [] [] [] [] [].

Definition mmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono asegs m m')
    /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
End CEIL_WRAP_2.

(* [comment removed for export] *)

End F_mm_syscalls.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0048.
Module F_memcpy_A.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Arr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Bytes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044.StrFun.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0048. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0048.STRW_tac.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition asegs := Plain.Plain_loaded_segments.   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at asegs m' (bv_unsigned a1) src.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation INV := (mc_inv asegs S D src W m).
  Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
  Ltac fin := mc_fin.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End Proofs.
End CEIL_WRAP_1.


End F_memcpy_A.
Module F_memcpy_B.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Arr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Bytes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044.StrFun.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0048. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0048.STRW_tac.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0051.F_memcpy_A.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation INV := (mc_inv asegs S D src W m).
  Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
  Ltac fin := mc_fin.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End Proofs.
End CEIL_WRAP_1.


End F_memcpy_B.
Module F_memcpy.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Arr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Bytes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044.StrFun.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0048. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0048.STRW_tac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0051.F_memcpy_A OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Agent.Mh_0051.F_memcpy_B.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation INV := (mc_inv asegs S D src W m).
  Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
  Ltac fin := mc_fin.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End Proofs.
End CEIL_WRAP_1.

(* [comment removed for export] *)

End F_memcpy.
