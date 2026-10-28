(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase AKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AKit2 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3mulK47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC35stdpp7tactics<f_equal_helpC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma le1_sym : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
ltac2:(KReplay.run1 (kr_t_AKit2 ()) ["CANSEC1"] "h01zp;1p;2p;3p;4p;8p;6g0000j10Tg000Uj13Tg0013j25Tg001Pj2>Tg0020j1;Tg002Nj1HTg0031j1FTg003Qj1ATg0040j27Tg004mj21Tg005Sj1=Tg0063j36j2<j1ITg006Sj32Tg006mj24Tg007Gj2:Tg007dj18Tg008Ij4GTg008cj4ETg009Ij3BTg00:Bj89Tg00:_j2@Tg00;Ij1CTg00<Jj6DTg00<hj1?Tg00=XR0P0f0R1g00>6R2#0R3#3R4%03#0R3#0#0#0R5#3'5R6'>R7%;3R8#HR9#FR:g00>[#AR;/71f1,18%=9R<56932X00P:P:1187R=,<91181R8,<9P<P<P9P:\:R>%I9R?P?P=P8P>\9/4?P1P6%33,54R3P01:139206X00%82#8#0#0#0#3,54R41:43,40CGCE9B71G914:<G917;7A698<R852:e%;5R51151R5'@%C1ED%?5=2:8eW0o"). Qed.

End CANSEC1.
Ltac sym_store_bytes :=
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_sym z)
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => change (Z_to_le_bytes 1 z) with (le1 (Z_to_bv 64 z)); rewrite (le1_sym z)
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
       end).
(* [comment removed for export] *)
Ltac sstep := step; sym_store_bytes; mem_after_store_opt.

(* [comment removed for export] *)
Ltac snapshot W MUx WMx :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl W m) as MUx; pose proof (wmono_refl bsegs m) as WMx end.

(* [comment removed for export] *)
Ltac xport H MUx WMx tac :=
  lazymatch type of MUx with munch ?W ?m0 ?m =>
  lazymatch type of H with
  | rw_cells _ m0 ?A ?cs =>
    apply (rw_cells_transport bsegs W m0 m A cs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; tac ]
  | u64arr _ m0 ?A ?xs =>
    apply (u64arr_transport bsegs W m0 m A xs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; rewrite ?upd_length; tac ]
  | u32arr _ m0 ?A ?xs =>
    apply (u32arr_transport bsegs W m0 m A xs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; rewrite ?upd_length; tac ]
  | stk _ m0 ?lo ?hi =>
    apply (stk_transport_disjoint bsegs W m0 m lo hi) in H; [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; tac ]
  end end.
Ltac carry H MUx WMx tac := unbox H; xport H MUx WMx tac.

(* [comment removed for export] *)
Ltac with_box D tac := let D' := fresh "DX" in pose proof D as D'; unbox D'; tac.
(* [comment removed for export] *)
Ltac unboxed D := let D' := fresh "DX" in pose proof D as D'; unbox D'; exact D'.

(* [comment removed for export] *)
Ltac addr_diff_guard k :=
  lazymatch eval vm_compute in ((0 <=? k) && (k <=? 4096))%Z with true => k end.
Ltac addr_diff E A ::=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in let k := eval vm_compute in (c1 - c2)%Z in addr_diff_guard k
      | X => let k := zlit c1 in addr_diff_guard k
      | _ => let e := zlit E in let a := zlit A in let k := eval vm_compute in (e - a)%Z in addr_diff_guard k
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in let k := eval vm_compute in (- c2)%Z in addr_diff_guard k
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in let k := eval vm_compute in (e - a)%Z in addr_diff_guard k
      end
  end.
