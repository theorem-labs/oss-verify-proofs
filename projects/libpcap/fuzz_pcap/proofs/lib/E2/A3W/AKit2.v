(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma le1_sym : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. rewrite unsigned_lit_wrap. cbn. f_equal. apply Z_to_bv8_mod.
  apply Z.mod_mod_divide. exists (2^56). reflexivity.
Qed.

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
    pose proof (munch_refl W m) as MUx; pose proof (wmono_refl asegs m) as WMx end.

(* [comment removed for export] *)
Ltac xport H MUx WMx tac :=
  lazymatch type of MUx with munch ?W ?m0 ?m =>
  lazymatch type of H with
  | rw_cells _ m0 ?A ?cs =>
    apply (rw_cells_transport asegs W m0 m A cs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; tac ]
  | u64arr _ m0 ?A ?xs =>
    apply (u64arr_transport asegs W m0 m A xs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; rewrite ?upd_length; tac ]
  | u32arr _ m0 ?A ?xs =>
    apply (u32arr_transport asegs W m0 m A xs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; rewrite ?upd_length; tac ]
  | stk _ m0 ?lo ?hi =>
    apply (stk_transport_disjoint asegs W m0 m lo hi) in H; [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; tac ]
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

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma le1_sym : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. rewrite unsigned_lit_wrap. cbn. f_equal. apply Z_to_bv8_mod.
  apply Z.mod_mod_divide. exists (2^56). reflexivity.
Qed.

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
    pose proof (munch_refl W m) as MUx; pose proof (wmono_refl asegs m) as WMx end.

(* [comment removed for export] *)
Ltac xport H MUx WMx tac :=
  lazymatch type of MUx with munch ?W ?m0 ?m =>
  lazymatch type of H with
  | rw_cells _ m0 ?A ?cs =>
    apply (rw_cells_transport asegs W m0 m A cs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; tac ]
  | u64arr _ m0 ?A ?xs =>
    apply (u64arr_transport asegs W m0 m A xs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; rewrite ?upd_length; tac ]
  | u32arr _ m0 ?A ?xs =>
    apply (u32arr_transport asegs W m0 m A xs) in H;
    [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; rewrite ?upd_length; tac ]
  | stk _ m0 ?lo ?hi =>
    apply (stk_transport_disjoint asegs W m0 m lo hi) in H; [ | exact MUx | exact WMx | cbn [disjoint_from fst snd]; tac ]
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
  end. Ltac twm_hook_1 E A :=
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
End TwB.
(* [comment removed for export] *) Ltac addr_diff E A ::=
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
