(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac ex_ext := repeat first [ rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ])
                            | rewrite ext_val_zx_id by (rewrite ?u_Z2bv by lia; ex_pow2; lia) ]; try reflexivity;
                rewrite ?m_mul, ?zbv_mul, ?zbv_add, ?ex_ptr_val; try reflexivity; try (f_equal; lia);
                rewrite ?zbv_addw_small by lia; try reflexivity; try (f_equal; lia).
(* [comment removed for export] *)
Ltac ex_mem2 regs Hms :=
  eapply ex_msteps_mem; [exact Hms|]; cbn [mem_denot s_log e_addr e_width e_val];
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs
                               | first [ solve [ex_bytes_eq regs]
                                       | (ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; f_equal; ex_ext) ] ]);
  reflexivity.

(* [comment removed for export] *)
Ltac ex_runN nx fuel stops scr HR HK R' HR' Hms :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok ?segs _ ?base ?kn =>
      lazymatch goal with
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in let Hlf := fresh "Hlf" in let Hex := fresh "Hex" in
              assert (Hex : sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr')) by (vm_cast_no_check (eq_refl (ss', scs, scr')));
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; ex_sc regs
              | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
                          Hex HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc Hlf Hex ]
          end
      end
    end
  end.

(* [comment removed for export] *)
Ltac exx_named z Hrdn tac :=
  eapply (dl_read _ _ _ z); [ tac | exact Hrdn | first [ reflexivity | (ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; reflexivity) ] ].

Section KnowSum.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma exx_kword_sum : forall E m (eb eo v : expr) (b o off z : Z) (w : nat),
  edenot E eb = Z_to_bv 64 b -> edenot E eo = Z_to_bv 64 o -> edenot E v = Z_to_bv 64 z -> (1 <= w)%nat -> (w <= 8)%nat ->
  (0 <= b + o < 2 ^ 64)%Z -> (0 <= b + o + off)%Z -> (b + o + off + Z.of_nat w <= 2 ^ 64)%Z -> (0 <= z < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 (b + o + off)) w = Some (Z_to_le_bytes w z) ->
  kentry_ok segs E m (KWord (SA (EAlu ALU_ADD eb eo) off) w v).
Proof.
  intros E m eb eo v b o off z w Hb Ho Hv Hw1 Hw Hbo H1 H2 Hz Hr.
  apply (ex_kword_Z segs E m (EAlu ALU_ADD eb eo) v (b + o) off z w); try assumption.
  cbn [edenot]. rewrite Hb, Ho. apply ex_ptr_val.
Qed.

Lemma exx_kwr_sum : forall E m (eb eo : expr) (b o off n lo : Z) (N : nat),
  edenot E eb = Z_to_bv 64 b -> edenot E eo = Z_to_bv 64 o -> store_ok segs m (Z_to_bv 64 lo) N = true ->
  (0 <= lo)%Z -> (lo + Z.of_nat N <= 2 ^ 64)%Z -> (0 <= b + o < 2 ^ 64)%Z -> (lo <= b + o + off)%Z -> (0 < n)%Z -> (b + o + off + n <= lo + Z.of_nat N)%Z ->
  kentry_ok segs E m (KWr (SA (EAlu ALU_ADD eb eo) off) n).
Proof.
  intros E m eb eo b o off n lo N Hb Ho HS Hlo HN Hbo H1 Hn H2.
  apply (ex_kwr segs E m (EAlu ALU_ADD eb eo) (b + o) off n lo N); try assumption.
  cbn [edenot]. rewrite Hb, Ho. apply ex_ptr_val.
Qed.

Lemma exx_kdisj_sum : forall E m (eb1 eo1 eb2 eo2 : expr) (b1 o1 b2 o2 k1 n1 k2 n2 : Z),
  edenot E eb1 = Z_to_bv 64 b1 -> edenot E eo1 = Z_to_bv 64 o1 -> edenot E eb2 = Z_to_bv 64 b2 -> edenot E eo2 = Z_to_bv 64 o2 ->
  (0 <= b1 + o1 < 2 ^ 64)%Z -> (0 <= b2 + o2 < 2 ^ 64)%Z ->
  (b1 + o1 + k1 + n1 <= b2 + o2 + k2 \/ b2 + o2 + k2 + n2 <= b1 + o1 + k1)%Z ->
  kentry_ok segs E m (KDisj (SA (EAlu ALU_ADD eb1 eo1) k1) n1 (SA (EAlu ALU_ADD eb2 eo2) k2) n2).
Proof.
  intros E m eb1 eo1 eb2 eo2 b1 o1 b2 o2 k1 n1 k2 n2 H1 H2 H3 H4 R1 R2 D.
  apply (ex_kdisj segs E m (EAlu ALU_ADD eb1 eo1) (EAlu ALU_ADD eb2 eo2) (b1 + o1) (b2 + o2) k1 n1 k2 n2); try assumption.
  - cbn [edenot]. rewrite H1, H2. apply ex_ptr_val.
  - cbn [edenot]. rewrite H3, H4. apply ex_ptr_val.
Qed.
End KnowSum.
