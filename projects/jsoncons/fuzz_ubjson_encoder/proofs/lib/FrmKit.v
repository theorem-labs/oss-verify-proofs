(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_FrmKit () := "C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPSteps?fp_frm_zero_fx0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6fp_csrC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPSteps8frm_zeroC13~~~K47Corelib4Init5Logic2eq01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6FrmKit4FRMK6frm_okC13~~~K47Corelib7Numbers7BinNums8positive03C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMK.

Definition frm_ok (fx : FPState) : Prop := frm_zero (@fp_csr fx).

Lemma frm_ok_fx0 : frm_ok fx0.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKit ()) [] "g0000o"). Qed.

Lemma frm_ok_unfold fx : frm_ok fx = frm_zero (@fp_csr fx).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKit ()) [] "h02fxp;1p;2g001Bj12Tg002Lj11Tg003Wj20Tg0041R0p-0f0R1#2#1'0X00P1O1W0o"). Qed.

(* [comment removed for export] *)
Lemma frm_ok_mkFP_same fr (fx : FPState) : frm_ok fx -> frm_ok (mkFP fr (@fp_csr fx)).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKit ()) [] "h02frh12fxh21Hp;1p;2g005>j10Tg005cj15Tg006Hj11Tg006fj12Tg007Ij24Tg0085j13Tg009B#0R0#5#1%00#0#0#0#0#1#2'4R0g0041R1f0R2#3P2W2X11X00f1P2O2W1W0o"). Qed.
Lemma frm_ok_mkFP fr cs : frm_zero cs -> frm_ok (mkFP fr cs).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKit ()) [] "h02csh12frh21Hp;1p;2g005>j10Tg005cj15Tg006Hj11Tg006fj12Tg007Ij24Tg002Lj13Tg009B#0R0#5#1%00#0#0#0R0#0#1#2'4R1%10#2R0f0R2#3P2W2X00X11f1P2O2W0W1o"). Qed.

(* [comment removed for export] *)
Lemma frm_ok_of_eq (fx fx' : FPState) :
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 -> frm_ok fx -> frm_ok fx'.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmKit ()) [] "h02fxh13fx'h21Eh31Hh41zp;1p;2p;3p;6g005>j10Tg006Hj1:Tg001Bj11Tg009gj24Tg005cj15Tg00:Qj17Tg00:oj23Tg00;Oj22Tg00;mj36Tg0085j19Tg00<Gj68Tg0041R0g00<eR1g009BR2#0R3#0#0#0#0#:R4f0R5#1'4%53#7R3'3%52#5#7R2'2f1R6#1,44/33/2236f2R7#9R8P1f3#1,44/33/22g00=C9615X41P5%17,44/33/22P6E8P8eW3W2X10X00P6P5O2X10W0o"). Qed.

(* [comment removed for export] *)
Definition msteps_keep_ty (segs : list Segment) : Prop :=
  forall (fx fx' : FPState) R R' pc pc' M M',
    msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').

(* [comment removed for export] *)
Ltac frm_solve_with L :=
  lazymatch goal with
  | |- frm_ok ?fx => change (frm_zero (@fp_csr fx)); frm_solve_with L
  | |- frm_zero (@fp_csr ?fx) =>
      first [ assumption
            | exact fp_frm_zero_fx0
            | lazymatch fx with
              | mkFP _ (@fp_csr ?f1) => change (frm_zero (@fp_csr f1)); frm_solve_with L
              | mkFP _ ?cs => cbn [fp_csr]; frm_solve_with L
              end
            | match goal with
              | MS : msteps _ (@mkst ?f0 _ _ _ _) (@mkst fx _ _ _ _) |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (L _ _ _ _ _ _ _ _ MS); frm_solve_with L
              | E : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr ?f0)) 5) 7 |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (frm_ok_of_eq f0 fx E); change (frm_zero (@fp_csr f0)); frm_solve_with L
              | E : _ /\ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr ?f0)) 5) 7 |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (frm_ok_of_eq f0 fx (proj2 E)); change (frm_zero (@fp_csr f0)); frm_solve_with L
              | H : frm_ok fx |- _ => exact H
              end
            | fail 1 "frm_solve: no frm fact for" fx ]
  | |- frm_zero ?cs => first [ assumption | fail 1 "frm_solve: no frm fact for csr" cs ]
  | |- _ => fail "frm_solve: goal is not an frm obligation"
  end.

End FRMK.
