(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocKitOL.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RelocTacOL () := "I69OSSVerify5KrLib6Common5Reloc;CanonCodeOL;RelocCodeOL00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib6Common5Reloc9RelocCode8code_hasC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc;CanonCodeOL=rl_code_ol_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocCode:code_soundC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common5Reloc5Reloc5Reloc00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00C69OSSVerify5KrLib6Common5Reloc;CanonCodeOL=canon_code_OLC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope bv_scope.

Lemma rl_fetch_OL : forall {RL : Reloc} {RC : RelocCodeOL RL} b c (w : bv 32),
  code_has canon_code_OL b c (bv_unsigned w) = true -> fetch_word rl_segs (rl (rl_delta b) c) = Some w.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocTacOL ()) [] "h01Hh12RCh22RLh31bh41ch51wp;1p;2p;4p;3p;8g0000j1:Tg001;j10Tg001`j12Tg002>j11Tg002aj29Tg003Kj48Tg004Oj33Tg004ij14Tg005hj15Tg006hj26Tg0083j87Tg0099f0R0#:g00:8g00:]g00;;#0#0#0#0#0#2R1#1g00;`g00<@R2f2R3f1R41910C8g00=K33f5R1#4%51P2f3P3P4f4,61P0G7W0W5W4W3W1W2o"). Qed.

(* [comment removed for export] *)
Ltac rl_ret_ok_try_OL RL b c off :=
  let c0 := eval vm_compute in (c + off)%Z in
  let z0 := eval vm_compute in (code_lookup canon_code_OL b c0) in
  lazymatch z0 with
  | Some ?w0 => exact (rl_ret_ok_near _ _ c0 c _ (rl_fetch_OL b c0 (Z_to_bv 32 w0) ltac:(vm_cast_no_check (@eq_refl bool true))) eq_refl)
  | None =>          (* [comment removed for export] *)
      let r := eval vm_compute in (site_find canon_sites_OL 0%nat c0) in
      lazymatch r with
      | Some (?i, _, _) =>
          let s := eval vm_compute in (nth_error canon_sites_OL i) in
          lazymatch s with
          | Some ?cs => exact (rl_ret_ok_near _ _ c0 c _ (rl_site_F_OL i cs (@eq_refl _ (Some cs))) eq_refl)
          end
      end
  end.

Ltac rl_ret_ok_OL :=
  lazymatch goal with
  | |- ret_ok (Z_to_bv 64 (?c + @rl_delta ?RL ?b)) => change (ret_ok (rl (@rl_delta RL b) c)); rl_ret_ok_OL
  | |- ret_ok (rl (@rl_delta ?RL ?b) ?c) =>
      first [ rl_ret_ok_try_OL RL b c 0%Z | rl_ret_ok_try_OL RL b c (-4)%Z | rl_ret_ok_try_OL RL b c 4%Z | rl_ret_ok_try_OL RL b c (-8)%Z
            | rl_ret_ok_try_OL RL b c 8%Z | rl_ret_ok_try_OL RL b c (-12)%Z | rl_ret_ok_try_OL RL b c 12%Z | rl_ret_ok ]
  end.

Ltac rl_vmc_OL :=
  first [ rl_ret_ok_OL
        | lazymatch goal with
          | |- context [@rl_delta _ _] => fail 1 "rl_vmc_OL: the goal mentions a delta (no computation on open terms)"
          | _ => vm_compute; reflexivity
          end ].
