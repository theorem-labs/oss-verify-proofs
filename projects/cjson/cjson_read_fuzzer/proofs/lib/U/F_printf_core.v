(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_strnlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Printf_zfacts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgU.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_common.
Module F_printf_core_common.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

(* [comment removed for export] *)

Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac show_goal := match goal with |- ?G => idtac "GOAL:" G end.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac plia := unfold zlength, got_ssp, ssp_guard, PC_DEPTH, OUT_DEPTH, GLOBALS_TOP, FMT_FP_DEPTH, INT_MAX in *; lia.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
(* [comment removed for export] *)
Tactic Notation "callw" tactic3(tac) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
  end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
(* [comment removed for export] *)
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
(* [comment removed for export] *)
Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).
(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Definition hide (P : Prop) := P.
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
  lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

(* [comment removed for export] *)
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.

(* [comment removed for export] *)
Lemma zb_length : forall l, length (zb l) = length l.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.zb_length | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.zb_length as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.zb_length | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.zb_length | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.zb_length OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

Lemma land_M64_id : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.land_M64_id | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.land_M64_id as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.land_M64_id | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.land_M64_id | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.land_M64_id OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_0 | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_0 as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_0 | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_0 | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Lemma dec_digits_small : forall x, (1 <= x <= 9)%Z -> dec_digits x = [48 + x]%Z.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_small | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_small as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_small | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_small | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Lemma dec_digits_step : forall x, (10 <= x < 2^64)%Z -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10]%Z.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_step | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_step as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_step | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_step | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Lemma dec_digits_length : forall x, (length (dec_digits x) <= 20)%nat.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_length | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_length as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_length | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_length | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.dec_digits_length OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells usegs m A [CB n bs] -> length bs = n.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.rw_CB_length | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.rw_CB_length as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.rw_CB_length | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.rw_CB_length | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.rw_CB_length OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Lemma cb8_c8_in : forall m A pre post bs, rw_cells usegs m A (pre ++ CB 8 bs :: post) -> rw_cells usegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.cb8_c8_in | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.cb8_c8_in as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.cb8_c8_in | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.cb8_c8_in | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core_common.cb8_c8_in OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let rec go pre l := lazymatch l with
     | CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
     | ?c :: ?l' => go constr:(pre ++ [c]) l'
     | [] => idtac end in
  go constr:(@nil cell) cs end.
End F_printf_core_common.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_conv.
Module F_printf_core_conv.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

   (* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
End F_printf_core_conv.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_cvd.
Module F_printf_core_cvd.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_cvd.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_cvfp.
Module F_printf_core_cvfp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_cvfp.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_cvs.
Module F_printf_core_cvs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

   (* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
End F_printf_core_cvs.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_cvu.
Module F_printf_core_cvu.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_cvu.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_cvx.
Module F_printf_core_cvx.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_cvx.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_dir.
Module F_printf_core_dir.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_dir.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_dloop.
Module F_printf_core_dloop.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_dloop.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_end.
Module F_printf_core_end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_end.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_exit.
Module F_printf_core_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_exit.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_exit1.
Module F_printf_core_exit1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_exit1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_flags.
Module F_printf_core_flags.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_flags.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_fmtu.
Module F_printf_core_fmtu.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_fmtu.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_fmtu2.
Module F_printf_core_fmtu2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_fmtu2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_head.
Module F_printf_core_head.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
End F_printf_core_head.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_intc.
Module F_printf_core_intc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_intc.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_intc2.
Module F_printf_core_intc2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_intc2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_p1.
Module F_printf_core_p1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_p1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_prec.
Module F_printf_core_prec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_prec.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_pro.
Module F_printf_core_pro.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_pro.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_scan.
Module F_printf_core_scan.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_scan.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_state.
Module F_printf_core_state.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_state.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_t1.
Module F_printf_core_t1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_t1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_t2.
Module F_printf_core_t2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_t2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_t3.
Module F_printf_core_t3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_t3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_t4.
Module F_printf_core_t4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_t4.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_t5.
Module F_printf_core_t5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_t5.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_t6.
Module F_printf_core_t6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_t6.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_tail.
Module F_printf_core_tail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_tail.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core.
Module F_printf_core_width.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_width.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core_xloop.
Module F_printf_core_xloop.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_xloop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_strnlen.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_strnlen F_fwritex F_pad F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_pop_arg Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg.

Export F_printf_core_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_strnlen.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.U_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pop_arg.U_pop_arg_contract.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.



(* [comment removed for export] *)
Theorem printf_core_proof : forall (St : Type) (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
  sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK -> out_stmt Fp B BS SINK TOPOK OUT ->
  printf_core_stmt Fp B BS SINK TOPOK OUT OUTFP.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
#[export] Instance U_printf_core_proof_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof_c_ok.
#[export] Instance U_printf_core1_proof_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof_c_ok.
