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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_sscanf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_pre2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgU.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_pre3.
Module F_fmt_fp_pre3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Definition ROUND0 : Z := f128_div (f128_of_i32 2) K_LDBL_EPSILON.
Definition ROUND1 : Z := f128_add ROUND0 (f128_of_i32 2).
(* [comment removed for export] *)
Notation zboxed := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre3.zboxed (only parsing).
Notation ZBoxed := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre3.ZBoxed (only parsing).
End F_fmt_fp_pre3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_pre4.
Module F_fmt_fp_pre4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Definition gadj_pp (p : Z) : Z := (p + Z.b2z (p <? 1))%Z.
Definition gadj_c1 (p e : Z) : Z :=
  Z.b2z (Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 <? Z.lxor (Z.land (gadj_pp p) 18446744073709551615) 9223372036854775808)%Z.
Definition gadj_c2 (e : Z) : Z := Z.lxor (Z.b2z (Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 <? 9223372036854775804)%Z) 1.

(* [comment removed for export] *)
Ltac weq := apply Z_to_bv_eqm; rewrite ?land_W64; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.shiftr_div_pow2 by lia;
            change (2^1)%Z with 2%Z; change (2^2)%Z with 4%Z; change (2^3)%Z with 8%Z; mlia.

(* [comment removed for export] *)
Definition rot10 (v : Z) : Z :=
  Z.lor (Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.land (v * 18446744072850558157) 18446744073709551615)) 1)) 18446744073709551615)
        (Z.land (bv_swrap 32 (Z.shiftl (Z.land (v * 18446744072850558157) 18446744073709551615) 31)) 18446744073709551615).

Definition K_set12 (K : midK) (eb : list byte) : midK :=
  MidK (K_pad K) (K_jk40 K) (K_jk8 K) (K_jk3 K) eb (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) (K_plz K) (K_pfx K) (K_Ft K).
(* [comment removed for export] *)
Notation lboxed := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre4.lboxed (only parsing).
Notation LBoxed := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre4.LBoxed (only parsing).
Lemma zb_length : forall l, length (zb l) = length l.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre4.zb_length | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre4.zb_length as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre4.zb_length | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre4.zb_length | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_pre4.zb_length OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Definition K_set37 (K : midK) (bf : list byte) : midK :=
  MidK (K_pad K) (K_jk40 K) (K_jk8 K) (K_jk3 K) (K_jk12 K) bf (K_p1 K) (K_prefix K) (K_pl K) (K_plz K) (K_pfx K) (K_Ft K).
End F_fmt_fp_pre4.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require FmtFp_facts2.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_join.
Module F_fmt_fp_rnd.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
End F_fmt_fp_rnd.

(* [comment removed for export] *)
Module F_fmt_fp_t100.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
End F_fmt_fp_t100.

(* [comment removed for export] *)
Module F_fmt_fp_t988.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
End F_fmt_fp_t988.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module F_fmt_fp_c00.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].
End F_fmt_fp_c00.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_c58.
Module F_fmt_fp_c58.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_c58.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_dig.
Module F_fmt_fp_dig.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].
End F_fmt_fp_dig.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_dn.
Module F_fmt_fp_dn.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_dn.

(* [comment removed for export] *)
Module F_fmt_fp_entry.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
End F_fmt_fp_entry.

(* [comment removed for export] *)
Module F_fmt_fp_r1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
End F_fmt_fp_r1.

(* [comment removed for export] *)
Module F_fmt_fp_r2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_r2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_r3.
Module F_fmt_fp_r3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_r3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_rd.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Module F_fmt_fp_rd.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].   (* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
End F_fmt_fp_rd.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_t9a8.
Module F_fmt_fp_t9a8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].
End F_fmt_fp_t9a8.

(* [comment removed for export] *)
Module F_fmt_fp_ta98.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_ta98.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_taec.
Module F_fmt_fp_taec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_taec.

(* [comment removed for export] *)
Module F_fmt_fp_tbb4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_tbb4.

(* [comment removed for export] *)
Module F_fmt_fp_tbc4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_tbc4.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_te1.
Module F_fmt_fp_te1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_te1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_te3.
Module F_fmt_fp_te3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_te3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_te4.
Module F_fmt_fp_te4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_te4.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_tf1.
Module F_fmt_fp_tf1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_tf1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_tf3.
Module F_fmt_fp_tf3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_tf3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_tf5.
Module F_fmt_fp_tf5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Local Ltac mlia ::= first [ lia | Z.div_mod_to_equations; lia ].
End F_fmt_fp_tf5.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_up.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StepFast.
Module F_fmt_fp_up.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
(* [comment removed for export] *)

#[local] Ltac2 Set OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StepFast.SF.sf_mode := 0.
End F_fmt_fp_up.

(* [comment removed for export] *)
Module F_fmt_fp_join.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
End F_fmt_fp_join.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp.
Module F_fmt_fp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_splitH.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.FmtFp_facts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2.F_fmt_fp_pre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_pre2 F_fmt_fp_pre3 F_fmt_fp_pre4.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.FmtFp_facts2.F_frexpl.U_frexpl_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_sscanf.F_divtf3_main.U_divtf3_spec_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c.

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
Definition FMT_FP_DEPTH : Z := 4640.

(* [comment removed for export] *)
Definition fmt_fp_facts (y fl p t : Z) : Prop :=
  yn_fact y /\ yn_fact (Z.lxor y F128_SIGNBIT)
  /\ dig_words_fact y fl /\ e2_range_fact y fl /\ dn_phase_fact y fl p t
  /\ words_all_fact y fl p t /\ carry_fact y fl p t /\ azr_fact y fl p t
  /\ below_a_fact y fl p t.

Definition fmt_fp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (o0 o1 : list Z) (junk0 : list byte)
    (canary : word) (ret : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - FMT_FP_DEPTH, bv_unsigned sp);
              (B + Z.of_nat (length o0), B + Z.of_nat (length o1));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ frm0 fc'
    /\ stk usegs m' (bv_unsigned sp - FMT_FP_DEPTH) (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (zb o1) (skipn (length o1 - length o0) junk0)
    /\ ssp_cells m' canary
    /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

Definition fmt_fp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
         (w p fl t : Z) (o0 o1 : list Z) (ret : Z),
    let y := (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z in
    let Fp := bv_unsigned a0 in
    fmt_fp o0 y w p fl t = Some (o1, ret) ->
    fmt_fp_facts y fl p t ->
    (5152 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^63)%Z -> (347200 <= bv_unsigned sp - FMT_FP_DEPTH)%Z ->
    (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
    (-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z -> (length junk0 < 256)%nat ->
    stk usegs m (bv_unsigned sp - FMT_FP_DEPTH) (bv_unsigned sp) ->
    mem_inv usegs m ->
    frm0 fc ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt usegs (fmt_fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp fl0 j1 j2 lbfw B o0 o1 junk0 canary ret m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19fd4) fc None m (seg_rom usegs)).

Lemma fmt_fp_spec : fmt_fp_stmt.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp.fmt_fp_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp.fmt_fp_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp.fmt_fp_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp.fmt_fp_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp.fmt_fp_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
#[export] Instance U_fmt_fp_contract : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp.fmt_fp_contract := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp.fmt_fp_contract_ok.
End F_fmt_fp.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
Import F_fmt_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition num_gch (c : Z) : Prop := 48 <= c <= 57 \/ c = 43 \/ c = 45 \/ c = 46 \/ c = 69 \/ c = 101.

Definition NUM_FMT_G_TOTAL : Prop :=
  forall d p1, ((d mod 2^64) / 2^52) mod 2^11 <> 2047 -> (p1 = 15 \/ p1 = 17) ->
    exists txt, fmt_g d p1 = Some (txt, zlength txt) /\ Forall num_gch txt /\ zlength txt <= p1 + 8.

Definition NUM_FMT_D_TOTAL : Prop :=
  forall x, exists o, fmt_d x = Some (o, zlength o) /\ Forall num_gch o /\ zlength o <= 22 /\ (- 2^31 <= x < 2^31 -> zlength o <= 11).

Definition NUM_FMT_G_FACTS : Prop :=
  forall d prec o r, (prec = 15 \/ prec = 17) -> fmt_g d prec = Some (o, r) -> F_fmt_fp.fmt_fp_facts (f128_of_d d) 0 prec CHR_g.

Definition NUM_SSCANF_JUNK : Prop :=
  forall t junk, Forall (fun c => FmtFp_facts3.is_numch c = true) t ->
    scan_sscanf_lg (t ++ 0 :: junk) = scan_sscanf_lg (t ++ [0]).
