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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_strnlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Gt_shgetc.
Module F_shgetc_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.Gt_shgetc.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].

(* [comment removed for export] *)

Definition SHLIM : Z := 0x1d5f4.
Definition SHGETC : Z := 0x1d62c.
Definition UFLOW : Z := 0x1d6f4.
Definition TOREAD : Z := 0x1d560.
Definition STRING_READ : Z := 0x1c97c.

(* [comment removed for export] *)
Definition got_ssp := 0x224e8%Z.
Definition ssp_guard := 0x53af8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].
(* [comment removed for export] *)

Definition M64 : Z := 18446744073709551615.

(* [comment removed for export] *)
Definition rf_rend (T p : Z) (w : bool) (f : shfile) : Z :=
  if sh_stdio f then (if w then T + p else T) else M64.

Definition rf_cells (T p : Z) (w : bool) (f : shfile) (J : rfj) : list cell :=
  let rend := rf_rend T p w f in
  [C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
   C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
   C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
   C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
   C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
   C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)); C8 (Z_to_bv 64 (- sh_cnt0 f));
   C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

(* [comment removed for export] *)
Definition rf_cells_raw (T p : Z) (w : bool) (f : shfile) (J : rfj) (she shl shc : word) : list cell :=
  let rend := rf_rend T p w f in
  [C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
   C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
   C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
   C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
   C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
   C8 she; C8 shl; C8 shc;
   C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

(* [comment removed for export] *)
Definition ssJ : rfj :=
  mkJ (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
      (Z_to_bv 64 STRING_READ) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 M64) (Z_to_bv 64 M64) (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition RFI (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
  sh_ok T txt f /\ (-1 <= c < 256)%Z /\
  (sh_shlim_neg f = false -> kmin <= sh_rpos f)%Z /\
  (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
  (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
                        (w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ /\ 0 <= sh_cnt0 f <= sh_rpos f)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shlim_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (w : bool) (f : shfile) (J : rfj) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(Fp, Fp + 232)%Z] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' Fp (rf_cells T p w (sh_lim0 f) J).

Definition shlim_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (txt : list Z) (f : shfile) (J : rfj) (she shl shc : word),
  rw_cells psegs m Fp (rf_cells_raw T p w f J she shl shc) ->
  sh_ok T txt f -> length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat ->
  (0 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= p <= zlength txt)%Z ->
  mem_inv psegs m ->
  evt psegs (shlim_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p w f J m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHLIM) fc None m (seg_rom psegs)).

Ltac show_goal := match goal with |- ?g => idtac g end.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero4 : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition w0 : word := Z_to_bv 64 0.
(* [comment removed for export] *)
Definition ss_cells (T rpos rend : Z) (mode : word) (cookie shend : Z) (shl shc : word) : list cell :=
  [C4 w0; CB 4 zero4; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend);
   C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C8 (Z_to_bv 64 STRING_READ); C8 w0; C8 w0;
   C8 (Z_to_bv 64 T); C8 w0; C8 w0; C8 w0; C4 w0; C4 w0; C8 w0;
   C4 mode; C4 (Z_to_bv 64 M64); C4 w0; CB 4 zero4;
   C8 (Z_to_bv 64 cookie); C8 w0; C8 w0; C8 w0;
   C8 (Z_to_bv 64 shend); C8 shl; C8 shc;
   C8 w0; C8 w0; C8 w0].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition toread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T cookie shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 16, q); (Fp, Fp + 232)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (q - 16) (q)
    /\ rw_cells psegs m' Fp (ss_cells T T T (Z_to_bv 64 M64) cookie shend shl shc).

Definition toread_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T rpos rend cookie shend : Z) (mode shl shc : word),
  rw_cells psegs m Fp (ss_cells T rpos rend mode cookie shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  (0 <= T /\ T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= cookie < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  stk psegs m (q - 16) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv psegs m ->
  evt psegs (toread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T cookie shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TOREAD) fc None m (seg_rom psegs)).
#[export] Instance P_shlim_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_Scan_iface.G_shgetc_A.shlim_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_Scan_iface.G_shgetc_A.shlim_spec_c_ok.
#[export] Instance P_toread_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_Scan_iface.G_shgetc_A.toread_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_Scan_iface.G_shgetc_A.toread_spec_c_ok.
End F_shgetc_A.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_scanexp.
From Ltac2 Require Ltac2.
Module F_shgetc_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.
Export F_shgetc_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c F_shgetc_A.P_shlim_spec_c F_shgetc_A.P_toread_spec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.

Module H4S.
  Import Ltac2.
  Ltac2 prune_share () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_share1 () : unit := Control.enter prune_share.
End H4S.
Local Ltac h4_prune_share := ltac2:(H4S.prune_share1 ()).
Local Ltac share_tier := solve [ sf_unhide; h4_prune_share; Zify.zify; xlia zchecker ].
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | share_tier | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
  txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
  ((T + zlength txt) mod 8 = 0)%Z /\ (zlength txt <= 256)%Z.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.

(* [comment removed for export] *)
Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ bytes_at psegs m' A buf.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at psegs m' Src src.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (q - 64) (q)
    /\ rw_cells psegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) mode (T + p) shend shl shc)
    /\ rw_cells psegs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
    /\ bytes_at psegs m' T (zbytes txt).

Definition sread_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
  rw_cells psegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at psegs m T (zbytes txt) -> rw_cells psegs m D [CB 1 [dj]] ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk psegs m (q - 64) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 64 \/ q <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv psegs m ->
  evt psegs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRING_READ) fc None m (seg_rom psegs)).
#[export] Instance P_sread_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc_B.sread_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc_B.sread_spec_c_ok.
End F_shgetc_B.

(* [comment removed for export] *)
Module F_shgetc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.
Export F_shgetc_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c F_shgetc_B.P_sread_spec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Module H4S.
  Import Ltac2.
  Ltac2 prune_share () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_share1 () : unit := Control.enter prune_share.
End H4S.
Local Ltac h4_prune_share := ltac2:(H4S.prune_share1 ()).
Local Ltac share_tier := solve [ sf_unhide; h4_prune_share; Zify.zify; xlia zchecker ].
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | share_tier | tlia | split; [ tlia | exact I ] ].


Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Local Ltac br01 K := brf K; [ | exfalso; lia ].
(* [comment removed for export] *)
Local Ltac lia_goal_g P := lazymatch P with
  | (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
  | (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
  | ?A /\ ?B => lia_goal_g A; lia_goal_g B | ?A \/ ?B => lia_goal_g A; lia_goal_g B | ?A -> ?B => lia_goal_g B | ~ _ => idtac
  | ?A <-> ?B => lia_goal_g A; lia_goal_g B | False => idtac | True => idtac
  end.
Local Ltac glia := lazymatch goal with |- ?G => lia_goal_g G end; lia.
Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (q - 128) (q)
    /\ rw_cells psegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
    /\ bytes_at psegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition uflow_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
  rw_cells psegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at psegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk psegs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 128 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 128)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv psegs m ->
  evt psegs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 UFLOW) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (q - 160) q
    /\ rw_cells psegs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
    /\ bytes_at psegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition shgetc_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells psegs m Fp (rf_cells T p w f ssJ) ->
  sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
  sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at psegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk psegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 160 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 160)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv psegs m ->
  evt psegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom psegs)).
#[export] Instance P_uflow_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.uflow_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.uflow_spec_c_ok.
#[export] Instance P_shgetc_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.shgetc_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.shgetc_spec_c_ok.
End F_shgetc.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_lib.
Module F_rfile.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c F_shgetc.P_uflow_spec_c F_shgetc.P_shgetc_spec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


(* [comment removed for export] *)
Definition RFJ (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
  sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
  (sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
  (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
  (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
                        (w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ)%Z.
(* [comment removed for export] *)

Open Scope bv_scope.
#[export] Instance P_shgetc_callJ_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_rfile.shgetc_callJ_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_rfile.shgetc_callJ_c_ok.
End F_rfile.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fwritex.
Module F_fwritex_gen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.


Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma memcpy_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at psegs m Src src -> length src = Z.to_nat N -> rw_cells psegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv psegs m ->
  evt psegs (F_shgetc_B.memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x209e8) fc None m (seg_rom psegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply F_memcpy.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold F_memcpy.memcpy_post, F_shgetc_B.memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.

(* [comment removed for export] *)
Definition fwx_nofit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp S l wfn lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 wfn) t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 wfn) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp).

Lemma fwx_nofit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
  rw_cells psegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  (0 < wend < 2^64) -> (0 <= wpos <= wend) -> (wend - wpos < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
  mem_inv psegs m ->
  (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  evt psegs (fwx_nofit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp S l wfn lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17554) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros FC -> -> -> WEND WPOS L SR WFN WFE ST LO LO0 MI SEPF.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold file_cells in FC.
  carve_frame 64%nat ST.
  do 13 step.
  if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
  do 3 step.
  if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
  do 13 step.
  rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
  release_frame FR ST (bv_unsigned sp).
  unfold fwx_nofit_post. sys_finish.
Qed.


(* [comment removed for export] *)
Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
    /\ rw_cells psegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
    /\ bytes_at psegs m' S src.

Lemma fwx_tail : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells psegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells psegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells psegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at psegs m S src -> Z.of_nat (length src) = l ->
  stk psegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono psegs m0 m -> mem_inv psegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
  evt psegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1764c) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  unfold file_cells in FC.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB psegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (F_fwritex.rw_cells_app psegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  call memcpy_callw.
  1:{ exact SRC. }
  1:{ rewrite Nat2Z.id. reflexivity. }
  1:{ rewrite Nat2Z.id. exact DSTa. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
  rewrite !Nat2Z.id in *.
  change psegs with psegs in *.
  do 4 step.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells psegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (apply (proj2 (F_fwritex.rw_cells_app psegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
  end.
  cbn [app] in DST'. rewrite !LEN in *.
  unfold fwx_ret_post, file_cells. sys_finish.
Qed.


(* [comment removed for export] *)
Lemma fwx_fit_plain : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l lo : Z),
  rw_cells psegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells psegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
  bytes_at psegs m S src -> Z.of_nat (length src) = l ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  (0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
  (2^31 <= lbf < 2^32) ->
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) -> (bv_unsigned sp < 2^63) ->
  mem_inv psegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
  evt psegs (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17554) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold file_cells in FC.
  carve_frame 64%nat ST.
  do 13 step.
  if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
  do 3 step.
  if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
  do 3 step.
  pose proof (F_fwritex.sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
  specialize (NEG ltac:(lia)).
  if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
  eapply fwx_tail; [exact FR | exact FC | exact DST | lia | exact SRC | exact LEN | exact ST | lia | lia | exact MU | exact WM | exact MI | lia ..].
Qed.
End F_fwritex_gen.

(* [comment removed for export] *)
Module F_scanexp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls F_shgetc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib F_rfile.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib.F_fmt_fp_calls.P_fpclassifyl_callv_c F_shgetc.P_uflow_spec_c F_shgetc.P_shgetc_spec_c F_rfile.P_shgetc_callJ_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac step ::= step2. Local Ltac stepz ::= step2.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.

  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac brsf K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
    repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
    first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac].
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Local Ltac br01 K := brf K; [ | exfalso; lia ].
  (* [comment removed for export] *)
Local Ltac zsimp_in_w H :=
    try (match type of H with
         | context [v_sltu _ _] => idtac | context [v_slt _ _] => idtac
         | context [v_sltiu _ _] => idtac | context [v_slti _ _] => idtac end;
         rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H);
    try (match type of H with context [zxb] => cbv delta [zxb] in H end);
    zb_fold_lits_in H;
    repeat match type of H with
    | context [bv_unsigned (Z_to_bv 64 ?e)] => zs_wrap_in e H
    | _ => progress (zs_idioms_in H)
    end; zb_fold_lits_in H.
Local Ltac brfw K := if_cases K; rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in K;
    unfold bv_eqb, bv_ltu, bv_lts, bv_leu in K; fold_lit_ux_in K; zsimp_in_w K; zify_bool K;
    try (rewrite ?signed_of_Z in K by lia).
(* [comment removed for export] *)
Local Ltac lia_goal_g P := lazymatch P with
  | (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
  | (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
  | ?A /\ ?B => lia_goal_g A; lia_goal_g B | ?A \/ ?B => lia_goal_g A; lia_goal_g B | ?A -> ?B => lia_goal_g B | ~ _ => idtac
  | ?A <-> ?B => lia_goal_g A; lia_goal_g B | False => idtac | True => idtac
  end.
Local Ltac glia := lazymatch goal with |- ?G => lia_goal_g G end; lia.
Definition SCANEXP : Z := 0x1f520.
Definition SCANEXP_DEPTH : Z := 240.

(* [comment removed for export] *)
Definition scanexp_tail (fuelc : nat) (neg c : Z) (f : shfile) : option (shfile * Z) :=
  if negb (isdigitc c) then Some (sh_unget f, LLONG_MIN_) else
  match scanexp_l1_loop fuelc (0%Z, c, f) with
  | None => None
  | Some (x, c, f) =>
    match scanexp_l2_loop fuelc (x, c, f) with
    | None => None
    | Some (y, c, f) =>
      match scanexp_l3_loop fuelc (c, f) with
      | None => None
      | Some (c, f) => Some (sh_unget f, if nz neg then (- y)%Z else y)
      end end end.

Definition scanexp_rpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) (e10 : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' k' c',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (q - SCANEXP_DEPTH) q
    /\ rw_cells psegs m' Fp (rf_cells T p true fR J)
    /\ RFJ T txt p true J k' c' fR /\ (1 <= k')%Z
    /\ bytes_at psegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition scanexp_rstmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z),
  scanexp fuelc f0 pok = Some (fR, e10) ->
  rw_cells psegs m Fp (rf_cells T p true f0 J) -> RFJ T txt p true J kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
  (sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre) ->
  Forall (fun c => 0 <= c < 256)%Z txt -> (0 <= p < zlength txt)%Z -> znth txt p = 0%Z ->
  bytes_at psegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk psegs m (q - SCANEXP_DEPTH) q -> (4096 <= q - SCANEXP_DEPTH)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= pok <= 1)%Z -> (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv psegs m ->
  evt psegs (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCANEXP) fc None m (seg_rom psegs)).
#[export] Instance P_scanexp_rspec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.scanexp_rspec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.scanexp_rspec_c_ok.
End F_scanexp.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.
Import F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.P_memset_contract F_shgetc_A.P_shlim_spec_c F_shgetc_A.P_toread_spec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Notation mem := (word -> option byte).

Definition RSTRTOD : Z := 0x20878.
Definition RSSCANF : Z := 0x179dc.
Definition RFMT_LG : Z := 0x102a8.            (* [comment removed for export] *)
Definition RATP : Z := 0x33890.               (* [comment removed for export] *)
Definition RERRNO : Z := 0x337ec.             (* [comment removed for export] *)
Definition RGLOBALS_TOP : Z := 0x55000.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RSTRTOD_DEPTH : Z := 8928.         (* [comment removed for export] *)
Definition RSSCANF_DEPTH : Z := 9504.         (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rstrtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PE : Z) (txt : list Z) (npre bits used lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (PE, PE + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ reg_get F' 10 = Z_to_bv 64 bits
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' PE [C8 (Z_to_bv 64 (T + used))]
    /\ bytes_at psegs m' T (map (Z_to_bv 8) txt)
    /\ ssp_cells m' canary
    /\ rw_cells psegs m' RERRNO [C4 ev']
    /\ 0 <= used <= npre.      (* [comment removed for export] *)

Definition rstrtod_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
    bytes_at psegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat -> zlength txt <= 2^40 ->
    rw_cells psegs m PE [C8 ejunk] ->
    scan_strtod txt = Some (bits, used) ->
    stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSTRTOD_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
    bv_unsigned sp <= T -> T + 2^41 <= 2^63 -> bv_unsigned sp <= PE -> PE + 8 <= 2^63 ->
    (PE + 8 <= T \/ T + zlength txt <= PE) ->
    ssp_cells m canary -> rw_cells psegs m RERRNO [C4 ev] ->
    mem_inv psegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
    evt psegs (rstrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RSTRTOD) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rsscanf_lg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PD : Z) (txt : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (PD, PD + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' PD [C8 (match res with Some bits => Z_to_bv 64 bits | None => djunk end)]
    /\ bytes_at psegs m' T (map (Z_to_bv 8) txt)
    /\ ssp_cells m' canary
    /\ rw_cells psegs m' RERRNO [C4 ev'].

Definition rsscanf_lg_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
    bytes_at psegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
    (T + zlength txt) mod 8 = 0 -> zlength txt <= 256 ->     (* [comment removed for export] *)
    rw_cells psegs m PD [C8 djunk] ->
    scan_sscanf_lg txt = Some (r, res) ->
    stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSSCANF_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
    bv_unsigned sp <= T -> T + 2^41 <= 2^63 -> bv_unsigned sp <= PD -> PD + 8 <= 2^63 ->
    (PD + 8 <= T \/ T + zlength txt <= PD) ->
    ssp_cells m canary -> rw_cells psegs m RERRNO [C4 ev] ->
    mem_inv psegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 RFMT_LG -> a2 = Z_to_bv 64 PD ->
    evt psegs (rsscanf_lg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RSSCANF) fc None m (seg_rom psegs)).
