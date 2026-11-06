(* The walk of pin_set_words on the ASan build of plugin-hostd/fuzz_command (0x8e66c, 94 instructions): the
   contract tpin_set_words_spec (lib/A/Prog/pin_set_words_c.v) from the four segments of the walk, in the layout of
   cgif_file_fuzzer's cgif_close walk (A/ACh1.v..ACh8.v, AChc.v) and fuzz_command's chain_words walk:

     pin_set_words_h.v   entry .. MID   the arity test, strlen(line), tok[3] and the inlined strcmp(tok[3], "-")
     pin_set_words_m.v   MID .. JOIN    ntok = 4, or ntok = 5 with strncmp(tok[4], "verdict=", 8)
     pin_set_words_ta.v  JOIN .. K2     tok[1], tok[2] and the call of pins_set
     pin_set_words_tb.v  K2 .. ret      lv2_refusals_forget(NULL) when pins_set accepted; the epilogue

   over the interface lib/A/Prog/pin_set_words_s4.v (the statement's binders as a context record, its premises
   psw_pre, its post psw_post, and the cut-point invariants INV_MID, INV_JOIN, INV_K2). Statement passes 4 and 5
   apply: the post is apost_baseF, pins_set returns at some FP
   state fx1 (it reaches the snprintf wrapper under answer_code), so the segment after it (Tb) is taken at fx1 and
   lifted (PaFx.v); the callee and runtime contracts are taken at every FP state.

   Section hypotheses: the four the statement names (the two recorder callees' contracts and the two string
   entries of lib/A/Rt/RtString.v), and the per-binary record facts with their final names: TL, HB, IMG,
   MTL, SIGP. The segments take a live block's word tail as a named premise; here it is CmdRecImg.v's
   cmd_heap_tail_vis. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdChk CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import pins_set_c lv2_refusals_forget_c pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import pin_set_words_s4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
pin_set_words_h pin_set_words_m pin_set_words_ta pin_set_words_tb.
Import ListNotations.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's Section hypotheses (pin_set_words_c.v:89-93) *)
Hypothesis PINS_SET : forall fx0 : YK11.FPState, @tpins_set_spec fx0 rc SK PI B MT.
Hypothesis LV2_REFUSALS_FORGET : forall fx0 : YK11.FPState, @tlv2_refusals_forget_spec fx0 rc SK PI B MT.
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
(* the per-binary record facts *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* a live block's word tail (CmdRecImg.v:33, CmdRecFacts group (c)) *)
Let HTAIL := cmd_heap_tail_vis SEGS B LAWS HB.

Theorem pin_set_words_proved : tpin_set_words_spec B MT.
Proof.
unfold tpin_set_words_spec.
intros ly S W regs mem md ch line nl tok ntok cb ncb T ptrs tks R O
HPRE HFRM HROD H10 Hl64 H11 Ht64 H12 Hlb Hlo HlT HlN HOBJ HTOKS Hcb Hcbo Hntk Hntok Hverb
HREC Hdecl Hcalls HRO HVO Hfr HEV HLIVE HMO.
set (c := mkPSWX ly S W regs mem md ch line nl tok ntok cb ncb T ptrs tks R O).
assert (HP : psw_pre B MT c)
by exact (mkPswPre B MT c HPRE HROD H10 Hl64 H11 Ht64 H12 Hlb Hlo HlT HlN HOBJ HTOKS Hcb Hcbo Hntk Hntok Hverb
  HREC Hdecl Hcalls HRO HVO Hfr HEV HLIVE HMO).
(* the segment after pins_set at the FP state pins_set returns (PaFx.v, statement pass 4) *)
pose proof (fun fx1 : YK11.FPState => psw_Tb (fx := fx1) B MT TL HB IMG MTL SIGP (LV2_REFUSALS_FORGET fx1) c HP) as FK2.
pose proof (psw_Ta B MT HB IMG MTL SIGP (PINS_SET fx) HTAIL c HP HFRM FK2) as FJ.
pose proof (psw_M B MT TL HB MTL (STRNCMP fx) HTAIL c HP FJ) as FM.
exact (psw_H B MT TL MTL (STRLEN fx) HTAIL c HP FM).
Qed.
End e.
End f.
End d.
