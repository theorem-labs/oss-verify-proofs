(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame SReach HeapCeil Spec SymRun RefPrintfLib
  LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0
  CXXRep Fuzz_stmt AsPrintfFirst.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat37Corelib7Numbers7BinNumsi34Nposi31Z35stdpp9bitvectorbdefinitionsk72bv37Corelib5Lists7ListDefm93nthk77Z_to_bvk7bbv_unsigned89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsDrvDefs4FPX1~~~~~~pe5hdr_b46Stdlib6ZArith6BinInt1Zua3addua6moduloua3mulua6to_nat01Spe7hdr_cfgua3sub06lengthua6of_nat37Corelib4Init5Peanohk42lepe9hdr_calls37Corelib4Init5Logichma3andua2leua2lt06option04Nonehma2eq04Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshq9h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hv53rdn69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~ij7floaded_segmentsua3pow04prod04pair04cons03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~iq15as_TRiq18trace_okiq19APC0_FREEiq1bAPC0_MALLOCiq15pf_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9Fuzz_stmt~~~~~~jh87PF_FUZZjh8afuzz_tr_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsDrvDefs~~~~~~jn09hdr_callsjn0fhdr_payload_leniq15as_Cfiq15as_Cmjh89fuzz_costhq9dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runjvf5mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statekj45Model3h5LinuxProcessSemantics5Riscv7Preludekmb5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~kpa5asegsiq15as_St69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ku7dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~lif8realizeskj45event89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsDrvDefs9TargetRun~~~~~~lnf7ATRpostlnf6ATRpreiq15blockiq14bptrhv57FPStatelif4TSetlif6t_emit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~mgb1Wiq13asr" s.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition hdr_b : ltac2:(zQ "50!h8!he!jc!k3!m4>4data@1$0@1$4@1$2#8>1i$1$3") := ltac2:(zQ "70!jc!m4!h8!he!o0!o6!p0\4data@1$2@1$1@1$0#8\1i$3@2$6@1$0#8@4$4@1$1@1$0#8^1^2@2$5@1$0#8Z").
Definition hdr_cfg : ltac2:(zQ "40!h8!jc!k3!m4>4data@1$0@1$3@1$1#8$2") := ltac2:(zQ "70!u2!h8!jc!hg2!hg8!hh1!m4\4data@1$1@1$6@1$2#8@2$4@2$3@2$0^1N0@2$5+hg0@2$0^1N1+ogg0").   (* [comment removed for export] *)
Definition hdr_calls : ltac2:(zQ "40!h8!he!jc!m4>4data@1$0@1$3@1$2#8$1") := ltac2:(zQ "90!he!hh7!hi0!h8!jc!u2!hi3!hg8!m4\4data@1$3@1$8@1$4#8M0\1x$0$0@1$1@1$6^1N1\1n$0@1$2@1$1@2$7@2$5^2N2+4").
Definition hdr_payload_len : ltac2:(zQ "40!h8!jc!k3!m4>4data@1$0@1$3@1$1#8$2") := ltac2:(zQ "70!jc!hid!m4!hj3!h8!hi3!hjb\4data@1$4@1$2@1$0#8@2$1@2$1@1$6@2$3@1$2@1$0#8^1+6@1$5^1").

Lemma hdr_calls_range : ltac2:(zQ "60!hl8!hle!h8!hne!jc!m4>4data@1$2@1$5@1$4#8@2$3@2$0N1@1$1^1@2$0@1$1^1N4").
Proof.
  intros data. unfold hdr_calls. destruct (Z.to_nat (hdr_cfg data)); [lia|].
  pose proof (Z.mod_pos_bound (hdr_b data 2) 4 ltac:(lia)). lia.
Qed.
Lemma hdr_cfg_range : ltac2:(zQ "70!hi3!h8!hne!jc!ho5!hoa!m4>4data@1$1@1$6@1$3#8@2$2@2$4Z@1$0^1@2$5@1$0^1+ogg0").
Proof. intros data. unfold hdr_cfg. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aro_none : ltac2:(zQ "30!jc!m4!hof>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "a0!jc!m4!hof!hp7!hne!hpd!k3!ho5!hoa!o6\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1i$6>0@2$4@2$7+hggg0^1@2$8^1+mngg0@3$5@1$2@1$1@1$0#8@1^3@2$9@1$0#k0^2@1$3@1$1@1$0#8").
Definition arelro_none : ltac2:(zQ "30!jc!m4!hof>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "a0!jc!m4!hof!hp7!hne!hpd!k3!ho5!hoa!o6\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1i$6>0@2$4@2$7+hqqgg0^1@2$8^1+hrkgg0@3$5@1$2@1$1@1$0#8@1^3@2$9@1$0#k0^2@1$3@1$1@1$0#8").

(* [comment removed for export] *)
Definition aglb_none : ltac2:(zQ "30!jc!m4!hof>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "a1!jc!m4!hof!hne!hp7!hpd!k3!ho5!hoa!o6&@3$5@1$2@1$1@1$0#8@1^3@2$9@1$0#k0^2@1$4@1$1@1$0#8\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$3>1i$6>0@2$3@2$7+hrmug8^1@2$8^1+hrmuh0~0>1i$6>0@2$3@2$7+hrmuv8^1@2$8^1+hrpqs0~0").

(* [comment removed for export] *)
Definition atid_cell : ltac2:(zQ "40!jc!m4!hof!k3>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>3tid$3P") := ltac2:(zQ "e0!jc!m4!h8!hof!hne!hoa!o6!hq3!hpd!k3!hu0!ij0!in1!io4\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\3tid$9@2$4@3$8@1$3@1$2@1$1@1$0#8@4$b$c^2@2$6@1$0#k0+mvhin0N4@2$7@1$2@1$1@1$0#8@2$aN4@2$6@1$0#k0^1@2$4@2$5Z^1@2$5^1@2$d+2+h6").
(* [comment removed for export] *)
Definition acanary : ltac2:(zQ "40!jc!m4!hof!k3>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>3can$3P") := ltac2:(zQ "f0!jc!m4!h8!hof!hne!o6!hq3!hpd!k3!hu0!ij0!in1!ho5!hoa!io4\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\3can$8@2$4@3$7@1$3@1$2@1$1@1$0#8@4$a$b^2@2$5@1$0#k0+nhhjl8N8@2$6@1$2@1$1@1$0#8@2$9N8@2$5@1$0#k0^1@2$4@2$cZ^1@2$d^1@2$e+2+k0").

(* [comment removed for export] *)
Definition adrv_cells : ltac2:(zQ "40!ioa!k3!h8!he@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!k3!ioa!he!ip0!ip6!ipc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmti0N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmti8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtj0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtl8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtm8N8+hporm0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtn8N8+nhhrj0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmto0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtp8N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtq8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtqcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtr0N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhlo8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhlqbN1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrprh0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkho0N8+hrkho0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhri0N8Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition adrv_ax1 : ltac2:(zQ "40!ioa!k3!h8!he@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!k3!ioa!he!ip0!ip6!ipc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+muvnt0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+muvnt4N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjm8N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjmcN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjn0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjn8N8+nhhjo0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjo0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjo8N8+hphii0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhko8N8+qujhc@1$5@2$1@2$1$0$2$0").
(* [comment removed for export] *)
Definition adrv_ax2 : ltac2:(zQ "40!ioa!k3!h8!he@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!k3!ioa!he!ip0!ip6!ipc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+muvnt0N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+muvnt4N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjm8N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjmcN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjn0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjn8N8+nhhjo0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjo0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjo8N8+hphii0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhko8N8+qujhc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjp0N8+hphii0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhkp0N8+rusu4@1$5@2$1@2$1$0$2$0").
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition astdout0 : ltac2:(zQ "40!ioa!k3!h8!he@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!k3!ioa!he!ip0!ip6!ipc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuh0N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuh8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmui0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuj0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuj8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuk8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmul8N8+hppolc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmum8N8+nhhrj8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmun0N8+kg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuo8N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmup8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmupcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuq0N4+a@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Record astdout_after (mem : word -> option byte) (k : nat) : Prop := ASOA {
  so_flags : rdn RSEGS mem (Z_to_bv 64 0x1b6e10) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  so_rpos  : rdn RSEGS mem (Z_to_bv 64 0x1b6e18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_rend  : rdn RSEGS mem (Z_to_bv 64 0x1b6e20) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_wend  : rdn RSEGS mem (Z_to_bv 64 0x1b6e30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x711f38));
  so_wpos  : rdn RSEGS mem (Z_to_bv 64 0x1b6e38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x711b38 + 2 * Z.of_nat k)));
  so_wbase : rdn RSEGS mem (Z_to_bv 64 0x1b6e48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x711b38));
  so_write : rdn RSEGS mem (Z_to_bv 64 0x1b6e58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x198b60));
  so_buf   : rdn RSEGS mem (Z_to_bv 64 0x1b6e68) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x711b38));
  so_bsz   : rdn RSEGS mem (Z_to_bv 64 0x1b6e70) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  so_fd    : rdn RSEGS mem (Z_to_bv 64 0x1b6e88) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  so_mode  : rdn RSEGS mem (Z_to_bv 64 0x1b6e98) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_lock  : rdn RSEGS mem (Z_to_bv 64 0x1b6e9c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_lbf   : rdn RSEGS mem (Z_to_bv 64 0x1b6ea0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_bytes : rdn RSEGS mem (Z_to_bv 64 0x711b38) (2 * k) = Some (zero_lines k) }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ATR_STACK : Z := 65536.
End FPX1.

Section TargetRun.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!mk7$0").

  (* [comment removed for export] *)
  Definition adrv_traces : ltac2:(zQ "00P") := ltac2:(zQ "c0!k3!ipc!hne!ite!ip6!iu7!iv3!jg0!ioa!jgf!jl7!jm2@2$2@3$5@1$3?1H$7@3$4$0+ruph0@1$1$0@2$2@3$5@1$3?1H$7@3$4$0+rupm4@1$1$0@2$2@3$5@1$3?1H$6@3$4$0+rupo8@1$1$0@2$2@3$5@1$3?1H$6@3$4$0+ruqr8@1$1$0@2$2@3$5@1$3?1H$7@3$4$0+rurv0@1$1$0@2$2@3$5@1$3?1H$6@3$4$0+ruso4@1$1$0@2$2@4$9@1$3?1H$a+rusl8@1$1@2$8$0$0@1$b?1H").

  (* [comment removed for export] *)
  Definition atr_cost : ltac2:(zQ "40!h8!jc!k3!m4>4data@1$0@1$3@1$1#8$2") := ltac2:(zQ "c0!hg2!h8!jc!k3!jqf!jrc!jsf!jt8!ju1!hh1!hjb!m4\4data@1$1@1$b@1$2#8=1N$3@1$5^1@2$0@2$0@2$7?1H^1@2$6?1H^1@2$9@1$a@1$4^2@2$8?1H^1").

  (* [comment removed for export] *)
  Record atr_statics (ax : list (Z * nat * Z)) (sp : word) (mem : word -> option byte) : Prop := ATRS {
    ats_inv   : mem_inv asegs mem;
    ats_ac    : ACONST mem;
    ats_ax    : cells_ok mem ax;               (* [comment removed for export] *)
    ats_bj    : bj_statics mem;                (* [comment removed for export] *)
    ats_relro : arelro_none mem;
    ats_glb   : aglb_none mem;                 (* [comment removed for export] *)
    ats_cells : cells_ok mem adrv_cells;
    ats_tid   : exists tid, atid_cell mem tid;
    ats_errno : exists e, rw_cells asegs mem AERRNO [C4 e];
    ats_can   : exists can, acanary mem can;
    ats_rfs   : as_RFS H [] mem;
    ats_sh0   : exists shi, stack0 mem (bv_unsigned sp - ATR_STACK) shi /\ bv_unsigned sp <= shi }.

  (* [comment removed for export] *)
  Record ATRpre (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block)
                (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte) : Prop := ATRPRE {
    (* [comment removed for export] *)
    atr_vis  : as_VIS H s msF = mkst regs (Z_to_bv 64 0x0beb8c) mem (seg_rom asegs);
    atr_krel : as_AKREL H s (mkCfg msF mo);
    (* [comment removed for export] *)
    atr_ra  : getr regs 1 = Z_to_bv 64 0x0bea30;
    atr_sp  : getr regs 2 = sp;
    atr_tp  : getr regs 4 = Z_to_bv 64 ATP;
    atr_a0  : getr regs 10 = Z_to_bv 64 (A + 2);                                  (* [comment removed for export] *)
    atr_a1  : getr regs 11 = Z_to_bv 64 (hdr_cfg data);                           (* [comment removed for export] *)
    atr_a2  : getr regs 12 = Z_to_bv 64 (A + 2 + hdr_cfg data + 4);                (* [comment removed for export] *)
    atr_a3  : getr regs 13 = Z_to_bv 64 (hdr_payload_len data);                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    atr_len6  : 6 + hdr_cfg data <= Z.of_nat (length data);
    atr_lenhi : Z.of_nat (length data) < MAX_INPUT;
    (* [comment removed for export] *)
    atr_sp16  : bv_unsigned sp mod 16 = 0;
    atr_splo  : aceil + ATR_STACK + 4096 <= bv_unsigned sp;
    atr_sphi  : bv_unsigned sp + 128 <= 0x800000000000;
    atr_stk   : stk_ok RSEGS mem sp ATR_STACK;
    atr_stkcj : stk asegs mem (bv_unsigned sp - ATR_STACK) (bv_unsigned sp);
    (* [comment removed for export] *)
    atr_rheap : as_RHEAP H s LB mem;
    atr_blk   : In (p, A, cap) LB;
    atr_lb1   : lb_bytes LB <= 2 ^ 27 /\ Z.of_nat (length LB) <= 2;
    atr_al    : atr_cost data <= as_AL H s;
    atr_aux   : exists B, as_rauxv_ok H mem B /\ bv_unsigned sp + 128 <= B < 2 ^ 64;
    (* [comment removed for export] *)
    atr_cap   : Z.of_nat (length data) <= cap;
    atr_data  : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    atr_addr  : addressable mem A cap;
    atr_cb    : exists junk, rw_cells asegs mem A [CB (Z.to_nat cap) junk];   (* [comment removed for export] *)
    (* [comment removed for export] *)
    atr_st    : atr_statics adrv_ax1 sp mem;
    atr_out   : cells_ok mem astdout0;        (* [comment removed for export] *)
    atr_frm   : FP.frm0 (@fp_csr fx);          (* [comment removed for export] *)
    (* [comment removed for export] *)
    atr_tr    : adrv_traces;
    atr_live  : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H;
    (* [comment removed for export] *)
    atr_fd1   : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    atr_fd2   : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record ATRpost (fx' : FPState) (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block) (mo : Model)
                 (regs : bvmap 5 word) (mem : word -> option byte)
                 (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H) : Prop := ATRPOST {
    atq_vis  : as_VIS H s' msF' = @mkst fx' regs' (Z_to_bv 64 0x0bea30) mem' (seg_rom asegs);
    atq_frm  : FP.frm0 (@fp_csr fx');
    atq_krel : as_AKREL H s' (mkCfg msF' mo');
    atq_mpres : as_MPRES H mo mo';
    atq_sp   : getr regs' 2 = sp;
    atq_tp   : getr regs' 4 = Z_to_bv 64 ATP;
    atq_a0   : getr regs' 10 = Z_to_bv 64 0;                                      (* [comment removed for export] *)
    atq_cs   : forall r : reg, In r ([8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list reg) -> getr regs' r = getr regs r;
    (* [comment removed for export] *)
    atq_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> mem' a = mem a;
    atq_stk   : stk_ok RSEGS mem' sp ATR_STACK;
    atq_stkcj : stk asegs mem' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp);
    (* [comment removed for export] *)
    atq_heap  : exists LB', as_RHEAP H s' LB' mem' /\ Permutation LB' LB;
    atq_al    : as_AL H s' >= as_AL H s - atr_cost data;
    atq_aux   : exists B, as_rauxv_ok H mem' B /\ bv_unsigned sp + 128 <= B < 2 ^ 64;
    (* [comment removed for export] *)
    atq_data  : rdn RSEGS mem' (Z_to_bv 64 A) (length data) = Some data;
    atq_addr  : addressable mem' A cap;
    atq_cb    : exists junk, rw_cells asegs mem' A [CB (Z.to_nat cap) junk];
    (* [comment removed for export] *)
    atq_st    : atr_statics adrv_ax2 sp mem';
    atq_out   : astdout_after mem' (Nat.pred (hdr_calls data));
    (* [comment removed for export] *)
    atq_fs    : m_fs mo' = m_fs mo;
    atq_fd1   : fd_lookup (m_fds mo') (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    atq_fd2   : fd_lookup (m_fds mo') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Definition as_target_run_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h91!jc!m4!ip6!h8!ipc!hof!k3!jue!kib!km2!kp1!kt5!kte!lhe!lma!o6!ln6!ls8!lt3!ltd!lu6!lue!lv9!mg1!mk2&>0@1$1@1$0#k0@1$5@1$1@1$0#8>2sp@1$1@1$0#k0>1A$6>3cap$6>4data@1$3@1$1@1$0#8>1p$h4>1s@1$c?1H>2LB@1$3$h3>3msF$7>2mo$9>4regs@2$a@1$0#5@1$1@1$0#k0>3mem~0>1K$h6>0@b$h2^c^b^a^9^8^7^6^5^4^3^2>0@1^2@1$4$h0>0>3fx'$h5>5regs'@2$a@1$0#5@1$1@1$0#k0>4mem'~0>4msF'$7>3mo'$9>2s'@1$c?1H>0@h0$h1^6^h4^h3^h2^h1^h0^f^e^c^b^a^5^4^3^2^1@4$e$b$d@2$8^4^3^a@4$e$b$d@2$8^8^7@2$h7@2$h8+1@3$2@1$1@1$0#8@2$f@1$0#8+j0@3$2@1$1@1$0#8@2$f@1$0#8+a@1$4@1$1@1$0#8^4").
End TargetRun.
(* [comment removed for export] *)
