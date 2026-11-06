(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  ExitSim ShapeAlg Nodes SumWalkTac.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Export RefExitBase.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16optionk14listhf7Z_to_bvk14Some37Corelib4Init5Logicna2eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp3h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~te3rdn69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hhffloaded_segmentsna3and46Stdlib6ZArith6BinInt1Zhme3addhme2lehfbbv_unsignedhme6of_natna2or01Zk13nat79OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefStdioDefs4FPX1~~~~~~hr97sw_posthme3powhme3sub3h5LinuxProcessSemanticsfLinuxProcessSem5Stateih65Model3h5LinuxProcessSemantics5Riscv7Preludeikd5bvmapna2exk13nilk14prodih67FdEntryk14Noneih69FdChannelih69fd_lookupih65m_fdsih68m_haltedih69m_vm_lazy69OSSVerify6Proofsaboost_jsonafuzz_parse3libbRefExitBase~~~~~~itcafile_cleanhr9bexit_commonhr9estdout_pending" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

(* [comment removed for export] *)
Definition ssp_cells : ltac2:(zQ "30!h9!jc!l9>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>3can@1$1@1$0#k0P") := ltac2:(zQ "b0!h9!jc!m2!l9!m9!n3!oe!sa!hh9!hl5!hm8\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\3can@1$1@1$0#k0@2$a@3$6@1$3@1$2@1$1@1$0#8@4$8$9^2@2$4@1$0#k0+vonn0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$4@1$0#k0+hirmv8@3$6@1$3@1$2@1$1@1$0#8@4$8$9^2@2$4@1$0#k0+hirmv8N8@2$5@1$2@1$1@1$0#8@2$7N8^1").

(* [comment removed for export] *)
Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
       (mem' : word -> option byte) : Prop := {
  swp_agree : forall x : word,
      ~ (su - 112 <= bv_unsigned x < su)%Z ->
      ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
      ~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
      mem' x = mem x;
  swp_grows : mem_grows mem mem';
  swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
  swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

(* [comment removed for export] *)
Lemma sw_post_rdn : ltac2:(zQ "h21!h9!jc!ho6!hod!hp3!m2!l9!hq1!hqb!n3!oe!hr0!hh9!hl5!hr3!hvd!ig8!igf&>0@1$1@1$0#k0@1$6@1$1@1$0#8>3mem~0>2su$b>1f$b>4bufp@1$1@1$0#k0>5bufsz@1$1@1$0#k0>4mem'~0>1a@1$1@1$0#k0>1n$e>2bs@1$5@1$1@1$0#8>0@6$f^9^8^7^6^5^4>0@3$a@1$6@1$5@1$1@1$0#8@4$c$d^a^4^3@2$9@1$5@1$1@1$0#8^2>0@2$3@2$2@2$4@1$0#k0^5@1$7^4@2$h0+2+k0>0@2$8@2$3@2$2@2$4@1$0#k0^6@1$7^5@2$h1^b+n0@2$3^b@2$4@1$0#k0^6>0@2$8@2$3@2$2@2$4@1$0#k0^7@1$7^6@2$2^b+i0@2$3@2$2^b+j0@2$4@1$0#k0^7>0@2$8@2$3@2$2@2$4@1$0#k0^8@1$7^7@2$2^c+j8@2$3@2$2^c+k0@2$4@1$0#k0^8@3$a@1$6@1$5@1$1@1$0#8@4$c$d^a^9^8@2$9@1$5@1$1@1$0#8^7").
Proof.
  intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
  rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
  intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
       (sp tp code : word) (tid : Z) (wp2 rp2 : word) (axh : Z) : Prop := {
  ec_sp   : getr regs 2 = sp;
  ec_tp   : getr regs 4 = tp;
  ec_a0   : getr regs 10 = code;
  ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  ec_tplo : (168 <= bv_unsigned tp)%Z;
  ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
  ec_tid  : (0 < tid < 2147483648)%Z;
  (* [comment removed for export] *)
  ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  (* [comment removed for export] *)
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x12b928) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0xf87a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf1218));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0xf87a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf1210));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0xf1210) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x47340));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0xf9bf8) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0xf8640) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xda5d8));
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0xf97c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf97c8));
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0xf8648) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_axl  : rdn RSEGS mem (Z_to_bv 64 0x12b70c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec_axh  : rdn RSEGS mem (Z_to_bv 64 0x12b718) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 axh));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0xf99a8 wp2 rp2
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdfa40));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0xf9a98 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x12b930 <= wb < wp /\ wp <= 0x12d000)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_pre : ltac2:(zQ "60!h9!jc!m2!l9!ik4!in3>4regs@2$5@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>5model$4>4code@1$1@1$0#k0>7pending@1$2@1$1@1$0#8P") := ltac2:(zQ "h91!h9!jc!inc!hr0!hm8!oe!m2!l9!io1!io7!ioe!m9!ip9!n3!hqb!iq0!ik4!iqd!ira!is3!isf!in3!jha!ji8!jj7&@2$9@1$1@1$0#k0@1$1@1$0#k0\4regs@2$h5@1$0#5@1$1@1$0#k0\3mem>0@1$1@1$0#k0@1$7@1$1@1$0#8\5model$h0\4code@1$1@1$0#k0\7pending@1$6@1$1@1$0#8@2$2@1$1@1$0#k0\2sp@1$1@1$0#k0@2$2@1$1@1$0#k0\2tp@1$1@1$0#k0@2$2$3\3tid$3@2$2@1$1@1$0#k0\3wp2@1$1@1$0#k0@2$2@1$1@1$0#k0\3rp2@1$1@1$0#k0@2$4@9$h7^a^9^5^4^7^3^2^1Z@2$4@3$5@1$7@1$1@1$0#k0@1$h3^8@1$c@1$1@1$0#k0@2$4@3$5@1$6~0@1$h4^8@1$8~0@2$e@2$4@3$5@1$6@1$1@1$0#8^6@1$8@1$1@1$0#8@2$2@1$1@1$0#k0\3wp1@1$1@1$0#k0@2$2@1$1@1$0#k0\3rp1@1$1@1$0#k0@4$h6^b+vpqp8^2^1@2$2$3\2wb$3@2$2$3\2wp$3@2$2@1$1@1$0#k0\4bufp@1$1@1$0#k0@2$2@1$1@1$0#k0\5bufsz@1$1@1$0#k0@2$2@1$1@1$0#k0\3rp1@1$1@1$0#k0@2$2@1$1@1$0#k0\3can@1$1@1$0#k0@2$4@8$h8^f^6^5^4^3^2^1^c@3$5@1$7$a@2$h1@1$h2^e@2$b@1$0#k0+1@2$d$a@1$f@2$b@1$0#k0+1").
End FPX1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
