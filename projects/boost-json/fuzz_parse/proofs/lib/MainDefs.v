(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame StreamSim FileSim
  SymRun Hoare Spec SReach LibDiagKn RefLayout RefStartupDefs RefStartupFacts RefStartup RefStdioDefs RefExitBase HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require FP.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require HeapMF_iface.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat37Corelib7Numbers7BinNumsi34Nposi31Z35stdpp9bitvectorbdefinitionsk72bv37Corelib5Lists7ListDefm93nthk77Z_to_bvk7bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs4FPX1~~~~~~pe5hdr_b46Stdlib6ZArith6BinInt1Zu63addu66modulou63mulu66to_nat01Spe7hdr_cfgu63sub06lengthu66of_nat37Corelib4Init5Peanohk02lepe9hdr_calls37Corelib4Init5Logichm63and06option04Nonehm62equ62leu62lthm62orpeh1lib_pristine_addr04Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshs0h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~igc3rdn69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~ikefloaded_segmentsu63powhm62ex04prod04andb04negbu63lebu63ltb36Stdlib4Bool4Boolis17Is_true25stdpp9decidableitebuncurry_dec69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~iveadiag_cells25stdpp4basejk86filteritebIs_true_dec35stdppblist_basics4listjmdblist_filter04pair04cons03nil3h5LinuxProcessSemanticsfLinuxProcessSem3Runjq55mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statejta5Model3h5LinuxProcessSemantics5Riscv7Preludekh15bvmapigc4mkstigc7seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~kl3dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~kpb8realizesjta5event79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs9TargetRun~~~~~~kub6TRpostkub5TRpreigc7FPState79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~lke5blockkpb4TSetkpb6t_emit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~lr36PState69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~lv91W79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefcHeapSR_iface~~~~~~mj57hs_KRELjta7FdEntryjta8with_fds79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs4FPX2~~~~~~mpaaheap_extramj53hsr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~muf3hmflke3memmuf7hs_KRELmuf8hs_RHEAPmufchs_lb_removemufbhs_rauxv_okmj58hs_RHEAPmj5chs_lb_removemj5bhs_rauxv_oklr34bptrjta9ProcInputjq5h1segments_reservedjtaainit_modeljta8with_tidjta7in_argvjta7in_envpjta5in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs~~~~~~og46model03h5LinuxProcessSemanticsfLinuxProcessSem2Fsok98valid_fsjq5h0entry_stack_fitsjq5avalid_argvjq5avalid_envpjq58valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutord9EntryDraw69OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Amb~~~~~~ove6amb_of69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~pje5hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~po24frm0og4ftarget_run_stmtigc6fp_csr69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefStartup~~~~~~pu0amain_entrylv94spec" s.
(* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition hdr_b : ltac2:(zQ "50!h8!he!jc!k3!m4>4data@1$0@1$4@1$2#8>1i$1$3") := ltac2:(zQ "70!jc!m4!h8!he!o0!o6!p0\4data@1$2@1$1@1$0#8\1i$3@2$6@1$0#8@4$4@1$1@1$0#8^1^2@2$5@1$0#8Z").
Definition hdr_cfg : ltac2:(zQ "40!h8!jc!k3!m4>4data@1$0@1$3@1$1#8$2") := ltac2:(zQ "70!te!h8!jc!ve!hg4!hgd!m4\4data@1$1@1$6@1$2#8@2$4@2$3@2$0^1N0@2$5+hg0@2$0^1N1+ogg0").   (* [comment removed for export] *)
Definition hdr_calls : ltac2:(zQ "40!h8!he!jc!m4>4data@1$0@1$3@1$2#8$1") := ltac2:(zQ "90!he!hh3!hhc!h8!jc!te!hhf!hg4!m4\4data@1$3@1$8@1$4#8M0\1x$0$0@1$1@1$6^1N1\1n$0@1$2@1$1@2$7@2$5^2N2+4").
Definition hdr_payload_len : ltac2:(zQ "40!h8!jc!k3!m4>4data@1$0@1$3@1$1#8$2") := ltac2:(zQ "70!jc!hi9!m4!hif!h8!hhf!hj7\4data@1$4@1$2@1$0#8@2$1@2$1@1$6@2$3@1$2@1$0#8^1+6@1$5^1").

Lemma hdr_calls_range : ltac2:(zQ "60!hl4!hla!h8!hna!jc!m4>4data@1$2@1$5@1$4#8@2$3@2$0N1@1$1^1@2$0@1$1^1N4").
Proof.
  intros data. unfold hdr_calls. destruct (Z.to_nat (hdr_cfg data)); [lia|].
  pose proof (Z.mod_pos_bound (hdr_b data 2) 4 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ro_none : ltac2:(zQ "30!jc!m4!ho1>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "a0!jc!m4!ho1!ho9!hna!hof!k3!hp5!hpa!o6\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1i$6>0@2$4@2$7+hggg0^1@2$8^1+vhgg0@3$5@1$2@1$1@1$0#8@1^3@2$9@1$0#k0^2@1$3@1$1@1$0#8").

(* [comment removed for export] *)
Definition relro_none : ltac2:(zQ "30!jc!m4!ho1>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "a0!jc!m4!ho1!ho9!hna!hof!k3!hp5!hpa!o6\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1i$6>0@2$4@2$7+vhgg0^1@2$8^1+vonn0@3$5@1$2@1$1@1$0#8@1^3@2$9@1$0#k0^2@1$3@1$1@1$0#8").

(* [comment removed for export] *)
Definition lib_pristine_addr : ltac2:(zQ "10!k3>1i$0P") := ltac2:(zQ "50!hna!hp5!hpa!hpf!k3\1i$4@2$3@2$0@2$1+vonn8^1@2$2^1+vons8@2$3@2$0@2$1+vpnv0^1@2$2^1+vpnv8@2$3@2$0@2$1+vpoq8^1@2$2^1+vpos0@2$3@2$0@2$1+vpov8^1@2$2^1+vppg8@2$3@2$0@2$1+hgpsmc^1@2$2^1+hgpuu8@2$0@2$1+hgrlu0^1@2$2^1+hgrlu8").
Definition lib_pristine : ltac2:(zQ "30!jc!m4!ho1>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "80!jc!m4!ho1!ho9!hof!k3!hq5!o6\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1i$5>0@1$6^1@3$4@1$2@1$1@1$0#8@1^3@2$7@1$0#k0^2@1$3@1$1@1$0#8").

(* [comment removed for export] *)
Definition tid_cell : ltac2:(zQ "40!jc!m4!ho1!k3>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>3tid$3P") := ltac2:(zQ "e0!jc!m4!h8!ho1!hna!hpa!o6!hra!hof!k3!hv7!ik7!io4!ip7\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\3tid$9@2$4@3$8@1$3@1$2@1$1@1$0#8@4$b$c^2@2$6@1$0#k0+hgrmh0N4@2$7@1$2@1$1@1$0#8@2$aN4@2$6@1$0#k0^1@2$4@2$5Z^1@2$5^1@2$d+2+h6").

(* [comment removed for export] *)
Definition errno_cell : ltac2:(zQ "30!jc!m4!ho1>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "d0!jc!m4!h8!ho1!hof!hra!hif!he!hna!ipd!ik7!io4!o6\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$9@1$2@1$1@1$0#8\2e4@1$2@1$1@1$0#8@2$8@3$4@1$3@1$2@1$1@1$0#8@4$a$b^2@2$c@1$0#k0+hgrmh4N4@2$5@1$2@1$1@1$0#8^1@3$4$7@2$6@1$1@1$0#8^1N4").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TR_STACK : Z := 65536.
End FPX1.

Section TargetRun.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.   (* [comment removed for export] *)
  Variable HS : ltac2:(zQ "10!mu8$0").                    (* [comment removed for export] *)
  Variable HM : ltac2:(zQ "10!nj1$0").       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record TRpre (sp : word) (A cap : Z) (data : list byte) (s : PState) (LB : list RMalloc_iface_stmt.block)
                (model : Model) (regs : bvmap 5 word) (mem : word -> option byte) : Prop := TRPRE {
    (* [comment removed for export] *)
    tr_ra  : getr regs 1 = Z_to_bv 64 0x47544;
    tr_sp  : getr regs 2 = sp;
    tr_tp  : getr regs 4 = Z_to_bv 64 0x10b6b8;
    tr_a0  : getr regs 10 = Z_to_bv 64 (A + 2);                                  (* [comment removed for export] *)
    tr_a1  : getr regs 11 = Z_to_bv 64 (hdr_cfg data);                           (* [comment removed for export] *)
    tr_a2  : getr regs 12 = Z_to_bv 64 (A + 2 + hdr_cfg data + 4);                (* [comment removed for export] *)
    tr_a3  : getr regs 13 = Z_to_bv 64 (hdr_payload_len data);                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    tr_len6  : 6 + hdr_cfg data <= Z.of_nat (length data);
    tr_lenhi : Z.of_nat (length data) < MAX_INPUT;
    (* [comment removed for export] *)
    tr_sp16  : bv_unsigned sp mod 16 = 0;
    tr_splo  : hceil + TR_STACK + 4096 <= bv_unsigned sp;
    tr_sphi  : bv_unsigned sp + 128 <= 0x800000000000;
    tr_stk   : stk_ok RSEGS mem sp TR_STACK;
    tr_stkcj : stk rsegs mem (bv_unsigned sp - TR_STACK) (bv_unsigned sp);
    (* [comment removed for export] *)
    tr_rheap : hs_RHEAP HS s LB mem;
    tr_krel  : hs_KREL HS s model;
    tr_blk   : In (A, cap) (map (fun b => (blk_addr b, blk_size b)) LB);
    tr_lb1   : lb_bytes LB <= 2 ^ 27 /\ Z.of_nat (length LB) <= 2;
    tr_aux   : exists B, hs_rauxv_ok HS mem B /\ bv_unsigned sp + 128 <= B < 2 ^ 64;
    (* [comment removed for export] *)
    tr_cap   : Z.of_nat (length data) <= cap;
    tr_data  : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    (* [comment removed for export] *)
    tr_ro    : ro_none mem;
    tr_inv   : mem_inv rsegs mem;
    tr_cells : cells_ok mem diag_cells;        (* [comment removed for export] *)
    tr_pf1   : cells_ok mem pf1_cells;         (* [comment removed for export] *)
    tr_relro : relro_none mem;                 (* [comment removed for export] *)
    tr_libp  : lib_pristine mem;               (* [comment removed for export] *)
    tr_tid   : exists tid, tid_cell mem tid;
    tr_errno : errno_cell mem;
    tr_canary : exists can, canary_ok mem can;  (* [comment removed for export] *)
    (* [comment removed for export] *)
    tr_frm   : FP.frm0 (@fp_csr fx);
    (* [comment removed for export] *)
    tr_h     : m_halted model = None;
    tr_lazy  : m_vm_lazy model = [];
    tr_fd1   : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    tr_fd2   : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record stdout_after (mem : word -> option byte) (k : nat) : Prop := SOA {
    so_flags : rdn RSEGS mem (Z_to_bv 64 0xf9a98) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    so_rpos  : rdn RSEGS mem (Z_to_bv 64 0xf9aa0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    so_rend  : rdn RSEGS mem (Z_to_bv 64 0xf9aa8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    so_wend  : rdn RSEGS mem (Z_to_bv 64 0xf9ab8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12c2a8));
    so_wpos  : rdn RSEGS mem (Z_to_bv 64 0xf9ac0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x12bea8 + 2 * Z.of_nat k)));
    so_wbase : rdn RSEGS mem (Z_to_bv 64 0xf9ad0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bea8));
    so_write : rdn RSEGS mem (Z_to_bv 64 0xf9ae0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdfa40));
    so_buf   : rdn RSEGS mem (Z_to_bv 64 0xf9af0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bea8));
    so_bsz   : rdn RSEGS mem (Z_to_bv 64 0xf9af8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
    so_fd    : rdn RSEGS mem (Z_to_bv 64 0xf9b10) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
    so_lock  : rdn RSEGS mem (Z_to_bv 64 0xf9b24) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    so_bytes : rdn RSEGS mem (Z_to_bv 64 0x12bea8) (2 * k) = Some (zero_lines k) }.

  (* [comment removed for export] *)
  Definition exit_cells : ltac2:(zQ "40!iq3!k3!h8!he@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "ec!k3!iq9!iq3!he!iqf!ir5!irb!it3!iuf!h8!jja!jl4!jle!jo5&@2$1@2$5+vpqp8^2@2$6^2+vpro0&@1$4~0&@2$1@2$5+hirng8^2@2$6^2+hirpi8&@1$4~2&@2$1~1~3&@2$1@2$5+hgpsg0^2@2$6^2+hgpsi0&@1$4~5&@2$1~4~6&@1$7~7&\2y1$3~8&\1a$0~9&M2\1y@2$2$0$3P^2~a@6$b@2$2@2$2$0$3$0@1$9@2$2@2$2$0$3$0@1$d@2$2@2$2$0$3$0\1c@2$2@2$2$0$3$0M2\1c@2$2@2$2$0$3$0P^1\1y@2$2$0$3\2y0$0~b@4$8@2$2$0$3$0\1x@2$2$0$3\1y$0~b\1x@2$2$0$3\1y$0@5$8$0$3\1x$0\1y$3~8\2x0$0\2y0$3@1$c~7^2$a").

  (* [comment removed for export] *)
  Definition ax1_cells : ltac2:(zQ "40!iq3!k3!h8!he@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!k3!iq3!he!jp4!jpa!jq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirng8N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirngcN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirnh0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirnh8N8+hirni0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirni0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirni8N8+tqnm8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiroi8N8+knnv8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hgpsg4N1Z@1$5@2$1@2$1$0$2$0").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record TRpost (sp : word) (A cap : Z) (data : list byte) (LB : list RMalloc_iface_stmt.block) (model : Model)
                 (regs : bvmap 5 word) (mem : word -> option byte)
                 (regs' : bvmap 5 word) (mem' : word -> option byte) (model' : Model) : Prop := TRPOST {
    tq_sp   : getr regs' 2 = sp;
    tq_tp   : getr regs' 4 = Z_to_bv 64 0x10b6b8;
    tq_a0   : getr regs' 10 = Z_to_bv 64 0;                                      (* [comment removed for export] *)
    tq_cs   : forall r : reg, In r ([8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list reg) -> getr regs' r = getr regs r;
    (* [comment removed for export] *)
    tq_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> mem' a = mem a;
    tq_stk   : stk_ok RSEGS mem' sp TR_STACK;
    tq_stkcj : stk rsegs mem' (bv_unsigned sp - TR_STACK) (bv_unsigned sp);
    (* [comment removed for export] *)
    tq_heap  : exists s' LB', HeapMF_iface.hs_RHEAP HM s' LB' mem' /\ HeapMF_iface.hs_KREL HM s' model'
                 /\ (forall b, In b LB -> In b LB') /\ lb_bytes LB' <= 2 ^ 27 /\ Z.of_nat (length LB') <= 2;
    tq_aux   : exists B, HeapMF_iface.hs_rauxv_ok HM mem' B /\ bv_unsigned sp + 128 <= B;
    (* [comment removed for export] *)
    tq_ro    : ro_none mem';
    tq_inv   : mem_inv rsegs mem';
    tq_cells : cells_ok mem' exit_cells;
    tq_ax    : cells_ok mem' ax1_cells;        (* [comment removed for export] *)
    tq_relro : relro_none mem';
    tq_out   : stdout_after mem' (Nat.pred (hdr_calls data));
    tq_canary : exists can, canary_ok mem' can;
    tq_tid   : exists tid, tid_cell mem' tid;
    tq_errno : errno_cell mem';
    (* [comment removed for export] *)
    tq_h     : m_halted model' = None;
    tq_lazy  : m_vm_lazy model' = [];
    tq_fs    : m_fs model' = m_fs model;
    tq_fd1   : fd_lookup (m_fds model') (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    tq_fd2   : fd_lookup (m_fds model') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Definition target_run_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h91!jc!m4!io4!o6!jpa!h8!jq0!ho1!k3!jt1!kg8!kj7!kk0!kk8!koa!kt6!ku2!lj0!lja!lk3!lp8!lq1!lq9!luf!mj0&>0@1$1@1$0#k0@1$7@1$1@1$0#8>2sp@1$1@1$0#k0>1A$8>3cap$8>4data@1$5@1$1@1$0#8>1s$h7>2LB@1$5$h4>5model$a>4regs@2$b@1$0#5@1$1@1$0#k0>3mem~0>1K$h5>0@9$h2^a^9^8^7^6^5^4^3^2>0@1^2@1$6$h0>0>3fx'$h3>5regs'@2$b@1$0#5@1$1@1$0#k0>4mem'~0>6model'$a>0@b$h1^h0^f^e^d^b^a^9^8^3^2^1@4$f$2$e@2$9@5$c^5^4@2$3@1$0#k0+knlk4^3@1$d$2^2^8@4$f$2$e@2$9@5$c?2fx^6@2$3@1$0#k0+knmq0^5@1$d$2^7@2$h6@2$h8+1@3$4@1$1@1$0#8@2$3@1$0#8+j0@3$4@1$1@1$0#8@2$3@1$0#8+a@1$6@1$1@1$0#8^4").
End TargetRun.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Record heap_extra (HS : hsr) : Prop := HEX {
  (* [comment removed for export] *)
  hx_sr    : forall Q c, hs_SR HS Q c -> sreach RSEGS Q c;
  (* [comment removed for export] *)
  hx_mpres : forall mo mo', hs_MPRES HS mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo;
  (* [comment removed for export] *)
  hx_live : 2 ^ 31 <= hs_LIVE_MAX HS /\ 600 <= hs_LIVE_CNT_MAX HS;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  hx_krel_vm : forall s mo mo', hs_KREL HS s mo ->
      m_halted mo' = m_halted mo -> m_vm_lazy mo' = m_vm_lazy mo ->
      m_vm_materialized mo' = m_vm_materialized mo -> m_vmmaps mo' = m_vmmaps mo -> hs_KREL HS s mo';
  (* [comment removed for export] *)
  hx_statics : forall s LB m, hs_RHEAP HS s LB m ->
      rdn RSEGS m (Z_to_bv 64 0x12b94b) 1 = Some [Z_to_bv 8 0]
      /\ rdn RSEGS m (Z_to_bv 64 0xf8770) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b6f8))
      /\ exists can, canary_ok m can }.

Lemma hx_krel_fds : ltac2:(zQ "b0!mn8!h8!iq3!jc!mo3!kg8!moe!mta!mu8!luf!m4>2HS$8>0@1$7^1>1s$9>2mo$5>1f@1$1@2$2@1$a@1$3#k0$4>0@3$0^5^3^2@3$0^6^4@2$6^2^3").
Proof. intros HS HX s mo f K. eapply (hx_krel_vm HS HX); [exact K | | | |]; destruct mo; reflexivity. Qed.
End FPX2.

(* [comment removed for export] *)
Section HeapM.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Record heap_extraM (HM : HeapMF_iface.hmf) : Prop := HEXM {
    hm_sr      : forall Q c, HeapMF_iface.hs_SR HM Q c -> sreach RSEGS Q c;
    hm_sr_laws : HeapMF_iface.SR_laws HM;
    hm_krel_h  : forall s mo, HeapMF_iface.hs_KREL HM s mo -> m_halted mo = None /\ m_vm_lazy mo = [];
    hm_mpres   : forall mo mo', HeapMF_iface.hs_MPRES HM mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo;
    hm_mpres_laws : HeapMF_iface.MPRES_laws HM;
    hm_krel_vm : forall s mo mo', HeapMF_iface.hs_KREL HM s mo ->
        m_halted mo' = m_halted mo -> m_vm_lazy mo' = m_vm_lazy mo ->
        m_vm_materialized mo' = m_vm_materialized mo -> m_vmmaps mo' = m_vmmaps mo -> HeapMF_iface.hs_KREL HM s mo';
    hm_statics : forall s LB m, HeapMF_iface.hs_RHEAP HM s LB m ->
        rdn RSEGS m (Z_to_bv 64 0x12b94b) 1 = Some [Z_to_bv 8 0]
        /\ rdn RSEGS m (Z_to_bv 64 0xf8770) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b6f8))
        /\ exists can, canary_ok m can;
    hm_free    : HeapMF_iface.free_mf_stmt HM;
    hm_rheap_frame : HeapMF_iface.RHEAP_frame HM;
    hm_block_range : HeapMF_iface.RHEAP_block_range HM;
    hm_blocks_nodup : HeapMF_iface.RHEAP_blocks_nodup HM;
    hm_perm    : HeapMF_iface.RHEAP_perm HM;
    hm_rauxv_frame : HeapMF_iface.rauxv_frame HM;
    hm_lb_remove : HeapMF_iface.lb_remove_laws HM }.

  Definition handover : ltac2:(zQ "20!nj1!mu8>2HS$1>2HM$0P") := ltac2:(zQ "h30!h8!hna!lp8!nj8!luf!hof!k3!kg8!nj1!njf!nka!nl6!nm6!mn8!nn5!no1!np1!mu8!nq0\2HS$h1\2HM$8@2$1>1s$4>2LB@1$0$2>1m$3>0@4$e^5^3^2^1@4$a^5^4^3^2@2$1>1s$4>2mo$7>0@3$d^4^2^1@3$9^4^3^2@2$1>1m$3>1B$6>0@3$h0^4^2^1@3$c^4^3^2>1p$h2>2LB@1$0$2@3$5@1$0$2@3$f^4^2^1@3$b^3^2^1").
End HeapM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition model0 : ltac2:(zQ "50!jc!m4!k3!kg8!nq8>3tid@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>3sp0@1$1@1$0#k0>3lim$2>3inp$4$3") := ltac2:(zQ "80!jc!m4!k3!nr5!nq8!nsb!nt9!io4\3tid@1$1@1$0#k0\3brk@1$1@1$0#k0\5mbase@1$1@1$0#k0\3sp0@1$1@1$0#k0\3lim$2\3inp$4@2$6^6@6$5@1$3$7^5^4^3^2^1").
End FPX3.

Section MainStmt.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Definition main_realizes_stmt : ltac2:(zQ "20!nj1!mu8>2HS$1>2HM$0P") := ltac2:(zQ "ic0!jc!m4!nu5!p0!nv0!hpa!hna!k3!nvb!ojf!io4!hp5!ip7!jq0!ho1!on4!oo0!jt1!op5!oq3!or1!ov1!nq8!kj7!pj4!nj1!pn9!prb!ps3!pt6!kk0!kk8!mn8!nn5!np1!mu8!lp8!qhd!koa!kt6!luf!qib!ve!o6\2HS$i3\2HM$h9>3sp0@1$1@1$0#k0>3tid@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>3rnd$h5>3lim$7>3inp$h6>4regs@2$h7@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$e@1$1@1$0#8>3ps0$i8>1B$7>0@1$h4^b>0@3$h0^c@1$2^6@1$4^6>0@1$h2@1$2^7>0@1$h3@1$4^8>0@1$f@1$8^9>0@2$6@2$5Z@2$3@1$0#k0^f@2$5@2$3@1$0#k0^f@2$c+2+h6>0@2$b@2$ia@1$ha?5HCEIL+ogggg0@2$3@1$0#k0^h1>0@8$i5@1$h8^c^h2@1$2^c@1$4^c^e^h1^b^a>0@4$i1^h5^a@1$d$i4^b>0@3$i0^h6^b@6$9^h3^h2^h1^h4^f^e>0@3$i2^h7^d^b>0@2$6@2$b@2$3@1$0#k0^h6^c@2$5^c@2$c+2+k0>0@4$hc?2fx?5HCEIL^h9^h8>0@1$hb@1$hd?2fx@4$i7$a$i6@2$h1@5$he?2fx^h2@2$ib@1$0#k0+knjt0^h1@1$hf$a@6$9^h8^h7^h6^h9^h4^h3@2$i9@1$2^h3@1$8^h3").
End MainStmt.
(* [comment removed for export] *)
