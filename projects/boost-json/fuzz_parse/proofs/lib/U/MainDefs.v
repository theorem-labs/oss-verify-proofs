(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame StreamSim FileSim SymRun Hoare Spec SReach RefLayout HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import LibDiagKn RefStartupDefs RefStartupFacts RefStartup RefStdioDefs RefExitBase.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require FP.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require HeapMF_iface.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat37Corelib7Numbers7BinNumsi34Nposi31Z35stdpp9bitvectorbdefinitionsk72bv37Corelib5Lists7ListDefm93nthk77Z_to_bvk7bbv_unsigned89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainDefs4FPX1~~~~~~pe5hdr_b46Stdlib6ZArith6BinInt1Zu83addu86modulou83mulu86to_nat01Spe7hdr_cfgu83sub06lengthu86of_nat37Corelib4Init5Peanohk22lepe9hdr_calls37Corelib4Init5Logichm83and06option04Nonehm82equ82leu82lthm82orpeh1lib_pristine_addr04Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshs2h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ige3rdn69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~il0floaded_segmentsu83powhm82ex04prod04andb04negbu83lebu83ltb36Stdlib4Bool4Boolis37Is_true25stdpp9decidableiu0buncurry_dec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~jg0adiag_cells25stdpp4basejkc6filteriu0bIs_true_dec35stdppblist_basics4listjn1blist_filter04pair04cons03nil3h5LinuxProcessSemanticsfLinuxProcessSem3Runjq95mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statejte5Model3h5LinuxProcessSemantics5Riscv7Preludekh55bvmapige4mkstige7seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~kl7dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~kpf8realizesjte5eventige7FPState79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~kva5blockkpf4TSetkpf6t_emit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~lm06PState69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~lq61W89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainDefs9TargetRun~~~~~~lu26TRpostlu25TRpre79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapSR_iface~~~~~~mjc7hs_KRELjte7FdEntryjte8with_fdsmjc3hsr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainDefs4FPX2~~~~~~mq9aheap_extra79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~mv93hmfkva3memmv97hs_KRELmv98hs_RHEAPmv9chs_lb_removemv9bhs_rauxv_okmjc8hs_RHEAPmjcchs_lb_removemjcbhs_rauxv_oklm04bptrjte9ProcInputjq9h1segments_reservedjteainit_modeljte8with_tidjte7in_argvjte7in_envpjte5in_fs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainDefs~~~~~~oh06model03h5LinuxProcessSemanticsfLinuxProcessSem2Fsol78valid_fsjq9h0entry_stack_fitsjq9avalid_argvjq9avalid_envpjq98valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutosb9EntryDraw69OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Amb~~~~~~pgc6amb_of69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~pkc5hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~pp04frm0ige6fp_csrlq64specoh0ftarget_run_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UaRefStartup~~~~~~pv6amain_entry" s.
(* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition hdr_b : ltac2:(zQ "50!h8!he!jc!k3!m4>4data@1$0@1$4@1$2#8>1i$1$3") := ltac2:(zQ "70!jc!m4!h8!he!o0!o6!p0\4data@1$2@1$1@1$0#8\1i$3@2$6@1$0#8@4$4@1$1@1$0#8^1^2@2$5@1$0#8Z").
Definition hdr_cfg : ltac2:(zQ "40!h8!jc!k3!m4>4data@1$0@1$3@1$1#8$2") := ltac2:(zQ "70!u0!h8!jc!hg0!hg6!hgf!m4\4data@1$1@1$6@1$2#8@2$4@2$3@2$0^1N0@2$5+hg0@2$0^1N1+ogg0").   (* [comment removed for export] *)
Definition hdr_calls : ltac2:(zQ "40!h8!he!jc!m4>4data@1$0@1$3@1$2#8$1") := ltac2:(zQ "90!he!hh5!hhe!h8!jc!u0!hi1!hg6!m4\4data@1$3@1$8@1$4#8M0\1x$0$0@1$1@1$6^1N1\1n$0@1$2@1$1@2$7@2$5^2N2+4").
Definition hdr_payload_len : ltac2:(zQ "40!h8!jc!k3!m4>4data@1$0@1$3@1$1#8$2") := ltac2:(zQ "70!jc!hib!m4!hj1!h8!hi1!hj9\4data@1$4@1$2@1$0#8@2$1@2$1@1$6@2$3@1$2@1$0#8^1+6@1$5^1").

Lemma hdr_calls_range : ltac2:(zQ "60!hl6!hlc!h8!hnc!jc!m4>4data@1$2@1$5@1$4#8@2$3@2$0N1@1$1^1@2$0@1$1^1N4").
Proof.
  intros data. unfold hdr_calls. destruct (Z.to_nat (hdr_cfg data)); [lia|].
  pose proof (Z.mod_pos_bound (hdr_b data 2) 4 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ro_none : ltac2:(zQ "30!jc!m4!ho3>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "a0!jc!m4!ho3!hob!hnc!hp1!k3!hp7!hpc!o6\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1i$6>0@2$4@2$7+hggg0^1@2$8^1+vkgg0@3$5@1$2@1$1@1$0#8@1^3@2$9@1$0#k0^2@1$3@1$1@1$0#8").

(* [comment removed for export] *)
Definition relro_none : ltac2:(zQ "30!jc!m4!ho3>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "a0!jc!m4!ho3!hob!hnc!hp1!k3!hp7!hpc!o6\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1i$6>0@2$4@2$7+vkgg0^1@2$8^1+vrsn8@3$5@1$2@1$1@1$0#8@1^3@2$9@1$0#k0^2@1$3@1$1@1$0#8").

(* [comment removed for export] *)
Definition lib_pristine_addr : ltac2:(zQ "10!k3>1i$0P") := ltac2:(zQ "50!hnc!hp7!hpc!hq1!k3\1i$4@2$3@2$0@2$1+vrso0^1@2$2^1+vrst0@2$3@2$0@2$1+vssv8^1@2$2^1+vstg0@2$3@2$3@2$0@2$1+vstn0^1@2$2^1+vstn8@2$0@2$1+vstg0^1@2$2^1+vsth0@2$3@2$0@2$1+vsuj8^1@2$2^1+vsuk8@2$3@2$0@2$1+hgthqc^1@2$2^1+hgtki8@2$0@2$1+hguri0^1@2$2^1+hguri8").
Definition lib_pristine : ltac2:(zQ "30!jc!m4!ho3>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "80!jc!m4!ho3!hob!hp1!k3!hq7!o6\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1i$5>0@1$6^1@3$4@1$2@1$1@1$0#8@1^3@2$7@1$0#k0^2@1$3@1$1@1$0#8").

(* [comment removed for export] *)
Definition tid_cell : ltac2:(zQ "40!jc!m4!ho3!k3>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>3tid$3P") := ltac2:(zQ "e0!jc!m4!h8!ho3!hnc!hpc!o6!hrc!hp1!k3!hv9!ik9!io6!ip9\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\3tid$9@2$4@3$8@1$3@1$2@1$1@1$0#8@4$b$c^2@2$6@1$0#k0+hgurl0N4@2$7@1$2@1$1@1$0#8@2$aN4@2$6@1$0#k0^1@2$4@2$5Z^1@2$5^1@2$d+2+h6").

(* [comment removed for export] *)
Definition errno_cell : ltac2:(zQ "30!jc!m4!ho3>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "d0!jc!m4!h8!ho3!hp1!hrc!hj1!he!hnc!ipf!ik9!io6!o6\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$9@1$2@1$1@1$0#8\2e4@1$2@1$1@1$0#8@2$8@3$4@1$3@1$2@1$1@1$0#8@4$a$b^2@2$c@1$0#k0+hgurl4N4@2$5@1$2@1$1@1$0#8^1@3$4$7@2$6@1$1@1$0#8^1N4").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TR_STACK : Z := 65536.
End FPX1.

Section TargetRun.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.   (* [comment removed for export] *)
  Variable HS : ltac2:(zQ "10!mq2$0").                    (* [comment removed for export] *)
  Variable HM : ltac2:(zQ "10!njd$0").       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record TRpre (sp : word) (A cap : Z) (data : list byte) (s : PState) (LB : list RMalloc_iface_stmt.block)
                (model : Model) (regs : bvmap 5 word) (mem : word -> option byte) : Prop := TRPRE {
    (* [comment removed for export] *)
    tr_ra  : getr regs 1 = Z_to_bv 64 0x47158;
    tr_sp  : getr regs 2 = sp;
    tr_tp  : getr regs 4 = Z_to_bv 64 0x10ebf8;
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
    so_flags : rdn RSEGS mem (Z_to_bv 64 0xfcfd8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    so_rpos  : rdn RSEGS mem (Z_to_bv 64 0xfcfe0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    so_rend  : rdn RSEGS mem (Z_to_bv 64 0xfcfe8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    so_wend  : rdn RSEGS mem (Z_to_bv 64 0xfcff8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f7e8));
    so_wpos  : rdn RSEGS mem (Z_to_bv 64 0xfd000) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x12f3e8 + 2 * Z.of_nat k)));
    so_wbase : rdn RSEGS mem (Z_to_bv 64 0xfd010) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f3e8));
    so_write : rdn RSEGS mem (Z_to_bv 64 0xfd020) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe2ee8));
    so_buf   : rdn RSEGS mem (Z_to_bv 64 0xfd030) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f3e8));
    so_bsz   : rdn RSEGS mem (Z_to_bv 64 0xfd038) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
    so_fd    : rdn RSEGS mem (Z_to_bv 64 0xfd050) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
    so_lock  : rdn RSEGS mem (Z_to_bv 64 0xfd064) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    so_bytes : rdn RSEGS mem (Z_to_bv 64 0x12f3e8) (2 * k) = Some (zero_lines k) }.

  (* [comment removed for export] *)
  Definition exit_cells : ltac2:(zQ "40!iq5!k3!h8!he@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "ec!k3!iqb!iq5!he!ir1!ir7!ird!it5!iv1!h8!jje!jl8!jm2!jo9&@2$1@2$5+vsvt8^2@2$6^2+vtgs0&@1$4~0&@2$1@2$5+hiusk8^2@2$6^2+hiuum8&@1$4~2&@2$1~1~3&@2$1@2$5+hgthk0^2@2$6^2+hgthm0&@1$4~5&@2$1~4~6&@1$7~7&\2y1$3~8&\1a$0~9&M2\1y@2$2$0$3P^2~a@6$b@2$2@2$2$0$3$0@1$9@2$2@2$2$0$3$0@1$d@2$2@2$2$0$3$0\1c@2$2@2$2$0$3$0M2\1c@2$2@2$2$0$3$0P^1\1y@2$2$0$3\2y0$0~b@4$8@2$2$0$3$0\1x@2$2$0$3\1y$0~b\1x@2$2$0$3\1y$0@5$8$0$3\1x$0\1y$3~8\2x0$0\2y0$3@1$c~7^2$a").

  (* [comment removed for export] *)
  Definition ax1_cells : ltac2:(zQ "40!iq5!k3!h8!he@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!k3!iq5!he!jp8!jpe!jq4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusk8N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiuskcN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusl0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusl8N8+hiusm0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusm0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusm8N8+ttsh0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiutm8N8+knkgc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hgthk4N1Z@1$5@2$1@2$1$0$2$0").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record TRpost (sp : word) (A cap : Z) (data : list byte) (LB : list RMalloc_iface_stmt.block) (model : Model)
                 (regs : bvmap 5 word) (mem : word -> option byte)
                 (regs' : bvmap 5 word) (mem' : word -> option byte) (model' : Model) : Prop := TRPOST {
    tq_sp   : getr regs' 2 = sp;
    tq_tp   : getr regs' 4 = Z_to_bv 64 0x10ebf8;
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
  Definition target_run_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h91!jc!m4!io6!o6!jpe!h8!jq4!ho3!k3!jt5!kgc!kjb!kk4!kkc!koe!kta!ku6!kuf!lk5!lke!ll6!lpc!ltd!mi9!mj3&>0@1$1@1$0#k0@1$7@1$1@1$0#8>2sp@1$1@1$0#k0>1A$8>3cap$8>4data@1$5@1$1@1$0#8>1s$h5>2LB@1$5$h2>5model$a>4regs@2$b@1$0#5@1$1@1$0#k0>3mem~0>1K$h3>0@9$h8^a^9^8^7^6^5^4^3^2>0@1^2@1$6$h0>0>3fx'$h1>5regs'@2$b@1$0#5@1$1@1$0#k0>4mem'~0>6model'$a>0@b$h7^h0^f^e^d^b^a^9^8^3^2^1@4$f$2$e@2$9@5$c^5^4@2$3@1$0#k0+knhl8^3@1$d$2^2^8@4$f$2$e@2$9@5$c?2fx^6@2$3@1$0#k0+knir4^5@1$d$2^7@2$h4@2$h6+1@3$4@1$1@1$0#8@2$3@1$0#8+j0@3$4@1$1@1$0#8@2$3@1$0#8+a@1$6@1$1@1$0#8^4").
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
      rdn RSEGS m (Z_to_bv 64 0x12ee8b) 1 = Some [Z_to_bv 8 0]
      /\ rdn RSEGS m (Z_to_bv 64 0xfbc78) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12ec38))
      /\ exists can, canary_ok m can }.

Lemma hx_krel_fds : ltac2:(zQ "b0!mo0!h8!iq5!jc!mob!kgc!mp6!mq2!lpc!mub!m4>2HS$7>0@1$9^1>1s$8>2mo$5>1f@1$1@2$2@1$a@1$3#k0$4>0@3$0^5^3^2@3$0^6^4@2$6^2^3").
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
        rdn RSEGS m (Z_to_bv 64 0x12ee8b) 1 = Some [Z_to_bv 8 0]
        /\ rdn RSEGS m (Z_to_bv 64 0xfbc78) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12ec38))
        /\ exists can, canary_ok m can;
    hm_free    : HeapMF_iface.free_mf_stmt HM;
    hm_rheap_frame : HeapMF_iface.RHEAP_frame HM;
    hm_block_range : HeapMF_iface.RHEAP_block_range HM;
    hm_blocks_nodup : HeapMF_iface.RHEAP_blocks_nodup HM;
    hm_perm    : HeapMF_iface.RHEAP_perm HM;
    hm_rauxv_frame : HeapMF_iface.rauxv_frame HM;
    hm_lb_remove : HeapMF_iface.lb_remove_laws HM }.

  Definition handover : ltac2:(zQ "20!njd!mq2>2HS$1>2HM$0P") := ltac2:(zQ "h30!h8!hnc!lk5!nk4!lpc!hp1!k3!kgc!njd!nkb!nl6!nm2!nn2!mo0!no1!nod!npd!mq2!nqc\2HS$h1\2HM$8@2$1>1s$4>2LB@1$0$2>1m$3>0@4$e^5^3^2^1@4$a^5^4^3^2@2$1>1s$4>2mo$7>0@3$d^4^2^1@3$9^4^3^2@2$1>1m$3>1B$6>0@3$h0^4^2^1@3$c^4^3^2>1p$h2>2LB@1$0$2@3$5@1$0$2@3$f^4^2^1@3$b^3^2^1").
End HeapM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition model0 : ltac2:(zQ "50!jc!m4!k3!kgc!nr4>3tid@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>3sp0@1$1@1$0#k0>3lim$2>3inp$4$3") := ltac2:(zQ "80!jc!m4!k3!ns1!nr4!nt7!nu5!io6\3tid@1$1@1$0#k0\3brk@1$1@1$0#k0\5mbase@1$1@1$0#k0\3sp0@1$1@1$0#k0\3lim$2\3inp$4@2$6^6@6$5@1$3$7^5^4^3^2^1").
End FPX3.

Section MainStmt.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Definition main_realizes_stmt : ltac2:(zQ "20!njd!mq2>2HS$1>2HM$0P") := ltac2:(zQ "ic0!jc!m4!nv1!p0!nvc!hpc!hnc!k3!og7!okd!io6!hp7!ip9!jq4!ho3!oo2!ooe!jt5!oq3!or1!orf!ovf!nr4!kjb!pk2!po7!ps9!pt1!kk4!kkc!njd!mo0!no1!npd!mq2!lk5!koe!kta!lpc!ptb!pu3!qj5!hg0!o6\2HS$i2\2HM$he>3sp0@1$1@1$0#k0>3tid@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>3rnd$h5>3lim$7>3inp$h6>4regs@2$h7@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$e@1$1@1$0#8>3ps0$i6>1B$7>0@1$h4^b>0@3$h0^c@1$2^6@1$4^6>0@1$h2@1$2^7>0@1$h3@1$4^8>0@1$f@1$8^9>0@2$6@2$5Z@2$3@1$0#k0^f@2$5@2$3@1$0#k0^f@2$c+2+h6>0@2$b@2$ia@1$h9?5HCEIL+ogggg0@2$3@1$0#k0^h1>0@8$i9@1$h8^c^h2@1$2^c@1$4^c^e^h1^b^a>0@4$i0^h5^a@1$d$i3^b>0@3$hf^h6^b@6$9^h3^h2^h1^h4^f^e>0@3$i1^h7^d^b>0@2$6@2$b@2$3@1$0#k0^h6^c@2$5^c@2$c+2+k0>0@4$i8?2fx?5HCEIL^h9^h8>0@1$ha@1$hb?2fx@4$i5$a$i4@2$h1@5$hc?2fx^h2@2$ib@1$0#k0+kmvu4^h1@1$hd$a@6$9^h8^h7^h6^h9^h4^h3@2$i7@1$2^h3@1$8^h3").
End MainStmt.
(* [comment removed for export] *)
