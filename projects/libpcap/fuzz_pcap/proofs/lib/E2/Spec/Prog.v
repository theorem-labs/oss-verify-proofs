(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Record PState (H hptr : Type) := mkPS {
  ps_heap : H;                          (* [comment removed for export] *)
  ps_libc : libc_st hptr;               (* [comment removed for export] *)
  ps_outfile : option hptr;             (* [comment removed for export] *)
  ps_tls : Z                            (* [comment removed for export] *)
}.
End WithCeil.

Arguments mkPS {H hptr} _ _ _ _.
Arguments ps_heap {H hptr} _.
Arguments ps_libc {H hptr} _.
Arguments ps_outfile {H hptr} _.
Arguments ps_tls {H hptr} _.

Section WithCeil.
Context {CE : CEIL}.
Section Lenses.
Context {H hptr : Type}.
Definition set_heap (h : H) (s : PState H hptr) : PState H hptr := mkPS h (ps_libc s) (ps_outfile s) (ps_tls s).
Definition set_libc (l : libc_st hptr) (s : PState H hptr) : PState H hptr := mkPS (ps_heap s) l (ps_outfile s) (ps_tls s).
Definition set_outfile (o : option hptr) (s : PState H hptr) : PState H hptr := mkPS (ps_heap s) (ps_libc s) o (ps_tls s).
Definition set_tls (a : Z) (s : PState H hptr) : PState H hptr := mkPS (ps_heap s) (ps_libc s) (ps_outfile s) a.
End Lenses.

(* [comment removed for export] *)
Record HeapOps (H hptr : Type) := mkHeapOps {
  ho_malloc : Z -> M (PState H hptr) (option hptr);          (* [comment removed for export] *)
  ho_calloc : Z -> Z -> M (PState H hptr) (option hptr);     (* [comment removed for export] *)
  ho_realloc : hptr -> Z -> M (PState H hptr) (option hptr); (* [comment removed for export] *)
  ho_free : hptr -> M (PState H hptr) unit;                  (* [comment removed for export] *)
  ho_addr : H -> hptr -> Z;                                  (* [comment removed for export] *)
  ho_eqb : hptr -> hptr -> bool;                             (* [comment removed for export] *)
  ho_pin : Z -> H -> H                                       (* [comment removed for export] *)
}.
End WithCeil.

Arguments ho_malloc {H hptr} _ _.
Arguments ho_calloc {H hptr} _ _ _.
Arguments ho_realloc {H hptr} _ _ _.
Arguments ho_free {H hptr} _ _.
Arguments ho_addr {H hptr} _ _ _.
Arguments ho_eqb {H hptr} _ _ _.
Arguments ho_pin {H hptr} _ _ _.

Section WithCeil.
Context {CE : CEIL}.
Section Prog.
Context {H hptr : Type} (HO : HeapOps H hptr).

#[local] Abbreviation PS := (PState H hptr) (only parsing).
#[local] Abbreviation MP := (M (PState H hptr)) (only parsing).

(* [comment removed for export] *)
Definition set_errno_ps (e : Z) : MP unit := @set_errno PS hptr ps_libc set_libc e.
Definition enomem_on_null (r : option hptr) : MP (option hptr) :=
  match r with
  | None => set_errno_ps ENOMEM ;;; mret None
  | Some p => mret (Some p)
  end.
Definition pmalloc (n : Z) : MP (option hptr) := r <- ho_malloc HO n ;; enomem_on_null r.
Definition pcalloc (m n : Z) : MP (option hptr) := r <- ho_calloc HO m n ;; enomem_on_null r.
Definition prealloc (q : hptr) (n : Z) : MP (option hptr) := r <- ho_realloc HO q n ;; enomem_on_null r.
Definition pfree (q : hptr) : MP unit := ho_free HO q.

(* [comment removed for export] *)
Record FrameOps := mkFO {
  fo_enter : forall A : Type, fframe -> MP A -> MP A ;
  fo_ret : forall A : Type, fframe -> A -> MP A ;
  fo_site : PS -> stack_site -> option Z
}.
Arguments fo_enter _ {A} _ _.
Arguments fo_ret _ {A} _ _.
Definition fo_nop : FrameOps := mkFO (fun A _ m => m) (fun A _ x => mret x) (fun _ _ => None).

(* [comment removed for export] *)
Definition blk_addr (s : PS) (q : hptr) : Z := ho_addr HO (ps_heap s) q.
Definition file_buf_addr (s : PS) (q : hptr) : Z := blk_addr s q + FILE_BUF_OFF.   (* [comment removed for export] *)
Definition eval_rdest (FO : FrameOps) (stk : stack_site -> Z) (s : PS) (d : rdest hptr) : Z :=
  match d with
  | DHeap q off => blk_addr s q + off
  | DStack site off => match fo_site FO s site with Some a => a + off | None => stk site + off end
  end.

(* [comment removed for export] *)
Definition s_fopen := @fopen PS hptr ps_libc set_libc pmalloc.
Definition s_fclose := @fclose PS hptr ps_libc set_libc (ho_eqb HO) pfree.
Definition s_fwrite := @fwrite PS hptr ps_libc set_libc (ho_eqb HO).
Definition s_fread := @fread PS hptr ps_libc set_libc (ho_eqb HO) file_buf_addr.
Definition s_ferror := @ferror PS hptr ps_libc (ho_eqb HO).
Definition s_fileno := @fileno PS hptr ps_libc (ho_eqb HO).
Definition s_fprintf := @fprintf PS hptr ps_libc set_libc (ho_eqb HO).
Definition s_printf := @printf PS hptr ps_libc set_libc.
Definition s_remove := @remove PS hptr ps_libc set_libc.
Definition s_unlink := @unlink PS hptr ps_libc set_libc.
Definition s_mkstemp := @mkstemp PS hptr ps_libc set_libc.
Definition s_close := @close PS.
Definition s_get_errno := @get_errno PS hptr ps_libc.
Definition s_stdio_exit := @stdio_exit PS hptr ps_libc.

(* [comment removed for export] *)
Definition MOps : MonadOps MP := mkMonadOps MP (@mret PS) (@mbind PS) (@munr PS).

Definition prims (FO : FrameOps) (stk : stack_site -> Z) : Prims MP hptr hptr :=
  mkPrims MP hptr hptr
    (fun name => s_fopen name false)      (* [comment removed for export] *)
    (fun name => s_fopen name true)       (* [comment removed for export] *)
    s_fclose
    (fun f d n => s <- mget ;; s_fread f (eval_rdest FO stk s d) n)   (* [comment removed for export] *)
    s_fwrite
    s_ferror
    s_fileno
    s_get_errno
    s_fprintf
    s_printf
    pmalloc
    pcalloc
    prealloc
    pfree
    s_mkstemp
    s_close
    s_remove
    s_unlink
    (s <- mget ;; mret (ps_outfile s))          (* [comment removed for export] *)
    (fun o => mupd (set_outfile o))            (* [comment removed for export] *)
    (@fo_enter FO) (@fo_ret FO).               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition harness_call (FO : FrameOps) (stk : stack_site -> Z) (data : list Z) : MP Z :=
  LLVMFuzzerTestOneInput MOps (prims FO stk) data ;;;
  mret 0.

(* [comment removed for export] *)
Definition diag (d : diag_msg) : MP unit :=
  match d with
  | DUsage argv0 => @diag_usage PS hptr ps_libc set_libc argv0
  | DCannotOpen p => @diag_cannot_open PS hptr ps_libc set_libc p
  | DReadError p => @diag_read_error PS hptr ps_libc set_libc p
  | DOom => @diag_oom PS hptr ps_libc set_libc
  | DTooBig => @diag_too_big PS hptr ps_libc set_libc
  | DShortHdr => @diag_short_hdr PS hptr ps_libc set_libc
  | DCfgOverrun => @diag_cfg_overrun PS hptr ps_libc set_libc
  end.

Definition run (FO : FrameOps) (stk : stack_site -> Z) (config payload : list Z) : MP Z :=
  target_run pmalloc pfree (@emit_d PS hptr ps_libc set_libc) (harness_call FO stk) config payload.

Definition main_prog (FO : FrameOps) (stk : stack_site -> Z) (argv : list (list Z)) : MP Z :=
  main_model diag pmalloc pfree (stk SiteReadStage) (run FO stk) argv.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition set_tls_pin (tb : Z) (s : PS) : PS := set_tls tb (set_heap (ho_pin HO tb (ps_heap s)) s).

Definition prog (tb : Z) (FO : FrameOps) (stk : stack_site -> Z) (argv : list (list Z)) : MP Empty_set :=
  startup_model set_tls_pin tb ;;;
  code <- main_prog FO stk argv ;;
  exit_model s_stdio_exit code.

(* [comment removed for export] *)
Definition ps_init (h0 : H) : PS := mkPS h0 libc_init None 0.

Definition argv_Z (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.

(* [comment removed for export] *)
Definition prog_itree (tb : Z) (h0 : H) (FO : FrameOps) (stk : stack_site -> Z) (argv : list (list byte))
  : itree node (exc unit) :=
  ebind (prog tb FO stk (argv_Z argv) (ps_init h0))
        (fun p => match fst p : Empty_set with end).

End Prog.

End WithCeil.
