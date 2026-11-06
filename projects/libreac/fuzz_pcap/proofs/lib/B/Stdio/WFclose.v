From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane): the ASAN-UBSAN-image walk of musl fclose
   on libreac/fuzz_pcap's fmemopen READ stream, i.e. lib/A/Stdio/PFclose.v's afclose_source_spec_stk
   (unchanged, image-generic) at PFCLOSE_MUSL_STK, proved on the asan-ubsan image.

   PORTED from a Theorem Labs lane's own proved ASan walk, a working branch 58e2132654e
   lib/A/Stdio/WFclose.v (afclose_source_spec_musl): the same four symbolic phases, the same
   hand-built phase-2 journal step (awr_byte has no disjunct for the open-file-list head; donor
   shape cgif AE24.v:176-225 + AE28.v:194 frameW), both arms of the FILE+124 (pipe_pid) test, and
   the two frees through YCbq's aj_free_null_at_io / aj_free_at_io. Every address is re-MEASURED on
   the asan-ubsan image BY SYMBOL + OFFSET, never by a numeric delta.

   IMAGE ROOT: the ORIGINAL v1.9.0 asan-ubsan set; the segments are AsanUbsan.M.loaded_segments.
   MEASURED in fuzz_pcap.nm.txt, fuzz_pcap.objdump.txt (sha256 49b2ad826669, af7c8be930de; internal record), the dumps of
   the pinned fuzz_pcap.asan-ubsan image's unstripped twin (sha256 c969d83cdd59; tool:
   GNU objdump / nm output already in those files, read with awk; the masked comparison against the asan
   dumps by cmpfn.py (sha256 b5223740aed9; internal record)). fclose / fflush are WEAK (W) symbols.

   MASKED-EQUAL to the asan code, symbol by symbol (cmpfn.py): fclose 51/51, __unlist_locked_file 1/1,
   __ofl_lock 12/12, __ofl_unlock 3/3, __lock 162/162, __unlock 29/29, mclose 2/2,
   ___interceptor_free 116/116. Every differing word is a pc-relative operand resolving to the SAME
   symbol + offset (the fflush / free trampolines, ofl_lock, __libc+3, stdout+0xf0).

   THE STACK BUDGET IS SOUND HERE TOO: fclose's frame is still 48 on asan-ubsan (`addi sp,sp,-48` at
   fclose+0 = 0x8e0e0) and both free calls (0x8e180, 0x8e188) sit at sp0 - 48 with no pop before them,
   so aj_free_*_at_io's `ASTACK - o <= STK` reads 16384 + 48 = 16432 = PFCLOSE_MUSL_STK, exactly tight
   as on asan. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YP0m YP0e YP09 YP02 YP0l YP0k YP08 YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YI16 YG0q YG0p YCbq YE01 YE00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFmopsM PFflush PFclose.
(* The asan-ubsan stdio pcs, from their one home (a working branch b4439851fa3): musl fclose
   PFCLOSE_MUSL_U 0x8e0e0, the fflush trampoline PFFLUSH_ICPT_U 0x41618, mclose PMCLOSE_U 0x8eb90. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PStdioImgB.
(* KS_U: a Theorem Labs lane's asan-ubsan pcap_KS (a working branch d6edf2117df; auditor PASSED 18/18). NOT
   lib/A/Stdio/PSourceK.v, which is the ASan record and is not in this file's closure. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* lia must keep its div / mod support here (cgif's AE2f disables it globally). The redefinition is LOCAL to
   this file: it does not escape the Require, so a file that Requires this one keeps its own setting. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* The asan-ubsan image of fuzz_pcap v1.9.0. *)
Definition wsegs : list Segment := AsanUbsan.M.loaded_segments.

Lemma wsegs_wx : wx_segs_nowrap wsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The image lies below the low-shadow start. The donor took this as a Section hypothesis; here it
   is discharged by evaluation (the form of pcapu_segs_low in WMclose.v (sha256 4729121bf767; internal record), a working branch). *)
Lemma wsegs_low : forall a, in_img wsegs a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hlo & Hhi).
  assert (Hb : forallb (fun s => (0 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd))
                 wsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb sg Hin).
  apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

(* The code the musl side of the walk steps through, MEASURED (asan-ubsan nm + objdump, symbol + offset):
     fclose                0x8e0e0 (nm W, size 0xcc), 51 insns (0x8e0e0..0x8e1a8)
     __unlist_locked_file  0x8e0dc (nm t, size 4), 1 insn (a bare ret)
     __ofl_lock            0x8f0a8 (nm t, size 0x30), 12 insns
     __ofl_unlock          0x8f0d8 (nm t, size 0xc), 3 insns (tail-jumps into __unlock)
     __lock                0x932f8 (nm t, size 0x288), 162 insns
     __unlock              0x93580 (nm t, size 0x74), 29 insns
     mclose                0x8eb90 (nm t, size 8), 2 insns (li a0,0; ret) -- f->close, reached by an
                           indirect jalr whose target source_static pins to as_close KS_U
   DELIBERATELY ABSENT, so that the symbolic run STOPS there and a contract takes over:
     0x41618 __interceptor_trampoline_fflush, 0x52c24 __interceptor_trampoline_free (nm T, size 4). *)
(* fclose and mclose by their PStdioImgB names (PFCLOSE_MUSL_U 0x8e0e0, PMCLOSE_U 0x8eb90). *)
Definition wfc_ranges : list (Z * nat) :=
  [ (PFCLOSE_MUSL_U, 51%nat); ((symaddr Symbols.AsanUbsan.s___unlist_locked_file), 1%nat); ((symaddr Symbols.AsanUbsan.s___ofl_lock), 12%nat); ((symaddr Symbols.AsanUbsan.s___ofl_unlock), 3%nat);
    ((symaddr Symbols.AsanUbsan.s___lock), 162%nat); ((symaddr Symbols.AsanUbsan.s___unlock), 29%nat); (PMCLOSE_U, 2%nat) ].

Fixpoint wfc_build (rs : list (Z * nat)) (t : ctable) : ctable :=
  match rs with [] => t | (lo, n) :: rest => wfc_build rest (build_table wsegs lo n t) end.

Lemma wfc_build_ok : forall rs t,
  Forall (fun r => 0 <= fst r) rs -> table_ok wsegs t -> table_ok wsegs (wfc_build rs t).
Proof.
  induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
  inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.

Definition wfc_tbl : ctable := Eval vm_compute in wfc_build wfc_ranges TEmpty.
Lemma wfc_tbl_eq : wfc_tbl = wfc_build wfc_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl wfc_tbl). Qed.
Lemma wfc_tbl_ok : table_ok wsegs wfc_tbl.
Proof.
  rewrite wfc_tbl_eq. apply wfc_build_ok; [| apply table_ok_empty].
  unfold wfc_ranges, PFCLOSE_MUSL_U, PMCLOSE_U. repeat constructor; cbn; discriminate.
Qed.

(* The table holds what the walk steps through and NOT the two trampolines it must stop at
   (fclose PFCLOSE_MUSL_U, mclose PMCLOSE_U and the fflush trampoline PFFLUSH_ICPT_U by name). *)
Lemma wfc_tbl_probe :
  clookup wfc_tbl PFCLOSE_MUSL_U = Some 0xfd010113 /\
  clookup wfc_tbl (symaddr (Symbols.AsanUbsan.s_fclose + 0xc8)%Z) = Some 0x00008067 /\
  clookup wfc_tbl (symaddr Symbols.AsanUbsan.s___unlist_locked_file) = Some 0x00008067 /\
  clookup wfc_tbl (symaddr Symbols.AsanUbsan.s___ofl_lock) = Some 0xff010113 /\
  clookup wfc_tbl (symaddr Symbols.AsanUbsan.s___ofl_unlock) = Some 0x00566517 /\
  clookup wfc_tbl (symaddr Symbols.AsanUbsan.s___lock) = Some 0x00561597 /\
  clookup wfc_tbl (symaddr Symbols.AsanUbsan.s___unlock) = Some 0x00052583 /\
  clookup wfc_tbl PMCLOSE_U = Some 0x00000513 /\
  clookup wfc_tbl PFFLUSH_ICPT_U = None /\
  clookup wfc_tbl (symaddr Symbols.AsanUbsan.s___wrap_free) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition RUN (s : sstate) : sstate * run_status := sym_runN wsegs wfc_tbl FUEL s.
Definition RUNTO (stop : Z) (s : sstate) : sstate * run_status := sym_run_toN wsegs wfc_tbl FUEL stop s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (s : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG s r) v.
Definition chunk_is (off : Z) (n : N) (v : sv) (c : YP09.chunk) : bool :=
  (YP09.c_off c =? off) && match YP09.c_val c with CVal n' e => N.eqb n' n && sv_eqb e v | _ => false end.
Definition has_chunk (s : sstate) (i : nat) (off : Z) (n : N) (v : sv) : bool :=
  match nth_error (ss_mem s) i with
  | Some r => existsb (chunk_is off n v) (YP09.r_chunks r)
  | None => false
  end.

Lemma chunk_is_sound : forall off n v c, chunk_is off n v c = true -> c = YP09.mkChunk off (CVal n v).
Proof.
  intros off n v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc.
  apply andb_prop in Hc as [Ho Hv]. apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate.
  apply andb_prop in Hv as [Hn He]. apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.

(* The addresses of the walk, MEASURED on asan-ubsan by symbol + offset (asan value for comparison):
     the entry is musl fclose = fclose+0, nm W 0x8e0e0; it is KS_U's PCAP_REAL_FCLOSE, the word the
     REAL(fclose) cell 0x9b4c0 holds, so the interceptor's jalr lands exactly here (asan 0x8e214);
     `jal __interceptor_trampoline_fflush` at fclose+0x1c = 0x8e0fc, returning to fclose+0x20
     (asan 0x8e230 / 0x8e234); the trampoline is nm T 0x41618 = PStdioImgB's PFFLUSH_ICPT_U;
     the two `jal __interceptor_trampoline_free` at fclose+0xa0 = 0x8e180 and fclose+0xa8 = 0x8e188,
     returning to fclose+0xa4 = 0x8e184 and fclose+0xac = 0x8e18c (asan 0x8e2b4 / 0x8e2bc returning
     to 0x8e2b8 / 0x8e2c0); the free trampoline is nm T 0x52c24 (asan 0x52bd4). *)
(* The entry is PStdioImgB's PFCLOSE_MUSL_U and the fflush call target is PStdioImgB's
   PFFLUSH_ICPT_U: neither is re-declared here. *)
Definition WF_AFTFF  : Z := (symaddr (Symbols.AsanUbsan.s_fclose + 0x20)%Z).   (* fclose+0x20, the return address of that call *)
Definition WF_FREETR : Z := (symaddr Symbols.AsanUbsan.s___wrap_free).   (* __interceptor_trampoline_free *)
Definition WF_FREE1  : Z := (symaddr (Symbols.AsanUbsan.s_fclose + 0xa4)%Z).   (* fclose+0xa4, the return address of free(getln_buf) *)
Definition WF_JOIN   : Z := (symaddr (Symbols.AsanUbsan.s_fclose + 0xac)%Z).   (* fclose+0xac, the return address of free(f) *)
Definition WF_FRAME  : Z := 48.        (* addi sp,sp,-48 at fclose+0 = 0x8e0e0 *)
(* PStdioImgB's musl fclose entry is KS_U's REAL(fclose) word (a working branch d6edf2117df, an
   ancestor of a working branch b4439851fa3): the two homes agree. *)
Lemma WF_named_val : PFCLOSE_MUSL_U = PCAP_REAL_FCLOSE.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------------------------- *)
(* Phase 1: musl fclose's prologue, 0x8e0e0 up to the fflush call. Seven instructions: the frame,  *)
(* the five callee-saved stores, `mv s0,a0` and `jal 0x41618`, which leaves the table and stops.   *)
(* -------------------------------------------------------------------------------------------- *)
Definition stk1 : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition ss1 : sstate :=
  mkSS PFCLOSE_MUSL_U sr_atoms [stk1] None
       (mkFacts [(2%nat, mkAF (2^43) (2^47) 4); (10%nat, mkAF 4096 (2^47) 4)] [] []).
Definition e1 : sstate := Eval vm_compute in fst (RUN ss1).
Lemma r_1 : RUN ss1 = (e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

Definition KEPT1 : list Z := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition cells1 : list (Z * sv) :=
  [(-8, SOff 1 0); (-16, SOff 8 0); (-24, SOff 9 0); (-32, SOff 18 0); (-40, SOff 19 0)].
Definition shape1 (e : sstate) : bool :=
  (ss_pc e =? PFFLUSH_ICPT_U) && match ss_resv e with None => true | _ => false end
  && reg_is e 10 (SOff 10 0) && reg_is e 1 (SLit WF_AFTFF) && reg_is e 2 (SOff 2 (-48)) && reg_is e 8 (SOff 10 0)
  && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPT1
  && forallb (fun c => has_chunk e 0 (fst c) 8 (snd c)) cells1.
Lemma shape1_ok : shape1 e1 = true. Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------------------------- *)
(* The image cells the musl body reads, all MEASURED (asan-ubsan nm) and all fields of KS_U, the     *)
(* lib/B/Stdio/PSourceK.v pcap_KS:                                                                  *)
(*   ofl_head 0x5f4e88 (nm b, size 8; written: *head = f->next), ofl_lock 0x5f4e80 (nm b, size 4;   *)
(*   read by __unlock), need_locks 0x5f4a23 = __libc+3 (__libc nm b 0x5f4a20; read by __lock at      *)
(*   __lock+4 = 0x932fc, which objdump resolves to <__libc+0x3>), mclose 0x8eb90 (f->close).         *)
(* -------------------------------------------------------------------------------------------- *)
Definition WF_OFL_HEAD   : Z := (symaddr Symbols.AsanUbsan.s_ofl_head).
Definition WF_OFL_LOCK   : Z := (symaddr Symbols.AsanUbsan.s_ofl_lock).
Definition WF_NEED_LOCKS : Z := (symaddr (Symbols.AsanUbsan.s___libc + 0x3)%Z).
(* mclose is PStdioImgB's PMCLOSE_U, not re-declared. Each cell is the KS_U field of that name (and
   PMCLOSE_U is KS_U's PCAP_MCLOSE): the walk's literals are the record's values, not a second
   measurement. *)
Lemma WF_cells_val : WF_OFL_HEAD = as_ofl_head pcap_KS /\ WF_OFL_LOCK = PCAP_OFL_LOCK /\
  WF_NEED_LOCKS = PCAP_NEED_LOCKS /\ PMCLOSE_U = PCAP_MCLOSE.
Proof. repeat split; reflexivity. Qed.

(* -------------------------------------------------------------------------------------------- *)
(* Phase 2: from the fflush call's return 0x8e100 to the FIRST free call 0x8e180, whose target     *)
(* 0x52c24 is outside the table, so the run stops there.                                          *)
(*                                                                                                *)
(* What it covers: the f->close call (an indirect jalr through FILE+24, which source_static pins   *)
(* to mclose 0x8eb90 -- IN the table, two instructions, so the walk steps through it rather than   *)
(* taking a contract), __unlist_locked_file (a bare ret), __ofl_lock -> __lock (which returns at   *)
(* once because need_locks is 0), the list unlink, and __ofl_unlock -> __unlock (which returns at  *)
(* once because ofl_lock is 0).                                                                    *)
(*                                                                                                *)
(* TWO PARAMETERS, because musl branches on two FILE cells:                                        *)
(*   fl   FILE+0, the flags: `lbu;andi 1;bnez` at 0x8e128-0x8e134 is the F_PERM test. PSource.v's  *)
(*        source_flags pins fl to 8 or 24, and bit 0 of both is 0, so the arm at 0x8e18c (keep the *)
(*        FILE, just unlist) is UNREACHABLE. Both values are run below.                            *)
(*   pp   FILE+124, which `lw;beqz` at 0x8e100-0x8e108 tests to decide whether __ofl_lock runs     *)
(*        BEFORE f->close (s3 = the head) or after it (s3 = 0 first, then the call at 0x8e144).    *)
(*        PSource.v does NOT pin this cell (musl's pipe_pid). So the walk takes BOTH arms; they    *)
(*        converge at 0x8e14c with s3 = &ofl_head either way.                                      *)
(* -------------------------------------------------------------------------------------------- *)
Definition stk2 : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 48 (-16) 0 [].
Definition hdr2 (fl : Z) (pp : sv) : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 232 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit fl)); YP09.mkChunk 24 (CVal 8 (SLit PMCLOSE_U));
     YP09.mkChunk 104 (CVal 8 (SLit 0)); YP09.mkChunk 112 (CVal 8 (SLit 0));
     YP09.mkChunk 124 (CVal 4 pp); YP09.mkChunk 168 (CVal 8 (SLit 0))].
Definition oflR : YP09.region :=
  YP09.mkRegion None WF_OFL_HEAD (WF_OFL_HEAD + 8) WF_OFL_HEAD (WF_OFL_HEAD + 8)
    [YP09.mkChunk WF_OFL_HEAD (CVal 8 (SOff 8 0))].
Definition envR : list YP09.region :=
  [YP09.mkRegion None WF_NEED_LOCKS (WF_NEED_LOCKS + 1) 0 0 [YP09.mkChunk WF_NEED_LOCKS (CVal 1 (SLit 0))];
   YP09.mkRegion None WF_OFL_LOCK (WF_OFL_LOCK + 4) 0 0 [YP09.mkChunk WF_OFL_LOCK (CVal 4 (SLit 0))]].
Definition facts2 : list (nat * afact) :=
  [(2%nat, mkAF (2^43) (2^47) 4); (8%nat, mkAF 4096 (2^47) 4)].
Definition ss2 (fl : Z) (pp : sv) (fs : list (nat * afact)) (cs : list acond) : sstate :=
  mkSS WF_AFTFF sr_atoms ([stk2; hdr2 fl pp; oflR] ++ envR) None (mkFacts (facts2 ++ fs) cs []).

Definition e2a : sstate := Eval vm_compute in fst (RUN (ss2 8 (SLit 0) [] [])).
Lemma r_2a : RUN (ss2 8 (SLit 0) [] []) = (e2a, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition e2b : sstate := Eval vm_compute in fst (RUN (ss2 24 (SLit 0) [] [])).
Lemma r_2b : RUN (ss2 24 (SLit 0) [] []) = (e2b, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.

Definition KEPT2 : list Z := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shape2 (e : sstate) : bool :=
  (ss_pc e =? WF_FREETR) && match ss_resv e with None => true | _ => false end
  && reg_is e 10 (SLit 0) && reg_is e 1 (SLit WF_FREE1) && reg_is e 2 (SOff 2 0) && reg_is e 8 (SOff 8 0)
  && reg_is e 9 (SOff 10 0) && reg_is e 18 (SLit 0)
  && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPT2
  && has_chunk e 2 WF_OFL_HEAD 8 (SLit 0)
  && match nth_error (ss_mem e) 2 with Some r => obase_eqb (YP09.r_base r) None | None => false end.
Lemma shape2a_ok : shape2 e2a = true. Proof. vm_compute. reflexivity. Qed.
Lemma shape2b_ok : shape2 e2b = true. Proof. vm_compute. reflexivity. Qed.

(* The other arm of the FILE+124 test: a NON-ZERO 32-bit value, as the atom 32, carried as the
   branch condition the engine assumes (YP0m.v cond_assumed) -- a range fact alone does not let it
   decide `beqz` on the sign-extended load once the value reaches 2^31. wf_nz_cond below discharges
   the condition for every value in (0, 2^32). *)
Definition pp_nz : list acond := [mkAC BC_NE (SExt true 32 (SOff 32 0)) (SLit 0)].
Definition e2c : sstate := Eval vm_compute in fst (RUN (ss2 8 (SOff 32 0) [] pp_nz)).
Lemma r_2c : RUN (ss2 8 (SOff 32 0) [] pp_nz) = (e2c, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition e2d : sstate := Eval vm_compute in fst (RUN (ss2 24 (SOff 32 0) [] pp_nz)).
Lemma r_2d : RUN (ss2 24 (SOff 32 0) [] pp_nz) = (e2d, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma shape2c_ok : shape2 e2c = true. Proof. vm_compute. reflexivity. Qed.
Lemma shape2d_ok : shape2 e2d = true. Proof. vm_compute. reflexivity. Qed.

Lemma wf_nz_cond : forall (regs : bvmap 5 word) ppv, 0 < ppv < 2 ^ 32 ->
  conds_ok (Ereg regs [w64 ppv]) pp_nz.
Proof.
  intros regs ppv Hp. unfold pp_nz. cbn [conds_ok]. split; [|exact I].
  unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot].
  assert (X32 : ew (Ereg regs [w64 ppv]) 32 = w64 ppv)
    by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  rewrite X32. unfold w64. rewrite (unsigned_lit_small ppv) by lia. rewrite Z.add_0_r.
  change (sext 64 (bv_extract 0 32 (Z_to_bv 64 ppv)))
    with (if true then sext 64 (bv_extract 0 32 (Z_to_bv 64 ppv)) else zext 64 (bv_extract 0 32 (Z_to_bv 64 ppv))).
  rewrite zext_low_sound. cbn [branch_taken].
  destruct (bv_eqb (Z_to_bv 64 (zext_low true 32 ppv)) (Z_to_bv 64 0)) eqn:Eq; [exfalso | reflexivity].
  unfold bv_eqb in Eq. apply Z.eqb_eq in Eq. rewrite !Z_to_bv_unsigned in Eq.
  unfold zext_low, zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Eq.
  cbn [Z.of_N] in Eq. lia.
Qed.

(* -------------------------------------------------------------------------------------------- *)
(* Phase 3: the two instructions between the frees, 0x8e184 and 0x8e188. a0 = s0 = f, and the     *)
(* call leaves the table again.                                                                   *)
(* -------------------------------------------------------------------------------------------- *)
Definition ss3 : sstate := mkSS WF_FREE1 sr_atoms [] None (mkFacts [] [] []).
Definition e3 : sstate := Eval vm_compute in fst (RUN ss3).
Lemma r_3 : RUN ss3 = (e3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition KEPT3 : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shape3 (e : sstate) : bool :=
  (ss_pc e =? WF_FREETR) && match ss_resv e with None => true | _ => false end
  && reg_is e 10 (SOff 8 0) && reg_is e 1 (SLit WF_JOIN)
  && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPT3
  && match ss_mem e with [] => true | _ => false end.
Lemma shape3_ok : shape3 e3 = true. Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------------------------- *)
(* Phase 4: the join and the epilogue, 0x8e18c .. 0x8e1a8. The result is s2 | s1, i.e. mclose's   *)
(* 0 or'd with fflush's 0; the five callee-saved registers come back off the frame and the `ret`  *)
(* leaves through the restored ra, so the run stops at that indirect jump.                        *)
(* -------------------------------------------------------------------------------------------- *)
Definition stk4_chunks : list YP09.chunk :=
  [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
   YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
   YP09.mkChunk 8 (CVal 8 (SOff 36 0))].
Definition stk4 : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 0 0 stk4_chunks.
Definition ss4 : sstate :=
  mkSS WF_JOIN sr_atoms [stk4] None (mkFacts [(2%nat, mkAF (2^43) (2^47 - 48) 4)] [] []).
Definition e4 : sstate := Eval vm_compute in fst (RUN ss4).
Lemma r_4 : RUN ss4 = (e4, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition shape4 (e : sstate) : bool :=
  match ss_resv e with None => true | _ => false end
  && reg_is e 10 (SAlu ALU_OR (SOff 18 0) (SOff 9 0)) && reg_is e 1 (SOff 32 0) && reg_is e 2 (SOff 2 48)
  && reg_is e 8 (SOff 33 0) && reg_is e 9 (SOff 34 0) && reg_is e 18 (SOff 35 0) && reg_is e 19 (SOff 36 0)
  && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPT2
  && match ss_mem e with [_] => true | _ => false end.
Lemma shape4_ok : shape4 e4 = true. Proof. vm_compute. reflexivity. Qed.

(* The walk's two stops are the two trampolines, and nothing else: the arms the predicate makes
   unreachable (F_PERM at 0x8e18c, the prev / next unlink stores at 0x8e158 / 0x8e164) are never
   entered in any of the four runs above, which is what shape2 records by reaching 0x52c24 with
   a0 = 0 and the head cell already zeroed. *)

End W.

(* ================================================================================================ *)
(* Carrying the stream predicate across a phase: every cell PSource.v names lies in the FILE block, *)
(* in the data buffer, or in the image, and no phase of the body writes any of those except the     *)
(* open-file-list head.                                                                             *)
(* ================================================================================================ *)
Lemma wf_aview_mod : forall H (m : word -> option byte) a,
  aview wsegs H m a = aview wsegs H m (a mod 2 ^ 64).
Proof.
  intros H m a. assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. }
  unfold aview, mbyte. rewrite E. reflexivity.
Qed.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable K : asource_syms.
Hypothesis ASIL : asource_img_laws SK wsegs B K.

(* Four present bytes have a 32-bit value: FILE+124 (musl's pipe_pid) is read by the body but is
   not a cell PSource.v pins, so its value comes from the block's own bytes. *)
Lemma wf_val4_of_bytes : forall (m : word -> option byte) a,
  (forall k, 0 <= k < 4 -> exists b : byte, mbyte wsegs m (a + k) = Some b) ->
  exists v, 0 <= v < 2 ^ 32 /\ val_mem wsegs m a 4 v.
Proof.
  intros m a HB.
  destruct (HB 0 ltac:(lia)) as [c0 M0]. destruct (HB 1 ltac:(lia)) as [c1 M1].
  destruct (HB 2 ltac:(lia)) as [c2 M2]. destruct (HB 3 ltac:(lia)) as [c3 M3].
  pose proof (bv_unsigned_in_range 8 c0) as R0. pose proof (bv_unsigned_in_range 8 c1) as R1.
  pose proof (bv_unsigned_in_range 8 c2) as R2. pose proof (bv_unsigned_in_range 8 c3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
  set (v := bv_unsigned c0 + 256 * bv_unsigned c1 + 65536 * bv_unsigned c2 + 16777216 * bv_unsigned c3).
  assert (Hv : 0 <= v < 2 ^ 32) by (subst v; cbn; lia).
  exists v. split; [exact Hv|]. intros k Hk.
  assert (EQ : forall (c : byte) (q : Z), bv_unsigned c = q -> Z_to_bv 8 q = c)
    by (intros c q <-; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap;
        change (bv_modulus 8) with 256; apply Z.mod_small; pose proof (bv_unsigned_in_range 8 c) as Rc;
        unfold bv_modulus in Rc; cbn in Rc; lia).
  unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; lia).
  destruct k as [|[|[|[|k]]]]; try lia.
  - change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.add_0_r.
    rewrite Z.add_0_r in M0.
    rewrite (EQ c0 (v mod 256)); [exact M0 | subst v; lia].
  - change (Z.of_nat 1) with 1. change (8 * 1) with 8.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite (EQ c1 (v / 256 mod 256)); [exact M1 | subst v; lia].
  - change (Z.of_nat 2) with 2. change (8 * 2) with 16.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
    rewrite (EQ c2 (v / 65536 mod 256)); [exact M2 | subst v; lia].
  - change (Z.of_nat 3) with 3. change (8 * 3) with 24.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216.
    rewrite (EQ c3 (v / 16777216 mod 256)); [exact M3 | subst v; lia].
Qed.

Lemma wf_env_frame : forall (m m' : word -> option byte),
  (forall a, in_img wsegs a -> mbyte wsegs m' a = mbyte wsegs m a) ->
  asrc_stdio_env wsegs K m -> asrc_stdio_env wsegs K m'.
Proof.
  intros m m' HEQ (E1 & E2 & E3 & E4 & E5 & cval & Hcv & E6).
  assert (IMG : forall a, asrc_env_addr K a -> mbyte wsegs m' a = mbyte wsegs m a)
    by (intros a Ha; apply HEQ; exact (proj1 (asil_env _ _ _ _ ASIL a Ha))).
  unfold asrc_stdio_env.
  split; [eapply val_mem_frame; [|exact E1]; intros x Hx; apply IMG; unfold asrc_env_addr; lia|].
  split; [eapply val_mem_frame; [|exact E2]; intros x Hx; apply IMG; unfold asrc_env_addr; lia|].
  split; [eapply val_mem_frame; [|exact E3]; intros x Hx; apply IMG; unfold asrc_env_addr; lia|].
  split; [eapply garr8_frame; [exact E4|]; intros x Hx; apply IMG; unfold asrc_env_addr;
           cbn [length src_mode_Z app] in Hx; lia|].
  split; [eapply garr8_frame; [exact E5|]; intros x Hx; apply IMG; unfold asrc_env_addr;
           cbn [length src_modeset_Z app] in Hx; lia|].
  exists cval. split; [exact Hcv|].
  eapply val_mem_frame; [|exact E6]. intros x Hx. apply IMG. unfold asrc_env_addr. lia.
Qed.

Lemma wf_rodata_frame : forall (W : world wsegs) (mem mem' : word -> option byte) (lo hi rlo rhi : Z),
  (forall a, in_img wsegs a -> 0 <= a < kLowMemEnd) ->
  alloc_ceiling <= lo -> lo <= hi ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     aview wsegs (w_H W) mem' a = aview wsegs (w_H W) mem a) ->
  (forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
  arodata_okS wsegs B rlo rhi (aview wsegs (w_H W) mem) ->
  arodata_okS wsegs B rlo rhi (aview wsegs (w_H W) mem').
Proof.
  intros W mem mem' lo hi rlo rhi SLOW Hlo Hlh AVk PRS HRO a Ha Hns He.
  pose proof asan_consts as (C1 & _).
  assert (Hmod : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. }
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  rewrite (wf_aview_mod (w_H W) mem' a). pose proof (HRO a Ha Hns He) as Hold.
  rewrite (wf_aview_mod (w_H W) mem a), Hmod in Hold.
  destruct (Z_le_gt_dec lo (a mod 2 ^ 64)) as [H1|H1];
    [destruct (Z_lt_ge_dec (a mod 2 ^ 64) hi) as [H2|H2]|].
  - exfalso. pose proof (PRS _ (conj H1 H2)) as Hp.
    assert (Hni : ~ in_img wsegs (a mod 2 ^ 64)) by (intros Hi; pose proof (SLOW _ Hi); unfold kLowMemEnd in *; lia).
    rewrite (seg_rom_none wsegs (a mod 2 ^ 64) Hr Hni) in Hold. cbn in Hold.
    exact (aview_some_of_apresent wsegs (w_H W) mem _ Hp Hold).
  - rewrite (AVk _ Hr ltac:(lia)). rewrite Hold, Hmod. reflexivity.
  - rewrite (AVk _ Hr ltac:(lia)). rewrite Hold, Hmod. reflexivity.

Qed.

Lemma wf_asource_frame : forall (m m' : word -> option byte) f b C p,
  (forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte wsegs m' a = mbyte wsegs m a) ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte wsegs m' a = mbyte wsegs m a) ->
  (forall a, in_img wsegs a -> mbyte wsegs m' a = mbyte wsegs m a) ->
  asource_at wsegs K m f b C p -> asource_at wsegs K m' f b C p.
Proof.
  intros m m' f b C p HF HB HI
    (Wn & cpos & fl & md & Hp0 & Hpc & Hcn & Hn63 & Hbw & Hcp & HW & Hbo & Hgar &
     (S24 & S64 & S72 & S80 & S88 & S96 & S240 & S248 & S256 & S264 & S152 & S32 & S40 & S48 & S56 &
      S104 & S112 & S168 & S120 & S140 & S144 & Hf0 & Hfal & Hb0 & Hdisj)
     & Hwin & (Hfl & Hflv) & Hfeof & (Hmd & Hmdv) & Hcook & Henv & Hhead & Hfnz).
  assert (IMG : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> mbyte wsegs m' a = mbyte wsegs m a).
  { intros a Ha. apply HI.
    assert (Hin : asrc_env_addr K a) by (unfold asrc_env_addr, as_ofl_head in *; lia).
    exact (proj1 (asil_env _ _ _ _ ASIL a Hin)). }
  exists Wn, cpos, fl, md.
  split; [exact Hp0|]. split; [exact Hpc|]. split; [exact Hcn|]. split; [exact Hn63|].
  split; [exact Hbw|]. split; [exact Hcp|]. split; [exact HW|]. split; [exact Hbo|].
  split; [eapply garr8_frame; [exact Hgar|]; intros x Hx; apply HB; lia|].
  split.
  { unfold source_static.
    repeat (split; [first [ eapply val_mem_frame;
              [ intros x Hx; apply HF; unfold SRC_FILE_BLOCK, SRC_COOKIE_OFF in *; cbn in Hx; lia
              | eassumption ]
            | assumption ] |]).
    assumption. }
  split.
  { destruct Hwin as [(HWe & H8 & H16) | (i & Hi0 & Hihi & H8 & H16 & Hgw)].
    - left. split; [exact HWe|].
      split; [eapply val_mem_frame; [intros x Hx; apply HF; unfold SRC_FILE_BLOCK in *; cbn in Hx; lia | exact H8]|].
      eapply val_mem_frame; [intros x Hx; apply HF; unfold SRC_FILE_BLOCK in *; cbn in Hx; lia | exact H16].
    - right. exists i. split; [exact Hi0|]. split; [exact Hihi|].
      split; [eapply val_mem_frame; [intros x Hx; apply HF; unfold SRC_FILE_BLOCK in *; cbn in Hx; lia | exact H8]|].
      split; [eapply val_mem_frame; [intros x Hx; apply HF; unfold SRC_FILE_BLOCK in *; cbn in Hx; lia | exact H16]|].
      eapply garr8_frame; [exact Hgw|]. intros x Hx. apply HF.
      unfold SRC_FILE_BLOCK, SRC_BUF_OFF, SRC_BUFSIZ in *. lia. }
  split.
  { unfold source_flags. split; [| exact Hflv].
    eapply val_mem_frame; [intros x Hx; apply HF; unfold SRC_FILE_BLOCK in *; cbn in Hx; lia | exact Hfl]. }
  split; [exact Hfeof|].
  split.
  { unfold source_mode. split; [| exact Hmdv].
    eapply val_mem_frame; [intros x Hx; apply HF; unfold SRC_FILE_BLOCK in *; cbn in Hx; lia | exact Hmd]. }
  split.
  { eapply val_mem_frame; [intros x Hx; apply HF; unfold SRC_FILE_BLOCK, SRC_COOKIE_OFF in *; cbn in Hx; lia | exact Hcook]. }
  split; [exact (wf_env_frame m m' HI Henv)|].
  split; [| exact Hfnz].
  eapply val_mem_frame; [intros x Hx; apply IMG; cbn in Hx; lia | exact Hhead].
Qed.

End F.


(* ================================================================================================ *)
(* The journal side: each symbolic phase above, carried over the core's allocator journal           *)
(* (YCbq.v SRr_run_AJ), so that AR and the kept-memory clauses come with it.                        *)
(* ================================================================================================ *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* AR_laws needs no hypothesis: lib/Reusable/YG0q.v:804 proves it for every segs and B. *)
Local Notation LAWS := (AR_laws_ok wsegs B).
(* The donor's Section hypothesis SEGS_LOW, discharged: wsegs_low above, by evaluation. *)
Local Notation SEGS_LOW := wsegs_low.
Local Notation AJ := (ajournal wsegs B).

(* The token-aware journal composition, ajournal_sub_tok, COPIED VERBATIM (statement and proof; only
   segs / segs_low specialised to wsegs / wsegs_low) from lib/A/Prog/YC85.v:33 (a working branch
   02075de74ec; identical text in a working branch 27d40cfe97f's YC85.v and in a working branch's image-free split
   YC85G.v f5f4434265d). It is NOT Required from YC85.v because YC85.v Requires lib/A/Prog/PcapSyms
   and PcapPa (the ASan program listing), which the lib/B closure rule keeps out of this file's
   closure; YC85G.v is not in this file's union. Every name it uses is lib/Reusable's (YCbq, YA0n,
   YG0f, YI04). It composes the fflush call's journal: asource_fp carries YI16.sink_token, so the
   plain ajournal_sub does not apply. *)
Lemma wf_ajournal_sub_tok : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
ajournal wsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
ajournal wsegs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
ajournal wsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT)
(HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & G5 & HQT2) Hlo Hhi HF.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [eapply wle_trans; eassumption|].
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0). destruct (HF 0 (ex_intro _ r (conj Hr H0))) as [(r' & Hr' & H0') | (b & n & Hin & _ & Hb)].
- exists r'. split; [exact Hr' | exact H0'].
- exfalso. pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _). zlia. }
split; [eapply aos_step_trans_fp; [exact HFo | exact Hio | exact Hio2]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [zlia|]. split; [zlia|].
split.
{   intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | zlia]. }
split.
{   intros p n i H1 H2 Hi Hnf.
assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
intros Hf1. destruct (HF _ Hf1) as [Hf | (b & m & Hbin & Hb0 & Hr)]; [exact (Hnf Hf)|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
pose proof (sep_blocks wsegs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{   intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). apply (G3 a Hi Hns He). intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{   intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
apply (G4 cid pos a HinC).
- unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr.
- intros Hf1. destruct (HF _ Hf1) as [Hf | (b & m & Hbin & Hb0 & Hrb)]; [exact (Hnf Hf)|].
destruct (frames_bounds wsegs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
pose proof (sep_block_frame wsegs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. rewrite Efr in Hd.
pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)).
pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)).
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
destruct Hr as [Hr|Hr]; zlia. }
split.
{   intros p n i H1 H2 Hi.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [|exact (Hgone p n i H1 Hc Hi)].
assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
destruct (HF _ Hf1) as [Hf | (b & m & Hbin & Hb0 & Hr)]; [exact Hf|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
pose proof (sep_blocks wsegs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{   intros a Ha.
destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; zlia|]].
- eapply (apresent_transfer wsegs); [zlia | intros Him; pose proof (SEGS_LOW a Him); zlia | apply G1; zlia | apply Hpres; exact Ha].
- eapply (apresent_transfer wsegs); [zlia | intros Him; pose proof (SEGS_LOW a Him); zlia | apply G1; zlia | apply Hpres; exact Ha]. }
split; [exact Hstatic|]. split; [|exact HQT2].
{   intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
apply G5; [rewrite Eextra; exact HXa | exact He]. }
Qed.

(* The eight bytes of musl's open-file-list head are WRITABLE image bytes: that cell is the only
   image byte fclose stores to (`sd a0,0(s3)` at fclose+0x94 = 0x8e174). MEASURED on the image itself. *)
Lemma wf_ofl_img_facts : forall i, 0 <= i < 8 ->
  img_writable_ok wsegs (WF_OFL_HEAD + i) = true /\
  seg_rom wsegs (Z_to_bv 64 (WF_OFL_HEAD + i)) <> None.
Proof.
  intros i Hi.
  assert (C : forall j, In j [0; 1; 2; 3; 4; 5; 6; 7] ->
    img_writable_ok wsegs (WF_OFL_HEAD + j) = true /\
    seg_rom wsegs (Z_to_bv 64 (WF_OFL_HEAD + j)) <> None).
  { intros j Hj. cbn [In] in Hj.
    repeat (destruct Hj as [<- | Hj]; [vm_compute; split; [reflexivity | discriminate]|]). destruct Hj. }
  apply C. cbn [In]. lia.
Qed.

Lemma wf_ofl_writable : forall (m : word -> option byte) o, 0 <= o < 8 ->
  writable_at wsegs m (WF_OFL_HEAD + o).
Proof.
  intros m o Ho. destruct (wf_ofl_img_facts o Ho) as [Hw _]. unfold img_writable_ok in Hw.
  apply (writable_at_grows wsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
  unfold writable_at.
  destruct (wview wsegs (fun _ => None) (Z_to_bv 64 (WF_OFL_HEAD + o))); [discriminate | discriminate Hw].
Qed.



(* The donor's frameW (cgif A/AE28.v:194) for this lane's write set: musl fclose's body writes
   ONLY its own stack window and the open-file-list head. Neither is owned, so AR survives, and
   everything outside the two is kept byte for byte. *)
Lemma wf_frameW : forall ly S (W : world wsegs) (memA mem1 : word -> option byte) mdA md1
    (Wr : Z -> Prop) (sp0 : Z),
  AR wsegs B ly S W memA mdA ->
  (forall a, Wr a \/ ~ Wr a) ->
  (forall a, Wr a -> (sp0 - PFCLOSE_MUSL_STK <= a < sp0) \/ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8)) ->
  (forall z : word, ~ Wr (bv_unsigned z) -> mem1 z = memA z) ->
  (forall a, Wr a -> ~ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) -> apresent (w_H W) mem1 a) ->
  same_but_materialized mdA md1 ->
  alloc_ceiling <= ly_stk_lo ly -> ly_stk_lo ly + PFCLOSE_MUSL_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
  (forall a, WF_OFL_HEAD <= a < WF_OFL_HEAD + 8 -> ~ aowned B ly S a) ->
  (forall a, sp0 - PFCLOSE_MUSL_STK <= a < sp0 -> apresent (w_H W) memA a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview wsegs (w_H W) mem1 a = aview wsegs (w_H W) memA a) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) ->
             apresent (w_H W) memA a -> apresent (w_H W) mem1 a) /\
  AR wsegs B ly S W mem1 md1.
Proof.
  intros ly S W memA mem1 mdA md1 Wr sp0 HAR Wdec HWin MEQ PRS MF Hceil Hslo Hshi HOFLown Hpres.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : PFCLOSE_MUSL_STK = 16432) by reflexivity. rewrite FS in Hslo, HWin, Hpres.
  assert (HD : WF_OFL_HEAD = (symaddr Symbols.AsanUbsan.s_ofl_head)) by reflexivity. rewrite HD in HWin, PRS, HOFLown.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
               aview wsegs (w_H W) mem1 a = aview wsegs (w_H W) memA a).
  { intros a Hr Hw. apply aview_eq_of. unfold mrestrict.
    destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
    apply MEQ. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hw. }
  assert (PM : forall a, 0 <= a < 2 ^ 64 -> ~ ((symaddr Symbols.AsanUbsan.s_ofl_head) <= a < (symaddr Symbols.AsanUbsan.s_ofl_head) + 8) ->
               apresent (w_H W) memA a -> apresent (w_H W) mem1 a).
  { intros a Hr Ho Hp. destruct (Wdec a) as [Hw|Hw]; [exact (PRS a Hw Ho)|].
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply MEQ.
    rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hw. }
  split; [exact AV|]. split; [rewrite HD; exact PM|].
  pose proof (same_but_materialized_frame mdA md1 MF)
    as (_ & Fmaps & Flazy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Feu).
  apply (al_frame _ _ LAWS ly S W memA mdA mem1 _ HAR).
  - intros a Hr Hown. apply AV; [exact Hr|]. intros Hw.
    destruct (HWin a Hw) as [Hs | Ho].
    + exact (al_stack _ _ LAWS ly S W memA mdA a HAR ltac:(lia) Hown).
    + exact (HOFLown a Ho Hown).
  - intros a Hv. rewrite (wf_aview_mod (w_H W) mem1 a). rewrite (wf_aview_mod (w_H W) memA a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    set (a' := a mod 2 ^ 64) in *.
    destruct (Wdec a') as [Hw|Hw]; [| rewrite AV by assumption; exact Hv].
    destruct (HWin a' Hw) as [Hs | Ho].
    + apply aview_some_of_apresent. apply PRS; [exact Hw | lia].
      
    + unfold aview, mbyte. destruct (mrestrict (w_H W) mem1 (Z_to_bv 64 a')) as [b|]; [cbn; discriminate|].
      destruct (wf_ofl_img_facts (a' - (symaddr Symbols.AsanUbsan.s_ofl_head)) ltac:(lia)) as [_ Hrom]. rewrite HD in Hrom.
      replace ((symaddr Symbols.AsanUbsan.s_ofl_head) + (a' - (symaddr Symbols.AsanUbsan.s_ofl_head))) with a' in Hrom by lia.
      destruct (seg_rom wsegs (Z_to_bv 64 a')); [cbn; discriminate | exfalso; exact (Hrom eq_refl)].
  - exact Fmaps.
  - exact Flazy.
  - exact Feu.
  - intros a Hband Hh. apply MEQ. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64).
    assert (Hra : 0 <= a < 2 ^ 64)
      by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband; lia).
    rewrite Z.mod_small by lia. intros Hw. destruct (HWin a Hw) as [Hs | Ho].
    + pose proof (Hpres a Hs) as [Hn0 _]. unfold w64 in Hh. rewrite Hh in Hn0. discriminate.
    + unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband.
      unfold WF_OFL_HEAD in Ho. lia.
Qed.

(* The journal after a write confined to the stack window and the open-file-list head: the donor
   builds this by hand (cgif A/AE24.v:176-225, its J1), because awr_byte (YCbq.v:457) has no
   disjunct for the head and so SRr_run_AJ / ajournal_after_write cannot carry that store. Every
   clause is the old one, read through the kept-memory fact: the head lies in the image and below
   alloc_ceiling, so the only clause it could touch is the image clause, and there fp_spares
   excludes it because the footprint is sink-open (asource_fp's token). *)
Lemma wf_journal_write : forall sp0 FP ly S (W0 W : world wsegs) mem0 md0 own lyc Sc mem mdc k mem1 md1,
  AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdc k ->
  YI16.sink_open_fp FP -> AOFL_HEAD = WF_OFL_HEAD ->
  (forall a, WF_OFL_HEAD <= a < WF_OFL_HEAD + 8 -> in_img wsegs a) ->
  AR wsegs B lyc Sc W mem1 md1 ->
  same_but_materialized mdc md1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - PFCLOSE_MUSL_STK <= a < sp0) -> ~ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) ->
     aview wsegs (w_H W) mem1 a = aview wsegs (w_H W) mem a) ->
  (forall a, sp0 - PFCLOSE_MUSL_STK <= a < sp0 -> apresent (w_H W) mem1 a) ->
  AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k.
Proof.
  intros sp0 FP ly S W0 W mem0 md0 own lyc Sc mem mdc k mem1 md1 HJ Hopen HHD HHIMG HAR1 MF AVk PRS1.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres
                    & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : PFCLOSE_MUSL_STK = 16432) by reflexivity.
  assert (HD : WF_OFL_HEAD = (symaddr Symbols.AsanUbsan.s_ofl_head)) by reflexivity.
  rewrite FS in *. rewrite HD in *.
  assert (NOHEAD_HI : forall a, alloc_ceiling <= a -> ~ ((symaddr Symbols.AsanUbsan.s_ofl_head) <= a < (symaddr Symbols.AsanUbsan.s_ofl_head) + 8)) by (intros; lia).
  split; [exact HAR1|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
  split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, MF]|].
  split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
  split.
  { intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply AVk; [lia | exact Hs | apply NOHEAD_HI; lia]. }
  split.
  { intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
    destruct (al_blocks _ _ LAWS lyc Sc W mem mdc p n HAR H2) as (_ & Hp0 & Hpc & _).
    apply AVk; [lia | lia |].
    intros Ho. exact (blk_img wsegs B LAWS lyc Sc W mem mdc p n (p + i) HAR H2 ltac:(lia) (HHIMG _ Ho)). }
  split.
  { intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (SEGS_LOW a Hi) as Ra.
    apply AVk; [lia | lia |]. intros Ho. apply (Hsp Hopen). rewrite HHD. exact Ho. }
  split.
  { intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
    assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
    assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    destruct (frames_bounds wsegs B LAWS lyc Sc W mem mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfapp).
    rewrite Efr in Hf0, Hfc. pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. destruct Hr as [Hr | Hr].
    - apply AVk; [lia | lia |]. intros Ho.
      apply (frm_img wsegs B LAWS lyc Sc W mem mdc cid pos a HAR HinC ltac:(rewrite Efr; lia) (HHIMG _ Ho)).
    - pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(unfold kHighMemEnd; lia)) as [B1 B2].
      pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
      pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid)
                    ltac:(unfold kHighMemEnd; lia)) as [U1 U2].
      apply AVk; unfold kLowMemEnd, kHighShadowEnd in *; lia. }
  split; [exact Hgone|].
  split; [exact PRS1|].
  split; [exact Hstatic|].
  split; [| exact HQT].
  { intros a HXa He. rewrite <- (F5 a HXa He).
    pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
    assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
    pose proof (AR_extra_law_ok wsegs B lyc Sc W mem mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
    pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
    apply AVk.
    - unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. lia.
    - intros Hs. apply Xs. rewrite Eslo, Eshi. lia.
    - intros Ho. exact (Xi (HHIMG _ Ho)). }
Qed.

(* A plain symbolic run that also hands back that the visible memory only GREW and the hidden
   memory is untouched: YCbq.v's SRr_chain_AJ without its journal (phase 2 cannot use the journal
   run, see wf_journal_write). *)
Lemma wf_run_grow : forall (W : world wsegs) n E ss ss' st ms model (Q : world wsegs -> config -> Prop),
  st_ok wsegs E ss (restrict (w_H W) ms) ->
  sym_runN wsegs wfc_tbl n ss = (ss', st) ->
  match st with RS_ecall => False | _ => True end ->
  (forall ms' mat',
     st_ok wsegs E ss' (restrict (w_H W) ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     (forall x, w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     SRr wsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q) ->
  SRr wsegs W (mkCfg ms model) Q.
Proof.
  intros W n E ss ss' st ms model Q HS Hrun Hst Hk.
  destruct (msteps_run_gen wsegs wfc_tbl wfc_tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
  apply (SRr_msteps wsegs wsegs_wx W ms msr' model Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb model model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  pose proof (msteps_mem_grows wsegs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
  apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
  - rewrite Hrr. destruct st; [exact HS' | destruct Hst | exact HS'].
  - rewrite Hmm. exact Hfr.
  - rewrite Hmm. exact Hgr.
  - intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
Qed.

(* Phase 2 as a journal step, built by hand. It writes the stack window [sp0 - 64, sp0 - 48)
   (__ofl_lock's frame) and the open-file-list head (`*head = f->next = 0`), and nothing else.
   Generic in the two cells musl branches on: the four runs of Section W instantiate it. *)
Lemma wf_step2_gen : forall (W W0 : world wsegs) ly S mem0 md0 own lyc Sc
    (regs : bvmap 5 word) (mem : word -> option byte) (mdc : Model) k sp0 FP f fl ppv
    (pp : sv) (fs : list (nat * afact)) (cs : list acond) (e : sstate) (Q : world wsegs -> config -> Prop),
  regions_wf ([stk2; hdr2 fl pp; oflR] ++ envR) = true ->
  RUN (ss2 fl pp fs cs) = (e, RS_stopped SR_fetch) -> shape2 e = true ->
  sv_denot (Ereg regs [w64 ppv]) pp = w64 ppv ->
  atoms_ok (Ereg regs [w64 ppv]) fs ->
  conds_ok (Ereg regs [w64 ppv]) cs ->
  AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdc k ->
  YI16.sink_open_fp FP -> AOFL_HEAD = WF_OFL_HEAD ->
  spZ regs = sp0 - 48 -> getr regs 8 = w64 f ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) ->
  0 <= fl < 2 ^ 32 -> 0 <= ppv < 2 ^ 32 ->
  (forall a, (WF_NEED_LOCKS <= a < WF_NEED_LOCKS + 1) \/ (WF_OFL_LOCK <= a < WF_OFL_LOCK + 4) \/
             (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) -> in_img wsegs a) ->
  (forall a, WF_OFL_HEAD <= a < WF_OFL_HEAD + 8 -> ~ aowned B lyc Sc a) ->
  val_mem wsegs (mrestrict (w_H W) mem) f 4 fl ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 24) 8 PMCLOSE_U ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 104) 8 0 ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 112) 8 0 ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 124) 4 ppv ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 168) 8 0 ->
  val_mem wsegs (mrestrict (w_H W) mem) WF_OFL_HEAD 8 f ->
  val_mem wsegs (mrestrict (w_H W) mem) WF_NEED_LOCKS 1 0 ->
  val_mem wsegs (mrestrict (w_H W) mem) WF_OFL_LOCK 4 0 ->
  (forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mdc1 : Model),
     AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 mdc1 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0 - 48) -> ~ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) ->
        aview wsegs (w_H W) mem1 a = aview wsegs (w_H W) mem a) ->
     val_mem wsegs (mrestrict (w_H W) mem1) WF_OFL_HEAD 8 0 ->
     same_io mdc mdc1 ->
     getr regs1 10 = w64 0 -> getr regs1 1 = w64 WF_FREE1 -> getr regs1 2 = w64 (sp0 - 48) ->
     getr regs1 8 = w64 f -> getr regs1 9 = getr regs 10 -> getr regs1 18 = w64 0 ->
     (forall r, In r KEPT2 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     SRr wsegs W (cfg_at wsegs WF_FREETR regs1 mem1 mdc1) Q) ->
  SRr wsegs W (cfg_at wsegs WF_AFTFF regs mem mdc) Q.
Proof.
intros W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP f fl ppv pp fs cs e Q
       HWF HRUN HSH HPP HATOMS HCONDS HJ Hopen HHD Hsp G8 Hblk Hfl Hppv HIMG HOWN
       Vfl V24 V104 V112 V124 V168 Vhead Vnl Vlock HK.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : PFCLOSE_MUSL_STK = 16432) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W mem mdc f SRC_FILE_BLOCK HAR Hblk) as (Hf16 & Hf0 & Hfceil & _).
assert (RQ : req_size SRC_FILE_BLOCK = 1304) by reflexivity. rewrite RQ in Hfceil.
assert (E2 : ew (Ereg regs [w64 ppv]) 2 = getr regs 2) by (apply (ew_Ereg_nat regs _ 2 2%bv); reflexivity).
assert (E2u : bv_unsigned (ew (Ereg regs [w64 ppv]) 2) = sp0 - 48) by (rewrite E2; exact Hsp).
assert (E8 : ew (Ereg regs [w64 ppv]) 8 = w64 f) by (rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact G8).
assert (E8u : bv_unsigned (ew (Ereg regs [w64 ppv]) 8) = f) by (rewrite E8; apply unsigned_lit_small; lia).
assert (NOIMG : forall a, f <= a < f + 1304 -> ~ in_img wsegs a)
  by (intros a Ha; exact (blk_img wsegs B LAWS lyc Sc W mem mdc f SRC_FILE_BLOCK a HAR Hblk ltac:(rewrite RQ; lia))).
assert (DISJ : forall lo hi, (forall a, lo <= a < hi -> in_img wsegs a) -> lo < hi -> f + 232 <= lo \/ hi <= f).
{ intros lo hi Himg Hlh.
  destruct (Z_le_gt_dec (f + 232) lo) as [Hx|Hx]; [left; exact Hx|].
  destruct (Z_le_gt_dec hi f) as [Hy|Hy]; [right; exact Hy|].
  exfalso. apply (NOIMG (Z.max lo f)); [lia|]. apply Himg. lia. }
assert (DNL : f + 232 <= WF_NEED_LOCKS \/ WF_NEED_LOCKS + 1 <= f)
  by (apply DISJ; [intros a Ha; apply HIMG; left; exact Ha | unfold WF_NEED_LOCKS; lia]).
assert (DOL : f + 232 <= WF_OFL_LOCK \/ WF_OFL_LOCK + 4 <= f)
  by (apply DISJ; [intros a Ha; apply HIMG; right; left; exact Ha | unfold WF_OFL_LOCK; lia]).
assert (DOH : f + 232 <= WF_OFL_HEAD \/ WF_OFL_HEAD + 8 <= f)
  by (apply DISJ; [intros a Ha; apply HIMG; right; right; exact Ha | unfold WF_OFL_HEAD; lia]).
unfold cfg_at.
assert (HS : st_ok wsegs (Ereg regs [w64 ppv]) (ss2 fl pp fs cs)
                   (restrict (w_H W) (mkst regs (w64 WF_AFTFF) mem (seg_rom wsegs)))).
{ rewrite restrict_mkst_fx. unfold ss2. apply (entry_st_ok_full wsegs).
  - apply regs_ok_Ereg.
  - exact HWF.
  - apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
    + unfold stk2, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2u.
      split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
      intros o Ho. apply apresent_writable. apply Hpres. rewrite FS. lia.
    + unfold hdr2, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E8u.
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ f 0 4 (SLit fl) fl);
        [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vfl]|].
      apply Forall_cons; [eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ f 24 8 (SLit PMCLOSE_U) PMCLOSE_U);
        [reflexivity | unfold PMCLOSE_U; cbn; lia | cbn; lia | exact V24]|].
      apply Forall_cons; [eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ f 104 8 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia | exact V104]|].
      apply Forall_cons; [eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ f 112 8 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia | exact V112]|].
      apply Forall_cons; [eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ f 124 4 pp ppv);
        [exact HPP | cbn; lia | cbn; lia | exact V124]|].
      apply Forall_cons; [eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ f 168 8 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia | exact V168]|].
      apply Forall_nil.
    + unfold oflR, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold WF_OFL_HEAD; lia|]. split; [unfold WF_OFL_HEAD; lia|]. split.
      { intros o Ho. rewrite Z.add_0_l. replace o with (WF_OFL_HEAD + (o - WF_OFL_HEAD)) by lia.
        apply wf_ofl_writable. lia. }
      apply Forall_cons; [| apply Forall_nil].
      eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ 0 WF_OFL_HEAD 8 (SOff 8 0) f);
        [cbn [sv_denot]; rewrite E8u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Vhead].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold WF_NEED_LOCKS; lia|]. split; [unfold WF_NEED_LOCKS; lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [| apply Forall_nil].
      eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ 0 WF_NEED_LOCKS 1 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Vnl].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold WF_OFL_LOCK; lia|]. split; [unfold WF_OFL_LOCK; lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [| apply Forall_nil].
      eapply (chunk_ok_val wsegs (Ereg regs [w64 ppv]) _ 0 WF_OFL_LOCK 4 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Vlock].
  - apply pairwise_disjoint_of_extents.
    unfold stk2, hdr2, oflR, envR, extent_of_region.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2u, E8u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold WF_OFL_HEAD, WF_NEED_LOCKS, WF_OFL_LOCK in *. rewrite FS in Hslo.
    repeat split; lia.
  - split; [| split; [exact HCONDS | exact I]].
    cbn [f_atoms facts2 app atoms_ok]. split; [|split; [|exact HATOMS]];
      unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?E2u, ?E8u;
      rewrite FS in Hslo; change (2 ^ 4) with 16; repeat split; lia. }
eapply (wf_run_grow W FUEL (Ereg regs [w64 ppv]) (ss2 fl pp fs cs) e _ (mkst regs (w64 WF_AFTFF) mem (seg_rom wsegs))
                    mdc Q HS HRUN I).
intros ms' mat' HS' HFr HGr HHid. cbn [ms_mem mkst] in HFr, HGr, HHid.
set (md1 := with_vm_backing (m_vm_lazy mdc) mat' mdc).
assert (MF : same_but_materialized mdc md1) by (apply same_but_materialized_wvb_any).
assert (WIN : forall a, in_wrange (Ereg regs [w64 ppv]) (ss_mem (ss2 fl pp fs cs)) a ->
              (sp0 - 64 <= a < sp0 - 48) \/ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8)).
{ intros a Hin. destruct (in_wrange_windows _ _ _ Hin) as (bw & lo & hi & Ht & Hr).
  assert (WL : windows (ss_mem (ss2 fl pp fs cs)) =
    [(Some 2%nat, -16, 0); (Some 8%nat, 0, 0); (None, WF_OFL_HEAD, WF_OFL_HEAD + 8); (None, 0, 0); (None, 0, 0)])
    by reflexivity.
  rewrite WL in Ht. cbn [In] in Ht.
  destruct Ht as [Et | [Et | [Et | [Et | [Et | []]]]]]; injection Et as <- <- <-; cbn [base_val] in Hr;
    rewrite ?E2u, ?E8u in Hr; lia. }
set (Wr := fun a => (sp0 - 64 <= a < sp0 - 48) \/ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8)).
assert (Wdec : forall a, Wr a \/ ~ Wr a) by (intros a; unfold Wr; lia).
assert (HWin : forall a, Wr a -> (sp0 - PFCLOSE_MUSL_STK <= a < sp0) \/ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8))
  by (intros a Ha; unfold Wr in Ha; rewrite FS; lia).
assert (MEQ : forall z : word, ~ Wr (bv_unsigned z) -> ms_mem ms' z = mem z).
{ intros z Hz. destruct (w_H W z) eqn:Hh; [apply HHid; exact Hh|].
  assert (Hnw : ~ in_wrange (Ereg regs [w64 ppv]) (ss_mem (ss2 fl pp fs cs)) (bv_unsigned z))
    by (intros Hin; exact (Hz (WIN _ Hin))).
  pose proof (HFr z Hnw) as E1. unfold mrestrict in E1. rewrite Hh in E1. exact E1. }
assert (GROW : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a).
{ intros a [Hh [bb Hb]]. split; [exact Hh|].
  assert (Hn : mrestrict (w_H W) (ms_mem ms') (Z_to_bv 64 a) <> None).
  { apply HGr. unfold mrestrict. rewrite Hh, Hb. discriminate. }
  unfold mrestrict in Hn. rewrite Hh in Hn.
  destruct (ms_mem ms' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; exact (Hn eq_refl)]. }
assert (PRS : forall a, Wr a -> ~ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) -> apresent (w_H W) (ms_mem ms') a).
{ intros a Ha Ho. apply GROW. apply Hpres. unfold Wr in Ha. rewrite FS. lia. }
destruct (wf_frameW lyc Sc W mem (ms_mem ms') mdc md1 Wr sp0 HAR Wdec HWin MEQ PRS MF
          ltac:(rewrite Eslo; exact Hceil) ltac:(rewrite Eslo; exact Hslo) ltac:(rewrite Eshi; exact Hshi) HOWN Hpres)
  as (AV & PM & HAR1).
assert (AVk : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - PFCLOSE_MUSL_STK <= a < sp0) ->
              ~ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) ->
              aview wsegs (w_H W) (ms_mem ms') a = aview wsegs (w_H W) mem a)
  by (intros a Ha Hs Ho; apply AV; [exact Ha | unfold Wr; rewrite FS in Hs; lia]).
assert (PRS1 : forall a, sp0 - PFCLOSE_MUSL_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms') a)
  by (intros a Ha; apply PM; [rewrite FS in Ha; lia | rewrite FS in Ha; unfold WF_OFL_HEAD; lia | apply Hpres; exact Ha]).
assert (HIMGH : forall a, WF_OFL_HEAD <= a < WF_OFL_HEAD + 8 -> in_img wsegs a)
  by (intros a Ha; apply HIMG; right; right; exact Ha).
pose proof (wf_journal_write sp0 FP ly S W0 W mem0 md0 own lyc Sc mem mdc k (ms_mem ms') md1
              HJ Hopen HHD HIMGH HAR1 MF AVk PRS1) as HJ1.
pose proof HSH as Hsh. unfold shape2 in Hsh.
apply andb_prop in Hsh as [Hsh Hb2]. apply andb_prop in Hsh as [Hsh Hh2].
apply andb_prop in Hsh as [Hsh HK2]. apply andb_prop in Hsh as [Hsh R18].
apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R8].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv e = None) by (destruct (ss_resv e); [discriminate | reflexivity]).
assert (RD : forall (r : bv 5) v, reg_is e (bv_unsigned r) v = true ->
             getr (ms_regs ms') r = sv_denot (Ereg regs [w64 ppv]) v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr.
  rewrite <- Hr. apply (st_ok_restrict_reg wsegs (w_H W) (Ereg regs [w64 ppv]) e ms' r HS'). }
assert (HEAD0 : val_mem wsegs (mrestrict (w_H W) (ms_mem ms')) WF_OFL_HEAD 8 0).
{ unfold has_chunk in Hh2. destruct (nth_error (ss_mem e) 2) as [r2|] eqn:Er2; [|discriminate].
  apply existsb_exists in Hh2 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
  destruct (YP09.r_base r2) as [nb|] eqn:Eb2; [discriminate|].
  pose proof (st_ok_mem_ok wsegs (Ereg regs [w64 ppv]) e _ HS') as (_ & Hrs & _).
  cbn [ms_mem restrict] in Hrs.
  pose proof (proj1 (Forall_forall _ _) Hrs r2 (nth_error_In _ _ Er2)) as (_ & _ & _ & Hcs).
  rewrite Eb2 in Hcs. cbn [base_val] in Hcs.
  pose proof (val_of_chunk_ok wsegs (Ereg regs [w64 ppv]) _ 0 WF_OFL_HEAD 8 (SLit 0) 0
                (proj1 (Forall_forall _ _) Hcs _ Hc) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  rewrite Z.add_0_l in Hv. exact Hv. }
pose proof (st_ok_restrict_mkst wsegs (w_H W) (Ereg regs [w64 ppv]) e ms' HS' Hresv) as Hshape.
rewrite Hpc in Hshape. rewrite Hshape. apply (HK (ms_regs ms') (ms_mem ms') md1).
- exact HJ1.
- intros a Ha Hs Ho. apply AV; [exact Ha | unfold Wr; lia].
- exact HEAD0.
- apply same_io_materialized, same_but_materialized_wvb_any.

- rewrite (RD 10%bv (SLit 0) R10). reflexivity.
- rewrite (RD 1%bv (SLit WF_FREE1) R1). reflexivity.
- rewrite (RD 2%bv (SOff 2 0) R2). cbn [sv_denot]. rewrite E2u, Z.add_0_r. reflexivity.
- rewrite (RD 8%bv (SOff 8 0) R8). cbn [sv_denot]. rewrite E8, Z.add_0_r. apply Z_to_bv_bv_unsigned.
- rewrite (RD 9%bv (SOff 10 0) R9). cbn [sv_denot].
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), Z.add_0_r. apply Z_to_bv_bv_unsigned.
- rewrite (RD 18%bv (SLit 0) R18). reflexivity.
- intros r Hr. assert (Hr32 : 0 <= r < 32) by (unfold KEPT2 in Hr; cbn in Hr; lia).
  rewrite forallb_forall in HK2. specialize (HK2 _ Hr). cbn beta in HK2.
  rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
  + cbn [sv_denot]. rewrite (ew_Ereg_nat regs _ (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r,
      Z_to_bv_bv_unsigned; [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. lia.
  + rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. exact HK2.
Qed.

(* Phase 2 for every FILE the predicate admits: flags 8 or 24, and any value at FILE+124. *)
Lemma wf_step2 : forall (W W0 : world wsegs) ly S mem0 md0 own lyc Sc
    (regs : bvmap 5 word) (mem : word -> option byte) (mdc : Model) k sp0 FP f fl ppv
    (Q : world wsegs -> config -> Prop),
  AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdc k ->
  YI16.sink_open_fp FP -> AOFL_HEAD = WF_OFL_HEAD ->
  spZ regs = sp0 - 48 -> getr regs 8 = w64 f ->
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) ->
  (fl = 8 \/ fl = 24) -> 0 <= ppv < 2 ^ 32 ->
  (forall a, (WF_NEED_LOCKS <= a < WF_NEED_LOCKS + 1) \/ (WF_OFL_LOCK <= a < WF_OFL_LOCK + 4) \/
             (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) -> in_img wsegs a) ->
  (forall a, WF_OFL_HEAD <= a < WF_OFL_HEAD + 8 -> ~ aowned B lyc Sc a) ->
  val_mem wsegs (mrestrict (w_H W) mem) f 4 fl ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 24) 8 PMCLOSE_U ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 104) 8 0 ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 112) 8 0 ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 124) 4 ppv ->
  val_mem wsegs (mrestrict (w_H W) mem) (f + 168) 8 0 ->
  val_mem wsegs (mrestrict (w_H W) mem) WF_OFL_HEAD 8 f ->
  val_mem wsegs (mrestrict (w_H W) mem) WF_NEED_LOCKS 1 0 ->
  val_mem wsegs (mrestrict (w_H W) mem) WF_OFL_LOCK 4 0 ->
  (forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mdc1 : Model),
     AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 mdc1 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0 - 48) -> ~ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) ->
        aview wsegs (w_H W) mem1 a = aview wsegs (w_H W) mem a) ->
     val_mem wsegs (mrestrict (w_H W) mem1) WF_OFL_HEAD 8 0 ->
     same_io mdc mdc1 ->
     getr regs1 10 = w64 0 -> getr regs1 1 = w64 WF_FREE1 -> getr regs1 2 = w64 (sp0 - 48) ->
     getr regs1 8 = w64 f -> getr regs1 9 = getr regs 10 -> getr regs1 18 = w64 0 ->
     (forall r, In r KEPT2 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     SRr wsegs W (cfg_at wsegs WF_FREETR regs1 mem1 mdc1) Q) ->
  SRr wsegs W (cfg_at wsegs WF_AFTFF regs mem mdc) Q.
Proof.
intros W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP f fl ppv Q HJ Hopen HHD Hsp G8 Hblk Hfl Hppv
       HIMG HOWN Vfl V24 V104 V112 V124 V168 Vhead Vnl Vlock HK.
assert (HPPA : sv_denot (Ereg regs [w64 ppv]) (SOff 32 0) = w64 ppv).
{ cbn [sv_denot]. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth].
  unfold w64. rewrite (unsigned_lit_small ppv) by lia. rewrite Z.add_0_r. reflexivity. }
assert (Hfl32 : 0 <= fl < 2 ^ 32) by (destruct Hfl; subst; lia).
destruct (Z.eq_dec ppv 0) as [Hz | Hnz].
- subst ppv.
  destruct Hfl as [-> | ->].
  + eapply (wf_step2_gen W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP f 8 0 (SLit 0) [] [] e2a Q);
      [vm_compute; reflexivity | exact r_2a | exact shape2a_ok | reflexivity | exact I | exact I | eassumption ..].
  + eapply (wf_step2_gen W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP f 24 0 (SLit 0) [] [] e2b Q);
      [vm_compute; reflexivity | exact r_2b | exact shape2b_ok | reflexivity | exact I | exact I | eassumption ..].
- assert (Hnz' : 0 < ppv < 2 ^ 32) by lia.
  destruct Hfl as [-> | ->].
  + eapply (wf_step2_gen W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP f 8 ppv (SOff 32 0) [] pp_nz e2c Q);
      [vm_compute; reflexivity | exact r_2c | exact shape2c_ok | exact HPPA | exact I
      | exact (wf_nz_cond regs ppv Hnz') | eassumption ..].
  + eapply (wf_step2_gen W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP f 24 ppv (SOff 32 0) [] pp_nz e2d Q);
      [vm_compute; reflexivity | exact r_2d | exact shape2d_ok | exact HPPA | exact I
      | exact (wf_nz_cond regs ppv Hnz') | eassumption ..].
Qed.

(* Phase 1 as a journal step: musl fclose's prologue writes only its own frame, which lies inside
   the window [sp0 - PFCLOSE_MUSL_STK, sp0) the journal already owns, so the journal is unchanged. *)
Lemma wf_step1 : forall (W W0 : world wsegs) ly S mem0 md0 own lyc Sc
    (regs : bvmap 5 word) (mem : word -> option byte) (mdc : Model) k sp0 FP f
    (Q : world wsegs -> config -> Prop),
  AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdc k ->
  spZ regs = sp0 ->
  getr regs 10 = w64 f ->
  4096 <= f -> f + SRC_FILE_BLOCK <= 2 ^ 47 -> f mod 16 = 0 ->
  (forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mdc1 : Model),
     AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 mdc1 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) ->
        aview wsegs (w_H W) mem1 a = aview wsegs (w_H W) mem a) ->
     same_io mdc mdc1 ->
     (forall off r, In (off, SOff r 0) cells1 ->
        val_mem wsegs (mrestrict (w_H W) mem1) (sp0 + off) 8
          (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))) ->
     (forall r, In r KEPT1 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     getr regs1 10 = w64 f -> getr regs1 1 = w64 WF_AFTFF ->
     getr regs1 2 = w64 (sp0 - 48) -> getr regs1 8 = w64 f ->
     SRr wsegs W (cfg_at wsegs PFFLUSH_ICPT_U regs1 mem1 mdc1) Q) ->
  SRr wsegs W (cfg_at wsegs PFCLOSE_MUSL_U regs mem mdc) Q.
Proof.
intros W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP f Q HJ Hsp G10 Hf0 Hfhi Hfal HK.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : PFCLOSE_MUSL_STK = 16432) by reflexivity. rewrite FS in Hslo, Hbot.
assert (Hal96 : sp0 mod 16 = 0) by exact Hal16.
assert (E2 : ew (Ereg regs []) 2 = getr regs 2) by (apply (ew_Ereg_nat regs [] 2 2%bv); reflexivity).
assert (E2u : bv_unsigned (ew (Ereg regs []) 2) = sp0) by (rewrite E2; exact Hsp).
assert (E10 : ew (Ereg regs []) 10 = w64 f)
  by (rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact G10).
assert (E10u : bv_unsigned (ew (Ereg regs []) 10) = f)
  by (rewrite E10; apply unsigned_lit_small; unfold SRC_FILE_BLOCK in Hfhi; lia).
unfold cfg_at.
assert (HS1 : st_ok wsegs (Ereg regs []) ss1
                    (restrict (w_H W) (mkst regs (w64 PFCLOSE_MUSL_U) mem (seg_rom wsegs)))).
{ rewrite restrict_mkst_fx. unfold ss1. apply (entry_st_ok wsegs).
  - vm_compute. reflexivity.
  - apply Forall_cons; [| apply Forall_nil]. unfold stk1.
    apply (region_ok_stack wsegs (Ereg regs []) (mrestrict (w_H W) mem) 2 sp0 (-48));
      [exact E2u | lia | lia |].
    intros a Ha. apply apresent_writable. apply Hpres. lia.
  - apply pairwise_disjoint_of_extents. cbn. repeat split; exact I.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2u, E10u.
    unfold SRC_FILE_BLOCK in Hfhi.
    change (2 ^ 4) with 16. repeat split; first [ lia | exact Hal96 | exact Hfal ]. }
eapply (SRr_run_AJ wsegs B LAWS SEGS_LOW wfc_tbl wfc_tbl_ok wsegs_wx W FUEL (Ereg regs []) ss1 e1 _ _
                   PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k Q HS1 r_1 I HJ).
{ unfold ss1. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off (Ereg regs []) stk1 [] PFCLOSE_MUSL_STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own 2 0);
    [reflexivity | rewrite E2u; lia | cbn [YP09.r_wlo stk1]; rewrite FS; lia | cbn [YP09.r_whi stk1]; lia |].
  apply awr_ok_nil. }
intros ms' mat' HS' HJ' HF HFr Hgrow.
pose proof shape1_ok as Hsh. unfold shape1 in Hsh.
apply andb_prop in Hsh as [Hsh Hcl]. apply andb_prop in Hsh as [Hsh HK1].
apply andb_prop in Hsh as [Hsh R8]. apply andb_prop in Hsh as [Hsh R2].
apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R10].
apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv e1 = None) by (destruct (ss_resv e1); [discriminate | reflexivity]).
assert (RD : forall (r : bv 5) v, reg_is e1 (bv_unsigned r) v = true ->
             getr (ms_regs ms') r = sv_denot (Ereg regs []) v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr.
  rewrite <- Hr. apply (st_ok_restrict_reg wsegs (w_H W) (Ereg regs []) e1 ms' r HS'). }
pose proof (st_ok_restrict_mkst wsegs (w_H W) (Ereg regs []) e1 ms' HS' Hresv) as Hshape. rewrite Hpc in Hshape.
rewrite Hshape. apply (HK (ms_regs ms') (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc)).
- exact HJ'.
- intros a Ha Hs. apply aview_eq_of. cbn [ms_mem mkst] in HFr. apply HFr.
  intros Hin. destruct (in_wrange_windows _ _ _ Hin) as (bw & lo & hi & Ht & Hr).
  assert (WL : windows (ss_mem ss1) = [(Some 2%nat, -48, 0)]) by reflexivity.
  rewrite WL in Ht. cbn [In] in Ht. destruct Ht as [Et | []]. injection Et as <- <- <-.
  cbn [base_val] in Hr. rewrite E2u in Hr.
  rewrite Z_to_bv_unsigned in Hr. unfold bv_wrap in Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  rewrite Z.mod_small in Hr by lia. lia.
- apply same_io_materialized, same_but_materialized_wvb_any.
- intros off r Hin.
  assert (Hr32 : (r < 32)%nat)
    by (unfold cells1 in Hin; cbn [In] in Hin;
        repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <-; lia|]); destruct Hin).
  rewrite forallb_forall in Hcl. specialize (Hcl _ Hin). cbn [fst snd] in Hcl.
  unfold has_chunk in Hcl. destruct (nth_error (ss_mem e1) 0) as [r0|] eqn:Er0; [|discriminate].
  apply existsb_exists in Hcl as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
  pose proof (st_ok_mem_ok wsegs (Ereg regs []) e1 _ HS') as (_ & Hrs & _).
  cbn [ms_mem restrict] in Hrs.
  pose proof (proj1 (Forall_forall _ _) Hrs r0 (nth_error_In _ _ Er0)) as (_ & _ & _ & Hcs).
  assert (Eb0 : YP09.r_base r0 = Some 2%nat)
    by (revert Er0; vm_compute (nth_error (ss_mem e1) 0); intros Er0; injection Er0 as <-; reflexivity).
  rewrite Eb0 in Hcs. cbn [base_val] in Hcs. rewrite E2u in Hcs.
  eapply (val_of_chunk_ok wsegs (Ereg regs []) _ sp0 off 8 (SOff r 0)
            (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r)))));
    [ exact (proj1 (Forall_forall _ _) Hcs _ Hc)
    | cbn [sv_denot]; rewrite (ew_Ereg_lt regs [] r Hr32), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; apply u64_range | cbn; lia ].
- intros r Hr. assert (Hr32 : 0 <= r < 32) by (unfold KEPT1 in Hr; cbn in Hr; lia).
  rewrite forallb_forall in HK1. specialize (HK1 _ Hr). cbn beta in HK1.
  rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
  + cbn [sv_denot]. rewrite (ew_Ereg_nat regs [] (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r,
      Z_to_bv_bv_unsigned; [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. lia.
  + rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. exact HK1.
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite E10, Z.add_0_r. apply Z_to_bv_bv_unsigned.
- rewrite (RD 1%bv (SLit WF_AFTFF) R1). reflexivity.
- rewrite (RD 2%bv (SOff 2 (-48)) R2). cbn [sv_denot]. rewrite E2u. unfold w64. f_equal; lia.
- rewrite (RD 8%bv (SOff 10 0) R8). cbn [sv_denot]. rewrite E10, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* Phase 3 as a journal step: `mv a0,s0` and the second free call. It reads and writes nothing,
   so its symbolic state carries no region at all and the journal passes through untouched. *)
Lemma wf_step3 : forall (W W0 : world wsegs) ly S mem0 md0 own lyc Sc
    (regs : bvmap 5 word) (mem : word -> option byte) (mdc : Model) k sp0 FP f
    (Q : world wsegs -> config -> Prop),
  AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdc k ->
  getr regs 8 = w64 f ->
  (forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mdc1 : Model),
     AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 mdc1 k ->
     (forall a, aview wsegs (w_H W) mem1 a = aview wsegs (w_H W) mem a) ->
     same_io mdc mdc1 ->
     getr regs1 10 = w64 f -> getr regs1 1 = w64 WF_JOIN ->
     (forall r, In r KEPT3 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     SRr wsegs W (cfg_at wsegs WF_FREETR regs1 mem1 mdc1) Q) ->
  SRr wsegs W (cfg_at wsegs WF_FREE1 regs mem mdc) Q.
Proof.
intros W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP f Q HJ G8 HK.
unfold cfg_at.
assert (HS3 : st_ok wsegs (Ereg regs []) ss3
                    (restrict (w_H W) (mkst regs (w64 WF_FREE1) mem (seg_rom wsegs)))).
{ rewrite restrict_mkst_fx. unfold ss3. apply (entry_st_ok wsegs).
  - reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - cbn [atoms_ok]. exact I. }
eapply (SRr_run_AJ wsegs B LAWS SEGS_LOW wfc_tbl wfc_tbl_ok wsegs_wx W FUEL (Ereg regs []) ss3 e3 _ _
                   PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k Q HS3 r_3 I HJ).
{ unfold ss3. cbn [ss_mem]. apply awr_ok_nil. }
intros ms' mat' HS' HJ' HF HFr Hgrow.
pose proof shape3_ok as Hsh. unfold shape3 in Hsh.
apply andb_prop in Hsh as [Hsh _]. apply andb_prop in Hsh as [Hsh HK3].
apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R10].
apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv e3 = None) by (destruct (ss_resv e3); [discriminate | reflexivity]).
assert (RD : forall (r : bv 5) v, reg_is e3 (bv_unsigned r) v = true ->
             getr (ms_regs ms') r = sv_denot (Ereg regs []) v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr.
  rewrite <- Hr. apply (st_ok_restrict_reg wsegs (w_H W) (Ereg regs []) e3 ms' r HS'). }
assert (E8 : ew (Ereg regs []) 8 = w64 f)
  by (rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl); exact G8).
pose proof (st_ok_restrict_mkst wsegs (w_H W) (Ereg regs []) e3 ms' HS' Hresv) as Hshape.
rewrite Hpc in Hshape.
rewrite Hshape. apply (HK (ms_regs ms') (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc)).
- exact HJ'.
- intros a. apply aview_eq_of. cbn [ms_mem mkst] in HFr. apply HFr.
  intros (r & Hin & _). unfold ss3 in Hin. cbn [ss_mem] in Hin. destruct Hin.
- apply same_io_materialized, same_but_materialized_wvb_any.
- rewrite (RD 10%bv (SOff 8 0) R10). cbn [sv_denot]. rewrite E8, Z.add_0_r. apply Z_to_bv_bv_unsigned.
- rewrite (RD 1%bv (SLit WF_JOIN) R1). reflexivity.
- intros r Hr. assert (Hr32 : 0 <= r < 32) by (unfold KEPT3 in Hr; cbn in Hr; lia).
  rewrite forallb_forall in HK3. specialize (HK3 _ Hr). cbn beta in HK3.
  rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
  + cbn [sv_denot]. rewrite (ew_Ereg_nat regs [] (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r,
      Z_to_bv_bv_unsigned; [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. lia.
  + rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. exact HK3.
Qed.

(* Phase 4 as a journal step, with the `ret` taken: the join 0x8e2c0 .. 0x8e2dc. It reads the five
   saved slots of fclose's own frame and writes nothing, so the journal passes through. The result
   is s2 | s1, and both are zero on this stream (mclose returns 0, fflush returns 0). *)
Lemma wf_step4 : forall (W W0 : world wsegs) ly S mem0 md0 own lyc Sc
    (regs : bvmap 5 word) (mem : word -> option byte) (mdc : Model) k sp0 FP
    (v1 v8 v9 v18 v19 : Z) (Q : world wsegs -> config -> Prop),
  AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdc k ->
  spZ regs = sp0 - 48 ->
  getr regs 9 = w64 0 -> getr regs 18 = w64 0 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v8 < 2 ^ 64 -> 0 <= v9 < 2 ^ 64 -> 0 <= v18 < 2 ^ 64 -> 0 <= v19 < 2 ^ 64 ->
  val_mem wsegs (mrestrict (w_H W) mem) (sp0 - 8) 8 v1 ->
  val_mem wsegs (mrestrict (w_H W) mem) (sp0 - 16) 8 v8 ->
  val_mem wsegs (mrestrict (w_H W) mem) (sp0 - 24) 8 v9 ->
  val_mem wsegs (mrestrict (w_H W) mem) (sp0 - 32) 8 v18 ->
  val_mem wsegs (mrestrict (w_H W) mem) (sp0 - 40) 8 v19 ->
  (forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mdc1 : Model),
     AJ PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 mdc1 k ->
     (forall a, aview wsegs (w_H W) mem1 a = aview wsegs (w_H W) mem a) ->
     same_io mdc mdc1 ->
     getr regs1 10 = w64 0 -> getr regs1 1 = w64 v1 -> getr regs1 2 = w64 sp0 ->
     getr regs1 8 = w64 v8 -> getr regs1 9 = w64 v9 ->
     getr regs1 18 = w64 v18 -> getr regs1 19 = w64 v19 ->
     (forall r, In r KEPT2 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     Q W (mkCfg (mkst regs1 (v_jalr (w64 v1) 0) mem1 (seg_rom wsegs)) mdc1)) ->
  SRr wsegs W (cfg_at wsegs WF_JOIN regs mem mdc) Q.
Proof.
intros W W0 ly S mem0 md0 own lyc Sc regs mem mdc k sp0 FP v1 v8 v9 v18 v19 Q
       HJ Hsp G9 G18 B1 B8 B9 B18 B19 M1 M8 M9 M18 M19 HK.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : PFCLOSE_MUSL_STK = 16432) by reflexivity. rewrite FS in Hslo, Hbot.
set (XT := map (Z_to_bv 64) [v1; v8; v9; v18; v19]).
assert (E2 : ew (Ereg regs XT) 2 = getr regs 2) by (apply (ew_Ereg_nat regs XT 2 2%bv); reflexivity).
assert (E2u : bv_unsigned (ew (Ereg regs XT) 2) = sp0 - 48) by (rewrite E2; exact Hsp).
assert (X0 : ew (Ereg regs XT) 32 = w64 v1)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; unfold XT; reflexivity).
assert (X1 : ew (Ereg regs XT) 33 = w64 v8)
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; unfold XT; reflexivity).
assert (X2 : ew (Ereg regs XT) 34 = w64 v9)
  by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; unfold XT; reflexivity).
assert (X3 : ew (Ereg regs XT) 35 = w64 v18)
  by (change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; unfold XT; reflexivity).
assert (X4 : ew (Ereg regs XT) 36 = w64 v19)
  by (change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; unfold XT; reflexivity).
assert (X0u : bv_unsigned (ew (Ereg regs XT) 32) = v1) by (rewrite X0; apply unsigned_lit_small; lia).
assert (X1u : bv_unsigned (ew (Ereg regs XT) 33) = v8) by (rewrite X1; apply unsigned_lit_small; lia).
assert (X2u : bv_unsigned (ew (Ereg regs XT) 34) = v9) by (rewrite X2; apply unsigned_lit_small; lia).
assert (X3u : bv_unsigned (ew (Ereg regs XT) 35) = v18) by (rewrite X3; apply unsigned_lit_small; lia).
assert (X4u : bv_unsigned (ew (Ereg regs XT) 36) = v19) by (rewrite X4; apply unsigned_lit_small; lia).
unfold cfg_at.
assert (HS4 : st_ok wsegs (Ereg regs XT) ss4
                    (restrict (w_H W) (mkst regs (w64 WF_JOIN) mem (seg_rom wsegs)))).
{ rewrite restrict_mkst_fx. unfold ss4. apply (entry_st_ok wsegs).
  - vm_compute. reflexivity.
  - apply Forall_cons; [| apply Forall_nil]. unfold stk4, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2u. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    unfold stk4_chunks.
    repeat (apply Forall_cons;
      [ eapply (chunk_ok_val wsegs (Ereg regs XT));
        [ cbn [sv_denot]; rewrite ?X0u, ?X1u, ?X2u, ?X3u, ?X4u, Z.add_0_r; reflexivity
        | cbn; lia | cbn; lia
        | cbn [YP09.c_off];
          first [ replace (sp0 - 48 + 40) with (sp0 - 8) by lia; exact M1
                | replace (sp0 - 48 + 32) with (sp0 - 16) by lia; exact M8
                | replace (sp0 - 48 + 24) with (sp0 - 24) by lia; exact M9
                | replace (sp0 - 48 + 16) with (sp0 - 32) by lia; exact M18
                | replace (sp0 - 48 + 8) with (sp0 - 40) by lia; exact M19 ] ] |]).
    apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. repeat split; exact I.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2u.
    change (2 ^ 4) with 16. repeat split; try lia. }
eapply (SRr_run_AJ wsegs B LAWS SEGS_LOW wfc_tbl wfc_tbl_ok wsegs_wx W FUEL (Ereg regs XT) ss4 e4 _ _
                   PFCLOSE_MUSL_STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k Q HS4 r_4 I HJ).
{ unfold ss4. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
intros ms' mat' HS' HJ' HF HFr Hgrow.
pose proof shape4_ok as Hsh. unfold shape4 in Hsh.
apply andb_prop in Hsh as [Hsh _]. apply andb_prop in Hsh as [Hsh HK4].
apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hsh R18].
apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R8].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hrv R10].
assert (Hresv : ss_resv e4 = None) by (destruct (ss_resv e4); [discriminate | reflexivity]).
assert (RD : forall (r : bv 5) v, reg_is e4 (bv_unsigned r) v = true ->
             getr (ms_regs ms') r = sv_denot (Ereg regs XT) v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr.
  rewrite <- Hr. apply (st_ok_restrict_reg wsegs (w_H W) (Ereg regs XT) e4 ms' r HS'). }
assert (R1' : getr (ms_regs ms') 1 = w64 v1)
  by (rewrite (RD 1%bv (SOff 32 0) R1); cbn [sv_denot]; rewrite X0, Z.add_0_r;
      apply Z_to_bv_bv_unsigned).
eapply (SRr_ret_at wsegs wfc_tbl wfc_tbl_ok wsegs_wx W (Ereg regs XT) e4 ms' _ Q HS' Hresv).
{ vm_compute. reflexivity. }
intros mat2. rewrite R1'.
apply (HK (ms_regs ms') (ms_mem ms')
          (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy mdc) mat' mdc)) mat2
             (with_vm_backing (m_vm_lazy mdc) mat' mdc))).
- rewrite wvb_collapse. exact (ajournal_materialize wsegs B LAWS SEGS_LOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ').
- intros a. apply aview_eq_of. cbn [ms_mem mkst] in HFr. apply HFr.
  intros Hin. destruct (in_wrange_windows _ _ _ Hin) as (bw & lo & hi & Ht & Hr).
  assert (WL : windows (ss_mem ss4) = [(Some 2%nat, 0, 0)]) by reflexivity.
  rewrite WL in Ht. cbn [In] in Ht. destruct Ht as [Et | []]. injection Et as <- <- <-. lia.
- eapply same_io_trans; apply same_io_materialized, same_but_materialized_wvb_any.
- rewrite (RD 10%bv (SAlu ALU_OR (SOff 18 0) (SOff 9 0)) R10). cbn [sv_denot].
  rewrite (ew_Ereg_nat regs XT 18 18%bv eq_refl), (ew_Ereg_nat regs XT 9 9%bv eq_refl), G9, G18.
  apply bv_eq. vm_compute. reflexivity.
- exact R1'.
- rewrite (RD 2%bv (SOff 2 48) R2). cbn [sv_denot]. rewrite E2u. unfold w64. f_equal; lia.
- rewrite (RD 8%bv (SOff 33 0) R8). cbn [sv_denot]. rewrite X1, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- rewrite (RD 9%bv (SOff 34 0) R9). cbn [sv_denot]. rewrite X2, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- rewrite (RD 18%bv (SOff 35 0) R18). cbn [sv_denot]. rewrite X3, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- rewrite (RD 19%bv (SOff 36 0) R19). cbn [sv_denot]. rewrite X4, Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
- intros r Hr. assert (Hr32 : 0 <= r < 32) by (unfold KEPT2 in Hr; cbn in Hr; lia).
  rewrite forallb_forall in HK4. specialize (HK4 _ Hr). cbn beta in HK4.
  rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
  + cbn [sv_denot]. rewrite (ew_Ereg_nat regs XT (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r,
      Z_to_bv_bv_unsigned; [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. lia.
  + rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. exact HK4.
Qed.


(* ================================================================================================ *)
(* The musl body of fclose on asan-ubsan: afclose_source_spec_stk at PFCLOSE_MUSL_STK, entered at    *)
(* musl fclose 0x8e0e0 (PStdioImgB's PFCLOSE_MUSL_U = KS_U's PCAP_REAL_FCLOSE). The interceptor front  *)
(* (fclose trampoline 0x4161c, ___interceptor_fclose 0x467f0) is a Theorem Labs lane's and composes   *)
(* with this.                                                                                         *)
(* ================================================================================================ *)
(* The free interceptor's first unwind pc, MEASURED: ___interceptor_free is nm T 0x52c2c (size 0x1d0,
   116 insns, masked-equal to asan's 0x52bdc); at ___interceptor_free+0x134 = 0x52d60 it calls
   `jal _ZN11__sanitizer10StackTrace12GetCurrentPcEv`, whose return address is
   ___interceptor_free+0x138 = 0x52d64 (asan: the same jal at 0x52d10, returning to 0x52d14, which is
   the donor's HRA0). The free wrapper is __interceptor_trampoline_free, nm T 0x52c24 (`j 0x52c2c`),
   the donor's HWRAPF (asan 0x52bd4). *)
Definition WF_FREE_RA0 : Z := (symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z).

Section T.
(* The allocator API and free's contract, as in the donor (YCbq aj_free_null_at_io / aj_free_at_io's
   own premises): carried by the program-level consumer. *)
Hypothesis ENV : api_env wsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes wsegs B.
Variable K : asource_syms.
Hypothesis ASIL : asource_img_laws SK wsegs B K.
(* K is KS_U (lib/B/Stdio/PSourceK.v pcap_KS, the asan-ubsan record). *)
Hypothesis HKS : K = pcap_KS.
Hypothesis HSK : AOFL_HEAD = WF_OFL_HEAD.
Hypothesis HWRAPF : pc_wrap_free (as_code B) = WF_FREETR.
Hypothesis HRA0 : pc_free_ra0 (as_code B) = WF_FREE_RA0.
Variables rlo rhi : Z.
(* fflush at the asan-ubsan fflush TRAMPOLINE, the target of fclose's `jal` at fclose+0x1c:
   lib/B/Stdio/WFflush.v's theorem pcapu_afflush_source_spec_icpt. *)
Hypothesis FFLUSH : afflush_source_spec SK wsegs B K PFFLUSH_ICPT_U rlo rhi.

Theorem pcapu_afclose_source_spec_musl :
  afclose_source_spec_stk SK wsegs B K PFCLOSE_MUSL_STK PFCLOSE_MUSL_U WF_FREE1 WF_JOIN rlo rhi.
Proof.
intros W ly S regs mem md ch f b M C p rest HPRE G10 Hperm HSRC Hbblk HMETA HRO Hev Hu1 Hu2.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : PFCLOSE_MUSL_STK = 16432) by reflexivity.
assert (HD : WF_OFL_HEAD = (symaddr Symbols.AsanUbsan.s_ofl_head)) by reflexivity.
set (sp0 := spZ regs) in *.
assert (ESP0 : w64 sp0 = getr regs 2) by (unfold w64, sp0, spZ; apply Z_to_bv_bv_unsigned).
assert (Hfblk : In (f, SRC_FILE_BLOCK) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md f SRC_FILE_BLOCK HAR Hfblk)
  as (Hf16 & Hf0 & Hfceil & Hfapp & Hfbytes & Hfdisj & Hfrange).
assert (RQ : req_size SRC_FILE_BLOCK = 1304) by reflexivity. rewrite RQ in Hfceil, Hfbytes.
destruct (al_blocks _ _ LAWS ly S W mem md b (Z.of_nat (length C)) HAR Hbblk)
  as (Hb16 & Hb4096 & Hbceil & _).
assert (Hbreq : Z.of_nat (length C) <= req_size (Z.of_nat (length C)))
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length C)) 0); lia).
(* the open-file-list head and the stdio environment are image cells, not owned and not errno *)
assert (HIMGE : forall a, (WF_NEED_LOCKS <= a < WF_NEED_LOCKS + 1) \/ (WF_OFL_LOCK <= a < WF_OFL_LOCK + 4) \/
                 (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) -> in_img wsegs a).
{ intros a Ha.
  assert (Hin : asrc_env_addr K a).
  { unfold asrc_env_addr. rewrite HKS.
    cbn [as_threaded as_need_locks as_ofl_lock as_mode as_canary pcap_KS].
    unfold WF_NEED_LOCKS, WF_OFL_LOCK, WF_OFL_HEAD, PCAP_NEED_LOCKS, PCAP_OFL_LOCK in *. lia. }
  exact (proj1 (asil_env _ _ _ _ ASIL a Hin)). }
assert (HOWNE : forall ly' S' W' mem' md', AR wsegs B ly' S' W' mem' md' ->
                forall a, WF_OFL_HEAD <= a < WF_OFL_HEAD + 8 -> ~ aowned B ly' S' a).
{ intros ly' S' W' mem' md' HAR' a Ha Hown.
  assert (Hi : in_img wsegs a) by (apply HIMGE; right; right; exact Ha).
  assert (Hin : asrc_env_addr K a).
  { unfold asrc_env_addr. rewrite HKS.
    cbn [as_threaded as_need_locks as_ofl_lock as_mode as_canary pcap_KS].
    unfold WF_OFL_HEAD, PCAP_OFL_LOCK in *. lia. }
  destruct (asil_env _ _ _ _ ASIL a Hin) as (_ & Hns & _).
  exact (Hns (proj1 (al_owned_image _ _ LAWS ly' S' W' mem' md' a HAR' Hi) Hown)). }
(* the head this lane names is the head the journal spares *)
assert (HEADK : as_ofl_head K = WF_OFL_HEAD)
  by (rewrite HKS; unfold as_ofl_head, WF_OFL_HEAD, pcap_KS, PCAP_OFL_LOCK; reflexivity).
assert (HOPEN : YI16.sink_open_fp (asource_fp f)) by (apply asource_fp_open).
unfold cfg_at. change (Z_to_bv 64 PFCLOSE_MUSL_U) with (w64 PFCLOSE_MUSL_U).
pose proof (ajournal_init wsegs B PFCLOSE_MUSL_STK (asource_fp f) ly S W regs mem md ch HPRE) as J0.
fold sp0 in J0.
eapply (wf_step1 W W ly S mem md [] ly S regs mem md 0 sp0 (asource_fp f) f);
  [exact J0 | reflexivity | exact G10 | lia | unfold SRC_FILE_BLOCK; lia | exact Hf16 |].
intros regs1 mem1 md1 J1 KEPT1v IO1 CELL1 KEPT1r G1_10 G1_1 G1_2 G1_8.
(* phase 1 wrote only fclose's own frame: the stream, the image and the blocks are untouched *)
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) ->
              mbyte wsegs (mrestrict (w_H W) mem1) a = mbyte wsegs (mrestrict (w_H W) mem) a)
  by (intros a Ha Hs; apply mbyte_of_aview; exact (KEPT1v a Ha Hs)).
assert (HSRC1 : asource_at wsegs K (mrestrict (w_H W) mem1) f b C p).
{ apply (wf_asource_frame B K ASIL (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) f b C p);
    [ intros a Ha; apply MB1; unfold SRC_FILE_BLOCK in *; lia
    | intros a Ha; apply MB1; lia
    | intros a Ha; pose proof (SEGS_LOW a Ha); apply MB1; unfold kLowMemEnd in *; lia
    | exact HSRC ]. }
assert (HRO1 : arodata_okS wsegs B rlo rhi (aview wsegs (w_H W) mem1)).
{ apply (wf_rodata_frame B W mem mem1 (sp0 - 48) sp0 rlo rhi SEGS_LOW ltac:(lia) ltac:(lia)
           KEPT1v ltac:(intros a Ha; apply Hpres; rewrite FS; lia) HRO). }
assert (HMETA1 : asrc_meta_inv wsegs K ly (mrestrict (w_H W) mem1) M)
  by (eapply (asrc_meta_inv_kept SK wsegs B K ASIL); [exact J1 | exact HMETA]).
(* the fflush call at 0x8e0fc, to the trampoline 0x41618 *)
assert (R1ra : YK0s.ret_ok (getr regs1 1)) by (rewrite G1_1; reflexivity).
assert (Ebv3 : (3%bv : bv 5) = Z_to_bv 5 3) by (apply bv_eq; reflexivity).
assert (Ebv4 : (4%bv : bv 5) = Z_to_bv 5 4) by (apply bv_eq; reflexivity).
assert (R1gp : getr regs1 3 = w64 (as_gp B))
  by (rewrite Ebv3, (KEPT1r 3 ltac:(unfold KEPT1; cbn; tauto)), <- Ebv3; exact Hgp).
assert (R1tp : getr regs1 4 = w64 (as_tp B))
  by (rewrite Ebv4, (KEPT1r 4 ltac:(unfold KEPT1; cbn; tauto)), <- Ebv4; exact Htp).
assert (R1sp : YG0d.spZ regs1 = sp0 + (-48)).
{ unfold YG0d.spZ. rewrite G1_2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HFNPRE : afn_pre wsegs B PFFLUSH_OWN_STK ly S W regs1 mem1 md1 []).
{ eapply (afn_pre_at wsegs B PFCLOSE_MUSL_STK sp0 (asource_fp f) ly S W mem md [] ly S W mem1 md1 0
            regs1 PFFLUSH_OWN_STK (-48) []);
    [ exact J1 | exact R1sp | reflexivity | lia | unfold PFFLUSH_OWN_STK; lia
    | unfold PFFLUSH_OWN_STK; rewrite FS; lia | exact R1ra
    | unfold YG0d.raZ; rewrite G1_1; unfold w64; rewrite unsigned_lit_small; unfold WF_AFTFF; lia
    | exact R1gp | exact R1tp
    | apply achain_low; unfold YG0d.s0Z; rewrite G1_8; unfold w64;
      rewrite unsigned_lit_small by (unfold SRC_FILE_BLOCK in *; lia); lia ]. }
eapply SRr_bind.
{ apply (FFLUSH W ly S regs1 mem1 md1 [] f b M C p HFNPRE G1_10 HRO1 HMETA1 HSRC1 Hfblk).
  
  rewrite R1sp. unfold PFFLUSH_OWN_STK. left. lia. }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & JF & APF & GF10 & HUNB & HCOOK & HFD2 & HFS2).
(* the fflush journal, composed with the token-aware rule (the footprint carries sink_token) *)
assert (J2 : AJ PFCLOSE_MUSL_STK sp0 (asource_fp f) ly S W mem md [] ly S W2 mem2 md2 0).
{ replace 0 with (0 + 0) by lia.
  eapply (wf_ajournal_sub_tok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] _ _ _ _ _);
    [exact J1 | rewrite R1sp in JF; exact JF | | | ].
  - rewrite FS. unfold PFFLUSH_OWN_STK. lia.
  - lia.
  - intros a Ha. left. exact Ha. }
pose proof HUNB as (HSRC2 & HWIN2).
pose proof HSRC2 as (Wn2 & cpos2 & fl2 & md2v & _ & _ & _ & _ & _ & _ & _ & _ & Hgar2 &
  (S24 & S64 & S72 & S80 & S88 & S96 & S240 & S248 & S256 & S264 & S152 & S32 & S40 & S48 & S56 &
   S104 & S112 & S168 & S120 & S140 & S144 & Hf0' & Hfal' & Hb0' & Hdisj')
  & _ & (Hfl2 & Hflv2) & _ & _ & _ & Henv2 & Hhead2 & Hfnz2).
pose proof Henv2 as (Ethr & Enl & Elock & Emode & Erwa & Ecan).
pose proof JF as (HAR2 & _).
destruct (al_blocks _ _ LAWS ly S W2 mem2 md2 f SRC_FILE_BLOCK HAR2 Hfblk)
  as (_ & _ & _ & _ & Hfbytes2 & _).
rewrite RQ in Hfbytes2.
assert (HPP : exists ppv, 0 <= ppv < 2 ^ 32 /\
          val_mem wsegs (mrestrict (w_H W2) mem2) (f + 124) 4 ppv).
{ apply wf_val4_of_bytes. intros k Hk.
  destruct (proj1 (Hfbytes2 (f + 124 + k) ltac:(unfold SRC_FILE_BLOCK; lia))) as [Hh [bb Hb]].
  exists bb. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
destruct HPP as (ppv & Hppv & V124).
assert (ECLOSE : as_close K = PMCLOSE_U) by (rewrite HKS; reflexivity).
assert (ENLK : as_need_locks K = WF_NEED_LOCKS) by (rewrite HKS; reflexivity).
assert (EOLK : as_ofl_lock K = WF_OFL_LOCK) by (rewrite HKS; reflexivity).
assert (Ebv2 : (2%bv : bv 5) = Z_to_bv 5 2) by (apply bv_eq; reflexivity).
assert (Ebv8 : (8%bv : bv 5) = Z_to_bv 5 8) by (apply bv_eq; reflexivity).
assert (Ebv9 : (9%bv : bv 5) = Z_to_bv 5 9) by (apply bv_eq; reflexivity).
assert (Ebv18 : (18%bv : bv 5) = Z_to_bv 5 18) by (apply bv_eq; reflexivity).
assert (Ebv19 : (19%bv : bv 5) = Z_to_bv 5 19) by (apply bv_eq; reflexivity).
assert (R2sp : getr regs2 2 = w64 (sp0 - 48))
  by (rewrite Ebv2, (APF 2 ltac:(unfold acallee_saved; lia)), <- Ebv2; exact G1_2).
assert (R2sp' : YG0d.spZ regs2 = sp0 - 48)
  by (unfold YG0d.spZ; rewrite R2sp; unfold w64; apply unsigned_lit_small; lia).
assert (R2_8 : getr regs2 8 = w64 f)
  by (rewrite Ebv8, (APF 8 ltac:(unfold acallee_saved; lia)), <- Ebv8; exact G1_8).
assert (R2gp : getr regs2 3 = w64 (as_gp B))
  by (rewrite Ebv3, (APF 3 ltac:(unfold acallee_saved; lia)), <- Ebv3; exact R1gp).
assert (R2tp : getr regs2 4 = w64 (as_tp B))
  by (rewrite Ebv4, (APF 4 ltac:(unfold acallee_saved; lia)), <- Ebv4; exact R1tp).
rewrite G1_1. change (mkCfg (mkst regs2 (w64 WF_AFTFF) mem2 (seg_rom wsegs)) md2)
  with (cfg_at wsegs WF_AFTFF regs2 mem2 md2).
eapply (wf_step2 W2 W ly S mem md [] ly S regs2 mem2 md2 0 sp0 (asource_fp f) f fl2 ppv);
  [ exact J2 | exact HOPEN | exact HSK | exact R2sp' | exact R2_8 | exact Hfblk | exact Hflv2 | lia
  | exact HIMGE | exact (HOWNE ly S W2 mem2 md2 HAR2)
  | exact Hfl2
  | rewrite ECLOSE in S24; exact S24
  | exact S104 | exact S112 | exact V124 | exact S168
  | rewrite <- HEADK; exact Hhead2
  | rewrite ENLK in Enl; exact Enl
  | rewrite EOLK in Elock; exact Elock |].
intros regs3 mem3 md3 J3 KEPT2v HEAD0 IO3 G3_10 G3_1 G3_2 G3_8 G3_9 G3_18 KEPT2r.
assert (R3sp : YG0d.spZ regs3 = sp0 + (-48))
  by (unfold YG0d.spZ; rewrite G3_2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (R3gp : getr regs3 3 = w64 (as_gp B))
  by (rewrite Ebv3, (KEPT2r 3 ltac:(unfold KEPT2; cbn; tauto)), <- Ebv3; exact R2gp).
assert (R3tp : getr regs3 4 = w64 (as_tp B))
  by (rewrite Ebv4, (KEPT2r 4 ltac:(unfold KEPT2; cbn; tauto)), <- Ebv4; exact R2tp).
assert (CHAIN : forall (Wx : world wsegs) (lyx : alayout) (regsx : bvmap 5 word)
          (memx : word -> option byte) (ra : Z),
          getr regsx 1 = w64 ra -> 4096 <= ra < 2 ^ 47 -> getr regsx 8 = w64 f ->
          YG0d.spZ regsx = sp0 + (-48) -> ly_top lyx = ly_top ly ->
          chain_pre lyx (aview wsegs (w_H Wx) memx) regsx []).
{ intros Wx lyx regsx memx ra Hr Hra' H8 Hsp' Etopx. unfold chain_pre. split.
  - unfold YG0d.raZ. rewrite Hr. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - destruct (frame0_ok lyx regsx); [|reflexivity].
    assert (Hbad : bad_next (YG0d.spZ regsx) (ly_top lyx) (YG0d.s0Z regsx) = true).
    { unfold bad_next, YG0d.s0Z. rewrite H8, Hsp'. unfold w64.
      rewrite unsigned_lit_small by (unfold SRC_FILE_BLOCK in *; lia).
      destruct (Z.leb_spec f (sp0 + -48)) as [L|L]; [reflexivity | exfalso; rewrite FS in Hslo; lia]. }
    rewrite Hbad. reflexivity. }
unfold cfg_at. rewrite <- HWRAPF.
eapply SRr_bind.
{ eapply (aj_free_null_at_io wsegs B LAWS SEGS_LOW ENV ML AFREE W2 regs3 mem3 PFCLOSE_MUSL_STK sp0
            (asource_fp f) ly S W mem md [] ly S md3 0 (-48) (w64 WF_FREE1) []);
    [ exact J3 | exact G3_10 | exact R3sp | reflexivity | lia | rewrite FS; unfold ASTACK; lia
    | exact R3gp | exact R3tp | exact G3_1 | reflexivity | lia
    | exact (CHAIN W2 ly regs3 mem3 WF_FREE1 G3_1 ltac:(unfold WF_FREE1; lia) G3_8 R3sp eq_refl)
    | idtac ].
  assert (Hraz : YG0d.raZ regs3 = WF_FREE1)
    by (unfold YG0d.raZ; rewrite G3_1; unfold w64; apply unsigned_lit_small; unfold WF_FREE1; lia).
  assert (Hne : (YG0d.raZ regs3 =? pc_free_ra0 (as_code B)) = false)
    by (rewrite Hraz, HRA0; reflexivity).
  unfold call_trace0, unwind_of_chain. cbn [flat_map app].
  rewrite Hne, Hraz. unfold kUnwindMax. cbn [firstn]. exact Hu1. }
cbv beta. intros W3 c3 Hwle3 (ly4 & S4 & regs4 & mem4 & md4 & -> & J4 & AP4 & HPERM4 & HFR4 & KEPT4 & IO4).
assert (R4_8 : getr regs4 8 = w64 f)
  by (rewrite Ebv8, (AP4 8 ltac:(unfold acallee_saved; lia)), <- Ebv8; exact G3_8).
assert (R4gp : getr regs4 3 = w64 (as_gp B))
  by (rewrite Ebv3, (AP4 3 ltac:(unfold acallee_saved; lia)), <- Ebv3; exact R3gp).
assert (R4tp : getr regs4 4 = w64 (as_tp B))
  by (rewrite Ebv4, (AP4 4 ltac:(unfold acallee_saved; lia)), <- Ebv4; exact R3tp).
assert (R4sp : YG0d.spZ regs4 = sp0 + (-48)).
{ rewrite <- R3sp. unfold YG0d.spZ. rewrite Ebv2, (AP4 2 ltac:(unfold acallee_saved; lia)). reflexivity. }
change (mkCfg (mkst regs4 (w64 WF_FREE1) mem4 (seg_rom wsegs)) md4)
  with (cfg_at wsegs WF_FREE1 regs4 mem4 md4).
eapply (wf_step3 W3 W ly S mem md [] ly4 S4 regs4 mem4 md4 1 sp0 (asource_fp f) f);
  [exact J4 | exact R4_8 |].
intros regs5 mem5 md5 J5 KEPT5v IO5 G5_10 G5_1 KEPT3r.
(* the second free: the FILE block itself *)
assert (R5sp : YG0d.spZ regs5 = sp0 + (-48)).
{ rewrite <- R4sp. unfold YG0d.spZ. f_equal.
  rewrite Ebv2, (KEPT3r 2 ltac:(unfold KEPT3; cbn; tauto)), <- Ebv2. reflexivity. }
assert (R5gp : getr regs5 3 = w64 (as_gp B))
  by (rewrite Ebv3, (KEPT3r 3 ltac:(unfold KEPT3; cbn; tauto)), <- Ebv3; exact R4gp).
assert (R5tp : getr regs5 4 = w64 (as_tp B))
  by (rewrite Ebv4, (KEPT3r 4 ltac:(unfold KEPT3; cbn; tauto)), <- Ebv4; exact R4tp).
assert (R5_8 : getr regs5 8 = w64 f)
  by (rewrite Ebv8, (KEPT3r 8 ltac:(unfold KEPT3; cbn; tauto)), <- Ebv8; exact R4_8).
assert (Hfblk4 : In (f, SRC_FILE_BLOCK) (ablocks B ly4 S4))
  by (apply (Permutation_in _ (Permutation_sym HPERM4)); exact Hfblk).
unfold cfg_at. rewrite <- HWRAPF.
eapply SRr_bind.
{ eapply (aj_free_at_io wsegs B LAWS SEGS_LOW ENV ML AFREE W3 regs5 mem5 PFCLOSE_MUSL_STK sp0
            (asource_fp f) ly S W mem md [] ly4 S4 md5 1 f SRC_FILE_BLOCK (-48) (w64 WF_JOIN) []);
    [ exact J5 | exact Hfblk4 | exact G5_10 | exact R5sp | reflexivity | lia
    | rewrite FS; unfold ASTACK; lia | exact R5gp | exact R5tp | exact G5_1 | reflexivity
    | pose proof J5 as (_ & _ & _ & _ & _ & _ & Hnev5 & _); lia
    | exact (CHAIN W3 ly4 regs5 mem5 WF_JOIN G5_1 ltac:(unfold WF_JOIN; lia) R5_8 R5sp
               ltac:(pose proof J4 as (_ & Hly4 & _);
                     pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & Et4 & _); exact Et4))
    | idtac
    | intros _ i Hi; exists (f, f + SRC_FILE_BLOCK); split; [left; reflexivity|];
      cbn [fst snd]; rewrite RQ in Hi; unfold SRC_FILE_BLOCK; lia ].
  assert (Hraz5 : YG0d.raZ regs5 = WF_JOIN)
    by (unfold YG0d.raZ; rewrite G5_1; unfold w64; apply unsigned_lit_small; unfold WF_JOIN; lia).
  assert (Hne5 : (YG0d.raZ regs5 =? pc_free_ra0 (as_code B)) = false)
    by (rewrite Hraz5, HRA0; reflexivity).
  unfold call_trace0, unwind_of_chain. cbn [flat_map app].
  rewrite Hne5, Hraz5. unfold kUnwindMax. cbn [firstn]. exact Hu2. }
cbv beta. intros W4 c4 Hwle4 (ly6 & S6 & regs6 & mem6 & md6 & -> & J6 & AP6 & HSPLIT6 & HFR6 & KEPT6 & IO6).
pose proof JF as (_ & _ & _ & _ & _ & _ & _ & _ & FF1 & _).
pose proof KEPT4 as (K4a & K4b & K4c & _ & _ & _).
pose proof KEPT6 as (K6a & K6b & K6c & _ & _ & _).
(* every address of fclose's own frame is kept by each step after phase 1 *)
assert (SLOT : forall a, sp0 - 48 <= a < sp0 ->
          aview wsegs (w_H W4) mem6 a = aview wsegs (w_H W) mem1 a).
{ intros a Ha. rewrite FS in Hslo.
  rewrite (K6a a ltac:(lia) ltac:(unfold ASTACK; lia)).
  rewrite (KEPT5v a).
  rewrite (K4a a ltac:(lia) ltac:(unfold ASTACK; lia)).
  rewrite (KEPT2v a ltac:(lia) ltac:(lia) ltac:(unfold WF_OFL_HEAD; lia)).
  rewrite (FF1 a ltac:(lia) ltac:(rewrite R1sp; unfold PFFLUSH_OWN_STK; lia)). reflexivity. }
assert (SLOTB : forall a, sp0 - 48 <= a < sp0 ->
          mbyte wsegs (mrestrict (w_H W4) mem6) a = mbyte wsegs (mrestrict (w_H W) mem1) a)
  by (intros a Ha; apply mbyte_of_aview; exact (SLOT a Ha)).
assert (CELL6 : forall off r, In (off, SOff r 0) cells1 ->
          val_mem wsegs (mrestrict (w_H W4) mem6) (sp0 + off) 8
            (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))).
{ intros off r Hin. eapply val_mem_frame; [| exact (CELL1 off r Hin)].
  intros x Hx. apply SLOTB. unfold cells1 in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <-; lia|]). destruct Hin. }
assert (R6sp : getr regs6 2 = w64 (sp0 - 48)).
{ rewrite Ebv2, (AP6 2 ltac:(unfold acallee_saved; lia)), <- Ebv2.
  rewrite Ebv2, (KEPT3r 2 ltac:(unfold KEPT3; cbn; tauto)), <- Ebv2.
  rewrite Ebv2, (AP4 2 ltac:(unfold acallee_saved; lia)), <- Ebv2. exact G3_2. }
assert (R6sp' : YG0d.spZ regs6 = sp0 - 48)
  by (unfold YG0d.spZ; rewrite R6sp; unfold w64; apply unsigned_lit_small; lia).
assert (R6_9 : getr regs6 9 = w64 0).
{ rewrite Ebv9, (AP6 9 ltac:(unfold acallee_saved; lia)), <- Ebv9.
  rewrite Ebv9, (KEPT3r 9 ltac:(unfold KEPT3; cbn; tauto)), <- Ebv9.
  rewrite Ebv9, (AP4 9 ltac:(unfold acallee_saved; lia)), <- Ebv9.
  rewrite G3_9. exact GF10. }
assert (R6_18 : getr regs6 18 = w64 0).
{ rewrite Ebv18, (AP6 18 ltac:(unfold acallee_saved; lia)), <- Ebv18.
  rewrite Ebv18, (KEPT3r 18 ltac:(unfold KEPT3; cbn; tauto)), <- Ebv18.
  rewrite Ebv18, (AP4 18 ltac:(unfold acallee_saved; lia)), <- Ebv18. exact G3_18. }
change (mkCfg (mkst regs6 (w64 WF_JOIN) mem6 (seg_rom wsegs)) md6)
  with (cfg_at wsegs WF_JOIN regs6 mem6 md6).
eapply (wf_step4 W4 W ly S mem md [] ly6 S6 regs6 mem6 md6 2 sp0 (asource_fp f)
          (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
          (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)));
  [ replace 2 with (1 + 1) by lia; exact J6 | exact R6sp' | exact R6_9 | exact R6_18
  | apply u64_range | apply u64_range | apply u64_range | apply u64_range | apply u64_range
  | exact (CELL6 (-8) 1%nat ltac:(cbn; tauto)) | exact (CELL6 (-16) 8%nat ltac:(cbn; tauto))
  | exact (CELL6 (-24) 9%nat ltac:(cbn; tauto)) | exact (CELL6 (-32) 18%nat ltac:(cbn; tauto))
  | exact (CELL6 (-40) 19%nat ltac:(cbn; tauto)) |].
intros regs7 mem7 md7 J7 KEPT7v IO7 G7_10 G7_1 G7_2 G7_8 G7_9 G7_18 G7_19 KEPT2r7.
exists ly6, S6, regs7, mem7, md7.
(* 1. the configuration: the `ret` leaves through the entry's own return address *)
assert (ERET : v_jalr (w64 (bv_unsigned (getr regs 1))) 0 = getr regs 1)
  by (unfold w64; rewrite Z_to_bv_bv_unsigned; exact Hra).
split; [rewrite ERET; reflexivity|].
split; [exact J7|].
(* 2. the callee-saved registers: 3, 4 and 20..27 are never written; 2, 8, 9, 18 and 19 come
   back off fclose's own frame in the epilogue. *)
split.
{ intros r Hr.
  assert (KEEP : In r KEPT2 -> getr regs7 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros Hz.
    rewrite (KEPT2r7 r Hz), (AP6 r Hr),
      (KEPT3r r ltac:(unfold KEPT2, KEPT3 in *; cbn in *; tauto)), (AP4 r Hr),
      (KEPT2r r Hz), (APF r Hr),
      (KEPT1r r ltac:(unfold KEPT1, KEPT2 in *; cbn in *; tauto)). reflexivity. }
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - rewrite <- Ebv2, G7_2. exact ESP0.
  - apply KEEP. unfold KEPT2. cbn. tauto.
  - apply KEEP. unfold KEPT2. cbn. tauto.
  - rewrite <- Ebv8, G7_8. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite <- Ebv9, G7_9. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - destruct (Z.eq_dec r 18) as [-> | H18].
    + rewrite <- Ebv18, G7_18. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + destruct (Z.eq_dec r 19) as [-> | H19].
      * rewrite <- Ebv19, G7_19. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
      * apply KEEP. unfold KEPT2. cbn. lia. }
(* 3. a0 = 0 *)
split; [exact G7_10|].
(* 4. the FILE block, and only it, left ablocks *)
split.
{ destruct HSPLIT6 as (l1 & l2 & Esplit & Erem). rewrite Erem.
  apply (Permutation_cons_inv (l := l1 ++ l2) (l' := rest) (a := (f, SRC_FILE_BLOCK))).
  eapply Permutation_trans; [apply (Permutation_middle l1 l2 (f, SRC_FILE_BLOCK))|].
  rewrite <- Esplit. eapply Permutation_trans; [exact HPERM4 | exact Hperm]. }
(* 5. the frame count *)
split; [rewrite HFR6, HFR4; reflexivity|].
(* 6. the stream is closed: the image cells are kept by every step, and the head is 0 *)
assert (IMGK : forall a, in_img wsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
          ~ (as_errno B <= a < as_errno B + 4) ->
          mbyte wsegs (mrestrict (w_H W4) mem7) a = mbyte wsegs (mrestrict (w_H W2) mem3) a).
{ intros a Hi Ho He. apply mbyte_of_aview.
  rewrite (KEPT7v a), (K6c a Hi Ho He), (KEPT5v a), (K4c a Hi Ho He). reflexivity. }
assert (ENVK : forall a, asrc_env_addr K a ->
          mbyte wsegs (mrestrict (w_H W4) mem7) a = mbyte wsegs (mrestrict (w_H W2) mem3) a).
{ intros a Ha. destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He). apply IMGK; assumption. }
assert (ENVKEEP : forall (mx my : word -> option byte),
  (forall a, asrc_env_addr K a -> ~ (WF_OFL_HEAD <= a < WF_OFL_HEAD + 8) ->
     mbyte wsegs my a = mbyte wsegs mx a) ->
  asrc_stdio_env wsegs K mx -> asrc_stdio_env wsegs K my).
{ intros mx my IMG (E1 & E2 & E3 & E4 & E5 & cv & Hcv & E6).
  assert (NH : forall a,
            a = as_threaded K \/ a = as_need_locks K \/ (as_ofl_lock K <= a < as_ofl_lock K + 4) \/
            (as_mode K <= a < as_mode K + 3) \/ (as_rwa K <= a < as_rwa K + 4) \/
            (as_canary K <= a < as_canary K + 8) ->
            mbyte wsegs my a = mbyte wsegs mx a).
  { intros a Ha. apply IMG.
    - unfold asrc_env_addr. lia.
    - rewrite <- HSK. exact (asil_env_static _ _ _ _ ASIL a Ha). }
  split; [eapply val_mem_frame; [|exact E1]; intros x Hx; apply NH; lia|].
  split; [eapply val_mem_frame; [|exact E2]; intros x Hx; apply NH; lia|].
  split; [eapply val_mem_frame; [|exact E3]; intros x Hx; apply NH; lia|].
  split; [eapply garr8_frame; [exact E4|]; intros x Hx;
          cbn [length src_mode_Z app] in Hx; apply NH; lia|].
  split; [eapply garr8_frame; [exact E5|]; intros x Hx;
          cbn [length src_modeset_Z app] in Hx; apply NH; lia|].
  exists cv. split; [exact Hcv|].
  eapply val_mem_frame; [|exact E6]. intros x Hx. apply NH. lia. }
assert (ENV3 : asrc_stdio_env wsegs K (mrestrict (w_H W2) mem3)).
{ apply (ENVKEEP (mrestrict (w_H W2) mem2)); [| exact Henv2].
  intros a Ha Hh. apply mbyte_of_aview.
  pose proof (proj1 (asil_env _ _ _ _ ASIL a Ha)) as Hi. pose proof (SEGS_LOW a Hi) as Hlo.
  apply KEPT2v; [unfold kLowMemEnd in *; lia | rewrite FS in Hslo; unfold kLowMemEnd in *; lia | exact Hh]. }
split.
{ split.
  - apply (ENVKEEP (mrestrict (w_H W2) mem3)); [| exact ENV3].
    intros a Ha _. exact (ENVK a Ha).
  - rewrite HEADK. eapply val_mem_frame; [| exact HEAD0].
    intros x Hx. apply ENVK. unfold asrc_env_addr. rewrite HKS.
    cbn [as_threaded as_need_locks as_ofl_lock as_mode as_rwa as_canary pcap_KS].
    unfold WF_OFL_HEAD, PCAP_OFL_LOCK in *. lia. }
(* 7. the harness's buffer survives: it is a live block, disjoint from the FILE block the
   second free removes, and no phase writes it. *)
split.
{ eapply garr8_frame; [exact Hgar2|]. intros x Hx. apply mbyte_of_aview.
  destruct (al_blocks _ _ LAWS ly S W2 mem2 md2 b (Z.of_nat (length C)) HAR2 Hbblk)
    as (_ & Hb0'' & Hbc'' & _).
  assert (Hbx : 0 <= x - b < req_size (Z.of_nat (length C)))
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length C)) 0); lia).
  assert (Hbf : ~ (f <= x < f + req_size SRC_FILE_BLOCK))
    by (rewrite RQ; unfold SRC_FILE_BLOCK in *; lia).
  assert (Hbblk4 : In (b, Z.of_nat (length C)) (ablocks B ly4 S4))
    by (apply (Permutation_in _ (Permutation_sym HPERM4)); exact Hbblk).
  transitivity (aview wsegs (w_H W4) mem6 x); [apply KEPT7v|].
  transitivity (aview wsegs (w_H W3) mem5 x);
    [replace x with (b + (x - b)) by lia;
     apply (K6b b (Z.of_nat (length C)) (x - b) Hbblk4 Hbx);
     replace (b + (x - b)) with x by lia; exact Hbf|].
  transitivity (aview wsegs (w_H W3) mem4 x); [apply KEPT5v|].
  transitivity (aview wsegs (w_H W2) mem3 x);
    [replace x with (b + (x - b)) by lia;
     apply (K4b b (Z.of_nat (length C)) (x - b) Hbblk Hbx); intros []|].
  apply KEPT2v; [lia | rewrite FS in Hslo; lia|].
  intros Hh. exact (blk_img wsegs B LAWS ly S W2 mem2 md2 b (Z.of_nat (length C)) x
                      HAR2 Hbblk ltac:(lia) (HIMGE x (or_intror (or_intror Hh)))). }
(* 8. no descriptor and no file-system change *)
assert (FDS : forall mx my, same_io mx my -> m_fds my = m_fds mx /\ m_fs my = m_fs mx).
{ intros mx my (E1 & E2 & E3 & E4). unfold m_fds, m_fs. rewrite E1, E3. split; reflexivity. }
split.
- rewrite (proj1 (FDS _ _ IO7)), (proj1 (FDS _ _ IO6)), (proj1 (FDS _ _ IO5)),
    (proj1 (FDS _ _ IO4)), (proj1 (FDS _ _ IO3)), HFD2, (proj1 (FDS _ _ IO1)). reflexivity.
- rewrite (proj2 (FDS _ _ IO7)), (proj2 (FDS _ _ IO6)), (proj2 (FDS _ _ IO5)),
    (proj2 (FDS _ _ IO4)), (proj2 (FDS _ _ IO3)), HFS2, (proj2 (FDS _ _ IO1)). reflexivity.
Qed.

End T.

End C.
Print Assumptions wsegs_wx.
Print Assumptions wsegs_low.
Print Assumptions wfc_tbl_ok.
Print Assumptions wfc_tbl_probe.
Print Assumptions WF_named_val.
Print Assumptions WF_cells_val.
Print Assumptions shape1_ok.
Print Assumptions shape2a_ok.
Print Assumptions shape2b_ok.
Print Assumptions shape2c_ok.
Print Assumptions shape2d_ok.
Print Assumptions shape3_ok.
Print Assumptions shape4_ok.
Print Assumptions wf_ajournal_sub_tok.
Print Assumptions wf_step1.
Print Assumptions wf_step2.
Print Assumptions wf_step3.
Print Assumptions wf_step4.
Print Assumptions pcapu_afclose_source_spec_musl.
About pcapu_afclose_source_spec_musl.
