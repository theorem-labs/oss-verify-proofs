(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_emitx.v (a working branch),
   the same names over B's states (frame 64, eight saved registers).
   rule 24: proves no function (kind: segment lemma; check_as_written, B 0x8164c, CONFIRM by a Theorem Labs lane). *)
(* The hand-over from the EMIT LOOP of check_as_written over fs.asan-ubsan (B A_check_as_written 0x8164c) to the back
   half of the function, at the loop exit 0x81a78 (`jal __wrap_free` of six).

   FSW_caw_emit.v's caw_emit_loop leaves the walk at 0x81a78 in cae_exit_ss: the loop's registers and atom facts and
   NO region.  The back half takes the walk at 0x81a78 in FSW_caw_accept.v's caa_xss: the registers re-keyed onto
   the atoms 44 .. (caa_P), the kept atom facts caa_xatoms and the frame region caw_stk (FSW_caw_defs.v), whose eight
   chunks the epilogue 0x81aac .. 0x81ac8 reads back (saved s6, s5, s4, s3, s2, s1, s0 and the entry ra).
   caw_emit_exit proves the hand-over:
   - the frame region is moved from the memory of a state that held it (ms0) to the post-loop memory (ms1): every
     byte of [sp0 - 64, sp0) is unchanged, so the eight chunks read the same bytes, and the write window [-64, 0)
     stays writable because the restricted memory only grows (YP09.writable_at_grows);
   - the registers are re-keyed with YL09.st_ok_reabs straight onto caa_xss with the target regions [caw_stk]:
     every kept register (atoms < 44: ra's 31 and ~six's 30 among them) is the same sv in cae_regs and caa_xregs,
     every atom fact of caa_xatoms (2, 32, 33, 34, 38) is in cae_exit_atoms with the same bounds, so reabs_check holds
     as it stands and the fact obligations are empty; the register obligations (atoms >= 44) are the caller's
     premise.

   HEADER: no Axiom, no Parameter, no Admitted, no admit, no Abort, no Hypothesis.  The lemma calls nothing, so it
   carries no callee contract; every premise is an explicit premise of the lemma, owned by its caller (a Theorem Labs lane).
   The Section carries only the three instance variables of the lane and the allocator symbols B. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP05 YL01 YL02 YL07 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K
FSW_caw_defs FSW_caw_model FSW_caw_tail FSW_caw_emit FSW_caw_accept.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* a chunk whose bytes read the same in m' as in m is ok in m' *)
Lemma cax_chunk_same : forall E (m m' : word -> option byte) base c,
  YP09.chunk_ok tfibsegs E m base c ->
  (forall i, 0 <= i < YP09.c_len c ->
     YP09.mbyte tfibsegs m' (base + YP09.c_off c + i) = YP09.mbyte tfibsegs m (base + YP09.c_off c + i)) ->
  YP09.chunk_ok tfibsegs E m' base c.
Proof.
intros E m m' base c Hc Heq i Hi. destruct (Hc i Hi) as (b & Hb & Hm).
exists b. split; [exact Hb|]. rewrite (Heq i Hi). exact Hm.
Qed.

(* a byte of [lo, hi) the raw memories agree on reads the same through the same restriction *)
Lemma cax_mbyte_same : forall (Hh : word -> bool) (m0 m1 : word -> option byte) lo hi a,
  (forall x : word, lo <= bv_unsigned x < hi -> m1 x = m0 x) ->
  0 <= a < 2 ^ 64 -> lo <= a < hi ->
  YP09.mbyte tfibsegs (mrestrict Hh m1) a = YP09.mbyte tfibsegs (mrestrict Hh m0) a.
Proof.
intros Hh m0 m1 lo hi a Heq Ha Hin. unfold YP09.mbyte, mrestrict.
destruct (Hh (Z_to_bv 64 a)); [reflexivity|].
rewrite (Heq (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hin.
Qed.

(* the frame region moves to a memory that keeps every byte of [sp0 - 64, sp0) and only grows *)
Lemma cax_stk_move : forall (Hh : word -> bool) E (m0 m1 : word -> option byte) sp0,
  YP09.region_ok tfibsegs E (mrestrict Hh m0) caw_stk ->
  bv_unsigned (ew E 2) = sp0 ->
  (forall x : word, sp0 - 64 <= bv_unsigned x < sp0 -> m1 x = m0 x) ->
  mem_grows (mrestrict Hh m0) (mrestrict Hh m1) ->
  YP09.region_ok tfibsegs E (mrestrict Hh m1) caw_stk.
Proof.
intros Hh E m0 m1 sp0 HR Hsp Heq Hg.
unfold YP09.region_ok, caw_stk in HR |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val] in HR |- *.
rewrite Hsp in HR |- *.
destruct HR as (Hlo & Hhi & Hwr & Hck).
split; [exact Hlo|]. split; [exact Hhi|]. split.
- intros o Ho. exact (YP09.writable_at_grows tfibsegs _ _ _ Hg (Hwr o Ho)).
- rewrite Forall_forall in Hck |- *. intros c Hin.
  apply (cax_chunk_same E (mrestrict Hh m0) _ _ c (Hck c Hin)).
  cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
    intros i Hi; cbn [YP09.c_len YP09.c_off YP09.c_val YP09.cv_len Z.of_N] in Hi |- *;
    (apply (cax_mbyte_same Hh m0 m1 (sp0 - 64) sp0); [exact Heq | lia | lia]).
Qed.

(* ---- the hand-over at 0x81a78: the emit loop's exit state, with the frame region of a state that held it
   (ms0) moved onto the post-loop memory, re-keyed into the back half's state caa_xss ---- *)
Lemma caw_emit_exit : forall (W : world tfibsegs) (E1 E2 : env) (ms0 ms1 : machine_state) (sp0 : Z),
  st_ok tfibsegs E1 cae_exit_ss (restrict (w_H W) ms1) ->
  region_ok tfibsegs E1 (ms_mem (restrict (w_H W) ms0)) caw_stk ->
  bv_unsigned (ew E1 2) = sp0 ->
  (forall x : word, sp0 - 64 <= bv_unsigned x < sp0 -> ms_mem ms1 x = ms_mem ms0 x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms1)) ->
  env_agree 44 E1 E2 ->
  Forall (fun rj : bv 5 * nat => ew E2 (snd rj) = getr (ms_regs ms1) (fst rj)) (reabs_obl caa_P caa_xregs) ->
  st_ok tfibsegs E2 caa_xss (restrict (w_H W) ms1).
Proof.
intros W E1 E2 ms0 ms1 sp0 HS HR Hsp Heq Hg HAG HOB.
assert (HR1 : region_ok tfibsegs E1 (ms_mem (restrict (w_H W) ms1)) caw_stk)
  by exact (cax_stk_move (w_H W) E1 (ms_mem ms0) (ms_mem ms1) sp0 HR Hsp Heq Hg).
assert (HM1 : mem_ok tfibsegs E1 (ms_mem (restrict (w_H W) ms1)) [caw_stk]).
{ split; [vm_compute; reflexivity|]. split.
  - apply Forall_cons; [exact HR1 | apply Forall_nil].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I. }
unfold caa_xss.
apply (st_ok_reabs tfibsegs caa_P E1 E2 cae_exit_ss (restrict (w_H W) ms1) caa_xregs [caw_stk]
        (mkFacts caa_xatoms [] []) HS (caa_agree_pd E1 E2 HAG) ltac:(vm_compute; reflexivity) HOB).
- apply Forall_forall. intros nf Hin. vm_compute in Hin. destruct Hin.
- apply (mem_ok_agree tfibsegs 44 E1 E2); [exact HAG | vm_compute; reflexivity | exact HM1].
Qed.

End W.
