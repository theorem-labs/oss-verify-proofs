(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pitems_dev.v, with its module paths and module names changed; 149 of its 179 lines of code are new or changed and 512 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_epi.v
   (a working branch 2ed11a3c43f), the same names over B's own code (B listing: capstone over the
   unstripped twin of fs.asan-ubsan, whose instructions 0x8164c .. 0x81b5c equal the pinned image's).
   check_as_written over fs.asan-ubsan, the epilogue (B 0x81aa4 .. 0x81ad0): from the state FSW_caw_back.cawb_mid gives
   at the bcmp return 0x81aa4 (a0 = 0, equal bytes) or at the join 0x81aa8, to check_as_written_spec's post cawb_post:
   - 0x81aa4 `bnez a0, 0x81ad8` falls through (a0 = 0, an assumed branch condition of the symbolic state);
   - 0x81aa8 `mv a0, s2` (a0 = want), 0x81aac .. 0x81ac8 the eight reloads of ra, s0 .. s6 from the frame (the extra
     atoms 39 .. 32 of FSW_caw_back.cawb_cs), 0x81acc `addi sp, sp, 64`;
   - 0x81ad0 `j 0x530e0`, the tail call of __wrap_free (PC_free = pc_wrap_free (as_code B), RTf: FsRt.fr_free's
     type), whose return is check_as_written's: FSW_caw_back.cawb_tail from there.
   The reloads are frame-spill loads with no ASan check (B listing 0x81aac .. 0x81ac8: plain `ld` off sp), and no UBSan
   trap lies in 0x81aa4 .. 0x81ad0, so the run is the plain engine (FSW_K fsw_aj_runU) over the frame region
   [sp, sp + 64) at atom 2 holding cawb_cs.
   Rule 24: proves function check_as_written (segment: epilogue cawb_epi; check_as_written B 0x8164c, CONFIRM by
   a Theorem Labs lane); none ported, written new; template lib/A/FSW_caw_epi.v.
   Section hypotheses: FSW_caw_back.v's Section W, by name (of the runtime, RTf only). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_caw_epi.v; 813 of its 871 lines of code are new or changed and 121 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_back.v
   (a working branch 2ed11a3c43f), the same names over B's own code. Every B literal below is from
   B's listing (capstone over the unstripped twin of fs.asan-ubsan, (internal path), whose
   instructions 0x8164c .. 0x81b5c equal the pinned image's, sha256 5ac5ce0954f8...) or from B's constants (lib/B/FSH_Base.v
   PC_free 0x530e0, PC_bcmp 0x426d8, FRAME_check_as_written = 64). *)
(*   check_as_written over fs.asan-ubsan, the back of the walk: from pc 0x81a78 (the `jal __wrap_free` of six, fs.c:102)
   to the function's return, B 0x81a78 .. 0x81ad0. In order (MEASURED, B listing):
   - 0x81a78 free (six) (FsRt.fr_free, FSW_malloc_free.fsw_aj_freeU), return 0x81a7c;
   - 0x81a7c .. 0x81a90: `seqz a0, s1; sltiu a1, s5, -1; beq a0, a1 -> 0x81ad8; beqz s1 -> 0x81aa8; bne s0, s5 -> 0x81ad8;
     beqz s0 -> 0x81aa8` (fs.c:177 and same_body, fs.c:183); every branch to the abort 0x81ad8 is dead from the
     decoder's answer (B keeps the answer n in s5, A in s3);
   - 0x81a94 .. 0x81aa0 bcmp (body, want, len) (FsRt.fr_bcmp), equal bytes, so `bnez a0 -> 0x81ad8` at 0x81aa4 is dead;
   - 0x81aa8 .. 0x81acc the epilogue (ra, s0 .. s6 reloaded, sp += 64) and the TAIL call 0x81ad0 `j __wrap_free` of
     want (fs.c:185), whose return is check_as_written's return.
   No ASan check and no UBSan trap lies in 0x81a78 .. 0x81ad0 (B's trap `unimp` 0x81ad4 follows the tail `j`; the
   report-site rows of check_as_written in reloc-check/report-sites-B.tsv have no report call in this range; the
   abort 0x81ad8 is reached only by the three branches above, each refuted here).
   The segments before (FSW_caw_tail.v, FSW_caw_emit.v, FSW_caw_accept.v) hand over ONE symbolic state at 0x81a78,
   FSW_caw_accept.v's caa_xss (used by name, not copied); cawb_to_mid walks it through free (six), the branches and
   bcmp to cawb_mid (0x81aa4 / 0x81aa8), from where FSW_caw_epi.v's cawb_epi runs the epilogue and the tail free
   (cawb_tail here); FSW_caw_backE.v's cawb_enter is the two together. The epilogue's loads are the frame's own spills,
   so the runs here are the plain engine (FSW_K fsw_aj_run_toU).
   Port-from: lib/A/FSW_caw_back.v (template, re-walked on B's listing). Section hypotheses: FS_ENV, ML
   (FSW_malloc_free.v's, by name), RTb, RTf : FsRt's fr_bcmp, fr_free by their field types, IMG : fs_img_facts (the
   allocator statics are no runtime-owned cell). The two free calls need no trace hypothesis: C5's
   `\/ st_nev S < EV_MAX` from the event budget gives their trace clause.
   Rule 24: proves function check_as_written (segment: free (six) .. bcmp, cawb_to_mid; check_as_written B 0x8164c,
   CONFIRM by a Theorem Labs lane 04:15Z); none ported, written new; template lib/A/FSW_caw_back.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_rres FSW_rd FSW_strkit FSW_malloc_free FSW_caw_defs FSH_Fn_checks
FSW_caw_accept.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the frame of check_as_written as the resumed states read it: atom 2 = sp (= entry sp - 64), the eight saved
   words at sp + 0 .. sp + 56 are the extra atoms 32 .. 39 = the entry s6, s5, s4, s3, s2, s1, s0, ra (caw_stk's
   order; B prologue 0x8164c .. 0x8166c: sd s6, 0(sp) .. sd ra, 0x38(sp)) ---- *)
Definition cawb_extra (regs0 : bvmap 5 word) : list word :=
  [getr regs0 22; getr regs0 21; getr regs0 20; getr regs0 19; getr regs0 18; getr regs0 9; getr regs0 8; getr regs0 1].
Definition cawb_cs : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
   YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0));
   YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0));
   YP09.mkChunk 48 (CVal 8 (SOff 38 0)); YP09.mkChunk 56 (CVal 8 (SOff 39 0))].
(* ---- the hand-over state at 0x81a78 (`jal __wrap_free` of six) is FSW_caw_accept.v's caa_xss, by name.
   NOTE atom 2 is the ENTRY sp: the frame region caw_stk is based at atom 2 with its chunks at -64 .. -8, while the
   machine sp is SOff 2 (-64) = entry sp - 64. So the epilogue's `ld ra, 0x38(sp)` reads entry sp - 64 + 56 =
   entry sp - 8, caw_stk's last chunk (atom 1, the entry ra). Atoms 0 .. 29 are the entry registers (the front's
   Ereg convention); a0 = six (33), s2 = want (34), s5 = the answer n (49), s0 = l (12), s1 = body (11), s4 = the
   shadow base (32), ra the atom 31, gp / tp / s7 .. s11 the entry's (3, 4, 23 .. 27). ---- *)

(* ---- the states the walk resumes in after free (six) (0x81a7c): fss_ret's frame (atom 2 = the machine sp, the eight
   saved words at sp + 0 .. 56 the extra atoms 32 .. 39), with the registers and atom facts that decide the branches
   0x81a7c .. 0x81a90: the refused answer (s1 = 0, s5 = SIZE_MAX), the empty answer (s0 = s5 = 0, s1 a block body),
   the non-empty answer (s5 = s0 = l in 1 .. 3145728, s1 a block body). The engine stops the first two at the join
   0x81aa8 and the non-empty one at the bcmp call 0x426d8 with ra = 0x81aa4, a0 = s1, a1 = s2, a2 = s0 (B listing
   0x81a94 .. 0x81aa0). ---- *)
Definition cawb_G0 : list (nat * afact) := [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)].
Definition cawb_ssR : sstate :=
  mkSS 0x81a7c (sr_set (sr_set sr_atoms 9%bv (SLit 0)) 21%bv (SLit 18446744073709551615))
    [fstk_ret 64 cawb_cs] None (mkFacts cawb_G0 [] []).
Definition cawb_ssA0 : sstate :=
  mkSS 0x81a7c (sr_set (sr_set sr_atoms 8%bv (SLit 0)) 21%bv (SLit 0))
    [fstk_ret 64 cawb_cs] None (mkFacts ((9%nat, mkAF 4096 CAW_CEIL 0) :: cawb_G0) [] []).
Definition cawb_ssA1 : sstate :=
  mkSS 0x81a7c (sr_set sr_atoms 21%bv (SOff 8 0))
    [fstk_ret 64 cawb_cs] None (mkFacts ((8%nat, mkAF 1 3145728 0) :: (9%nat, mkAF 4096 CAW_CEIL 0) :: cawb_G0) [] []).
Ltac cawb_acs :=
  unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* the 32 registers, one goal each; the ones outside the bound Hr closed from it *)
Ltac cawb_reg_cases Hr tac :=
  let Hin := fresh "Hin" in
  lazymatch goal with |- context [getr _ ?r] =>
    pose proof (all_regs_in r) as Hin; cbv [all_regs In] in Hin;
    repeat (destruct Hin as [<-|Hin];
      [first [ exfalso; lazymatch type of Hr with context [bv_unsigned ?q] =>
                 let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z in Hr end; lia
             | tac ] |]);
    destruct Hin
  end.

(* ---- pure helpers ---- *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cawb_pw_last : forall (R : Z * Z -> Z * Z -> Prop) (l : list (Z * Z)) x y,
  pairwise R (l ++ [x]) -> In y l -> R y x.
Proof.
intros R l. induction l as [|z t IH]; intros x y P Hy; [destruct Hy|].
cbn [app pairwise] in P. destruct P as [F P]. destruct Hy as [<-|Hy].
- rewrite Forall_forall in F. apply F. apply in_or_app. right. left. reflexivity.
- exact (IH x y P Hy).
Qed.

(* a chunk read at one base and offset is the same chunk at another base and offset with an equal value *)
Lemma cawb_chunk_mv : forall E1 E2 m b1 b2 o1 o2 w v1 v2,
  b1 + o1 = b2 + o2 -> sv_denot E2 v2 = sv_denot E1 v1 ->
  YP09.chunk_ok tfibsegs E1 m b1 (YP09.mkChunk o1 (CVal w v1)) ->
  YP09.chunk_ok tfibsegs E2 m b2 (YP09.mkChunk o2 (CVal w v2)).
Proof.
intros E1 E2 m b1 b2 o1 o2 w v1 v2 Hb Hv H i Hi.
destruct (H i Hi) as (bb & H1 & H2). exists bb.
cbn [YP09.c_off YP09.c_val YP09.cbyte] in *. rewrite Hv, <- Hb. split; assumption.
Qed.

(* the frame read through the hand-over state (caw_stk at the entry sp, entry atoms) is cawb_cs at sp - 64 *)
Lemma cawb_cs_of_stk : forall E m sp0 R (regs0 : bvmap 5 word),
  ew E 22 = getr regs0 22 -> ew E 21 = getr regs0 21 ->
  ew E 20 = getr regs0 20 -> ew E 19 = getr regs0 19 -> ew E 18 = getr regs0 18 ->
  ew E 9 = getr regs0 9 -> ew E 8 = getr regs0 8 -> ew E 1 = getr regs0 1 ->
  Forall (YP09.chunk_ok tfibsegs E m sp0) (YP09.r_chunks caw_stk) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg R (cawb_extra regs0)) m (sp0 - 64)) cawb_cs.
Proof.
intros E m sp0 R regs0 E22 E21 E20 E19 E18 E9 E8 E1 H.
unfold caw_stk in H. cbn [YP09.r_chunks] in H.
apply Forall_cons_iff in H as [C0 H]. apply Forall_cons_iff in H as [C1 H].
apply Forall_cons_iff in H as [C2 H]. apply Forall_cons_iff in H as [C3 H].
apply Forall_cons_iff in H as [C4 H]. apply Forall_cons_iff in H as [C5 H].
apply Forall_cons_iff in H as [C6 H]. apply Forall_cons_iff in H as [C7 _].
unfold cawb_cs.
constructor; [eapply cawb_chunk_mv; [| |exact C0]; [lia | rewrite !fsw_SOff0, E22; reflexivity]|].
constructor; [eapply cawb_chunk_mv; [| |exact C1]; [lia | rewrite !fsw_SOff0, E21; reflexivity]|].
constructor; [eapply cawb_chunk_mv; [| |exact C2]; [lia | rewrite !fsw_SOff0, E20; reflexivity]|].
constructor; [eapply cawb_chunk_mv; [| |exact C3]; [lia | rewrite !fsw_SOff0, E19; reflexivity]|].
constructor; [eapply cawb_chunk_mv; [| |exact C4]; [lia | rewrite !fsw_SOff0, E18; reflexivity]|].
constructor; [eapply cawb_chunk_mv; [| |exact C5]; [lia | rewrite !fsw_SOff0, E9; reflexivity]|].
constructor; [eapply cawb_chunk_mv; [| |exact C6]; [lia | rewrite !fsw_SOff0, E8; reflexivity]|].
constructor; [eapply cawb_chunk_mv; [| |exact C7]; [lia | rewrite !fsw_SOff0, E1; reflexivity]|].
constructor.
Qed.

(* cawb_cs reads only the extra atoms, so the registers of the Ereg env do not matter *)
Lemma cawb_cs_Ereg : forall r1 r2 xs m b,
  Forall (YP09.chunk_ok tfibsegs (Ereg r1 xs) m b) cawb_cs -> Forall (YP09.chunk_ok tfibsegs (Ereg r2 xs) m b) cawb_cs.
Proof.
intros r1 r2 xs m b H. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) H c Hc) as Hk.
unfold cawb_cs in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
  (eapply cawb_chunk_mv; [| |exact Hk]; [lia | rewrite !fsw_SOff0; reflexivity]).
Qed.

(* cawb_cs on a memory that keeps the 64 frame bytes *)
Lemma cawb_cs_kept : forall E m m' b,
  (forall a, b <= a < b + 64 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m b) cawb_cs -> Forall (YP09.chunk_ok tfibsegs E m' b) cawb_cs.
Proof.
intros E m m' b Hk H. apply Forall_forall. intros c Hc.
apply (chunk_ok_mbyte E m m' b c); [|exact (proj1 (Forall_forall _ _) H c Hc)].
intros i Hi. apply Hk. unfold cawb_cs in Hc. cbn [In] in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn in Hi |- *; lia.
Qed.

(* a register the state leaves as its own atom / as an atom *)
Lemma cawb_reg_atom : forall E ss (H : word -> bool) ms (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof. intros E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply fsw_SOff0. Qed.
Lemma cawb_reg_self : forall E ss (H : word -> bool) ms (r : bv 5),
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
  getr (ms_regs ms) r = ew E (Z.to_nat (bv_unsigned r)).
Proof. intros E ss H ms r HS Hr. exact (cawb_reg_atom E ss H ms r _ HS Hr). Qed.

(* the chunks of the frame read off a state whose first region is caw_stk (FSW_caw_front's cawf_frame_chunks) *)
Lemma cawb_frame_chunks : forall E ss ms (H : word -> bool) sp0,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) 0 = Some caw_stk ->
  bv_unsigned (ew E 2) = sp0 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H (ms_mem ms)) sp0) (YP09.r_chunks caw_stk).
Proof.
intros E ss ms H sp0 HS Hm E2.
pose proof (fsw_region_nth E ss (restrict H ms) 0 caw_stk HS Hm) as HR.
cbn [ms_mem restrict] in HR. destruct HR as (_ & _ & _ & Hcs).
unfold caw_stk in *. cbn [YP09.r_base base_val] in Hcs. rewrite E2 in Hcs. exact Hcs.
Qed.

(* one more atom fact on a state (FSW_caw_front's cawf_add_atom / cawf_afact) *)
Lemma cawb_add_atom : forall E ss ms n f,
  st_ok tfibsegs E ss ms -> afact_ok E n f ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
      (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms n f HS Hf. apply (st_ok_facts tfibsegs E ss ms); [exact HS|].
apply facts_ok_add_atom; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))) | exact Hf].
Qed.
Lemma cawb_afact : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi Hn Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hn, unsigned_lit_small by exact Hv. rewrite Z.pow_0_r, Z.mod_1_r.
split; [lia | split; [reflexivity | lia]].
Qed.
End h.

(* the allocator statics fs_glob reads are image bytes (fs.asan .data / .bss) *)
Lemma cawb_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hseg : forallb (fun r : Z * Z => existsb (fun s : Segment => (Z.of_N (seg_base s) <=? fst r) &&
  (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) FS_PSTAT_FP = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hseg. specialize (Hseg r Hr). apply existsb_exists in Hseg as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis RTb : FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp.
Hypothesis RTf : pc_wrap_free (as_code B) = PC_free /\ FSupoisonU.afree_realizesU tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the spec's post (FSH_Fn_checks.v check_as_written_spec) *)
Definition cawb_post (regs0 : bvmap 5 word) ly0 S0 U W0 mem0 md0 (live peak cnt fail : Z) :
    world tfibsegs -> config -> Prop :=
  @fpostU fx rc SK tfibsegs B STK_check_as_written (spZ regs0) [] regs0 ly0 S0 U W0 mem0 md0 EV_check_as_written U
    (fun ly' S' W' regs' mem' md' =>
       Permutation (ablocks B ly' S') (ablocks B ly0 S0) /\ fs_glob tfibsegs W' mem' live peak cnt fail).

(* ---- the state at the bcmp return 0x81aa4 (and at 0x81aa8, where the refused arm, the l = 0 arm and the bcmp arm
   meet): the epilogue 0x81aa8 .. 0x81acc and the tail free 0x81ad0 take it to cawb_post.
   regs0 / ly0 S0 U W0 mem0 md0 are the entry's (check_as_written_spec's fpreU), want / nw the block that is still
   live (fs.c:167), ly S W regs mem mdc the machine's here: three events done (malloc want, malloc six, free six), the
   live blocks are the entry's plus want, s2 = want, sp = entry sp - 64, gp / tp / s7 .. s11 the entry's, and the
   frame at [sp, sp + 64) holds the entry's s6, s5, s4, s3, s2, s1, s0, ra (the extra atoms 32 .. 39 of cawb_cs).
   At 0x81aa4 a0 is bcmp's answer 0 (equal bytes). ---- *)
Definition cawb_mid (pc : Z) (regs0 : bvmap 5 word) (ly0 : alayout) (S0 : astate) (U : list (Z * Z))
    (W0 : world tfibsegs) (mem0 : word -> option byte) (md0 : Model) (want nw : Z)
    (W : world tfibsegs) (c : config) : Prop :=
  exists ly S regs mem mdc,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) mdc /\
    (pc = 0x81aa4 -> getr regs 10 = w64 0) /\
    @ajournal rc SK tfibsegs B STK_check_as_written (spZ regs0) [] ly0 S0 W0 (unpoison U mem0) md0 []
      ly S W (unpoison U mem) mdc 3 /\
    ARU tfibsegs B ly S U W mem mdc /\
    Permutation (ablocks B ly S) ((want, nw) :: ablocks B ly0 S0) /\
    (forall m, ~ In (want, m) (ablocks B ly0 S0)) /\
    getr regs 18 = w64 want /\ spZ regs = spZ regs0 - 64 /\
    getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
    (forall r : bv 5, 23 <= bv_unsigned r <= 27 -> getr regs r = getr regs0 r) /\
    Forall (YP09.chunk_ok tfibsegs (Ereg regs (cawb_extra regs0)) (mrestrict (w_H W) mem) (spZ regs0 - 64)) cawb_cs.

(* below the shadow the memory is the allocator's (no user-poisoned shadow byte there) *)
Lemma cawb_aview_low : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < SHADOW_OFF ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha. apply (aview_at tfibsegs). apply unpoison_out.
rewrite (wz a ltac:(unfold SHADOW_OFF in Ha; lia)).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
assert (UF : aowned B ly S a /\ SHADOW_OFF <= a < kHighMemBeg) by (eapply ush_facts; eassumption).
lia.
Qed.

(* fs_glob at the end from fs_glob at the entry: the four statics are image bytes no runtime owns (IMG), so the
   journal keeps them *)
Lemma cawb_glob : forall STK sp0 ly0 S0 U W0 mem0 md0 ly S W mem md k live peak cnt fail,
  @ajournal rc SK tfibsegs B STK sp0 [] ly0 S0 W0 (unpoison U mem0) md0 [] ly S W (unpoison U mem) md k ->
  ARU tfibsegs B ly0 S0 U W0 mem0 md0 -> ARU tfibsegs B ly S U W mem md ->
  fs_glob tfibsegs W0 mem0 live peak cnt fail -> fs_glob tfibsegs W mem live peak cnt fail.
Proof.
intros STK sp0 ly0 S0 U W0 mem0 md0 ly S W mem md k live peak cnt fail HJ HARU0 HARU HG.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIM & _).
assert (K : forall g, In (g, g + 8) FS_PSTAT_FP -> forall k, (k < 8)%nat ->
  mbyte tfibsegs (mrestrict (w_H W) mem) (g + Z.of_nat k) =
  mbyte tfibsegs (mrestrict (w_H W0) mem0) (g + Z.of_nat k)).
{ intros g Hg j Hj.
  assert (Hin : inFP FS_PSTAT_FP (g + Z.of_nat j)) by (apply (inFP_FS_PSTAT_FP g Hg); lia).
  destruct (proj1 IMG _ Hin) as [Hown Herr].
  assert (Hlo : 0 <= g + Z.of_nat j < SHADOW_OFF).
  { unfold FS_PSTAT_FP in Hg. unfold SHADOW_OFF.
    destruct Hg as [Hg|[Hg|[Hg|[Hg|[]]]]]; injection Hg as Hg _; subst g; lia. }
  apply (mbyte_of_aview tfibsegs).
  rewrite <- (cawb_aview_low ly S U W mem md _ HARU Hlo), <- (cawb_aview_low ly0 S0 U W0 mem0 md0 _ HARU0 Hlo).
  apply HIM.
  - exact (cawb_pstat_img _ Hin).
  - exact Hown.
  - exact Herr.
  - apply inFP_nil.
  - apply fp_spares_closed. exact sink_closed_nil. }
destruct HG as (G1 & G2 & G3 & G4 & R).
split; [intros j Hj; rewrite (K G_LIVE ltac:(cbv; tauto) j Hj); exact (G1 j Hj)|].
split; [intros j Hj; rewrite (K G_PEAK ltac:(cbv; tauto) j Hj); exact (G2 j Hj)|].
split; [intros j Hj; rewrite (K G_COUNT ltac:(cbv; tauto) j Hj); exact (G3 j Hj)|].
split; [intros j Hj; rewrite (K G_FAIL ltac:(cbv; tauto) j Hj); exact (G4 j Hj)|].
exact R.
Qed.

(* ---- the tail call 0x81ad0 `j __wrap_free` of want: free returns to the caller's ra, which is the function's
   return ---- *)
Lemma cawb_tail : forall regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail regsF memF mdF ly S W want nw,
  fpreU tfibsegs B STK_check_as_written ly0 S0 U W0 regs0 mem0 md0 ch ->
  fs_heads B ly0 S0 U ->
  fs_glob tfibsegs W0 mem0 live peak cnt fail ->
  st_nev S0 + EV_check_as_written <= EV_MAX ->
  @ajournal rc SK tfibsegs B STK_check_as_written (spZ regs0) [] ly0 S0 W0 (unpoison U mem0) md0 []
    ly S W (unpoison U memF) mdF 3 ->
  ARU tfibsegs B ly S U W memF mdF ->
  Permutation (ablocks B ly S) ((want, nw) :: ablocks B ly0 S0) ->
  (forall m, ~ In (want, m) (ablocks B ly0 S0)) ->
  aregs_preserved regs0 regsF -> getr regsF 1 = getr regs0 1 -> getr regsF 10 = w64 want ->
  SRr tfibsegs W (mkCfg (mkst regsF (Z_to_bv 64 (pc_wrap_free (as_code B))) memF (seg_rom tfibsegs)) mdF)
    (cawb_post regs0 ly0 S0 U W0 mem0 md0 live peak cnt fail).
Proof.
intros regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail regsF memF mdF ly S W want nw
  HPRE HH HG Hev HJ HARU HPerm Hfresh HP Hra1 Ha0.
destruct HPRE as [HAPU _].
pose proof (fsw_ARU B _ _ _ _ _ _ _ _ _ HAPU) as HARU0.
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HJ as (HARj & Hly & _ & _ & _ & _ & Hnev & _ & G1 & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_check_as_written = 16448) by reflexivity.
assert (FE : EV_check_as_written = 4) by reflexivity.
assert (Hin : In (want, nw) (ablocks B ly S))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity]).
assert (HHc : fs_heads B ly S U).
{ intros r Hr. destruct (HH r Hr) as (E16 & m & Hm & M16). split; [exact E16|]. exists m. split; [|exact M16].
  eapply Permutation_in; [apply Permutation_sym; exact HPerm | right; exact Hm]. }
assert (Hn16 : ~ In (want, 16) U).
{ intros Hu. destruct (HH _ Hu) as (_ & m & Hm & _). exact (Hfresh m Hm). }
pose proof (ARU_free_outside tfibsegs B LAWS ly S U W memF mdF want nw HARU HHc Hin Hn16) as Hout.
assert (P2 : getr regsF 2 = getr regs0 2) by (apply (fsw_pres regs0 regsF 2%bv HP); cawb_acs).
assert (P3 : getr regsF 3 = getr regs0 3) by (apply (fsw_pres regs0 regsF 3%bv HP); cawb_acs).
assert (P4 : getr regsF 4 = getr regs0 4) by (apply (fsw_pres regs0 regsF 4%bv HP); cawb_acs).
assert (P8 : getr regsF 8 = getr regs0 8) by (apply (fsw_pres regs0 regsF 8%bv HP); cawb_acs).
assert (Hsp : spZ regsF = spZ regs0 + 0) by (unfold spZ; rewrite P2; lia).
assert (Hch' : chain_pre ly (aview tfibsegs (w_H W) (unpoison U memF)) regsF ch).
{ apply (achain_chain_pre ly _ (spZ regs0) (s0Z regs0) ch regsF).
  - apply (achain_ly_top ly0 ly); [first [exact Etop | symmetry; exact Etop]|].
    apply (achain_kept ly0 _ _ (spZ regs0) (s0Z regs0) ch (spZ regs0) Hch); [lia | lia |].
    intros a Ha. apply G1; lia.
  - lia.
  - unfold s0Z. rewrite P8. reflexivity.
  - unfold raZ. rewrite Hra1. exact Hra4. }
eapply SRr_mono.
{ exact (@fsw_aj_freeU fx rc SK B FS_ENV ML (proj2 RTf) W regsF memF STK_check_as_written
    (spZ regs0) [] ly0 S0 W0 mem0 md0 [] ly S U mdF 3 want nw 0 (getr regs0 1) ch
    HJ HARU Hin Hout Ha0 Hsp eq_refl ltac:(lia) ltac:(unfold ASTACK; lia)
    ltac:(rewrite P3; exact Hgp) ltac:(rewrite P4; exact Htp) Hra1 Hra ltac:(lia) Hch'
    (fun Hw => False_ind _ (Hfresh nw Hw))). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HARU2 & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & _ & _).
pose proof HARU2 as (_ & OK2 & PO2).
unfold cawb_post, fpostU. exists ly2, S2, regs2, mem2, md2.
split; [reflexivity|].
split; [rewrite FE; exact HJ2|].
split; [exact OK2|]. split; [exact PO2|].
split; [exact (aregs_preserved_trans regs0 regsF regs2 HP HP2)|].
split.
- rewrite Ebl2. apply Permutation_sym.
  refine (Permutation_cons_app_inv l1 l2
    (_ : Permutation ((want, nw) :: ablocks B ly0 S0) (l1 ++ (want, nw) :: l2))).
  rewrite <- Ebl. apply Permutation_sym. exact HPerm.
- exact (cawb_glob _ _ ly0 S0 U W0 mem0 md0 ly2 S2 W2 mem2 md2 _ live peak cnt fail HJ2 HARU0 HARU2 HG).
Qed.

(* ---- the machine invariant from the return of free (six) to the epilogue: cawb_mid's conjuncts without the pc ---- *)
Definition cawb_inv (regs0 : bvmap 5 word) (ly0 : alayout) (S0 : astate) (U : list (Z * Z))
    (W0 : world tfibsegs) (mem0 : word -> option byte) (md0 : Model) (want nw : Z)
    (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (mdc : Model)
    : Prop :=
  @ajournal rc SK tfibsegs B STK_check_as_written (spZ regs0) [] ly0 S0 W0 (unpoison U mem0) md0 []
    ly S W (unpoison U mem) mdc 3 /\
  ARU tfibsegs B ly S U W mem mdc /\
  Permutation (ablocks B ly S) ((want, nw) :: ablocks B ly0 S0) /\
  (forall m, ~ In (want, m) (ablocks B ly0 S0)) /\
  getr regs 18 = w64 want /\ spZ regs = spZ regs0 - 64 /\
  getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  (forall r : bv 5, 23 <= bv_unsigned r <= 27 -> getr regs r = getr regs0 r) /\
  Forall (YP09.chunk_ok tfibsegs (Ereg regs (cawb_extra regs0)) (mrestrict (w_H W) mem) (spZ regs0 - 64)) cawb_cs.

Lemma cawb_mid_of_inv : forall pc regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc,
  cawb_inv regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc ->
  (pc = 0x81aa4 -> getr regs 10 = w64 0) ->
  cawb_mid pc regs0 ly0 S0 U W0 mem0 md0 want nw W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) mdc).
Proof.
intros pc regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc
  (HJ & HARU & HP & Hf & R18 & Rsp & R3 & R4 & R21 & Hcs) H10.
exists ly, S, regs, mem, mdc. split; [reflexivity|]. split; [exact H10|].
repeat (split; [assumption|]). exact Hcs.
Qed.

(* a byte of a live block reads the same through unpoison (it is no shadow byte) *)
Lemma cawb_aview_unp : forall ly S U (W : world tfibsegs) mem md p n a,
  ARU tfibsegs B ly S U W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md p n a HARU Hin Ha.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hin) as (_ & H4096 & Hcl & _).
pose proof asan_consts as (C1 & _).
apply (aview_at tfibsegs).
apply (fsw_unpoison_app B ly S U W mem md a HARU); [lia|].
exact (fsw_ablock_off_shadow B ly S W (unpoison U mem) md p n HAR Hin a Ha).
Qed.

(* the state at a return address inside the frame: fss_ret at sp = sp0 - 64 over the frame cawb_cs *)
Lemma cawb_ret_st : forall STK sp0 ly0 S0 W0 mem0 md0 ly S U W regs mem md k xs pc,
  @ajournal rc SK tfibsegs B STK sp0 [] ly0 S0 W0 mem0 md0 [] ly S W (unpoison U mem) md k ->
  ARU tfibsegs B ly S U W mem md ->
  64 <= STK -> spZ regs = sp0 - 64 ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs xs) (mrestrict (w_H W) mem) (sp0 - 64)) cawb_cs ->
  st_ok tfibsegs (Ereg regs xs) (fss_ret pc 64 cawb_cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros STK sp0 ly0 S0 W0 mem0 md0 ly S U W regs mem md k xs pc HJ HARU HSTK Hsp Hcs.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (E2 : bv_unsigned (ew (Ereg regs xs) 2) = sp0 - 64)
  by (rewrite (ew_Ereg_nat regs xs 2 2%bv eq_refl); exact Hsp).
rewrite restrict_mkst_fx. unfold fss_ret. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, fstk_ret.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly S U W mem md _ HARU); [lia|]. apply Hpres. lia.
  + exact Hcs.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. reflexivity.
Qed.

(* ---- free (six) at 0x81a78: from the hand-over state to the machine at the return 0x81a7c ---- *)
Lemma cawb_free6 : forall ly S U W0 regs mem md ch bd l (tb : list Z) E ms mdc lyc Sc W six want n nw n6,
  fpreU tfibsegs B STK_check_as_written ly S U W0 regs mem md ch -> fs_heads B ly S U ->
  getr regs 12 = w64 l -> caw_answerA tfibsegs B ly S U W0 mem tb bd l ->
  st_nev S + EV_check_as_written <= EV_MAX ->
  st_ok tfibsegs E caa_xss (restrict (w_H W) ms) ->
  ew E 1 = getr regs 1 ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> ew E (Z.to_nat (bv_unsigned r)) = getr regs r) ->
  ew E 11 = getr regs 11 -> ew E 12 = getr regs 12 ->
  ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want -> ew E 49 = Z_to_bv 64 n ->
  @ajournal rc SK tfibsegs B STK_check_as_written (spZ regs) [] ly S W0 (unpoison U mem) md [] lyc Sc W
    (unpoison U (ms_mem ms)) mdc 2 ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ablocks B lyc Sc = (ablocks B ly S ++ [(want, nw)]) ++ [(six, n6)] ->
  (forall m, ~ In (want, m) (ablocks B ly S)) -> (forall m, ~ In (six, m) (ablocks B ly S)) ->
  SRr tfibsegs W (mkCfg ms mdc) (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x81a7c) mem2 (seg_rom tfibsegs)) md2 /\
    cawb_inv regs ly S U W0 mem md want nw ly2 S2 W2 regs2 mem2 md2 /\
    getr regs2 9 = getr regs 11 /\ getr regs2 8 = getr regs 12 /\ getr regs2 21 = Z_to_bv 64 n /\
    (forall a, want <= a < want + req_size nw ->
       aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a)).
Proof.
intros ly S U W0 regs mem md ch bd l tb E ms mdc lyc Sc W six want n nw n6
  HPRE FH H12 HANS Hev HS E1 ECS E11 E12 E33 E34 E49 HJ HARU Hab Hfw Hfs.
pose proof HPRE as (HAPU & _).
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof (fsw_sp B STK_check_as_written ly S U W0 regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_check_as_written = 16448) by reflexivity.
assert (FE : EV_check_as_written = 4) by reflexivity.
assert (EA : forall (r : bv 5) (k : nat), Z.of_nat k = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
  ew E k = getr regs r) by (intros r k Hk Hc; rewrite <- (ECS r Hc); f_equal; lia).
assert (E2a : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EA 2%bv 2%nat eq_refl ltac:(cawb_acs)); reflexivity).
(* the free's frame-chain head s0 = l: SIZE_MAX (odd) or a reader block's length, below alloc_ceiling *)
assert (Hl8 : (0 <= l < alloc_ceiling) \/ (0 <= l < 2 ^ 64 /\ l mod 8 <> 0)).
{ destruct HANS as [(_ & _ & ->) | (bs & m & _ & _ & El & _ & Hrb & Hlm & _)].
  - right. unfold SIZE_MAXZ. split; [lia|]. vm_compute. discriminate.
  - left. destruct Hrb as (Hin & _ & Hm0 & _).
    destruct (al_blocks _ _ LAWS ly S W0 (unpoison U mem) md (bd - HEAD) (m + HEAD) HAR0 Hin)
      as (_ & H4096b & Hcl & _).
    assert (Hreq : req_size (m + HEAD) = m + HEAD)
      by (unfold req_size; destruct (Z.eqb_spec (m + HEAD) 0); [unfold HEAD in *; lia | reflexivity]).
    rewrite Hreq in Hcl. unfold HEAD in *. lia. }
fsw_aj_runU caw_tbl_ok HS HJ HARU.
{ unfold caa_xss. cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact E2a | cbn; lia | cbn; lia |]. apply awr_ok_nil. }
(* ---- at __wrap_free: ra = 0x81a7c, everything else as at 0x81a78 ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms0 HS eq_refl) as Hms0. cbn [ss_pc] in Hms0.
pose proof (fsw_reg_lit _ E _ ms0 1%bv 0x81a7c HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_off _ E _ ms0 2%bv 2 (-64) (spZ regs) HS ltac:(vm_compute; reflexivity) E2a ltac:(lia)) as R2.
pose proof (cawb_reg_atom E _ (w_H W) ms0 10%bv 33 HS ltac:(vm_compute; reflexivity)) as R10.
pose proof (cawb_reg_atom E _ (w_H W) ms0 18%bv 34 HS ltac:(vm_compute; reflexivity)) as R18.
pose proof (cawb_reg_atom E _ (w_H W) ms0 21%bv 49 HS ltac:(vm_compute; reflexivity)) as R21.
pose proof (cawb_reg_atom E _ (w_H W) ms0 9%bv 11 HS ltac:(vm_compute; reflexivity)) as R9.
pose proof (cawb_reg_atom E _ (w_H W) ms0 8%bv 12 HS ltac:(vm_compute; reflexivity)) as R8.
assert (RX : forall r : bv 5, (bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ 23 <= bv_unsigned r <= 27) ->
  getr (ms_regs ms0) r = getr regs r).
{ intros r Hr. cawb_reg_cases Hr ltac:(
    lazymatch goal with |- getr _ ?q = _ =>
      rewrite (cawb_reg_self E _ (w_H W) ms0 q HS ltac:(vm_compute; reflexivity)) end;
    apply ECS; cawb_acs). }
assert (Hsp0 : spZ (ms_regs ms0) = spZ regs + -64) by (unfold spZ at 1; rewrite R2; lia).
pose proof (cawb_frame_chunks E _ ms0 (w_H W) (spZ regs) HS ltac:(vm_compute; reflexivity) E2a) as HC0.
pose proof RTf as [HFPC AFREE].
rewrite Hms0. change (Z_to_bv 64 340192) with (Z_to_bv 64 PC_free). rewrite <- HFPC.
assert (Hin6 : In (six, n6) (ablocks B lyc Sc)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (Hinw : In (want, nw) (ablocks B lyc Sc))
  by (rewrite Hab; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (FHc : fs_heads B lyc Sc U).
{ intros r Hr. destruct (FH r Hr) as (E16 & m & Hm & M16). split; [exact E16|]. exists m. split; [|exact M16].
  rewrite Hab. apply in_or_app. left. apply in_or_app. left. exact Hm. }
assert (Hn16 : ~ In (six, 16) U) by (intros Hu; destruct (FH _ Hu) as (_ & m & Hm & _); exact (Hfs m Hm)).
pose proof (ARU_free_outside tfibsegs B LAWS lyc Sc U W (ms_mem ms0) _ six n6 HARU FHc Hin6 Hn16) as Hout.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
assert (Hs0 : s0Z (ms_regs ms0) = l)
  by (unfold s0Z; rewrite R8, E12, H12; unfold w64; apply unsigned_lit_small; lia).
eapply SRr_mono.
{ exact (@fsw_aj_freeU fx rc SK B FS_ENV ML AFREE W (ms_regs ms0) (ms_mem ms0) STK_check_as_written
    (spZ regs) [] ly S W0 mem md [] lyc Sc U _ 2 six n6 (-64) (Z_to_bv 64 0x81a7c) []
    HJ HARU Hin6 Hout ltac:(rewrite R10, E33; reflexivity) Hsp0 eq_refl ltac:(lia) ltac:(unfold ASTACK; lia)
    ltac:(rewrite (RX 3%bv ltac:(left; reflexivity)); exact Hgp)
    ltac:(rewrite (RX 4%bv ltac:(right; left; reflexivity)); exact Htp)
    R1 ltac:(apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity) ltac:(lia)
    ltac:(apply (achain_chain_pre lyc _ (spZ (ms_regs ms0)) (s0Z (ms_regs ms0)) [] (ms_regs ms0));
          [ left; split; [|reflexivity]; rewrite Hs0;
            destruct Hl8 as [Hx|[_ Hx]]; [left; lia | right; right; exact Hx]
          | lia | reflexivity | unfold raZ; rewrite R1, unsigned_lit_small by lia; lia ])
    (fun Hw => False_ind _ (Hfs n6 Hw))). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HARU2 & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & _ & HK2).
pose proof HK2 as (K1 & K2 & _).
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms0) r)
  by (intros r Hr; exact (fsw_pres (ms_regs ms0) regs2 r HP2 Hr)).
(* the live blocks: the entry's and want *)
assert (Hperm : Permutation (ablocks B ly2 S2) ((want, nw) :: ablocks B ly S)).
{ rewrite Ebl2.
  assert (P1 : Permutation (ablocks B ly S ++ [(want, nw)]) (l1 ++ l2)).
  { refine (Permutation_cons_app_inv l1 l2
      (_ : Permutation ((six, n6) :: (ablocks B ly S ++ [(want, nw)])) (l1 ++ (six, n6) :: l2))).
    rewrite <- Ebl, Hab. apply Permutation_cons_append. }
  apply Permutation_sym. eapply Permutation_trans; [apply Permutation_cons_append | exact P1]. }
assert (Hinw2 : In (want, nw) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
(* want's block is disjoint from six's *)
destruct (al_blocks _ _ LAWS lyc Sc W (unpoison U (ms_mem ms0)) _ six n6 (proj1 HARU) Hin6)
  as (_ & _ & _ & _ & _ & PW & _).
rewrite Hab, map_app in PW. cbn [map fst snd] in PW.
assert (Dws : zdisjoint (want, req_size nw) (six, req_size n6)).
{ apply (cawb_pw_last zdisjoint _ (six, req_size n6) (want, req_size nw) PW).
  rewrite map_app. apply in_or_app. right. left. reflexivity. }
unfold zdisjoint in Dws. cbn [fst snd] in Dws.
cbv beta. exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [|split; [|split; [|split]]].
- split; [exact HJ2|]. split; [exact HARU2|]. split; [exact Hperm|]. split; [exact Hfw|].
  split; [rewrite (KP 18%bv ltac:(cawb_acs)), R18, E34; reflexivity|].
  split; [unfold spZ at 1; rewrite (KP 2%bv ltac:(cawb_acs)), R2; lia|].
  split; [rewrite (KP 3%bv ltac:(cawb_acs)); exact (RX 3%bv ltac:(left; reflexivity))|].
  split; [rewrite (KP 4%bv ltac:(cawb_acs)); exact (RX 4%bv ltac:(right; left; reflexivity))|].
  split; [intros r Hr; rewrite (KP r ltac:(unfold acallee_saved; lia)); apply RX; right; right; exact Hr|].
  apply (cawb_cs_kept _ (mrestrict (w_H W) (ms_mem ms0))).
  + intros a Ha. apply (mbyte_of_aview tfibsegs).
    rewrite <- (fsw_aview_unpoison_high B ly2 S2 U W2 mem2 md2 a HARU2) by lia.
    rewrite <- (fsw_aview_unpoison_high B lyc Sc U W (ms_mem ms0) _ a HARU) by lia.
    apply K1; lia.
  + exact (cawb_cs_of_stk E _ (spZ regs) regs2 regs (EA 22%bv 22%nat eq_refl ltac:(cawb_acs))
      (EA 21%bv 21%nat eq_refl ltac:(cawb_acs)) (EA 20%bv 20%nat eq_refl ltac:(cawb_acs))
      (EA 19%bv 19%nat eq_refl ltac:(cawb_acs)) (EA 18%bv 18%nat eq_refl ltac:(cawb_acs))
      (EA 9%bv 9%nat eq_refl ltac:(cawb_acs)) (EA 8%bv 8%nat eq_refl ltac:(cawb_acs)) E1 HC0).
- rewrite (KP 9%bv ltac:(cawb_acs)), R9. exact E11.
- rewrite (KP 8%bv ltac:(cawb_acs)), R8. exact E12.
- rewrite (KP 21%bv ltac:(cawb_acs)), R21. exact E49.
- intros a Ha.
  destruct (al_blocks _ _ LAWS lyc Sc W (unpoison U (ms_mem ms0)) _ want nw (proj1 HARU) Hinw)
    as (_ & Hw4096 & Hwc & _).
  rewrite <- (cawb_aview_unp ly2 S2 U W2 mem2 md2 want nw a HARU2 Hinw2 Ha).
  replace a with (want + (a - want)) by lia.
  rewrite (K2 want nw (a - want) Hinw ltac:(lia) ltac:(cbv beta; lia)).
  replace (want + (a - want)) with a by lia.
  rewrite (cawb_aview_unp lyc Sc U W (ms_mem ms0) _ want nw a HARU Hinw Ha).
  apply (aview_at tfibsegs). apply HF. rewrite (wz a ltac:(lia)). intros (r & Hr & Hra).
  cbn [caa_xss ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi caw_stk] in Hra. rewrite E2a in Hra. lia.
Qed.

(* ---- one more step of the invariant: a later machine state whose callee-saved registers and frame are kept ---- *)
Lemma cawb_inv_step : forall regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc regs' mem' mdc',
  cawb_inv regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc ->
  @ajournal rc SK tfibsegs B STK_check_as_written (spZ regs0) [] ly0 S0 W0 (unpoison U mem0) md0 []
    ly S W (unpoison U mem') mdc' 3 ->
  ARU tfibsegs B ly S U W mem' mdc' ->
  (forall r : bv 5, bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 18 \/
     23 <= bv_unsigned r <= 27 -> getr regs' r = getr regs r) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs (cawb_extra regs0)) (mrestrict (w_H W) mem') (spZ regs0 - 64)) cawb_cs ->
  cawb_inv regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs' mem' mdc'.
Proof.
intros regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc regs' mem' mdc' HI HJ' HARU' HR Hcs'.
destruct HI as (_ & _ & HP & Hf & R18 & Rsp & R3 & R4 & R21 & _).
split; [exact HJ'|]. split; [exact HARU'|]. split; [exact HP|]. split; [exact Hf|].
split; [rewrite (HR 18%bv ltac:(right; right; right; left; reflexivity)); exact R18|].
split; [unfold spZ at 1; rewrite (HR 2%bv ltac:(left; reflexivity)); exact Rsp|].
split; [rewrite (HR 3%bv ltac:(right; left; reflexivity)); exact R3|].
split; [rewrite (HR 4%bv ltac:(right; right; left; reflexivity)); exact R4|].
split; [intros r Hr; rewrite (HR r ltac:(right; right; right; right; exact Hr)); exact (R21 r Hr)|].
exact (cawb_cs_Ereg regs regs' _ _ _ Hcs').
Qed.

(* the frame chunks off a resumed state whose first region is fstk_ret 64 cawb_cs *)
Lemma cawb_ret_chunks : forall E ss ms (H : word -> bool) b,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) 0 = Some (fstk_ret 64 cawb_cs) ->
  bv_unsigned (ew E 2) = b ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H (ms_mem ms)) b) cawb_cs.
Proof.
intros E ss ms H b HS Hm E2.
pose proof (fsw_region_nth E ss (restrict H ms) 0 _ HS Hm) as HR.
cbn [ms_mem restrict] in HR. destruct HR as (_ & _ & _ & Hcs).
unfold fstk_ret in Hcs. cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite E2 in Hcs. exact Hcs.
Qed.

(* the registers 2, 3, 4, 18, 21 .. 27 of a state the run left as their own atoms *)
Ltac cawb_selfregs HS ms W :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cawb_reg_cases Hr ltac:(
    lazymatch goal with |- getr _ ?q = _ =>
      rewrite (cawb_reg_self _ _ (w_H W) ms q HS ltac:(vm_compute; reflexivity)) end;
    apply ew_Ereg_reg).

(* ---- 0x81a7c .. 0x81a88 on the refused answer (s1 = NULL, s5 = SIZE_MAX): `beqz s1` to 0x81aa8 ---- *)
Lemma cawb_br_R : forall regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc,
  cawb_inv regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc ->
  getr regs 9 = w64 0 -> getr regs 21 = w64 SIZE_MAXZ ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81a7c) mem (seg_rom tfibsegs)) mdc)
    (cawb_mid 0x81aa8 regs0 ly0 S0 U W0 mem0 md0 want nw).
Proof.
intros regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc HI H9 H21.
pose proof HI as (HJ & HARU & _ & _ & _ & Hsp & _ & _ & _ & Hcs).
assert (FS : STK_check_as_written = 16448) by reflexivity.
pose proof (cawb_ret_st STK_check_as_written (spZ regs0) ly0 S0 W0 (unpoison U mem0) md0 ly S U W regs mem mdc 3
  (cawb_extra regs0) 0x81a7c HJ HARU ltac:(lia) Hsp Hcs) as HS0.
assert (HS : st_ok tfibsegs (Ereg regs (cawb_extra regs0)) cawb_ssR
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81a7c) mem (seg_rom tfibsegs))))
  by exact (st_ok_pin_reg' tfibsegs _ _ _ 21%bv 18446744073709551615
              (st_ok_pin_reg' tfibsegs _ _ _ 9%bv 0 HS0 H9 eq_refl) H21 eq_refl).
assert (E2 : bv_unsigned (ew (Ereg regs (cawb_extra regs0)) 2) = spZ regs0 - 64)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
clear HS0.
fsw_aj_run_toU caw_tbl_ok HS HJ HARU 0x81aa8.
{ unfold cawb_ssR. cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64);
    [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
apply SRr_ret.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms. rewrite Hms.
apply (cawb_mid_of_inv 0x81aa8 regs0 ly0 S0 U W0 mem0 md0 want nw ly S W (ms_regs ms) (ms_mem ms) _).
- apply (cawb_inv_step regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc _ _ _ HI HJ HARU).
  + cawb_selfregs HS ms W.
  + exact (cawb_ret_chunks _ _ ms (w_H W) _ HS ltac:(vm_compute; reflexivity) E2).
- intros Hx. exfalso. lia.
Qed.

(* ---- 0x81a7c .. 0x81a90 on the empty answer (s0 = s5 = 0, s1 a body): `beqz s0` to 0x81aa8 ---- *)
Lemma cawb_br_A0 : forall regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc bd,
  cawb_inv regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc ->
  getr regs 9 = w64 bd -> 4096 <= bd <= CAW_CEIL -> getr regs 8 = w64 0 -> getr regs 21 = w64 0 ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81a7c) mem (seg_rom tfibsegs)) mdc)
    (cawb_mid 0x81aa8 regs0 ly0 S0 U W0 mem0 md0 want nw).
Proof.
intros regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc bd HI H9 Hbd H8 H21.
pose proof HI as (HJ & HARU & _ & _ & _ & Hsp & _ & _ & _ & Hcs).
assert (FS : STK_check_as_written = 16448) by reflexivity.
pose proof (cawb_ret_st STK_check_as_written (spZ regs0) ly0 S0 W0 (unpoison U mem0) md0 ly S U W regs mem mdc 3
  (cawb_extra regs0) 0x81a7c HJ HARU ltac:(lia) Hsp Hcs) as HS0.
assert (E9 : ew (Ereg regs (cawb_extra regs0)) 9 = Z_to_bv 64 bd)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (HS : st_ok tfibsegs (Ereg regs (cawb_extra regs0)) cawb_ssA0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81a7c) mem (seg_rom tfibsegs))))
  by exact (cawb_add_atom _ _ _ 9%nat (mkAF 4096 CAW_CEIL 0)
              (st_ok_pin_reg' tfibsegs _ _ _ 21%bv 0 (st_ok_pin_reg' tfibsegs _ _ _ 8%bv 0 HS0 H8 eq_refl) H21 eq_refl)
              (cawb_afact _ 9 bd 4096 CAW_CEIL E9 ltac:(unfold CAW_CEIL in Hbd; lia) Hbd)).
assert (E2 : bv_unsigned (ew (Ereg regs (cawb_extra regs0)) 2) = spZ regs0 - 64)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
clear HS0.
fsw_aj_run_toU caw_tbl_ok HS HJ HARU 0x81aa8.
{ unfold cawb_ssA0. cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64);
    [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
apply SRr_ret.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms. rewrite Hms.
apply (cawb_mid_of_inv 0x81aa8 regs0 ly0 S0 U W0 mem0 md0 want nw ly S W (ms_regs ms) (ms_mem ms) _).
- apply (cawb_inv_step regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc _ _ _ HI HJ HARU).
  + cawb_selfregs HS ms W.
  + exact (cawb_ret_chunks _ _ ms (w_H W) _ HS ltac:(vm_compute; reflexivity) E2).
- intros Hx. exfalso. lia.
Qed.

(* ---- byte facts for bcmp ---- *)
Lemma cawb_aview_some : forall (H : word -> bool) m a, apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. cbv [aview mbyte mrestrict]. rewrite Hh, Hb. discriminate. Qed.

Lemma cawb_bytes_kept : forall (W W' : world tfibsegs) m m' p l,
  caw_bytes W m p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  caw_bytes W' m' p l.
Proof.
intros W W' m m' p l H Hk i Hi k Hk1.
rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W') m m').
- exact (H i Hi k Hk1).
- assert (k = 0)%nat by lia. subst k. apply Hk. lia.
Qed.

Lemma cawb_bytes_of_garr8 : forall (W : world tfibsegs) m p l,
  garr8 tfibsegs (mrestrict (w_H W) m) p l -> caw_bytes W m p l.
Proof. intros W m p l H i Hi. exact (proj1 (H i Hi)). Qed.

Lemma cawb_bytes_eq : forall (W : world tfibsegs) m p q l,
  caw_bytes W m p l -> caw_bytes W m q l ->
  forall i, 0 <= i < Z.of_nat (length l) -> aview tfibsegs (w_H W) m (p + i) = aview tfibsegs (w_H W) m (q + i).
Proof.
intros W m p q l Hp Hq i Hi.
pose proof (Hp (Z.to_nat i) ltac:(lia) 0%nat ltac:(lia)) as A.
pose proof (Hq (Z.to_nat i) ltac:(lia) 0%nat ltac:(lia)) as Bq.
rewrite Z2Nat.id in A, Bq by lia. cbn [Z.of_nat] in A, Bq. rewrite Z.add_0_r in A, Bq.
unfold aview. rewrite A, Bq. reflexivity.
Qed.

(* the bytes of a live block whose base is no head of U are addressable on the machine's memory (the twin of
   FSW_rd.fsw_block_body_addressable for a block with no head: want, from the raw __wrap_malloc) *)
Lemma cawb_block_addressable : forall ly S U (W : world tfibsegs) mem md P n z len,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (P, n) (ablocks B ly S) -> (forall r, In r U -> fst r <> P) -> P <= z -> 0 <= len -> z + len <= P + req_size n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF z len.
Proof.
intros ly S U W mem md P n z len HARU FH Hin HnoP Hz Hl Hn.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (YCbq.range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P n z len HAR Hin Hz Hn) as HRA.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P n HAR Hin) as (HP16 & HP4096 & HPc & _ & _ & PW & _).
pose proof asan_consts as (C1 & _).
intros x Hx. destruct (HRA x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (NI : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
{ rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply fsw_head_ush_out; [lia|]. intros (h & q) Hr. cbn [fst snd].
  destruct (FH (h, q) Hr) as (E16 & m & Hm & M16). cbn [fst snd] in E16, Hm. subst q.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m HAR Hm) as (Hh16 & _).
  split; [reflexivity|].
  split; [apply Z.mod_divide in Hh16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((k * 2) * 8) by lia; apply Z_mod_mult|].
  destruct (Z.eq_dec h P) as [->|NE]; [exfalso; exact (HnoP (P, 16) Hr eq_refl)|].
  assert (I1 : In (h, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
    by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (h, m)); exact Hm).
  assert (I2 : In (P, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
    by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (P, n)); exact Hin).
  destruct (FSupoisonU.pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E; injection E; intros _ E'; exact (NE E')))
    as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ NI). exact Es.
Qed.

(* the shadow hull of a sub-range of a live block is visible on the machine's memory *)
Lemma cawb_block_hull : forall ly S U (W : world tfibsegs) mem md P n z len,
  ARU tfibsegs B ly S U W mem md -> In (P, n) (ablocks B ly S) -> P <= z -> z + len <= P + req_size n -> 0 < len ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) z len.
Proof.
intros ly S U W mem md P n z len HARU Hin Hz Hzl Hl s Hs.
pose proof HARU as (HAR & _ & PO).
destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md P n HAR Hin) as [_ Hh].
exact (aview_unpoison_vis U W mem s PO (shadow_hull_vis_sub _ P (req_size n) z len Hh Hz Hzl Hl s Hs)).
Qed.

(* ---- 0x81a7c .. 0x81aa0 on a non-empty answer (s0 = s5 = l >= 1, s1 = bd a reader block's body), the bcmp
   0x81aa0 (FsRt.fr_bcmp: equal bytes, so a0 = 0) to the return 0x81aa4 ---- *)
Lemma cawb_br_A1 : forall regs0 ly0 S0 U W0 mem0 md0 ch want nw ly S W regs mem mdc bd l bs m,
  fpreU tfibsegs B STK_check_as_written ly0 S0 U W0 regs0 mem0 md0 ch -> fs_heads B ly0 S0 U ->
  cawb_inv regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc ->
  getr regs 9 = w64 bd -> getr regs 8 = w64 l -> getr regs 21 = w64 l ->
  l = Z.of_nat (length bs) -> 1 <= l -> l <= nw -> nw <= 2359299 ->
  src_rd tfibsegs W0 mem0 bd bs -> fs_rblock tfibsegs B ly0 S0 W0 mem0 bd m -> l <= m ->
  caw_bytes W mem want bs ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81a7c) mem (seg_rom tfibsegs)) mdc)
    (cawb_mid 0x81aa4 regs0 ly0 S0 U W0 mem0 md0 want nw).
Proof.
intros regs0 ly0 S0 U W0 mem0 md0 ch want nw ly S W regs mem mdc bd l bs m
  HPRE FH0 HI H9 H8 H21 El Hl1 Hlw Hnw Hsrc Hrb Hlm HWB.
pose proof HI as (HJ & HARU & HP & Hfw & R18 & Hsp & R3 & R4 & R21 & Hcs).
pose proof HPRE as (HAPU & _). pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk0 & _ & _ & _).
pose proof (fsw_sp B STK_check_as_written ly0 S0 U W0 regs0 mem0 md0 ch HAPU) as (Hal16 & Hceil & H47 & HSP0).
pose proof (fsw_ARU B STK_check_as_written ly0 S0 U W0 regs0 mem0 md0 ch HAPU) as HARU0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_check_as_written = 16448) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
(* the two blocks bcmp reads: bd's reader block (entry and now) and want *)
pose proof Hrb as (Hrin & Hbd16 & Hm0 & _).
unfold HEAD in Hrin.
assert (Hrin2 : In (bd - 16, m + 16) (ablocks B ly S))
  by (eapply Permutation_in; [apply Permutation_sym; exact HP | right; exact Hrin]).
assert (Hinw : In (want, nw) (ablocks B ly S))
  by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
assert (Hreqm : req_size (m + 16) = m + 16)
  by (unfold req_size; destruct (Z.eqb_spec (m + 16) 0); [lia | reflexivity]).
assert (Hreqw : req_size nw = nw) by (unfold req_size; destruct (Z.eqb_spec nw 0); [lia | reflexivity]).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) mdc (bd - 16) (m + 16) (proj1 HARU) Hrin2)
  as (_ & Hb4096 & Hbc & _). rewrite Hreqm in Hbc.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) mdc want nw (proj1 HARU) Hinw)
  as (_ & Hw4096 & Hwc & _). rewrite Hreqw in Hwc.
assert (FH : fs_heads B ly S U).
{ intros r Hr. destruct (FH0 r Hr) as (E16 & m' & Hm' & M16). split; [exact E16|]. exists m'. split; [|exact M16].
  eapply Permutation_in; [apply Permutation_sym; exact HP | right; exact Hm']. }
assert (HnoW : forall r, In r U -> fst r <> want).
{ intros r Hr Ew. destruct (FH0 r Hr) as (_ & m' & Hm' & _). rewrite Ew in Hm'. exact (Hfw m' Hm'). }
(* the state at 0x81a7c deciding the branches *)
pose proof (cawb_ret_st STK_check_as_written (spZ regs0) ly0 S0 W0 (unpoison U mem0) md0 ly S U W regs mem mdc 3
  (cawb_extra regs0) 0x81a7c HJ HARU ltac:(lia) Hsp Hcs) as HS0.
assert (E9 : ew (Ereg regs (cawb_extra regs0)) 9 = Z_to_bv 64 bd)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E8 : ew (Ereg regs (cawb_extra regs0)) 8 = Z_to_bv 64 l)
  by (rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact H8).
assert (H21' : getr regs 21 = sv_denot (Ereg regs (cawb_extra regs0)) (SOff 8 0))
  by (rewrite fsw_SOff0, E8; exact H21).
assert (HS : st_ok tfibsegs (Ereg regs (cawb_extra regs0)) cawb_ssA1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81a7c) mem (seg_rom tfibsegs)))).
{ exact (cawb_add_atom _ _ _ 8%nat (mkAF 1 3145728 0)
    (cawb_add_atom _ _ _ 9%nat (mkAF 4096 CAW_CEIL 0)
       (st_ok_set_reg tfibsegs _ _ _ 21%bv (SOff 8 0) HS0
          ltac:(intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc) H21')
       (cawb_afact _ 9 bd 4096 CAW_CEIL E9 ltac:(lia) ltac:(unfold CAW_CEIL; lia)))
    (cawb_afact _ 8 l 1 3145728 E8 ltac:(lia) ltac:(lia))). }
assert (E2 : bv_unsigned (ew (Ereg regs (cawb_extra regs0)) 2) = spZ regs0 - 64)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
clear HS0.
fsw_aj_run_toU caw_tbl_ok HS HJ HARU 0x81aa8.
{ unfold cawb_ssA1. cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -64);
    [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
(* ---- at __wrap_bcmp: ra = 0x81aa4, a0 = bd, a1 = want, a2 = l ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms.
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x81aa4 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (cawb_reg_atom _ _ (w_H W) ms 10%bv 9 HS ltac:(vm_compute; reflexivity)) as R10.
pose proof (cawb_reg_atom _ _ (w_H W) ms 11%bv 18 HS ltac:(vm_compute; reflexivity)) as R11.
pose proof (cawb_reg_atom _ _ (w_H W) ms 12%bv 8 HS ltac:(vm_compute; reflexivity)) as R12.
rewrite E9 in R10. rewrite E8 in R12. rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), R18 in R11.
assert (RS : forall r : bv 5, bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 18 \/
  23 <= bv_unsigned r <= 27 -> getr (ms_regs ms) r = getr regs r) by (cawb_selfregs HS ms W).
assert (spB : spZ (ms_regs ms) = spZ regs0 + -64)
  by (unfold spZ at 1; rewrite (RS 2%bv ltac:(left; reflexivity)); fold (spZ regs); lia).
pose proof (cawb_ret_chunks _ _ ms (w_H W) _ HS ltac:(vm_compute; reflexivity) E2) as HCm.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
(* want's bytes, kept by the run (they lie outside the frame window) *)
assert (HWBm : caw_bytes W (ms_mem ms) want bs).
{ apply (cawb_bytes_kept W W mem (ms_mem ms) want bs HWB). intros a Ha.
  apply (aview_at tfibsegs). apply HF. rewrite (wz a ltac:(lia)). intros (r & Hr & Hra).
  cbn [cawb_ssA1 ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi fstk_ret] in Hra. rewrite E2 in Hra. lia. }
(* bd's bytes: the entry's (src_rd), kept by the journal (an entry block, live now, off FP = []) *)
assert (HBDm : caw_bytes W (ms_mem ms) bd bs).
{ apply (cawb_bytes_kept W0 W mem0 (ms_mem ms) bd bs (cawb_bytes_of_garr8 W0 mem0 bd bs (proj1 Hsrc))).
  intros a Ha.
  rewrite <- (cawb_aview_unp ly S U W (ms_mem ms) _ (bd - 16) (m + 16) a HARU Hrin2 ltac:(rewrite Hreqm; lia)).
  rewrite <- (cawb_aview_unp ly0 S0 U W0 mem0 md0 (bd - 16) (m + 16) a HARU0 Hrin ltac:(rewrite Hreqm; lia)).
  replace a with ((bd - 16) + (a - (bd - 16))) by lia.
  apply (F2 (bd - 16) (m + 16)); [exact Hrin | exact Hrin2 | rewrite Hreqm; lia | apply inFP_nil]. }
assert (Hraok : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity).
pose proof (fsw_ecall_preU_k_at B STK_check_as_written (spZ regs0) [] ly0 S0 W0 (unpoison U mem0) md0 [] ly S U W
  (ms_mem ms) _ 3 (ms_regs ms) (-64) 8192 HJ HARU spB eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hraok
  ltac:(rewrite (RS 3%bv ltac:(right; left; reflexivity)), R3; exact Hgp)
  ltac:(rewrite (RS 4%bv ltac:(right; right; left; reflexivity)), R4; exact Htp)) as (HEC & HLO & HPR).
rewrite Hms. change (Z_to_bv 64 272088) with (w64 PC_bcmp).
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_check_as_written (spZ regs0) [] ly0 S0 W0 (unpoison U mem0) md0 [] ly S U W (ms_mem ms)
    _ 3 U (fun a => spZ (ms_regs ms) - 2 * ESTACK <= a < spZ (ms_regs ms)) (Z_to_bv 64 0x81aa4)
    (cfg_at tfibsegs PC_bcmp (ms_regs ms) (ms_mem ms) _)
    (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\ getr regs' 10 = w64 0 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms) - 2 * ESTACK <= a < spZ (ms_regs ms)) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a)) HJ).
  - eapply SRr_mono.
    + apply (RTb ly S U W (ms_regs ms) (ms_mem ms) _ bd want l HEC HLO HPR R10 R11 R12).
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * intros a Ha. split; [|lia].
        rewrite <- (cawb_aview_unp ly S U W (ms_mem ms) _ (bd - 16) (m + 16) a HARU Hrin2 ltac:(rewrite Hreqm; lia)).
        destruct (al_blocks _ _ LAWS ly S W (unpoison U (ms_mem ms)) _ (bd - 16) (m + 16) (proj1 HARU) Hrin2)
          as (_ & _ & _ & _ & Hpr & _).
        apply cawb_aview_some. apply (proj1 (Hpr a ltac:(rewrite Hreqm; lia))).
      * intros a Ha. split; [|lia].
        rewrite <- (cawb_aview_unp ly S U W (ms_mem ms) _ want nw a HARU Hinw ltac:(rewrite Hreqw; lia)).
        destruct (al_blocks _ _ LAWS ly S W (unpoison U (ms_mem ms)) _ want nw (proj1 HARU) Hinw)
          as (_ & _ & _ & _ & Hpr & _).
        apply cawb_aview_some. apply (proj1 (Hpr a ltac:(rewrite Hreqw; lia))).
      * intros a Ha. lia.
      * intros a Ha. lia.
      * exact (amem_range_of_block tfibsegs B LAWS ly S W (unpoison U (ms_mem ms)) _ (bd - 16) (m + 16) bd l
          (proj1 HARU) Hrin2 ltac:(lia) ltac:(rewrite Hreqm; lia)).
      * exact (amem_range_of_block tfibsegs B LAWS ly S W (unpoison U (ms_mem ms)) _ want nw want l
          (proj1 HARU) Hinw ltac:(lia) ltac:(rewrite Hreqw; lia)).
      * exact (fsw_block_body_addressable B ly S U W (ms_mem ms) _ (bd - 16) (m + 16) bd l HARU FH Hrin2
          ltac:(lia) ltac:(lia) ltac:(rewrite Hreqm; lia)).
      * intros _. exact (cawb_block_hull ly S U W (ms_mem ms) _ (bd - 16) (m + 16) bd l HARU Hrin2
          ltac:(lia) ltac:(rewrite Hreqm; lia) ltac:(lia)).
      * exact (cawb_block_addressable ly S U W (ms_mem ms) _ want nw want l HARU FH Hinw HnoW
          ltac:(lia) ltac:(lia) ltac:(rewrite Hreqw; lia)).
      * intros _. exact (cawb_block_hull ly S U W (ms_mem ms) _ want nw want l HARU Hinw
          ltac:(lia) ltac:(rewrite Hreqw; lia) ltac:(lia)).
    + cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & -> & HARU' & HP' & Hsame & Hv & Hiff & Hfr' & Hgr').
      split; [reflexivity|]. exists regs', mem', md'.
      split; [unfold cfg_at, w64, raZ; rewrite R1, unsigned_lit_small by lia; reflexivity|].
      split; [exact HARU'|]. split; [exact Hsame|].
      split.
      { intros a Ha HW. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
        - apply (aview_unpoison_in tfibsegs). exact Eu.
        - rewrite !(aview_unpoison_out tfibsegs _ U _ a Eu). exact (Hfr' a Ha HW). }
      split.
      { intros a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in Hb |- *.
        destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [exists (Z_to_bv 8 0); reflexivity|].
        apply Hgr'. split; [exact Hh | exists b; exact Hb]. }
      split; [exact HP'|]. split; [|exact Hfr'].
      rewrite Hv. apply Hiff. intros i Hi. apply (cawb_bytes_eq W (ms_mem ms) bd want bs HBDm HWBm). lia.
  - intros a Ha. cbv beta in Ha. left. left. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & H10 & Hfr2).
apply SRr_ret.
apply (cawb_mid_of_inv 0x81aa4 regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs2 mem2 md2).
- apply (cawb_inv_step regs0 ly0 S0 U W0 mem0 md0 want nw ly S W regs mem mdc _ _ _ HI HJ2 HARU2).
  + intros r Hr. rewrite (fsw_pres (ms_regs ms) regs2 r HP2 ltac:(unfold acallee_saved; lia)). exact (RS r Hr).
  + apply (cawb_cs_kept _ (mrestrict (w_H W) (ms_mem ms))); [|exact HCm].
    intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr2; lia.
- intros _. exact H10.
Qed.

(* ---- THE BACK HALF up to the epilogue: from the hand-over state at 0x81a78 (every arm of the walk reaches it, in
   FSW_caw_accept.v's caa_xss) through free (six), the branches and bcmp, to cawb_mid at 0x81aa4 (bcmp answered 0)
   or 0x81aa8 (the refused and the empty answer). The premises are check_as_written_spec's and what the walk before
   0x81a78 gives: the entry convention of the atoms, the journal at two events, the two blocks, and the decoder's
   answer in s5 (atom 49) with want holding the decoded bytes. ---- *)
Theorem cawb_to_mid : forall ly S U W0 regs mem md ch bd l (tb : list Z) E ms mdc lyc Sc W six want n,
  fpreU tfibsegs B STK_check_as_written ly S U W0 regs mem md ch -> fs_heads B ly S U ->
  getr regs 11 = w64 bd -> getr regs 12 = w64 l -> Z.of_nat (length tb) <= PRESET_FILE_MAX_BYTES ->
  caw_answerA tfibsegs B ly S U W0 mem tb bd l ->
  st_nev S + EV_check_as_written <= EV_MAX ->
  st_ok tfibsegs E caa_xss (restrict (w_H W) ms) ->
  ew E 1 = getr regs 1 ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> ew E (Z.to_nat (bv_unsigned r)) = getr regs r) ->
  ew E 11 = getr regs 11 -> ew E 12 = getr regs 12 ->
  ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want -> ew E 49 = Z_to_bv 64 n ->
  @ajournal rc SK tfibsegs B STK_check_as_written (spZ regs) [] ly S W0 (unpoison U mem) md [] lyc Sc W
    (unpoison U (ms_mem ms)) mdc 2 ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ablocks B lyc Sc = (ablocks B ly S ++ [(want, b64_alloc_bound (Z.of_nat (length tb)))]) ++
    [(six, Z.max (Z.of_nat (length tb)) 1)] ->
  (forall m, ~ In (want, m) (ablocks B ly S)) -> (forall m, ~ In (six, m) (ablocks B ly S)) ->
  (WriterSpec.b64_dec tb = None -> n = SIZE_MAXZ) ->
  (forall bs, WriterSpec.b64_dec tb = Some bs ->
     n = Z.of_nat (length bs) /\ n <= b64_alloc_bound (Z.of_nat (length tb)) /\ caw_bytes W (ms_mem ms) want bs) ->
  SRr tfibsegs W (mkCfg ms mdc) (fun W' c' => exists pc, (pc = 0x81aa4 \/ pc = 0x81aa8) /\
    cawb_mid pc regs ly S U W0 mem md want (b64_alloc_bound (Z.of_nat (length tb))) W' c').
Proof.
intros ly S U W0 regs mem md ch bd l tb E ms mdc lyc Sc W six want n
  HPRE FH H11 H12 Htb HANS Hev HS E1 ECS E11 E12 E33 E34 E49 HJ HARU Hab Hfw Hfs Hnone Hsome.
pose proof HPRE as (HAPU & _). pose proof HAPU as (HAP & _ & _). pose proof HAP as (HAR0 & _).
pose proof asan_consts as (C1 & _).
set (nw := b64_alloc_bound (Z.of_nat (length tb))) in *.
assert (Hnw : 3 <= nw <= 2359299)
  by (subst nw; unfold b64_alloc_bound, PRESET_FILE_MAX_BYTES in *; Z.div_mod_to_equations; lia).
eapply SRr_bind.
{ exact (cawb_free6 ly S U W0 regs mem md ch bd l tb E ms mdc lyc Sc W six want n nw _ HPRE FH H12 HANS Hev HS E1
    ECS E11 E12 E33 E34 E49 HJ HARU Hab Hfw Hfs). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HI & R9 & R8 & R21 & Hwb).
rewrite H11 in R9. rewrite H12 in R8.
destruct HANS as [(Hdec & -> & ->) | (bs & m & Hdec & Hbd & El & Hsrc & Hrb & Hlm & _)].
- specialize (Hnone Hdec). subst n.
  eapply SRr_mono; [exact (cawb_br_R regs ly S U W0 mem md want nw ly2 S2 W2 regs2 mem2 md2 HI R9 R21)|].
  intros W' c' _ HM. exists 0x81aa8. split; [right; reflexivity | exact HM].
- destruct (Hsome bs Hdec) as (En & Hnb & HWB).
  assert (Enl : n = l) by lia. rewrite Enl in R21, Hnb.
  pose proof Hrb as (Hrin & _ & Hm0 & _). unfold HEAD in Hrin.
  destruct (al_blocks _ _ LAWS ly S W0 (unpoison U mem) md (bd - 16) (m + 16) HAR0 Hrin) as (_ & Hb4096 & Hbc & _).
  assert (Hreqm : req_size (m + 16) = m + 16)
    by (unfold req_size; destruct (Z.eqb_spec (m + 16) 0); [lia | reflexivity]).
  rewrite Hreqm in Hbc.
  destruct (Z.eq_dec l 0) as [El0 | Hl0].
  + rewrite El0 in R8, R21.
    eapply SRr_mono; [exact (cawb_br_A0 regs ly S U W0 mem md want nw ly2 S2 W2 regs2 mem2 md2 bd HI R9
      ltac:(unfold CAW_CEIL; lia) R8 R21)|].
    intros W' c' _ HM. exists 0x81aa8. split; [right; reflexivity | exact HM].
  + eapply SRr_mono.
    { apply (cawb_br_A1 regs ly S U W0 mem md ch want nw ly2 S2 W2 regs2 mem2 md2 bd l bs m HPRE FH HI R9 R8 R21 El
        ltac:(lia) Hnb ltac:(lia) Hsrc Hrb Hlm).
      apply (cawb_bytes_kept W W2 (ms_mem ms) mem2 want bs HWB). intros a Ha. apply Hwb.
      assert (req_size nw = nw) by (unfold req_size; destruct (Z.eqb_spec nw 0); lia). lia. }
    intros W' c' _ HM. exists 0x81aa4. split; [left; reflexivity | exact HM].
Qed.

End W.
