(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 1279 of its 1357 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_K.v from a working branch
   60d0985773d, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_K.v; 95 of its 117 lines of code are new or changed and 1335 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_defs.v (a working branch
   83638d8ab68), the same names over B's own code. Every B literal below is from B's listing (capstone over the unstripped
   twin of fs.asan-ubsan, sha256 b1566a1c..., whose bytes 0x8164c .. 0x81b5c equal the pinned image's, sha256
   5ac5ce0954f8...) or from B's generated constants (lib/B/YB1w.v tfib_A_check_as_written / tfib_E_check_as_written,
   lib/B/FSH_Base.v A_check_as_written, FRAME_check_as_written = 64).
   rule 24: proves no function (kind: segment lemma; check_as_written, B 0x8164c, CONFIRM by a Theorem Labs lane). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_caw_defs.v, with its numbers changed; 85 of its 129 lines of code are new or changed and 73 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_tail.v (a working branch),
   the same names over B's own code (B listing: capstone over the unstripped twin of fs.asan-ubsan, sha256 b1566a1c...).
   rule 24: proves no function (kind: segment lemma; check_as_written, B 0x8164c, CONFIRM by a Theorem Labs lane). *)
(* check_as_written over fs.asan-ubsan, the tail of the inlined expected_body (fs.c:91-93, `r = m % 4; if ( *text ||
   pad > 2 || r == 1 || (r == 2 && (six[m-1] & 15)) || (r == 3 && (six[m-1] & 3))) n = SIZE_MAX;`), B 0x81804 ..
   0x818ac / 0x81a78: from the scan loop's NUL exit the walk either refuses (n = SIZE_MAX, pc 0x81a78, the
   `jal __wrap_free` of six) or accepts and enters the emit loop (pc 0x818ac), or accepts with m = 0 and goes straight
   to 0x81a78 with n = 0. This is `WriterSpec.b64_dec`'s `(pad <=? 2) && six_tail_ok six` (lib/Prog/WriterSpec.v).
   B's code reaches 0x81804 only at the NUL: a refused character leaves the scan straight for 0x81a78
   (FSW_caw_scan.v caw_ssB), so B has no `*text` test here and no text byte in the state.
   This file: the state at 0x81804 (cawt_ss), the pad refusal (cawt_refuse_pad: 0x81804 `slti a1, t3, 3; xori a1, a1,
   1`, 0x81818 `addi s5, zero, -1`, 0x8181c `bnez a1` to 0x81a78), its exit state cawt_ss_free (MEASURED: the engine's
   state after that run), and two helpers of FSW_caw_accept.v. The other arms are FSW_caw_accept.v's.
   Section hypotheses: none (this segment calls nothing; it only runs instrumented program code). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K
FSW_caw_defs FSW_caw_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the symbolic state at 0x81804 (the scan loop's NUL exit) ----
   atoms: 30 ~six, 31 RA (FSW_caw_defs.v caw_regs1: ra is an atom; no segment reads it), 33 six, 34 want, 35 the text
   pointer at the NUL, 38 m, 39 pad, 40 six + m (alias), 43 six[m - 1], 50-61 scratch (t0 t1 t2 a1 a2 a5 a6 a7 t4 t5
   t6 s5: the tail sets s5 before it reads it) *)
Definition cawt_regs : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-64); SOff 3 0; SOff 4 0;
   SOff 50 0; SOff 51 0; SOff 52 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SOff 53 0; SOff 54 0; SOff 30 0; SOff 38 0;
   SOff 55 0; SOff 56 0; SOff 57 0;
   SOff 34 0; SOff 35 0; SOff 32 0;
   SOff 61 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 39 0; SOff 58 0; SOff 59 0; SOff 60 0].
(* the byte six[m - 1], read through `add a1, a0, a1` (a1 = m - 1) at 0x81844 / 0x81870 *)
Definition cawt_six : YP09.region :=
  YP09.mkRegion (Some 40%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 43 0))].
Definition cawt_facts (plo phi : Z) : facts :=
  mkFacts [(39%nat, mkAF plo phi 0);
           (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (30%nat, mkAF CAW_NLO CAW_NHI 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 CAW_CEIL 0);
           (34%nat, mkAF 4096 CAW_CEIL 0);
           (35%nat, mkAF 4096 CAW_CEIL 0);
           (38%nat, mkAF 0 3145728 0);
           (40%nat, mkAF 4096 CAW_CEIL 0);
           (43%nat, mkAF 0 63 0)]
          []
          [(SAlu ALU_ADD (SOff 33 0) (SOff 38 0), SOff 40 0)].
Definition cawt_ss (plo phi : Z) : sstate := mkSS 0x81804 cawt_regs [caw_stk] None (cawt_facts plo phi).
(* the arms read no memory but six[m - 1] (FSW_caw_accept.v caa_SH6): no shadow entry here *)
Definition cawt_SH : list shent := [].
Definition cawt_K : nat := Eval vm_compute in run_K 0 caw_Bx cawt_SH (cawt_ss 0 3145728).

(* the state at 0x81a78 (`jal __wrap_free` of six) on the pad refusal: a1 = 1 (pad > 2), s5 = SIZE_MAX
   (MEASURED: the engine's state after the run from 0x81804 with pad in [3, 3145728]) *)
Definition cawt_regs_free : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-64); SOff 3 0; SOff 4 0;
   SOff 50 0; SOff 51 0; SOff 52 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SLit 1; SOff 54 0; SOff 30 0; SOff 38 0;
   SOff 55 0; SOff 56 0; SOff 57 0;
   SOff 34 0; SOff 35 0; SOff 32 0;
   SLit CAW_M1; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 39 0; SOff 58 0; SOff 59 0; SOff 60 0].
Definition cawt_facts_free (plo phi : Z) : facts :=
  mkFacts ((39%nat, mkAF plo phi 0) :: f_atoms (cawt_facts 0 3145728))
          (f_conds (cawt_facts 0 3145728)) (f_alias (cawt_facts 0 3145728)).
Definition cawt_ss_free (plo phi : Z) : sstate :=
  mkSS 0x81a78 cawt_regs_free [caw_stk] None (cawt_facts_free plo phi).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable Q : world tfibsegs -> config -> Prop.

(* st_ok with one more atom fact (YP06 add_atom / facts_ok_add_atom) *)
Lemma cawt_add_atom : forall E ss ms n f,
  st_ok tfibsegs E ss ms -> afact_ok E n f ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
      (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms n f HS Hf. apply (st_ok_facts tfibsegs E ss ms); [exact HS|].
apply facts_ok_add_atom; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))) | exact Hf].
Qed.

(* `andi a1, a4, 3` is m mod 4 *)
Lemma cawt_and3 : forall E n m, ew E n = w64 m -> 0 <= m < 2 ^ 64 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 3)) = m mod 4.
Proof.
intros E n m Hn Hm. rewrite U_and_lit by lia. rewrite U_SOff, Hn, Z.add_0_r.
unfold w64. rewrite unsigned_lit_small by exact Hm. rewrite (zcanon_id m) by (unfold M64; lia).
replace 3 with (Z.ones 2) by reflexivity. rewrite Z.land_ones by lia. reflexivity.
Qed.

(* ---- the refusal arm: the scan reached the NUL but more than two '=' were read (plain check_as_written_c.v:25;
   b64_dec's `pad <=? 2` false) ---- *)
Lemma cawt_refuse_pad : forall E ms mdc (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world tfibsegs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout)
    (Sc : astate) (Up : list (Z * Z)) (W : world tfibsegs) (kj pad : Z),
  st_ok tfibsegs E (cawt_ss 0 3145728) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms)) mdc kj ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms) mdc ->
  ew E 39 = w64 pad -> 3 <= pad <= 3145728 ->
  bv_unsigned (ew E 2) = sp0 -> 64 <= STK ->
  (forall E' ms' mdc',
     (forall n, (n < 62)%nat -> ew E' n = ew E n) ->
     st_ok tfibsegs E' (cawt_ss_free 3 3145728) (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms')) mdc' kj ->
     ARU tfibsegs B lyc Sc Up W (ms_mem ms') mdc' ->
     (forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem ms' x = ms_mem ms x) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros E ms mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc Up W kj pad HS HJ HARU E39 Hpad Esp HSTK HCONT.
pose proof (cawt_add_atom E _ _ 39%nat (mkAF 3 3145728 0) HS
  ltac:(split; [rewrite E39; unfold w64; rewrite unsigned_lit_small by lia; cbn [af_lo af_hi]; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts cawt_ss cawt_facts f_atoms f_conds f_alias] in HS1.
clear HS.
assert (SHOK : sh_ok tfibsegs caw_Bx cawt_SH E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok, cawt_SH; constructor).
fsw_aj_run_to_tokU caw_tbl_ok HS1 HJ HARU SHOK caw_Bspan 0x81a78.
- (* the run writes only the frame window of check_as_written *)
  cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat).
  { reflexivity. }
  { exact Esp. }
  { cbn. lia. }
  { cbn. lia. }
  { apply awr_ok_nil. }
- apply (HCONT E ms0 (with_vm_backing (m_vm_lazy mdc) mat mdc)).
  + intros n Hn. reflexivity.
  + unfold cawt_ss_free, cawt_regs_free, cawt_facts_free, cawt_facts. exact HS1.
  + exact HJ.
  + exact HARU.
  + intros x Hx. apply HF. intros (rr & Hin & Hb). cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[]]. cbn [caw_stk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
    rewrite Esp in Hb. apply Hx. lia.
  + exact HG.
Qed.

End W.
