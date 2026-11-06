(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v, with its module paths and module names changed; 639 of its 687 lines of code are new or changed and 451 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_fuzz_free.v; 834 of its 931 lines of code are new or changed and 590 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_realloc_pn.v, with its module paths and module names changed; 22 of its 63 lines of code are new or changed and 890 lines of the source are left out. *)
(* fs ASan+UBSan (image B: fs.asan-ubsan), group ALLOC, a Theorem Labs lane: fuzz_realloc_spec (lib/B/FSH_Fn_alloc.v, B 0x82bc4,
   alloc.c:75-94) from its walk's pieces: lib/B/FSW_realloc.fsr_p0 (p = 0, the tail call to fuzz_malloc),
   lib/B/FSW_realloc_pn.fsr_pn0_fail (p <> 0, failing()), lib/B/FSW_realloc_pn.fsr_segAB (entry -> the realloc call point)
   and lib/B/FSW_realloc_segCD.fsr_segCD (the realloc call point -> arm (c), through the tail call into own).
   proves function fuzz_realloc (B 0x82bc4) (reuse search: proof-index on main@f4cc67298b7 / ossv/recipes@5121fb8693b
   / ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb, by address on those four refs, and on named
   lane branches / `proof-index fuzz_realloc`, `git grep -i -e <addr>`, `git grep -E '^(Theorem|Lemma)
   .*fuzz_realloc_spec'`; B 0x82bc4: 0 hits, CONFIRM).
   port-from: lib/A/FSW_realloc_pn.fsr_of_segs and lib/A/FSW_realloc_top.v (this lane, image A; B has one segment fewer:
   own() is out of line, so SEG-C and SEG-D are one segment, fsr_segCD). No rename. Relocated files: none.

   The callees are discharged by their proofs: fuzz_malloc_spec by a Theorem Labs lane's lib/B/FSW_fuzz_malloc
   .fuzz_malloc_holds, own_spec by lib/B/FSW_own.own_holds, the two ASan poison helpers by a Theorem Labs lane's lib/B/FSpoisonW
   .tfib_poison16 / tfib_unpoison16.

   NAMED SECTION HYPOTHESES (Print Assumptions shows them as the theorem's arguments):
   - IMG : fs_img_facts tfibsegs B, SHS : FsShadowSyms B, FS_ENV : api_env tfibsegs B, TB : TfibSyms B: facts of fs's
     TfibB; owner RELOC / the B start-up layer.
   - FS_AREALLOC_BU_H : FSupoisonRealloc.FS_AREALLOC_BU tfibsegs B (as_universe B), the any-U __wrap_realloc contract at
     B's 0x530e8; owner a Theorem Labs lane via a Theorem Labs lane.
   - FS_AMALLOC_AU : FSupoisonU.amalloc_realizesU tfibsegs B, the any-U __wrap_malloc contract (fuzz_malloc_holds' premise,
     the p = 0 arm); owner the shared runtime (a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YA0n YM05 YG00 YG0a YG01 YG0d YG0f YG0n YG0q YCbq YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_Gen FSpoisonS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YF0m FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSupoisonRealloc FSpoisonS FSpoisonW FSW_K FSW_realloc FSW_realloc_pn
FSW_realloc_segCD FSW_own FSW_fuzz_malloc.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis SHS : FsShadowSyms B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis FS_AREALLOC_BU_H : FS_AREALLOC_BU tfibsegs B (as_universe B).
Hypothesis FS_AMALLOC_AU : FSupoisonU.amalloc_realizesU tfibsegs B.

(* the three arms, given the two callees' specs and the unpoison contract *)
Lemma fsr_of_segs : aunpoison16_realizes tfibsegs B PC_unpoison -> @fuzz_malloc_spec fx rc SK tfibsegs B ->
  @own_spec fx rc SK tfibsegs B -> @fuzz_realloc_spec fx rc SK tfibsegs B.
Proof.
intros UPO MALLOC OWN.
unfold fuzz_realloc_spec.
intros ly S U W regs mem md ch p k n old live peak cnt fail HPRE FH H10 H11 Hn1 Hn2 HGL Hlv Hcn Hdata [Hev0 Hev3] Hbb.
destruct (Z.eq_dec p 0) as [Hp | Hp].
- subst p. destruct Hdata as [(_ & -> & ->) | (Hne & _)]; [|exfalso; exact (Hne eq_refl)].
  exact (fsr_p0 B MALLOC ly S U W regs mem md ch n live peak cnt fail HPRE FH H10 H11 Hn1 Hn2 HGL Hlv Hcn
    (Hev0 eq_refl) Hbb).
- destruct Hdata as [(Hz & _) | (_ & (U1 & U2 & EU) & HRB & Hlen & HZB & Hkl)]; [exfalso; exact (Hp Hz)|].
  destruct (Z.eq_dec cnt fail) as [Hcf | Hcf].
  + pose proof HPRE as ((HAN & _ & _) & _).
    pose proof HAN as (HAR & _).
    pose proof HRB as (Hblk & _ & Hk0 & _).
    destruct (al_blocks _ _ LAWS ly S W _ md (p - HEAD) (k + HEAD) HAR Hblk) as (_ & Hb4096 & Hbceil & _).
    assert (Hceil47 : alloc_ceiling < 2 ^ 47) by exact alloc_ceiling_lt.
    assert (Hrqk : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
    rewrite Hrqk in Hbceil.
    assert (Hpr : 0 < p < 2 ^ 64) by (clear - Hb4096 Hbceil Hceil47 Hk0; unfold HEAD in *; lia).
    exact (fsr_pn0_fail B IMG SHS ly S U W regs mem md ch p k n old live peak cnt fail HPRE FH H10 Hpr Hcf HGL Hcn).
  + assert (Hpre : fsr_pre_pn B ly S U W regs mem md ch p k n old live peak cnt fail U1 U2)
      by exact (conj HPRE (conj FH (conj H10 (conj H11 (conj Hn1 (conj Hn2 (conj HGL (conj (Hlv Hcf) (conj Hcn
        (conj Hcf (conj Hp (conj EU (conj HRB (conj Hlen (conj HZB (conj Hkl (conj (Hev3 Hp) (Hbb Hcf)))))))))))))))))).
    eapply SRr_bind.
    { exact (fsr_segAB B IMG SHS UPO ly S U W regs mem md ch p k n old live peak cnt fail U1 U2 Hpre). }
    intros W2 c2 _ H2.
    eapply SRr_mono.
    { exact (fsr_segCD B IMG SHS FS_ENV FS_AREALLOC_BU_H OWN ly S U W regs mem md ch p k n old live peak cnt fail U1 U2
        W2 c2 Hpre H2). }
    intros W' c' _ (res & Hpost).
    right. right. split; [exact Hcf|]. split; [exact Hp|]. exists U1, U2, res. split; [exact EU | exact Hpost].
Qed.

Theorem fuzz_realloc_holds : @fuzz_realloc_spec fx rc SK tfibsegs B.
Proof.
exact (fsr_of_segs (tfib_unpoison16 B LAWS TB)
  (@fuzz_malloc_holds fx rc SK B IMG SHS TB FS_ENV FS_AMALLOC_AU (tfib_poison16 B LAWS TB))
  (@own_holds fx rc SK B IMG SHS (tfib_poison16 B LAWS TB))).
Qed.
End t.
