(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_exit_ab: image B's LLVMFuzzerTestOneInput from +0xab8 (segX_exit_defs.v ex_ab8) to the
   join +0xae0 (llvm_b_st_ae0): free #2 of the upstream buffer (s7) and free #3 of the body copy (s11), each
   segX_exit_fr.v fr_free_at, then the re-poison stretch segX_exit_rp.v rp_ae0. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_segX_exit_defs
  LLVMFuzzerTestOneInput_segX_exit_fr LLVMFuzzerTestOneInput_segX_exit_rp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the
   plain ones (YM03.v:179-180 lf_lia_orig / lf_nia_orig). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Open Scope Z_scope.

Section ab. Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation base cx :=
  (@dec_b_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx).

(* What both frees carry: s7 = upb (free #2's argument) and s11 = res (free #3's). *)
Definition ab_R (res upb : Z) (r : bvmap 5 word) : Prop := YK11.getr r 23 = w64 upb /\ YK11.getr r 27 = w64 res.

Lemma ab_R_kept : forall res upb r r', ab_R res upb r -> aregs_preserved r r' -> ab_R res upb r'.
Proof.
intros res upb r r' [H23 H27] HP. split.
- rewrite <- H23. exact (HP 23 ltac:(unfold acallee_saved; lia)).
- rewrite <- H27. exact (HP 27 ltac:(unfold acallee_saved; lia)).
Qed.

Lemma ex_ab8_ae0 :
  pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B -> AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc dec_B_sink_head segs B MT) ->
  forall (cx : dctx) (W : world segs) (c : config),
  base cx -> ex_ab8 B MT cx W c -> SRr segs W c (llvm_b_st_ae0 B MT cx).
Proof.
intros HPCF HUTR LAWS MTL AFREE cx W c HB
  (fx' & ly & S & regs & mem & md & k & res & upb & spent & rest & -> & Hfz & Hcore & Hk & Hperm & Hmle & Hrest &
   Hmok & Hsp & Hfrs & Hfsh & R23 & R27).
destruct (ex_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx HB)
  as (_ & _ & _ & _ & _ & _ & _ & Hnlen & _).
pose proof (mo_free_nonneg MT MTL) as Hf0.
eapply SRr_bind.
{ exact (@fr_free_at rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI fx'
    HPCF HUTR LAWS MTL AFREE 0xab8 23 cx W regs mem md ly S k [(res, dec_b_len (d_n cx))] upb
    (dec_b_uolen (CChan.upstream_result (dec_b_len (d_n cx)))) spent (mo_free MT + rest) (ab_R res upb)
    (or_introl (conj eq_refl eq_refl)) HB Hcore ltac:(lia) Hperm Hmle ltac:(lia) Hmok Hfrs Hfsh
    (conj R23 R27) (fun r Hr => proj1 Hr) (ab_R_kept res upb) Hfz). }
intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfz2 & Hcore2 & Hperm2 & Hmle2 & Hmok2 & Hfrs2 & Hfsh2 & HR2).
eapply SRr_bind.
{ exact (@fr_free_at rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI fx2
    HPCF HUTR LAWS MTL AFREE 0xac0 27 cx W2 regs2 mem2 md2 ly2 S2 (k + 1) [] res (dec_b_len (d_n cx))
    (spent + mo_free MT) rest (ab_R res upb)
    (or_intror (conj eq_refl eq_refl)) HB Hcore2 ltac:(lia) Hperm2 Hmle2 Hrest Hmok2 Hfrs2 Hfsh2
    HR2 (fun r Hr => proj2 Hr) (ab_R_kept res upb) Hfz2). }
intros W3 c3 _ H3.
apply (rp_ae0 B MT LAWS MTL cx W3 c3 (k + 1 + 1) (spent + mo_free MT + mo_free MT) rest (ab_R res upb) Hnlen H3).
- unfold dec_ev_ae0. lia.
- exact Hsp.
Qed.
End ab.
