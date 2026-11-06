(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_crt: the two call-context facts every call of check_round_trip inside image B's
   LLVMFuzzerTestOneInput needs, which lib/B/Prog/check_round_trip_cg.v:150-168 asks for and no leaf bridge gives:

     c1c_chain : the frame-pointer chain at the call, built from the slot pre's own chain (which is empty) and the
                 frame record the prologue wrote below the entry sp (dec_b_saved's words (8, ra) and (16, s0));
     c1c_ctx   : the call context is one of CTX_check_round_trip's
                 (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:193, :165).

   Both are cgif's pattern at fuzz_decode's names: cgif_file_fuzzer lib/A/ACf5.v:172 rt_chain (over
   lib/Reusable/YCbq.v:296 achain_push) and :132 rt_ctx_in (origin/ossv/recipes c8557374ad2e).  The segment that
   calls check_round_trip (crt1 at +0x68c, exit at +0xaa0) uses both. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
Import ListNotations.
Open Scope Z_scope.

Section CrtCall.
Context {rc : YM05.RunCeil}.
Local Notation segs := decodesegsB0.

(* cgif lib/A/ACf5.v:172 rt_chain, at image B's frame: the chain at a call site inside the slot is the one entry
   the prologue wrote at the entry sp, on top of the caller's (empty) chain -- or empty, when the entry sp is
   within 16 bytes of the layout's top (YCbq.v:218 achain's first disjunct). *)
Lemma c1c_chain : forall (ly lyc : alayout) (rd rd' : reader) (sp0 s0c sp1 ra : Z),
  @achain rc ly rd sp0 s0c [] ->
  ly_top lyc = ly_top ly -> ly_top ly <= 2 ^ 64 ->
  (forall a, sp0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  rdword rd' (sp0 - 8) = Some ra -> rdword rd' (sp0 - 16) = Some s0c ->
  4096 <= ra -> alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> sp1 + 16 <= sp0 ->
  exists ch, @achain rc lyc rd' sp1 sp0 ch /\ (ch = [] \/ spine ch = [ra]).
Proof.
  intros ly lyc rd rd' sp0 s0c sp1 ra HC Etop Htop64 Hkeep H8 H16 Hra Hceil Hal Hsp.
  destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
  - exists [(sp0, ra, s0c)]. split; [| right; reflexivity].
    apply (achain_ly_top ly lyc rd' sp1 sp0 [(sp0, ra, s0c)] Etop).
    eapply achain_push; try eassumption; try lia.
  - exists []. split; [| left; reflexivity].
    left. split; [right; left; lia | reflexivity].
Qed.

(* cgif lib/A/ACf5.v:132 rt_ctx_in, at CTX_check_round_trip: the call's own return address followed by the
   chain's spine, which is empty or the slot's own return address. *)
Lemma c1c_ctx : forall (RA_LLVMF ra : Z) (ch : list (Z * Z * Z)),
  (ra = DEC_A_LLVMF + 0x690 \/ ra = DEC_A_LLVMF + 0xaa4) ->
  (ch = [] \/ spine ch = [RA_LLVMF]) ->
  In (ra :: spine ch) (CTX_check_round_trip RA_LLVMF).
Proof.
  intros RA_LLVMF ra ch Hra Hch.
  unfold CTX_check_round_trip, DEC_LLVMF_RA_CRT.
  destruct Hch as [-> | E]; [cbn [spine map flat_map app] | rewrite E; cbn [map flat_map app]];
    destruct Hra as [-> | ->]; cbn [In]; tauto.
Qed.
End CrtCall.
