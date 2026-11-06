(* crtA_close: the close of the cgif-form walk of check_round_trip, image A: the four pieces of the walk
   (lib/A/Prog/crtA_cuts.v cut points) compose into the contract dec_check_round_trip_cg of the FROZEN statement
   lib/A/Prog/check_round_trip_cg.v (a working branch cc88c36cf66), in cgif's
   backward-chain form (origin/ossv/recipes proofs/cgif/cgif_file_fuzzer/lib/A/ACet.v:36-43, the composition of
   ACey.v's RFC_*_stmt pieces).

   The pieces:
     HEADP  entry -> crtA_at_calloc          (lib/A/Prog/crtA_w_head.v crtA_head)
     MIDP   crtA_at_calloc <- crtA_at_loopout (lib/A/Prog/crtA_w_mid.v crtA_mid_piece)
     ENCP   crtA_at_loopout <- crtA_at_bcmp  (a Theorem Labs lane's lib/A/Prog/crtA_encw.v crtA_enc_piece)
     TAILP  crtA_at_bcmp                     (lib/A/Prog/crtA_w_tail.v crtA_tail)
   The cut Props' read-only read set RO_RD is the statement's DEC_RO_RD; crtA_in_ro_rd_dec shows the cut Props'
   membership is the statement's dec_in_ro_rd, so crtA_ro_scoped DEC_RO_RD is the statement's dec_ro_rd_scoped,
   derived from the holds statement's two instance facts dec_ro_rd_unowned / dec_rom_no_errno; and the
   contract's read-only view premise is itself scoped to DEC_RO_RD (dec_rom_view_rd), which is exactly what
   crtA_rom_on DEC_RO_RD needs.
   crtA_close_of_pieces builds crtA_pre from the contract's premises and the trace facts of dec_crt_uctx /
   dec_crt_ufix, and passes the contract's stack-depth premise to the entry piece (only the calloc call needs it,
   so it is a premise of the entry piece and not of the cut Props). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_iface check_round_trip_cg crtA_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeList crtA_w_tail crtA_w_head crtA_encw.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_loop_stmt crtA_w_mid crtA_loop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require reac_braid_encode_cg.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_braid_encode_cg.

(* The cut Props' membership in a read-only read set is the statement's (in_zr, YG0n.v:197). *)
Lemma crtA_in_ro_rd_iff : forall (RO : list (Z * Z)) (a : Z),
  crtA_in_ro_rd RO a <-> Exists (in_zr a) RO.
Proof.
  intros RO a. unfold crtA_in_ro_rd. rewrite Exists_exists. unfold in_zr. reflexivity.
Qed.
Lemma crtA_in_ro_rd_dec : forall a, crtA_in_ro_rd DEC_RO_RD a <-> dec_in_ro_rd a.
Proof. intros a. unfold dec_in_ro_rd. apply crtA_in_ro_rd_iff. Qed.

Section Close.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation segs := decodesegs0.

(* The callee contracts, exactly as dec_check_round_trip_cg_holds_stmt (check_round_trip_cg.v) states them. *)
Hypothesis HMPC : pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc.
Hypothesis HFPC : pc_wrap_free (as_code B) = decode_sigma DS___interceptor_trampoline_free.
Hypothesis HCELLS : dec_crt_cells B.
Hypothesis HOWN : dec_ro_rd_unowned B.
Hypothesis HERR : dec_rom_no_errno B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC : forall fx' : YKK.FPState, @amalloc04_rule fx' rc dec_A_sink_head segs B MT.
Hypothesis AFREE : forall fx' : YKK.FPState, @afree04_rule fx' rc dec_A_sink_head segs B MT.
Hypothesis ACALLOC : forall fx' : YKK.FPState, @acalloc04_rule fx' segs B (as_universe B)
  (@ajournal rc dec_A_sink_head segs B) (@acall_kept rc segs B) (mo_ok MT) (mo_le MT) (mo_malloc MT)
  (decode_sigma DS___interceptor_trampoline_calloc) DEC_A_calloc_ra0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH.
Hypothesis ABCMP : forall fx' : YKK.FPState,
  @abcmp_realizes fx' rc segs B (decode_sigma DS___interceptor_trampoline_bcmp).
Hypothesis ALEAF : forall fx' : YKK.FPState, @dec_leaf_wr_at rc B (@LBraid.dec_reac_braid_encode_cg) fx'.

(* The pieces not yet wired in (each becomes a Definition when its file lands). *)
Hypothesis MIDP : crtA_at_loopout B MT DEC_RO_RD -> crtA_at_calloc B MT DEC_RO_RD.

(* Piece 1 is proved: lib/A/Prog/crtA_w_head.v. *)
Definition HEADP := crtA_head B MT DEC_RO_RD HMPC HCELLS LAWS MTL AMALLOC ACALLOC.
(* Piece 3 is proved: a Theorem Labs lane's lib/A/Prog/crtA_encw.v (a working branch 80da47845a8),
   at the statement's DEC_RO_RD with the braid leaf's read-only set contained in it by computation. *)
Definition ENCP : crtA_at_bcmp B MT DEC_RO_RD -> crtA_at_loopout B MT DEC_RO_RD :=
  @crtA_enc_piece_dec rc B MT LAWS HCELLS ABCMP ALEAF.
(* Piece 4 is proved: lib/A/Prog/crtA_w_tail.v. *)
Definition TAILP : crtA_at_bcmp B MT DEC_RO_RD := crtA_tail B MT DEC_RO_RD HFPC LAWS MTL AFREE.

(* The trace facts of one call context c = raZ regs :: spine ch. *)
Lemma crtA_uctx_at : forall (CTX : list (list Z)) (regs : bvmap 5 word) (ch : list (Z * Z * Z)),
  dec_crt_uctx B CTX -> In (raZ regs :: spine ch) CTX ->
  In (dec_utrace (pc_malloc_ra0 (as_code B)) (DEC_CRT_RA_MALLOC1 :: spine ch)) (as_universe B) /\
  In (dec_utrace (pc_free_ra0 (as_code B)) (raZ regs :: spine ch)) (as_universe B).
Proof.
  intros CTX regs ch HU Hin. destruct (HU _ Hin) as [H1 H2]. split; [exact H1 | exact H2].
Qed.

Theorem crtA_close_of_pieces : forall CTX : list (list Z),
  dec_crt_uctx B CTX -> dec_crt_ufix B ->
  dec_check_round_trip_cg B MT (decode_sigma DS_check_round_trip) CTX.
Proof.
  intros CTX HU HF.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
    HJ Hra Hra4 Hgp Htp H10 H11 H12 H13 Hch HinC Hal Hwlo Hwhi Hfrm Hev Hnch Hns Hreg Hdepth
    HbA HbA1 HbA2 HbP HbP1 HbP2 Hbraid HROM Hnev Hlive Hmo Hcost.
  destruct (crtA_uctx_at CTX regs ch HU HinC) as [Htm Htf].
  apply (HEADP (MIDP (ENCP TAILP)) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
           audio pcm nch ns bA nA bP nP T ch); [| exact Hfrm | exact Hdepth].
  unfold crtA_pre.
  split; [exact HJ|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|]. split; [exact Hch|].
  split; [exact Hal|]. split; [exact Hwlo|]. split; [exact Hwhi|].
  split; [exact Hev|]. split; [exact Hnch|]. split; [exact Hns|]. split; [exact Hreg|].
  split; [exact HbA|]. split; [exact HbA1|]. split; [exact HbA2|].
  split; [exact HbP|]. split; [exact HbP1|]. split; [exact HbP2|].
  split; [exact Hbraid|]. split; [exact Hnev|]. split; [exact Hlive|]. split; [exact Hmo|].
  split; [exact Hcost|]. split; [exact Htm|]. split; [exact Htf|]. split; [exact HF|].
  split; [intros a Ha _; exact (HROM a (proj1 (crtA_in_ro_rd_dec a) Ha))|].
  intros a Ha. apply (dec_ro_rd_scoped B HOWN HERR). apply crtA_in_ro_rd_dec. exact Ha.
Qed.
End Close.

(* The statement itself: dec_check_round_trip_cg_holds_stmt of lib/A/Prog/check_round_trip_cg.v, from the close.
   Piece 2 is lib/A/Prog/crtA_w_mid.v crtA_mid_piece, which takes the convert loop's statement crt_loop_stmt_F
   (lib/A/Prog/crtA_loop_stmt.v); lib/A/Prog/crtA_loop.v proves it (crt_loop_holds_F). No hypothesis is left:
   every premise of the theorem is a premise of the statement. *)
Theorem crtA_check_round_trip_cg_holds {fx : YKK.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  forall CTX : list (list Z), dec_check_round_trip_cg_holds_stmt B MT CTX.
Proof.
  intros CTX HMPC HFPC HCELLS HOWN HERR LAWS MTL HU HF AMALLOC AFREE ACALLOC ABCMP ALEAF.
  pose proof (crtA_mid_piece B MT DEC_RO_RD LAWS crt_loop_holds_F) as MIDP.
  eapply crtA_close_of_pieces; eauto.
Qed.
