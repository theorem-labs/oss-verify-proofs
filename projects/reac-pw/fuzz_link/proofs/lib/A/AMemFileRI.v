(** * reac-pw/fuzz_link (asan, image A): the kept FILE block in the driver's allocator budget.

    The A twin of lib/MemFileRI.v (plain). The plain frame bounds the allocator across driver calls by a slot
    resource invariant over the kept blocks [T] ([RI_mf]: the driver's bound plus [TD [] T]). The A frame states
    the per-call budget in the call's pre ([blocks_bytes S + LIVE_LIB <= LIVE_MAX], pcap's PcapEntry.v) and lets
    no block outlive the call ([Permutation (ablocks B ly' S') (ablocks B ly S)]). Link's call may keep the
    FILE block, so the driver carries [ARI_mf b0 T S]: the live bytes are at most the driver's own bound [b0]
    plus the kept blocks, and the kept blocks are none or the one FILE block. [ARI_mf_step] carries it across a
    call whose post has [amf_blocks_post] and [amf_gi]; [ARI_mf_room] gives every call's budget premise from
    [b0 + AMF_BLOCK]; [ARI_mf_room_file] gives the premise of fmemopen's malloc ([ml_malloc]'s
    [blocks_bytes s + n <= LIVE_MAX]) inside the first marking call. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
Import ListNotations.
Local Open Scope Z_scope.

Definition ARI_mf (b0 : Z) (T : list (Z * Z)) (S : astate) : Prop :=
  blocks_bytes S <= b0 + kept_bytes T /\ (T = [] \/ exists f, T = [(f, AMF_BLOCK)]).

(** The driver's first call: nothing kept. *)
Lemma ARI_mf_init : forall b0 S, blocks_bytes S <= b0 -> ARI_mf b0 [] S.
Proof. intros b0 S H. split; [cbn [kept_bytes fold_right]; lia | left; reflexivity]. Qed.

Lemma ARI_mf_bound : forall b0 T S, ARI_mf b0 T S -> blocks_bytes S <= b0 + AMF_BLOCK.
Proof.
  intros b0 T S (H & [-> | (f & ->)]); cbn [kept_bytes fold_right snd] in H; unfold AMF_BLOCK in *; lia.
Qed.

(** Every call's budget premise from the driver's bound and the one kept block. *)
Lemma ARI_mf_room : forall b0 T S L, ARI_mf b0 T S -> b0 + AMF_BLOCK + L <= LIVE_MAX ->
  blocks_bytes S + L <= LIVE_MAX.
Proof. intros b0 T S L H HL. pose proof (ARI_mf_bound b0 T S H). lia. Qed.

(** fmemopen's malloc in the first marking call: with nothing kept yet and [n] bytes of the call's own live
    blocks, the 1304 bytes fit whenever the call's budget [L] leaves them. *)
Lemma ARI_mf_room_file : forall b0 S L n, ARI_mf b0 [] S -> b0 + L <= LIVE_MAX -> 0 <= n -> n + AMF_BLOCK <= L ->
  blocks_bytes S + n + AMF_BLOCK <= LIVE_MAX.
Proof. intros b0 S L n (H & _) HL Hn HnL. cbn [kept_bytes fold_right] in H. lia. Qed.

Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(** Across one call whose post has the A clauses [amf_blocks_post] and [amf_gi]. *)
Lemma ARI_mf_step : forall segs MS b0 ly S ly' S' T T' m',
  ARI_mf b0 T S -> amf_blocks_post T T' (ablocks B ly S) (ablocks B ly' S') -> amf_gi segs MS T' m' ->
  ARI_mf b0 T' S'.
Proof.
  intros segs MS b0 ly S ly' S' T T' m' (Hb & _) HP HG.
  pose proof (amf_blocks_post_bytes B ly S ly' S' T T' HP) as E.
  split; [lia | exact (amf_gi_shape segs MS T' m' HG)].
Qed.

(** The kept list of an [ARI_mf] state, once in the ledger, is exactly the GI's. *)
Lemma ARI_mf_of_gi : forall segs MS b0 T S m, blocks_bytes S <= b0 + kept_bytes T -> amf_gi segs MS T m ->
  ARI_mf b0 T S.
Proof. intros segs MS b0 T S m H HG. split; [exact H | exact (amf_gi_shape segs MS T m HG)]. Qed.

End a.
