(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzArr BzArrD BzCLemmasFs BzCStream BzCState BzCDriver BzDState BzDOut BzR5a BzParams BzRT1 BzRT2 BzRTB2 BzRT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition wfP (w : Z) : Z := if w =? 0 then 30 else w.

Definition enc_okN (bs : list byte) (k w : Z) (str : list byte) : Prop :=
  exists (BZP : BzParams) (a1 a2 ft inU uns mtf sel selM len code rfreq lenp : zarr) (bsB bsL nIn oP nM : Z),
    @p_bs BZP = k /\ @p_wf BZP = wfP w /\ zbok a1 /\ zbok a2 /\ bh_w32 ft
    /\ str = map (Z_to_bv 8) (@enc_stream BZP (est_init a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM) (map bv_unsigned bs)).

Definition dec_okN (z : list byte) (sm : bool) (cap : Z) (out : list byte) : Prop :=
  exists (junkD : BzDState.dst),
    let '(r, n, o, _) := buffToBuffDecompress junkD (map bv_unsigned z) cap (if sm then 1 else 0) in
    r = BZ_OK /\ out = map (Z_to_bv 8) o.

Lemma map_u8_roundtrip : forall l : list byte, map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply definitions.Z_to_bv_bv_unsigned. Qed.
Lemma map_unsigned_u8 : forall l : list Z, bytes_ok l -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [H1 H2]. cbn.
  rewrite IH by exact H2. f_equal. apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.
Lemma bytes_of_payload : forall l : list byte, bytes (map bv_unsigned l).
Proof.
  induction l as [|b l IH]; [constructor|]. cbn. constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

(* [comment removed for export] *)
Theorem round_trip_weak_N : forall bs k w str sm cap out,
  Z.of_nat (length bs) <= cap -> enc_okN bs k w str -> dec_okN str sm cap out -> out = bs.
Proof.
  intros bs k w str sm cap out CAP (BZP & a1 & a2 & ft & inU & uns & mtf & sel & selM & len & code & rfreq & lenp & bsB & bsL & nIn & oP & nM & _ & _ & Z1 & Z2 & FT & ->)
    (junkD & DEC).
  set (e0 := est_init a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM) in *.
  pose proof (init_ok a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM Z1 Z2 FT) as IOK. cbv zeta in IOK. fold e0 in IOK.
  destruct IOK as [E0OK SIn].
  assert (PLZ : Z.of_nat (length (map bv_unsigned bs)) = Z.of_nat (length bs)) by (rewrite length_map; reflexivity).
  assert (STRB : bytes_ok (enc_stream e0 (map bv_unsigned bs))) by (apply enc_stream_bytes; [exact E0OK| apply SIn| apply bytes_of_payload]).
  rewrite (map_unsigned_u8 _ STRB) in DEC.
  pose proof (rt_small (if sm then 1 else 0) junkD e0 (map bv_unsigned bs) cap ltac:(destruct sm; [right| left]; reflexivity) E0OK (SIn _) (bytes_of_payload bs)
                ltac:(rewrite PLZ; exact CAP)) as X.
  destruct (buffToBuffDecompress junkD (enc_stream e0 (map bv_unsigned bs)) cap (if sm then 1 else 0)) as [[[r n'] o] d'].
  destruct DEC as (_ & ->). injection X as _ _ ->. apply map_u8_roundtrip.
Qed.
