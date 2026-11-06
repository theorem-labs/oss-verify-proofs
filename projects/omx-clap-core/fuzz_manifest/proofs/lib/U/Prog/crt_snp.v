From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem printf_facts_c snprintf_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import crt_text crt_ka0.
Import ListNotations.
Open Scope Z_scope.

Lemma length_zb : forall bs : list byte, length (zbytes bs) = length bs.
Proof. intros bs. apply length_map. Qed.

Lemma pf_bytes_app : forall a b, pf_bytes (a ++ b) = pf_bytes a ++ pf_bytes b.
Proof. intros a b. apply map_app. Qed.

Lemma pf_zb : forall bs : list byte, pf_bytes (map bv_unsigned bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. unfold pf_bytes in *. cbn [map]. rewrite IH.
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma zb_nz : forall bs : list byte, Forall (fun b => bv_unsigned b <> 0) bs -> Forall (fun c => 0 < c < 256) (zbytes bs).
Proof.
  induction bs as [|b bs IH]; intros H; constructor; inversion H; subst; [|apply IH; assumption].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma aptr_ok : forall m S lo D n (r : word) (s sl : list byte),
  cstr_at m (bv_unsigned r) s sl -> 0 < bv_unsigned r ->
  (bv_unsigned r + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= lo \/ S <= bv_unsigned r) ->
  (bv_unsigned r + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= D \/ D + n <= bv_unsigned r) ->
  pf_arg_ok m S lo D n r (APtr (zbytes s)).
Proof.
  intros m S lo D n r s sl (Hb & Hn & Ha) H0 H1 H2.
  unfold pf_arg_ok, zbytes. rewrite length_map.
  split; [exact (zb_nz s Hn)|]. exists sl.
  rewrite pf_bytes_app, pf_zb. cbn [pf_bytes map]. rewrite <- app_assoc. cbn [app].
  split; [exact Hb|]. split; [exact Ha|]. split; [exact H0|]. split; [exact H1 | exact H2].
Qed.

Lemma cstr_sfx : forall m U s sl k, cstr_at m U s sl -> (k <= length s)%nat ->
  cstr_at m (U + Z.of_nat k) (skipn k s) sl.
Proof.
  intros m U s sl k (Hb & Hn & Ha) Hk.
  rewrite <- (firstn_skipn k s) in Hb. rewrite <- app_assoc in Hb. apply bytes_at_app in Hb as [_ Hb].
  rewrite length_firstn in Hb. replace (Nat.min k (length s)) with k in Hb by lia.
  split; [exact Hb|]. split.
  - rewrite Forall_forall in *. intros x Hx. apply Hn. rewrite <- (firstn_skipn k s). apply in_or_app. right. exact Hx.
  - rewrite length_skipn. replace (U + Z.of_nat k + Z.of_nat (length s - k) + 1) with (U + Z.of_nat (length s) + 1) by lia.
    exact Ha.
Qed.

Lemma text_cstr : forall m m' res sz junk T W,
  rw_cells rsegs m res [CB (Z.to_nat sz) junk] -> bytes_at rsegs m' res (pf_bytes (T ++ [0])) ->
  munch W m m' -> disjoint_from W (res + Z.of_nat (length T) + 1) (sz - Z.of_nat (length T) - 1) ->
  Forall (fun c => 0 < c < 256) T -> Z.of_nat (length T) + 8 <= sz ->
  cstr_at m' res (pf_bytes T) (skipn (length T + 1) junk).
Proof.
  intros m m' res sz junk T W [[[Hl _] Hb] _] HT MU DJ NZ HL.
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  rewrite <- (firstn_skipn (length T + 1) junk) in Hb. apply bytes_at_app in Hb as [_ Hs].
  rewrite length_firstn in Hs. cbn [cell_wf] in Hl. replace (Nat.min (length T + 1) (length junk)) with (length T + 1)%nat in Hs by lia.
  assert (Ls : Z.of_nat (length (skipn (length T + 1) junk)) = sz - Z.of_nat (length T) - 1)
    by (rewrite length_skipn; lia).
  apply (bytes_at_transport rsegs W m m') in Hs; [| exact MU | rewrite Ls; replace (res + Z.of_nat (length T + 1)) with (res + Z.of_nat (length T) + 1) by lia; exact DJ].
  split.
  - rewrite pf_bytes_app in HT. change (pf_bytes [0]) with [Z_to_bv 8 0] in HT.
    change (pf_bytes T ++ Z_to_bv 8 0 :: skipn (length T + 1) junk) with (pf_bytes T ++ [Z_to_bv 8 0] ++ skipn (length T + 1) junk).
    rewrite app_assoc. apply bytes_at_app. split; [exact HT|].
    rewrite length_app. unfold pf_bytes. rewrite length_map. cbn [length].
    replace (res + Z.of_nat (length T + 1)) with (res + Z.of_nat (length T) + 1) in Hs by lia.
    replace (res + Z.of_nat (length T + 1)%nat) with (res + Z.of_nat (length T) + 1) by lia. exact Hs.
  - split.
    + unfold pf_bytes. rewrite Forall_forall in *. intros x Hx. apply in_map_iff in Hx as (c & <- & Hc).
      specialize (NZ c Hc). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      rewrite Z.mod_small by lia. lia.
    + unfold pf_bytes. rewrite length_map. rewrite Ls. pose proof (Z.mod_pos_bound (- (res + Z.of_nat (length T) + 1)) 8). lia.
Qed.
