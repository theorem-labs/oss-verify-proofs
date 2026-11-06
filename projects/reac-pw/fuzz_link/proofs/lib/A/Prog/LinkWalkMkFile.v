(* reac-pw/fuzz_link, image A: link's memory FILE between the two vocabularies that talk about it, for the walks of
   link's own functions that print on g_say (reac_code_emit, reac_served_mark):
   - the contracts of link's own functions state the FILE as lib/A/Prog/reac_code_emit_c.v `amemfile_k` (the
     frame's amemfile_at at link_amf, the window with k pending bytes, the block and g_said writable);
   - the printf-family wrapper contracts (lib/A/Rt/LinkVfDefs.v `afprintf_mf_realizes` / `avfprintf_mf_realizes`)
     take it as lib/A/Rt/LinkMfDefs.v `amf_k`, `amf_dyn` (the seven words the path changes, as values) and
     `amf_pend` (the k pending bytes), and return it as `apf_file_post`.
   The bridges: `amf_k_facts` (the printf premises from `amf_k` and the pending bytes readable), `amf_k_ext` (the FILE
   across a step that keeps the block's bytes), `amf_k_unique` / `amemfile_k_unique` (one memory names one k),
   `apf_file_post_parts`, `amemfile_k_of_amf_k` / `amf_k_of_amemfile_k`, and `awrange_grows` (a writable range stays
   writable when every present byte stays present).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP09 YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require reac_code_emit_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac mkf_mv VM := apply VM; [eassumption | lia | lia].

Section a.
Variable segs : list Segment.
Variable MS : amemfile_syms.

(* two field facts at one place agree on each byte of the field *)
Lemma mkf_le_byte_eq : forall m a n v1 v2 j,
  val_mem segs m a n v1 -> val_mem segs m a n v2 -> (j < n)%nat ->
  YO0f.le_byte v1 n j = YO0f.le_byte v2 n j.
Proof.
  intros m a n v1 v2 j H1 H2 Hj. pose proof (eq_trans (eq_sym (H1 j Hj)) (H2 j Hj)) as E.
  apply (f_equal (fun o : option byte => match o with Some b => bv_unsigned b | None => 0 end)) in E.
  cbv beta iota in E. rewrite !Z_to_bv_unsigned in E.
  unfold bv_wrap, bv_modulus in E. change (2 ^ Z.of_N 8) with 256 in E.
  rewrite (Z.mod_small (YO0f.le_byte v1 n j) 256), (Z.mod_small (YO0f.le_byte v2 n j) 256) in E
    by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
  exact E.
Qed.

(* the low two bytes of an 8-byte field fix its value modulo 2 ^ 16 *)
Lemma mkf_low16 : forall m a v1 v2, val_mem segs m a 8 v1 -> val_mem segs m a 8 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 mod 65536 = v2 mod 65536.
Proof.
  intros m a v1 v2 H1 H2 R1 R2.
  pose proof (mkf_le_byte_eq m a 8 v1 v2 0 H1 H2 ltac:(lia)) as E0.
  pose proof (mkf_le_byte_eq m a 8 v1 v2 1 H1 H2 ltac:(lia)) as E1.
  unfold YO0f.le_byte in E0, E1. change (8 * Z.of_nat 8) with 64 in E0, E1.
  change (8 * Z.of_nat 0) with 0 in E0. change (8 * Z.of_nat 1) with 8 in E1.
  rewrite !Z.shiftr_0_r in E0. rewrite !Z.shiftr_div_pow2 in E1 by lia. change (2 ^ 8) with 256 in E1.
  rewrite (Z.mod_small v1 (2 ^ 64)), (Z.mod_small v2 (2 ^ 64)) in E0, E1 by lia.
  lia.
Qed.

(* THE PRINTF PREMISES from amf_k: the seven words as values, and the k pending bytes when each is readable *)
Lemma amf_k_facts : forall m f k, amf_k segs MS m f k ->
  (forall i, 0 <= i < k -> ard segs m (f + AMF_BUF + i) <> None) ->
  exists fl om wend wpos wbase pos len pb,
    amf_dyn segs MS m f fl om wend wpos wbase pos len /\ amf_pend segs m f pb /\ Z.of_nat (length pb) = k.
Proof.
  intros m f k ((H0 & H1 & H2 & _ & Hfl & Hom & _ & (pos & len & Hp & Hl & Hpos & Hlen)) & Hw) Hv.
  unfold AMF_BLOCK in H1.
  assert (Hf : f + 1304 < 2 ^ 64) by lia.
  assert (Hfl' : exists fl, 0 <= fl < 2 ^ 32 /\ val_mem segs m (f + 0) 4 fl).
  { destruct Hfl as [H | H]; [exists AF_NORD | exists (AF_NORD + AF_ERR)];
      unfold AF_NORD, AF_ERR in *; (split; [lia | exact H]). }
  assert (Hom' : exists om, 0 <= om < 2 ^ 32 /\ val_mem segs m (f + 136) 4 om).
  { destruct Hom as [H | H]; [exists 0 | exists AU32M1];
      unfold AU32M1 in *; (split; [lia | exact H]). }
  assert (Hwin : exists wend wpos wbase, 0 <= k /\ 0 <= wend < 2 ^ 64 /\ 0 <= wpos < 2 ^ 64 /\
            0 <= wbase < 2 ^ 64 /\ val_mem segs m (f + 32) 8 wend /\ val_mem segs m (f + 40) 8 wpos /\
            val_mem segs m (f + 56) 8 wbase).
  { unfold LinkMfDefs.amf_win in Hw.
    destruct Hw as [(-> & A & B & C) | (R & A & B & C)];
      [exists 0, 0, 0 | exists (f + AMF_BUF + AMF_BUFSIZ), (f + AMF_BUF + k), (f + AMF_BUF)];
      unfold AMF_BUF, AMF_BUFSIZ in *; repeat split; try lia; assumption. }
  destruct Hfl' as (fl & Rfl & Vfl). destruct Hom' as (om & Rom & Vom).
  destruct Hwin as (wend & wpos & wbase & Hk & Rwe & Rwp & Rwb & Vwe & Vwp & Vwb).
  set (g := fun i : nat => match ard segs m (f + AMF_BUF + Z.of_nat i) with Some z => z | None => 0 end).
  exists fl, om, wend, wpos, wbase, pos, len, (map g (seq 0 (Z.to_nat k))).
  split; [|split].
  - unfold amf_dyn. repeat split; try lia; assumption.
  - unfold amf_pend, azbytes. intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite nth_indep with (d' := g 0%nat) by (rewrite length_map, length_seq; exact Hi).
    rewrite map_nth, seq_nth by exact Hi. cbn [Nat.add]. unfold g.
    destruct (ard segs m (f + AMF_BUF + Z.of_nat i)) as [z|] eqn:E.
    + exact E.
    + exfalso. apply (Hv (Z.of_nat i)); [lia | exact E].
  - rewrite length_map, length_seq. lia.
Qed.

(* the FILE across a step that keeps every byte of its block *)
Lemma amf_k_ext : forall m m' f k,
  (forall a, f <= a < f + AMF_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  amf_k segs MS m f k -> amf_k segs MS m' f k.
Proof.
  intros m m' f k HX HK.
  assert (VM : forall a n v, val_mem segs m a n v -> f <= a -> a + Z.of_nat n <= f + AMF_BLOCK ->
                 val_mem segs m' a n v).
  { intros a n v Hv Hlo Hhi j Hj. rewrite HX by lia. exact (Hv j Hj). }
  unfold amf_k, amemfile_at, amemfile_static, amemfile_flags, amemfile_omode, amemfile_window,
    amemfile_cookie, LinkMfDefs.amf_win in *.
  unfold AMF_COOKIE, AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *.
  destruct HK as ((H0 & H1 & H2 & Hst & Hfl & Hom & (Hw8 & Hw16 & Hwin) & (pos & len & Hp & Hl & Hpos & Hlen)) & Hw).
  split; [split; [exact H0|]; split; [exact H1|]; split; [exact H2|]; split; [|split; [|split; [|split]]]|].
  - repeat match goal with H : _ /\ _ |- _ => destruct H end. repeat split; mkf_mv VM.
  - destruct Hfl as [Hf | Hf]; [left | right]; mkf_mv VM.
  - destruct Hom as [Hf | Hf]; [left | right]; mkf_mv VM.
  - split; [mkf_mv VM|]. split; [mkf_mv VM|].
    destruct Hwin as [(Ha & Hb & Hc) | (k' & Hk' & Ha & Hb & Hc)];
      [left; split; [mkf_mv VM|]; split; mkf_mv VM
      | right; exists k'; split; [exact Hk'|]; split; [mkf_mv VM|]; split; mkf_mv VM].
  - exists pos, len. split; [exact Hp|]. split; [exact Hl|]. split; mkf_mv VM.
  - destruct Hw as [(Hk & Ha & Hb & Hc) | (Hk & Ha & Hb & Hc)];
      [left; split; [exact Hk|]; split; [mkf_mv VM|]; split; mkf_mv VM
      | right; split; [exact Hk|]; split; [mkf_mv VM|]; split; mkf_mv VM].
Qed.

(* one memory names one pending count *)
Lemma amf_k_unique : forall m f k1 k2, amf_k segs MS m f k1 -> amf_k segs MS m f k2 -> k1 = k2.
Proof.
  intros m f k1 k2 ((H0 & H1 & H2 & _) & W1) (_ & W2).
  unfold AMF_BLOCK in H1. assert (Hf : f + 1304 < 2 ^ 64) by lia.
  unfold LinkMfDefs.amf_win, AMF_BUF, AMF_BUFSIZ in W1, W2.
  assert (Hmix : val_mem segs m (f + 32) 8 0 -> val_mem segs m (f + 32) 8 (f + 280 + 1024) -> False).
  { intros A B. pose proof (mkf_low16 m (f + 32) 0 (f + 280 + 1024) A B ltac:(lia) ltac:(lia)) as E. lia. }
  destruct W1 as [(-> & E1 & _ & _) | (R1 & A1 & P1 & _)]; destruct W2 as [(-> & E2 & _ & _) | (R2 & A2 & P2 & _)].
  - reflexivity.
  - exfalso. exact (Hmix E1 A2).
  - exfalso. exact (Hmix E2 A1).
  - pose proof (mkf_low16 m (f + 40) (f + 280 + k1) (f + 280 + k2) P1 P2 ltac:(lia) ltac:(lia)) as E. lia.
Qed.

(* the printf post is the three FILE facts at k + |T| *)
Lemma apf_file_post_parts : forall m' f k pb T fl om wend pos len,
  apf_file_post segs MS m' f k pb T fl om wend pos len ->
  amf_k segs MS m' f (k + Z.of_nat (length T)) /\
  amf_dyn segs MS m' f fl (if wend =? 0 then AU32M1 else om)
    (f + AMF_BUF + AMF_BUFSIZ) (f + AMF_BUF + k + Z.of_nat (length T)) (f + AMF_BUF) pos len /\
  amf_pend segs m' f (pb ++ T).
Proof. intros m' f k pb T fl om wend pos len H. exact H. Qed.

End a.

(* the contracts' FILE and the printf contracts' FILE, at link_amf *)
Lemma amemfile_k_of_amf_k : forall segs m f k, amf_k segs link_amf m f k ->
  awrange segs m f AMF_BLOCK -> awrange segs m LA_G_SAID SAID_SIZE -> reac_code_emit_c.amemfile_k segs m f k.
Proof. intros segs m f k (Ha & Hw) H1 H2. exact (conj Ha (conj Hw (conj H1 H2))). Qed.

Lemma amf_k_of_amemfile_k : forall segs m f k, reac_code_emit_c.amemfile_k segs m f k ->
  amf_k segs link_amf m f k /\ awrange segs m f AMF_BLOCK /\ awrange segs m LA_G_SAID SAID_SIZE.
Proof. intros segs m f k (Ha & Hw & H1 & H2). exact (conj (conj Ha Hw) (conj H1 H2)). Qed.

Lemma amemfile_k_unique : forall segs m f k1 k2,
  reac_code_emit_c.amemfile_k segs m f k1 -> reac_code_emit_c.amemfile_k segs m f k2 -> k1 = k2.
Proof.
  intros segs m f k1 k2 H1 H2.
  exact (amf_k_unique segs link_amf m f k1 k2 (proj1 (amf_k_of_amemfile_k segs m f k1 H1))
    (proj1 (amf_k_of_amemfile_k segs m f k2 H2))).
Qed.

(* a writable range stays writable when every present byte stays present *)
Lemma awrange_grows : forall segs (W : world segs) mem mem' a n,
  (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x) ->
  awrange segs (mrestrict (w_H W) mem) a n -> awrange segs (mrestrict (w_H W) mem') a n.
Proof.
  intros segs W mem mem' a n Hp Hw i Hi. eapply writable_at_grows; [|exact (Hw i Hi)].
  intros x Hx. unfold mrestrict in *. destruct (w_H W x) eqn:Eh; [exact Hx|].
  destruct (mem x) as [b|] eqn:Em; [|congruence].
  assert (Ha : apresent (w_H W) mem (bv_unsigned x)).
  { unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
  destruct (Hp _ Ha) as (_ & b' & Hb'). rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

About amf_k_facts. About amf_k_ext. About amf_k_unique. About apf_file_post_parts.
About amemfile_k_of_amf_k. About amf_k_of_amemfile_k. About amemfile_k_unique. About awrange_grows.
Print Assumptions amf_k_facts. Print Assumptions amf_k_ext. Print Assumptions amemfile_k_unique.
Print Assumptions awrange_grows.
