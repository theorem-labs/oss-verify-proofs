From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import crt_lib crt_inv.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ceil8_mono : forall y z, y <= z -> y + (- y) mod 8 <= z + (- z) mod 8.
Proof. intros y z H. Z.div_mod_to_equations. lia. Qed.

Lemma ceil8_le : forall y d, y <= d -> d mod 8 = 0 -> y + (- y) mod 8 <= d.
Proof. intros y d H Hd. Z.div_mod_to_equations. lia. Qed.

Lemma ceil8_ge : forall y, 0 <= (- y) mod 8 < 8.
Proof. intros y. apply Z.mod_pos_bound. lia. Qed.

Lemma ceil8_slack : forall y z, y <= z -> y + (- y) mod 8 <= 8 * ((z + 7) / 8).
Proof. intros y z H. Z.div_mod_to_equations. lia. Qed.

Lemma statics_split : forall z, alloc_statics z <-> (G_LIVE <= z < G_COUNT + 8 \/ G_FAIL <= z < G_FAIL + 8).
Proof. intros z. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia. Qed.

Lemma off_statics_slack : forall s m, 0 < m ->
  (forall z, s <= z < s + m -> ~ alloc_statics z) -> off_statics s (m + (- (s + m)) mod 8).
Proof.
  intros s m Hm H. pose proof (ceil8_ge (s + m)) as R.
  unfold off_statics. split.
  - destruct (Z_le_dec (G_COUNT + 8) s) as [E|E]; [right; exact E|].
    destruct (Z_lt_le_dec (s + m - 1) G_LIVE) as [F|F].
    + left. unfold G_LIVE in *. Z.div_mod_to_equations. lia.
    + exfalso. apply (H (Z.max s G_LIVE)); [unfold G_LIVE, G_COUNT in *; lia|]. apply statics_split. left. unfold G_LIVE, G_COUNT in *; lia.
  - destruct (Z_le_dec (G_FAIL + 8) s) as [E|E]; [right; exact E|].
    destruct (Z_lt_le_dec (s + m - 1) G_FAIL) as [F|F].
    + left. unfold G_FAIL in *. Z.div_mod_to_equations. lia.
    + exfalso. apply (H (Z.max s G_FAIL)); [unfold G_FAIL in *; lia|]. apply statics_split. right. unfold G_FAIL in *; lia.
Qed.

Lemma off_statics_in : forall s m, 0 < m ->
  (forall z, s <= z < s + m -> ~ alloc_statics z) -> off_statics s m.
Proof.
  intros s m Hm H. pose proof (off_statics_slack s m Hm H) as O. pose proof (ceil8_ge (s + m)).
  unfold off_statics in *. lia.
Qed.

Lemma zbytes_pf : forall l : list Z, Forall (fun c => 0 <= c < 256) l -> zbytes (pf_bytes l) = l.
Proof.
  unfold zbytes, pf_bytes. induction l as [|c l IH]; intros H; [reflexivity|]. inversion H; subst. cbn [map].
  rewrite IH by assumption. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma pf_zbytes : forall bs : list byte, pf_bytes (zbytes bs) = bs.
Proof.
  unfold zbytes, pf_bytes. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. rewrite IH.
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma zbytes_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (zbytes bs).
Proof.
  induction bs as [|b bs IH]; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma zbytes_nz : forall bs : list byte, Forall (fun b => bv_unsigned b <> 0) bs -> Forall (fun c => 0 < c < 256) (zbytes bs).
Proof.
  induction bs as [|b bs IH]; intros H; constructor; inversion H; subst; [|apply IH; assumption].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma length_zbytes : forall bs, length (zbytes bs) = length bs.
Proof. intros bs. apply length_map. Qed.

Lemma bytes_at_keep : forall (segs : list Segment) m m' a bs, bytes_at segs m a bs ->
  (forall i, (i < length bs)%nat -> mbyte segs m' (a + Z.of_nat i) = mbyte segs m (a + Z.of_nat i)) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (Ha & Hl & Hb) H. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (Hb i Hi). exact (H i Hi).
Qed.

Section A.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis CTX : ManifestB.ctx_owned B MR.
Hypothesis SFA : statics_facts B.
Hypothesis SF : statics_free B MR.
Hypothesis SNE : statics_noerrno B.
Hypothesis ERR : errno_low B.
Hypothesis GS : guard_syms B.
Hypothesis BSP : block_slack_present B API.

Lemma ledger_rebuild : forall K L A regs mem md blk L1 A1 mem1 md1 Lam peak cnt fail peak' cnt' fail',
  crt_inv B API K L A regs mem md blk L1 A1 mem1 md1 -> ledger B L A mem Lam peak cnt fail ->
  alloc_words B mem1 (lsum Lam) peak' cnt' fail' -> lsum Lam <= peak' < 2 ^ 64 -> 0 <= cnt' < 2 ^ 64 ->
  0 <= fail' < 2 ^ 64 -> ledger B L1 A1 mem1 Lam peak' cnt' fail'.
Proof.
  intros K L A regs mem md blk L1 A1 mem1 md1 Lam peak cnt fail peak' cnt' fail' IV LG AW P C F.
  destruct IV as (_ & _ & _ & _ & _ & (b1 & b2 & Eb1 & Eb0) & Hbb & _).
  destruct LG as (_ & _ & _ & _ & ND & FA).
  split; [exact AW|]. split; [exact P|]. split; [exact C|]. split; [exact F|]. split; [exact ND|].
  eapply Forall_impl; [|exact FA]. intros [a k] (Hk & Hin & Hw & Hni). cbn [fst snd] in *.
  split; [exact Hk|]. split; [rewrite Eb1; apply in_mid; rewrite <- Eb0; exact Hin|].
  split; [|exact Hni].
  intros j Hj. rewrite <- (Hw j Hj). rewrite SEG.
  exact (Hbb (a - 16) (k + 16) (Z.of_nat j) Hin ltac:(lia)).
Qed.

Lemma aw_munch : forall m m' W live peak cnt fail, alloc_words B m live peak cnt fail -> munch W m m' ->
  (forall x, alloc_statics x -> outside W x) -> alloc_words B m' live peak cnt fail.
Proof.
  intros m m' W live peak cnt fail (W1 & W2 & W3 & W4) HW Ho.
  unfold alloc_words in *.
  split; [|split; [|split]];
    (eapply word_mem_munch; [exact HW | unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia | unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia | | eassumption]);
    intros x Hx; apply Ho; unfold alloc_statics; lia.
Qed.

Lemma aw_cpost : forall L1 A1 regs1 m1 md1 E L2 A2 regs2 m2 md2 live peak cnt fail,
  alloc_words B m1 live peak cnt fail -> MR L1 A1 m1 md1 ->
  call_post B MR L1 A1 regs1 m1 md1 E L2 A2 regs2 m2 md2 ->
  (forall x, alloc_statics x -> ~ E x) -> alloc_ceiling + ALLOC_STACK <= spZ regs1 ->
  alloc_words B m2 live peak cnt fail.
Proof.
  intros L1 A1 regs1 m1 md1 E L2 A2 regs2 m2 md2 live peak cnt fail (W1 & W2 & W3 & W4) HM1 CP HE HS.
  destruct CP as (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof alloc_ceiling_val as Hacv.
  assert (K : forall x, alloc_statics x -> mbyte (ms_segs B) m2 x = mbyte (ms_segs B) m1 x).
  { intros x Hx. destruct (SFA x Hx) as (Hi & _ & _).
    apply (Hfr x (or_intror Hi) (SF _ _ _ _ x HM1 Hx) (SF _ _ _ _ x HM2 Hx)); [|exact (HE x Hx)].
    intros [S|S]; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, ALLOC_STACK in *; lia | exact (SNE x Hx S)]. }
  unfold alloc_words in *.
  split; [|split; [|split]]; intros j Hj; [rewrite <- (W1 j Hj) | rewrite <- (W2 j Hj) | rewrite <- (W3 j Hj) | rewrite <- (W4 j Hj)];
    apply K; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia.
Qed.

Lemma fc_bpost : forall K1 E L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 S cs,
  bpost B MR K1 E L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 -> MR L1 A1 mem1 md1 ->
  rw_cells rsegs mem1 S cs -> spZ regs1 <= S -> alloc_ceiling <= S -> S + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall a, E a -> a < alloc_ceiling) ->
  rw_cells rsegs mem2 S cs.
Proof.
  intros K1 E L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 S cs BP HM1 FR H1 H2 H3 HE.
  destruct BP as (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _). rewrite SEG in Hfr.
  pose proof alloc_ceiling_val as Hacv.
  apply (rw_cells_keep mem1 mem2 S cs FR). intros a Ha.
  apply Hfr; [left; lia | | | |].
  - intros O. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 O). lia.
  - intros O. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 O). lia.
  - intros [Sc|Sc]; [lia | unfold errno_low in ERR; lia].
  - intros He. pose proof (HE a He). lia.
Qed.
Lemma ustr : forall K L A regs mem md blk L1 A1 mem1 md1 U u us ua uk,
  crt_inv B API K L A regs mem md blk L1 A1 mem1 md1 ->
  cstr_at mem U u us -> In (ua, uk) (blocks L A) -> ua <= U -> U + Z.of_nat (length u) + 1 <= ua + uk ->
  exists us', cstr_at mem1 U u us' /\ Z.of_nat (length us') = (- (U + Z.of_nat (length u) + 1)) mod 8.
Proof.
  intros K L A regs mem md blk L1 A1 mem1 md1 U u us ua uk IV (Hb & Hn & Ha) Hin HL HR.
  destruct IV as (HM1 & _ & _ & _ & _ & (b1 & b2 & Eb1 & Eb0) & Hbb & _).
  assert (Hin1 : In (ua, uk) (blocks L1 A1)) by (rewrite Eb1; apply in_mid; rewrite <- Eb0; exact Hin).
  pose proof (blk_present B API L1 A1 mem1 md1 ua uk 0 HM1 Hin1) as P0.
  pose proof (blocks_low B API L1 A1 mem1 md1 ua uk 0 HM1 Hin1) as BL0.
  assert (Hk : 0 < uk) by lia.
  specialize (BL0 ltac:(lia)).
  pose proof alloc_ceiling_val as Hacv.
  pose proof (blocks_low B API L1 A1 mem1 md1 ua uk (uk - 1) HM1 Hin1 ltac:(lia)) as BL1.
  set (r := (- (U + Z.of_nat (length u) + 1)) mod 8).
  assert (Hr : 0 <= r < 8) by (apply Z.mod_pos_bound; lia).
  replace (u ++ Z_to_bv 8 0 :: us) with ((u ++ [Z_to_bv 8 0]) ++ us) in Hb by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in Hb as [Hb _].
  assert (B1 : bytes_at rsegs mem1 U (u ++ [Z_to_bv 8 0])).
  { apply (bytes_at_keep rsegs mem mem1 U _ Hb). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    replace (U + Z.of_nat i) with (ua + (U + Z.of_nat i - ua)) by lia.
    apply (Hbb ua uk); [exact Hin | lia]. }
  assert (PS : forall i, 0 <= i < Z.of_nat (Z.to_nat r) -> present mem1 (U + Z.of_nat (length u) + 1 + i)).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia.
    destruct (Z_lt_le_dec (U + Z.of_nat (length u) + 1 + i) (ua + uk)) as [Hx|Hx].
    - replace (U + Z.of_nat (length u) + 1 + i) with (ua + (U + Z.of_nat (length u) + 1 + i - ua)) by lia.
      exact (proj1 (blk_present B API L1 A1 mem1 md1 ua uk (U + Z.of_nat (length u) + 1 + i - ua) HM1 Hin1 ltac:(lia))).
    - apply (BSP L1 A1 mem1 md1 ua uk); [exact HM1 | exact Hin1 |]. split; [exact Hx|].
      pose proof (ceil8_slack (U + Z.of_nat (length u) + 1) (ua + uk) HR) as C. unfold r in Hi. lia. }
  destruct (present_bytes rsegs mem1 (U + Z.of_nat (length u) + 1) (Z.to_nat r) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) PS)
    as (bs & Hlb & Hbs).
  exists bs. split.
  - split; [|split; [exact Hn|]].
    + replace (u ++ Z_to_bv 8 0 :: bs) with ((u ++ [Z_to_bv 8 0]) ++ bs) by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact B1|]. rewrite length_app. cbn [length].
      replace (U + Z.of_nat (length u + 1)) with (U + Z.of_nat (length u) + 1) by lia. exact Hbs.
    + rewrite Hlb, Z2Nat.id by lia. unfold r. lia.
  - rewrite Hlb, Z2Nat.id by lia. reflexivity.
Qed.
End A.
