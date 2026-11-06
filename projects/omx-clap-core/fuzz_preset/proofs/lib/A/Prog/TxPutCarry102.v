(* fuzz_preset, harness fix #102: the CARRY of the tx_put walks across a stretch that writes only tx_put's own frame
   and the record's 28 bytes (the S0 row of both images: the prologue, the checks and the branches before any call;
   A' and B' alike). Image-free: over any {PA : PAImg L}, any allocator relation ARx with its laws, PRH_Base's fpre
   and K0's PRH_FnTx.v predicates (blob b6f264e13647, cold/h-hpreset-7-walkkit-next eee71ebe8d49).
   Owner: TxPutB102 (h-rw-pre-7's #102 lanes); the A' S0 row (h-rw-dis-3) takes it by path.
   rule 24: proves no function (kind: shared lemmas)
   txc_carry: from the entry's fpre / fwin / prhtx_place and a word-level keep of every byte outside
   [sp0 - F, sp0) and [t, t + 28) (F + 8 <= STK_tx_put: the frame lies 8 bytes above the ceiling at least), the walk's
   cj_kept from entry (YCbqGcallW.cj_kept_exec, window STK_tx_put, written cells prhtx_fp), the read-only view, the
   record's place, and the keep of prhtx_inv / prhtx_trace / prh_ledger / prh_own / src_rd / bytes_at (TxPutKeep102.v;
   the ledger's head cells directly, as they may reach 8 bytes past a block below the ceiling). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger TxPutKeep102.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.

(* the record's 28 bytes are visible wherever the record's four fields read *)
Lemma txc_present_of_rec : forall (W : world segs) mem t b len cap f,
  prhtx_rec W mem t b len cap f -> forall a, t <= a < t + 28 -> aview segs (w_H W) mem a <> None.
Proof.
intros W mem t b len cap f (_ & _ & _ & _ & Mb & Ml & Mc & Mf) a Ha.
assert (Hm : exists v, mbyte segs (mrestrict (w_H W) mem) a = Some v).
{ unfold val_mem in Mb, Ml, Mc, Mf.
  destruct (Z_lt_ge_dec a (t + 8)) as [H1|H1].
  { pose proof (Mb (Z.to_nat (a - t)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
    replace (t + (a - t)) with a in E by lia. eexists. exact E. }
  destruct (Z_lt_ge_dec a (t + 16)) as [H2|H2].
  { pose proof (Ml (Z.to_nat (a - (t + 8))) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
    replace (t + 8 + (a - (t + 8))) with a in E by lia. eexists. exact E. }
  destruct (Z_lt_ge_dec a (t + 24)) as [H3|H3].
  { pose proof (Mc (Z.to_nat (a - (t + 16))) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
    replace (t + 16 + (a - (t + 16))) with a in E by lia. eexists. exact E. }
  pose proof (Mf (Z.to_nat (a - (t + 24))) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
  replace (t + 24 + (a - (t + 24))) with a in E by lia. eexists. exact E. }
destruct Hm as (v & Hv). unfold aview. rewrite Hv. cbn [option_map]. discriminate.
Qed.

Lemma txc_carry : forall (F : Z) ly S Hp (W : world segs) regs mem md ch mem3 md3 dw t b0 cap0,
  fpre B ARx STK_tx_put ly S Hp W regs mem md ch ->
  0 <= F -> F + 8 <= STK_tx_put ->
  fwin ly W regs mem dw -> prhtx_place ly S W regs mem dw t ->
  (forall x : word, ~ (spZ regs - F <= bv_unsigned x < spZ regs) -> ~ (t <= bv_unsigned x < t + 28) ->
     mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem x) ->
  same_but_materialized md md3 ->
  (forall a, t <= a < t + 28 -> writable_at segs (mrestrict (w_H W) mem3) a) ->
  (forall a, t <= a < t + 28 -> aview segs (w_H W) mem3 a <> None) ->
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  cj_kept (SK := SK) segs B prh_pst STK_tx_put (spZ regs) (prhtx_fp t b0 cap0) (prhtx_fp t b0 cap0)
    ly S W mem md ly S W mem3 md3 /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem3) /\
  prhtx_place ly S W regs mem3 dw t /\
  (forall Lam b len cap txt, prhtx_inv B Lam ly S W mem b len cap txt -> prhtx_inv B Lam ly S W mem3 b len cap txt) /\
  (prhtx_trace B ly W mem t -> prhtx_trace B ly W mem3 t) /\
  (forall Hp' Lam peak cnt fail ran most own, prh_ledger B ly S Hp' W mem Lam peak cnt fail ran most own ->
     prh_ledger B ly S Hp' W mem3 Lam peak cnt fail ran most own) /\
  (forall own, prh_own W mem own -> prh_own W mem3 own) /\
  (forall s src, src_rd W mem s src -> src_rd W mem3 s src /\ bytes_at W mem3 s src).
Proof.
intros F ly S Hp W regs mem md ch mem3 md3 dw t b0 cap0 HPRE HF0 HF HFW HPLACE HK Hsame Hw3 Hp3 HPST.
destruct HPRE as (HPRE0 & HROD & HSTKHI & HRAC).
pose proof HPRE0 as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFW as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit & Hra28).
pose proof YM05.alloc_ceiling_lt as CL.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as [Rsp _]. fold (spZ regs) in Rsp.
destruct (keep_bundle_frame W mem mem3 F (spZ regs) t HK HF0 ltac:(lia) ltac:(lia)) as (KM & KA & KH & KMH).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - F <= a < spZ regs) -> ~ (t <= a < t + 28) ->
  aview segs (w_H W) mem3 a = aview segs (w_H W) mem a).
{ intros a Ha Hn1 Hn2. apply tpk_aview_of_m. apply HK; rewrite tpk_word_small by lia; assumption. }
split.
{ apply (cj_kept_exec (SK := SK) segs B prh_pst ARx LAWS pa_segs_low STK_tx_put (spZ regs)
    (prhtx_fp t b0 cap0) (prhtx_fp t b0 cap0) ly S Hp W mem md mem3 md3
    (fun a => (spZ regs - F <= a < spZ regs) \/ (t <= a < t + 28)) HAR); [lia | lia | lia | | | exact Hsame].
  - intros x Hx. apply HK; intros Hc; apply Hx; [left | right]; exact Hc.
  - intros a [Ha | Ha]; [left; lia|]. right. left. exists (t, t + 28). split; [left; reflexivity|]. cbn [fst snd]. lia. }
split; [exact (keep_arodata_okP B W W mem mem3 HROD KA)|].
split; [apply (keep_prhtx_place ly S W W regs mem mem3 dw t HPLACE); [lia | exact Hw3 | exact KA]|].
split; [intros Lam b len cap txt H; exact (keep_prhtx_inv B Lam ly S W W mem mem3 b len cap txt H KA KM)|].
split; [intros H; exact (keep_prhtx_trace B (spZ regs) ly W W mem mem3 t H KH ltac:(lia) ltac:(lia) Hp3)|].
split.
{ intros Hp' Lam peak cnt fail ran most own HLd.
  apply (prh_ledger_kept_aview B ly S Hp' W mem ly S Hp' W mem3 Lam peak cnt fail ran most own HLd);
    [| | intros a k _ H; exact H | apply Permutation_refl].
  - intros a Ha. apply KA. exact (tpk_pst_lo a HPST Ha).
  - intros a k i Hin Hi.
    destruct (prh_ledger_hblock B ly S Hp' W mem Lam peak cnt fail ran a k most own HLd Hin) as (Hk0 & Hab & _).
    pose proof (alx_blocks segs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096 & Hc & _).
    pose proof cf_head_nonneg as Hh0.
    assert (1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    apply KW; lia. }
split; [intros own H; exact (keep_prh_own W W mem mem3 own H KA HPST)|].
intros s src H. pose proof (keep_src_rd W W mem mem3 s src H KA) as H3. split; [exact H3 | exact (proj1 H3)].
Qed.

(* g_most (prh_most of d7c502629be9) across the same frame-plus-record-only write *)
Lemma txc_most_keep : forall (F : Z) ly S Hp (W : world segs) regs mem md ch mem3 t,
  fpre B ARx STK_tx_put ly S Hp W regs mem md ch ->
  0 <= F -> F + 8 <= STK_tx_put -> spZ regs + 16 <= t ->
  (forall x : word, ~ (spZ regs - F <= bv_unsigned x < spZ regs) -> ~ (t <= bv_unsigned x < t + 28) ->
     mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem x) ->
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  forall m, prh_most W mem m -> prh_most W mem3 m.
Proof.
intros F ly S Hp W regs mem md ch mem3 t HPRE HF0 HF Ht HK HPST m Hm.
destruct HPRE as (HPRE0 & _ & _ & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
destruct (keep_bundle_frame W mem mem3 F (spZ regs) t HK HF0 ltac:(lia) Ht) as (KM & KA & _).
exact (keep_prh_most W W mem mem3 m Hm KA HPST).
Qed.

End c.
