From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec Mem Frame Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem Ledger ManifestB names_c printf_facts_c check_round_trip_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition img_b (a : Z) (bs : list byte) : bool :=
  (0 <=? a) && (a + Z.of_nat (length bs) <=? 2 ^ 64) && ro_bytes_b rsegs a bs.

Lemma ro_agree_bytes : forall m a bs, ro_agree rsegs m -> img_b a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs H Hb. unfold img_b in Hb.
  apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
  apply Z.leb_le in H1, H2. apply ro_bytes_b_sound in H3.
  split; [lia|]. split; [lia|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (ro_bytes_nth rsegs bs a i b H3 E) as [R1 R2]. rewrite (H _ R2). exact R1.
Qed.

Lemma img_strings_ro : forall m, ro_agree rsegs m -> img_strings m.
Proof.
  intros m H. unfold img_strings.
  split; [|split]; (apply ro_agree_bytes; [exact H | vm_compute; reflexivity]).
Qed.

Lemma crt_strings_ro : forall m, ro_agree rsegs m -> crt_strings m.
Proof.
  intros m H. unfold crt_strings.
  repeat lazymatch goal with |- _ /\ _ => split end; (apply ro_agree_bytes; [exact H | vm_compute; reflexivity]).
Qed.

Lemma range_b : forall (f : Z -> bool) lo n,
  forallb f (map (fun i => lo + Z.of_nat i) (seq 0 n)) = true -> forall a, lo <= a < lo + Z.of_nat n -> f a = true.
Proof.
  intros f lo n H a Ha. rewrite forallb_forall in H.
  replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) by lia.
  apply H. apply in_map_iff. exists (Z.to_nat (a - lo)). split; [reflexivity|]. apply in_seq. lia.
Qed.

Definition resv_b (a : Z) : bool :=
  existsb (fun s => (bv_unsigned (fst s) <=? a) && (a <? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs).

Lemma in_img_of_b : forall B, ms_segs B = rsegs -> forall a, resv_b a = true -> in_img B a.
Proof.
  intros B HS a H. unfold resv_b in H. apply existsb_exists in H as (s & Hs & E).
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  split; [rewrite HS; vm_compute; discriminate|]. exists s. rewrite HS. split; [exact Hs | lia].
Qed.

Lemma sink_cells_img : forall B, ms_segs B = rsegs -> forall a,
  (0x4fdc8 <= a < 0x4fdd0 \/ a = 0x4f999 \/ 0x4fdc0 <= a < 0x4fdc4) -> in_img B a.
Proof.
  intros B HS a Ha. apply (in_img_of_b B HS). destruct Ha as [Ha | [-> | Ha]].
  - apply (range_b resv_b 0x4fdc8 8%nat); [vm_compute; reflexivity | lia].
  - vm_compute. reflexivity.
  - apply (range_b resv_b 0x4fdc0 4%nat); [vm_compute; reflexivity | lia].
Qed.

Definition wseg_b (a : Z) : bool :=
  match find_segment rsegs a 1 with Some s => seg_writable s | None => false end.

Lemma globals_seg_w : forall a, (0x2f620 <= a < 0x2f638 \/ 0x1f3a8 <= a < 0x1f3b0) ->
  exists seg, find_segment rsegs a 1 = Some seg /\ seg_writable seg = true.
Proof.
  intros a Ha.
  assert (W : wseg_b a = true).
  { destruct Ha as [Ha | Ha].
    - apply (range_b wseg_b 0x2f620 24%nat); [vm_compute; reflexivity | lia].
    - apply (range_b wseg_b 0x1f3a8 8%nat); [vm_compute; reflexivity | lia]. }
  unfold wseg_b in W. destruct (find_segment rsegs a 1) as [s|]; [|discriminate].
  exists s. split; [reflexivity | exact W].
Qed.
