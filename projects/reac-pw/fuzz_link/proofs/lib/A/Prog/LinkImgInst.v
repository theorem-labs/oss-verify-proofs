(* The image instance of link's listing: `PI_link : PAImg link_listing` for fuzz_link.asan (the PUBLISHED pin,
   sha256 059dae63e07c...). Every image-A walk of link's own functions is stated at an abstract
   `{PI : PAImg link_listing}` (lib/A/Prog/LinkPa.v); this file is the one place that builds the instance from
   the image the build loads, so that a top lemma can be stated at it.

   The form is pcap's lib/A/Prog/PcapEntryTop.v sections "the listing's image" and "the instance's named
   equalities" (origin/ossv/recipes), with link's tables: the code table lib/A/Prog/LinkPaCheck.v `linktbl`
   (8289 words from fuzz_socket 0x821cc), the value table `link_val` over LinkAddr.v (66 objects, 138 auipc
   values) and the certificate `link_lib_check`. The segments are AB1v.v `tfibsegs`, which is
   `Asan.M.loaded_segments` by definition, so `HSEGS : pa_segs = tfibsegs` is `eq_refl` at this instance.

   Proves no function (kind: image instance). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YCbn YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaCheck.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro PcapRelroA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.

Lemma link_B_ok : 0 <= link_val A_TEXT /\ link_val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ link_val A_TEXT mod 4 = 0.
Proof. unfold link_val, link_text, A_TEXT. cbn. split; [lia|]. split; [lia | reflexivity]. Qed.

Lemma link_val_range : forall a, 0 <= link_val a < 2 ^ 64.
Proof.
  intros a. unfold link_val. destruct (Nat.eqb a A_TEXT); [zlit|].
  destruct (Nat.ltb a (A_HI 0)).
  - unfold link_obj. generalize (a - A_OBJ 0)%nat as m. intros m.
    do 66 (destruct m as [|m]; [zlit|]). zlit.
  - unfold link_hi. generalize (a - A_HI 0)%nat as m. intros m.
    do 138 (destruct m as [|m]; [zlit|]). zlit.
Qed.

Lemma link_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The four loaded segments of fuzz_link.asan, as the image module gives them. *)
Lemma link_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr). unfold kLowMemEnd.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
    (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs))
    by (exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin)).
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H. repeat (destruct H as [H|H]); try contradiction; injection H as <- <-; lia.
Qed.

Lemma link_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < pcap_img_end.
Proof.
  intros a (sg & Hin & Hr). unfold pcap_img_end, IMG_TOP.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
    (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs))
    by (exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin)).
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H. repeat (destruct H as [H|H]); try contradiction; injection H as <- <-; lia.
Qed.

Lemma link_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img tfibsegs a.
Proof.
  intros a Ha. destruct pcap_relro_in_image as (s & Hs & H1 & H2 & H3). exists s. split; [exact Hs | lia].
Qed.

(* Every object of the value table lies inside the image, with its eight bytes. *)
Lemma link_obj_img_b :
  forallb (fun i => (0x10000 <=? link_val (A_OBJ i)) && (link_val (A_OBJ i) + 8 <=? pcap_img_end))
    (seq 0 66) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma link_obj_img : forall i, (i < 66)%nat ->
  0x10000 <= link_val (A_OBJ i) /\ link_val (A_OBJ i) + 8 <= pcap_img_end.
Proof.
  intros i Hi.
  assert (Hin : In i (seq 0 66)) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) link_obj_img_b i Hin) as H.
  apply andb_prop in H as [H1 H2].
  split; [apply Z.leb_le; exact H1 | apply Z.leb_le; exact H2].
Qed.

Lemma link_xcalls_ok : forall s k, In (s, k) link_xcalls -> link_sigma s = link_val A_TEXT + k.
Proof.
  intros s k H.
  assert (Hb : forallb (fun p => Z.eqb (link_sigma (fst p)) (link_val A_TEXT + snd p)) link_xcalls = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. apply Z.eqb_eq. exact (Hb (s, k) H).
Qed.

Section inst. Context {rc : YM05.RunCeil}.

(* The ledger's image window covers the whole loaded image: the first segment's base and the last one's end
   (the form of lib/A/ACeg.v:106-111). *)
Lemma link_img_cover : forall ly S md, ALedger tfibsegs ly S md ->
  fst (ly_img ly) <= 0x10000 /\ pcap_img_end <= fst (ly_img ly) + snd (ly_img ly).
Proof.
  intros ly S md L. split.
  - destruct (al_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
  - destruct (al_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
    cbn in H. unfold pcap_img_end, IMG_TOP. lia.
Qed.

(* The instance: link's listing on fuzz_link.asan, its read-only window PcapRelro.v's measured relro. *)
Definition PI_link : PAImg link_listing := {|
  pa_segs := tfibsegs;
  pa_tbl := linktbl;
  pa_tbl_ok := linktbl_ok;
  pa_val := link_val;
  pa_sigma := link_sigma;
  pa_cert := link_lib_check;
  pa_B_ok := link_B_ok;
  pa_val_range := link_val_range;
  pa_wx := link_wx;
  pa_segs_low := link_segs_low;
  pa_img_range := link_img_range;
  pa_img_cover := link_img_cover;
  pa_obj_img := link_obj_img;
  pa_relro_lo := PCAP_RLO;
  pa_relro_hi := PCAP_RHI;
  pa_relro_img := link_relro_img;
  pa_xcalls := link_xcalls_ok |}.

(* The instance's named equalities, so that a walk's HSEGS / LinkVals / relro premises are discharged by
   name and never by unfolding the record. *)
Lemma pi_link_segs : @pa_segs rc link_listing PI_link = tfibsegs.
Proof. reflexivity. Qed.
Lemma pi_link_text : @pa_val rc link_listing PI_link A_TEXT = link_text.
Proof. reflexivity. Qed.
Lemma pi_link_relro :
  @pa_relro_lo rc link_listing PI_link = PCAP_RLO /\ @pa_relro_hi rc link_listing PI_link = PCAP_RHI.
Proof. split; reflexivity. Qed.
Lemma pi_link_entry : @pa_val rc link_listing PI_link A_TEXT + AF_LLVMFuzzerTestOneInput = 0x827d4.
Proof. vm_compute. reflexivity. Qed.

(* LinkWalk.v's LinkVals at this instance: the value table IS LinkAddr.v's. *)
Lemma pi_link_vals : LinkVals (PI := PI_link).
Proof.
  split; try reflexivity.
  - intros i Hi. cbn [pa_val PI_link]. unfold link_val.
    replace (Nat.eqb (A_OBJ i) A_TEXT) with false
      by (symmetry; apply Nat.eqb_neq; unfold A_OBJ, A_TEXT; lia).
    replace (Nat.ltb (A_OBJ i) (A_HI 0)) with true
      by (symmetry; apply Nat.ltb_lt; unfold A_OBJ, A_HI, link_nobj in *; lia).
    f_equal. unfold A_OBJ. lia.
  - intros j Hj. cbn [pa_val PI_link]. unfold link_val.
    replace (Nat.eqb (A_HI j) A_TEXT) with false
      by (symmetry; apply Nat.eqb_neq; unfold A_HI, A_TEXT; lia).
    replace (Nat.ltb (A_HI j) (A_HI 0)) with false
      by (symmetry; apply Nat.ltb_ge; unfold A_HI; lia).
    f_equal. unfold A_HI. lia.
Qed.

End inst.
