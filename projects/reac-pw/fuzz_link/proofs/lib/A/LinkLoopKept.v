From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD1y AD1u AD1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The kept blocks T of link's memory FILE in the driver's call loop: the ledger holds the driver's buffer, the
   payload block when there is one, and T (AMemFileSink.v amf_blocks_post). *)

Lemma pairwise_zdisjoint_perm : forall l l', Permutation l l' -> pairwise zdisjoint l -> pairwise zdisjoint l'.
Proof.
intros l l' HP. induction HP as [| x l1 l2 HP IH | x y l1 | l1 l2 l3 _ IH1 _ IH2]; cbn [pairwise]; intros H.
- exact I.
- destruct H as [F P]. split; [| exact (IH P)].
  apply Forall_forall. intros z Hz. exact (proj1 (Forall_forall _ _) F z (Permutation_in _ (Permutation_sym HP) Hz)).
- destruct H as [Fy [Fx P]]. pose proof (Forall_inv Fy) as Dyx. pose proof (Forall_inv_tail Fy) as Fy'.
  split; [| split; [exact Fy' | exact P]].
  constructor; [unfold zdisjoint in *; tauto | exact Fx].
- exact (IH2 (IH1 H)).
Qed.

Lemma amf_blocks_post_incl : forall T T' bl bl', amf_blocks_post T T' bl bl' -> incl T bl -> incl T' bl'.
Proof.
intros T T' bl bl' (D & -> & HP) HT x Hx. apply (Permutation_in _ (Permutation_sym HP)).
apply in_or_app. apply in_app_or in Hx as [Hx|Hx]; [right; exact (HT x Hx) | left; exact Hx].
Qed.

Lemma amf_blocks_post_perm : forall T T' bl bl' L, amf_blocks_post T T' bl bl' -> Permutation bl (L ++ T) ->
Permutation bl' (L ++ T').
Proof.
intros T T' bl bl' L (D & -> & HP) HL.
apply (Permutation_trans HP). apply (Permutation_trans (Permutation_app_head D HL)).
rewrite (app_assoc L T D). apply Permutation_app_comm.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis ARL : AR_laws tfibsegs B.

(* Every kept block in the ledger is an application block with no image byte (FINV's finv_loc). *)
Lemma finv_loc_ledger : forall ly S (W : world tfibsegs) mem md T,
AR tfibsegs B ly S W mem md -> incl T (ablocks B ly S) -> finv_loc T.
Proof.
intros ly S W mem md T HAR HT f Hf.
pose proof (amf_block_facts tfibsegs B ARL ly S W mem md f HAR (HT _ Hf)) as (_ & _ & _ & Happ & Hby & _).
split; [exact Happ|]. intros a Ha. exact (proj2 (proj2 (Hby a Ha))).
Qed.

Lemma blocks_pairwise : forall ly S (W : world tfibsegs) mem md x L,
AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (x :: L) ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (x :: L)).
Proof.
intros ly S W mem md [p n] L HAR HP.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
exact (pairwise_zdisjoint_perm _ _ (Permutation_map _ HP) Hpw).
Qed.

(* The payload block is not a kept block. *)
Lemma kept_notin : forall ly S (W : world tfibsegs) mem md buf cap q n T,
AR tfibsegs B ly S W mem md -> 0 < n ->
Permutation (ablocks B ly S) ((buf, cap) :: (q, n) :: T) -> ~ In (q, n) T.
Proof.
intros ly S W mem md buf cap q n T HAR Hn HP Hin.
pose proof (blocks_pairwise ly S W mem md _ _ HAR HP) as Hpw. cbn [map pairwise fst snd] in Hpw.
destruct Hpw as [_ [F _]].
pose proof (proj1 (Forall_forall _ _) F (q, req_size n) (in_map (fun b => (fst b, req_size (snd b))) T (q, n) Hin)) as D.
unfold zdisjoint in D. cbn [fst snd] in D.
assert (R : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). rewrite R in D. lia.
Qed.

(* No byte of a kept block is a byte of the payload block. *)
Lemma kept_apart : forall ly S (W : world tfibsegs) mem md buf cap q n T a,
AR tfibsegs B ly S W mem md ->
Permutation (ablocks B ly S) ((buf, cap) :: (q, n) :: T) -> in_kept T a -> ~ (q <= a < q + req_size n).
Proof.
intros ly S W mem md buf cap q n T a HAR HP (f & Hin & Hfa) Ha.
pose proof (blocks_pairwise ly S W mem md _ _ HAR HP) as Hpw. cbn [map pairwise fst snd] in Hpw.
destruct Hpw as [_ [F _]].
pose proof (proj1 (Forall_forall _ _) F (f, req_size AMF_BLOCK)
  (in_map (fun b => (fst b, req_size (snd b))) T (f, AMF_BLOCK) Hin)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. replace (req_size AMF_BLOCK) with AMF_BLOCK in D by reflexivity. lia.
Qed.

(* The ledger after a free of the block (pf, nf): the rest of the blocks, at the same addresses. *)
Lemma ablocks_free_perm : forall ly S ly' S' l1 l2 pf nf L,
(forall b n, In (b, n) (blocks S) -> sptr_addr B ly' b = sptr_addr B ly b) ->
blocks S = l1 ++ (pf, nf) :: l2 -> blocks S' = l1 ++ l2 ->
Permutation (ablocks B ly S) ((sptr_addr B ly pf, nf) :: L) -> Permutation (ablocks B ly' S') L.
Proof.
intros ly S ly' S' l1 l2 pf nf L EXT E1 E2 HP.
assert (EQ : ablocks B ly' S' = map (fun b => (sptr_addr B ly (fst b), snd b)) (l1 ++ l2)).
{ unfold ablocks. rewrite E2. apply map_ext_in. intros [b n] Hb. cbn [fst snd]. f_equal. apply (EXT b n).
  rewrite E1. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
rewrite EQ. unfold ablocks in HP. rewrite E1, map_app in HP. cbn [map fst snd] in HP. rewrite map_app.
exact (Permutation_app_inv _ _ [] L _ HP).
Qed.

Lemma ablocks_same : forall ly S ly' S',
(forall b n, In (b, n) (blocks S) -> sptr_addr B ly' b = sptr_addr B ly b) -> blocks S' = blocks S ->
ablocks B ly' S' = ablocks B ly S.
Proof.
intros ly S ly' S' EXT E. unfold ablocks. rewrite E. apply map_ext_in. intros [b n] Hb. cbn [fst snd]. f_equal. exact (EXT b n Hb).
Qed.

(* A driver call site whose callee writes only the bytes E (no image byte, no kept byte) and the scratch keeps
   FINV T when the kept blocks stay in the ledger. *)
Lemma finv_site_kept : forall stk ly S (W : world tfibsegs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp T,
AR tfibsegs B ly S W mem md -> acall_post tfibsegs B stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> ~ in_img tfibsegs a) -> (forall a, in_kept T a -> ~ E a) ->
incl T (ablocks B ly S) -> incl T (ablocks B ly' S') ->
top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
FINV T (w_H W) mem -> FINV T (w_H W') mem'.
Proof.
intros stk ly S W regs mem md E ly' S' W' regs' mem' md' usp T HAR HP HEi HEk HT HT' (_ & Hlo & Hhi & HCT) Ulo Uhi Hsp Hstk HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
assert (SLO : ly_stk_lo ly <= spZ regs - stk) by (rewrite Hlo; unfold ASAN_CEIL, stack_max_size in *; lia).
assert (SHI : spZ regs <= ly_stk_hi ly) by (rewrite Hhi; unfold kHighMemEnd, sp_window_hi in *; lia).
assert (S24 : 2 ^ 24 <= spZ regs - stk) by (unfold sp_window_lo in *; lia).
pose proof (FINV_loc _ _ _ HFI) as HL.
pose proof HP as (HAR' & _ & _ & _ & _ & Hfr & _).
assert (KO : forall ly0 S0 (W0 : world tfibsegs) mem0 md0 a, AR tfibsegs B ly0 S0 W0 mem0 md0 ->
  incl T (ablocks B ly0 S0) -> in_kept T a -> ~ aowned B ly0 S0 a).
{ intros ly0 S0 W0 mem0 md0 a HA0 HT0 (f & Hin & Hfa).
  pose proof (amf_block_facts tfibsegs B ARL ly0 S0 W0 mem0 md0 f HA0 (HT0 _ Hin)) as (_ & _ & _ & _ & Hby & _).
  exact (proj1 (proj2 (Hby a Hfa))). }
apply (finv_aview (w_H W) (w_H W') mem mem'); [|exact HFI].
intros a Ha. apply Hfr.
- destruct Ha as [Ha|Ha]; [pose proof (finv_img_range a Ha); unfold pcap_img_end, YImgTop.IMG_TOP in *; lia|].
  destruct (finv_kept_place T a HL Ha) as [Hc _]. lia.
- destruct Ha as [Ha|Ha]; [| exact (KO ly S W mem md a HAR HT Ha)].
  intros Ho. exact (finv_img_not_owned B HB a Ha (proj1 (al_owned_image _ _ ARL ly S W mem md a HAR (finv_img_img a Ha)) Ho)).
- destruct Ha as [Ha|Ha]; [| exact (KO ly' S' W' mem' md' a HAR' HT' Ha)].
  intros Ho. exact (finv_img_not_owned B HB a Ha (proj1 (al_owned_image _ _ ARL ly' S' W' mem' md' a HAR' (finv_img_img a Ha)) Ho)).
- unfold ascratch. intros [Hsc | Her].
  + exact (finv_avoids_stack B ly S W mem md (spZ regs - stk) (spZ regs) a HAR HL SLO SHI S24 Ha Hsc).
  + destruct Ha as [Ha|Ha]; [exact (finv_img_not_errno B HB a Ha Her)|].
    destruct (finv_kept_place T a HL Ha) as [_ Hni]. apply Hni. apply in_img_hull.
    rewrite (ts_errno B HB) in Her. unfold TFIB_ERRNO in Her. unfold pcap_img_end, YImgTop.IMG_TOP. lia.
- destruct Ha as [Ha|Ha]; [intros Ea; exact (HEi a Ea (finv_img_img a Ha)) | exact (HEk a Ha)].
Qed.

End a.
