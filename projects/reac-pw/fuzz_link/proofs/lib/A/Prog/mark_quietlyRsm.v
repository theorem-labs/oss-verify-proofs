(* reac-pw/fuzz_link, image A: mark_quietly's later arm (0x883d4, listing
   (internal path) (internal record, sha256 83bb83545bf3)) from its entry to its tail jump
   into reac_served_mark (+0x70). Up to the jump the arm changes only the bytes of mark_quietlyDefs.v `mqa_X` (its
   window, the FILE block's first AMF_ZEROED bytes, g_said, errno) and grows presence (`mqa_agree`); the rewind leaves
   the FILE with its window empty (LinkMfDefs.v `amf_k` at 0); a0, a1 and sp at the jump are the entry's. Then:
   - mqa_rsm_pre: reac_served_mark's Pre at the jump;
   - mqa_rsm_rd: its read set at the jump is kept (`akb`) at its window, inside the caller's;
   - mqa_q: mark_quietly's later-arm Post from reac_served_mark's Post;
   - mqa_akept: mark_quietly's kept clause from its entry to the jump;
   - mqa_arodata: `arodata_okP` at the jump.
   Every byte the Pres read is outside mqa_X: a shadow byte lies in [kLowMemEnd, kHighShadowEnd), below the
   allocator's ceiling, off the heap and above g_said and errno; g_nl, g_sink, g_say, ofl_head and the .rodata
   literals (amk_policy_ok, each with its exact bytes) lie in [IMG_LO, IMG_TOP), off every heap block (LinkPaLib.v
   blk_off_imgP), below the ceiling and apart from g_said and errno (errno is TFIB_ERRNO, lib/A/AF0m.v); the name,
   the live table strings and the marks block lie apart from mqa_X by the Pre's own separations (`amq_globals` for
   g_said). A string's granule tail is read only as visible (`astr_rt_ok`'s tail clause, `amk_rd`'s spans) and
   moves, as `shadow_hull_vis` and writability do, by presence growth.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkMfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk LinkWalkNlk LinkWalkErrno
model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c mark_quietlyDefs PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. Computations over the image (no section hypothesis)
   ========================================================================== *)

(* every non-writable segment of the image lies apart from g_said *)
Lemma mq_ro_said : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? LA_G_SAID)
  || (LA_G_SAID + SAID_SIZE <=? Z.of_N (seg_base s))) AB1v.tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* g_sink, g_say and ofl_head: in one segment of the image each, and apart from every owned static range *)
Lemma mq_word_facts :
  existsb (relro_in_seg LA_G_SINK (LA_G_SINK + 8)) AB1v.tfibsegs = true /\
  existsb (relro_in_seg LA_G_SAY (LA_G_SAY + 8)) AB1v.tfibsegs = true /\
  existsb (relro_in_seg LA_OFL_HEAD (LA_OFL_HEAD + 8)) AB1v.tfibsegs = true /\
  forallb (fun r => (LA_G_SINK + 8 <=? fst r) || (fst r + snd r <=? LA_G_SINK)) AF0m.Tfib_owned_static = true /\
  forallb (fun r => (LA_G_SAY + 8 <=? fst r) || (fst r + snd r <=? LA_G_SAY)) AF0m.Tfib_owned_static = true /\
  forallb (fun r => (LA_OFL_HEAD + 8 <=? fst r) || (fst r + snd r <=? LA_OFL_HEAD)) AF0m.Tfib_owned_static = true.
Proof.
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. vm_compute; reflexivity.
Qed.

(* a closed comparison of constants *)
Ltac mq_cmp := repeat match goal with |- _ /\ _ => split end; apply Z.leb_le; vm_compute; reflexivity.

Lemma mq_list_ext : forall (A : Type) (l1 l2 : list A), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.

(* the memory relation, entry to jump *)
Definition mqa_agree (sp f : Z) (W : world SEGS) (memc memj : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ mqa_X B sp f a -> aview SEGS (w_H W) memj a = aview SEGS (w_H W) memc a)
  /\ mem_grows (rdW W memc) (rdW W memj).

(* ==========================================================================
   1. Moving a fact from m to m' (bytes that agree; presence that grows)
   ========================================================================== *)

Lemma mq_mb_of_av : forall H H' (m m' : word -> option byte) a,
  aview SEGS H' m' a = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H H' m m' a E. unfold aview in E.
  destruct (mbyte SEGS (mrestrict H' m') a) as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|]; cbn in E;
    try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma mq_vm_tr : forall (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> mbyte SEGS m' (a + Z.of_nat k) = mbyte SEGS m (a + Z.of_nat k)) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v E H k Hk. rewrite (E k Hk). exact (H k Hk). Qed.

Lemma mq_ab_tr : forall (m m' : word -> option byte) a bs,
  (forall i, (i < length bs)%nat -> mbyte SEGS m' (a + Z.of_nat i) = mbyte SEGS m (a + Z.of_nat i)) ->
  abytes SEGS m a bs -> abytes SEGS m' a bs.
Proof.
  intros m m' a bs E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (E i Hi). exact (H i Hi).
Qed.

Lemma mq_cstr_tr : forall (m m' : word -> option byte) p s,
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> mbyte SEGS m' x = mbyte SEGS m x) ->
  acstr_at SEGS m p s -> acstr_at SEGS m' p s.
Proof.
  intros m m' p s E [Hb Hn]. split; [|exact Hn]. apply (mq_ab_tr m m' p); [|exact Hb].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply E. lia.
Qed.

Lemma mq_wr_gr : forall (m m' : word -> option byte) a n,
  mem_grows m m' -> awrange SEGS m a n -> awrange SEGS m' a n.
Proof. intros m m' a n Hg H i Hi. exact (wview_grows SEGS m m' _ Hg (H i Hi)). Qed.

Lemma mq_u8_tr : forall (m m' : word -> option byte) a bs,
  mem_grows m m' ->
  (forall i, (i < length bs)%nat -> mbyte SEGS m' (a + Z.of_nat i) = mbyte SEGS m (a + Z.of_nat i)) ->
  au8arr SEGS m a bs -> au8arr SEGS m' a bs.
Proof.
  intros m m' a bs Hg E [Hb Hw].
  split; [exact (mq_ab_tr m m' a bs E Hb) | exact (mq_wr_gr m m' a _ Hg Hw)].
Qed.

Lemma mq_vis_gr : forall (m m' : word -> option byte) a,
  mem_grows m m' -> ard SEGS m a <> None -> ard SEGS m' a <> None.
Proof.
  intros m m' a Hg H. unfold ard, mbyte in *.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [cbn; discriminate|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [|exact H].
  exfalso. apply (Hg (Z_to_bv 64 a)); [rewrite E; discriminate | exact E'].
Qed.

Lemma mq_shv_gr : forall (m m' : word -> option byte) x n,
  mem_grows m m' -> shadow_hull_vis (ard SEGS m) x n -> shadow_hull_vis (ard SEGS m') x n.
Proof. intros m m' x n Hg H s Hs. exact (mq_vis_gr m m' s Hg (H s Hs)). Qed.

(* the shadow bytes of every application address agree *)
Definition mq_shag (m m' : word -> option byte) : Prop :=
  forall x, 0 <= x < kHighMemEnd -> mbyte SEGS m' (shadow_addr x) = mbyte SEGS m (shadow_addr x).

Lemma mq_ra_tr : forall (m m' : word -> option byte) a n,
  mq_shag m m' -> 0 <= a -> a + n <= kHighMemEnd ->
  range_addressable (ard SEGS m) SHADOW_OFF a n -> range_addressable (ard SEGS m') SHADOW_OFF a n.
Proof.
  intros m m' a n SH H0 H1 H. apply (ra_shadow_eq _ _ a n H).
  intros x Hx. unfold ard. rewrite (SH x ltac:(lia)). reflexivity.
Qed.

Lemma mq_amr_hi : forall p n, amem_range p n -> p + n <= kHighMemEnd.
Proof. intros p n H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. Qed.

Lemma mq_af : forall (regs regs' : bvmap 5 word) K K' a n,
  K' <= K -> spZ regs' = spZ regs -> apart_frame regs K a n -> apart_frame regs' K' a n.
Proof. intros regs regs' K K' a n HK Hs H. unfold apart_frame in *. rewrite Hs. lia. Qed.

Lemma mq_rt_tr : forall (m m' : word -> option byte) (regs regs' : bvmap 5 word) K K' p s,
  mem_grows m m' -> mq_shag m m' -> K' <= K -> spZ regs' = spZ regs ->
  astr_rt_ok SEGS regs K m p s -> astr_rt_ok SEGS regs' K' m' p s.
Proof.
  intros m m' regs regs' K K' p s Hg SH HK Hs (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  pose proof (mq_amr_hi _ _ H3) as Hh.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply (mq_ra_tr m m' p _ SH); [lia | lia | exact H4]|].
  split; [exact (mq_shv_gr m m' p _ Hg H5)|].
  split; [intros b Hb; exact (mq_vis_gr m m' b Hg (H6 b Hb))|].
  exact (mq_af regs regs' K K' p _ HK Hs H7).
Qed.

(* ==========================================================================
   2. What a memory fixes uniquely
   ========================================================================== *)

Lemma mq_cstr_rng : forall (m : word -> option byte) p s,
  acstr_at SEGS m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof. intros m p s [(H0 & H1 & _) _]. rewrite length_app in H1. cbn [length] in H1. lia. Qed.

Lemma mq_cstr_len : forall (m : word -> option byte) a s1 s2,
  acstr_at SEGS m a s1 -> acstr_at SEGS m a s2 -> (length s1 <= length s2)%nat.
Proof.
  intros m a s1 s2 [(_ & _ & H1) N1] [(_ & _ & H2) N2].
  destruct (Nat.le_gt_cases (length s1) (length s2)) as [|Hlt]; [assumption|]. exfalso.
  assert (L1 : (length s2 < length (s1 ++ [zb 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  assert (L2 : (length s2 < length (s2 ++ [zb 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (H1 _ L1) as E1. pose proof (H2 _ L2) as E2.
  rewrite nth_error_app1 in E1 by lia. rewrite nth_error_app2 in E2 by lia.
  rewrite Nat.sub_diag in E2. cbn [nth_error] in E2. rewrite E2 in E1.
  apply N1. apply (nth_error_In s1 (length s2)). symmetry. exact E1.
Qed.

Lemma mq_cstr_unique : forall (m : word -> option byte) a s1 s2,
  acstr_at SEGS m a s1 -> acstr_at SEGS m a s2 -> s1 = s2.
Proof.
  intros m a s1 s2 H1 H2.
  pose proof (mq_cstr_len m a s1 s2 H1 H2) as L1. pose proof (mq_cstr_len m a s2 s1 H2 H1) as L2.
  destruct H1 as [(_ & _ & B1) _]. destruct H2 as [(_ & _ & B2) _].
  apply lw_list_ext; [lia|]. intros k Hk.
  assert (K1 : (k < length (s1 ++ [zb 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  assert (K2 : (k < length (s2 ++ [zb 0]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (B1 k K1) as E1. pose proof (B2 k K2) as E2.
  rewrite nth_error_app1 in E1 by lia. rewrite nth_error_app1 in E2 by lia. congruence.
Qed.

Lemma mq_sarg_unique : forall (m : word -> option byte) a o1 o2,
  astr_arg SEGS m a o1 -> astr_arg SEGS m a o2 -> o1 = o2.
Proof.
  intros m a [s1|] [s2|]; unfold astr_arg; intros H1 H2.
  - f_equal. exact (mq_cstr_unique m a s1 s2 (proj2 H1) (proj2 H2)).
  - exfalso. exact (proj1 H1 H2).
  - exfalso. exact (proj1 H2 H1).
  - reflexivity.
Qed.

Lemma mq_vm_unique : forall (m : word -> option byte) a (n : nat) v1 v2,
  val_mem SEGS m a n v1 -> val_mem SEGS m a n v2 ->
  0 <= v1 < 2 ^ (8 * Z.of_nat n) -> 0 <= v2 < 2 ^ (8 * Z.of_nat n) -> v1 = v2.
Proof.
  intros m a n v1 v2 H1 H2 R1 R2.
  set (l := map (fun k => Z_to_bv 8 (le_byte v1 n k)) (seq 0 n)).
  assert (Hl : length l = n) by (unfold l; rewrite length_map, length_seq; reflexivity).
  assert (E1 : bytes_le_to_Z l = v1).
  { apply (lw_bytes_of_vals n l v1 Hl R1). intros k Hk. unfold l. rewrite lw_nth_error_map_seq by exact Hk.
    reflexivity. }
  assert (E2 : bytes_le_to_Z l = v2).
  { apply (lw_bytes_of_vals n l v2 Hl R2). intros k Hk. unfold l. rewrite lw_nth_error_map_seq by exact Hk.
    pose proof (H1 k Hk) as F1. pose proof (H2 k Hk) as F2. rewrite F1 in F2. exact F2. }
  congruence.
Qed.

Lemma mq_iftab_unique : forall (m : word -> option byte) g bs t1 t2,
  aiftab_at SEGS m g bs t1 -> aiftab_at SEGS m g bs t2 -> t1 = t2.
Proof.
  intros m g bs t1 t2 (N1 & _ & E1) (N2 & _ & E2).
  assert (L : length t1 = length t2) by lia.
  apply mq_list_ext. intros i.
  destruct (nth_error t1 i) as [[n1 x1]|] eqn:H1.
  - assert (Hi : (i < length t2)%nat) by (rewrite <- L; apply nth_error_Some; congruence).
    destruct (nth_error t2 i) as [[n2 x2]|] eqn:H2; [|apply nth_error_None in H2; lia].
    destruct (E1 i n1 x1 H1) as (R1 & p1 & P1 & _ & C1 & I1).
    destruct (E2 i n2 x2 H2) as (R2 & p2 & P2 & _ & C2 & I2).
    pose proof (mq_cstr_rng m p1 n1 C1) as Q1. pose proof (mq_cstr_rng m p2 n2 C2) as Q2.
    assert (Ep : p1 = p2).
    { apply (mq_vm_unique m _ 8 p1 p2 P1 P2); change (8 * Z.of_nat 8) with 64; lia. }
    subst p2. rewrite (mq_cstr_unique m p1 n1 n2 C1 C2).
    assert (Ex : x1 = x2).
    { apply (mq_vm_unique m _ 4 x1 x2 I1 I2); change (8 * Z.of_nat 4) with 32; lia. }
    subst x2. reflexivity.
  - destruct (nth_error t2 i) as [[n2 x2]|] eqn:H2; [|reflexivity].
    exfalso. apply nth_error_None in H1. assert (Hi : (i < length t2)%nat) by (apply nth_error_Some; congruence).
    lia.
Qed.

(* ==========================================================================
   3. The situation: mqa_X against the image, the heap block and the shadow
   ========================================================================== *)

Definition mq_ag (sp f : Z) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ mqa_X B sp f a -> mbyte SEGS m' a = mbyte SEGS m a.

Lemma mq_ag_of : forall sp f (W : world SEGS) memc memj,
  (forall a, 0 <= a < 2 ^ 64 -> ~ mqa_X B sp f a -> aview SEGS (w_H W) memj a = aview SEGS (w_H W) memc a) ->
  mq_ag sp f (rdW W memc) (rdW W memj).
Proof. intros sp f W memc memj AG a Ha Hx. exact (mq_mb_of_av _ _ memc memj a (AG a Ha Hx)). Qed.

(* the window above the ceiling, the FILE block a heap block off the image, errno at its image address *)
Definition mq_sit (sp f : Z) : Prop :=
  alloc_ceiling <= sp - MARK_QUIETLY_AK /\ 4096 <= f /\ in_app f AMF_BLOCK /\
  (f + AMF_BLOCK <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= f) /\ as_errno B = AF0m.TFIB_ERRNO.

Lemma mq_sit_of : forall lyc Sc (W : world SEGS) memc mdc sp f,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= sp - MARK_QUIETLY_AK -> In (f, AMF_BLOCK) (ablocks B lyc Sc) ->
  mq_sit sp f.
Proof.
  intros lyc Sc W memc mdc sp f HAR HC HF.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f AMF_BLOCK HAR HF) as (_ & H4 & _ & Happ & _).
  pose proof (blk_off_imgP B lyc Sc W memc mdc f AMF_BLOCK HAR HF) as Hoff.
  change (req_size AMF_BLOCK) with AMF_BLOCK in Happ, Hoff. unfold off_img in Hoff.
  split; [exact HC|]. split; [exact H4|]. split; [exact Happ|]. split; [exact Hoff | exact (AF0m.ts_errno B TB)].
Qed.

Lemma mq_shadow : forall sp f m m', mq_sit sp f -> mq_ag sp f m m' -> mq_shag m m'.
Proof.
  intros sp f m m' (HC & H4 & Happ & _ & He) AG x Hx.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hs : SHADOW_OFF <= shadow_addr x < kHighMemBeg).
  { unfold shadow_addr, SHADOW_OFF, kHighMemBeg. unfold kHighMemEnd in Hx. lia. }
  set (y := shadow_addr x) in *. clearbody y.
  apply AG; [unfold SHADOW_OFF, kHighMemBeg in Hs; lia|].
  unfold mqa_X. rewrite He.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, AMF_ZEROED, AMF_BLOCK, LA_G_SAID, SAID_SIZE,
    AF0m.TFIB_ERRNO in *.
  lia.
Qed.

Lemma mq_img : forall sp f m m', mq_sit sp f -> mq_ag sp f m m' ->
  forall x, YImgTop.IMG_LO <= x < YImgTop.IMG_TOP -> ~ (LA_G_SAID <= x < LA_G_SAID + SAID_SIZE) ->
  ~ (AF0m.TFIB_ERRNO <= x < AF0m.TFIB_ERRNO + 4) -> mbyte SEGS m' x = mbyte SEGS m x.
Proof.
  intros sp f m m' (HC & _ & _ & Hoff & He) AG x Hx Hs Herr.
  pose proof asan_consts as ((C1a & C1b) & _).
  apply AG; [unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hx; lia|].
  unfold mqa_X. rewrite He. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, AMF_ZEROED, AMF_BLOCK in *. lia.
Qed.

(* a range apart from the window, the FILE block, g_said and errno *)
Lemma mq_sep : forall sp f m m', mq_ag sp f m m' ->
  forall lo n, 0 <= lo -> lo + n <= 2 ^ 64 ->
  (lo + n <= sp - MARK_QUIETLY_AK \/ sp <= lo) -> (lo + n <= f \/ f + AMF_BLOCK <= lo) ->
  (lo + n <= LA_G_SAID \/ LA_G_SAID + SAID_SIZE <= lo) -> (lo + n <= as_errno B \/ as_errno B + 4 <= lo) ->
  forall x, lo <= x < lo + n -> mbyte SEGS m' x = mbyte SEGS m x.
Proof.
  intros sp f m m' AG lo n H0 H1 Hw Hf Hs He x Hx. apply AG; [lia|].
  unfold mqa_X, AMF_ZEROED, AMF_BLOCK in *. lia.
Qed.

Lemma mq_gnl : forall sp f m m', mq_sit sp f -> mq_ag sp f m m' ->
  forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte SEGS m' x = mbyte SEGS m x.
Proof.
  intros sp f m m' HS AG x Hx. apply (mq_img sp f m m' HS AG);
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_NL, NK_SIZE, LA_G_SAID, SAID_SIZE, AF0m.TFIB_ERRNO in *; lia.
Qed.

Lemma mq_word : forall sp f m m', mq_sit sp f -> mq_ag sp f m m' ->
  forall lo v, (lo = LA_G_SINK \/ lo = LA_G_SAY \/ lo = LA_OFL_HEAD) ->
  au64_at SEGS m lo v -> au64_at SEGS m' lo v.
Proof.
  intros sp f m m' HS AG lo v Hlo H. apply (mq_vm_tr m m' lo 8 v); [|exact H].
  intros k Hk. apply (mq_img sp f m m' HS AG);
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_SINK, LA_G_SAY, LA_OFL_HEAD, LA_G_SAID, SAID_SIZE,
      AF0m.TFIB_ERRNO in *; lia.
Qed.

(* a literal of [IMG_LO, 0x22000) (.rodata) *)
Lemma mq_lit : forall sp f m m', mq_sit sp f -> mq_ag sp f m m' ->
  forall p s, YImgTop.IMG_LO <= p -> p + Z.of_nat (length s) + 1 <= 0x22000 ->
  acstr_at SEGS m p s -> acstr_at SEGS m' p s.
Proof.
  intros sp f m m' HS AG p s H1 H2 C. apply (mq_cstr_tr m m' p s); [|exact C].
  intros x Hx. apply (mq_img sp f m m' HS AG);
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_SAID, SAID_SIZE, AF0m.TFIB_ERRNO in *; lia.
Qed.

(* ==========================================================================
   4. The pieces of the Pres
   ========================================================================== *)

(* amq_common's second conjunct: the name and the live table strings apart from the four globals *)
Definition mq_glob (regs : bvmap 5 word) (m : word -> option byte) (nm : option (list byte))
    (tab : list (list byte * Z)) : Prop :=
  forall g n, In (g, n) amq_globals ->
    (forall s, nm = Some s -> apart g n (aarg regs 1) (Z.of_nat (length s) + 8))
    /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
          au64_at SEGS m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
          apart g n p (Z.of_nat (length n2) + 1)).

Lemma mq_nlk : forall sp f m m', mq_sit sp f -> mq_ag sp f m m' -> mem_grows m m' ->
  forall bs, anlk_at SEGS m LA_G_NL bs -> anlk_at SEGS m' LA_G_NL bs.
Proof.
  intros sp f m m' HS AG Hg bs [Hu HL]. split; [|exact HL].
  apply (mq_u8_tr m m' LA_G_NL bs Hg); [|exact Hu].
  intros i Hi. apply (mq_gnl sp f m m' HS AG). lia.
Qed.

Lemma mq_iftab : forall sp f m m', mq_sit sp f -> mq_ag sp f m m' ->
  forall bs tab, aiftab_at SEGS m LA_G_NL bs tab ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) -> au64_at SEGS m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     acstr_at SEGS m p n2 -> forall x, p <= x < p + Z.of_nat (length n2) + 1 -> mbyte SEGS m' x = mbyte SEGS m x) ->
  aiftab_at SEGS m' LA_G_NL bs tab.
Proof.
  intros sp f m m' HS AG bs tab (N & L & E) ST. split; [exact N|]. split; [exact L|].
  intros i nm ix Hi. destruct (E i nm ix Hi) as (R & p & P & Pn & C & I).
  assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  split; [exact R|]. exists p. split; [|split; [exact Pn|split]].
  - apply (mq_vm_tr m m' _ 8 p); [|exact P]. intros k Hk. apply (mq_gnl sp f m m' HS AG).
    unfold NK_IF_NAME, NK_SIZE in *. lia.
  - exact (mq_cstr_tr m m' p nm (ST i nm ix p Hi P C) C).
  - apply (mq_vm_tr m m' _ 4 ix); [|exact I]. intros k Hk. apply (mq_gnl sp f m m' HS AG).
    unfold NK_IF_INDEX, NK_SIZE in *. lia.
Qed.

(* the name string's bytes: the Pre's separations *)
Lemma mq_name_bytes : forall f m m' (regs : bvmap 5 word) nm tab s,
  mq_ag (spZ regs) f m m' -> astr_arg SEGS m (aarg regs 1) nm ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK f AMF_BLOCK m nm -> mq_glob regs m nm tab -> nm = Some s ->
  forall x, aarg regs 1 <= x < aarg regs 1 + Z.of_nat (length s) + 1 -> mbyte SEGS m' x = mbyte SEGS m x.
Proof.
  intros f m m' regs nm tab s AG HA HN HX Es x Hx. subst nm.
  destruct HA as [_ C]. destruct (mq_cstr_rng m _ s C) as [R0 R1].
  destruct (HN s eq_refl) as (_ & (_ & _ & _ & _ & _ & _ & AF) & _ & AFB & AE & _).
  pose proof (proj1 (HX LA_G_SAID SAID_SIZE ltac:(unfold amq_globals; right; left; reflexivity)) s eq_refl) as AS.
  unfold apart_frame, apart in *.
  apply (mq_sep _ f m m' AG (aarg regs 1) (Z.of_nat (length s) + 1)); lia.
Qed.

(* a live table string's bytes: the Pre's separations *)
Lemma mq_tab_bytes : forall f m m' (regs : bvmap 5 word) nm tab,
  mq_ag (spZ regs) f m m' -> amk_table_ok SEGS B regs MARK_QUIETLY_AK f AMF_BLOCK m tab ->
  mq_glob regs m nm tab ->
  forall i n2 ix p, nth_error tab i = Some (n2, ix) -> au64_at SEGS m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  acstr_at SEGS m p n2 -> forall x, p <= x < p + Z.of_nat (length n2) + 1 -> mbyte SEGS m' x = mbyte SEGS m x.
Proof.
  intros f m m' regs nm tab AG HT HX i n2 ix p Hi Hp C x Hx.
  destruct (mq_cstr_rng m p n2 C) as [R0 R1].
  destruct (HT i n2 ix p Hi Hp ltac:(lia)) as ((_ & _ & _ & _ & _ & _ & AF) & _ & AE & AFB & _).
  pose proof (proj2 (HX LA_G_SAID SAID_SIZE ltac:(unfold amq_globals; right; left; reflexivity)) i n2 ix p Hi Hp
    ltac:(lia)) as AS.
  unfold apart_frame, apart in *.
  apply (mq_sep _ f m m' AG p (Z.of_nat (length n2) + 1)); lia.
Qed.

(* the marks block's bytes: the Pre's separations, and above the image's top (g_said is below it) *)
Lemma mq_marks_bytes : forall f m m' (regs : bvmap 5 word) bl,
  mq_ag (spZ regs) f m m' -> (aarg regs 0 <> 0 -> amarks_ledger bl (aarg regs 0)) ->
  amk_block_ok SEGS B regs MARK_QUIETLY_AK f AMF_BLOCK m -> aarg regs 0 <> 0 ->
  forall x, aarg regs 0 <= x < aarg regs 0 + MK_SIZE -> mbyte SEGS m' x = mbyte SEGS m x.
Proof.
  intros f m m' regs bl AG HL HB Hn x Hx.
  destruct (HB Hn) as ((M1 & M2 & _ & _ & _ & M6) & _ & G2 & G3 & _).
  destruct (HL Hn) as [_ Htop]. pose proof (mq_amr_hi _ _ M2) as Hh.
  unfold apart_frame, apart in *.
  unfold YCbq.off_img in Htop.
  apply (mq_sep _ f m m' AG (aarg regs 0) MK_SIZE);
    unfold kHighMemEnd, MK_SIZE, YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_SAID, SAID_SIZE in *; destruct Htop as [Htop | Htop]; lia.
Qed.

Lemma mq_nlk_ok : forall f m m' (regs : bvmap 5 word) kbs tab nm,
  mq_sit (spZ regs) f -> mq_ag (spZ regs) f m m' -> mem_grows m m' -> mq_shag m m' ->
  amk_table_ok SEGS B regs MARK_QUIETLY_AK f AMF_BLOCK m tab -> mq_glob regs m nm tab ->
  amk_nlk_ok SEGS m kbs tab 2 -> amk_nlk_ok SEGS m' kbs tab 2.
Proof.
  intros f m m' regs kbs tab nm HS AG Hg SH HT HX (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
  split; [exact (mq_nlk _ f m m' HS AG Hg kbs N1)|].
  do 4 (split; [assumption|]).
  split; [exact (mq_iftab _ f m m' HS AG kbs tab N6 (mq_tab_bytes f m m' regs nm tab AG HT HX))|].
  split; [apply (mq_ra_tr m m' _ _ SH); [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE, kHighMemEnd; lia | exact N7]|].
  exact (mq_shv_gr m m' _ _ Hg N8).
Qed.

Lemma mq_errno_tr : forall sp f m m' (regs regs' : bvmap 5 word) fb fn,
  mq_sit sp f -> mem_grows m m' -> mq_shag m m' -> spZ regs' = spZ regs -> aarg regs' 0 = aarg regs 0 ->
  amk_errno_ok SEGS B regs MARK_QUIETLY_AK fb fn m -> amk_errno_ok SEGS B regs' REAC_SERVED_MARK_AK fb fn m'.
Proof.
  intros sp f m m' regs regs' fb fn (_ & _ & _ & _ & He) Hg SH Hsp Ha0 (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  split; [exact E1|]. split; [exact (mq_wr_gr m m' _ _ Hg E2)|].
  split; [apply (mq_ra_tr m m' _ _ SH);
    [rewrite He; unfold AF0m.TFIB_ERRNO; lia | rewrite He; unfold AF0m.TFIB_ERRNO, kHighMemEnd; lia | exact E3]|].
  split; [exact (mq_af regs regs' _ _ _ _ MARK_QUIETLY_AK_covers_tail Hsp E4)|].
  split; [exact E5|]. split; [exact E6|]. rewrite Ha0. exact E7.
Qed.

Lemma mq_table_tr : forall f m m' (regs regs' : bvmap 5 word) tab,
  mq_sit (spZ regs) f -> mq_ag (spZ regs) f m m' -> mem_grows m m' -> mq_shag m m' -> spZ regs' = spZ regs ->
  aarg regs' 0 = aarg regs 0 -> Z.of_nat (length tab) <= 80 ->
  amk_table_ok SEGS B regs MARK_QUIETLY_AK f AMF_BLOCK m tab ->
  amk_table_ok SEGS B regs' REAC_SERVED_MARK_AK f AMF_BLOCK m' tab.
Proof.
  intros f m m' regs regs' tab HS AG Hg SH Hsp Ha0 L80 HT i n2 ix p Hi Hp Hr.
  assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  assert (Hp0 : au64_at SEGS m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { apply (mq_vm_tr m' m _ 8 p); [|exact Hp]. intros k Hk. symmetry. apply (mq_gnl _ f m m' HS AG).
    unfold NK_IF_NAME, NK_SIZE. lia. }
  destruct (HT i n2 ix p Hi Hp0 Hr) as (RT & G1 & G2 & G3 & G4).
  split; [exact (mq_rt_tr m m' regs regs' _ _ p n2 Hg SH MARK_QUIETLY_AK_covers_tail Hsp RT)|].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. rewrite Ha0. exact G4.
Qed.

Lemma mq_arg_tr : forall f m m' (regs : bvmap 5 word) nm tab,
  mq_ag (spZ regs) f m m' -> astr_arg SEGS m (aarg regs 1) nm ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK f AMF_BLOCK m nm -> mq_glob regs m nm tab ->
  astr_arg SEGS m' (aarg regs 1) nm.
Proof.
  intros f m m' regs nm tab AG HA HN HX. destruct nm as [s|]; [|exact HA].
  pose proof (mq_name_bytes f m m' regs (Some s) tab s AG HA HN HX eq_refl) as E.
  destruct HA as [Hn C]. split; [exact Hn|]. exact (mq_cstr_tr m m' _ s E C).
Qed.

Lemma mq_name_tr : forall f m m' (regs regs' : bvmap 5 word) nm,
  mem_grows m m' -> mq_shag m m' -> spZ regs' = spZ regs -> aarg regs' 0 = aarg regs 0 ->
  aarg regs' 1 = aarg regs 1 ->
  amk_name_ok SEGS B regs MARK_QUIETLY_AK f AMF_BLOCK m nm ->
  amk_name_ok SEGS B regs' REAC_SERVED_MARK_AK f AMF_BLOCK m' nm.
Proof.
  intros f m m' regs regs' nm Hg SH Hsp Ha0 Ha1 HN s Hs. rewrite Ha0, Ha1.
  destruct (HN s Hs) as (L & RT & G1 & G2 & G3 & G4).
  split; [exact L|]. split; [|exact (conj G1 (conj G2 (conj G3 G4)))].
  exact (mq_rt_tr m m' regs regs' _ _ _ s Hg SH MARK_QUIETLY_AK_covers_tail Hsp RT).
Qed.

Lemma mq_marks_tr : forall f m m' (regs regs' : bvmap 5 word) bl,
  mq_ag (spZ regs) f m m' -> mem_grows m m' -> mq_shag m m' -> spZ regs' = spZ regs ->
  aarg regs' 0 = aarg regs 0 -> (aarg regs 0 <> 0 -> amarks_ledger bl (aarg regs 0)) ->
  amk_block_ok SEGS B regs MARK_QUIETLY_AK f AMF_BLOCK m ->
  amk_block_ok SEGS B regs' REAC_SERVED_MARK_AK f AMF_BLOCK m'.
Proof.
  intros f m m' regs regs' bl AG Hg SH Hsp Ha0 HL HB. unfold amk_block_ok. rewrite Ha0. intros Hn.
  pose proof (mq_marks_bytes f m m' regs bl AG HL HB Hn) as E.
  destruct (HB Hn) as ((M1 & M2 & M3 & M4 & M5 & M6) & G1 & G2 & G3 & gbs & Hm & Hwf).
  pose proof (mq_amr_hi _ _ M2) as Hh.
  split; [|split; [exact G1|split; [exact G2|split; [exact G3|]]]].
  - split; [exact M1|]. split; [exact M2|].
    split; [apply (mq_ra_tr m m' _ _ SH); [lia | unfold MK_SIZE in *; lia | exact M3]|].
    split; [exact (mq_shv_gr m m' _ _ Hg M4)|].
    split; [intros b Hb; exact (mq_vis_gr m m' b Hg (M5 b Hb))|].
    exact (mq_af regs regs' _ _ _ _ MARK_QUIETLY_AK_covers_tail Hsp M6).
  - exists gbs. split; [|exact Hwf]. destruct Hm as [Hu HLn]. split; [|exact HLn].
    apply (mq_u8_tr m m' _ gbs Hg); [|exact Hu]. intros i Hi. apply E. lia.
Qed.

Lemma mq_blk_tr : forall sp f m m' (regs regs' : bvmap 5 word),
  mq_sit sp f -> mem_grows m m' -> mq_shag m m' -> spZ regs' = spZ regs ->
  amf_blk_ok SEGS regs MARK_QUIETLY_AK m f -> amf_blk_ok SEGS regs' REAC_SERVED_MARK_AK m' f.
Proof.
  intros sp f m m' regs regs' (_ & H4 & _) Hg SH Hsp (B1 & B2 & B3 & B4).
  pose proof (mq_amr_hi _ _ B1) as Hh.
  split; [exact B1|]. split; [apply (mq_ra_tr m m' _ _ SH); [lia | unfold AMF_BLOCK in *; lia | exact B2]|].
  split; [exact (mq_shv_gr m m' _ _ Hg B3)|].
  exact (mq_af regs regs' _ _ _ _ MARK_QUIETLY_AK_covers_tail Hsp B4).
Qed.

(* the FILE at the jump: the rewind's FILE and window, the two writable ranges by presence growth *)
Lemma mq_mf0 : forall (m m' : word -> option byte) f,
  mem_grows m m' -> (exists k, amemfile_k SEGS m f k) -> LinkMfDefs.amf_k SEGS link_amf m' f 0 ->
  amemfile_k SEGS m' f 0.
Proof.
  intros m m' f Hg (k & _ & _ & W1 & W2) (A & Wn).
  split; [exact A|]. split; [exact Wn|].
  split; [exact (mq_wr_gr m m' _ _ Hg W1) | exact (mq_wr_gr m m' _ _ Hg W2)].
Qed.

(* the thirteen literals, each with its exact bytes, all in [IMG_LO, 0x22000) *)
Lemma mq_policy : forall sp f m m' (regs regs' : bvmap 5 word),
  mq_sit sp f -> mq_ag sp f m m' -> mem_grows m m' -> spZ regs' = spZ regs ->
  amk_policy_ok SEGS regs MARK_QUIETLY_AK m -> amk_policy_ok SEGS regs' REAC_SERVED_MARK_AK m'.
Proof.
  intros sp f m m' regs regs' HS AG Hg Hsp
    (P1 & R1 & P2 & R2 & P3 & R3 & P4 & R4 & P5 & R5 & P6 & R6 & P7 & R7 & P8 & R8 & P9 & R9 & P10 & R10 & P11 & R11
     & P12 & R12 & P13 & R13).
  pose proof (mq_shadow sp f _ _ HS AG) as SH.
  pose proof MARK_QUIETLY_AK_covers_tail as HKK.
  assert (RT : forall p s, astr_rt_ok SEGS regs MARK_QUIETLY_AK m p s ->
            astr_rt_ok SEGS regs' REAC_SERVED_MARK_AK m' p s)
    by (intros p s; exact (mq_rt_tr _ _ regs regs' _ _ p s Hg SH HKK Hsp)).
  assert (LT : forall p s, YImgTop.IMG_LO <= p -> p + Z.of_nat (length s) + 1 <= 0x22000 ->
            acstr_at SEGS m p s -> acstr_at SEGS m' p s)
    by (intros p s; exact (mq_lit sp f _ _ HS AG p s)).
  split; [apply LT; [mq_cmp | mq_cmp | exact P1]|]. split; [exact (RT _ _ R1)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P2]|]. split; [exact (RT _ _ R2)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P3]|]. split; [exact (RT _ _ R3)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P4]|]. split; [exact (RT _ _ R4)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P5]|]. split; [exact (RT _ _ R5)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P6]|]. split; [exact (RT _ _ R6)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P7]|]. split; [exact (RT _ _ R7)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P8]|]. split; [exact (RT _ _ R8)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P9]|]. split; [exact (RT _ _ R9)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P10]|]. split; [exact (RT _ _ R10)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P11]|]. split; [exact (RT _ _ R11)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P12]|]. split; [exact (RT _ _ R12)|].
  split; [apply LT; [mq_cmp | mq_cmp | exact P13]|]. exact (RT _ _ R13).
Qed.

(* ==========================================================================
   5. The five lemmas
   ========================================================================== *)

Lemma mqa_rsm_pre : forall sink lyc Sc (W : world SEGS) memc memj mdc (regs regsj : bvmap 5 word),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  mark_quietly_apre_again SEGS B sink (ablocks B lyc Sc) regs (rdW W memc) ->
  mqa_agree (spZ regs) sink W memc memj ->
  LinkMfDefs.amf_k SEGS link_amf (rdW W memj) sink 0 ->
  aarg regsj 0 = aarg regs 0 -> aarg regsj 1 = aarg regs 1 -> spZ regsj = spZ regs ->
  reac_served_mark_apre SEGS B sink (ablocks B lyc Sc) regsj (rdW W memj).
Proof.
  intros sink lyc Sc W memc memj mdc regs regsj HAR HC HP [AGv Hg] HMF Ha0 Ha1 Hsp.
  destruct HP as (HF & _ & Hs0 & HCX & HK & Hsay & _ & HBO & _).
  destruct HCX as (kbs & tab & nm & HL & HFIX & HNLK & HERR & Esay & Esaid & _ & _ & HTAB & HPOL & HARG & HNAME
    & HBLK).
  pose proof (mq_sit_of lyc Sc W memc mdc (spZ regs) sink HAR HC HF) as HS.
  pose proof (mq_ag_of (spZ regs) sink W memc memj AGv) as AG.
  pose proof (mq_shadow _ _ _ _ HS AG) as SH.
  pose proof HNLK as (_ & _ & _ & _ & _ & (_ & L80 & _) & _).
  exists kbs, tab, nm, 0.
  split; [exact HF|].
  split; [rewrite Ha0; exact HL|].
  split; [exact (mq_nlk_ok sink _ _ regs kbs tab nm HS AG Hg SH HTAB HFIX HNLK)|].
  split; [exact (mq_errno_tr _ sink _ _ regs regsj sink AMF_BLOCK HS Hg SH Hsp Ha0 HERR)|].
  split; [exact Esay|]. split; [exact Esaid|].
  split; [exact (mq_table_tr sink _ _ regs regsj tab HS AG Hg SH Hsp Ha0 L80 HTAB)|].
  split; [exact (mq_policy _ sink _ _ regs regsj HS AG Hg Hsp HPOL)|].
  split; [exact (mq_word _ sink _ _ HS AG LA_G_SAY sink (or_intror (or_introl eq_refl)) Hsay)|].
  split; [exact Hs0|].
  split; [exact (mq_mf0 _ _ sink Hg HK HMF)|].
  split; [unfold MARK_LINE_MAX, AMF_BUFSIZ; lia|].
  split; [exact (mq_blk_tr _ sink _ _ regs regsj HS Hg SH Hsp HBO)|].
  split; [rewrite Ha1; exact (mq_arg_tr sink _ _ regs nm tab AG HARG HNAME HFIX)|].
  split; [exact (mq_name_tr sink _ _ regs regsj nm Hg SH Hsp Ha0 Ha1 HNAME)|].
  exact (mq_marks_tr sink _ _ regs regsj _ AG Hg SH Hsp Ha0 HL HBLK).
Qed.

Lemma mq_akb_mono : forall lyc Sc sp K K' a, K' <= K ->
  akb SEGS B lyc Sc (sp - K) sp a -> akb SEGS B lyc Sc (sp - K') sp a.
Proof.
  intros lyc Sc sp K K' a HK [(H1 & H2)|H]; [left; split; [exact H1 | lia] | right; exact H].
Qed.

Lemma mqa_rsm_rd : forall sink lyc Sc (W : world SEGS) memc memj mdc (regs regsj : bvmap 5 word),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  mark_quietly_apre_again SEGS B sink (ablocks B lyc Sc) regs (rdW W memc) ->
  (forall a, amk_rd SEGS regs (rdW W memc) a -> akb SEGS B lyc Sc (spZ regs - MARK_QUIETLY_AK) (spZ regs) a) ->
  mqa_agree (spZ regs) sink W memc memj ->
  aarg regsj 0 = aarg regs 0 -> aarg regsj 1 = aarg regs 1 -> spZ regsj = spZ regs ->
  forall a, amk_rd SEGS regsj (rdW W memj) a ->
    akb SEGS B lyc Sc (spZ regsj - REAC_SERVED_MARK_AK) (spZ regsj) a.
Proof.
  intros sink lyc Sc W memc memj mdc regs regsj HAR HC HP HRD [AGv Hg] Ha0 Ha1 Hsp a Ha.
  destruct HP as (HF & _ & _ & HCX & _).
  destruct HCX as (kbs & tab & nm & _ & HFIX & HNLK & _ & _ & _ & _ & _ & HTAB & _ & HARG & HNAME & _).
  pose proof (mq_sit_of lyc Sc W memc mdc (spZ regs) sink HAR HC HF) as HS.
  pose proof (mq_ag_of (spZ regs) sink W memc memj AGv) as AG.
  rewrite Hsp. apply (mq_akb_mono lyc Sc (spZ regs) MARK_QUIETLY_AK REAC_SERVED_MARK_AK a MARK_QUIETLY_AK_covers_tail).
  apply HRD.
  destruct Ha as [H1|[H2|H3]].
  - left. destruct H1 as (Hn & s' & C' & Hr). rewrite Ha1 in Hn, C', Hr.
    destruct nm as [s|]; [|exfalso; exact (Hn HARG)].
    pose proof (mq_cstr_tr _ _ _ s (mq_name_bytes sink _ _ regs (Some s) tab s AG HARG HNAME HFIX eq_refl)
      (proj2 HARG)) as C.
    rewrite (mq_cstr_unique _ _ s' s C' C) in Hr.
    split; [exact Hn|]. exists s. split; [exact (proj2 HARG) | exact Hr].
  - right; left; exact H2.
  - right; right. destruct H3 as (bs & tab' & i & n2 & ix & p & Hn' & Hi' & Ht & Hp & Hc & Hr).
    destruct HNLK as (Hn & _ & _ & _ & _ & Hi & _).
    pose proof (mq_nlk _ sink _ _ HS AG Hg kbs Hn) as Hn2.
    pose proof (anlk_at_unique SEGS _ _ _ _ Hn' Hn2) as Eb. subst bs.
    pose proof (mq_iftab _ sink _ _ HS AG kbs tab Hi (mq_tab_bytes sink _ _ regs nm tab AG HTAB HFIX)) as Hi2.
    pose proof (mq_iftab_unique _ _ _ _ _ Hi' Hi2) as Et. subst tab'.
    pose proof Hi as (_ & L80 & EI).
    destruct (EI i n2 ix Ht) as (_ & p0 & P0 & _ & C0 & _).
    assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; congruence).
    assert (P0' : au64_at SEGS (rdW W memj) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0).
    { apply (mq_vm_tr (rdW W memc) (rdW W memj) _ 8 p0); [|exact P0]. intros k Hk. apply (mq_gnl _ sink _ _ HS AG).
      unfold NK_IF_NAME, NK_SIZE in *. lia. }
    pose proof (mq_cstr_rng _ p n2 Hc) as Q1. pose proof (mq_cstr_rng _ p0 n2 C0) as Q0.
    assert (Ep : p = p0).
    { apply (mq_vm_unique _ _ 8 p p0 Hp P0'); change (8 * Z.of_nat 8) with 64; lia. }
    subst p0. exists kbs, tab, i, n2, ix, p.
    split; [exact Hn|]. split; [exact Hi|]. split; [exact Ht|]. split; [exact P0|]. split; [exact C0 | exact Hr].
Qed.

(* a word of the image that akept keeps: in a segment, not an owned static, not errno, not written *)
Lemma mq_in_img : forall lo n, existsb (relro_in_seg lo (lo + n)) AB1v.tfibsegs = true ->
  forall a, lo <= a < lo + n -> in_img SEGS a.
Proof.
  intros lo n Hb a Ha. rewrite HSEGS. destruct (proj1 (existsb_exists _ _) Hb) as (s & Hin & H).
  unfold relro_in_seg in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H3. exists s. split; [exact Hin | lia].
Qed.

Lemma mq_not_owned : forall lo n,
  forallb (fun r => (lo + n <=? fst r) || (fst r + snd r <=? lo)) AF0m.Tfib_owned_static = true ->
  forall a, lo <= a < lo + n -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
  intros lo n Hb a Ha HE. rewrite (AF0m.ts_owned B TB) in HE.
  apply Exists_exists in HE as (r & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) Hb r Hin) as H. apply orb_true_iff in H.
  unfold in_zr in Hr. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma mq_word_kept : forall lyc Sc (W : world SEGS) memj (W2 : world SEGS) mem2 slo shi (E : Z -> Prop) lo v,
  akept SEGS B lyc Sc W memj W2 mem2 slo shi E ->
  existsb (relro_in_seg lo (lo + 8)) AB1v.tfibsegs = true ->
  forallb (fun r => (lo + 8 <=? fst r) || (fst r + snd r <=? lo)) AF0m.Tfib_owned_static = true ->
  (lo + 8 <= as_errno B \/ as_errno B + 4 <= lo) ->
  (forall a, lo <= a < lo + 8 -> ~ E a) ->
  au64_at SEGS (rdW W memj) lo v -> au64_at SEGS (rdW W2 mem2) lo v.
Proof.
  intros lyc Sc W memj W2 mem2 slo shi E lo v HK Hi Ho He HE Hv.
  apply (mq_vm_tr (rdW W memj) (rdW W2 mem2) lo 8 v); [|exact Hv].
  intros k Hk. apply mq_mb_of_av. destruct HK as (_ & _ & K3 & _).
  apply K3.
  - apply (mq_in_img lo 8 Hi). lia.
  - apply (mq_not_owned lo 8 Ho). lia.
  - lia.
  - apply HE. lia.
Qed.

Lemma mq_not_wr : forall sink (regsj : bvmap 5 word) m lo,
  (sink + AMF_BLOCK <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= sink) ->
  (aarg regsj 0 <> 0 -> YCbq.off_img (aarg regsj 0) MK_SIZE) ->
  LA_G_NL + NK_N_SENT + 4 <= lo -> YImgTop.IMG_LO <= lo -> lo + 8 <= YImgTop.IMG_TOP ->
  forall a, lo <= a < lo + 8 -> ~ inFP (reac_served_mark_awr sink regsj m) a.
Proof.
  intros sink regsj m lo Hoff Hm H1 H2 H3 a Ha (r & Hin & Hr).
  unfold reac_served_mark_awr in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[]]]]; subst r; cbn [fst snd] in Hr.
  - lia.
  - unfold aivl in Hr. cbn [fst snd] in Hr. revert Hr.
    destruct (Z.eqb_spec (aarg regsj 0) 0) as [E0|E0]; intros Hr; [lia|].
    pose proof (Hm E0) as Hm0. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    unfold MK_SIZE in *. destruct Hm0 as [Hm0 | Hm0]; lia.
  - unfold aivl in Hr. cbn [fst snd] in Hr. revert Hr.
    destruct (Z.eqb_spec sink 0) as [E0|E0]; intros Hr; [lia|]. unfold AMF_BLOCK in *. lia.
Qed.

Lemma mqa_q : forall sink lyc Sc (W : world SEGS) memc memj mdc (regs regsj : bvmap 5 word)
    (W2 : world SEGS) (regs2 : bvmap 5 word) mem2,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  mark_quietly_apre_again SEGS B sink (ablocks B lyc Sc) regs (rdW W memc) ->
  mqa_agree (spZ regs) sink W memc memj ->
  LinkMfDefs.amf_k SEGS link_amf (rdW W memj) sink 0 ->
  aarg regsj 0 = aarg regs 0 -> aarg regsj 1 = aarg regs 1 -> spZ regsj = spZ regs ->
  akept SEGS B lyc Sc W memj W2 mem2 (spZ regsj - REAC_SERVED_MARK_AK) (spZ regsj)
    (fun a => inFP (reac_served_mark_awr sink regsj (rdW W memj)) a) ->
  reac_served_mark_apost SEGS sink regsj (rdW W memj) regs2 (rdW W2 mem2) ->
  mark_quietly_apost_again SEGS sink regs (rdW W memc) regs2 (rdW W2 mem2).
Proof.
  intros sink lyc Sc W memc memj mdc regs regsj W2 regs2 mem2 HAR HC HP [AGv Hg] HMF Ha0 Ha1 Hsp HKP HQ.
  destruct HP as (HF & Hsink & Hs0 & HCX & HK & Hsay & Hofl & _).
  destruct HCX as (kbs & tab & nm & HL & HFIX & HNLK & _ & _ & _ & _ & _ & HTAB & _ & HARG & HNAME & HBLK).
  pose proof (mq_sit_of lyc Sc W memc mdc (spZ regs) sink HAR HC HF) as HS.
  pose proof (mq_ag_of (spZ regs) sink W memc memj AGv) as AG.
  pose proof HS as (_ & _ & _ & Hoff & He).
  pose proof mq_word_facts as (I1 & I2 & I3 & O1 & O2 & O3).
  assert (Hm : aarg regsj 0 <> 0 -> YCbq.off_img (aarg regsj 0) MK_SIZE)
    by (rewrite Ha0; intros H0; exact (proj2 (HL H0))).
  assert (KW : forall lo v, (lo = LA_G_SINK \/ lo = LA_G_SAY \/ lo = LA_OFL_HEAD) ->
    existsb (relro_in_seg lo (lo + 8)) AB1v.tfibsegs = true ->
    forallb (fun r => (lo + 8 <=? fst r) || (fst r + snd r <=? lo)) AF0m.Tfib_owned_static = true ->
    au64_at SEGS (rdW W memc) lo v -> au64_at SEGS (rdW W2 mem2) lo v).
  { intros lo v Hlo Hi Ho Hv.
    apply (mq_word_kept lyc Sc W memj W2 mem2 _ _ _ lo v HKP Hi Ho).
    - rewrite He. unfold LA_G_SINK, LA_G_SAY, LA_OFL_HEAD, AF0m.TFIB_ERRNO in *. lia.
    - apply (mq_not_wr sink regsj _ lo Hoff Hm);
        unfold LA_G_NL, NK_N_SENT, YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_SINK, LA_G_SAY, LA_OFL_HEAD in *; lia.
    - exact (mq_word _ sink _ _ HS AG lo v Hlo Hv). }
  destruct HQ as (Q1 & Q2 & Q3).
  split; [exact (KW _ _ (or_introl eq_refl) I1 O1 Hsink)|].
  split; [exact (KW _ _ (or_intror (or_introl eq_refl)) I2 O2 Hsay)|].
  split; [exact (KW _ _ (or_intror (or_intror eq_refl)) I3 O3 Hofl)|].
  split.
  - destruct (Q1 0 (mq_mf0 _ _ sink Hg HK HMF)) as (k' & Hk' & Hmf).
    exists k'. split; [lia | exact Hmf].
  - destruct HNLK as (Hn & _ & _ & _ & _ & Hi & _).
    split.
    + intros H0. rewrite <- Ha0 in H0. destruct (Q2 H0) as (R & N). split; [exact R|].
      intros bs Hb. apply N. exact (mq_nlk _ sink _ _ HS AG Hg bs Hb).
    + intros H0 bs tab' nm' gbs Hb Ht Ha Hmk.
      pose proof (anlk_at_unique SEGS _ _ _ _ Hb Hn) as Eb. subst bs.
      pose proof (mq_iftab_unique _ _ _ _ _ Ht Hi) as Et. subst tab'.
      pose proof (mq_sarg_unique _ _ _ _ Ha HARG) as En. subst nm'.
      assert (H0j : aarg regsj 0 <> 0) by (rewrite Ha0; exact H0).
      assert (Hmk' : amarks_at SEGS (rdW W memj) (aarg regsj 0) gbs).
      { rewrite Ha0. destruct Hmk as [Hu HLn]. split; [|exact HLn].
        apply (mq_u8_tr _ _ _ gbs Hg); [|exact Hu]. intros i Hi'.
        apply (mq_marks_bytes sink _ _ regs _ AG HL HBLK H0). lia. }
      assert (Ha' : astr_arg SEGS (rdW W memj) (aarg regsj 1) nm)
        by (rewrite Ha1; exact (mq_arg_tr sink _ _ regs nm tab AG HARG HNAME HFIX)).
      pose proof (Q3 H0j kbs tab nm gbs (mq_nlk _ sink _ _ HS AG Hg kbs Hn)
        (mq_iftab _ sink _ _ HS AG kbs tab Hi (mq_tab_bytes sink _ _ regs nm tab AG HTAB HFIX)) Ha' Hmk') as R.
      rewrite Ha0 in R. exact R.
Qed.

Lemma mqa_akept : forall sink lyc Sc (W : world SEGS) memc memj mdc (regs : bvmap 5 word),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK -> sink <> 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mqa_X B (spZ regs) sink a -> aview SEGS (w_H W) memj a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memj a) ->
  (forall a, spZ regs - MARK_QUIETLY_AK <= a < spZ regs -> apresent (w_H W) memj a) ->
  akept SEGS B lyc Sc W memc W memj (spZ regs - MARK_QUIETLY_AK) (spZ regs)
    (fun a => inFP (mark_quietly_awr_again sink regs (rdW W memc)) a).
Proof.
  intros sink lyc Sc W memc memj mdc regs HAR HC Hs0 AGv Hpres Hwin.
  apply (akept_errno SEGS B LAWS (pal_env B TL) lyc Sc W memc mdc W memj _ _ _ HAR).
  apply (akept_run SEGS B LAWS pa_segs_low lyc Sc W memc mdc W memj _ _ _ HAR HC);
    [rewrite MARK_QUIETLY_AK_val; lia | | exact Hpres | exact Hwin].
  intros a Ha Hw HE. cbv beta in HE. apply AGv; [exact Ha|]. intros HX. apply HE. unfold mqa_X in HX.
  destruct HX as [H|[H|[H|H]]].
  - exfalso. exact (Hw H).
  - left. exists (aivl sink AMF_BLOCK).
    split; [unfold mark_quietly_awr_again; right; right; right; left; reflexivity|].
    unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec sink 0) as [E|_]; [exfalso; exact (Hs0 E)|].
    unfold AMF_ZEROED, AMF_BLOCK in *. lia.
  - left. exists (LA_G_SAID, LA_G_SAID + SAID_SIZE).
    split; [unfold mark_quietly_awr_again; right; right; left; reflexivity | cbn [fst snd]; lia].
  - right. exact H.
Qed.

Lemma mqa_arodata : forall sink lyc Sc (W : world SEGS) memc memj mdc (regs : bvmap 5 word),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  In (sink, AMF_BLOCK) (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mqa_X B (spZ regs) sink a -> aview SEGS (w_H W) memj a = aview SEGS (w_H W) memc a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) memc) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) memj).
Proof.
  intros sink lyc Sc W memc memj mdc regs HAR HC HF AGv HRO a Hro Hno Herr.
  pose proof (mq_sit_of lyc Sc W memc mdc (spZ regs) sink HAR HC HF) as (_ & _ & _ & Hoff & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Ha : YImgTop.IMG_LO <= a < YImgTop.IMG_TOP /\ ~ (LA_G_SAID <= a < LA_G_SAID + SAID_SIZE)).
  { destruct Hro as [(s & Hin & Hw & Hr)|Hr].
    - assert (Hi : in_img SEGS a) by (exists s; split; [exact Hin | exact Hr]).
      pose proof (pa_img_range a Hi) as Hb. unfold PcapImgEnd.pcap_img_end in Hb.
      rewrite HSEGS in Hin. pose proof (proj1 (forallb_forall _ _) mq_ro_said s Hin) as Hs.
      cbv beta in Hs. rewrite Hw in Hs. cbn [orb] in Hs. apply orb_true_iff in Hs.
      split; [unfold YImgTop.IMG_LO; lia|]. destruct Hs as [Hs|Hs]; apply Z.leb_le in Hs; lia.
    - unfold PCAP_RLO, PCAP_RHI, YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_SAID, SAID_SIZE in *. lia. }
  rewrite <- (HRO a Hro Hno Herr). apply AGv.
  - unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Ha. lia.
  - unfold mqa_X. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, AMF_ZEROED, AMF_BLOCK in *. lia.
Qed.
End s.

Print Assumptions mqa_rsm_pre.
Print Assumptions mqa_rsm_rd.
Print Assumptions mqa_q.
Print Assumptions mqa_akept.
Print Assumptions mqa_arodata.
