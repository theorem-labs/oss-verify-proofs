(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YA0nR.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* The re-hide step of a secondary recycle. After the madvise_dontneed of the dead shadow hull's interior [PB, PE),
   with no page of it materialized, the walk continues in the world wrehide W h PB PE: [PB, PE) hidden, and in the
   allowance the hull h replaced by its two edges [fst h, PB) and [PE, snd h). The map itself stays in the allowance
   here; the later munmap refunds it as today (YFfn.AI_refund). The step lowers A_bytes by PE - PB (A_bytes_rehide),
   keeps AI (AI_rehide), and is a wle' step when [PB, PE) lies in the zone RZ (wle'_rehide), so SRr' composes over it
   (SRr'_rehide). The model premise is satisfiable at a real madvise: madvise_mat_out. Additive: no existing text
   changes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0n YK0i YK15 YK0j YK18 YK0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YK05 YA0i YA0n YA06 YFfn YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition in_ivb (PB PE : Z) (a : word) : bool := (PB <=? bv_unsigned a) && (bv_unsigned a <? PE).
Definition H_rehide (H : word -> bool) (PB PE : Z) : word -> bool := fun a => H a || in_ivb PB PE a.
Definition A_rehide (A : list (Z * Z)) (h : Z * Z) (PB PE : Z) : list (Z * Z) :=
  A_drop h A ++ [(fst h, PB); (PE, snd h)].

(* The arithmetic shape of the step: the hull h, the madvised interior [PB, PE) inside it, all page aligned. *)
Definition rh_shape (h : Z * Z) (PB PE : Z) : Prop :=
  0 <= fst h /\ fst h <= PB /\ PB <= PE /\ PE <= snd h /\ snd h <= 2 ^ 64 /\
  fst h mod page_size = 0 /\ PB mod page_size = 0 /\ PE mod page_size = 0 /\ snd h mod page_size = 0.

Lemma u64_rh : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma page_base_unsigned_rh : forall a : word, bv_unsigned (page_base a) = bv_unsigned a / page_size * page_size.
Proof.
  intros a. unfold page_base, page_base_of. pose proof (bv_unsigned_in_range 64 a) as Ha. unfold bv_modulus in Ha.
  apply u64_rh. unfold page_size. pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)). lia.
Qed.

(* A page outside [PB, PE) that A allows is allowed by the re-hidden allowance. *)
Lemma page_allowed_rehide : forall A h PB PE (p : word),
  rh_shape h PB PE -> bv_unsigned p mod page_size = 0 -> ~ (PB <= bv_unsigned p < PE) ->
  page_allowedb A p = true -> page_allowedb (A_rehide A h PB PE) p = true.
Proof.
  intros A h PB PE p (S0 & S1 & S2 & S3 & S4 & A1 & A2 & A3 & A4) Hal Hout Hp.
  unfold page_allowedb in *. apply existsb_exists in Hp as (iv & Hin & Hb).
  apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  apply existsb_exists. unfold A_rehide.
  destruct (zz_eqb iv h) eqn:E.
  - apply zz_eqb_eq in E. subst iv. unfold page_size in *.
    pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)) as Dp. rewrite Hal in Dp.
    pose proof (Z.div_mod PB 4096 ltac:(lia)) as Db. rewrite A2 in Db.
    pose proof (Z.div_mod PE 4096 ltac:(lia)) as De. rewrite A3 in De.
    destruct (Z_lt_le_dec (bv_unsigned p) PB) as [Lt | Ge].
    + exists (fst h, PB). split; [apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. apply andb_true_iff. split; apply Z.leb_le; lia.
    + exists (PE, snd h). split; [apply in_or_app; right; right; left; reflexivity|].
      cbn [fst snd]. apply andb_true_iff. split; apply Z.leb_le; lia.
  - exists iv. split.
    + apply in_or_app. left. apply A_drop_In. split; [exact Hin|]. intros ->. rewrite (proj2 (zz_eqb_eq h h) eq_refl) in E. discriminate.
    + apply andb_true_iff. split; apply Z.leb_le; assumption.
Qed.

Lemma A_bytes_rehide : forall A h PB PE,
  A_wf A -> In h A -> rh_shape h PB PE -> A_bytes (A_rehide A h PB PE) <= A_bytes A - (PE - PB).
Proof.
  intros A h PB PE WF Hin (S0 & S1 & S2 & S3 & _).
  pose proof (A_bytes_refund h A WF Hin) as R. unfold A_rehide. rewrite A_bytes_app. cbn [A_bytes fst snd]. lia.
Qed.

Lemma Awf_rehide : forall A h PB PE, A_wf A -> rh_shape h PB PE -> A_wf (A_rehide A h PB PE).
Proof.
  intros A h PB PE WF (S0 & S1 & S2 & S3 & S4 & A1 & A2 & A3 & A4). unfold A_rehide, A_wf.
  apply Forall_app. split; [apply A_drop_wf; exact WF|]. repeat constructor; cbn [fst snd]; assumption.
Qed.

(* The re-hidden interval's ends are page aligned when the re-hidden allowance is well formed: A_rehide adds the
   entries (fst h, PB) and (PE, snd h). *)
Lemma A_wf_rehide_al : forall A h PB PE, A_wf (A_rehide A h PB PE) -> PB mod 8 = 0 /\ PE mod 8 = 0.
Proof.
  intros A h PB PE WF. unfold A_rehide, A_wf in WF. apply Forall_app in WF as [_ WF].
  inversion WF as [|x l (_ & _ & P1) WF' E1]. inversion WF' as [|y l' (_ & P2 & _) _ E2]. cbn [fst snd] in P1, P2.
  unfold page_size in *.
  pose proof (Z.div_mod PB 4096 ltac:(lia)). pose proof (Z.div_mod PE 4096 ltac:(lia)).
  split; apply Z.mod_divide; try lia; [exists (PB / 4096 * 512) | exists (PE / 4096 * 512)]; lia.
Qed.

(* On the two shadow bands, a hidden map that is constant on each 8-byte-aligned word stays so after the re-hide,
   when PB and PE are 8-aligned: a word lies wholly inside [PB, PE) or wholly outside it. Stated over a plain map,
   so a unit whose world carries this as a field (w_H8) builds its re-hidden world from it. *)
Lemma H_rehide_H8 : forall (H : word -> bool) PB PE, PB mod 8 = 0 -> PE mod 8 = 0 ->
  (forall a, YG0f.in_band_rw a -> H (Z_to_bv 64 a) = H (Z_to_bv 64 (a - a mod 8))) ->
  forall a, YG0f.in_band_rw a -> H_rehide H PB PE (Z_to_bv 64 a) = H_rehide H PB PE (Z_to_bv 64 (a - a mod 8)).
Proof.
  intros H PB PE P8 E8 H8 a Ha. unfold H_rehide. rewrite (H8 a Ha). f_equal.
  assert (Hr : 0 <= a < 2 ^ 64)
    by (unfold YG0f.in_band_rw, YG0f.kLowShadowBeg, YG0f.kLowShadowEnd, YG0f.kHighShadowBeg, YG0f.kHighShadowEnd in Ha; lia).
  pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  pose proof (Z.div_mod PB 8 ltac:(lia)). pose proof (Z.div_mod PE 8 ltac:(lia)).
  unfold in_ivb. rewrite (u64_rh a Hr), (u64_rh (a - a mod 8) ltac:(lia)).
  destruct (Z.leb_spec PB a), (Z.leb_spec PB (a - a mod 8)), (Z.ltb_spec a PE), (Z.ltb_spec (a - a mod 8) PE);
    cbn [andb]; try reflexivity; exfalso; lia.
Qed.

Section e. Context {fx : YK11.FPState}.
Variable segs : list Segment.

Lemma Hoff_rehide : forall H PB PE,
  H_off_segments segs H -> (forall a : word, PB <= bv_unsigned a < PE -> find_segment segs (bv_unsigned a) 1 = None) ->
  H_off_segments segs (H_rehide H PB PE).
Proof.
  intros H PB PE HO HS a Ha. unfold H_rehide in Ha. apply orb_true_iff in Ha as [Ha | Ha]; [exact (HO a Ha)|].
  unfold in_ivb in Ha. apply andb_true_iff in Ha as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  apply HS. lia.
Qed.

(* The relation holds at the re-hidden world. *)
Theorem AI_rehide : forall H A md h PB PE,
  AI segs H A md -> In h A -> rh_shape h PB PE ->
  (forall a : word, PB <= bv_unsigned a < PE -> find_segment segs (bv_unsigned a) 1 = None) ->
  (forall p, In p (m_vm_materialized md) -> ~ (PB <= bv_unsigned p < PE)) ->
  AI segs (H_rehide H PB PE) (A_rehide A h PB PE) md.
Proof.
  intros H A md h PB PE (HO & WF & COV & MI & HH) Hin SH HS MO.
  pose proof SH as (S0 & S1 & S2 & S3 & S4 & A1 & A2 & A3 & A4).
  split; [exact (Hoff_rehide H PB PE HO HS)|]. split; [exact (Awf_rehide A h PB PE WF SH)|]. split.
  - intros w Hl Hw. unfold H_rehide in Hw. apply orb_false_iff in Hw as [Hw1 Hw2].
    apply (page_allowed_rehide A h PB PE (page_base w) SH).
    + rewrite page_base_unsigned_rh. unfold page_size. apply Z_mod_mult.
    + rewrite page_base_unsigned_rh. unfold in_ivb in Hw2. apply andb_false_iff in Hw2.
      unfold page_size in *. pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)).
      pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
      pose proof (Z.div_mod PE 4096 ltac:(lia)) as De. rewrite A3 in De.
      destruct Hw2 as [Hw2 | Hw2]; [apply Z.leb_gt in Hw2 | apply Z.ltb_ge in Hw2]; lia.
    + exact (COV w Hl Hw1).
  - split; [|exact HH]. destruct MI as [N1 N2 N3 N4 N5]. constructor; try assumption.
    + intros p Hp. apply (page_allowed_rehide A h PB PE p SH (N2 p Hp) (MO p Hp) (N3 p Hp)).
    + pose proof (A_bytes_rehide A h PB PE WF Hin SH). lia.
Qed.

(* The re-hidden world. Preset's world carries the field w_H8 (YA0n.v:25), so the re-hidden world takes its proof
   H8 as a further argument, built by H_rehide_H8 above from w_H8 W and 8-aligned PB / PE (preset-side hunk). *)
Definition wrehide (W : world segs) (h : Z * Z) (PB PE : Z)
    (HO : H_off_segments segs (H_rehide (w_H W) PB PE)) (HA : A_wf (A_rehide (w_A W) h PB PE))
    (H8 : forall a : Z, YG0f.in_band_rw a ->
      H_rehide (w_H W) PB PE (Z_to_bv 64 a) = H_rehide (w_H W) PB PE (Z_to_bv 64 (a - a mod 8))) : world segs :=
  mkW segs (H_rehide (w_H W) PB PE) (A_rehide (w_A W) h PB PE) HO HA H8.

Variable RZ : Z -> Prop.

Lemma wle'_rehide : forall W h PB PE HO HA H8,
  (forall a, PB <= a < PE -> RZ a) -> wle' segs RZ W (wrehide W h PB PE HO HA H8).
Proof.
  intros W h PB PE HO HA H8 HZ a Ha. cbn [w_H wrehide] in Ha. unfold H_rehide in Ha.
  apply orb_true_iff in Ha as [Ha | Ha]; [left; exact Ha | right].
  unfold in_ivb in Ha. apply andb_true_iff in Ha as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply HZ. lia.
Qed.

(* The step: a walk may continue in the re-hidden world. *)
Theorem SRr'_rehide : forall W h PB PE HO HA H8 c Q,
  (forall a, PB <= a < PE -> RZ a) ->
  In h (w_A W) -> rh_shape h PB PE ->
  (forall a : word, PB <= bv_unsigned a < PE -> find_segment segs (bv_unsigned a) 1 = None) ->
  (forall p, In p (m_vm_materialized (cfg_model c)) -> ~ (PB <= bv_unsigned p < PE)) ->
  SRr' segs RZ (wrehide W h PB PE HO HA H8) c Q -> SRr' segs RZ W c Q.
Proof.
  intros W h PB PE HO HA H8 c Q HZ Hin SH HS MO H.
  unfold SRr' in *. eapply (SRrG_world_le segs (wle' segs RZ) (wle'_trans segs RZ)); [exact (wle'_rehide W h PB PE HO HA H8 HZ) | | exact H].
  intros HI. cbn [w_H w_A wrehide]. exact (AI_rehide _ _ _ h PB PE HI Hin SH HS MO).
Qed.

(* The step's EXACT hidden set (Revision 1, B2): only [PB, PE) is newly hidden. A caller keeps every shadow fact
   outside it; wle'_rehide is this lifted into the composition zone by YA0nH.wle_in_mono. *)
Lemma rehide_hid_exact : forall W h PB PE HO HA H8,
  wle_in segs (fun a => PB <= a < PE) W (wrehide W h PB PE HO HA H8).
Proof.
  intros W h PB PE HO HA H8 a Ha. cbn [w_H wrehide] in Ha. unfold H_rehide in Ha.
  apply orb_true_iff in Ha as [Ha | Ha]; [left; exact Ha | right].
  unfold in_ivb in Ha. apply andb_true_iff in Ha as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* The step at the recycle walk's RETURN (Revision 1, B1): the map entry has already left the allowance with the
   munmap's refund (W2), so the step drops the hull only, and the walk's own post gives the materialized-page
   premise (DMrcSecMat.mat_gone's first conjunct). *)
Theorem SRr'_rehide_ret : forall W h PB PE HO HA H8 c Q,
  (forall a, PB <= a < PE -> RZ a) ->
  In h (w_A W) -> rh_shape h PB PE ->
  (forall a : word, PB <= bv_unsigned a < PE -> find_segment segs (bv_unsigned a) 1 = None) ->
  (forall p, In p (m_vm_materialized (cfg_model c)) -> page_outside_range PB PE p = true) ->
  SRr' segs RZ (wrehide W h PB PE HO HA H8) c Q -> SRr' segs RZ W c Q.
Proof.
  intros W h PB PE HO HA H8 c Q HZ Hin SH HS MO H.
  apply (SRr'_rehide W h PB PE HO HA H8 c Q HZ Hin SH HS); [|exact H].
  intros p Hp. pose proof (MO p Hp) as Ho. unfold page_outside_range in Ho.
  rewrite negb_true_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge in Ho. lia.
Qed.
End e.

(* Satisfiability at a real madvise (the model premise): no page of [PB, PE) is materialized after
   madvise_dontneed_next md PB (PE - PB) (YA06.madvise_next_materialized). *)
Lemma madvise_mat_out : forall md PB PE (p : word),
  0 <= PB -> PB <= PE -> PE < 2 ^ 64 ->
  In p (m_vm_materialized (madvise_dontneed_next md (Z_to_bv 64 PB) (Z_to_bv 64 (PE - PB)))) ->
  ~ (PB <= bv_unsigned p < PE).
Proof.
  intros md PB PE p H0 H1 H2 Hp. rewrite madvise_next_materialized, filter_In in Hp. destruct Hp as [_ Ho].
  rewrite (u64_rh PB) in Ho by lia. rewrite (u64_rh (PE - PB)) in Ho by lia.
  unfold page_outside_range in Ho. rewrite negb_true_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge in Ho. lia.
Qed.
