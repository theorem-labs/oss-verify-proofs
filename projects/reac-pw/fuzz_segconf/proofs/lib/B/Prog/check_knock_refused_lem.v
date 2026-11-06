(* The image-B port of lib/A/Prog/check_knock_refused_lem.v (commit 38b2a0dc4f6b), the model
   lemmas of the walk lib/B/Prog/check_knock_refused.v on fuzz_segconf.asan-ubsan: SegModel's strstr_found gives an
   occurrence of the needle, and SegABase's list-Z string forms convert to the list-byte forms the wrapper contracts
   state. Image-independent: only the module paths differ from the A file (image B's kit and SegABase copies). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ============================== the needle occurs in the haystack ============================== *)
Lemma ckr_cut_nul_id : forall l, ~ In 0 l -> cut_nul l = l.
Proof.
induction l as [|b l IH]; intros H; cbn [cut_nul]; [reflexivity|].
destruct (Z.eqb_spec b 0) as [E|E]; [exfalso; apply H; left; exact E|].
f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma ckr_prefix_occ : forall p l, prefixb p l = true ->
(length p <= length l)%nat /\ firstn (length p) l = p.
Proof.
induction p as [|x p IH]; intros [|y l] H; cbn [prefixb] in H.
- split; [cbn; lia | reflexivity].
- split; [cbn; lia | reflexivity].
- discriminate H.
- apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y.
  destruct (IH l H2) as [L F]. cbn [length firstn]. split; [lia | rewrite F; reflexivity].
Qed.

Lemma ckr_infix_occ : forall n h, infixb n h = true ->
exists j, (j + length n <= length h)%nat /\ firstn (length n) (skipn j h) = n.
Proof.
intros n h. induction h as [|y h IH]; intros H; cbn [infixb] in H; apply orb_true_iff in H as [H|H].
- exists 0%nat. destruct (ckr_prefix_occ n [] H) as [L F]. cbn [skipn]. split; [lia | exact F].
- discriminate H.
- exists 0%nat. destruct (ckr_prefix_occ n (y :: h) H) as [L F]. cbn [skipn]. split; [lia | exact F].
- destruct (IH H) as (j & L & F). exists (S j). cbn [skipn length]. split; [lia | exact F].
Qed.

(* strstr_found on a NUL-free haystack: the needle occurs at some j, its last byte inside the haystack *)
Lemma ckr_found_occ : forall gs nd, ~ In 0 gs -> strstr_found gs nd = true ->
exists j, (j + length nd <= length gs)%nat /\ firstn (length nd) (skipn j gs) = nd.
Proof.
intros gs nd H F. unfold strstr_found in F. rewrite (ckr_cut_nul_id gs H) in F. exact (ckr_infix_occ nd gs F).
Qed.

(* ============================== list Z strings as list byte strings ============================== *)
Lemma ckr_aview_range : forall segs H mem a z, aview segs H mem a = Some z -> 0 <= z < 256.
Proof.
intros segs H mem a z E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Definition rd_bytes (rd : reader) : Prop := forall a z, rd a = Some z -> 0 <= z < 256.

Lemma ckr_rd_bytes_view : forall segs H mem, rd_bytes (aview segs H mem).
Proof. intros segs H mem a z E. exact (ckr_aview_range segs H mem a z E). Qed.

Lemma ckr_zs_bytes : forall rd p (s : list Z), rd_bytes rd -> sa_zs rd p s -> sa_bytes rd p (map (Z_to_bv 8) s).
Proof.
intros rd p s HR H i Hi. rewrite length_map in Hi. pose proof (H i Hi) as Hv.
pose proof (HR _ _ Hv) as R. rewrite Hv. f_equal.
replace (nth i (map (Z_to_bv 8) s) ZB0) with (Z_to_bv 8 (nth i s 0))
  by (change ZB0 with (Z_to_bv 8 0); rewrite map_nth; reflexivity).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by lia. reflexivity.
Qed.

(* sa_strz over a byte reader is astr_atR's body at the byte list map (Z_to_bv 8) s *)
Lemma ckr_strz_bytes : forall rd p (s : list Z), rd_bytes rd -> sa_strz rd p s ->
sa_bytes rd p (map (Z_to_bv 8) s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) s).
Proof.
intros rd p s HR [HZ HN]. split.
- replace (map (Z_to_bv 8) s ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (s ++ [0])) by (rewrite map_app; reflexivity).
  exact (ckr_zs_bytes rd p (s ++ [0]) HR HZ).
- intros Hin. apply in_map_iff in Hin as (z & Ez & Hz). apply HN.
  destruct (In_nth s z 0 Hz) as (i & Hi & Hn).
  assert (Hi' : (i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (HZ i Hi') as Hv. rewrite app_nth1 in Hv by exact Hi. rewrite Hn in Hv.
  pose proof (HR _ _ Hv) as R.
  apply (f_equal bv_unsigned) in Ez. rewrite Z_to_bv_unsigned in Ez. unfold bv_wrap in Ez.
  change (bv_modulus 8) with 256 in Ez. rewrite Z.mod_small in Ez by lia. change (bv_unsigned (Z_to_bv 8 0)) with 0 in Ez.
  rewrite <- Ez. exact Hz.
Qed.

Lemma ckr_unsigned_map : forall s : list Z, Forall (fun z => 0 <= z < 256) s -> map bv_unsigned (map (Z_to_bv 8) s) = s.
Proof.
induction s as [|z s IH]; intros H; [reflexivity|]. inversion H as [|? ? Hz Hs]; subst.
cbn [map]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by lia. rewrite (IH Hs). reflexivity.
Qed.

Lemma ckr_zs_range : forall rd p (s : list Z), rd_bytes rd -> sa_zs rd p s -> Forall (fun z => 0 <= z < 256) s.
Proof.
intros rd p s HR H. apply Forall_forall. intros z Hz. destruct (In_nth s z 0 Hz) as (i & Hi & Hn).
pose proof (H i Hi) as Hv. rewrite Hn in Hv. exact (HR _ _ Hv).
Qed.

Lemma ckr_zs_app_l : forall rd p (l1 l2 : list Z), sa_zs rd p (l1 ++ l2) -> sa_zs rd p l1.
Proof.
intros rd p l1 l2 H i Hi. assert (Hi' : (i < length (l1 ++ l2))%nat) by (rewrite length_app; lia).
pose proof (H i Hi') as Hv. rewrite app_nth1 in Hv by exact Hi. exact Hv.
Qed.
