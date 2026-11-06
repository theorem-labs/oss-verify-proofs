(** struct pod_props in memory (fuzz/pod.h:70-86): 19744 bytes, the same layout in the six images of fuzz_role,
    fuzz_rate and fuzz_headamp (plain and UBSan; read from their DWARF and from the stores of the compiled code):
    buf at 0 (16384 bytes), len at 16384 (size_t), is_props at 16392, has_params at 16396, params_struct at 16400,
    ent at 16404 (32 entries of 104 bytes: type at 0, size at 4, body at 8, 96 bytes), n_ent at 19732, corrupt at
    19736, then 4 bytes of tail padding. Statement text: no function of a binary is proved here.

    pod_build starts with memset(pp, 0, sizeof *pp) (pod.h:384), so every byte it does not write is 0: the buffer
    past len, the ent entries past n_ent, each entry's body past its size (ent_build's memset, pod.h:279, and the
    104-byte copy of pod.h:432) and the padding. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model.
Import ListNotations.
Open Scope Z_scope.

Definition POD_BUF_MAX : Z := 16384.
Definition POD_ENT_MAX : Z := 32.
Definition OFF_LEN : Z := 16384.
Definition OFF_IS_PROPS : Z := 16392.
Definition OFF_HAS_PARAMS : Z := 16396.
Definition OFF_PARAMS_STRUCT : Z := 16400.
Definition OFF_ENT : Z := 16404.
Definition ENT_SIZE : Z := 104.
Definition OFF_N_ENT : Z := 19732.
Definition OFF_CORRUPT : Z := 19736.
Definition PP_SIZE : Z := 19744.

(** One struct pod_ent: type, size, then the 96-byte body (the body bytes, then 0). *)
Definition ent_mem (e : ent) : list byte := le32 (e_type e) ++ le32 (e_size e) ++ e_body e ++ zeros (96 - length (e_body e)).

(** The struct with buf[0..len) = b, the three flags, ent[0..n) = es and corrupt. *)
Definition pp_image (b : list byte) (isp hasp pst : bool) (es : list ent) (corr : bool) : list byte :=
  b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))) ++ le64 (Z.of_nat (length b))
  ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst)
  ++ flat_map ent_mem es ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es))))
  ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4.

(** The 19744 bytes at pp when pod_build returns. *)
Definition pp_bytes (r : pod_rec) : list byte :=
  pp_image (buf r) (is_props r) (has_params r) (params_struct r) (ents r) (corrupt r).

(** The bytes at pp at a cut of pod_build (Pod/Model.v [pb_cut]): is_props is written with the header
    (pod.h:395), has_params and params_struct when a first SPA_PROP_params property ends (pod.h:414-419, :435-438). *)
Definition pc_image (c : pb_cut) : list byte :=
  pp_image (pc_buf c) (is_props (PodRec (pc_shape c) (pc_props c) None))
    (has_params (PodRec (pc_shape c) (pc_props c) None)) (params_struct (PodRec (pc_shape c) (pc_props c) None))
    (pc_ents c) false.

(** ** Facts *)
Lemma length_ent_mem : forall e, (length (e_body e) <= 96)%nat -> length (ent_mem e) = 104%nat.
Proof.
  intros e H. unfold ent_mem. rewrite !length_app, !length_le32, length_zeros. lia.
Qed.

Lemma length_flat_ent_mem : forall es, Forall (fun e => (length (e_body e) <= 96)%nat) es ->
  length (flat_map ent_mem es) = (104 * length es)%nat.
Proof.
  intros es H. induction H as [|e es He Hs IH]; cbn [flat_map length]; [reflexivity|].
  rewrite length_app, length_ent_mem by exact He. lia.
Qed.

Lemma length_pp_image : forall b isp hasp pst es corr,
  Z.of_nat (length b) <= 16384 -> (length es <= 32)%nat -> Forall (fun e => (length (e_body e) <= 96)%nat) es ->
  Z.of_nat (length (pp_image b isp hasp pst es corr)) = PP_SIZE.
Proof.
  intros b isp hasp pst es corr Hb He Hs. unfold pp_image.
  rewrite !length_app, !length_zeros, !length_le32, length_le64, length_flat_ent_mem by exact Hs.
  unfold POD_BUF_MAX, ENT_SIZE, POD_ENT_MAX, PP_SIZE. lia.
Qed.

(** The fields sit at their offsets: buf and its zero tail fill 16384 bytes, then len (8), the three flags (4 each),
    the 32 entries (104 each), n_ent and corrupt. *)
Lemma length_buf_area : forall b, Z.of_nat (length b) <= 16384 ->
  Z.of_nat (length (b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))))) = OFF_LEN.
Proof. intros b H. rewrite length_app, length_zeros. unfold POD_BUF_MAX, OFF_LEN. lia. Qed.

Lemma length_ent_area : forall es, (length es <= 32)%nat -> Forall (fun e => (length (e_body e) <= 96)%nat) es ->
  Z.of_nat (length (flat_map ent_mem es ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es))))))
  = OFF_N_ENT - OFF_ENT.
Proof.
  intros es H Hs. rewrite length_app, length_flat_ent_mem, length_zeros by exact Hs.
  unfold ENT_SIZE, POD_ENT_MAX, OFF_N_ENT, OFF_ENT. lia.
Qed.

(** The image right after memset(pp, 0, 19744) (pod.h:384) is all zeros. *)
Lemma pp_image_memset : pp_image [] false false false [] false = zeros 19744.
Proof. vm_compute. reflexivity. Qed.

(** pp_bytes is 19744 bytes for every record pod_build makes. *)
Lemma length_pp_bytes : forall r, pod_rec_wf r -> Z.of_nat (length (pp_bytes r)) = PP_SIZE.
Proof.
  intros r (Hs & Hk & He & Hl & HL & Hc). unfold pp_bytes. apply length_pp_image.
  - unfold buf. destruct (p_corr r) as [[off bs]|].
    + destruct Hc as (Ho & Hb & _). unfold overwrite. rewrite !length_app, length_firstn, length_skipn. lia.
    + lia.
  - unfold ents. destruct (first_params (p_props r)) as [[i|es]|] eqn:E; cbn [length]; try lia.
    unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E.
    apply find_some in F as [Hin _]. rewrite Forall_forall in Hk. destruct (Hk kv Hin) as [_ Hv].
    injection E as E. rewrite E in Hv. exact Hv.
  - unfold ents. destruct (first_params (p_props r)) as [[i|es]|] eqn:E; try constructor.
    unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E.
    apply find_some in F as [Hin _]. apply all_ents_Forall in He. rewrite Forall_forall in He |- *.
    intros e Hie. specialize (He kv Hin). injection E as E. rewrite E in He. cbn [ents_of] in He. rewrite Forall_forall in He.
    destruct (He e Hie) as (_ & Hb & Hz). lia.
Qed.

(** ** The stores of pod_build as overwrites of the image (the builder walks' steps) *)
Lemma firstn_app_eq : forall (A B : list byte) n, n = length A -> firstn n (A ++ B) = A.
Proof.
  intros A B n ->. rewrite <- (Nat.add_0_r (length A)) at 1. rewrite firstn_app_len. cbn [firstn]. apply app_nil_r.
Qed.

Lemma skipn_app_eq : forall (A B : list byte) n, n = length A -> skipn n (A ++ B) = B.
Proof. intros A B n ->. rewrite <- (Nat.add_0_r (length A)). rewrite skipn_app_len. reflexivity. Qed.

(** x written over the field F that starts at |A|. *)
Lemma overwrite_mid : forall (A F C x : list byte), length x = length F ->
  overwrite (A ++ F ++ C) (length A) x = A ++ x ++ C.
Proof.
  intros A F C x H. unfold overwrite. rewrite firstn_app_eq by reflexivity. rewrite H, skipn_app_len.
  rewrite skipn_app_eq by reflexivity. reflexivity.
Qed.

Lemma overwrite_app_l : forall (A B x : list byte) o, (o + length x <= length A)%nat ->
  overwrite (A ++ B) o x = overwrite A o x ++ B.
Proof.
  intros A B x o H. unfold overwrite. rewrite firstn_app. replace (o - length A)%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. rewrite skipn_app. replace (o + length x - length A)%nat with 0%nat by lia.
  cbn [skipn]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma zeros_app : forall n m, zeros (n + m) = zeros n ++ zeros m.
Proof. intros n m. unfold zeros. apply repeat_app. Qed.

(** The image after buf: len, the three flags, the entries, n_ent, corrupt, the padding. *)
Definition pp_tail (isp hasp pst : bool) (es : list ent) (corr : bool) : list byte :=
  le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst)
  ++ flat_map ent_mem es ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es))))
  ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4.

Lemma pp_image_tail : forall b isp hasp pst es corr,
  pp_image b isp hasp pst es corr
  = b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))) ++ le64 (Z.of_nat (length b)) ++ pp_tail isp hasp pst es corr.
Proof. reflexivity. Qed.

(** pod_put: x appended to buf[0..len), then len := len + |x| (pod.h:175-182). *)
Lemma pp_image_put : forall b x isp hasp pst es corr,
  Z.of_nat (length b + length x) <= POD_BUF_MAX ->
  pp_image (b ++ x) isp hasp pst es corr
  = overwrite (overwrite (pp_image b isp hasp pst es corr) (length b) x)
      (Z.to_nat OFF_LEN) (le64 (Z.of_nat (length b + length x))).
Proof.
  intros b x isp hasp pst es corr H. rewrite !pp_image_tail. set (T := pp_tail isp hasp pst es corr).
  set (k := Z.to_nat (POD_BUF_MAX - Z.of_nat (length (b ++ x)))).
  assert (Ez : zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))) = zeros (length x) ++ zeros k).
  { rewrite <- zeros_app. f_equal. subst k. rewrite length_app. unfold POD_BUF_MAX in *. lia. }
  rewrite Ez, <- (app_assoc (zeros (length x))).
  rewrite (overwrite_mid b (zeros (length x)) (zeros k ++ le64 (Z.of_nat (length b)) ++ T) x)
    by (rewrite length_zeros; reflexivity).
  replace (b ++ x ++ zeros k ++ le64 (Z.of_nat (length b)) ++ T)
    with ((b ++ x ++ zeros k) ++ le64 (Z.of_nat (length b)) ++ T) by (rewrite <- !app_assoc; reflexivity).
  replace (Z.to_nat OFF_LEN) with (length (b ++ x ++ zeros k))
    by (rewrite !length_app, length_zeros; subst k; rewrite length_app; unfold POD_BUF_MAX, OFF_LEN in *; lia).
  rewrite overwrite_mid by (rewrite !length_le64; reflexivity).
  rewrite length_app. rewrite <- !app_assoc. reflexivity.
Qed.

(** pod_patch32 and the corruption: bytes written inside buf[0..len) (pod.h:195-198, :434, :440, :446). *)
Lemma pp_image_patch : forall b o x isp hasp pst es corr, (o + length x <= length b)%nat ->
  pp_image (overwrite b o x) isp hasp pst es corr = overwrite (pp_image b isp hasp pst es corr) o x.
Proof.
  intros b o x isp hasp pst es corr H. rewrite !pp_image_tail. rewrite length_overwrite by exact H.
  rewrite overwrite_app_l by exact H. reflexivity.
Qed.

(** The prefix of the image up to the entries (16404 bytes). *)
Definition pp_head (b : list byte) (isp hasp pst : bool) : list byte :=
  b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))) ++ le64 (Z.of_nat (length b))
  ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst).

Lemma length_pp_head : forall b isp hasp pst, Z.of_nat (length b) <= POD_BUF_MAX ->
  Z.of_nat (length (pp_head b isp hasp pst)) = OFF_ENT.
Proof.
  intros b isp hasp pst H. unfold pp_head. rewrite !length_app, length_zeros, length_le64, !length_le32.
  unfold POD_BUF_MAX, OFF_ENT in *. lia.
Qed.

Lemma pp_image_head : forall b isp hasp pst es corr,
  pp_image b isp hasp pst es corr
  = pp_head b isp hasp pst ++ flat_map ent_mem es ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es))))
    ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4.
Proof. intros. unfold pp_image, pp_head. rewrite <- !app_assoc. reflexivity. Qed.

(** The record copy pp->ent[pp->n_ent++] = e (pod.h:432): the entry, then n_ent. *)
Lemma pp_image_ent : forall b isp hasp pst es e corr,
  Z.of_nat (length b) <= POD_BUF_MAX -> (length es < 32)%nat ->
  Forall (fun e => (length (e_body e) <= 96)%nat) (es ++ [e]) ->
  pp_image b isp hasp pst (es ++ [e]) corr
  = overwrite (overwrite (pp_image b isp hasp pst es corr)
                 (Z.to_nat (OFF_ENT + ENT_SIZE * Z.of_nat (length es))) (ent_mem e))
      (Z.to_nat OFF_N_ENT) (le32 (Z.of_nat (length es) + 1)).
Proof.
  intros b isp hasp pst es e corr Hb Hl Hs. apply Forall_app in Hs as [Hs He]. apply Forall_inv in He.
  rewrite !pp_image_head. set (P := pp_head b isp hasp pst). set (F := flat_map ent_mem es).
  pose proof (length_pp_head b isp hasp pst Hb) as LP. fold P in LP.
  pose proof (length_flat_ent_mem es Hs) as LF. fold F in LF.
  set (k := Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length (es ++ [e]))))).
  assert (Ez : zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es)))) = zeros 104 ++ zeros k).
  { rewrite <- zeros_app. f_equal. subst k. rewrite length_app. cbn [length]. unfold ENT_SIZE, POD_ENT_MAX. lia. }
  rewrite Ez.
  replace (P ++ F ++ (zeros 104 ++ zeros k) ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4)
    with ((P ++ F) ++ zeros 104 ++ (zeros k ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4))
    by (rewrite <- !app_assoc; reflexivity).
  replace (Z.to_nat (OFF_ENT + ENT_SIZE * Z.of_nat (length es))) with (length (P ++ F))
    by (rewrite length_app, LF; unfold ENT_SIZE; lia).
  rewrite overwrite_mid by (rewrite length_zeros; apply length_ent_mem; exact He).
  replace ((P ++ F) ++ ent_mem e ++ zeros k ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4)
    with (((P ++ F) ++ ent_mem e ++ zeros k) ++ le32 (Z.of_nat (length es)) ++ (le32 (Z.b2z corr) ++ zeros 4))
    by (rewrite <- !app_assoc; reflexivity).
  replace (Z.to_nat OFF_N_ENT) with (length ((P ++ F) ++ ent_mem e ++ zeros k))
    by (rewrite !length_app, LF, length_ent_mem, length_zeros by exact He; subst k; rewrite length_app;
        cbn [length]; unfold ENT_SIZE, POD_ENT_MAX, OFF_N_ENT, OFF_ENT in *; lia).
  rewrite overwrite_mid by (rewrite !length_le32; reflexivity).
  subst F. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r, length_app. cbn [length].
  replace (Z.of_nat (length es + 1)) with (Z.of_nat (length es) + 1) by lia. rewrite <- !app_assoc. reflexivity.
Qed.

(** The int fields one at a time: is_props, has_params, params_struct (pod.h:395, :418, :436-437) and corrupt
    (pod.h:447). *)
Section Fields.
Variables (b : list byte) (isp hasp pst : bool) (es : list ent) (corr : bool).
Hypothesis Hb : Z.of_nat (length b) <= POD_BUF_MAX.
Hypothesis He : (length es <= 32)%nat.
Hypothesis Hs : Forall (fun e => (length (e_body e) <= 96)%nat) es.

Let Z1 := zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))).
Let L8 := le64 (Z.of_nat (length b)).
Let Z2 := zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es)))).
Let FE := flat_map ent_mem es.

Lemma len_Z1 : Z.of_nat (length b) + Z.of_nat (length Z1) = 16384.
Proof. unfold Z1. rewrite length_zeros. pose proof Hb. unfold POD_BUF_MAX in *. lia. Qed.
Lemma len_FE_Z2 : Z.of_nat (length FE) + Z.of_nat (length Z2) = 3328.
Proof. unfold FE, Z2. rewrite length_flat_ent_mem, length_zeros by exact Hs. pose proof He. unfold ENT_SIZE, POD_ENT_MAX. lia. Qed.

Lemma pp_image_is_props : forall isp',
  overwrite (pp_image b isp hasp pst es corr) (Z.to_nat OFF_IS_PROPS) (le32 (Z.b2z isp'))
  = pp_image b isp' hasp pst es corr.
Proof.
  intros isp'. pose proof len_Z1.
  assert (E : forall i, pp_image b i hasp pst es corr
              = (b ++ Z1 ++ L8) ++ le32 (Z.b2z i) ++ (le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ FE ++ Z2
                ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4))
    by (intros i; unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite !E. replace (Z.to_nat OFF_IS_PROPS) with (length (b ++ Z1 ++ L8))
    by (rewrite !length_app; unfold L8; rewrite length_le64; unfold OFF_IS_PROPS; lia).
  apply overwrite_mid. reflexivity.
Qed.

Lemma pp_image_has_params : forall hasp',
  overwrite (pp_image b isp hasp pst es corr) (Z.to_nat OFF_HAS_PARAMS) (le32 (Z.b2z hasp'))
  = pp_image b isp hasp' pst es corr.
Proof.
  intros hasp'. pose proof len_Z1.
  assert (E : forall h, pp_image b isp h pst es corr
              = (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp)) ++ le32 (Z.b2z h) ++ (le32 (Z.b2z pst) ++ FE ++ Z2
                ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4))
    by (intros h; unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite !E. replace (Z.to_nat OFF_HAS_PARAMS) with (length (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp)))
    by (rewrite !length_app; unfold L8; rewrite length_le64, length_le32; unfold OFF_HAS_PARAMS; lia).
  apply overwrite_mid. reflexivity.
Qed.

Lemma pp_image_params_struct : forall pst',
  overwrite (pp_image b isp hasp pst es corr) (Z.to_nat OFF_PARAMS_STRUCT) (le32 (Z.b2z pst'))
  = pp_image b isp hasp pst' es corr.
Proof.
  intros pst'. pose proof len_Z1.
  assert (E : forall q, pp_image b isp hasp q es corr
              = (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp)) ++ le32 (Z.b2z q) ++ (FE ++ Z2
                ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4))
    by (intros q; unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite !E. replace (Z.to_nat OFF_PARAMS_STRUCT) with (length (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp)))
    by (rewrite !length_app; unfold L8; rewrite length_le64, !length_le32; unfold OFF_PARAMS_STRUCT; lia).
  apply overwrite_mid. reflexivity.
Qed.

Lemma pp_image_corrupt : forall corr',
  overwrite (pp_image b isp hasp pst es corr) (Z.to_nat OFF_CORRUPT) (le32 (Z.b2z corr'))
  = pp_image b isp hasp pst es corr'.
Proof.
  intros corr'. pose proof len_Z1. pose proof len_FE_Z2.
  assert (E : forall c, pp_image b isp hasp pst es c
              = (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ FE ++ Z2
                 ++ le32 (Z.of_nat (length es))) ++ le32 (Z.b2z c) ++ zeros 4)
    by (intros c; unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite !E.
  replace (Z.to_nat OFF_CORRUPT)
    with (length (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ FE ++ Z2
                  ++ le32 (Z.of_nat (length es))))
    by (rewrite !length_app; unfold L8; rewrite length_le64, !length_le32; unfold OFF_CORRUPT; lia).
  apply overwrite_mid. reflexivity.
Qed.

(** The fields as the checking code reads them (memcpy of buf[0..len), the loads of expect_role inlined). *)
Lemma read_mid : forall (A F C : list byte) n, n = length A -> firstn (length F) (skipn n (A ++ F ++ C)) = F.
Proof. intros A F C n ->. rewrite skipn_app_eq by reflexivity. apply firstn_app_eq. reflexivity. Qed.

Lemma pp_read_buf : firstn (length b) (pp_image b isp hasp pst es corr) = b.
Proof. unfold pp_image. apply firstn_app_eq. reflexivity. Qed.

Lemma pp_read_len : firstn 8 (skipn (Z.to_nat OFF_LEN) (pp_image b isp hasp pst es corr)) = le64 (Z.of_nat (length b)).
Proof.
  pose proof len_Z1. unfold pp_image. fold Z1. rewrite app_assoc.
  change 8%nat with (length (le64 (Z.of_nat (length b)))). apply read_mid.
  rewrite length_app. unfold OFF_LEN. lia.
Qed.

Lemma pp_read_is_props :
  firstn 4 (skipn (Z.to_nat OFF_IS_PROPS) (pp_image b isp hasp pst es corr)) = le32 (Z.b2z isp).
Proof.
  pose proof len_Z1.
  assert (E : pp_image b isp hasp pst es corr = (b ++ Z1 ++ L8) ++ le32 (Z.b2z isp) ++ (le32 (Z.b2z hasp)
              ++ le32 (Z.b2z pst) ++ FE ++ Z2 ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4))
    by (unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite E. apply (read_mid (b ++ Z1 ++ L8) (le32 (Z.b2z isp))).
  rewrite !length_app. unfold L8. rewrite length_le64. unfold OFF_IS_PROPS. lia.
Qed.

Lemma pp_read_has_params :
  firstn 4 (skipn (Z.to_nat OFF_HAS_PARAMS) (pp_image b isp hasp pst es corr)) = le32 (Z.b2z hasp).
Proof.
  pose proof len_Z1.
  assert (E : pp_image b isp hasp pst es corr = (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp)) ++ le32 (Z.b2z hasp)
              ++ (le32 (Z.b2z pst) ++ FE ++ Z2 ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4))
    by (unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite E. apply (read_mid (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp)) (le32 (Z.b2z hasp))).
  rewrite !length_app. unfold L8. rewrite length_le64, length_le32. unfold OFF_HAS_PARAMS. lia.
Qed.

Lemma pp_read_params_struct :
  firstn 4 (skipn (Z.to_nat OFF_PARAMS_STRUCT) (pp_image b isp hasp pst es corr)) = le32 (Z.b2z pst).
Proof.
  pose proof len_Z1.
  assert (E : pp_image b isp hasp pst es corr = (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp))
              ++ le32 (Z.b2z pst) ++ (FE ++ Z2 ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4))
    by (unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite E. apply (read_mid (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp)) (le32 (Z.b2z pst))).
  rewrite !length_app. unfold L8. rewrite length_le64, !length_le32. unfold OFF_PARAMS_STRUCT. lia.
Qed.

Lemma pp_read_n_ent :
  firstn 4 (skipn (Z.to_nat OFF_N_ENT) (pp_image b isp hasp pst es corr)) = le32 (Z.of_nat (length es)).
Proof.
  pose proof len_Z1. pose proof len_FE_Z2.
  assert (E : pp_image b isp hasp pst es corr
              = (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ FE ++ Z2)
                ++ le32 (Z.of_nat (length es)) ++ (le32 (Z.b2z corr) ++ zeros 4))
    by (unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite E.
  apply (read_mid (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ FE ++ Z2)
                  (le32 (Z.of_nat (length es)))).
  rewrite !length_app. unfold L8. rewrite length_le64, !length_le32. unfold OFF_N_ENT. lia.
Qed.

Lemma pp_read_corrupt :
  firstn 4 (skipn (Z.to_nat OFF_CORRUPT) (pp_image b isp hasp pst es corr)) = le32 (Z.b2z corr).
Proof.
  pose proof len_Z1. pose proof len_FE_Z2.
  assert (E : pp_image b isp hasp pst es corr
              = (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ FE ++ Z2
                 ++ le32 (Z.of_nat (length es))) ++ le32 (Z.b2z corr) ++ zeros 4)
    by (unfold pp_image; fold Z1 L8 FE Z2; rewrite <- !app_assoc; reflexivity).
  rewrite E.
  apply (read_mid (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ FE ++ Z2
                   ++ le32 (Z.of_nat (length es))) (le32 (Z.b2z corr))).
  rewrite !length_app. unfold L8. rewrite length_le64, !length_le32. unfold OFF_CORRUPT. lia.
Qed.

(** Entry i of ent[0..n_ent) (struct pod_ent: type, size, the 96-byte body). *)
Lemma pp_read_ent : forall i, (i < length es)%nat ->
  firstn 104 (skipn (Z.to_nat (OFF_ENT + ENT_SIZE * Z.of_nat i)) (pp_image b isp hasp pst es corr))
  = ent_mem (nth i es (Ent 0 0 [])).
Proof.
  intros i Hi. pose proof len_Z1.
  destruct (nth_error es i) as [a|] eqn:N; [|apply nth_error_None in N; lia].
  rewrite (nth_error_nth es i (Ent 0 0 []) N).
  destruct (nth_error_split es i N) as (l1 & l2 & El & Ll).
  assert (Hs' := Hs). rewrite El in Hs'. apply Forall_app in Hs' as [Hs1 Hs2]. pose proof (Forall_inv Hs2) as Ha.
  assert (E : pp_image b isp hasp pst es corr
              = (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ flat_map ent_mem l1)
                ++ ent_mem a ++ (flat_map ent_mem l2 ++ Z2 ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4)).
  { unfold pp_image. fold Z1 L8 Z2. rewrite El at 1. rewrite flat_map_app. cbn [flat_map]. rewrite <- !app_assoc.
    reflexivity. }
  rewrite E. rewrite <- (length_ent_mem a Ha).
  apply (read_mid (b ++ Z1 ++ L8 ++ le32 (Z.b2z isp) ++ le32 (Z.b2z hasp) ++ le32 (Z.b2z pst) ++ flat_map ent_mem l1)
                  (ent_mem a)).
  rewrite !length_app, length_flat_ent_mem by exact Hs1. unfold L8. rewrite length_le64, !length_le32.
  unfold OFF_ENT, ENT_SIZE. lia.
Qed.

End Fields.
