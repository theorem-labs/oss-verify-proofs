(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KIGNP
   (KIGN 0x86968 -> KKNOCK 0x86a7c or KDONE 0x86c1c): the facts of the model and of the reader its walk
   (mf_kignp_*.v) uses. A walk lane of the image-B m_file-family owner's G2B. ADAPTED from the image-A m_file-family lane's image-A
   lib/A/Prog/m_file_s_kign_t.v and m_file_s_kign_e.v (commit a11e040adbd4): pure lemmas, the
   same text over image B's copies (only the Require lines and this header differ; the struct mconf layout is the
   same in both images).
   proves no function (kind: model lemma of m_file's walk, segment S_MF_KIGNP).

   - ki_dec: the value test of the code, in the code's order (ieq "yes" 0x86994, "true" 0x869b0, v[0] = '1'
     0x869e0, ieq "no" 0x869f4, "false" 0x86a0c, v[0] = '0' 0x86c04), and mk_disp (m_file_m.v) at the KIGN cut
     reduced by it.
   - the snprintf text of the hit path (0x86a74, "%s" of c->reading) is c->reading itself.
   - the key and the value as list byte for ieq_contract (lib/B/Prog/ieq_c.v ieq_pre: sa_bytes of the n bytes at
     s): the bytes of a slice of the text, read through an ASan reader, are bytes.
   - the sizes of the two models the segment leaves (m_upd, m_refuse) and the cursor's entry inside the final model,
     over the shared model facts of lib/B/Prog/m_file_mdl.v.
   - the mconf block after the hit path's three writes (0x86a3c g->ignore = b, 0x86a5c g->ignore_set = 1, the
     snprintf 0x86a74 into g->ignore_file): ki_e_mconf_ign, a pure lemma over readers (ki_e_bytes_patch, the
     patch of a byte list); its last premise (every value rd' returns is a byte) makes the snprintf's bytes, given
     as the list of Z f ++ [0], a list of bytes (without it the lemma is false, f = [300]); the ASan reader aview
     gives it. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_mdl.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== the value test ===================================== *)
(* the ignore value the code accepts (fuzz_segconf.c m_key; SegModel.m_key's S_ignore arm): Some true for "yes",
   "true" or "1", Some false for "no", "false" or "0", None for anything else *)
Definition ki_dec (v : list Z) : option bool :=
  if ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49)) then Some true
  else if ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48)) then Some false
  else None.

(* the K cut's model step after "role" and "model" missed and "ignore" hit *)
Lemma ki_disp_hit : forall c gi k v line b,
  ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = true -> ki_dec v = Some b ->
  mk_disp c gi k v line = m_upd c gi (ms_with_ignore b (snprintf_s 96 F_s [AS (mc_reading c)])).
Proof.
intros c gi k v line b H1 H2 H3 HD. unfold mk_disp. rewrite H1, H2, H3. unfold ki_dec in HD.
destruct (ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49))).
- injection HD as <-. reflexivity.
- destruct (ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48))); [|discriminate].
  injection HD as <-. reflexivity.
Qed.

Lemma ki_disp_ref : forall c gi k v line,
  ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = true -> ki_dec v = None ->
  mk_disp c gi k v line = m_refuse c line false.
Proof.
intros c gi k v line H1 H2 H3 HD. unfold mk_disp. rewrite H1, H2, H3. unfold ki_dec in HD.
destruct (ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49))); [discriminate|].
destruct (ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48))); [discriminate|].
reflexivity.
Qed.

(* the six tests one at a time, as the code's branches meet them *)
Lemma ki_dec_yes : forall v, ieq v S_yes = true -> ki_dec v = Some true.
Proof. intros v H. unfold ki_dec. rewrite H. reflexivity. Qed.
Lemma ki_dec_true : forall v, ieq v S_true = true -> ki_dec v = Some true.
Proof. intros v H. unfold ki_dec. rewrite H, orb_true_r. reflexivity. Qed.
Lemma ki_dec_one : forall v, length v = 1%nat -> hd0 v = 49 -> ki_dec v = Some true.
Proof.
intros v H1 H2. unfold ki_dec. rewrite H1, H2. change ((1 =? 1)%nat && (49 =? 49)) with true.
rewrite orb_true_r. reflexivity.
Qed.
Lemma ki_dec_no : forall v, ieq v S_yes = false -> ieq v S_true = false ->
  ~ (length v = 1%nat /\ hd0 v = 49) -> ieq v S_no = true -> ki_dec v = Some false.
Proof.
intros v H1 H2 H3 H4. unfold ki_dec. rewrite H1, H2, H4. cbn [orb].
destruct ((length v =? 1)%nat && (hd0 v =? 49)) eqn:E; [|reflexivity].
apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. tauto.
Qed.
Lemma ki_dec_false : forall v, ieq v S_yes = false -> ieq v S_true = false ->
  ~ (length v = 1%nat /\ hd0 v = 49) -> ieq v S_false = true -> ki_dec v = Some false.
Proof.
intros v H1 H2 H3 H4. unfold ki_dec. rewrite H1, H2, H4, orb_true_r. cbn [orb].
destruct ((length v =? 1)%nat && (hd0 v =? 49)) eqn:E; [|reflexivity].
apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. tauto.
Qed.
Lemma ki_dec_zero : forall v, ieq v S_yes = false -> ieq v S_true = false ->
  ~ (length v = 1%nat /\ hd0 v = 49) -> length v = 1%nat -> hd0 v = 48 -> ki_dec v = Some false.
Proof.
intros v H1 H2 H3 H4 H5. unfold ki_dec. rewrite H1, H2. cbn [orb].
destruct ((length v =? 1)%nat && (hd0 v =? 49)) eqn:E.
- apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. tauto.
- rewrite H4, H5. change ((1 =? 1)%nat && (48 =? 48)) with true. rewrite orb_true_r. reflexivity.
Qed.
Lemma ki_dec_none : forall v, ieq v S_yes = false -> ieq v S_true = false ->
  ~ (length v = 1%nat /\ hd0 v = 49) -> ieq v S_no = false -> ieq v S_false = false ->
  ~ (length v = 1%nat /\ hd0 v = 48) -> ki_dec v = None.
Proof.
intros v H1 H2 H3 H4 H5 H6. unfold ki_dec. rewrite H1, H2, H4, H5. cbn [orb].
destruct ((length v =? 1)%nat && (hd0 v =? 49)) eqn:E.
- apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. tauto.
- destruct ((length v =? 1)%nat && (hd0 v =? 48)) eqn:E'; [|reflexivity].
  apply andb_true_iff in E' as [E1 E2]. apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. tauto.
Qed.

(* the value's first byte, when the value is the 1 byte at offset ov of the text left *)
Lemma ki_hd0_slice : forall (rest : list Z) ov, (ov < length rest)%nat ->
  hd0 (firstn 1 (skipn ov rest)) = nth ov rest 0.
Proof.
intros rest ov H. revert rest H. induction ov as [|ov IH]; intros [|x r] H; cbn [length] in H; try lia.
- reflexivity.
- cbn [skipn nth]. apply IH. lia.
Qed.

(* the line is a prefix of the text left *)
Lemma ki_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
unfold mf_line. induction rest as [|b r IH]; cbn [break_nl]; [cbn; lia|].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q] eqn:E. cbn [fst] in IH |- *. cbn [length]. lia.
Qed.

(* ===================================== the snprintf text ===================================== *)
Lemma ki_cut_nul_id : forall l : list Z, ~ In 0 l -> cut_nul l = l.
Proof.
induction l as [|x r IH]; intros H; [reflexivity|]. cbn [cut_nul].
destruct (Z.eqb_spec x 0) as [E|E]; [exfalso; apply H; left; congruence|].
rewrite IH; [reflexivity|]. intros Hin. apply H. right. exact Hin.
Qed.

(* snprintf(g->ignore_file, 96, "%s", c->reading) stores c->reading (a C string of at most 95 bytes) *)
Lemma ki_snp_reading : forall r, (length r < 96)%nat -> ~ In 0 r -> snprintf_s 96 F_s [AS r] = r.
Proof.
intros r Hl Hn. unfold snprintf_s. change (fmt F_s [AS r]) with (arg_s (AS r) ++ fmt [] []).
cbn [arg_s fmt]. rewrite app_nil_r, ki_cut_nul_id by exact Hn.
apply firstn_all2. change (Z.to_nat (96 - 1)) with 95%nat. lia.
Qed.

(* ===================================== bytes of the text ===================================== *)
(* the bytes [o, o + n) of l at p + o *)
Lemma ki_zs_slice : forall (rd : reader) p (l : list Z) o n, sa_zs rd p l -> (o + n <= length l)%nat ->
  sa_zs rd (p + Z.of_nat o) (firstn n (skipn o l)).
Proof.
intros rd p l o n H Hon i Hi. rewrite length_firstn, length_skipn in Hi.
rewrite nth_firstn. destruct (Nat.ltb_spec i n) as [Hlt|Hge]; [|lia]. rewrite nth_skipn.
replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia. apply H. lia.
Qed.

(* the values an ASan reader gives are bytes *)
Lemma ki_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate]. cbn in E. injection E as <-.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma ki_zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
induction l as [|x r IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [Hx Hr].
unfold seg_spec.zs, seg_spec.zb in *. cbn [map]. rewrite IH by exact Hr. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.

(* ieq_pre's bytes: the list Z read at a through an ASan reader, as list byte, and back *)
Lemma ki_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
  sa_bytes (aview segs H mem) a (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  Forall (fun z => 0 <= z < 256) l.
Proof.
intros segs H mem a l HZ.
assert (HR : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-).
  exact (ki_aview_byte segs H mem _ _ (HZ i Hi)). }
split; [|split; [exact (ki_zs_zb l HR) | exact HR]].
intros i Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi. rewrite (HZ i Hi). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.

(* ===================================== the sizes of the models ===================================== *)
(* the shared model facts are lib/B/Prog/m_file_mdl.v's (image A's text): upd_nth_length, m_refuse_sizes, mf_grows,
   m_refuse_grows, m_upd_grows, m_lines_ok *)

(* the K cut's step keeps seg's length and never shrinks kept *)
Lemma ki_disp_grows : forall c gi k v line, mf_grows c (mk_disp c gi k v line) /\
  length (mc_seg (mk_disp c gi k v line)) = length (mc_seg c).
Proof.
  intros c gi k v line.
  assert (R : forall ln kn, length (mc_seg (m_refuse c ln kn)) = length (mc_seg c))
    by (intros ln kn; destruct (m_refuse_sizes c ln kn) as [E _]; rewrite E; reflexivity).
  assert (U : forall i f, length (mc_seg (m_upd c i f)) = length (mc_seg c))
    by (intros i f; unfold m_upd, m_set_segs; cbn [mc_seg]; apply upd_nth_length).
  unfold mk_disp. cbv zeta.
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [h_role_word ?a] => destruct (h_role_word a)
         | |- context [cat_row ?a] => destruct (cat_row a)
         end; first [ split; [apply m_refuse_grows | apply R] | split; [apply m_upd_grows | apply U] ].
Qed.

(* the K cut's entry gi is an entry of the final model, so the walk's stores into it lie in M_FILE_FP's first range *)
Lemma ki_gi_final : forall mcc gi k vv line rest fin,
  (gi < length (mc_seg mcc))%nat -> mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = fin ->
  (gi < length (mc_seg fin))%nat.
Proof.
intros mcc gi k vv line rest fin Hgi Hfin. unfold mf_fin in Hfin.
destruct (ki_disp_grows mcc gi k vv (line + 1)) as [_ HL].
assert (HC : mf_cur_ok (fst (mk_disp mcc gi k vv (line + 1), Some gi)) (snd (mk_disp mcc gi k vv (line + 1), Some gi)))
  by (cbn [fst snd]; unfold mf_cur_ok; rewrite HL; exact Hgi).
destruct (m_lines_ok (lines (mf_rest rest)) (mk_disp mcc gi k vv (line + 1), Some gi) (line + 1) HC)
  as [[G _] _].
rewrite Hfin in G. cbn [fst] in G. lia.
Qed.

(* the two models the segment leaves: m_upd keeps every counter; m_refuse adds one refusal *)
Lemma ki_upd_cnt : forall c gi f,
  length (mc_seg (m_upd c gi f)) = length (mc_seg c) /\ mc_kept (m_upd c gi f) = mc_kept c /\
  mc_refused (m_upd c gi f) = mc_refused c /\ mc_overflow (m_upd c gi f) = mc_overflow c /\
  mc_gen (m_upd c gi f) = mc_gen c /\ mc_reading (m_upd c gi f) = mc_reading c.
Proof.
intros c gi f. unfold m_upd, m_set_segs. cbn [mc_seg mc_kept mc_refused mc_overflow mc_gen mc_reading].
rewrite upd_nth_length. repeat split; reflexivity.
Qed.
Lemma ki_refuse_cnt : forall c line kn,
  mc_seg (m_refuse c line kn) = mc_seg c /\ mc_refused (m_refuse c line kn) = mc_refused c + 1 /\
  mc_overflow (m_refuse c line kn) = mc_overflow c /\ mc_gen (m_refuse c line kn) = mc_gen c /\
  mc_reading (m_refuse c line kn) = mc_reading c /\
  (length (mc_kept c) <= length (mc_kept (m_refuse c line kn)))%nat.
Proof.
intros c line kn. destruct (m_refuse_sizes c line kn) as [E L].
split; [exact E|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity | exact (proj1 L)].
Qed.

(* ================================ the mconf block after the hit path ================================ *)
Local Notation le4 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.

(* ---------------------------------------------- lists ---------------------------------------------- *)
Lemma ki_e_nth_firstn : forall {A} n i (l : list A) d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A n; induction n as [|n IH]; intros i l d Hi; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|].
  cbn [firstn nth]. apply IH. lia.
Qed.

Lemma ki_e_nth_skipn : forall {A} n i (l : list A) d, nth i (skipn n l) d = nth (n + i) l d.
Proof.
  intros A n; induction n as [|n IH]; intros i l d; [reflexivity|].
  destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma ki_e_upd_len : forall {A} i (f : A -> A) l, length (upd_nth i f l) = length l.
Proof.
  intros A i f l; revert i; induction l as [|x l IH]; intros [|i]; cbn [upd_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma ki_e_upd_nth_eq : forall {A} i (f : A -> A) l d, (i < length l)%nat -> nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros A i f l d; revert i; induction l as [|x l IH]; intros [|i] Hi; cbn [length] in Hi.
  - lia.
  - lia.
  - reflexivity.
  - cbn [upd_nth nth]. apply IH. lia.
Qed.

Lemma ki_e_upd_nth_ne : forall {A} i j (f : A -> A) l d, i <> j -> nth j (upd_nth i f l) d = nth j l d.
Proof.
  intros A i j f l d; revert i j; induction l as [|x l IH]; intros [|i] [|j] Hij; cbn [upd_nth nth];
    try reflexivity; try lia.
  apply IH. lia.
Qed.

(* ------------------------------------------ fields of a byte list ------------------------------------------ *)
Lemma ki_e_fld_len : forall off n (l : list byte), length (seg_spec.fld off n l) = Nat.min n (length l - off).
Proof. intros. unfold seg_spec.fld. rewrite length_firstn, length_skipn. reflexivity. Qed.

Lemma ki_e_fld_nth : forall off n (l : list byte) i d, (i < n)%nat ->
  nth i (seg_spec.fld off n l) d = nth (off + i) l d.
Proof. intros off n l i d Hi. unfold seg_spec.fld. rewrite ki_e_nth_firstn by exact Hi. apply ki_e_nth_skipn. Qed.

Lemma ki_e_fld_ext : forall (l1 l2 : list byte) off n, length l1 = length l2 ->
  (forall i, (i < n)%nat -> (off + i < length l1)%nat -> nth (off + i) l1 ZB0 = nth (off + i) l2 ZB0) ->
  seg_spec.fld off n l1 = seg_spec.fld off n l2.
Proof.
  intros l1 l2 off n HL H. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !ki_e_fld_len, HL. reflexivity.
  - intros i Hi. rewrite ki_e_fld_len in Hi. rewrite !ki_e_fld_nth by lia. apply H; lia.
Qed.

Lemma ki_e_fld_fld : forall (l : list byte) a m o n, (o + n <= m)%nat ->
  seg_spec.fld o n (seg_spec.fld a m l) = seg_spec.fld (a + o) n l.
Proof.
  intros l a m o n H. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !ki_e_fld_len. lia.
  - intros i Hi. rewrite !ki_e_fld_len in Hi. rewrite !ki_e_fld_nth by lia. f_equal. lia.
Qed.

Lemma ki_e_firstn_fld : forall (l : list byte) off n k, (k <= n)%nat ->
  firstn k (seg_spec.fld off n l) = seg_spec.fld off k l.
Proof. intros l off n k H. unfold seg_spec.fld. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma ki_e_fld_all : forall (l : list byte), seg_spec.fld 0 (length l) l = l.
Proof. intros l. unfold seg_spec.fld. cbn [skipn]. apply firstn_all. Qed.

Lemma ki_e_fld_app_l : forall (X Y : list byte) n, length X = n -> seg_spec.fld 0 n (X ++ Y) = X.
Proof.
  intros X Y n <-. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite ki_e_fld_len, length_app. lia.
  - intros i Hi. rewrite ki_e_fld_len, length_app in Hi. rewrite ki_e_fld_nth by lia. cbn [Nat.add].
    apply app_nth1. lia.
Qed.

Lemma ki_e_fld_app_r : forall (X Y : list byte) o n, length X = o -> length Y = n ->
  seg_spec.fld o n (X ++ Y) = Y.
Proof.
  intros X Y o n <- <-. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite ki_e_fld_len, length_app. lia.
  - intros i Hi. rewrite ki_e_fld_len, length_app in Hi. rewrite ki_e_fld_nth by lia.
    rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma ki_e_firstn_zs : forall n (l : list byte), firstn n (seg_spec.zs l) = seg_spec.zs (firstn n l).
Proof.
  unfold seg_spec.zs. induction n as [|n IH]; intros [|x l]; cbn [firstn map]; try reflexivity.
  f_equal. apply IH.
Qed.

Lemma ki_e_bu8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma ki_e_zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
  induction l as [|z l IH]; intros H; [reflexivity|].
  pose proof (Forall_inv H) as Hz. pose proof (Forall_inv_tail H) as Hl. cbv beta in Hz.
  unfold seg_spec.zs, seg_spec.zb in *. cbn [map]. rewrite ki_e_bu8 by exact Hz. f_equal. apply IH. exact Hl.
Qed.

Lemma ki_e_len_le4 : forall v, length (le4 v) = 4%nat.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.length_le4. Qed.

(* the 8 bytes the two stores write: ignore = b at +0, ignore_set = 1 at +4 *)
Lemma ki_e_ys1_bytes : forall (b : bool) k, (k < 8)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 (seg_spec.b2z b)) ++ le4 (Z_to_bv 64 1)) ZB0) =
  if (k <? 4)%nat then le_byte (seg_spec.b2z b) 4 k else le_byte 1 4 (k - 4).
Proof. intros b k Hk. destruct b; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia. Qed.

(* --------------------------------------------- the patch --------------------------------------------- *)
(* bs with the bytes [p, p + |ys|) replaced by ys *)
Definition ki_e_patch (bs ys : list byte) (p : nat) : list byte := firstn p bs ++ ys ++ skipn (p + length ys) bs.

Lemma ki_e_patch_len : forall bs ys p, (p + length ys <= length bs)%nat -> length (ki_e_patch bs ys p) = length bs.
Proof. intros bs ys p H. unfold ki_e_patch. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma ki_e_patch_out : forall bs ys p i d, (p + length ys <= length bs)%nat -> (i < p \/ p + length ys <= i)%nat ->
  nth i (ki_e_patch bs ys p) d = nth i bs d.
Proof.
  intros bs ys p i d HL Hi. unfold ki_e_patch.
  assert (Lf : length (firstn p bs) = p) by (rewrite length_firstn; lia).
  destruct Hi as [Hi|Hi].
  - rewrite app_nth1 by lia. apply ki_e_nth_firstn. exact Hi.
  - rewrite app_nth2 by lia. rewrite Lf. rewrite app_nth2 by lia. rewrite ki_e_nth_skipn. f_equal. lia.
Qed.

Lemma ki_e_patch_in : forall bs ys p i d, (p + length ys <= length bs)%nat -> (p <= i < p + length ys)%nat ->
  nth i (ki_e_patch bs ys p) d = nth (i - p) ys d.
Proof.
  intros bs ys p i d HL Hi. unfold ki_e_patch.
  assert (Lf : length (firstn p bs) = p) by (rewrite length_firstn; lia).
  rewrite app_nth2 by lia. rewrite Lf. apply app_nth1. lia.
Qed.

Lemma ki_e_fld_patch_out : forall bs ys p off n, (p + length ys <= length bs)%nat ->
  (off + n <= p \/ p + length ys <= off)%nat ->
  seg_spec.fld off n (ki_e_patch bs ys p) = seg_spec.fld off n bs.
Proof.
  intros bs ys p off n HL Hd. apply ki_e_fld_ext; [apply ki_e_patch_len; exact HL|].
  intros i Hi _. apply ki_e_patch_out; [exact HL | lia].
Qed.

Lemma ki_e_fld_patch_at : forall o bs ys p off n, (p + length ys <= length bs)%nat -> off = (p + o)%nat ->
  (o + n <= length ys)%nat -> seg_spec.fld off n (ki_e_patch bs ys p) = seg_spec.fld o n ys.
Proof.
  intros o bs ys p off n HL -> Ho. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !ki_e_fld_len, ki_e_patch_len by exact HL. lia.
  - intros i Hi. rewrite ki_e_fld_len, ki_e_patch_len in Hi by exact HL.
    rewrite !ki_e_fld_nth by lia. rewrite ki_e_patch_in by lia. f_equal. lia.
Qed.

Lemma ki_e_bytes_patch : forall (rd rd' : reader) (a : Z) (bs ys : list byte) (off : nat),
  sa_bytes rd a bs -> (off + length ys <= length bs)%nat ->
  (forall i, (i < length bs)%nat -> ~ (off <= i < off + length ys)%nat -> rd' (a + Z.of_nat i) = rd (a + Z.of_nat i)) ->
  sa_bytes rd' (a + Z.of_nat off) ys ->
  sa_bytes rd' a (firstn off bs ++ ys ++ skipn (off + length ys) bs).
Proof.
  intros rd rd' a bs ys off HB HL HO HY.
  change (firstn off bs ++ ys ++ skipn (off + length ys) bs) with (ki_e_patch bs ys off).
  intros i Hi. rewrite ki_e_patch_len in Hi by exact HL.
  destruct (Nat.lt_ge_cases i off) as [H1|H1].
  - rewrite ki_e_patch_out by lia. rewrite HO by lia. exact (HB i Hi).
  - destruct (Nat.lt_ge_cases i (off + length ys)) as [H2|H2].
    + rewrite ki_e_patch_in by lia.
      replace (a + Z.of_nat i) with (a + Z.of_nat off + Z.of_nat (i - off)) by lia.
      exact (HY (i - off)%nat ltac:(lia)).
    + rewrite ki_e_patch_out by lia. rewrite HO by lia. exact (HB i Hi).
Qed.

(* ------------------------------------- a reader between the two writes ------------------------------------- *)
(* rd' on [lo, hi), rd elsewhere *)
Definition ki_e_ovl (rd' rd : reader) (lo hi : Z) : reader :=
  fun x => if (lo <=? x) && (x <? hi) then rd' x else rd x.

Lemma ki_e_ovl_in : forall rd' rd lo hi x, lo <= x < hi -> ki_e_ovl rd' rd lo hi x = rd' x.
Proof.
  intros rd' rd lo hi x Hx. unfold ki_e_ovl.
  replace ((lo <=? x) && (x <? hi)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma ki_e_ovl_out : forall rd' rd lo hi x, ~ (lo <= x < hi) -> ki_e_ovl rd' rd lo hi x = rd x.
Proof.
  intros rd' rd lo hi x Hx. unfold ki_e_ovl.
  replace ((lo <=? x) && (x <? hi)) with false; [reflexivity|].
  symmetry. apply andb_false_iff. destruct (Z.le_gt_cases lo x).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.leb_gt. lia.
Qed.

Lemma ki_e_ovl_cases : forall rd' rd lo hi x,
  ki_e_ovl rd' rd lo hi x = rd' x \/ (~ (lo <= x < hi) /\ ki_e_ovl rd' rd lo hi x = rd x).
Proof.
  intros rd' rd lo hi x. destruct (Z.le_gt_cases lo x) as [L|L]; [destruct (Z.le_gt_cases hi x) as [M|M]|].
  - right. split; [lia|]. apply ki_e_ovl_out. lia.
  - left. apply ki_e_ovl_in. lia.
  - right. split; [lia|]. apply ki_e_ovl_out. lia.
Qed.

(* --------------------------------------- the mconf after the writes --------------------------------------- *)
Lemma ki_e_mconf_ign : forall (rd rd' : reader) (c : Z) (mc : mconf) (gi : nat) (b : bool) (f : list Z),
  sa_mconf rd c mc -> (gi < length (mc_seg mc))%nat ->
  (length f < 96)%nat -> ~ In 0 f ->
  (forall x, c <= x < c + seg_spec.SEG_M_SIZE ->
     ~ (seg_spec.mseg_addr c gi + 24 <= x < seg_spec.mseg_addr c gi + 32) ->
     ~ (seg_spec.mseg_addr c gi + 156 <= x < seg_spec.mseg_addr c gi + 156 + Z.of_nat (length f) + 1) ->
     rd' x = rd x) ->
  sa_val rd' (seg_spec.mseg_addr c gi + 24) 4 (seg_spec.b2z b) ->
  sa_val rd' (seg_spec.mseg_addr c gi + 28) 4 1 ->
  sa_zs rd' (seg_spec.mseg_addr c gi + 156) (f ++ [0]) ->
  (forall x v, rd' x = Some v -> 0 <= v < 256) ->
  sa_mconf rd' c (m_upd mc gi (ms_with_ignore b f)).
Proof.
  intros rd rd' c mc gi b f HM Hgi Hf Hf0 HO HV1 HV2 HZ HR.
  destruct HM as (bs & HB & HE).
  pose proof HE as (HL & H32 & HS & HN & HOV & HRF & HK8 & HK & HKP & HNK & HG & HRD).
  unfold seg_spec.SEG_M_SIZE in HL, HO.
  assert (Hg32 : (gi < 32)%nat) by lia.
  assert (HA : seg_spec.mseg_addr c gi = c + Z.of_nat (256 * gi)).
  { unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia. }
  rewrite HA in HO, HV1, HV2, HZ.
  (* the bytes of f and its NUL *)
  assert (HfB : Forall (fun z => 0 <= z < 256) (f ++ [0])).
  { apply Forall_forall. intros z Hz. apply (In_nth _ _ 0) in Hz as (k & Hk & Ek). subst z. cbv beta.
    apply (HR (c + Z.of_nat (256 * gi) + 156 + Z.of_nat k)). exact (HZ k Hk). }
  (* the new bytes: bs patched at 256 gi + 24 with the two words, then at 256 gi + 156 with f and its NUL *)
  set (ys1 := le4 (Z_to_bv 64 (seg_spec.b2z b)) ++ le4 (Z_to_bv 64 1)).
  assert (Ly1 : length ys1 = 8%nat) by (unfold ys1; rewrite length_app, !ki_e_len_le4; reflexivity).
  set (ys2 := seg_spec.zb (f ++ [0])).
  assert (Ly2 : length ys2 = S (length f)).
  { unfold ys2, seg_spec.zb. rewrite length_map, length_app. cbn [length]. lia. }
  assert (P1 : (256 * gi + 24 + length ys1 <= length bs)%nat) by lia.
  set (bs1 := ki_e_patch bs ys1 (256 * gi + 24)).
  assert (Lb1 : length bs1 = length bs) by (unfold bs1; apply ki_e_patch_len; exact P1).
  assert (P2 : (256 * gi + 156 + length ys2 <= length bs1)%nat) by lia.
  set (bs2 := ki_e_patch bs1 ys2 (256 * gi + 156)).
  assert (Lb2 : length bs2 = length bs) by (unfold bs2; rewrite ki_e_patch_len by exact P2; exact Lb1).
  (* rd' reads bs2 at c *)
  assert (HB1 : sa_bytes (ki_e_ovl rd' rd (c + Z.of_nat (256 * gi) + 24) (c + Z.of_nat (256 * gi) + 32)) c bs1).
  { unfold bs1, ki_e_patch. apply ki_e_bytes_patch with (rd := rd).
    - exact HB.
    - exact P1.
    - intros i Hi Hn. apply ki_e_ovl_out. lia.
    - intros k Hk. rewrite Ly1 in Hk. rewrite ki_e_ovl_in by lia.
      destruct (Nat.lt_ge_cases k 4) as [K|K].
      + replace (c + Z.of_nat (256 * gi + 24) + Z.of_nat k) with (c + Z.of_nat (256 * gi) + 24 + Z.of_nat k) by lia.
        rewrite (HV1 k K). unfold ys1. rewrite ki_e_ys1_bytes by lia. rewrite (proj2 (Nat.ltb_lt k 4) K).
        reflexivity.
      + replace (c + Z.of_nat (256 * gi + 24) + Z.of_nat k)
          with (c + Z.of_nat (256 * gi) + 28 + Z.of_nat (k - 4)) by lia.
        rewrite (HV2 (k - 4)%nat) by lia. unfold ys1. rewrite ki_e_ys1_bytes by lia.
        rewrite (proj2 (Nat.ltb_ge k 4) K). reflexivity. }
  assert (HB2 : sa_bytes rd' c bs2).
  { unfold bs2, ki_e_patch.
    apply ki_e_bytes_patch with (rd := ki_e_ovl rd' rd (c + Z.of_nat (256 * gi) + 24) (c + Z.of_nat (256 * gi) + 32)).
    - exact HB1.
    - exact P2.
    - intros i Hi Hn. rewrite Lb1 in Hi.
      destruct (ki_e_ovl_cases rd' rd (c + Z.of_nat (256 * gi) + 24) (c + Z.of_nat (256 * gi) + 32) (c + Z.of_nat i))
        as [E|[Hn' E]]; rewrite E; [reflexivity|].
      apply HO; [lia | exact Hn' | lia].
    - intros k Hk. rewrite Ly2 in Hk.
      replace (c + Z.of_nat (256 * gi + 156) + Z.of_nat k) with (c + Z.of_nat (256 * gi) + 156 + Z.of_nat k) by lia.
      rewrite (HZ k) by (rewrite length_app; cbn [length]; lia).
      f_equal. unfold ys2, seg_spec.zb. change ZB0 with (Z_to_bv 8 0). rewrite map_nth.
      rewrite ki_e_bu8; [reflexivity|].
      apply (proj1 (Forall_forall _ _) HfB). apply nth_In. rewrite length_app. cbn [length]. lia. }
  (* the fields: away from the two patches, bs2 is bs *)
  assert (Fout : forall off n,
    (off + n <= 256 * gi + 24 \/ (256 * gi + 32 <= off /\ off + n <= 256 * gi + 156) \/
     256 * gi + 157 + length f <= off)%nat ->
    seg_spec.fld off n bs2 = seg_spec.fld off n bs).
  { intros off n Hd. unfold bs2. rewrite ki_e_fld_patch_out by lia. unfold bs1. apply ki_e_fld_patch_out; lia. }
  assert (Un : forall o n,
    (o + n <= 24 \/ (32 <= o /\ o + n <= 156) \/ (157 + length f <= o /\ o + n <= 256))%nat ->
    seg_spec.fld o n (seg_spec.fld (256 * gi) 256 bs2) = seg_spec.fld o n (seg_spec.fld (256 * gi) 256 bs)).
  { intros o n Ho. rewrite !ki_e_fld_fld by lia. apply Fout. lia. }
  unfold sa_mconf, sa_mconfp. exists bs2. split; [exact HB2|].
  unfold m_upd, m_set_segs, seg_spec.mconf_encp.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  rewrite ki_e_upd_len.
  unfold seg_spec.fldz, seg_spec.MC_N, seg_spec.MC_OVERFLOW, seg_spec.MC_REFUSED, seg_spec.MC_KEPT,
    seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - rewrite Lb2. unfold seg_spec.SEG_M_SIZE. exact HL.
  - exact H32.
  - intros i Hi. destruct (Nat.eq_dec i gi) as [->|Hne].
    + (* entry gi: ignore, ignore_set and ignore_file are the new ones, every other field is the old one *)
      rewrite ki_e_upd_nth_eq by exact Hgi.
      destruct (HS gi Hgi) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
      unfold ms_with_ignore, seg_spec.mseg_enc.
      cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file ms_ignore_file
        ms_gen].
      unfold seg_spec.fldz, seg_spec.MS_ROLE, seg_spec.MS_ROLE_SET, seg_spec.MS_IGNORE, seg_spec.MS_IGNORE_SET,
        seg_spec.MS_MODEL_SET, seg_spec.MS_MODEL, seg_spec.MS_ROLE_FILE, seg_spec.MS_IGNORE_FILE, seg_spec.MS_GEN.
      split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      * rewrite !ki_e_fld_len. lia.
      * rewrite Un by lia. exact E1.
      * rewrite Un by lia. exact E2.
      * rewrite Un by lia. exact E3.
      * unfold seg_spec.flag_enc. rewrite ki_e_fld_fld by lia. unfold bs2. rewrite ki_e_fld_patch_out by lia.
        unfold bs1. rewrite (ki_e_fld_patch_at 0) by lia. unfold ys1.
        etransitivity; [apply ki_e_fld_app_l; rewrite ki_e_len_le4; reflexivity | reflexivity].
      * unfold seg_spec.flag_enc. rewrite ki_e_fld_fld by lia. unfold bs2. rewrite ki_e_fld_patch_out by lia.
        unfold bs1. rewrite (ki_e_fld_patch_at 4) by lia. unfold ys1.
        etransitivity; [apply ki_e_fld_app_r; rewrite ki_e_len_le4; reflexivity | reflexivity].
      * rewrite Un by lia. exact E6.
      * rewrite Un by lia. exact E7.
      * rewrite Un by lia. exact E8.
      * unfold seg_spec.cstr_enc. split; [|split; [exact Hf|split; [exact Hf0|]]].
        -- rewrite !ki_e_fld_len. lia.
        -- rewrite ki_e_firstn_zs, ki_e_firstn_fld by lia. rewrite ki_e_fld_fld by lia.
           unfold bs2. rewrite (ki_e_fld_patch_at 0) by lia. rewrite <- Ly2, ki_e_fld_all.
           unfold ys2. apply ki_e_zs_zb. exact HfB.
      * rewrite Un by lia. exact E10.
    + (* entry i <> gi: untouched *)
      rewrite ki_e_upd_nth_ne by lia. rewrite Fout by lia. exact (HS i Hi).
  - rewrite Fout by lia. exact HN.
  - rewrite Fout by lia. exact HOV.
  - rewrite Fout by lia. exact HRF.
  - exact HK8.
  - intros i Hi. rewrite !Fout by lia. exact (HK i Hi).
  - intros i Hi. rewrite Fout by lia. exact (HKP i Hi).
  - rewrite Fout by lia. exact HNK.
  - rewrite Fout by lia. exact HG.
  - rewrite Fout by lia. exact HRD.
Qed.
