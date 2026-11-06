(* m_file on fuzz_segconf.asan (image A), segment S_MF_KIGNP (KIGN 0x8693c -> KKNOCK 0x86b20 or KDONE 0x86cd0): the
   facts of the model and of the reader its walk (m_file_s_kign*.v) uses. The KIGNP segment lane of the G2 walk owner's G2.
   proves no function (kind: model lemma of m_file's walk, segment S_MF_KIGNP).

   - ki_dec: the value test of the code, in the code's order (ieq "yes" 0x86964, "true" 0x86980, v[0] = '1' 0x869ac,
     ieq "no" 0x869c0, "false" 0x869d8, v[0] = '0' 0x86cb0), and mk_disp (m_file_m.v) at the KIGN cut reduced by it.
   - the snprintf text of the hit path (0x86a34, "%s" of c->reading) is c->reading itself.
   - the key and the value as list byte for ieq_contract (lib/A/Prog/ieq_c.v ieq_pre: sa_bytes of the n bytes at s):
     the bytes of a slice of the text, read through an ASan reader, are bytes.
   - the sizes of the two models the segment leaves (m_upd, m_refuse) and the cursor's entry inside the final model,
     over the shared model facts of lib/A/Prog/m_file_mdl.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_mdl.
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
(* the shared model facts are lib/A/Prog/m_file_mdl.v's (the KEYA segment lane): upd_nth_length, m_refuse_sizes, mf_grows,
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
