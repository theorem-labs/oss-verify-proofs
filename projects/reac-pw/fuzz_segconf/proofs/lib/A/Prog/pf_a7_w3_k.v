(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the facts piece KWOK of segment A7 of
   reac_segconf_parse_file's walk needs beside the walk itself (segment A7's proof, 2026-10-30).
   The walk is lib/A/Prog/pf_a7_w3.v (a7_w3 : A7_S_KWOK B, pf_a7_m.v): KWOK 0x882f0 -> SEG 0x887a4, UNK 0x880e4 or
   the funnel FUN 0x88064. No instruction is walked here.

   - the header's body and name as C strings through a reader: body[7] (the byte 0x88304 loads), the body from
     byte 7 on (the string trim gets at 0x88310), and the name trim leaves at np = body + 7 + lead
     (lead = trim_lead (skipn 7 body)): its bytes and NUL from trim's post (trim_c.v: the first
     lead + |r_trim| bytes of the string, then a NUL), its slack after the NUL from the body's own bytes and
     slack, which trim does not touch; name[0] (the byte 0x88328 loads) is hd0 name; the name stays in buf;
   - the step of each exit as pf_a7_f.v's r_header equations: UNK (body[7] no blank), FUN after F_noname and
     after F_toolong, SEG (pf_pieces.v's pf_seg_step, by pf_a7_f.v's a7_get_is_seg_step). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase trim_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a7_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** 1. Lists *)
Lemma w3_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.

Lemma w3_nul7 : forall body, ~ In 0 body -> ~ In 0 (skipn 7 body).
Proof. intros body H. exact (nulfree_skipn 7 body H). Qed.

(* where the name sits in the body from byte 7 on (pfA_facts' L_trim) *)
Lemma w3_name_facts : forall body, ~ In 0 body ->
  (seg_spec.trim_lead (skipn 7 body) + length (a7_name body) <= length (skipn 7 body))%nat /\
  a7_name body = firstn (length (a7_name body)) (skipn (seg_spec.trim_lead (skipn 7 body)) (skipn 7 body)) /\
  ~ In 0 (a7_name body).
Proof. intros body H. unfold a7_name. exact (L_trim_holds (skipn 7 body) (w3_nul7 body H)). Qed.

Lemma w3_name_nth : forall body i, ~ In 0 body -> (i < length (a7_name body))%nat ->
  nth i (a7_name body) 0 = nth (7 + (seg_spec.trim_lead (skipn 7 body) + i)) body 0.
Proof.
  intros body i H Hi. destruct (w3_name_facts body H) as (_ & HE & _).
  rewrite HE at 1. rewrite nth_firstn.
  destruct (Nat.ltb_spec i (length (a7_name body))) as [_|]; [|lia].
  rewrite !w3_nth_skipn. reflexivity.
Qed.

(* the name's address: the body's, plus the keyword, plus the blanks trim skips *)
Definition w3_np (bp : Z) (body : list Z) : Z := bp + 7 + Z.of_nat (seg_spec.trim_lead (skipn 7 body)).

(** ** 2. The body and the name through a reader *)
Lemma w3_zs_nth : forall (rd : reader) p (s : list Z) i, sa_zs rd p (s ++ [0]) -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i s 0).
Proof.
  intros rd p s i H Hi. rewrite (H i) by (rewrite length_app; cbn [length]; lia).
  destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hg].
  - rewrite app_nth1 by exact Hl. reflexivity.
  - assert (i = length s) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    rewrite nth_overflow by lia. reflexivity.
Qed.

(* the bytes of trim's post list: the kept prefix, then the NUL (trim_t.v's sa_bytes_nth_lt / _end) *)
Lemma w3_zb_nth_lt : forall (l : list Z) i, (i < length l)%nat ->
  nth i (seg_spec.zb l ++ [seg_spec.ZERO]) ZB0 = Z_to_bv 8 (nth i l 0).
Proof.
  intros l i Hi. unfold seg_spec.zb. rewrite app_nth1 by (rewrite length_map; exact Hi).
  change ZB0 with (Z_to_bv 8 0). apply map_nth.
Qed.
Lemma w3_zb_nth_end : forall (l : list Z) i, length l = i ->
  nth i (seg_spec.zb l ++ [seg_spec.ZERO]) ZB0 = seg_spec.ZERO.
Proof.
  intros l i Hi. unfold seg_spec.zb. rewrite app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Hi, Nat.sub_diag. reflexivity.
Qed.

(* body[7], the byte 0x88304 loads (the body's NUL when the body is the bare keyword) *)
Lemma w3_byte7 : forall (rd : reader) bp body, sa_str rd bp body -> (7 <= length body)%nat ->
  rd (bp + 7) = Some (nth 7 body 0).
Proof.
  intros rd bp body ((HZ & _) & _) H7. pose proof (w3_zs_nth rd bp body 7 HZ H7) as E.
  change (Z.of_nat 7) with 7 in E. exact E.
Qed.

(* the C string trim gets at 0x88310: the body from byte 7 on, with the body's own NUL and slack *)
Lemma w3_skip7_str : forall (rd : reader) bp body, sa_str rd bp body -> (7 <= length body)%nat ->
  sa_str rd (bp + 7) (skipn 7 body).
Proof.
  intros rd bp body ((HZ & HN) & HT) H7. split; [split|].
  - intros i Hi. rewrite length_app, length_skipn in Hi; cbn [length] in Hi.
    replace (bp + 7 + Z.of_nat i) with (bp + Z.of_nat (7 + i)) by lia.
    rewrite (w3_zs_nth rd bp body (7 + i) HZ) by lia. f_equal.
    destruct (Nat.lt_ge_cases i (length (skipn 7 body))) as [Hl|Hg].
    + rewrite app_nth1 by exact Hl. rewrite w3_nth_skipn. reflexivity.
    + rewrite length_skipn in Hg. rewrite app_nth2 by (rewrite length_skipn; lia).
      rewrite length_skipn. assert (Hi' : i = (length body - 7)%nat) by lia. subst i.
      rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
  - exact (w3_nul7 body HN).
  - rewrite length_skipn. replace (bp + 7 + Z.of_nat (length body - 7)) with (bp + Z.of_nat (length body)) by lia.
    exact HT.
Qed.

(* the name after trim(body + 7): its bytes and NUL are trim's post (sa_bytes at body + 7 of the first
   lead + |name| bytes of the string, then a NUL); the bytes after the NUL up to the next 8-byte boundary are the
   body's own bytes or its slack, which trim did not write (KEEP) *)
Lemma w3_name_str : forall segs H mem H' mem' bp body,
  sa_str (aview segs H mem) bp body -> (7 <= length body)%nat ->
  sa_bytes (aview segs H' mem') (bp + 7)
    (seg_spec.zb (firstn (seg_spec.trim_lead (skipn 7 body) + length (r_trim (skipn 7 body))) (skipn 7 body)) ++
     [seg_spec.ZERO]) ->
  (forall a, w3_np bp body + Z.of_nat (length (a7_name body)) < a ->
     a < bp + Z.of_nat (length body) - (bp + Z.of_nat (length body)) mod 8 + 8 ->
     aview segs H' mem' a = aview segs H mem a) ->
  sa_str (aview segs H' mem') (w3_np bp body) (a7_name body).
Proof.
  intros segs H mem H' mem' bp body HS H7 HB HK.
  change (r_trim (skipn 7 body)) with (a7_name body) in HB.
  pose proof HS as ((HZ & HN) & HT).
  destruct (w3_name_facts body HN) as (HL & _ & HNN).
  rewrite length_skipn in HL.
  unfold w3_np in *.
  set (lead := seg_spec.trim_lead (skipn 7 body)) in *.
  set (nm := a7_name body) in *.
  (* the body's bytes are bytes *)
  assert (HR : forall j, (j <= length body)%nat -> 0 <= nth j body 0 < 256).
  { intros j Hj. exact (sa_aview_rng _ _ _ _ _ (w3_zs_nth _ bp body j HZ Hj)). }
  assert (HBL : length (seg_spec.zb (firstn (lead + length nm) (skipn 7 body)) ++ [seg_spec.ZERO]) =
                S (lead + length nm)).
  { unfold seg_spec.zb. rewrite length_app, length_map, length_firstn, length_skipn. cbn [length]. lia. }
  split; [split|].
  - intros i Hi. rewrite length_app in Hi; cbn [length] in Hi.
    replace (bp + 7 + Z.of_nat lead + Z.of_nat i) with (bp + 7 + Z.of_nat (lead + i)) by lia.
    rewrite (HB (lead + i)%nat) by (rewrite HBL; lia). f_equal.
    destruct (Nat.lt_ge_cases i (length nm)) as [Hl | Hg].
    + rewrite (w3_zb_nth_lt _ (lead + i)) by (rewrite length_firstn, length_skipn; lia).
      rewrite nth_firstn.
      destruct (Nat.ltb_spec (lead + i) (lead + length nm)) as [_|]; [|lia].
      rewrite w3_nth_skipn. rewrite (app_nth1 nm [0] 0 Hl).
      subst nm. rewrite (w3_name_nth body i HN Hl). fold lead.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply HR. lia.
    + assert (Hi' : i = length nm) by lia. subst i.
      rewrite (w3_zb_nth_end _ (lead + length nm)) by (rewrite length_firstn, length_skipn; lia).
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - exact HNN.
  - intros x Hx.
    set (e := bp + 7 + Z.of_nat lead + Z.of_nat (length nm)) in *.
    set (E := bp + Z.of_nat (length body)) in *.
    assert (HeE : e <= E) by (subst e E; lia).
    pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
    pose proof (Z.div_mod E 8 ltac:(lia)) as DE. pose proof (Z.mod_pos_bound E 8 ltac:(lia)) as ME.
    pose proof (Z.div_le_mono e E 8 ltac:(lia) HeE) as Dm.
    rewrite HK by lia.
    destruct (Z_le_gt_dec x E) as [Hle | Hgt].
    + replace x with (bp + Z.of_nat (Z.to_nat (x - bp))) by lia.
      rewrite (w3_zs_nth _ bp body (Z.to_nat (x - bp)) HZ) by lia. discriminate.
    + unfold sa_tail in HT. apply HT. lia.
Qed.

(* name[0], the byte 0x88328 loads: hd0 name (the name's NUL when it is empty) *)
Lemma w3_name_hd : forall (rd : reader) np nm, sa_str rd np nm -> rd np = Some (hd0 nm).
Proof.
  intros rd np nm ((HZ & _) & _). pose proof (w3_zs_nth rd np nm 0 HZ ltac:(lia)) as E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E. rewrite E. destruct nm; reflexivity.
Qed.

(* the name stays in buf *)
Lemma w3_name_inb : forall b bp body, pf_inb b bp body -> ~ In 0 body -> (7 <= length body)%nat ->
  pf_inb b (w3_np bp body) (a7_name body).
Proof.
  intros b bp body [H1 H2] HN H7. destruct (w3_name_facts body HN) as (HL & _).
  rewrite length_skipn in HL. unfold pf_inb, w3_np. lia.
Qed.

(* 1 <= |name| <= 15 on the SEG exit *)
Lemma w3_name_len : forall nm, hd0 nm <> 0 -> (length nm < 16)%nat -> (1 <= length nm <= 15)%nat.
Proof. intros [|x nm] H1 H2; cbn in *; [lia | lia]. Qed.

(** ** 3. The step of each exit *)
Section post.
Variables (rc : rconf) (nm : list Z) (ln : Z) (l : list Z) (ci : nat).
Hypothesis HCL : strchr l RBR = Some ci.
Hypothesis HNUL : nth (S ci) l 0 = 0.

(* UNK 0x880e4 from 0x8830c: body[7] is neither ' ' nor '\t' *)
Lemma w3_post_unk : nth 7 (a7_body l ci) 0 <> 32 -> nth 7 (a7_body l ci) 0 <> 9 ->
  r_header rc nm ln l = (refuse rc ln F_unknown [AS (a7_body l ci)], None, nm).
Proof.
  intros H1 H2. apply (a7_hdr_unknown rc nm ln l ci HCL HNUL). right. exact (a7_sp_tab_false _ H1 H2).
Qed.

Hypothesis HKW : strncasecmp (a7_body l ci) S_segment 7 = 0.

(* FUN after F_noname (0x88794): body[7] a blank, the name empty *)
Lemma w3_post_noname : nth 7 (a7_body l ci) 0 = 32 \/ nth 7 (a7_body l ci) 0 = 9 ->
  hd0 (a7_name (a7_body l ci)) = 0 ->
  r_header rc nm ln l = (refuse rc ln F_noname [], None, nm).
Proof. intros H1 H2. exact (a7_hdr_noname rc nm ln l ci HCL HNUL HKW (a7_sp_tab_true _ H1) H2). Qed.

(* FUN after F_toolong (0x8835c): 16 bytes or more *)
Lemma w3_post_toolong : nth 7 (a7_body l ci) 0 = 32 \/ nth 7 (a7_body l ci) 0 = 9 ->
  hd0 (a7_name (a7_body l ci)) <> 0 -> (16 <= length (a7_name (a7_body l ci)))%nat ->
  r_header rc nm ln l = (refuse rc ln F_toolong [AS (a7_name (a7_body l ci)); AI 15], None, nm).
Proof.
  intros H1 H2 H3. apply (a7_hdr_toolong rc nm ln l ci HCL HNUL HKW (a7_sp_tab_true _ H1) H2).
  rewrite a7_strlen_name. exact H3.
Qed.

(* SEG 0x887a4: 1 to 15 bytes *)
Lemma w3_post_seg : nth 7 (a7_body l ci) 0 = 32 \/ nth 7 (a7_body l ci) 0 = 9 ->
  hd0 (a7_name (a7_body l ci)) <> 0 -> (length (a7_name (a7_body l ci)) < 16)%nat ->
  r_header rc nm ln l = pf_seg_step rc nm ln (a7_name (a7_body l ci)).
Proof.
  intros H1 H2 H3. rewrite <- a7_get_is_seg_step.
  apply (a7_hdr_get rc nm ln l ci HCL HNUL HKW (a7_sp_tab_true _ H1) H2).
  rewrite a7_strlen_name. exact H3.
Qed.
End post.
