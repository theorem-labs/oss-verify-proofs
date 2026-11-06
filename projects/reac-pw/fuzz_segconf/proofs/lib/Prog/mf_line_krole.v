(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the sub-piece S_MF_KROLE of one line (Prog/mf_cuts.v,
    family F3). From the key dispatch KDISP 0x142f8 (the key k at s5 with its length in s8, the value v at s4 with
    its length in s7, cur = Some gi) to KMODEL 0x144d4 or to the tail 0x143d4:
    - [kr_main]: ieq(k, kl, "role" 0x10298) 0x14308; 0 goes to KMODEL ([kr_kmodel], the premise H_MF_KMODEL).
    - [kr_role], [kr_fold_entry], [kr_fold_iter], [kr_fold], [kr_after_fold]: s7 = min(vl, 63) (0x14314), the fold
      0x14328-0x14348 of v into low = sp + 0x28 (the 64 frame bytes [sp + 0x28, sp + 0x68): lower as the code computes
      it, mfp_facts.lower_bin), its NUL at low + s7 (0x1435c); low holds h_fold v 64.
    - [kr_iter], [kr_next], [kr_words]: the words loop 0x1436c-0x1439c over m_key.words (five pointers read through
      words_img), strlen 0x14374 and bcmp 0x14388; it computes SegModel.word_go word by word.
    - [kr_hit]: the role table (.rodata 0x10a10: role[i] = i), role_set = 1 0x14574, role 0x14578, then
      snprintf(cur->role_file, 96, "%s", c->reading) 0x14590 (mf_common.mf_snprintf_s), then the tail ([kr_tail]).
    - [kr_refuse]: all five missed: m_refuse(c, line + 1) 0x143a8 (mf_common.mf_refuse_call), then the tail.
    The writes: the callees' frames and low in [sp0 - M_FILE_STACK, sp0), entry gi of seg (role, role_set,
    role_file), m_refuse's slot, n_kept and refused; each path ends with mf_common.mf_post_back over them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  Image Arr ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c mf_cuts
  mfu_facts mf_common mfp_mconf mfp_facts ieq_c strlen_c bcmp_c snprintf_c m_refuse_c printf_facts_c.
Import ListNotations.
Open Scope Z_scope.

(** * Generic facts (no section) *)

Lemma kr_unsigned8 : forall b, 0 <= b < 256 -> bv_unsigned (Z_to_bv 8 b) = b.
Proof. intros b H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma kr_zxb : forall b, 0 <= b < 256 -> zxb (Z_to_bv 8 b) = Z_to_bv 64 b.
Proof. intros b H. unfold zxb. rewrite kr_unsigned8 by exact H. reflexivity. Qed.

Lemma kr_le1 : forall (x : word) z, bv_unsigned x mod 256 = z mod 256 -> le1 x = [Z_to_bv 8 z].
Proof.
  intros x z H. rewrite <- (le1_zxb (Z_to_bv 8 z)). unfold le1.
  rewrite <- (Z_to_le_bytes_mod 1 (bv_unsigned x) 8) by lia.
  rewrite <- (Z_to_le_bytes_mod 1 (bv_unsigned (zxb (Z_to_bv 8 z))) 8) by lia.
  f_equal. change (2 ^ 8) with 256. rewrite H. unfold zxb.
  pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 z)) as R. change (bv_modulus 8) with 256 in R.
  rewrite (unsigned_lit (bv_unsigned (Z_to_bv 8 z))) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma kr_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

Lemma kr_zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  cbn [map]. f_equal; [apply kr_unsigned8; exact Hx | exact (IH Hl)].
Qed.

Lemma kr_zb_inj : forall l1 l2, Forall (fun x => 0 <= x < 256) l1 -> Forall (fun x => 0 <= x < 256) l2 ->
  zb l1 = zb l2 -> l1 = l2.
Proof. intros l1 l2 H1 H2 E. rewrite <- (kr_zs_zb l1 H1), <- (kr_zs_zb l2 H2), E. reflexivity. Qed.

Lemma kr_length_zb : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. apply length_map. Qed.

Lemma kr_firstn_all : forall (l : list Z) n, (length l <= n)%nat -> firstn n l = l.
Proof.
  induction l as [|x l IH]; intros [|n] H; cbn [length] in H; try reflexivity; [lia|].
  cbn [firstn]. f_equal. apply IH. lia.
Qed.

Lemma kr_firstn_S : forall (l : list Z) i, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l 0].
Proof.
  induction l as [|x l IH]; intros i H; cbn [length] in H; [lia|].
  destruct i as [|i]; cbn [firstn nth app]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.

Lemma kr_firstn_upd : forall (l : list byte) i x, (i < length l)%nat -> firstn (S i) (upd l i x) = firstn i l ++ [x].
Proof.
  induction l as [|y l IH]; intros i x H; cbn [length] in H; [lia|].
  destruct i as [|i]; cbn [upd firstn app]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.

Lemma kr_In_fs : forall (l : list Z) a b x, In x (firstn a (skipn b l)) -> In x l.
Proof.
  intros l a b x H. assert (H1 : In x (skipn b l)).
  { rewrite <- (firstn_skipn a (skipn b l)). apply in_or_app. left. exact H. }
  rewrite <- (firstn_skipn b l). apply in_or_app. right. exact H1.
Qed.

Lemma kr_Forall_fs : forall (P : Z -> Prop) (l : list Z) a b, Forall P l -> Forall P (firstn a (skipn b l)).
Proof. intros P l a b H. rewrite Forall_forall in *. intros x Hx. apply H. eapply kr_In_fs. exact Hx. Qed.

Lemma kr_nth_fs : forall (l : list Z) a b i, (i < a)%nat -> nth i (firstn a (skipn b l)) 0 = nth (b + i) l 0.
Proof.
  intros l a b. revert l a. induction b as [|b IH]; intros l a i H.
  - cbn [skipn Nat.add]. revert a i H. induction l as [|x l IHl]; intros a i H; [destruct a, i; reflexivity|].
    destruct a as [|a]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IHl. lia.
  - destruct l as [|x l]; [destruct a, i; reflexivity|]. cbn [skipn]. rewrite (IH l a i H). reflexivity.
Qed.

Lemma kr_nth_byte : forall (l : list Z) i, Forall (fun x => 0 <= x < 256) l -> 0 <= nth i l 0 < 256.
Proof.
  intros l i H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact Hi.
  - rewrite nth_overflow by exact Hi. lia.
Qed.

Lemma kr_upd_nth_comp {A} : forall (f g : A -> A) l i, upd_nth i g (upd_nth i f l) = upd_nth i (fun x => g (f x)) l.
Proof. intros f g l. induction l as [|x r IH]; intros i; destruct i; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma kr_upd_nth_ext {A} : forall (f g : A -> A) l i, (forall x, f x = g x) -> upd_nth i f l = upd_nth i g l.
Proof. intros f g l. induction l as [|x r IH]; intros i H; destruct i; cbn; try reflexivity; f_equal; auto. Qed.

Lemma kr_m_upd_comp : forall c0 i f g, m_upd (m_upd c0 i f) i g = m_upd c0 i (fun x => g (f x)).
Proof.
  intros. unfold m_upd, m_set_segs. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  rewrite kr_upd_nth_comp. reflexivity.
Qed.

Lemma kr_m_upd_ext : forall c0 i f g, (forall x, f x = g x) -> m_upd c0 i f = m_upd c0 i g.
Proof. intros c0 i f g H. unfold m_upd. f_equal. apply kr_upd_nth_ext. exact H. Qed.

Lemma kr_m_upd_len : forall c0 i f, length (mc_seg (m_upd c0 i f)) = length (mc_seg c0).
Proof. intros. unfold m_upd, m_set_segs. cbn [mc_seg]. apply upd_nth_length. Qed.

Lemma kr_memcmp : forall n l r v, length l = n -> length r = n -> StrFun.memcmp_model l r n = Some v ->
  -256 < v < 256 /\ (v = 0 <-> l = r).
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. injection H as <-.
    split; [lia|]. split; intros; reflexivity.
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
    cbn [StrFun.memcmp_model] in H. cbn [length] in Hl, Hr. injection Hl as Hl. injection Hr as Hr.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v Hl Hr H) as [R I]. split; [exact R|]. rewrite I.
      assert (Eab : a = b) by (apply bv_eq; exact E). subst b.
      split; [intros ->; reflexivity | intros Q; injection Q as Q; exact Q].
    + injection H as <-. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
      change (bv_modulus 8) with 256 in Ra, Rb. split; [lia|]. split; [lia|].
      intros Q; injection Q as Q1 _; subst b; congruence.
Qed.

Fixpoint kr_beqs (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => (bv_unsigned a =? bv_unsigned b) && kr_beqs r1 r2
  | _, _ => false
  end.

Lemma kr_beqs_eq : forall l1 l2, kr_beqs l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|a r1 IH]; intros [|b r2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma kr_ro : forall m a l, mem_inv rsegs m ->
  ((0 <=? a) && (a + Z.of_nat (length l) <=? 2 ^ 64) && ro_bytes_b rsegs a l)%bool = true -> bytes_at rsegs m a l.
Proof.
  intros m a l MI H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply ro_bytes_at; [exact MI | lia | lia |]. apply ro_bytes_b_sound. exact H3.
Qed.

Lemma kr_forallb_byte : forall l, forallb (fun x => (0 <=? x) && (x <? 256)) l = true -> Forall (fun x => 0 <= x < 256) l.
Proof.
  intros l H. rewrite forallb_forall in H. rewrite Forall_forall. intros x Hx. specialize (H x Hx).
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma kr_nonul_zb : forall l, forallb (fun x => (0 <? x) && (x <? 256)) l = true -> ~ In (Z_to_bv 8 0) (zb l).
Proof.
  intros l H Hin. unfold zb in Hin. apply in_map_iff in Hin as (x & Ex & Hx). rewrite forallb_forall in H.
  specialize (H x Hx). apply andb_true_iff in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
  apply (f_equal bv_unsigned) in Ex. rewrite (kr_unsigned8 x) in Ex by lia. rewrite (kr_unsigned8 0) in Ex by lia. lia.
Qed.

Lemma kr_noimg_sub : forall c0 N a n0, blk_noimg rsegs c0 N -> c0 <= a -> a + n0 <= c0 + N -> blk_noimg rsegs a n0.
Proof. intros c0 N a n0 H H1 H2 i Hi s Hs. replace (a + i) with (c0 + (a - c0 + i)) by lia. apply H; [lia | exact Hs]. Qed.

Lemma kr_outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[a b] W1 IH]; intros W2 x; cbn [app outside].
  - split; [intros H; split; [exact I | exact H] | intros [_ H]; exact H].
  - rewrite IH. tauto.
Qed.

Lemma kr_sub_l : forall W1 W2, sub_fp W1 (W1 ++ W2).
Proof. intros W1 W2 x Hx. apply kr_outside_app in Hx. exact (proj1 Hx). Qed.
Lemma kr_sub_r : forall W1 W2, sub_fp W2 (W1 ++ W2).
Proof. intros W1 W2 x Hx. apply kr_outside_app in Hx. exact (proj2 Hx). Qed.

Lemma kr_rd_bytes : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

(** The byte the fold stores (0x1432c-0x1433c): lower as the code computes it. *)
Lemma kr_lower_le1 : forall b, 0 <= b < 256 ->
  le1 (Z_to_bv 64 (b + Z.shiftl (bv_unsigned (v_sltiu (Z_to_bv 64 (b + -65)) 26)) 5)) = [Z_to_bv 8 (lower b)].
Proof.
  intros b Hb. apply kr_le1. rewrite (lower_bin b Hb). unfold v_sltiu.
  change (bv_wrap 64 26) with 26.
  rewrite (unsigned_lit_wrap (b + -65)). replace (b + -65) with (b - 65) by lia.
  destruct ((b - 65) mod 2 ^ 64 <? 26); cbv iota.
  - rewrite (unsigned_lit 1) by lia. change (Z.shiftl 1 5) with 32. rewrite unsigned_lit by lia. reflexivity.
  - rewrite (unsigned_lit 0) by lia. change (Z.shiftl 0 5) with 0. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma kr_mod8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma kr_span_rd : forall c0 s, c0 mod 16 = 0 -> (length s < 96)%nat ->
  1 <= cstr_span (c0 + MC_READING) s /\ c0 + MC_READING + cstr_span (c0 + MC_READING) s <= c0 + SEG_M_SIZE + 4.
Proof.
  intros c0 s H L. unfold cstr_span, MC_READING, SEG_M_SIZE.
  pose proof (Z.mod_pos_bound (- (c0 + 9140 + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
  Z.div_mod_to_equations. split; lia.
Qed.

Lemma kr_penv : forall m fc lo sp0 lo' sp', printf_env m fc lo sp0 -> lo <= lo' -> sp' <= sp0 -> printf_env m fc lo' sp'.
Proof. intros m fc lo sp0 lo' sp' (A & B & C & D & E) H1 H2. refine (conj A (conj B (conj C (conj _ _)))); lia. Qed.

(** ** The image: "role", the words table and its five strings, the role table *)
Definition KR_ROLE_LIT : Z := 0x10298.
Definition KR_WORDS : list (list Z) := [S_auto; S_master; S_slave; S_tap; S_box].
Definition KR_WPTR : list Z := [0x1030e; 0x10548; 0x1075c; 0x10470; 0x10303].
Definition kr_word (i : nat) : list Z := nth i KR_WORDS [].
Definition kr_wptr (i : nat) : Z := nth i KR_WPTR 0.
Definition kr_sl (i : nat) : list byte :=
  match image_bytes rsegs (kr_wptr i + Z.of_nat (length (kr_word i)) + 1) 7 with Some l => l | None => [] end.
Definition KR_WB : list byte := concat (map (fun z => le8 (Z_to_bv 64 z)) KR_WPTR).
Definition KR_RB : list byte := concat (map (fun z => le4 (Z_to_bv 64 z)) [0; 1; 2; 3; 4]).

Lemma kr_role_at : forall m, mem_inv rsegs m -> cstr_at rsegs m KR_ROLE_LIT S_role.
Proof.
  intros m MI. exists (zb S_role), (zb [102; 97; 108]). split; [apply kr_ro; [exact MI | vm_compute; reflexivity]|].
  split; [vm_compute; reflexivity|]. split.
  - intros H. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H.
  - apply Z.leb_le. vm_compute. reflexivity.
Qed.

Lemma kr_word_at : forall m i, mem_inv rsegs m -> (i < 5)%nat ->
  bytes_at rsegs m (kr_wptr i) (zb (kr_word i) ++ Z_to_bv 8 0 :: kr_sl i).
Proof.
  intros m i MI Hi. do 5 (destruct i as [|i]; [apply kr_ro; [exact MI | vm_compute; reflexivity]|]). lia.
Qed.

Lemma kr_word_facts : forall i, (i < 5)%nat ->
  ~ In (Z_to_bv 8 0) (zb (kr_word i)) /\
  (- (kr_wptr i + Z.of_nat (length (zb (kr_word i))) + 1)) mod 8 <= Z.of_nat (length (kr_sl i)) /\
  Forall (fun x => 0 <= x < 256) (kr_word i) /\ (length (kr_word i) <= 6)%nat /\ 0 < kr_wptr i < 0x20000.
Proof.
  intros i Hi.
  do 5 (destruct i as [|i];
    [refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
     first [ apply kr_nonul_zb; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
           | apply kr_forallb_byte; vm_compute; reflexivity | apply Nat.leb_le; vm_compute; reflexivity
           | apply Z.ltb_lt; vm_compute; reflexivity ] |]).
  lia.
Qed.

Lemma kr_skipn_words : forall i, (i < 5)%nat -> skipn i KR_WORDS = kr_word i :: skipn (S i) KR_WORDS.
Proof. intros i Hi. do 5 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma kr_image_nth : forall n A bs, image_bytes rsegs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|]. cbn in H.
  destruct (seg_rom rsegs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (image_bytes rsegs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  inversion H; subst bs. destruct i as [|i].
  - rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E' i ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma kr_bytes_img : forall m A n bs, image_bytes rsegs A n = Some bs -> 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall a, A <= a < A + Z.of_nat n -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) -> bytes_at rsegs m A bs.
Proof.
  intros m A n bs E H0 H1 H. pose proof (image_bytes_length rsegs n A bs E) as L.
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite H by lia. apply (kr_image_nth n A bs E). lia.
Qed.

Lemma kr_wb_img : match image_bytes rsegs M_KEY_WORDS 40 with Some l => kr_beqs l KR_WB | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma kr_words_rd : forall m i, words_img m -> (i < 5)%nat ->
  ov_read_bytes rsegs m (wa (M_KEY_WORDS + 8 * Z.of_nat i)) 8 = Some (le8 (Z_to_bv 64 (kr_wptr i))).
Proof.
  intros m i HW Hi. pose proof kr_wb_img as H.
  destruct (image_bytes rsegs M_KEY_WORDS 40) as [l|] eqn:E; [|discriminate]. apply kr_beqs_eq in H. subst l.
  assert (B : bytes_at rsegs m M_KEY_WORDS KR_WB).
  { apply (kr_bytes_img m M_KEY_WORDS 40 KR_WB E); [unfold M_KEY_WORDS; lia | unfold M_KEY_WORDS; lia |].
    intros a Ha. apply HW. cbn [Z.of_nat] in Ha. lia. }
  replace (M_KEY_WORDS + 8 * Z.of_nat i) with (M_KEY_WORDS + Z.of_nat (8 * i)) by lia.
  rewrite (bytes_at_ov_read rsegs m M_KEY_WORDS KR_WB (8 * i) 8 B) by (change (length KR_WB) with 40%nat; lia).
  f_equal. do 5 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma kr_rb_ro : ((0 <=? M_KEY_ROLE) && (M_KEY_ROLE + Z.of_nat (length KR_RB) <=? 2 ^ 64) &&
                  ro_bytes_b rsegs M_KEY_ROLE KR_RB)%bool = true.
Proof. vm_compute. reflexivity. Qed.

Lemma kr_role_rd : forall m i, mem_inv rsegs m -> (i < 5)%nat ->
  ov_read_bytes rsegs m (wa (M_KEY_ROLE + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat i))).
Proof.
  intros m i MI Hi. pose proof (kr_ro m M_KEY_ROLE KR_RB MI kr_rb_ro) as B.
  replace (M_KEY_ROLE + 4 * Z.of_nat i) with (M_KEY_ROLE + Z.of_nat (4 * i)) by lia.
  rewrite (bytes_at_ov_read rsegs m M_KEY_ROLE KR_RB (4 * i) 4 B) by (change (length KR_RB) with 20%nat; lia).
  f_equal. do 5 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Ltac kr_unf := unfold mseg_addr, apart, M_FILE_STACK, M_REFUSE_STACK, M_FILE_FRAME, PRINTF_K, SEG_M_SIZE, MSEG_SIZE,
  IEQ_STACK, MC_READING, MS_ROLE, MS_ROLE_SET, MS_ROLE_FILE, M_KEY_ROLE, M_KEY_WORDS in *.
Ltac nlia := kr_unf; lia.

(** * The walk *)
Section KR.
Variables (sp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F0 : bvmap 5 word) (fc0 : bv 32)
  (m0 : word -> option byte) (lo c p line : Z) (mc : mconf) (gi k0 : nat) (rest : list Z)
  (ok kl ov vl : nat) (k v : list Z) (n : nat).
Hypothesis HIEQ : ieq_contract.
Hypothesis HSL : strlen_contract.
Hypothesis HBC : bcmp_contract.
Hypothesis HSN : snprintf_contract.
Hypothesis HMR : m_refuse_contract.
Hypothesis HT : H_MF_TAIL n.
Hypothesis HKM : H_MF_KMODEL n.
Hypothesis Hn : (length rest <= n)%nat.
Hypothesis Hne : rest <> [].
Hypothesis HC0 : mf_ctx m0 fc0 (bv_unsigned sp0) (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis HX0 : mf_text m0 (bv_unsigned sp0) lo c p rest.
Hypothesis HS0 : mf_st m0 (bv_unsigned sp) c mc (Some gi) k0 line rest.
Hypothesis HKV : mk_kv rest ok kl ov vl k v.

Local Abbreviation Sp := (bv_unsigned sp).
Local Abbreviation Sp0 := (bv_unsigned sp0).
Local Abbreviation QP mf := (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F0 m0 lo c k0 mf).
Local Abbreviation KS pc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc m :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 0x3b) a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 s7 s8
       (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x23) (Z_to_bv 64 0x20) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Local Abbreviation Wst := [(Sp0 - M_FILE_STACK, Sp0)].
Local Abbreviation Whit := [(Sp0 - M_FILE_STACK, Sp0); (mseg_addr c gi, mseg_addr c gi + 256)].

(** The model of the role branch. *)
Definition kr_low : list Z := h_fold v 64.
Definition kr_n : nat := Nat.min vl 63.
Definition kr_res (o : option Z) : mconf :=
  match o with
  | Some r => m_upd mc gi (ms_with_role r (snprintf_s 96 F_s [AS (mc_reading mc)]))
  | None => m_refuse mc (line + 1) false
  end.
Local Abbreviation QR := (QP (mf_fin (kr_res (h_role_word kr_low), Some gi) line rest)).

Lemma kr_disp_role : ieq k S_role = true -> mk_disp mc gi k v (line + 1) = kr_res (h_role_word kr_low).
Proof. intros H. unfold mk_disp. rewrite H. unfold kr_res, kr_low. destruct (h_role_word (h_fold v 64)); reflexivity. Qed.

(** ** Facts that hold whatever the memory *)
Lemma kr_ctx_facts : forall m fc, mf_ctx m fc Sp0 Sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  Sp + 208 = Sp0 /\ 341736 <= lo /\ lo + 6160 <= Sp0 /\ Sp0 < 2 ^ 63 /\
  (c + 9240 <= lo \/ Sp0 <= c) /\ 0 < c /\ c + 9244 <= 2 ^ 64 /\ c mod 16 = 0 /\ Sp mod 16 = 0.
Proof.
  intros m fc H. pose proof H as H'. apply mf_ctx_bounds in H'. destruct H' as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  destruct H as (E & _ & _ & _ & _ & _ & C16 & _). unfold M_FILE_FRAME in E. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in B2.
  unfold SEG_M_SIZE in B6, B8. change (sa_img_end SA) with 341736 in B1.
  refine (conj _ (conj B1 (conj _ (conj B3 (conj _ (conj B7 (conj _ (conj C16 B5)))))))); lia.
Qed.

Lemma kr_text_facts : forall m, mf_text m Sp0 lo c p rest ->
  ~ In 0 rest /\ Forall (fun x => 0 <= x < 256) rest /\ 0 < p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64 /\
  (p + Z.of_nat (length rest) + 8 <= lo \/ Sp0 <= p).
Proof.
  intros m HX. pose proof HX as HX'. apply mf_text_props in HX'. destruct HX' as (A & B & C & D & E).
  destruct HX as (_ & _ & _ & AP & _). unfold apart in AP.
  assert (G : Z.of_nat (length rest) + 1 <= cstr_span p rest).
  { unfold cstr_span. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)). lia. }
  refine (conj A (conj B (conj C (conj _ _)))); lia.
Qed.

Lemma kr_line_le : (length (mf_line rest) <= length rest)%nat.
Proof.
  destruct (mf_line_rest rest) as [[E _]|[E _]].
  - apply (f_equal (@length Z)) in E. rewrite length_app in E. cbn [length] in E. lia.
  - apply (f_equal (@length Z)) in E. lia.
Qed.

Lemma kr_st_facts : (gi < length (mc_seg mc))%nat /\ (k0 <= length (mc_kept mc))%nat /\ 0 <= line /\
  line + Z.of_nat (length rest) <= 65535 /\ mc_refused mc + Z.of_nat (length rest) < 2 ^ 32 /\
  mc_overflow mc + Z.of_nat (length rest) < 2 ^ 32 /\ (length (mc_seg mc) <= 32)%nat /\ (1 <= length rest)%nat.
Proof.
  destruct HS0 as (HM & _ & HG & HK & HL0 & HL1 & HR & HO).
  destruct (mconf_atp_bytes rsegs false m0 c mc HM) as (bs & _ & E & _).
  destruct (mconf_enc_bounds false mc bs E) as (_ & B32 & _).
  assert (L1 : (1 <= length rest)%nat).
  { destruct (length rest) eqn:EL; [|lia]. apply length_zero_iff_nil in EL. congruence. }
  cbn [cur_ok] in HG. repeat split; assumption.
Qed.

Lemma kr_mc_facts : (length (mc_reading mc) < 96)%nat /\ ~ In 0 (mc_reading mc) /\
  Forall (fun x => 0 <= x < 256) (mc_reading mc).
Proof.
  destruct HS0 as (HM & _).
  destruct (mconf_atp_bytes rsegs false m0 c mc HM) as (bs & _ & E & _).
  destruct (mconf_enc_bounds false mc bs E) as (_ & _ & _ & _ & _ & _ & R1 & R2 & R3 & _).
  exact (conj R1 (conj R2 R3)).
Qed.

Lemma kr_kv : (ok + kl <= length rest)%nat /\ (ov + vl <= length rest)%nat /\ length k = kl /\ length v = vl /\
  Forall (fun x => 0 <= x < 256) k /\ Forall (fun x => 0 <= x < 256) v /\ ~ In 0 v.
Proof.
  destruct HKV as (H1 & H2 & Ek & Ev). pose proof kr_line_le as LL.
  pose proof (kr_text_facts m0 HX0) as (NZ & FB & _ & _ & _).
  assert (L1 : (ok + kl <= length rest)%nat) by lia. assert (L2 : (ov + vl <= length rest)%nat) by lia.
  refine (conj L1 (conj L2 (conj _ (conj _ (conj _ (conj _ _)))))).
  - rewrite <- Ek, length_firstn, length_skipn. lia.
  - rewrite <- Ev, length_firstn, length_skipn. lia.
  - rewrite <- Ek. apply kr_Forall_fs. exact FB.
  - rewrite <- Ev. apply kr_Forall_fs. exact FB.
  - rewrite <- Ev. intros H. apply NZ. eapply kr_In_fs. exact H.
Qed.

Lemma kr_low_facts : length kr_low = kr_n /\ kr_n = Nat.min vl 63 /\ Forall (fun x => 0 <= x < 256) kr_low.
Proof.
  destruct kr_kv as (_ & _ & _ & Lv & _ & Fv & Nv).
  refine (conj _ (conj eq_refl _)).
  - unfold kr_low, kr_n. rewrite h_fold_length, Lv. reflexivity.
  - unfold kr_low. exact (proj2 (h_fold_props v 64 Nv Fv)).
Qed.

Lemma kr_nth_low : forall i, (i < kr_n)%nat -> nth i kr_low 0 = lower (nth (ov + i) rest 0).
Proof.
  intros i Hi. destruct kr_low_facts as (L1 & L2 & _). destruct kr_kv as (_ & _ & _ & Lv & _).
  unfold kr_low. rewrite h_fold_nth by (fold kr_low; lia). f_equal.
  destruct HKV as (_ & _ & _ & Ev). rewrite <- Ev. apply kr_nth_fs. lia.
Qed.

(** ** The loop facts the walk keeps: the context, the text, c holding mcx, the cur cell. *)
Definition kr_inv (m : word -> option byte) (fc : bv 32) (mcx : mconf) : Prop :=
  mf_ctx m fc Sp0 Sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 /\ mf_text m Sp0 lo c p rest /\
  mconf_atp rsegs false m c mcx /\ cell8 m (Sp + 0x20) (mseg_addr c gi).

Lemma kr_inv0 : kr_inv m0 fc0 mc.
Proof. destruct HS0 as (HM & HQ & _). exact (conj HC0 (conj HX0 (conj HM HQ))). Qed.

Lemma kr_stack_ok : forall m fc mcx d, kr_inv m fc mcx -> d <= 16 + PRINTF_K -> stack_ok rsegs m lo Sp d.
Proof.
  intros m fc mcx d (HC & _) Hd. pose proof (kr_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & STL & STA & STR) & _).
  unfold PRINTF_K in Hd. destruct (stk_split rsegs m lo Sp Sp0 STK ltac:(lia)) as [S1 _].
  refine (conj S1 (conj _ (conj F9 _))); [lia|]. intros a Ha. apply STR. lia.
Qed.

Lemma kr_stack_pf : forall m fc mcx, kr_inv m fc mcx -> stack_ok rsegs m (Sp - PRINTF_K) Sp PRINTF_K.
Proof.
  intros m fc mcx (HC & _). pose proof (kr_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & STL & STA & STR) & _).
  unfold PRINTF_K. destruct (stk_split rsegs m lo Sp Sp0 STK ltac:(lia)) as [S1 _].
  destruct (stk_split rsegs m lo (Sp - 5936) Sp S1 ltac:(lia)) as [_ S2].
  refine (conj S2 (conj _ (conj F9 _))); [lia|]. intros a Ha. apply STR. lia.
Qed.

(** A callee that writes only below sp. *)
Lemma kr_inv_call : forall m m' fc fc' mcx W,
  kr_inv m fc mcx -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm0 fc' -> stk rsegs m' lo Sp ->
  sub_fp W [(lo, Sp)] -> disjoint_from W Sp (Sp0 - Sp) -> disjoint_from W c SEG_M_SIZE ->
  disjoint_from W (Sp + 0x20) 8 -> kr_inv m' fc' mcx.
Proof.
  intros m m' fc fc' mcx W (HC & HX & HM & HQ) MU WM MI FR ST SF D1 D2 D3.
  pose proof (kr_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & _) & _).
  assert (SF3 : sub_fp W [(lo, Sp); (Sp + 0x20, Sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. apply SF. cbn [outside] in *. destruct Hx as (X1 & _ & _ & _). split; [exact X1 | exact I]. }
  assert (TM : MemNorm.task_mem rsegs m') by (eapply mf_task_mem; [exact HC | exact HM | exact MU | exact SF3]).
  assert (STK' : stk rsegs m' lo Sp0).
  { eapply mf_stk_after; [exact STK | exact MU | exact WM | exact ST | lia | exact D1]. }
  refine (conj _ (conj _ (conj _ _))).
  - eapply mf_ctx_transport; [exact HC | exact MU | exact WM | exact MI | exact TM | exact FR | exact STK' | exact SF3].
  - eapply mf_text_transport; [exact HX | exact MU |]. intros x Hx. apply SF. cbn [outside] in *.
    destruct Hx as (X1 & _ & _). split; [lia | exact I].
  - eapply mconf_atp_transport; [exact HM | exact MU | exact D2].
  - eapply cell8_transport; [exact HQ | exact MU | exact D3].
Qed.

(** strlen and bcmp change no byte. *)
Lemma kr_inv_nil : forall m m' fc mcx, kr_inv m fc mcx -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  kr_inv m' fc mcx.
Proof.
  intros m m' fc mcx INV MU WM MI. pose proof INV as (HC & _).
  pose proof (kr_ctx_facts m fc HC) as (F1 & F2 & F3 & _).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _ & _ & (STK & _) & _).
  destruct (stk_split rsegs m lo Sp Sp0 STK ltac:(lia)) as [S1 _].
  eapply kr_inv_call; [exact INV | exact MU | exact WM | exact MI | exact FR | | | exact I | exact I | exact I].
  - eapply stk_transport_disjoint; [exact S1 | exact MU | exact WM | exact I].
  - intros x _. exact I.
Qed.

(** A byte store into low = [sp + 0x28, sp + 0x68). *)
Lemma kr_inv_wbuf : forall m fc mcx a nb, kr_inv m fc mcx -> Sp + 0x28 <= a -> a + Z.of_nat (length nb) <= Sp + 0x68 ->
  store_ok rsegs m (wa a) (length nb) = true -> kr_inv (write_to_mem m (wa a) nb) fc mcx.
Proof.
  intros m fc mcx a nb (HC & HX & HM & HQ) H1 H2 HS.
  pose proof (kr_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _ & _ & (STK & _) & MI).
  assert (MU : munch [(a, a + Z.of_nat (length nb))] m (write_to_mem m (wa a) nb)).
  { apply munch_write; [apply munch_refl | lia | lia | cbn [inside]; left; lia]. }
  assert (WM : wmono rsegs m (write_to_mem m (wa a) nb)) by (apply wmono_write; apply wmono_refl).
  assert (MI' : mem_inv rsegs (write_to_mem m (wa a) nb)) by (apply mem_inv_store; assumption).
  assert (SF3 : sub_fp [(a, a + Z.of_nat (length nb))] [(lo, Sp); (Sp + 0x20, Sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. cbn [outside] in *. destruct Hx as (X1 & X2 & X3 & _). split; [lia | exact I]. }
  assert (TM : MemNorm.task_mem rsegs (write_to_mem m (wa a) nb)) by (eapply mf_task_mem; eassumption).
  assert (STK' : stk rsegs (write_to_mem m (wa a) nb) lo Sp0) by (apply stk_write; [exact STK | lia | lia]).
  refine (conj _ (conj _ (conj _ _))).
  - eapply mf_ctx_transport; eassumption.
  - eapply mf_text_transport; [exact HX | exact MU |]. intros x Hx. cbn [outside] in *.
    destruct Hx as (X1 & _ & _). split; [lia | exact I].
  - eapply mconf_atp_transport; [exact HM | exact MU |]. cbn [disjoint_from]. unfold SEG_M_SIZE. split; [lia | exact I].
  - eapply cell8_transport; [exact HQ | exact MU |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** A store into c. *)
Lemma kr_inv_wc : forall m fc mcx mcx' a nb, kr_inv m fc mcx -> c <= a -> a + Z.of_nat (length nb) <= c + SEG_M_SIZE ->
  store_ok rsegs m (wa a) (length nb) = true ->
  (forall bs, mconf_encp false mcx bs -> mconf_encp false mcx' (upd_bytes bs (Z.to_nat (a - c)) nb)) ->
  kr_inv (write_to_mem m (wa a) nb) fc mcx'.
Proof.
  intros m fc mcx mcx' a nb (HC & HX & HM & HQ) H1 H2 HS ENC.
  pose proof (kr_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _ & _ & (STK & _) & MI).
  unfold SEG_M_SIZE in H2.
  assert (MU : munch [(a, a + Z.of_nat (length nb))] m (write_to_mem m (wa a) nb)).
  { apply munch_write; [apply munch_refl | lia | lia | cbn [inside]; left; lia]. }
  assert (WM : wmono rsegs m (write_to_mem m (wa a) nb)) by (apply wmono_write; apply wmono_refl).
  assert (MI' : mem_inv rsegs (write_to_mem m (wa a) nb)) by (apply mem_inv_store; assumption).
  assert (SF3 : sub_fp [(a, a + Z.of_nat (length nb))] [(lo, Sp); (Sp + 0x20, Sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. cbn [outside] in *. unfold SEG_M_SIZE in Hx. destruct Hx as (X1 & X2 & X3 & _). split; [lia | exact I]. }
  assert (TM : MemNorm.task_mem rsegs (write_to_mem m (wa a) nb)) by (eapply mf_task_mem; eassumption).
  assert (STK' : stk rsegs (write_to_mem m (wa a) nb) lo Sp0) by (apply stk_write; [exact STK | lia | lia]).
  refine (conj _ (conj _ (conj _ _))).
  - eapply mf_ctx_transport; eassumption.
  - eapply mf_text_transport; [exact HX | exact MU |]. intros x Hx. cbn [outside] in *. unfold SEG_M_SIZE in Hx.
    destruct Hx as (X1 & X2 & _). split; [lia | exact I].
  - eapply mconf_atp_store; [exact HM | lia | unfold SEG_M_SIZE; lia | exact ENC].
  - eapply cell8_transport; [exact HQ | exact MU |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** snprintf(D, 96, "%s", reading) with D inside c and its stack [lo', sp). *)
Lemma kr_inv_snp : forall m m' fc fc' mcx mcx' lo' D L nb,
  kr_inv m fc mcx -> lo <= lo' -> lo' <= Sp -> c <= D -> D + L <= c + SEG_M_SIZE -> Z.of_nat (length nb) = L ->
  munch [(lo', Sp); (D, D + L)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  frm0 fc' -> stk rsegs m' lo' Sp -> bytes_at rsegs m' D nb ->
  (forall bs, mconf_encp false mcx bs -> mconf_encp false mcx' (upd_bytes bs (Z.to_nat (D - c)) nb)) ->
  kr_inv m' fc' mcx'.
Proof.
  intros m m' fc fc' mcx mcx' lo' D L nb (HC & HX & HM & HQ) L1 L2 D1 D2 EL MU WM MI TM FR ST BA ENC.
  pose proof (kr_ctx_facts m fc HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & _) & _).
  unfold SEG_M_SIZE in D2.
  assert (Lnn : 0 <= L) by lia.
  assert (ST0 : stk rsegs m' lo Sp).
  { destruct (stk_split rsegs m lo lo' Sp0 STK ltac:(lia)) as [S1 _].
    eapply stk_merge; [| exact ST | lia]. eapply stk_transport_disjoint; [exact S1 | exact MU | exact WM |].
    cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (STK' : stk rsegs m' lo Sp0).
  { eapply mf_stk_after; [exact STK | exact MU | exact WM | exact ST0 | lia |].
    cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (SF3 : sub_fp [(lo', Sp); (D, D + L)] [(lo, Sp); (Sp + 0x20, Sp + 0x68); (c, c + SEG_M_SIZE)]).
  { intros x Hx. cbn [outside] in *. unfold SEG_M_SIZE in Hx. destruct Hx as (X1 & X2 & X3 & _).
    split; [lia|]. split; [lia | exact I]. }
  refine (conj _ (conj _ (conj _ _))).
  - eapply mf_ctx_transport; eassumption.
  - eapply mf_text_transport; [exact HX | exact MU |]. intros x Hx. cbn [outside] in *. unfold SEG_M_SIZE in Hx.
    destruct Hx as (X1 & X2 & _). split; [lia|]. split; [lia | exact I].
  - eapply mconf_atp_upd; [exact HM | exact MU | | exact BA | lia | unfold SEG_M_SIZE; lia | exact ENC].
    intros x Hx Hn'. unfold SEG_M_SIZE in Hx. rewrite EL.
    destruct (Z.le_gt_cases D x); destruct (Z.lt_ge_cases x (D + L)); try (split; assumption);
      exfalso; apply Hn'; cbn [outside]; repeat split; try exact I; lia.
  - eapply cell8_transport; [exact HQ | exact MU |]. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

(** The step facts of a byte store into low. *)
Lemma kr_wbuf_step : forall mk buf (i : nat) (b : byte),
  kr_inv mk fc0 mc -> munch Wst m0 mk -> wmono rsegs m0 mk -> u8arr rsegs mk (Sp + 40) buf -> length buf = 64%nat ->
  (i < 64)%nat ->
  kr_inv (write_to_mem mk (Z_to_bv 64 (Sp + 40 + Z.of_nat i)) [b]) fc0 mc /\
  munch Wst m0 (write_to_mem mk (Z_to_bv 64 (Sp + 40 + Z.of_nat i)) [b]) /\
  wmono rsegs m0 (write_to_mem mk (Z_to_bv 64 (Sp + 40 + Z.of_nat i)) [b]) /\
  u8arr rsegs (write_to_mem mk (Z_to_bv 64 (Sp + 40 + Z.of_nat i)) [b]) (Sp + 40) (upd buf i b).
Proof.
  intros mk buf i b INV MU WM U BL Hi. pose proof INV as (HC & _).
  pose proof (kr_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  assert (HS : store_ok rsegs mk (wa (Sp + 40 + Z.of_nat i)) 1 = true)
    by (eapply (u8arr_store_ok rsegs mk (Sp + 40) buf (Z.of_nat i)); [exact U | rewrite BL; lia | reflexivity]).
  change (Z_to_bv 64 (Sp + 40 + Z.of_nat i)) with (wa (Sp + 40 + Z.of_nat i)).
  refine (conj _ (conj _ (conj _ _))).
  - apply kr_inv_wbuf; [exact INV | lia | cbn [length]; lia | exact HS].
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; left; unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia].
  - apply wmono_write. exact WM.
  - pose proof (u8arr_write rsegs mk (Sp + 40) buf (Z.of_nat i) b U ltac:(rewrite BL; lia)) as U'.
    rewrite Nat2Z.id in U'. exact U'.
Qed.

(** The step facts of a store into c. *)
Lemma kr_wc_step : forall m W mcx mcx' a nb,
  kr_inv m fc0 mcx -> munch W m0 m -> wmono rsegs m0 m -> inside W a (Z.of_nat (length nb)) ->
  c <= a -> a + Z.of_nat (length nb) <= c + SEG_M_SIZE -> store_ok rsegs m (wa a) (length nb) = true ->
  (forall bs, mconf_encp false mcx bs -> mconf_encp false mcx' (upd_bytes bs (Z.to_nat (a - c)) nb)) ->
  kr_inv (write_to_mem m (Z_to_bv 64 a) nb) fc0 mcx' /\ munch W m0 (write_to_mem m (Z_to_bv 64 a) nb) /\
  wmono rsegs m0 (write_to_mem m (Z_to_bv 64 a) nb).
Proof.
  intros m W mcx mcx' a nb INV MU WM IN H1 H2 HS ENC. pose proof INV as (HC & _).
  pose proof (kr_ctx_facts m fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  unfold SEG_M_SIZE in H2.
  change (Z_to_bv 64 a) with (wa a).
  refine (conj _ (conj _ _)).
  - eapply kr_inv_wc; [exact INV | lia | unfold SEG_M_SIZE; lia | exact HS | exact ENC].
  - apply munch_write; [exact MU | lia | lia | exact IN].
  - apply wmono_write. exact WM.
Qed.

(** The encoding of an edit of entry gi at offset off. *)
Lemma kr_enc_upd : forall mcx (f : mseg -> mseg) off nb, 0 <= off ->
  (gi < length (mc_seg mcx))%nat -> (Z.to_nat off + length nb <= 256)%nat ->
  (forall fb, mseg_enc (nth gi (mc_seg mcx) mseg_d) fb ->
              mseg_enc (f (nth gi (mc_seg mcx) mseg_d)) (upd_bytes fb (Z.to_nat off) nb)) ->
  forall bs, mconf_encp false mcx bs ->
    mconf_encp false (m_upd mcx gi f) (upd_bytes bs (Z.to_nat (mseg_addr c gi + off - c)) nb).
Proof.
  intros mcx f off nb H0 Hg Hk Hf bs E.
  replace (Z.to_nat (mseg_addr c gi + off - c)) with (256 * gi + Z.to_nat off)%nat by (unfold mseg_addr, MSEG_SIZE; lia).
  apply mconf_enc_seg; assumption.
Qed.

(** ** The tail 0x143d4: H_MF_TAIL for the next line, and the post moved back to m0. *)
Lemma kr_tail : forall mt Ft fct mcx W (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 w7 w8 t3 t4 t5 t6 : word),
  w7 = Z_to_bv 64 9 -> w8 = Z_to_bv 64 0x1ff ->
  kr_inv mt fct mcx -> munch W m0 mt -> wmono rsegs m0 mt -> sub_fp W (M_FILE_W Sp0 c k0 mcx) ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get Ft r = reg_get F0 r) ->
  (gi < length (mc_seg mcx))%nat -> (k0 <= length (mc_kept mcx))%nat ->
  mc_refused mcx <= mc_refused mc + 1 -> mc_overflow mcx <= mc_overflow mc + 1 ->
  evt rsegs (QP (mf_fin (mcx, Some gi) line rest))
    (KS 0x143d4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 w7 w8 t3 t4 t5 t6 Ft fct mt).
Proof.
  intros mt Ft fct mcx W ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 w7 w8 t3 t4 t5 t6 E7 E8 (HC & HX & HM & HQ)
    MU WM SF FF Hg Hk Hr Ho. subst w7 w8.
  destruct kr_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  eapply mf_post_back; [exact FF | exact MU | exact WM | |].
  { eapply sub_fp_trans; [exact SF | apply mf_W_fin; exact Hg]. }
  unfold mf_post, mf_fin. pose proof HT as HT'. unfold H_MF_TAIL in HT'.
  eapply HT' with (rest := mf_rest rest) (p := mf_next p rest) (line := line + 1) (mc := mcx) (cur := Some gi) (k0 := k0).
  - pose proof (mf_rest_lt rest Hne). lia.
  - eapply mf_tail_loop; [exact HC | exact HX | exact Hne | exact HM | exact HQ | exact Hg | exact Hk | lia | lia | |].
    + eapply mf_cnt_next; [exact Hne | exact S5 | lia].
    + eapply mf_cnt_next; [exact Hne | exact S6 | lia].
  - unfold m_file_regs. repeat split; reflexivity.
Qed.

(** ** KMODEL 0x144d4: ieq said no; the premise H_MF_KMODEL. *)
Lemma kr_kmodel : forall m1 (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  ieq k S_role = false -> kr_inv m1 fc0 mc -> munch Wst m0 m1 -> wmono rsegs m0 m1 ->
  evt rsegs (QP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (KS 0x144d4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 (p + Z.of_nat ok))
        (Z_to_bv 64 (p + Z.of_nat (ov + vl))) (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl)) t3 t4 t5 t6 F0 fc0 m1).
Proof.
  intros m1 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EQ (HC & HX & HM & HQ) MU WM.
  destruct kr_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  eapply mf_post_back; [intros r _; reflexivity | exact MU | exact WM | apply mf_W_frame; lia |].
  pose proof HKM as HK. unfold H_MF_KMODEL, H_MF_KAT in HK.
  eapply HK; [exact Hn | exact Hne | | | exact HKV | constructor; [exact EQ | constructor]].
  - apply mf_loop_iff. refine (conj HC (conj HX _)). unfold mf_st. refine (conj HM (conj HQ _)).
    cbn [cur_ok]. repeat split; lia.
  - unfold mk_regs. repeat split; reflexivity.
Qed.

(** ** The refusal 0x143a0: m_refuse(c, line + 1), then the tail. *)
Lemma kr_refuse : forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word),
  kr_inv mk fc0 mc -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (kr_res None, Some gi) line rest))
    (KS 0x143a0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 t3 t4 t5 t6 INV MU WM.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (kr_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct kr_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  change (kr_res None) with (m_refuse mc (line + 1) false).
  step. step. step.
  eapply (mf_refuse_call HMR 0x143a8) with (lo := lo) (sp0 := Sp0) (p := p) (rest := rest) (w := mseg_addr c gi)
    (mc := mc) (knock := false) (ra0 := ra0) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
    (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11).
  - lia.
  - lia.
  - reflexivity.
  - exact HC.
  - exact HX.
  - exact HQ.
  - exact HM.
  - lia.
  - lia.
  - intros m' F' fc' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HC' HX' HQ' HM' MU' WM' FF'.
    replace (Z_to_bv 64 (0x143a8 + 4)) with (Z_to_bv 64 0x143ac) by reflexivity.
    step. step. step. step.
    destruct (m_refuse_sizes mc (line + 1) false) as (Eseg & Ekept).
    eapply kr_tail with (mcx := m_refuse mc (line + 1) false) (W := Wst ++ m_refuse_W Sp c mc).
    + reflexivity.
    + reflexivity.
    + exact (conj HC' (conj HX' (conj HM' HQ'))).
    + eapply munch_trans.
      * eapply munch_weaken; [apply kr_sub_l | exact MU].
      * eapply munch_weaken; [apply kr_sub_r | exact MU'].
    + eapply wmono_trans; eassumption.
    + apply sub_fp_app; [apply mf_W_frame; lia |].
      apply mf_W_refuse; [unfold M_FILE_STACK, M_FILE_FRAME, M_REFUSE_STACK, PRINTF_K; lia | lia | exact S2].
    + exact FF'.
    + rewrite Eseg. exact S1.
    + lia.
    + unfold m_refuse. cbn [mc_refused]. lia.
    + unfold m_refuse. cbn [mc_overflow]. lia.
Qed.

(** ** The hit 0x14568: role = role[i], role_set = 1, snprintf of role_file, then the tail. *)
Lemma kr_hit : forall (i : nat) mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 w6 s8 t3 t4 t5 t6 : word),
  (i < 5)%nat -> w6 = Z_to_bv 64 (M_KEY_ROLE + 4 * Z.of_nat i) ->
  kr_inv mk fc0 mc -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  evt rsegs (QP (mf_fin (kr_res (Some (Z.of_nat i)), Some gi) line rest))
    (KS 0x14568 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 w6 (Z_to_bv 64 (Z.of_nat kr_n)) s8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros i mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 w6 s8 t3 t4 t5 t6 Hi E6 INV MU WM. subst w6.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (kr_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct kr_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  destruct kr_mc_facts as (R1 & R2 & R3).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HNI & HWR & _ & _ & _ & _ & _ & _ & MI).
  pose proof (kr_role_rd mk i MI Hi) as RR.
  pose proof (kr_rd_bytes _ _ _ HQ) as RC. rewrite length_le8 in RC.
  assert (MUh : munch Whit m0 mk).
  { eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _ & _). split; [exact X1 | exact I]. }
  assert (HS1 : store_ok rsegs mk (wa (mseg_addr c gi + 20)) 4 = true).
  { replace (mseg_addr c gi + 20) with (c + (256 * Z.of_nat gi + 20)) by (unfold mseg_addr, MSEG_SIZE; lia).
    apply (wr_at_store_ok rsegs mk c SEG_M_SIZE (256 * Z.of_nat gi + 20) 4 HWR); unfold SEG_M_SIZE; lia. }
  step. rewrite (kr_sx32_small (Z.of_nat i)) by lia.
  step. step. step.
  pose proof (kr_wc_step mk Whit mc (m_upd mc gi (ms_set_role_set true)) (mseg_addr c gi + 20) (le4 (Z_to_bv 64 1))
     INV MUh WM ltac:(rewrite length_le4; cbn [inside]; right; left; nlia) ltac:(nlia) ltac:(rewrite length_le4; nlia)
     ltac:(rewrite length_le4; exact HS1)
     (kr_enc_upd mc (ms_set_role_set true) 20 (le4 (Z_to_bv 64 1)) ltac:(lia) S1 ltac:(rewrite length_le4; lia)
        (fun fb Ef => mseg_enc_role_set _ fb true Ef))) as (INV1 & MU1 & WM1).
  set (mk1 := write_to_mem mk (Z_to_bv 64 (mseg_addr c gi + 20)) (le4 (Z_to_bv 64 1))) in *. clearbody mk1.
  clear HQ HM HC HX RC HS1.
  set (mc1 := m_upd mc gi (ms_set_role_set true)) in *.
  assert (G1 : (gi < length (mc_seg mc1))%nat) by (unfold mc1; rewrite kr_m_upd_len; exact S1).
  pose proof INV1 as (HC1 & _ & _ & _).
  pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & HWR1 & _).
  assert (HS2 : store_ok rsegs mk1 (wa (mseg_addr c gi + 16)) 4 = true).
  { replace (mseg_addr c gi + 16) with (c + (256 * Z.of_nat gi + 16)) by (unfold mseg_addr, MSEG_SIZE; lia).
    apply (wr_at_store_ok rsegs mk1 c SEG_M_SIZE (256 * Z.of_nat gi + 16) 4 HWR1); unfold SEG_M_SIZE; lia. }
  step.
  pose proof (kr_wc_step mk1 Whit mc1 (m_upd mc1 gi (ms_set_role (Z.of_nat i))) (mseg_addr c gi + 16)
     (le4 (Z_to_bv 64 (Z.of_nat i)))
     INV1 MU1 WM1 ltac:(rewrite length_le4; cbn [inside]; right; left; nlia) ltac:(nlia) ltac:(rewrite length_le4; nlia)
     ltac:(rewrite length_le4; exact HS2)
     (kr_enc_upd mc1 (ms_set_role (Z.of_nat i)) 16 (le4 (Z_to_bv 64 (Z.of_nat i))) ltac:(lia) G1
        ltac:(rewrite length_le4; lia) (fun fb Ef => mseg_enc_role _ fb (Z.of_nat i) Ef ltac:(lia)))) as (INV2 & MU2 & WM2).
  set (mk2 := write_to_mem mk1 (Z_to_bv 64 (mseg_addr c gi + 16)) (le4 (Z_to_bv 64 (Z.of_nat i)))) in *. clearbody mk2.
  clear INV1 MU1 WM1 HC1 HWR1 HS2.
  set (mc2 := m_upd mc1 gi (ms_set_role (Z.of_nat i))) in *.
  assert (G2 : (gi < length (mc_seg mc2))%nat) by (unfold mc2; rewrite kr_m_upd_len; exact G1).
  pose proof INV2 as (HC2 & HX2 & HM2 & HQ2).
  pose proof HC2 as (_ & _ & _ & _ & HR8 & _ & _ & _ & HWR2 & HSL2 & _ & HPE2 & _ & _ & _ & MI2).
  pose proof (kr_rd_bytes _ _ _ HR8) as RR8. rewrite length_le8 in RR8.
  step. step. step. step. step. step.
  destruct (mconf_field_cells rsegs false mk2 c mc2 (256 * Z.of_nat gi + 60) HM2 HWR2 ltac:(lia) ltac:(nlia))
    as [junk HJ].
  pose proof (mconf_reading_cstr rsegs false mk2 c mc2 HM2 HSL2 (kr_mod8 c F8)) as CR.
  change (mc_reading mc2) with (mc_reading mc) in CR.
  pose proof (kr_span_rd c (mc_reading mc) F8 R1) as (SP1 & SP2).
  eapply evt_cut.
  { eapply (mf_snprintf_s HSN) with (lo := Sp - PRINTF_K) (s := mc_reading mc) (junk := junk);
      rewrite ?unsigned_lit by nlia.
    - reflexivity.
    - reflexivity.
    - nlia.
    - exact CR.
    - lia.
    - nlia.
    - nlia.
    - replace (mseg_addr c gi + 60) with (c + (256 * Z.of_nat gi + 60)) by (unfold mseg_addr, MSEG_SIZE; lia). exact HJ.
    - nlia.
    - nlia.
    - apply (kr_noimg_sub c SEG_M_SIZE); [exact HNI | nlia | nlia].
    - eapply kr_penv; [exact HPE2 | unfold PRINTF_K; lia | lia].
    - exact (kr_stack_pf mk2 fc0 mc2 INV2).
    - exact MI2. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & Fq & fc3 & m3 & -> &
              MU3 & WM3 & MI3 & TM3 & FR3 & FF3 & ST3 & BA3).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (kr_firstn_all (mc_reading mc) 95) in MU3, BA3 by lia.
  assert (PB : pf_bytes (mc_reading mc ++ [0]) = zb (mc_reading mc) ++ [ZERO])
    by (unfold pf_bytes, zb; rewrite map_app; reflexivity).
  rewrite PB in BA3.
  rewrite (unsigned_lit (mseg_addr c gi + 60)) in MU3, BA3 by nlia.
  replace (mseg_addr c gi + 60 + Z.of_nat (length (mc_reading mc)) + 1)
    with (mseg_addr c gi + 60 + (Z.of_nat (length (mc_reading mc)) + 1)) in MU3 by lia.
  set (mc3 := m_upd mc2 gi (ms_set_role_file (mc_reading mc))).
  assert (G3 : (gi < length (mc_seg mc3))%nat) by (unfold mc3; rewrite kr_m_upd_len; exact G2).
  pose proof (kr_inv_snp mk2 m3 fc0 fc3 mc2 mc3 (Sp - PRINTF_K) (mseg_addr c gi + 60) (Z.of_nat (length (mc_reading mc)) + 1)
     (zb (mc_reading mc) ++ [ZERO]) INV2 ltac:(unfold PRINTF_K; lia) ltac:(unfold PRINTF_K; lia) ltac:(nlia) ltac:(nlia)
     ltac:(rewrite length_app, kr_length_zb; cbn [length]; lia) MU3 WM3 MI3 TM3 FR3 ST3 BA3
     (kr_enc_upd mc2 (ms_set_role_file (mc_reading mc)) 60 (zb (mc_reading mc) ++ [ZERO]) ltac:(lia) G2
        ltac:(rewrite length_app, kr_length_zb; cbn [length]; lia)
        (fun fb Ef => mseg_enc_role_file _ fb (mc_reading mc) Ef R1 R2 R3))) as INV3.
  assert (MU3' : munch Whit m0 m3).
  { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside] in *.
    unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K, mseg_addr, MSEG_SIZE in *. destruct Hx as (X1 & X2 & _).
    split; [lia|]. split; [lia | exact I]. }
  assert (WM3' : wmono rsegs m0 m3) by (eapply wmono_trans; eassumption).
  assert (EQM : kr_res (Some (Z.of_nat i)) = mc3).
  { unfold kr_res, mc3, mc2, mc1. rewrite (mf_snprintf_s_model _ R2 R1). rewrite !kr_m_upd_comp.
    apply kr_m_upd_ext. intros x. apply ms_with_role_eq. }
  rewrite EQM.
  step. step. step.
  eapply kr_tail with (mcx := mc3) (W := Whit).
  - reflexivity.
  - reflexivity.
  - exact INV3.
  - exact MU3'.
  - exact WM3'.
  - change Whit with ([(Sp0 - M_FILE_STACK, Sp0)] ++ [(mseg_addr c gi, mseg_addr c gi + 256)]).
    apply sub_fp_app; [apply mf_W_frame; lia |].
    pose proof (mf_W_seg Sp0 c k0 mc3 gi 0 256 G3 ltac:(lia) ltac:(unfold MSEG_SIZE; lia)) as H.
    rewrite !Z.add_0_r in H. exact H.
  - exact FF3.
  - exact G3.
  - exact S2.
  - unfold mc3, mc2, mc1, m_upd, m_set_segs. cbn [mc_refused]. lia.
  - unfold mc3, mc2, mc1, m_upd, m_set_segs. cbn [mc_overflow]. lia.
Qed.

(** ** The words loop 0x1436c: word i (j words left after it). *)
Lemma kr_wg_miss : forall i, (i < 5)%nat -> kr_word i <> kr_low ->
  word_go (skipn i KR_WORDS) kr_low (Z.of_nat i) = word_go (skipn (S i) KR_WORDS) kr_low (Z.of_nat (S i)).
Proof.
  intros i Hi Hne'. rewrite (kr_skipn_words i Hi). cbn [word_go].
  destruct ((length (kr_word i) =? length kr_low)%nat && leqb (firstn (length kr_low) (kr_word i)) kr_low) eqn:E.
  - exfalso. apply andb_true_iff in E as [E1 E2]. apply Nat.eqb_eq in E1. apply leqb_eq in E2.
    rewrite <- E1, firstn_all in E2. exact (Hne' E2).
  - f_equal. lia.
Qed.

Lemma kr_wg_hit : forall i, (i < 5)%nat -> kr_word i = kr_low ->
  word_go (skipn i KR_WORDS) kr_low (Z.of_nat i) = Some (Z.of_nat i).
Proof.
  intros i Hi E. rewrite (kr_skipn_words i Hi). cbn [word_go]. rewrite <- E, Nat.eqb_refl, firstn_all.
  replace (leqb (kr_word i) (kr_word i)) with true by (symmetry; apply leqb_eq; reflexivity). reflexivity.
Qed.

Definition kr_head (j i : nat) : Prop :=
  forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w4 s5 w6 w8 t3 t4 t5 t6 : word),
  w4 = Z_to_bv 64 (Z.of_nat (S j)) -> w6 = Z_to_bv 64 (M_KEY_ROLE + 4 * Z.of_nat i) ->
  w8 = Z_to_bv 64 (M_KEY_WORDS + 8 * Z.of_nat i) ->
  h_role_word kr_low = word_go (skipn i KR_WORDS) kr_low (Z.of_nat i) ->
  kr_inv mk fc0 mc -> munch Wst m0 mk -> wmono rsegs m0 mk -> bytes_at rsegs mk (Sp + 40) (zb kr_low) ->
  evt rsegs QR
    (KS 0x1436c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w4 s5 w6 (Z_to_bv 64 (Z.of_nat kr_n)) w8 t3 t4 t5 t6 F0 fc0 mk).

(** 0x14390, after word i missed: the next word, or the refusal after the fifth. *)
Lemma kr_next : forall j i, (i + S j = 5)%nat -> (forall j', j = S j' -> kr_head j' (S i)) ->
  forall mk (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w4 s5 w6 w8 t3 t4 t5 t6 : word),
  w4 = Z_to_bv 64 (Z.of_nat (S j)) -> w6 = Z_to_bv 64 (M_KEY_ROLE + 4 * Z.of_nat i) ->
  w8 = Z_to_bv 64 (M_KEY_WORDS + 8 * Z.of_nat i) ->
  h_role_word kr_low = word_go (skipn (S i) KR_WORDS) kr_low (Z.of_nat (S i)) ->
  kr_inv mk fc0 mc -> munch Wst m0 mk -> wmono rsegs m0 mk -> bytes_at rsegs mk (Sp + 40) (zb kr_low) ->
  evt rsegs QR
    (KS 0x14390 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w4 s5 w6 (Z_to_bv 64 (Z.of_nat kr_n)) w8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros j i Hij IH mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w4 s5 w6 w8 t3 t4 t5 t6 E4 E6 E8 HW INV MU WM BA.
  subst w4 w6 w8.
  step. step. step. step.
  if_cases K; cbv iota; zify_cond K.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1436c) _ _ _ _) =>
      destruct j as [|j']; [exfalso; lia|];
      pose proof (IH j' eq_refl) as IH'; unfold kr_head in IH';
      eapply IH'; [f_equal; lia | f_equal; lia | f_equal; lia | exact HW | exact INV | exact MU | exact WM | exact BA]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x143a0) _ _ _ _) =>
      destruct j as [|j']; [|exfalso; lia];
      assert (HN : h_role_word kr_low = None) by (rewrite HW; replace (S i) with 5%nat by lia; reflexivity);
      rewrite HN; eapply kr_refuse; [exact INV | exact MU | exact WM]
  end.
Qed.

Lemma kr_iter : forall j i, (i + S j = 5)%nat -> (forall j', j = S j' -> kr_head j' (S i)) -> kr_head j i.
Proof.
  intros j i Hij IH. unfold kr_head.
  intros mk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w4 s5 w6 w8 t3 t4 t5 t6 E4 E6 E8 HW INV MU WM BA. subst w4 w6 w8.
  assert (Hi : (i < 5)%nat) by lia.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (kr_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct kr_low_facts as (L1 & L2 & L3).
  pose proof (kr_word_facts i Hi) as (WF1 & WF2 & WF3 & WF4 & WF5).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWI & _ & MI).
  pose proof (kr_words_rd mk i HWI Hi) as RW.
  step. step. step.
  eapply evt_cut.
  { eapply HSL with (str := zb (kr_word i)) (slack := kr_sl i).
    - rewrite unsigned_lit by lia. exact (kr_word_at mk i MI Hi).
    - exact WF1.
    - rewrite unsigned_lit by lia. exact WF2.
    - exact MI. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & -> & MU2 & WM2 & MI2 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite kr_length_zb.
  pose proof (kr_inv_nil mk m2 fc0 mc INV MU2 WM2 MI2) as INV2.
  assert (MUa : munch Wst m0 m2) by (eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU2]; intros x _; exact I]).
  assert (WMa : wmono rsegs m0 m2) by (eapply wmono_trans; eassumption).
  assert (BA2 : bytes_at rsegs m2 (Sp + 40) (zb kr_low)) by (eapply bytes_at_transport; [exact BA | exact MU2 | exact I]).
  clear INV MU WM BA HC HX HM HQ HWI MI RW.
  step.
  if_cases K; cbv iota; zify_cond K.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14390) _ _ _ _) =>
      eapply kr_next; [exact Hij | exact IH | reflexivity | reflexivity | reflexivity | | exact INV2 | exact MUa
                      | exact WMa | exact BA2];
      rewrite HW; apply kr_wg_miss; [exact Hi | intros EW; rewrite EW, L1 in K; lia]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1437c) _ _ _ _) =>
      assert (Leq : length (kr_word i) = kr_n) by lia;
      step; step; step; step;
      destruct (StrFun.memcmp_model_total (zb (kr_word i)) (zb kr_low) kr_n
                  ltac:(rewrite kr_length_zb; lia) ltac:(rewrite kr_length_zb; lia)) as [vv Hvv];
      pose proof (kr_memcmp kr_n (zb (kr_word i)) (zb kr_low) vv ltac:(rewrite kr_length_zb; lia)
                    ltac:(rewrite kr_length_zb; lia) Hvv)
        as (VR & VE);
      pose proof (kr_word_at m2 i MI2 Hi) as WA; apply bytes_at_app in WA; destruct WA as [WA _];
      eapply evt_cut;
      [ eapply HBC with (ls := zb (kr_word i)) (rs := zb kr_low) (v := vv);
        [ rewrite unsigned_lit by lia; exact WA
        | rewrite unsigned_lit by lia; exact BA2
        | rewrite unsigned_lit by lia; rewrite Nat2Z.id; exact Hvv
        | exact MI2 ] |];
      intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MU3 & WM3 &
                  MI3 & _);
      rewrite ret_pc_even by (try lia; reflexivity);
      pose proof (kr_inv_nil m2 m3 fc0 mc INV2 MU3 WM3 MI3) as INV3;
      assert (MUb : munch Wst m0 m3)
        by (eapply munch_trans; [exact MUa | eapply munch_weaken; [|exact MU3]; intros x _; exact I]);
      assert (WMb : wmono rsegs m0 m3) by (eapply wmono_trans; eassumption);
      assert (BA3 : bytes_at rsegs m3 (Sp + 40) (zb kr_low))
        by (eapply bytes_at_transport; [exact BA2 | exact MU3 | exact I]);
      step;
      if_cases K2; cbv iota; zify_cond K2;
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14568) _ _ _ _) =>
          assert (V0 : vv = 0) by (Z.div_mod_to_equations; lia);
          assert (EW : kr_word i = kr_low) by (apply kr_zb_inj; [exact WF3 | exact L3 | apply VE; exact V0]);
          assert (HS : h_role_word kr_low = Some (Z.of_nat i)) by (rewrite HW; apply kr_wg_hit; [exact Hi | exact EW]);
          rewrite HS; eapply kr_hit; [exact Hi | reflexivity | exact INV3 | exact MUb | exact WMb]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14390) _ _ _ _) =>
          assert (V0 : vv <> 0) by (Z.div_mod_to_equations; lia);
          eapply kr_next; [exact Hij | exact IH | reflexivity | reflexivity | reflexivity | | exact INV3 | exact MUb
                          | exact WMb | exact BA3];
          rewrite HW; apply kr_wg_miss; [exact Hi | intros EW; apply V0; apply VE; rewrite EW; reflexivity]
      end
  end.
Qed.

Lemma kr_words : forall j i, (i + S j = 5)%nat -> kr_head j i.
Proof.
  induction j as [|j IH]; intros i Hij; apply kr_iter; [exact Hij | intros j' E; discriminate E | exact Hij |].
  intros j' E. injection E as <-. apply IH. lia.
Qed.


Lemma kr_fold_iter : forall i mk buf (ra t0 t1 t2 w10 w11 a2 a3 a4 a5 a6 a7 w20 s5 s8 t3 t4 t5 t6 : word),
  (i < kr_n)%nat -> w10 = Z_to_bv 64 (Sp + 40 + Z.of_nat i) -> w20 = Z_to_bv 64 (p + Z.of_nat (ov + i)) ->
  kr_inv mk fc0 mc -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  u8arr rsegs mk (Sp + 40) buf -> length buf = 64%nat -> firstn i buf = zb (firstn i kr_low) ->
  (forall mk' buf' (x10 x12 x13 x20 : word),
     x10 = Z_to_bv 64 (Sp + 40 + Z.of_nat (S i)) -> x20 = Z_to_bv 64 (p + Z.of_nat (ov + S i)) ->
     kr_inv mk' fc0 mc -> munch Wst m0 mk' -> wmono rsegs m0 mk' ->
     u8arr rsegs mk' (Sp + 40) buf' -> length buf' = 64%nat -> firstn (S i) buf' = zb (firstn (S i) kr_low) ->
     evt rsegs QR
       (KS 0x14348 ra t0 t1 t2 x10 w11 x12 x13 a4 a5 a6 a7 x20 s5 (Z_to_bv 64 (p + Z.of_nat (ov + vl)))
           (Z_to_bv 64 (Z.of_nat kr_n)) s8 t3 t4 t5 t6 F0 fc0 mk')) ->
  evt rsegs QR
    (KS 0x14328 ra t0 t1 t2 w10 w11 a2 a3 a4 a5 a6 a7 w20 s5 (Z_to_bv 64 (p + Z.of_nat (ov + vl)))
        (Z_to_bv 64 (Z.of_nat kr_n)) s8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros i mk buf ra t0 t1 t2 w10 w11 a2 a3 a4 a5 a6 a7 w20 s5 s8 t3 t4 t5 t6 Hi E10 E20 INV MU WM U BL FB K.
  subst w10 w20.
  pose proof INV as (HC & HX & HM & HQ).
  pose proof (kr_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (kr_text_facts mk HX) as (T1 & T2 & T3 & T4 & T5).
  destruct kr_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  destruct kr_low_facts as (L1 & L2 & L3).
  assert (Hb : 0 <= nth (ov + i) rest 0 < 256) by (apply kr_nth_byte; exact T2).
  pose proof (mf_text_byte mk Sp0 lo c p rest (ov + i) HX ltac:(lia)) as RD.
  pose proof (kr_nth_low i Hi) as NL.
  assert (HS : store_ok rsegs mk (wa (Sp + 40 + Z.of_nat i)) 1 = true)
    by (eapply (u8arr_store_ok rsegs mk (Sp + 40) buf (Z.of_nat i)); [exact U | rewrite BL; lia | reflexivity]).
  step. rewrite (kr_zxb (nth (ov + i) rest 0) Hb).
  step. step. step. step.
  step.
  rewrite (kr_lower_le1 (nth (ov + i) rest 0) Hb).
  destruct (kr_wbuf_step mk buf i (Z_to_bv 8 (lower (nth (ov + i) rest 0))) INV MU WM U BL ltac:(lia))
    as (INV' & MU' & WM' & U').
  set (mk' := write_to_mem mk (Z_to_bv 64 (Sp + 40 + Z.of_nat i)) [Z_to_bv 8 (lower (nth (ov + i) rest 0))]) in *.
  clearbody mk'.
  step. step.
  eapply K; [f_equal; lia | f_equal; lia | exact INV' | exact MU' | exact WM' | exact U' | rewrite upd_length; exact BL |].
  rewrite kr_firstn_upd by lia. rewrite FB. rewrite (kr_firstn_S kr_low i) by lia.
  unfold zb at 2. rewrite map_app. rewrite NL. reflexivity.
Qed.

(** 0x1434c, after the fold: the NUL at low + s7, then s4 = 5, s6 = m_key.role, s8 = m_key.words. *)
Lemma kr_after_fold : forall mk buf (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 t3 t4 t5 t6 : word),
  kr_inv mk fc0 mc -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  u8arr rsegs mk (Sp + 40) buf -> length buf = 64%nat -> firstn kr_n buf = zb kr_low ->
  evt rsegs QR (KS 0x1434c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 (Z_to_bv 64 (Z.of_nat kr_n)) s8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  intros mk buf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 t3 t4 t5 t6 INV MU WM U BL FB.
  pose proof INV as (HC & _).
  pose proof (kr_ctx_facts mk fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct kr_low_facts as (L1 & L2 & L3).
  assert (BA : bytes_at rsegs mk (Sp + 40) (zb kr_low)).
  { destruct U as [UB _]. rewrite <- (firstn_skipn kr_n buf) in UB. apply bytes_at_app in UB as [UB _].
    rewrite FB in UB. exact UB. }
  assert (HS : store_ok rsegs mk (wa (Sp + 40 + Z.of_nat kr_n)) 1 = true)
    by (eapply (u8arr_store_ok rsegs mk (Sp + 40) buf (Z.of_nat kr_n)); [exact U | rewrite BL; lia | reflexivity]).
  step. step. step. step. step.
  lazymatch goal with
  | |- context [write_to_mem mk ?aa (le1 ?x)] =>
      replace (le1 x) with [Z_to_bv 8 0] by (symmetry; apply kr_le1; vm_compute; reflexivity)
  end.
  destruct (kr_wbuf_step mk buf kr_n (Z_to_bv 8 0) INV MU WM U BL ltac:(lia)) as (INV' & MU' & WM' & _).
  assert (BA' : bytes_at rsegs (write_to_mem mk (Z_to_bv 64 (Sp + 40 + Z.of_nat kr_n)) [Z_to_bv 8 0]) (Sp + 40) (zb kr_low)).
  { change (Z_to_bv 64 (Sp + 40 + Z.of_nat kr_n)) with (wa (Sp + 40 + Z.of_nat kr_n)).
    apply bytes_at_write_other; [exact BA | lia | cbn [length]; lia | rewrite kr_length_zb, L1; left; lia]. }
  set (mk' := write_to_mem mk (Z_to_bv 64 (Sp + 40 + Z.of_nat kr_n)) [Z_to_bv 8 0]) in *. clearbody mk'.
  step. step. step.
  pose proof (kr_words 4 0 eq_refl) as KW. unfold kr_head in KW.
  eapply KW; [reflexivity | reflexivity | reflexivity | reflexivity | exact INV' | exact MU' | exact WM' | exact BA'].
Qed.

Lemma kr_fold : forall j i mk buf (ra t0 t1 t2 w10 w11 a2 a3 a4 a5 a6 a7 w20 s5 s8 t3 t4 t5 t6 : word),
  (i + S j = kr_n)%nat -> w10 = Z_to_bv 64 (Sp + 40 + Z.of_nat i) -> w11 = Z_to_bv 64 (Sp + 40 + Z.of_nat kr_n) ->
  w20 = Z_to_bv 64 (p + Z.of_nat (ov + i)) ->
  kr_inv mk fc0 mc -> munch Wst m0 mk -> wmono rsegs m0 mk ->
  u8arr rsegs mk (Sp + 40) buf -> length buf = 64%nat -> firstn i buf = zb (firstn i kr_low) ->
  evt rsegs QR
    (KS 0x14328 ra t0 t1 t2 w10 w11 a2 a3 a4 a5 a6 a7 w20 s5 (Z_to_bv 64 (p + Z.of_nat (ov + vl)))
        (Z_to_bv 64 (Z.of_nat kr_n)) s8 t3 t4 t5 t6 F0 fc0 mk).
Proof.
  induction j as [|j IH]; intros i mk buf ra t0 t1 t2 w10 w11 a2 a3 a4 a5 a6 a7 w20 s5 s8 t3 t4 t5 t6 Hij E10 E11 E20
    INV MU WM U BL FB; subst w11.
  - eapply (kr_fold_iter i); [lia | exact E10 | exact E20 | exact INV | exact MU | exact WM | exact U | exact BL | exact FB |].
    intros mk' buf' x10 x12 x13 x20 E10' E20' INV' MU' WM' U' BL' FB'. subst x10 x20.
    pose proof INV' as (HC & _).
    pose proof (kr_ctx_facts mk' fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    destruct kr_low_facts as (L1 & L2 & L3).
    step. if_cases K; cbv iota; zify_cond K.
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14328) _ _ _ _) => exfalso; lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1434c) _ _ _ _) =>
        eapply kr_after_fold; [exact INV' | exact MU' | exact WM' | exact U' | exact BL' |];
        replace kr_n with (S i) by lia; rewrite FB'; f_equal; apply kr_firstn_all; lia
    end.
  - eapply (kr_fold_iter i); [lia | exact E10 | exact E20 | exact INV | exact MU | exact WM | exact U | exact BL | exact FB |].
    intros mk' buf' x10 x12 x13 x20 E10' E20' INV' MU' WM' U' BL' FB'. subst x10 x20.
    pose proof INV' as (HC & _).
    pose proof (kr_ctx_facts mk' fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    destruct kr_low_facts as (L1 & L2 & L3).
    step. if_cases K; cbv iota; zify_cond K.
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14328) _ _ _ _) =>
        eapply (IH (S i)); [lia | f_equal; lia | reflexivity | f_equal; lia | exact INV' | exact MU' | exact WM'
                           | exact U' | exact BL' | exact FB']
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1434c) _ _ _ _) => exfalso; lia
    end.
Qed.

(** 0x1431c: low = sp + 0x28 is carved from the frame; vl = 0 skips the loop. *)
Lemma kr_fold_entry : forall m1 (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w23 t3 t4 t5 t6 : word),
  w23 = Z_to_bv 64 (Z.of_nat kr_n) ->
  kr_inv m1 fc0 mc -> munch Wst m0 m1 -> wmono rsegs m0 m1 ->
  evt rsegs QR (KS 0x1431c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 (p + Z.of_nat ok))
                   (Z_to_bv 64 (p + Z.of_nat (ov + vl))) w23 (Z_to_bv 64 (Z.of_nat kl)) t3 t4 t5 t6 F0 fc0 m1).
Proof.
  intros m1 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w23 t3 t4 t5 t6 E23 INV MU WM. subst w23.
  pose proof INV as (HC & HX & _).
  pose proof (kr_ctx_facts m1 fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (kr_text_facts m1 HX) as (T1 & T2 & T3 & T4 & T5).
  destruct kr_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  destruct kr_low_facts as (L1 & L2 & L3).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (STK & _) & _).
  destruct (stk_split rsegs m1 lo (Sp + 104) Sp0 STK ltac:(lia)) as [S1 _].
  destruct (stk_carve rsegs m1 lo (Sp + 104) 64 S1 ltac:(lia)) as [_ [junk HJ]].
  replace (Sp + 104 - Z.of_nat 64) with (Sp + 40) in HJ by lia.
  pose proof HJ as [[HJwf _] _]. cbn in HJwf. destruct HJwf as [HJl _].
  pose proof (u8arr_of_rw_cells rsegs m1 (Sp + 40) 64 junk HJ) as U.
  step.
  if_cases K; cbv iota; zify_cond K.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1434c) _ _ _ _) =>
      assert (V0 : vl = 0%nat) by lia;
      assert (LN : kr_low = []) by (apply length_zero_iff_nil; lia);
      eapply kr_after_fold; [exact INV | exact MU | exact WM | exact U | exact HJl |];
      rewrite LN; replace kr_n with 0%nat by lia; reflexivity
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14320) _ _ _ _) =>
      step; step;
      eapply (kr_fold (kr_n - 1) 0); [lia | f_equal; lia | f_equal; lia | f_equal; lia | exact INV | exact MU | exact WM
                                     | exact U | exact HJl | reflexivity]
  end.
Qed.

(** 0x14310: s7 = min(vl, 63). *)
Lemma kr_role : forall m1 (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  kr_inv m1 fc0 mc -> munch Wst m0 m1 -> wmono rsegs m0 m1 ->
  evt rsegs QR (KS 0x14310 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 (p + Z.of_nat ok))
                   (Z_to_bv 64 (p + Z.of_nat (ov + vl))) (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl))
                   t3 t4 t5 t6 F0 fc0 m1).
Proof.
  intros m1 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 INV MU WM.
  destruct kr_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  destruct kr_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  destruct kr_low_facts as (L1 & L2 & L3).
  step. step.
  if_cases K; cbv iota; zify_cond K.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1431c) _ _ _ _) =>
      eapply kr_fold_entry; [f_equal; lia | exact INV | exact MU | exact WM]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14318) _ _ _ _) =>
      step; eapply kr_fold_entry; [f_equal; lia | exact INV | exact MU | exact WM]
  end.
Qed.

(** ** KDISP 0x142f8: ieq(k, kl, "role"). *)
Lemma kr_main : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs (QP (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest))
    (KS 0x142f8 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + Z.of_nat ov)) (Z_to_bv 64 (p + Z.of_nat ok))
        (Z_to_bv 64 (p + Z.of_nat (ov + vl))) (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl)) t3 t4 t5 t6 F0 fc0 m0).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof kr_inv0 as INV. pose proof INV as (HC & HX & HM & HQ).
  pose proof (kr_ctx_facts m0 fc0 HC) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (kr_text_facts m0 HX) as (T1 & T2 & T3 & T4 & T5).
  destruct kr_kv as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  destruct kr_st_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _ & _ & _ & MI).
  step. step. step. step. step.
  eapply evt_cut.
  { eapply HIEQ with (l := zb k) (w := S_role) (lo := lo). unfold ieq_pre. rewrite !unsigned_lit by nlia.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    - nlia.
    - destruct HKV as (_ & _ & Ek & _). rewrite <- Ek. apply (mf_text_bytes m0 Sp0 lo c p rest ok kl HX). lia.
    - rewrite kr_length_zb. lia.
    - nlia.
    - lia.
    - exact (kr_role_at m0 MI).
    - change (length S_role) with 4%nat. nlia.
    - apply (kr_stack_ok m0 fc0 mc); [exact INV | unfold IEQ_STACK, PRINTF_K; lia].
    - exact MI. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & MU & WM & MI1 & ST1 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (kr_zs_zb k K5).
  assert (INV1 : kr_inv m1 fc0 mc).
  { eapply kr_inv_call; [exact INV | exact MU | exact WM | exact MI1 | exact FR | exact ST1 | | | |].
    - intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _). unfold IEQ_STACK. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK, SEG_M_SIZE. split; [lia | exact I].
    - cbn [disjoint_from]. unfold IEQ_STACK. split; [lia | exact I]. }
  assert (MU1 : munch Wst m0 m1).
  { eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (X1 & _).
    unfold IEQ_STACK, M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *. split; [lia | exact I]. }
  destruct (ieq k S_role) eqn:EQ; unfold b2z.
  - rewrite (kr_disp_role EQ).
    step. if_cases K; cbv iota; try (exfalso; vm_compute in K; discriminate K).
    eapply kr_role; [exact INV1 | exact MU1 | exact WM].
  - step. if_cases K; cbv iota; try (exfalso; vm_compute in K; discriminate K).
    eapply kr_kmodel; [exact EQ | exact INV1 | exact MU1 | exact WM].
Qed.

End KR.

Lemma mf_krole_holds : ieq_contract -> strlen_contract -> bcmp_contract -> snprintf_contract -> m_refuse_contract ->
  S_MF_KROLE.
Proof.
  intros HIEQ HSL HBC HSN HMR n HT HKM. unfold H_MF_KDISP, H_MF_KAT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc gi k0 rest ok kl ov vl k v Hlen Hne HL HR HKV _.
  destruct HR as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
  apply mf_loop_iff in HL. destruct HL as (HC & HX & HS).
  eapply kr_main; eassumption.
Qed.
