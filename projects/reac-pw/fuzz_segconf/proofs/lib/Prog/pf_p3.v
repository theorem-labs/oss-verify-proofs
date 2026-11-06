(** reac_segconf_parse_file, piece P3 (plain build, image 3776ca44d75c): the long line and its shared refuse site.
    Proof of [S_P3] (reac_segconf_parse_file_pieces_c.v, family F3) from the contracts of strspn (strspn_c.v) and
    refuse (refuse_c.v). Written new.

    Code (plain binary):
      LONG 0x14e08 mv a0,s7; 0x14e0c ld a1,0x40(sp) (" \t\r"); 0x14e10 jal strspn
           0x14e14 bgeu a0,s8 -> 0x14e30
           0x14e18 add a0,s7,a0; lbu a0,0(a0); addi a0,a0,-0x5b; seqz; addi a0,a0,-1; 0x14e2c and s6,a0,s6
           0x14e30 li a3,511; mv a0,s0; mv a1,s3; 0x14e3c ld a2,0x38(sp) (F_long)
      OUTS 0x14e40 jal refuse; 0x14e44 j 0x154b4 (TAIL)
    strspn runs on the rest of the text from the line's start (pfA_facts.r_line_long_rest and O2_strspn_rest_holds
    tie it to SegModel.r_line's long branch). The refuse site [p3_site] serves both cuts: LONG with (F_long, [AI 511])
    and OUTS with (F_outside, [AS key]); after it, TAIL is applied at the next line's offset with the callee's memory,
    FP registers and fcsr, and its post is weakened back to the cut's (p3_ret_weak). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import strspn_c refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_pieces_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Memory facts over any segment list *)
Section Gen.
Variable segs : list Segment.

Lemma p3_disj_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; cbn [disjoint_from]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

Lemma p3_rconf_munch : forall W m m' c rc,
  rconf_at segs m c rc -> munch W m m' -> disjoint_from W c SEG_C_SIZE -> rconf_at segs m' c rc.
Proof.
  intros W m m' c rc (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

(** A write apart from the read span of a C string keeps it. *)
Lemma p3_cstr_munch : forall W m m' a s,
  cstr_at segs m a s -> munch W m m' -> disjoint_from W a (cstr_span a s) -> cstr_at segs m' a s.
Proof.
  intros W m m' a s (bs & sl & B & Ez & N & S) MU D.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  pose (k := Z.to_nat ((- (a + Z.of_nat (length s) + 1)) mod 8)).
  assert (Hk : Z.of_nat k = (- (a + Z.of_nat (length s) + 1)) mod 8) by (unfold k; lia).
  clearbody k.
  assert (Lbs : length bs = length s) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  assert (Lk : length (firstn k sl) = k) by (rewrite length_firstn; lia).
  exists bs, (firstn k sl). split; [|split; [exact Ez|split; [exact N|rewrite Lk; lia]]].
  rewrite <- (firstn_skipn k sl) in B.
  replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with ((bs ++ ZERO :: firstn k sl) ++ skipn k sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _].
  eapply bytes_at_transport; [exact B | exact MU |].
  eapply p3_disj_sub; [exact D | lia |].
  unfold cstr_span. rewrite length_app; cbn [length]. rewrite Lk, Lbs. lia.
Qed.

(** The bytes of the rest of a C string from offset o, with its NUL (what strspn reads). *)
Lemma p3_rest_bytes : forall m t s o, cstr_at segs m t s -> (o <= length s)%nat ->
  exists str, bytes_at segs m (t + Z.of_nat o) (str ++ [ZERO]) /\ zs str = skipn o s /\ ~ In ZERO str.
Proof.
  intros m t s o (bs & sl & B & Ez & N & _) Ho.
  assert (Lbs : length bs = length s) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  exists (skipn o bs).
  rewrite <- (firstn_skipn o bs) in B. rewrite <- app_assoc in B.
  apply bytes_at_app in B as [_ B]. rewrite length_firstn in B.
  replace (Nat.min o (length bs)) with o in B by lia.
  replace (skipn o bs ++ ZERO :: sl) with ((skipn o bs ++ [ZERO]) ++ sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _].
  split; [exact B|]. split.
  - rewrite <- Ez. unfold zs. symmetry. apply pfa_skipn_map.
  - intros HI. apply N. rewrite <- Ez. rewrite <- (firstn_skipn o bs). unfold zs. rewrite map_app.
    apply in_or_app. right. change 0 with (bv_unsigned ZERO). apply in_map. exact HI.
Qed.

(** A slot of a saved-register list, as `ld` reads it. *)
Lemma p3_slot : forall m ws a k w, saved_at segs m a ws -> nth_error ws k = Some w ->
  ov_read_bytes segs m (wa (a + 8 * Z.of_nat k)) 8 = Some (le8 w).
Proof.
  intros m ws. induction ws as [|w0 ws IH]; intros a k w H E; [destruct k; discriminate|].
  unfold saved_at in H. cbn [map concat] in H. apply bytes_at_app in H as [H0 H1].
  rewrite length_le8 in H1. change (Z.of_nat 8) with 8 in H1.
  destruct k as [|k]; cbn [nth_error] in E.
  - injection E as <-. replace (a + 8 * Z.of_nat 0) with (a + Z.of_nat 0) by lia.
    rewrite (bytes_at_ov_read segs m a (le8 w0) 0 8 H0) by (rewrite length_le8; lia).
    reflexivity.
  - replace (a + 8 * Z.of_nat (S k)) with ((a + 8) + 8 * Z.of_nat k) by lia.
    exact (IH (a + 8) k w H1 E).
Qed.

Lemma p3_saved_len : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia. Qed.

(** Every byte of a present stack region is a task byte (MemNorm.task_mem's condition). *)
Lemma p3_stk_task : forall m lo hi, MemNorm.task_mem segs m -> stk segs m lo hi ->
  forall x : word, lo <= bv_unsigned x < hi ->
  find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m lo hi T (_ & _ & S) x Hx. destruct (S _ Hx) as [_ [b Hb]].
  replace (wa (bv_unsigned x)) with x in Hb by (unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  unfold mrd in Hb. destruct (m x) as [b'|] eqn:E.
  - exact (T x b' E).
  - left. intros Nf. rewrite (MemNorm.seg_rom_unmapped segs x Nf) in Hb. discriminate.
Qed.

Lemma p3_task_frame : forall lo' hi' m m', MemNorm.task_mem segs m -> munch [(lo', hi')] m m' ->
  (forall x : word, lo' <= bv_unsigned x < hi' ->
     find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE) ->
  MemNorm.task_mem segs m'.
Proof.
  intros lo' hi' m m' T MU H a b E.
  destruct (Z_lt_le_dec (bv_unsigned a) lo') as [L|L].
  - assert (Q : m' a = m a) by (apply MU; cbn [outside]; split; [lia | exact I]).
    rewrite Q in E. exact (T a b E).
  - destruct (Z_lt_le_dec (bv_unsigned a) hi') as [L2|L2]; [apply H; lia|].
    assert (Q : m' a = m a) by (apply MU; cbn [outside]; split; [lia | exact I]).
    rewrite Q in E. exact (T a b E).
Qed.

(** One byte of a byte list, as `lbu` reads it. *)
Lemma p3_firstn1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l ZERO].
Proof.
  induction l as [|x l IH]; intros k H; cbn [length] in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
End Gen.

(** ** This build's image *)
Lemma p3_fs_in_range : forall (sl : list Segment) z lo hi,
  forallb (fun s => (lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi)) sl = true ->
  find_segment sl z 1 <> None -> lo <= z < hi.
Proof.
  induction sl as [|sg rest IH]; intros z lo hi Hall H; cbn [find_segment] in H; [exfalso; apply H; reflexivity|].
  cbn [forallb] in Hall. apply andb_prop in Hall as [H1 H2]. apply andb_prop in H1 as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2.
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) z); cbn [andb] in H;
    [destruct (Z.leb_spec (z + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); [lia|]|];
    eapply IH; eauto.
Qed.

(** Every address of the image's span [0x10000, 0x54000) lies in one of its reserved (page-rounded) segments. *)
Lemma p3_resv_cover : forall z, 65536 <= z < 344064 ->
  exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) <= z < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  intros z Hz.
  assert (L : (4 <= length (segments_reserved rsegs))%nat) by (vm_compute; lia).
  set (d := (Z_to_bv 64 0, Z_to_bv 64 0)).
  destruct (Z_lt_ge_dec z 77824) as [A|A];
    [exists (nth 0 (segments_reserved rsegs) d) | destruct (Z_lt_ge_dec z 131072) as [B|B];
      [exists (nth 1 (segments_reserved rsegs) d) | destruct (Z_lt_ge_dec z 139264) as [C|C];
        [exists (nth 2 (segments_reserved rsegs) d) | exists (nth 3 (segments_reserved rsegs) d)]]];
    (split; [apply nth_In; lia | vm_compute (bv_unsigned (fst (nth _ (segments_reserved rsegs) d)));
             vm_compute (bv_unsigned (snd (nth _ (segments_reserved rsegs) d))); lia]).
Qed.

(** The reader block and the image are apart (both are intervals, and no byte of the block is reserved). *)
Lemma p3_blk_apart_img : forall c, blk_noimg rsegs c SEG_C_SIZE -> c + 16616 <= 65536 \/ 344064 <= c.
Proof.
  intros c Hblk.
  destruct (Z_le_gt_dec (c + 16616) 65536) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec 344064 c) as [R|R]; [exact R|exfalso].
  destruct (p3_resv_cover (Z.max c 65536) ltac:(lia)) as (s & Hin & Hb).
  apply (Hblk (Z.max c 65536 - c) ltac:(unfold SEG_C_SIZE; lia) s Hin). lia.
Qed.

Lemma p3_nz_of_existsb : forall l, existsb (Z.eqb 0) l = false -> ~ In 0 l.
Proof.
  intros l H Hin. assert (E : existsb (Z.eqb 0) l = true) by (apply existsb_exists; exists 0; split; [exact Hin | reflexivity]).
  congruence.
Qed.

Lemma p3_fmt_at : forall m (fp : Z) (f : list Z),
  mem_inv rsegs m -> ro_bytes_b rsegs fp (zb f ++ [ZERO]) = true -> 0 <= fp ->
  fp + Z.of_nat (length f) + 1 <= 2^64 -> existsb (Z.eqb 0) f = false -> zs (zb f) = f ->
  cstrz_at rsegs m fp f.
Proof.
  intros m fp f MI HB H0 H1 HZ HS. exists (zb f). split.
  - apply ro_bytes_at; [exact MI | lia | unfold zb; rewrite length_app, length_map; cbn [length]; lia |].
    apply ro_bytes_b_sound. exact HB.
  - split; [exact HS | apply p3_nz_of_existsb; exact HZ].
Qed.

(** The two formats of P3's site in .rodata (0x10628 F_long, 0x10402 F_outside). *)
Lemma p3_long_at : forall m, mem_inv rsegs m -> cstrz_at rsegs m PF_STR_LONG F_long.
Proof.
  intros m MI. apply p3_fmt_at;
    [exact MI | vm_compute; reflexivity | unfold PF_STR_LONG; lia | apply Z.leb_le; vm_compute; reflexivity
     | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma p3_outside_at : forall m, mem_inv rsegs m -> cstrz_at rsegs m PF_STR_OUTSIDE F_outside.
Proof.
  intros m MI. apply p3_fmt_at;
    [exact MI | vm_compute; reflexivity | unfold PF_STR_OUTSIDE; lia | apply Z.leb_le; vm_compute; reflexivity
     | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma p3_long_end : PF_STR_LONG + Z.of_nat (length F_long) + 1 <= sa_ro_end SA.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma p3_outside_end : PF_STR_OUTSIDE + Z.of_nat (length F_outside) + 1 <= sa_ro_end SA.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma p3_in_long : In F_long REFUSE_FORMATS.
Proof. unfold REFUSE_FORMATS. left. reflexivity. Qed.

Lemma p3_in_outside : In F_outside REFUSE_FORMATS.
Proof. unfold REFUSE_FORMATS. cbn [In]. do 9 right. left. reflexivity. Qed.

(** strspn's set " \t\r" at 0x10954 (the frame slot sp + 0x40 holds its address). *)
Lemma p3_blanks_at : forall m, mem_inv rsegs m -> bytes_at rsegs m PF_STR_BLANKS (zb [32; 9; 13] ++ [ZERO]).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold PF_STR_BLANKS; lia | |].
  - change (length (zb [32; 9; 13] ++ [ZERO])) with 4%nat. unfold PF_STR_BLANKS. lia.
  - apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma p3_blanks_nz : ~ In (Z_to_bv 8 0) (zb [32; 9; 13]).
Proof.
  intros H. apply (in_map bv_unsigned) in H.
  change (In 0 (zs (zb [32; 9; 13]))) in H.
  replace (zs (zb [32; 9; 13])) with [32; 9; 13] in H by (vm_compute; reflexivity).
  cbn [In] in H. lia.
Qed.

(** CMD's spn_len with the set " \t\r" is the spine's strspn_blank. *)
Lemma p3_in_set : forall x : byte, in_set (zb [32; 9; 13]) x = blank (bv_unsigned x).
Proof.
  intros x. unfold in_set, blank. cbn [zb map existsb].
  change (bv_unsigned (Z_to_bv 8 32)) with 32. change (bv_unsigned (Z_to_bv 8 9)) with 9.
  change (bv_unsigned (Z_to_bv 8 13)) with 13.
  rewrite (Z.eqb_sym 32), (Z.eqb_sym 9), (Z.eqb_sym 13), orb_false_r. apply orb_assoc.
Qed.

Lemma p3_spn : forall str : list byte, ~ In 0 (zs str) ->
  spn_len (zb [32; 9; 13]) str = strspn_blank (zs str).
Proof.
  intros str H. unfold strspn_blank. rewrite (cut_nul_id (zs str) H). clear H.
  induction str as [|x str IH]; [reflexivity|].
  change (zs (x :: str)) with (bv_unsigned x :: zs str).
  cbn [spn_len takewhile]. rewrite p3_in_set. destruct (blank (bv_unsigned x)); cbn [length]; [rewrite IH|]; reflexivity.
Qed.

(** ** The spine *)
Lemma p3_refuse_seg : forall c l f a, rc_seg (refuse c l f a) = rc_seg c.
Proof. intros c l f a. exact (proj1 (refuse_proj c l f a)). Qed.

(** The text bound 65535 is a large nat literal (Nat.of_num_uint), which lia does not read: these restate it. *)
Lemma p3_len_z : forall n : nat, (n <= 65535)%nat -> Z.of_nat n <= 65535.
Proof. intros n H. apply Nat2Z.inj_le in H. change (Z.of_nat 65535) with 65535 in H. exact H. Qed.

Lemma p3_le_65535 : forall n : nat, (n < 512)%nat -> (n <= 65535)%nat.
Proof. intros n H. apply Nat.le_trans with 512%nat; [lia | apply Nat.leb_le; reflexivity]. Qed.

Lemma p3_mod16 : forall x, (x + PARSE_FILE_FRAME) mod 16 = 0 -> x mod 16 = 0.
Proof.
  intros x H. unfold PARSE_FILE_FRAME in H. replace (x + 0x3d0) with (x + 61 * 16) in H by lia.
  rewrite Z_mod_plus_full in H. exact H.
Qed.

(** ** The cut's post from the callee's state
    A cut applied after a call holds for the callee's F', m': its post is weakened back to the F, m at this cut by
    the transitivity of munch and wmono and F' agreeing with F off fa0. *)
Lemma p3_ret_weak : forall v sp gp tp F F' m m' lo c rcf ms,
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  munch ((bv_unsigned sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, bv_unsigned sp + PARSE_FILE_FRAME) :: RC_PARSE_W c)
    m m' ->
  wmono rsegs m m' ->
  pf_ret v sp gp tp F' m' lo c rcf ms -> pf_ret v sp gp tp F m lo c rcf ms.
Proof.
  intros v sp gp tp F F' m m' lo c rcf ms HF MU WM P. unfold pf_ret, ret_post_fp in *.
  destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F2 & fc2 & m2 &
                 E & FR & FF & MU2 & WM2 & MI & TM & ST & Q).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, F2, fc2, m2.
  split; [exact E|]. split; [exact FR|].
  split; [intros k Hk; rewrite (FF k Hk); exact (HF k Hk)|].
  split; [exact (munch_trans _ _ _ _ MU MU2)|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|].
  split; [exact MI|]. split; [exact TM|]. split; [exact ST|exact Q].
Qed.

(** ** The cut's facts across a callee's writes
    A callee writes only below the cut's sp (its frame, [lo, sp)) and inside the reader block c: [p3_inW]. Every
    object of pf_env / pf_text / pf_spill and the cur_name buffer is apart from both. *)
Definition p3_inW (lo Sp c : Z) (W : list ivl) : Prop :=
  Forall (fun iv => (lo <= fst iv /\ snd iv <= Sp) \/ (c <= fst iv /\ snd iv <= c + SEG_C_SIZE)) W.

Lemma p3_inW_disj : forall lo Sp c W a n, p3_inW lo Sp c W ->
  (a + n <= lo \/ Sp <= a) -> (a + n <= c \/ c + SEG_C_SIZE <= a) -> disjoint_from W a n.
Proof.
  intros lo Sp c W a n H. induction H as [|[l h] W Hx _ IH]; intros H1 H2; cbn [disjoint_from]; [exact I|].
  cbn [fst snd] in Hx. split; [lia | exact (IH H1 H2)].
Qed.

Lemma p3_inW_strspn : forall lo Sp c, lo <= Sp - 48 -> p3_inW lo Sp c [(Sp - 48, Sp)].
Proof. intros lo Sp c H. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. Qed.

Lemma p3_inW_refuse : forall lo Sp c rc, lo <= Sp - REFUSE_STACK -> (length (rc_refusal rc) <= 8)%nat ->
  p3_inW lo Sp c (refuse_W Sp c rc).
Proof.
  intros lo Sp c rc H1 H2. unfold refuse_W, p3_inW. apply Forall_app. split.
  - apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; cbn [fst snd]; unfold RC_REFUSED, SEG_C_SIZE; lia | apply Forall_nil].
  - destruct (length (rc_refusal rc) <? 8)%nat; [|apply Forall_nil].
    apply Forall_cons; [right; cbn [fst snd]; unfold refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, SEG_C_SIZE; lia|].
    apply Forall_cons; [right; cbn [fst snd]; unfold RC_NREF, SEG_C_SIZE; lia | apply Forall_nil].
Qed.

(** The callees' footprints lie in the function's W. *)
Lemma p3_sub_strspn : forall Sp c,
  sub_fp [(Sp - 48, Sp)] ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c).
Proof.
  intros Sp c x Hx. unfold RC_PARSE_W, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in *.
  cbn [outside] in *. destruct Hx as [H0 _].
  split; [intros [H1 H2]; apply H0; split; lia | exact I].
Qed.

Lemma p3_sub_refuse : forall Sp c rc, (length (rc_refusal rc) <= 8)%nat ->
  sub_fp (refuse_W Sp c rc) ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c).
Proof.
  intros Sp c rc HL x Hx. unfold refuse_W, RC_PARSE_W, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in *.
  cbn [outside] in Hx.
  destruct (Nat.ltb_spec (length (rc_refusal rc)) 8) as [L8|L8]; cbn [app outside];
    unfold refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED, RC_NREF, RC_N, RC_OVERFLOW, RC_READING, RC_GEN in *;
    repeat split; lia.
Qed.

Lemma p3_env_munch : forall m m' fc fc' Sp lo c v W,
  pf_env m fc Sp lo c v -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  MemNorm.task_mem rsegs m' -> stk rsegs m' lo Sp -> frm0 fc' -> p3_inW lo Sp c W ->
  pf_env m' fc' Sp lo c v.
Proof.
  intros m m' fc fc' Sp lo c v W
    (C0 & C16 & APc & IEc & (FR & TM & (G1 & g & G2) & IL & SPH) & CAT & (ST & DEP & S16 & NR) & MI & SV)
    MU WM MI' TM' ST' FR' IW.
  pose proof (p3_blk_apart_img c IEc) as AI.
  assert (IL' : 341736 <= lo) by exact IL.
  assert (LO : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (DEP' : lo + 7008 <= Sp + 976) by exact DEP.
  assert (APc' : c + 16616 <= lo \/ Sp + 976 <= c) by exact APc.
  assert (DI : forall a n, 65536 <= a -> a + n <= 341736 -> disjoint_from W a n).
  { intros a n H1 H2. apply (p3_inW_disj lo Sp c W a n IW); unfold SEG_C_SIZE; lia. }
  split; [exact C0|]. split; [exact C16|]. split; [exact APc|]. split; [exact IEc|].
  split.
  { split; [exact FR'|]. split; [exact TM'|]. split; [|split; [exact IL | exact SPH]].
    split.
    - eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8. apply DI; cbn; lia.
    - exists g. eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8. apply DI; cbn; lia. }
  split.
  { intros a Ha. rewrite <- (CAT a Ha). unfold mrd.
    cbn [SA SEG_PLAIN sa_catalogue] in Ha. unfold CAT_BYTES in Ha.
    assert (Q : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [apply (DI a 1); lia | lia]. }
    rewrite Q. reflexivity. }
  split.
  { split; [|split; [exact DEP | split; [exact S16 | exact NR]]].
    destruct (stk_split rsegs m lo Sp (Sp + PARSE_FILE_FRAME) ST ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ ST2].
    apply (stk_merge rsegs m' lo Sp); [exact ST' | | unfold PARSE_FILE_FRAME; lia].
    eapply stk_transport_disjoint; [exact ST2 | exact MU | exact WM |].
    apply (p3_inW_disj lo Sp c W); [exact IW | unfold PARSE_FILE_FRAME; lia | unfold PARSE_FILE_FRAME, SEG_C_SIZE; lia]. }
  split; [exact MI'|].
  unfold saved_at in *. eapply bytes_at_transport; [exact SV | exact MU |].
  rewrite p3_saved_len. cbn [sv_list length].
  apply (p3_inW_disj lo Sp c W); [exact IW | unfold PF_SAVE; lia | unfold PF_SAVE, SEG_C_SIZE; lia].
Qed.

Lemma p3_text_munch : forall m m' Sp lo c t s W,
  pf_text m Sp lo c t s -> munch W m m' -> p3_inW lo Sp c W -> pf_text m' Sp lo c t s.
Proof.
  intros m m' Sp lo c t s W (T0 & CS & LS & AP1 & AP2) MU IW.
  split; [exact T0|]. split; [|split; [exact LS | split; [exact AP1 | exact AP2]]].
  eapply p3_cstr_munch; [exact CS | exact MU |].
  apply (p3_inW_disj lo Sp c W); [exact IW | | ].
  - unfold apart, cstr_span, PARSE_FILE_FRAME in *.
    pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
  - unfold apart in AP2. unfold SEG_C_SIZE in *. lia.
Qed.

Lemma p3_spill_munch : forall m m' Sp lo c W, pf_spill m Sp c -> munch W m m' -> p3_inW lo Sp c W ->
  (c + SEG_C_SIZE <= Sp \/ Sp + PARSE_FILE_FRAME <= c) -> pf_spill m' Sp c.
Proof.
  intros m m' Sp lo c W SP MU IW AP. unfold pf_spill, saved_at in *.
  eapply bytes_at_transport; [exact SP | exact MU |]. rewrite p3_saved_len. cbn [length].
  apply (p3_inW_disj lo Sp c W); [exact IW | | ]; unfold PARSE_FILE_FRAME, SEG_C_SIZE in *; lia.
Qed.

Lemma p3_nm_munch : forall m m' Sp lo c W nm, pf_nm_at m (Sp + PF_NAMEBUF) nm -> munch W m m' ->
  p3_inW lo Sp c W -> (c + SEG_C_SIZE <= Sp \/ Sp + PARSE_FILE_FRAME <= c) -> pf_nm_at m' (Sp + PF_NAMEBUF) nm.
Proof.
  intros m m' Sp lo c W nm (f & B & E) MU IW AP. exists f. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L.
  apply (p3_inW_disj lo Sp c W); [exact IW | | ]; unfold PF_NAMEBUF, PARSE_FILE_FRAME, SEG_C_SIZE in *; lia.
Qed.

Ltac fix_ret_pc :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(** ** The refuse site 0x14e40 (OUTS, and the end of LONG): refuse(c, lineno, f, args), then `j` TAIL. *)
Lemma p3_site : refuse_contract -> forall n, H_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (f : list Z) (fp : Z) (args : list arg),
  pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
  pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
  pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
  s9 = Z_to_bv 64 512 -> s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 (ln + 1) -> a2 = Z_to_bv 64 fp ->
  In f REFUSE_FORMATS -> conv_kinds f = map arg_is_s args ->
  fp <> 0 -> cstrz_at rsegs m fp f -> RO_LO <= fp -> fp + Z.of_nat (length f) + 1 <= sa_ro_end SA ->
  va_args_ok rsegs m
    [(lo, bv_unsigned sp);
     (refusal_addr c (length (rc_refusal rc)), refusal_addr c (length (rc_refusal rc)) + RC_REFUSAL_LEN);
     (c + RC_REFUSED, c + RC_REFUSED + 4)] [a3; a4; a5; a6; a7] args ->
  evt rsegs
    (pf_fin v sp gp tp F m lo c
       (r_lines (refuse rc (ln + 1) f args, cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PF_PC_OUTS) fc None m (seg_rom rsegs)).
Proof.
  intros HRF n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d f fp args HC HS HR E9 E6 E0 E1 E2 HIn HCK HF0 HFA HFL HFH HVA.
  destruct HC as (HE & HTx & HSp & Ho & Hn & HLc).
  pose proof HE as HE0.
  destruct HE as (C0 & C16 & APc & IEc & (FRM & TM & SSP & IL & SPH) & CAT & (ST & DEP & S16 & NR) & MI & SV).
  pose proof HS as (RC & COK & NM & CNT).
  pose proof HLc as (Lo' & Llines & Lln & Lle).
  pose proof HTx as (_ & _ & LS & _). pose proof (p3_len_z _ LS) as LSz.
  pose proof RC as (bs & BC & (LBC & _ & _ & _ & HL8 & _)).
  pose proof (bytes_at_bound _ _ _ _ BC) as BCr. rewrite LBC in BCr. unfold SEG_C_SIZE in BCr.
  pose proof (bv_unsigned_in_range 64 sp) as RS. change (bv_modulus 64) with (2^64) in RS.
  assert (IL' : 341736 <= lo) by exact IL.
  assert (LO : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (DEP' : lo + 7008 <= bv_unsigned sp + 976) by exact DEP.
  assert (APc' : c + 16616 <= lo \/ bv_unsigned sp + 976 <= c) by exact APc.
  assert (SPH' : bv_unsigned sp + 976 < 2^63) by exact SPH.
  pose proof (pf_next_gt s o Ho) as NG. pose proof (pf_next_le s o Ho) as NL'.
  assert (FPr : 0 <= fp < 2^64).
  { pose proof HFL as X. pose proof HFH as Y. unfold RO_LO in X. cbn [SA SEG_PLAIN sa_ro_end] in Y. lia. }
  subst a0 a1 a2. unfold PF_PC_OUTS.
  step.
  eapply evt_cut.
  { eapply (HRF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (ln + 1) rc f args).
    rewrite !unsigned_lit by lia.
    split; [exact C0|]. split; [exact C16|]. split; [exact RC|].
    split; [unfold apart, SEG_C_SIZE; lia|]. split; [exact IEc|].
    split; [destruct CNT as [CN1 _]; lia|].
    split; [pose proof (p3_len_z _ LS); lia|]. split; [reflexivity|].
    split; [exact HIn|]. split; [exact HCK|]. split; [exact HF0|]. split; [exact HFA|].
    split; [exact HFL|]. split; [exact HFH|]. split; [exact HVA|].
    split; [split; [exact FRM|]; split; [exact TM|]; split; [exact SSP|]; split; [exact IL | lia]|].
    split; [|exact MI].
    split; [exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                            ltac:(unfold PARSE_FILE_FRAME; lia)))|].
    split; [unfold REFUSE_STACK, PRINTF_K; lia|].
    split; [exact (p3_mod16 _ S16)|].
    intros a Ha. apply NR. unfold PARSE_FILE_FRAME; lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' &
                  m' & E & FRM' & FF & MU & WM & MI' & TM' & ST' & RC').
  subst ms'. rewrite (unsigned_lit c) in MU, RC' by lia.
  fix_ret_pc.
  step.
  assert (IW : p3_inW lo (bv_unsigned sp) c (refuse_W (bv_unsigned sp) c rc))
    by (apply p3_inW_refuse; [unfold REFUSE_STACK, PRINTF_K; lia | exact HL8]).
  assert (APs : c + SEG_C_SIZE <= bv_unsigned sp \/ bv_unsigned sp + PARSE_FILE_FRAME <= c)
    by (unfold SEG_C_SIZE, PARSE_FILE_FRAME; lia).
  pose proof (p3_env_munch m m' fc fc' (bv_unsigned sp) lo c v _ HE0 MU WM MI' TM' ST' FRM' IW) as HE'.
  pose proof (p3_text_munch m m' (bv_unsigned sp) lo c t s _ HTx MU IW) as HTx'.
  eapply evt_mono.
  { eapply (HT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo v c t s
              (refuse rc (ln + 1) f args) cur nm (pf_next s o) (ln + 1) d).
    - split; [exact HE'|]. split; [exact HTx'|].
      split; [exact (p3_spill_munch m m' (bv_unsigned sp) lo c _ HSp MU IW APs)|].
      split; [exact HLc|].
      destruct HTx' as (_ & CS' & _). exact (L_cstr_skipn_holds rsegs m' t s (pf_next s o) CS' Lo').
    - split; [exact RC'|].
      split; [destruct cur as [i|]; cbn [pf_cur_ok] in *; [rewrite p3_refuse_seg; exact COK | exact I]|].
      split; [exact (p3_nm_munch m m' (bv_unsigned sp) lo c _ nm NM MU IW APs)|].
      eapply pf_cnt_refuse; [exact (pf_next_skipn_lt s o Ho) | exact CNT].
    - pose proof (pf_next_skipn_lt s o Ho). lia.
    - exact HR.
    - exact E9.
    - exact E6. }
  intros ms P. eapply p3_ret_weak; [exact FF | | exact WM | exact P].
  eapply munch_weaken; [| exact MU]. apply p3_sub_refuse. exact HL8.
Qed.

(** ** OUTS (0x14e40, entered from P5): refuse(c, lineno, F_outside, key), cur = NULL. *)
Lemma p3_outs : refuse_contract -> forall n, H_TAIL n -> H_OUTS n.
Proof.
  intros HRF n HT. unfold H_OUTS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d kp key HC HS HR E9 E6 E0 E1 E2 E3 HK HKB.
  pose proof HC as (HE & _).
  pose proof HE as (_ & _ & APc & _ & _ & _ & (ST & DEP & _) & MI & _).
  pose proof HS as (RC & _).
  pose proof RC as (bs & BC & (LBC & _ & _ & _ & HL8 & _)).
  pose proof (bytes_at_bound _ _ _ _ BC) as BCr. rewrite LBC in BCr. unfold SEG_C_SIZE in BCr.
  pose proof (bv_unsigned_in_range 64 sp) as RS. change (bv_modulus 64) with (2^64) in RS.
  assert (LO : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (DEP' : lo + 7008 <= bv_unsigned sp + 976) by exact DEP.
  assert (APc' : c + 16616 <= lo \/ bv_unsigned sp + 976 <= c) by exact APc.
  assert (SPT : bv_unsigned sp + 976 <= 2^64) by (destruct ST as (_ & X & _); exact X).
  unfold pf_inb, PF_BUF in HKB.
  eapply (p3_site HRF n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            t3 t4 t5 t6 F fc m lo v c t s rc None nm o ln d F_outside PF_STR_OUTSIDE [AS key]
            HC HS HR E9 E6 E0 E1 E2 p3_in_outside).
  - vm_compute. reflexivity.
  - unfold PF_STR_OUTSIDE. lia.
  - exact (p3_outside_at m MI).
  - unfold PF_STR_OUTSIDE, RO_LO. lia.
  - exact p3_outside_end.
  - cbn [va_args_ok]. split; [|exact I]. subst a3. unfold va_arg_ok. rewrite unsigned_lit by lia.
    split; [lia|]. split; [exact HK|]. split; [apply p3_le_65535; lia|].
    unfold apart_all.
    apply Forall_cons; [unfold apart; cbn [fst snd]; lia|].
    apply Forall_cons; [unfold apart, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN; cbn [fst snd]; lia|].
    apply Forall_cons; [unfold apart, RC_REFUSED; cbn [fst snd]; lia | apply Forall_nil].
Qed.

(** ** LONG 0x14e30 .. 0x14e3c: a3 = 511, a0 = c, a1 = lineno, a2 = F_long from the slot sp + 0x38, then the site. *)
Lemma p3_long_tail : refuse_contract -> forall n, H_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
  pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
  pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
  pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
  s9 = Z_to_bv 64 512 -> s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
  evt rsegs
    (pf_fin v sp gp tp F m lo c
       (r_lines (refuse rc (ln + 1) F_long [AI 511], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e30) fc None m (seg_rom rsegs)).
Proof.
  intros HRF n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d HC HS HR E9 E6.
  pose proof HC as (HE & _ & HSp & _).
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & MI & _).
  pose proof HR as HR0. destruct HR0 as (E0 & _ & E3 & _).
  assert (HL2 : ov_read_bytes rsegs m (wa (bv_unsigned sp + 56)) 8 = Some (le8 (Z_to_bv 64 PF_STR_LONG))).
  { unfold pf_spill in HSp. pose proof (p3_slot rsegs m _ (bv_unsigned sp + 8) 6 _ HSp eq_refl) as X.
    replace (bv_unsigned sp + 8 + 8 * Z.of_nat 6) with (bv_unsigned sp + 56) in X by lia. exact X. }
  subst s0 s3.
  step. step. step. step.
  eapply (p3_site HRF n HT) with (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc) (cur := cur) (nm := nm)
    (o := o) (ln := ln) (d := d) (f := F_long) (fp := PF_STR_LONG) (args := [AI 511]).
  - exact HC.
  - exact HS.
  - exact HR.
  - exact E9.
  - exact E6.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact p3_in_long.
  - vm_compute. reflexivity.
  - unfold PF_STR_LONG. lia.
  - exact (p3_long_at m MI).
  - unfold PF_STR_LONG, RO_LO. lia.
  - exact p3_long_end.
  - cbn [va_args_ok]. split; [|exact I]. unfold va_arg_ok. rewrite unsigned_lit by lia. lia.
Qed.

(** ** LONG 0x14e18 .. 0x14e2c: at[lead] == '[' clears s6 by the mask (seqz, addi -1, and). *)
Lemma p3_mask_val : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -91)) 1) + -1)) =
  if bv_unsigned b =? 91 then 0 else Z.ones 64.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia. rewrite v_sltiu_b2z.
  destruct (Z.eqb_spec (bv_unsigned b) 91) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - assert (K : (bv_unsigned (Z_to_bv 64 (bv_unsigned b + -91)) <? bv_wrap 64 1) = false).
    { rewrite Z_to_bv_unsigned. change (bv_wrap 64 1) with 1. apply Z.ltb_ge. unfold bv_wrap.
      change (bv_modulus 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
    rewrite K. vm_compute. reflexivity.
Qed.

Lemma p3_mask : forall (b : byte) (x : Z), 0 <= x < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -91)) 1) + -1)))
                     (bv_unsigned (Z_to_bv 64 x))) =
  Z_to_bv 64 (if bv_unsigned b =? 91 then 0 else x).
Proof.
  intros b x Hx. rewrite p3_mask_val. rewrite (unsigned_lit x) by lia.
  destruct (bv_unsigned b =? 91).
  - rewrite Z.land_0_l. reflexivity.
  - rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma p3_byte_val : forall (str : list byte) k, (k < length str)%nat ->
  bv_unsigned (nth k (str ++ [ZERO]) ZERO) = nth k (zs str) 0.
Proof.
  intros str k H. rewrite app_nth1 by exact H. unfold zs. rewrite <- (map_nth bv_unsigned str ZERO k). reflexivity.
Qed.

Lemma p3_cur_range : forall c rc cur, pf_cur_ok rc cur -> (length (rc_seg rc) <= 32)%nat -> 0 <= c ->
  c + 16616 <= 2^64 -> 0 <= pf_cur_ptr c cur < 2^64.
Proof.
  intros c rc [i|] H L C0 C1; cbn [pf_cur_ptr pf_cur_ok] in *; [unfold rseg_addr, RSEG_SIZE; lia | lia].
Qed.

Lemma p3_cur_ptr_if : forall c (e : bool) cur,
  Z_to_bv 64 (if e then 0 else pf_cur_ptr c cur) = Z_to_bv 64 (pf_cur_ptr c (if e then None else cur)).
Proof. intros c [|] cur; reflexivity. Qed.

Lemma p3_cur_ok_if : forall rc (e : bool) cur, pf_cur_ok rc cur -> pf_cur_ok rc (if e then None else cur).
Proof. intros rc [|] cur H; [exact I | exact H]. Qed.

(** ** LONG (0x14e08, entered from P2): strspn on the rest of the text, the '[' test, then the refusal. *)
Lemma p3_long : strspn_contract -> refuse_contract -> forall n, H_TAIL n -> H_LONG n.
Proof.
  intros HSS HRF n HT. unfold H_LONG.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d HC HS HR E9 E6 E7 E8 HL.
  pose proof HC as (HE & HTx & HSp & Ho & Hn & HLc).
  pose proof HE as (C0 & C16 & APc & IEc & (FRM & TM & SSP & IL & SPH) & CAT & (ST & DEP & S16 & NR) & MI & SV).
  pose proof HS as (RC & COK & NM & CNT).
  pose proof HTx as (T0 & CS & LS & AP1 & AP2). pose proof (p3_len_z _ LS) as LSz.
  pose proof RC as (bs & BC & (LBC & LSEG & _ & _ & HL8 & _)).
  pose proof (bytes_at_bound _ _ _ _ BC) as BCr. rewrite LBC in BCr. unfold SEG_C_SIZE in BCr.
  pose proof (bv_unsigned_in_range 64 sp) as RS. change (bv_modulus 64) with (2^64) in RS.
  assert (IL' : 341736 <= lo) by exact IL.
  assert (LO : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (DEP' : lo + 7008 <= bv_unsigned sp + 976) by exact DEP.
  assert (APc' : c + 16616 <= lo \/ bv_unsigned sp + 976 <= c) by exact APc.
  assert (AP1' : t + (Z.of_nat (length s) + 8) <= lo \/ bv_unsigned sp + 976 <= t) by exact AP1.
  pose proof CS as (tb & tsl & TB & TZ & TN & _).
  assert (Ltb : length tb = length s) by (rewrite <- TZ; unfold zs; symmetry; apply length_map).
  pose proof (bytes_at_bound _ _ _ _ TB) as TBr. rewrite length_app in TBr. cbn [length] in TBr. rewrite Ltb in TBr.
  pose proof (pf_line_len_le s o) as PLL. rewrite pfa_len_skipn in PLL.
  destruct (p3_rest_bytes rsegs m t s o CS ltac:(lia)) as (str & HB & HZ & HNZ).
  assert (Lstr : length str = (length s - o)%nat)
    by (rewrite <- (pfa_len_skipn o s), <- HZ; unfold zs; rewrite length_map; reflexivity).
  assert (NZs : ~ In 0 (skipn o s)) by exact (nulfree_skipn o s TN).
  assert (RLd : (strspn_blank (skipn o s) <= length (skipn o s))%nat).
  { unfold strspn_blank. pose proof (cut_nul_len (skipn o s)).
    pose proof (pfa_takewhile_len blank (cut_nul (skipn o s))). lia. }
  rewrite pfa_len_skipn in RLd.
  pose proof (p3_cur_range c rc cur COK LSEG ltac:(lia) ltac:(lia)) as CR.
  assert (HR1 : ov_read_bytes rsegs m (wa (bv_unsigned sp + 64)) 8 = Some (le8 (Z_to_bv 64 PF_STR_BLANKS))).
  { unfold pf_spill in HSp. pose proof (p3_slot rsegs m _ (bv_unsigned sp + 8) 7 _ HSp eq_refl) as X.
    replace (bv_unsigned sp + 8 + 8 * Z.of_nat 7) with (bv_unsigned sp + 64) in X by lia. exact X. }
  pose proof HR as HR0.
  subst s9 s6 s7 s8. unfold PF_PC_LONG.
  step. step. step.
  (* strspn(at, " \t\r") *)
  destruct SSP as (G1 & g & G2).
  eapply evt_cut.
  { eapply (HSS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m str (zb [32; 9; 13]) lo g).
    - rewrite unsigned_lit by lia. exact HB.
    - exact HNZ.
    - rewrite unsigned_lit by (unfold PF_STR_BLANKS; lia). exact (p3_blanks_at m MI).
    - exact p3_blanks_nz.
    - exact G1.
    - exact G2.
    - exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                     ltac:(unfold PARSE_FILE_FRAME; lia))).
    - lia.
    - rewrite unsigned_lit by lia. rewrite Lstr. lia.
    - rewrite unsigned_lit by (unfold PF_STR_BLANKS; lia). left. change (length (zb [32; 9; 13])) with 3%nat.
      unfold PF_STR_BLANKS. lia.
    - left. unfold SSP_GOT. lia.
    - left. unfold SSP_GUARD. lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU & WM & MI1 & ST1).
  subst ms'. fix_ret_pc.
  rewrite (p3_spn str) by (rewrite HZ; exact NZs). rewrite HZ.
  (* the cut's facts at strspn's memory m1 *)
  assert (IW : p3_inW lo (bv_unsigned sp) c [(bv_unsigned sp - 48, bv_unsigned sp)]) by (apply p3_inW_strspn; lia).
  assert (APs : c + SEG_C_SIZE <= bv_unsigned sp \/ bv_unsigned sp + PARSE_FILE_FRAME <= c)
    by (unfold SEG_C_SIZE, PARSE_FILE_FRAME; lia).
  assert (TM1 : MemNorm.task_mem rsegs m1).
  { eapply p3_task_frame; [exact TM | exact MU |]. intros x Hx.
    apply (p3_stk_task rsegs m lo (bv_unsigned sp + PARSE_FILE_FRAME) TM ST). unfold PARSE_FILE_FRAME; lia. }
  assert (HC1 : pf_ctx m1 fc (bv_unsigned sp) lo v c t s o ln d n).
  { split; [exact (p3_env_munch m m1 fc fc (bv_unsigned sp) lo c v _ HE MU WM MI1 TM1 ST1 FRM IW)|].
    split; [exact (p3_text_munch m m1 (bv_unsigned sp) lo c t s _ HTx MU IW)|].
    split; [exact (p3_spill_munch m m1 (bv_unsigned sp) lo c _ HSp MU IW APs)|].
    split; [exact Ho|]. split; [exact Hn|]. exact HLc. }
  assert (HS1 : pf_state m1 (bv_unsigned sp) c rc cur nm (length (skipn o s))).
  { split; [eapply p3_rconf_munch; [exact RC | exact MU | cbn [disjoint_from]; unfold SEG_C_SIZE; split; [lia | exact I]]|].
    split; [exact COK|]. split; [exact (p3_nm_munch m m1 (bv_unsigned sp) lo c _ nm NM MU IW APs)|]. exact CNT. }
  assert (HB1 : bytes_at rsegs m1 (t + Z.of_nat o) (str ++ [ZERO])).
  { eapply bytes_at_transport; [exact HB | exact MU |]. rewrite length_app, Lstr. cbn [length disjoint_from].
    split; [lia | exact I]. }
  assert (WK : forall st ms, pf_fin v sp gp tp F m1 lo c st ms -> pf_fin v sp gp tp F m lo c st ms).
  { intros st ms P. eapply p3_ret_weak; [intros k _; reflexivity | | exact WM | exact P].
    eapply munch_weaken; [apply p3_sub_strspn | exact MU]. }
  (* bgeu lead, len *)
  step.
  if_cases HB2.
  - (* lead >= len: cur is kept *)
    unfold bv_ltu in HB2. rewrite !unsigned_lit in HB2 by lia.
    apply negb_true_iff, Z.ltb_ge in HB2.
    destruct (O2_strspn_rest_holds (skipn o s) NZs) as [_ O2e].
    change (strspn_blank (fst (break_nl (skipn o s)))) with (strspn_blank (pf_line s o)) in O2e.
    replace (r_line rc cur nm (ln + 1) (pf_line s o)) with (refuse rc (ln + 1) F_long [AI 511], cur, nm).
    2: { rewrite (r_line_long rc cur nm (ln + 1) s o HL). rewrite <- O2e.
         replace ((strspn_blank (skipn o s) <? length (pf_line s o))%nat) with false
           by (symmetry; apply Nat.ltb_ge; lia).
         reflexivity. }
    eapply evt_mono; [| exact (WK _)].
    eapply (p3_long_tail HRF n HT) with (m := m1) (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc)
      (cur := cur) (nm := nm) (o := o) (ln := ln) (d := d).
    + exact HC1.
    + exact HS1.
    + exact HR0.
    + reflexivity.
    + reflexivity.
  - (* lead < len: at[lead] == '[' sets cur = NULL *)
    unfold bv_ltu in HB2. rewrite !unsigned_lit in HB2 by lia.
    apply negb_false_iff, Z.ltb_lt in HB2.
    assert (Kl : (strspn_blank (skipn o s) < length str)%nat) by (rewrite Lstr; lia).
    assert (HR3 : ov_read_bytes rsegs m1 (wa (t + Z.of_nat o + Z.of_nat (strspn_blank (skipn o s)))) 1 =
                  Some [nth (strspn_blank (skipn o s)) (str ++ [ZERO]) ZERO]).
    { rewrite (bytes_at_ov_read rsegs m1 _ _ _ 1 HB1) by (rewrite length_app; cbn [length]; lia).
      rewrite (p3_firstn1 (str ++ [ZERO])) by (rewrite length_app; cbn [length]; lia). reflexivity. }
    step. step. step. step. step. step.
    rewrite (p3_mask _ (pf_cur_ptr c cur) CR).
    rewrite (p3_byte_val str _ Kl), HZ.
    rewrite p3_cur_ptr_if.
    replace (r_line rc cur nm (ln + 1) (pf_line s o)) with
      (refuse rc (ln + 1) F_long [AI 511],
       (if nth (strspn_blank (skipn o s)) (skipn o s) 0 =? LBR then None else cur), nm)
      by (symmetry; exact (r_line_long_rest rc cur nm (ln + 1) s o TN HL)).
    eapply evt_mono; [| exact (WK _)].
    eapply (p3_long_tail HRF n HT) with (m := m1) (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc)
      (cur := if nth (strspn_blank (skipn o s)) (skipn o s) 0 =? LBR then None else cur)
      (nm := nm) (o := o) (ln := ln) (d := d).
    + exact HC1.
    + split; [exact (proj1 HS1)|]. split; [apply p3_cur_ok_if; exact COK|]. exact (proj2 (proj2 HS1)).
    + exact HR0.
    + reflexivity.
    + reflexivity.
Qed.

(** ** The piece *)
Theorem pf_p3_holds : strspn_contract -> refuse_contract -> S_P3.
Proof. intros HSS HRF n. split; [exact (p3_long HSS HRF n) | exact (p3_outs HRF n)]. Qed.
