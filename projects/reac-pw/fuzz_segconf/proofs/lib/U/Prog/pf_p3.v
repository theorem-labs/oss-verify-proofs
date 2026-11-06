(** reac_segconf_parse_file, UBSan build (image 1696d6c34ffd): piece P3, the long line and its shared refuse site
    (S_P3 of U/Prog/reac_segconf_parse_file_pieces_c.v: LONG -> TAIL, NEITHER -> TAIL). Written new; the plain walk
    is lib/Prog/pf_p3.v.

    Code (UBSan binary):
      LONG 0x153f8 mv a0,s7 (at = t + o); ld a1,0x78(sp) (" \t\r"); 0x15400 jal strspn (lead)
           0x15404 bgeu a0,s8 -> 0x15430 (lead >= len: cur kept)
           0x15408 not a1,s7; 0x1540c bltu a1,a0 -> trap (at + lead wraps: at lies in the text block)
           0x15410 add a0,s7,a0; lbu a0,0(a0); addi -0x5b; seqz; addi -1 (0 when at[lead] == '[', else -1)
           0x15424 ld a1,0x88(sp); and a1,a0,a1; 0x1542c sd a1,0x88(sp) (cur cleared or kept)
           0x15430 a3 = 511; ld a0,0x90(sp) (c); mv a1,s3 (lineno); ld a2,0x70(sp) (F_long)
      NEITHER 0x15440 jal refuse (a0-a3 set by the caller); 0x15444 j TAIL 0x156a4.
    The strspn call reads the rest of the text from the line's start, the spine's r_line the line only: they agree
    (pfA_facts.O2_strspn_rest_holds). The refuse call's post is weakened to the function's post at the cut
    (its W lies inside the function's, its F' agrees with F off f10). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env strspn_c refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Pure facts *)
Lemma p3_nul_bool : forall l, existsb (Z.eqb 0) l = false -> ~ In 0 l.
Proof.
  intros l H Hi.
  assert (E : existsb (Z.eqb 0) l = true)
    by (apply existsb_exists; exists 0; split; [exact Hi | apply Z.eqb_refl]).
  congruence.
Qed.

Lemma p3_in_set : forall x : byte, in_set (zb [SP; TAB; CR]) x = blank (bv_unsigned x).
Proof.
  intros x.
  assert (A : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z).
  { intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact Hz. }
  unfold in_set. cbn [zb map existsb]. rewrite !A by lia. unfold blank.
  rewrite (Z.eqb_sym 32), (Z.eqb_sym 9), (Z.eqb_sym 13), orb_false_r, orb_assoc. reflexivity.
Qed.

(** strspn's answer on the bytes of a C string is the spine's strspn_blank. *)
Lemma p3_spn : forall bs : list byte, ~ In 0 (zs bs) -> spn_len (zb [SP; TAB; CR]) bs = strspn_blank (zs bs).
Proof.
  intros bs H. unfold strspn_blank. rewrite cut_nul_id by exact H. clear H. unfold zs.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [spn_len map takewhile]. rewrite p3_in_set.
  destruct (blank (bv_unsigned b)); cbn [length]; [rewrite IH; reflexivity | reflexivity].
Qed.

Lemma p3_nth_firstn : forall (l : list Z) n k, (k < n)%nat -> nth k (firstn n l) 0 = nth k l 0.
Proof.
  induction l as [|x l IH]; intros [|n] [|k] H; cbn [firstn nth]; try lia; try reflexivity.
  apply IH. lia.
Qed.

Lemma p3_len_saved : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia.
Qed.

Lemma p3_mod16 : forall x, (x + 1056) mod 16 = 0 -> x mod 16 = 0.
Proof. intros x H. replace x with ((x + 1056) + (-66) * 16) by lia. rewrite Z_mod_plus_full. exact H. Qed.

(** The contracts' nat bound 65535 is kept as a numeral term (Nat.of_num_uint) that lia does not read. *)
Lemma p3_n65 : forall k : nat, (k <= 65535)%nat <-> Z.of_nat k <= 65535.
Proof.
  intros k. rewrite Nat2Z.inj_le. replace (Z.of_nat 65535%nat) with 65535 by (vm_compute; reflexivity).
  reflexivity.
Qed.

(** The cur slot's new word (0x15418 .. 0x15428): addi -0x5b; seqz; addi -1; and with the old cur. *)
Lemma p3_mask : forall (b : byte) (p : Z), 0 <= p < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -91)) 1) + -1)))
                     (bv_unsigned (Z_to_bv 64 p)))
  = Z_to_bv 64 (if bv_unsigned b =? 91 then 0 else p).
Proof.
  intros b p Hp.
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  unfold zxb, v_sltiu. rewrite (unsigned_lit (bv_unsigned b)) by lia. rewrite (unsigned_lit p) by lia.
  change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (bv_unsigned b) 91) as [E|E].
  - rewrite E. change (Z_to_bv 64 (91 + -91)) with (Z_to_bv 64 0).
    rewrite (unsigned_lit 0) by lia. change (0 <? 1) with true. cbv iota.
    rewrite (unsigned_lit 1) by lia. change (1 + -1) with 0. rewrite (unsigned_lit 0) by lia.
    rewrite Z.land_0_l. reflexivity.
  - assert (L : (bv_unsigned (Z_to_bv 64 (bv_unsigned b + -91)) <? 1) = false).
    { rewrite unsigned_lit_wrap. apply Z.ltb_ge.
      pose proof (Z.mod_pos_bound (bv_unsigned b + -91) (2 ^ 64) ltac:(lia)) as MB.
      destruct (Z.eq_dec ((bv_unsigned b + -91) mod 2 ^ 64) 0) as [Z0|Z0]; [|lia].
      exfalso. apply Z.mod_divide in Z0; [|lia]. destruct Z0 as [q Hq]. lia. }
    rewrite L. cbv iota. rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1).
    rewrite unsigned_lit_wrap. change ((-1) mod 2 ^ 64) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
    replace (bv_unsigned b =? 91) with false by (symmetry; apply Z.eqb_neq; exact E). reflexivity.
Qed.

Lemma p3_not : forall x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615) = Z_to_bv 64 (18446744073709551615 - x).
Proof. intros x Hx. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. reflexivity. Qed.

(** ** This image *)
(** No byte of the reader block lies in a reserved segment: the four cover [0x10000, 0x55000). *)
Lemma p3_noimg : forall c k, blk_noimg rsegs c k -> 0 < k -> c + k <= 0x10000 \/ 0x55000 <= c.
Proof.
  intros c k H Hk.
  destruct (Z_le_gt_dec (c + k) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec 0x55000 c) as [G|G]; [right; exact G|]. exfalso.
  set (x := Z.max c 0x10000).
  assert (Hx : c <= x < c + k) by (unfold x; lia).
  assert (Hx2 : 0x10000 <= x < 0x55000) by (unfold x; lia).
  assert (E : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) =
              [(65536, 12288); (77824, 57344); (135168, 8192); (143360, 204800)]) by (vm_compute; reflexivity).
  assert (P : exists p, In p [(65536, 12288); (77824, 57344); (135168, 8192); (143360, 204800)] /\
                        fst p <= x < fst p + snd p).
  { destruct (Z_lt_le_dec x 77824); [exists (65536, 12288)|].
    2: destruct (Z_lt_le_dec x 135168); [exists (77824, 57344)|].
    3: destruct (Z_lt_le_dec x 143360); [exists (135168, 8192) | exists (143360, 204800)].
    all: split; [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [fst snd]; lia]. }
  destruct P as (p & Hp & Hpx). rewrite <- E in Hp. apply in_map_iff in Hp as (sg & Esg & Hsg).
  apply (H (x - c) ltac:(lia) sg Hsg). subst p. cbn [fst snd] in Hpx. replace (c + (x - c)) with x by lia.
  exact Hpx.
Qed.

Lemma p3_ro_str : forall m a l, mem_inv rsegs m -> ro_bytes_b rsegs a (zb l ++ [ZERO]) = true -> 0 <= a ->
  a + Z.of_nat (length l) + 1 <= 2 ^ 64 -> bytes_at rsegs m a (zb l ++ [ZERO]).
Proof.
  intros m a l MI H Ha Hl. apply ro_bytes_at; [exact MI | exact Ha | | apply ro_bytes_b_sound; exact H].
  rewrite length_app. unfold zb. rewrite length_map. cbn [length]. lia.
Qed.

Lemma p3_blanks_at : forall m, mem_inv rsegs m -> bytes_at rsegs m PF_STR_BLANKS (zb [SP; TAB; CR] ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. apply p3_ro_str; [exact MI | vm_compute; reflexivity | unfold PF_STR_BLANKS; lia |].
  cbn [length]. unfold PF_STR_BLANKS. lia.
Qed.

Lemma p3_fmt_at : forall m fp f, mem_inv rsegs m -> ro_bytes_b rsegs fp (zb f ++ [ZERO]) = true ->
  existsb (Z.eqb 0) f = false -> zs (zb f) = f -> 0 <= fp -> fp + Z.of_nat (length f) + 1 <= 2 ^ 64 ->
  cstrz_at rsegs m fp f.
Proof.
  intros m fp f MI H N Z Hf Hl. exists (zb f). split; [apply p3_ro_str; assumption|].
  split; [exact Z | apply p3_nul_bool; exact N].
Qed.

Lemma p3_len_long : length F_long = 46%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma p3_len_neither : length F_neither = 59%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma p3_long_at : forall m, mem_inv rsegs m -> cstrz_at rsegs m PF_STR_LONG F_long.
Proof.
  intros m MI. apply p3_fmt_at; [exact MI | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | unfold PF_STR_LONG; lia |].
  rewrite p3_len_long. unfold PF_STR_LONG. lia.
Qed.

Lemma p3_neither_at : forall m, mem_inv rsegs m -> cstrz_at rsegs m PF_STR_NEITHER F_neither.
Proof.
  intros m MI. apply p3_fmt_at; [exact MI | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | unfold PF_STR_NEITHER; lia |].
  rewrite p3_len_neither. unfold PF_STR_NEITHER. lia.
Qed.

(** ** Memory facts *)
Lemma p3_cstr_munch : forall W m m' a s,
  cstr_at rsegs m a s -> munch W m m' -> disjoint_from W a (cstr_span a s) -> cstr_at rsegs m' a s.
Proof.
  intros W m m' a s (bs & sl & B & Ez & N & SL) MU D.
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
  rewrite length_app; cbn [length]. rewrite Lk, Lbs. unfold cstr_span in D.
  replace (Z.of_nat (length s + S k)) with (Z.of_nat (length s) + 1 + (- (a + Z.of_nat (length s) + 1)) mod 8)
    by lia.
  exact D.
Qed.

Lemma p3_rc_tr : forall W m m' c rc,
  rconf_at rsegs m c rc -> munch W m m' -> disjoint_from W c SEG_C_SIZE -> rconf_at rsegs m' c rc.
Proof.
  intros W m m' c rc (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

Lemma p3_read_byte : forall m a r k, cstr_at rsegs m a r -> (k < length r)%nat ->
  exists b : byte, ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [b] /\ bv_unsigned b = nth k r 0.
Proof.
  intros m a r k (bs & sl & B & Ez & N & S) Hk.
  assert (Lbs : length bs = length r) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  exists (nth k bs ZERO). split.
  - rewrite (bytes_at_ov_read rsegs m a _ k 1 B) by (rewrite length_app; cbn [length]; lia).
    rewrite (sq_skipn_cons (bs ++ ZERO :: sl) k ZERO) by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by lia. reflexivity.
  - rewrite <- Ez. unfold zs. rewrite <- (map_nth bv_unsigned bs ZERO k). reflexivity.
Qed.

(** The stack region's bytes are task bytes, so a callee's write there keeps MemNorm's normal form. *)
Lemma p3_stk_task : forall m lo hi, MemNorm.task_mem rsegs m -> stk rsegs m lo hi ->
  forall x : word, lo <= bv_unsigned x < hi ->
  find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m lo hi T (_ & _ & S) x Hx. destruct (S _ Hx) as [_ [b Hb]].
  replace (wa (bv_unsigned x)) with x in Hb by (unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  unfold mrd in Hb. destruct (m x) as [b'|] eqn:E.
  - exact (T x b' E).
  - left. intros Nf. rewrite (MemNorm.seg_rom_unmapped rsegs x Nf) in Hb. discriminate.
Qed.

Lemma p3_task_frame : forall lo' hi' m m', MemNorm.task_mem rsegs m -> munch [(lo', hi')] m m' ->
  (forall x : word, lo' <= bv_unsigned x < hi' ->
     find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE) ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros lo' hi' m m' T MU H a b E.
  destruct (Z_lt_le_dec (bv_unsigned a) lo') as [L|L].
  - assert (Q : m' a = m a) by (apply MU; cbn [outside]; split; [lia | exact I]).
    rewrite Q in E. exact (T a b E).
  - destruct (Z_lt_le_dec (bv_unsigned a) hi') as [L2|L2]; [apply H; lia|].
    assert (Q : m' a = m a) by (apply MU; cbn [outside]; split; [lia | exact I]).
    rewrite Q in E. exact (T a b E).
Qed.

(** What a write inside the stack region below sp, inside the cur slot, or inside c may change. *)
Definition p3_W (lo sp c : Z) (hole : list ivl) : list ivl := (lo, sp) :: (c, c + SEG_C_SIZE) :: hole.

Lemma p3_dj_frame : forall hole lo Sp c A k,
  (hole = [] \/ hole = [(Sp + 0x88, Sp + 0x90)]) -> lo <= Sp ->
  (c + SEG_C_SIZE <= lo \/ Sp + PARSE_FILE_FRAME <= c) -> Sp <= A -> 0 <= k -> A + k <= Sp + PARSE_FILE_FRAME ->
  (A + k <= Sp + 0x88 \/ Sp + 0x90 <= A) -> disjoint_from (p3_W lo Sp c hole) A k.
Proof.
  intros hole lo Sp c A k Hh H1 H2 H3 H4 H5 H6. unfold p3_W, SEG_C_SIZE, PARSE_FILE_FRAME in *.
  destruct Hh as [-> | ->]; cbn [disjoint_from]; repeat split; first [exact I | lia].
Qed.

Lemma p3_dj_img : forall hole lo Sp c A k,
  (hole = [] \/ hole = [(Sp + 0x88, Sp + 0x90)]) -> 0x54088 <= lo -> lo <= Sp ->
  (c + SEG_C_SIZE <= 0x10000 \/ 0x55000 <= c) -> 0x10000 <= A -> A + k <= 0x54088 ->
  disjoint_from (p3_W lo Sp c hole) A k.
Proof.
  intros hole lo Sp c A k Hh H1 H2 H3 H4 H5. unfold p3_W, SEG_C_SIZE in *.
  destruct Hh as [-> | ->]; cbn [disjoint_from]; repeat split; first [exact I | lia].
Qed.

Lemma p3_dj_text : forall hole lo Sp c t s,
  (hole = [] \/ hole = [(Sp + 0x88, Sp + 0x90)]) -> lo <= Sp ->
  apart t (Z.of_nat (length s) + 8) lo (Sp + PARSE_FILE_FRAME) -> apart t (cstr_span t s) c (c + SEG_C_SIZE) ->
  disjoint_from (p3_W lo Sp c hole) t (cstr_span t s).
Proof.
  intros hole lo Sp c t s Hh H1 H2 H3.
  pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  unfold p3_W, apart, cstr_span, SEG_C_SIZE, PARSE_FILE_FRAME in *.
  destruct Hh as [-> | ->]; cbn [disjoint_from]; repeat split; first [exact I | lia].
Qed.

(** The cut facts that do not name the state, carried through a write [p3_W]. *)
Lemma p3_env_tr : forall hole m m' fc fc' Sp lo c v t s,
  (hole = [] \/ hole = [(Sp + 0x88, Sp + 0x90)]) ->
  pf_env m fc Sp lo c v -> pf_text m Sp lo c t s -> pf_spill m Sp c ->
  munch (p3_W lo Sp c hole) m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> frm0 fc' ->
  stk rsegs m' lo (Sp + PARSE_FILE_FRAME) ->
  pf_env m' fc' Sp lo c v /\ pf_text m' Sp lo c t s /\ pf_spill m' Sp c.
Proof.
  intros hole m m' fc fc' Sp lo c v t s Hh ENV TXT SPL MU MI TM FRM ST.
  destruct ENV as (C0 & C16 & APc & NI & PE & CAT & STK & MI0 & SV).
  destruct PE as (FRM0 & TM0 & SSP & IL & SPH).
  destruct STK as (ST0 & DEP & S16 & NR).
  destruct TXT as (T0 & CS & LS & APt & APtc).
  destruct SPL as (SP1 & SP2 & SP3).
  pose proof (p3_noimg c SEG_C_SIZE NI ltac:(unfold SEG_C_SIZE; lia)) as CI.
  assert (LO0 : 0 <= lo) by (destruct ST0 as [? _]; assumption).
  assert (ILo : 0x54088 <= lo) by exact IL.
  assert (LSp : lo <= Sp) by (unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in DEP; lia).
  assert (APc' : c + SEG_C_SIZE <= lo \/ Sp + PARSE_FILE_FRAME <= c) by exact APc.
  unfold saved_at in *.
  split; [|split].
  - split; [exact C0|]. split; [exact C16|]. split; [exact APc|]. split; [exact NI|].
    split.
    { split; [exact FRM|]. split; [exact TM|]. split; [|split; [exact IL | exact SPH]].
      destruct SSP as (G1 & g & G2). split; [|exists g].
      - eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8.
        apply p3_dj_img; first [exact Hh | exact CI | (cbn [SA SEG_UBSAN sa_got_guard sa_guard]; lia)].
      - eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8.
        apply p3_dj_img; first [exact Hh | exact CI | (cbn [SA SEG_UBSAN sa_got_guard sa_guard]; lia)]. }
    split.
    { intros a Ha. rewrite <- (CAT a Ha). unfold mrd.
      cbn [SA SEG_UBSAN sa_catalogue] in Ha. unfold CAT_BYTES in Ha.
      assert (Q : m' (wa a) = m (wa a)).
      { apply MU. rewrite wa_unsigned by lia. apply (disjoint_outside _ 0x21468 3256); [|lia].
        apply (p3_dj_img hole lo Sp c 0x21468 3256); first [exact Hh | exact CI | lia]. }
      rewrite Q. reflexivity. }
    split; [split; [exact ST|]; split; [exact DEP|]; split; [exact S16 | exact NR]|].
    split; [exact MI|].
    eapply bytes_at_transport; [exact SV | exact MU |]. rewrite p3_len_saved. cbn [length sv_list].
    apply p3_dj_frame; first [exact Hh | exact APc' | unfold PF_SAVE, PARSE_FILE_FRAME; lia].
  - split; [exact T0|]. split; [|split; [exact LS | split; [exact APt | exact APtc]]].
    eapply p3_cstr_munch; [exact CS | exact MU |]. apply p3_dj_text; first [exact Hh | exact APt | exact APtc | lia].
  - split; [|split].
    + eapply bytes_at_transport; [exact SP1 | exact MU |]. rewrite p3_len_saved. cbn [length].
      apply p3_dj_frame; first [exact Hh | exact APc' | unfold PARSE_FILE_FRAME; lia].
    + eapply bytes_at_transport; [exact SP2 | exact MU |]. rewrite p3_len_saved. cbn [length].
      apply p3_dj_frame; first [exact Hh | exact APc' | unfold PARSE_FILE_FRAME; lia].
    + eapply bytes_at_transport; [exact SP3 | exact MU |]. rewrite length_le8.
      apply p3_dj_frame; first [exact Hh | exact APc' | unfold PF_CSLOT, PARSE_FILE_FRAME; lia].
Qed.

Lemma p3_nm_tr : forall hole m m' lo Sp c nm,
  (hole = [] \/ hole = [(Sp + 0x88, Sp + 0x90)]) -> lo <= Sp ->
  (c + SEG_C_SIZE <= lo \/ Sp + PARSE_FILE_FRAME <= c) -> munch (p3_W lo Sp c hole) m m' ->
  pf_nm_at m (Sp + PF_NAMEBUF) nm -> pf_nm_at m' (Sp + PF_NAMEBUF) nm.
Proof.
  intros hole m m' lo Sp c nm Hh H1 H2 MU (f & B & E). exists f. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L.
  apply p3_dj_frame; first [exact Hh | exact H2 | unfold PF_NAMEBUF, PARSE_FILE_FRAME; lia].
Qed.

Lemma p3_slot_tr : forall m m' lo Sp c w, lo <= Sp ->
  (c + SEG_C_SIZE <= lo \/ Sp + PARSE_FILE_FRAME <= c) -> munch (p3_W lo Sp c []) m m' ->
  bytes_at rsegs m (Sp + PF_CURSLOT) (le8 w) -> bytes_at rsegs m' (Sp + PF_CURSLOT) (le8 w).
Proof.
  intros m m' lo Sp c w H1 H2 MU B.
  eapply bytes_at_transport; [exact B | exact MU |]. rewrite length_le8.
  unfold p3_W, PF_CURSLOT, SEG_C_SIZE, PARSE_FILE_FRAME in *. cbn [disjoint_from]. repeat split; first [exact I | lia].
Qed.

(** The function's post at a later cut, weakened back to the one at this cut. *)
Lemma p3_fin_weaken : forall v (sp gp tp : word) (F F' : bvmap 5 word) m m' lo c st ms,
  munch ((bv_unsigned sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, bv_unsigned sp + PARSE_FILE_FRAME) :: RC_PARSE_W c)
    m m' ->
  wmono rsegs m m' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  pf_fin v sp gp tp F' m' lo c st ms -> pf_fin v sp gp tp F m lo c st ms.
Proof.
  intros v sp gp tp F F' m m' lo c st ms MU WM FF H.
  unfold pf_fin, pf_ret, ret_post_fp in *.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F2 & fc2 & m2 & E & FRM
    & FF2 & MU2 & WM2 & MI2 & TM2 & ST2 & Q).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F2, fc2, m2.
  split; [exact E|]. split; [exact FRM|]. split; [intros k Hk; rewrite (FF2 k Hk); exact (FF k Hk)|].
  split; [eapply munch_trans; [exact MU | exact MU2]|]. split; [eapply wmono_trans; [exact WM | exact WM2]|].
  split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2 | exact Q].
Qed.

Lemma p3_sub_ref : forall lo Sp c rc, lo + REFUSE_STACK <= Sp -> (length (rc_refusal rc) <= 8)%nat ->
  sub_fp (refuse_W Sp c rc) (p3_W lo Sp c []).
Proof.
  intros lo Sp c rc H1 H2. unfold sub_fp, refuse_W, p3_W, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED,
    RC_NREF, SEG_C_SIZE.
  destruct (length (rc_refusal rc) <? 8)%nat; cbn [app outside]; intros x Hx;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [exact I | lia].
Qed.

Lemma p3_sub_ref_fun : forall Sp c rc, (length (rc_refusal rc) <= 8)%nat ->
  sub_fp (refuse_W Sp c rc)
    ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c).
Proof.
  intros Sp c rc H2. unfold sub_fp, refuse_W, RC_PARSE_W, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED,
    RC_NREF, RC_N, RC_OVERFLOW, RC_READING, RC_GEN, PARSE_FILE_STACK, PARSE_FILE_FRAME.
  destruct (Nat.ltb_spec (length (rc_refusal rc)) 8) as [L|L]; cbn [app outside]; intros x Hx;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [exact I | lia].
Qed.

Section P3.
Variable n : nat.
Hypothesis HSS : strspn_contract.
Hypothesis HRF : refuse_contract.
Hypothesis HT : H_TAIL n.

(** The refuse site 0x15440 (NEITHER, and LONG after its argument loads), then `j` TAIL. *)
Lemma p3_site : forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F F0 : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (lo Sp : Z) (v : pf_sv)
    (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
    (f : list Z) (fp : Z) (args : list arg),
  0 <= Sp < 2 ^ 64 ->
  pf_ctx m fc Sp lo v c t s o ln d n ->
  rconf_at rsegs m c rc -> pf_cur_ok rc cur -> pf_nm_at m (Sp + PF_NAMEBUF) nm -> pf_cnt rc (length (skipn o s)) ->
  pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
  pf_curslot m Sp c cur ->
  In f REFUSE_FORMATS -> conv_kinds f = map arg_is_s args ->
  cstrz_at rsegs m fp f -> RO_LO <= fp -> fp + Z.of_nat (length f) + 1 <= sa_ro_end SA ->
  va_args_ok rsegs m
    [(lo, Sp); (refusal_addr c (length (rc_refusal rc)), refusal_addr c (length (rc_refusal rc)) + RC_REFUSAL_LEN);
     (c + RC_REFUSED, c + RC_REFUSED + 4)] [a3; a4; a5; a6; a7] args ->
  munch ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c) m0 m ->
  wmono rsegs m0 m -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) ->
  evt rsegs
    (pf_fin v (Z_to_bv 64 Sp) gp tp F0 m0 lo c
       (r_lines (refuse rc (ln + 1) f args, cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 fp)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PF_PC_NEITHER) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F F0 fc m m0 lo Sp v
    c t s rc cur nm o ln d f fp args HSp CTX RC CO NM CN RG CS HF HK FS FL FH VA MU0 WM0 FF0.
  destruct CTX as (ENV & TXT & SPL & Ho & Hn & LC).
  pose proof ENV as ENV0. pose proof TXT as TXT0. pose proof SPL as SPL0.
  destruct ENV as (C0 & C16 & APc & NI & PE & CAT & STK & MI & SV).
  destruct PE as (FRM & TM & SSP & IL & SPH). destruct STK as (ST & DEP & S16 & NR).
  destruct TXT as (T0 & CSt & LS & APt & APtc).
  pose proof RC as RC0. destruct RC0 as (bs & B & E).
  pose proof (bytes_at_bound _ _ _ _ B) as Bc. destruct E as (HL & _ & _ & _ & HNR & _).
  pose proof LC as LC0. destruct LC0 as (Ho' & Hlines & Hln & Hle).
  pose proof (pf_next_le s o Ho) as Hnx. pose proof (pf_next_skipn_lt s o Ho) as Hsk.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ILo : 0x54088 <= lo) by exact IL.
  assert (DEP' : lo + REFUSE_STACK + PARSE_FILE_FRAME <= Sp + PARSE_FILE_FRAME)
    by (unfold PARSE_FILE_STACK in DEP; lia).
  unfold REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME in DEP'.
  assert (SPH' : Sp + 0x420 < 2 ^ 63) by exact SPH.
  assert (APc' : c + SEG_C_SIZE <= lo \/ Sp + PARSE_FILE_FRAME <= c) by exact APc.
  assert (FL' : 0x10000 <= fp) by exact FL.
  assert (FH' : fp + Z.of_nat (length f) + 1 <= 0x1229c) by exact FH.
  unfold SEG_C_SIZE in HL. rewrite HL in Bc.
  pose proof (proj1 (p3_n65 _) LS) as LSz.
  assert (Hln1 : 0 <= ln + 1 < 2 ^ 31) by (clear - Hln Hle Hnx LSz; lia).
  assert (Hfp : 0 <= fp < 2 ^ 64) by (clear - FL' FH'; lia).
  unfold PF_PC_NEITHER.
  step.
  eapply evt_cut.
  { eapply (HRF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (ln + 1) rc f args).
    rewrite !unsigned_lit by lia.
    unfold refuse_pre.
    split; [exact C0|]. split; [exact C16|]. split; [exact RC|].
    split; [unfold apart in *; unfold PARSE_FILE_FRAME in APc'; lia|]. split; [exact NI|].
    split; [destruct CN as [CN1 _]; lia|].
    split; [exact Hln1|]. split; [reflexivity|].
    split; [exact HF|]. split; [exact HK|]. split; [lia|]. split; [exact FS|]. split; [exact FL|].
    split; [exact FH|]. split; [exact VA|].
    split; [split; [exact FRM|]; split; [exact TM|]; split; [exact SSP|]; split; [exact IL | lia]|].
    split; [|exact MI].
    split; [exact (proj1 (stk_split rsegs m lo Sp (Sp + PARSE_FILE_FRAME) ST ltac:(unfold PARSE_FILE_FRAME; lia)))|].
    split; [unfold REFUSE_STACK, PRINTF_K; lia|]. split; [apply p3_mod16; exact S16|].
    intros a Ha. apply NR. unfold PARSE_FILE_FRAME. lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1
    & m1 & E1 & FRM1 & FF1 & MU1 & WM1 & MI1 & TM1 & ST1 & RC1).
  subst ms'.
  assert (ESp : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  rewrite ESp, Ec in MU1. rewrite ESp in ST1. rewrite Ec in RC1.
  rewrite ret_pc_even by (try lia; reflexivity).
  step.
  (* the memory facts after the call *)
  assert (MW1 : munch (p3_W lo Sp c []) m m1)
    by (eapply munch_weaken; [apply p3_sub_ref; [unfold REFUSE_STACK, PRINTF_K; lia | exact HNR] | exact MU1]).
  pose proof (proj2 (stk_split rsegs m lo Sp (Sp + PARSE_FILE_FRAME) ST ltac:(unfold PARSE_FILE_FRAME; lia))) as STf.
  assert (ST1' : stk rsegs m1 lo (Sp + PARSE_FILE_FRAME)).
  { eapply stk_merge; [exact ST1 | | unfold PARSE_FILE_FRAME; lia].
    eapply stk_transport_disjoint; [exact STf | exact MW1 | exact WM1 |].
    unfold p3_W, SEG_C_SIZE, PARSE_FILE_FRAME in *. cbn [disjoint_from]. repeat split; first [exact I | lia]. }
  destruct (p3_env_tr [] m m1 fc fc1 Sp lo c v t s (or_introl eq_refl) ENV0 TXT0 SPL0 MW1 MI1 TM1 FRM1 ST1')
    as (ENV1 & TXT1 & SPL1).
  pose proof (p3_nm_tr [] m m1 lo Sp c nm (or_introl eq_refl) ltac:(lia) APc' MW1 NM) as NM1.
  pose proof (p3_slot_tr m m1 lo Sp c _ ltac:(lia) APc' MW1 CS) as CS1.
  assert (MUF : munch ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c) m0 m1)
    by (eapply munch_trans; [exact MU0 | eapply munch_weaken; [apply p3_sub_ref_fun; exact HNR | exact MU1]]).
  eapply evt_mono.
  { eapply (HT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 lo v c t s
              (refuse rc (ln + 1) f args) cur nm (pf_next s o) (ln + 1) d);
      rewrite ?unsigned_lit by lia.
    - split; [exact ENV1|]. split; [exact TXT1|]. split; [exact SPL1|]. split; [exact LC|].
      destruct TXT1 as (_ & CS2 & _). apply L_cstr_skipn_holds; [exact CS2 | exact Hnx].
    - split; [exact RC1|]. split.
      + unfold pf_cur_ok in *. destruct cur as [i|]; [|exact I].
        destruct (refuse_proj rc (ln + 1) f args) as (Es & _). rewrite Es. exact CO.
      + split; [exact NM1|]. eapply pf_cnt_refuse; [exact Hsk | exact CN].
    - lia.
    - exact RG.
    - exact CS1. }
  intros ms' Q. eapply p3_fin_weaken; [| | | exact Q].
  - rewrite unsigned_lit by lia. exact MUF.
  - eapply wmono_trans; [exact WM0 | exact WM1].
  - intros k Hk. rewrite (FF1 k Hk). exact (FF0 k Hk).
Qed.

(** LONG from 0x15430 (cur already decided, in its slot): a3 = 511, c from its slot, lineno, F_long from its slot,
    then the site. *)
Lemma p3_ltail : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      : word) (F F0 : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (lo Sp : Z) (v : pf_sv)
    (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
  0 <= Sp < 2 ^ 64 ->
  pf_ctx m fc Sp lo v c t s o ln d n ->
  rconf_at rsegs m c rc -> pf_cur_ok rc cur -> pf_nm_at m (Sp + PF_NAMEBUF) nm -> pf_cnt rc (length (skipn o s)) ->
  pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
  pf_curslot m Sp c cur ->
  munch ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c) m0 m ->
  wmono rsegs m0 m -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) ->
  evt rsegs
    (pf_fin v (Z_to_bv 64 Sp) gp tp F0 m0 lo c
       (r_lines (refuse rc (ln + 1) F_long [AI 511], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15430) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F F0 fc m m0
    lo Sp v c t s rc cur nm o ln d HSp CTX RC CO NM CN RG CS MU0 WM0 FF0.
  pose proof CTX as CTX0. destruct CTX0 as (ENV & TXT & SPL & _).
  destruct SPL as (SP1 & SP2 & SP3).
  destruct ENV as (_ & _ & _ & _ & _ & _ & _ & MI & _).
  assert (RO70 : ro_cells rsegs m (Sp + 0x70)
                   [C8 (Z_to_bv 64 PF_STR_LONG); C8 (Z_to_bv 64 PF_STR_BLANKS); C8 (pf_not (Sp + PF_BUF))])
    by (split; [cbn; tauto | exact SP2]).
  assert (RO90 : ro_cells rsegs m (Sp + 0x90) [C8 (Z_to_bv 64 c)])
    by (split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact SP3]).
  pose proof RG as RG0. destruct RG0 as (E2 & E3 & _). subst s3.
  step. step. step. step.
  eapply p3_site with (f := F_long) (fp := PF_STR_LONG) (args := [AI 511]) (m0 := m0) (F0 := F0) (t := t) (d := d);
    first [exact HSp | exact CTX | exact RC | exact CO | exact NM | exact CN | exact RG | exact CS | exact MU0
          | exact WM0 | exact FF0 | idtac].
  - unfold REFUSE_FORMATS. left. reflexivity.
  - vm_compute. reflexivity.
  - apply p3_long_at. exact MI.
  - unfold RO_LO, PF_STR_LONG. lia.
  - rewrite p3_len_long. cbn [SA SEG_UBSAN sa_ro_end]. unfold PF_STR_LONG. lia.
  - cbn [va_args_ok va_arg_ok]. split; [|exact I]. split; [lia | apply unsigned_lit; lia].
Qed.

(** NEITHER: the site with the caller's a0-a3. *)
Lemma p3_neither : H_NEITHER n.
Proof.
  unfold H_NEITHER.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v
    c t s rc cur nm o ln d lp x CTX ST RG CS E0 E1 E2 E3 HX HXB.
  subst a0 a1 a2 a3.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (Z_to_bv_bv_unsigned sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  destruct ST as (RC & CO & NM & CN).
  pose proof CTX as CTX0. destruct CTX0 as (ENV & TXT & SPL & Ho & Hn & LC).
  destruct ENV as (C0 & C16 & APc & NI & PE & CAT & STK & MI & SV).
  destruct PE as (FRM & TM & SSP & IL & SPH). destruct STK as (ST & DEP & S16 & NR).
  assert (SPH' : Sp + 0x420 < 2 ^ 63) by exact SPH.
  pose proof RC as RC0. destruct RC0 as (bs & B & E).
  pose proof (bytes_at_bound _ _ _ _ B) as Bc. destruct E as (HL & _ & _ & _ & HNR & _).
  unfold SEG_C_SIZE in HL. rewrite HL in Bc.
  assert (LSp : lo + REFUSE_STACK <= Sp)
    by (unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in *; lia).
  unfold REFUSE_STACK, PRINTF_K in LSp.
  destruct HXB as [HXB1 HXB2].
  assert (APc' : c + SEG_C_SIZE <= lo \/ Sp + PARSE_FILE_FRAME <= c) by exact APc.
  unfold PF_BUF in HXB1, HXB2.
  eapply (p3_site ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F F fc m m lo Sp v c t s rc cur nm o ln d F_neither PF_STR_NEITHER [AS x]);
    first [exact RSP | exact CTX | exact RC | exact CO | exact NM | exact CN | exact RG | exact CS | idtac].
  - unfold REFUSE_FORMATS. do 8 right. left. reflexivity.
  - vm_compute. reflexivity.
  - apply p3_neither_at. exact MI.
  - unfold RO_LO, PF_STR_NEITHER. lia.
  - rewrite p3_len_neither. cbn [SA SEG_UBSAN sa_ro_end]. unfold PF_STR_NEITHER. lia.
  - cbn [va_args_ok va_arg_ok]. rewrite unsigned_lit by lia.
    split; [|exact I]. split; [lia|]. split; [exact HX|]. split; [apply p3_n65; lia|].
    unfold apart_all. repeat apply Forall_cons; try apply Forall_nil; unfold apart; cbn [fst snd];
      unfold refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED, SEG_C_SIZE, PARSE_FILE_FRAME in *; lia.
  - apply munch_refl.
  - apply wmono_refl.
  - intros k Hk. reflexivity.
Qed.

(** LONG: strspn, the '[' test, the argument loads, the site. *)
Lemma p3_long : H_LONG n.
Proof.
  unfold H_LONG.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v
    c t s rc cur nm o ln d CTX ST RG CS E7 E8 HL.
  subst s7 s8.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (Z_to_bv_bv_unsigned sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  destruct ST as (RC & CO & NM & CN).
  pose proof CTX as CTX0. destruct CTX0 as (ENV & TXT & SPL & Ho & Hn & LC).
  pose proof ENV as ENV0. pose proof TXT as TXT0. pose proof SPL as SPL0.
  destruct ENV as (C0 & C16 & APc & NI & PE & CAT & STK & MI & SV).
  destruct PE as (FRM & TM & SSP & IL & SPH). destruct STK as (ST & DEP & S16 & NR).
  destruct TXT as (T0 & CSt & LS & APt & APtc).
  destruct SPL as (SP1 & SP2 & SP3).
  pose proof SSP as SSP0. destruct SSP0 as (G1 & g & G2).
  pose proof RC as RC0. destruct RC0 as (bsc & Bc0 & Ec).
  pose proof (bytes_at_bound _ _ _ _ Bc0) as Bc. destruct Ec as (HLc & HSL & _ & _ & HNR & _).
  unfold SEG_C_SIZE in HLc. rewrite HLc in Bc.
  pose proof CSt as CSt0. destruct CSt0 as (bst & slt & Bt0 & Ebt & NS & _).
  pose proof (bytes_at_bound _ _ _ _ Bt0) as Bt. rewrite length_app in Bt. cbn [length] in Bt.
  assert (Lbt : length bst = length s) by (rewrite <- Ebt; unfold zs; symmetry; apply length_map).
  assert (Hos : (o <= length s)%nat) by lia.
  pose proof (L_cstr_skipn_holds rsegs m t s o CSt Hos) as CRt.
  pose proof CRt as CRt0. destruct CRt0 as (bs & sl & BR & Ebs & NRo & _).
  assert (Lbs : length bs = length (skipn o s)) by (rewrite <- Ebs; unfold zs; symmetry; apply length_map).
  pose proof (pf_line_len_le s o) as HLL.
  pose proof (length_skipn o s) as Lsk.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ILo : 0x54088 <= lo) by exact IL.
  assert (DEP' : lo + REFUSE_STACK <= Sp)
    by (unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in *; lia).
  unfold REFUSE_STACK, PRINTF_K in DEP'.
  assert (SPH' : Sp + 0x420 < 2 ^ 63) by exact SPH.
  assert (APc' : c + SEG_C_SIZE <= lo \/ Sp + PARSE_FILE_FRAME <= c) by exact APc.
  assert (APt' : t + Z.of_nat (length s) + 8 <= lo \/ Sp + PARSE_FILE_FRAME <= t) by (unfold apart in APt; lia).
  (* the spine's step: r_line's long branch, its strspn on the rest of the text *)
  rewrite (r_line_long rc cur nm (ln + 1) s o HL).
  assert (Elead : strspn_blank (pf_line s o) = strspn_blank (skipn o s)).
  { unfold pf_line. symmetry. exact (proj2 (O2_strspn_rest_holds (skipn o s) (nulfree_skipn o s NS))). }
  rewrite Elead.
  assert (RO70 : ro_cells rsegs m (Sp + 0x70)
                   [C8 (Z_to_bv 64 PF_STR_LONG); C8 (Z_to_bv 64 PF_STR_BLANKS); C8 (pf_not (Sp + PF_BUF))]).
  { split; [cbn; tauto | exact SP2]. }
  unfold PF_PC_LONG.
  step. step. step.
  eapply evt_cut.
  { eapply (HSS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs (zb [SP; TAB; CR]) lo g).
    all: rewrite ?unsigned_lit by (unfold PF_STR_BLANKS; lia).
    - replace (bs ++ [Z_to_bv 8 0]) with (bs ++ [ZERO]) by reflexivity.
      replace (bs ++ ZERO :: sl) with ((bs ++ [ZERO]) ++ sl) in BR by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in BR as [BR _]. exact BR.
    - apply sq_zs_nul. rewrite Ebs. exact NRo.
    - apply p3_blanks_at. exact MI.
    - apply sq_zs_nul. change (zs (zb [SP; TAB; CR])) with [32; 9; 13]. cbn [In]. lia.
    - exact G1.
    - exact G2.
    - exact (proj1 (stk_split rsegs m lo Sp (Sp + PARSE_FILE_FRAME) ST ltac:(unfold PARSE_FILE_FRAME; lia))).
    - lia.
    - rewrite Lbs, Lsk. unfold PARSE_FILE_FRAME in APt'. lia.
    - left. change (length (zb [SP; TAB; CR])) with 3%nat.
      unfold PF_STR_BLANKS. lia.
    - left. unfold SSP_GOT. lia.
    - left. unfold SSP_GUARD. lia.
    - exact MI. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & E1 & MU1
    & WM1 & MI1 & ST1).
  subst ms'.
  assert (ESp : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  rewrite ?ESp in MU1, ST1.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (p3_spn bs) by (rewrite Ebs; exact NRo). rewrite Ebs.
  assert (Hlead : (strspn_blank (skipn o s) <= length (skipn o s))%nat).
  { unfold strspn_blank. pose proof (pfa_takewhile_len blank (cut_nul (skipn o s))).
    pose proof (cut_nul_len (skipn o s)). lia. }
  pose proof (proj1 (p3_n65 _) LS) as LSz.
  set (lead := strspn_blank (skipn o s)) in *.
  set (len := length (pf_line s o)) in *.
  (* the memory after strspn: it wrote [Sp - 48, Sp) *)
  pose proof (proj2 (stk_split rsegs m lo Sp (Sp + PARSE_FILE_FRAME) ST ltac:(unfold PARSE_FILE_FRAME; lia))) as STf.
  assert (MW1 : munch (p3_W lo Sp c []) m m1).
  { eapply munch_weaken; [|exact MU1]. unfold sub_fp, p3_W. intros x Hx. cbn [outside] in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end. repeat split; first [exact I | lia]. }
  assert (ST1' : stk rsegs m1 lo (Sp + PARSE_FILE_FRAME)).
  { eapply stk_merge; [exact ST1 | | unfold PARSE_FILE_FRAME; lia].
    eapply stk_transport_disjoint; [exact STf | exact MU1 | exact WM1 |].
    cbn [disjoint_from]. unfold PARSE_FILE_FRAME. repeat split; first [exact I | lia]. }
  assert (TM1 : MemNorm.task_mem rsegs m1).
  { eapply p3_task_frame; [exact TM | exact MU1 |]. intros x Hx.
    apply (p3_stk_task m lo (Sp + PARSE_FILE_FRAME) TM ST x). unfold PARSE_FILE_FRAME. lia. }
  destruct (p3_env_tr [] m m1 fc fc Sp lo c v t s (or_introl eq_refl) ENV0 TXT0 SPL0 MW1 MI1 TM1 FRM ST1')
    as (ENV1 & TXT1 & SPL1).
  pose proof (p3_nm_tr [] m m1 lo Sp c nm (or_introl eq_refl) ltac:(lia) APc' MW1 NM) as NM1.
  pose proof (p3_slot_tr m m1 lo Sp c _ ltac:(lia) APc' MW1 CS) as CS1.
  assert (RC1 : rconf_at rsegs m1 c rc).
  { eapply p3_rc_tr; [exact RC | exact MU1 |]. cbn [disjoint_from].
    unfold SEG_C_SIZE, PARSE_FILE_FRAME in *. repeat split; first [exact I | lia]. }
  assert (MUF1 : munch ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c) m m1).
  { eapply munch_weaken; [|exact MU1]. unfold sub_fp, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K.
    intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I]. }
  pose proof TXT1 as TXT1c. destruct TXT1c as (_ & CSt1 & _).
  pose proof (L_cstr_skipn_holds rsegs m1 t s o CSt1 Hos) as CRt1.
  assert (CTX1 : pf_ctx m1 fc Sp lo v c t s o ln d n)
    by exact (conj ENV1 (conj TXT1 (conj SPL1 (conj Ho (conj Hn LC))))).
  (* 0x15404 bgeu lead, len *)
  step.
  let K := fresh "K" in if_cases K.
  - (* lead >= len: cur kept *)
    apply negb_true_iff in K. unfold bv_ltu in K. rewrite !unsigned_lit in K by lia. apply Z.ltb_ge in K.
    cbv iota.
    replace ((lead <? len)%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
    cbn [andb].
    eapply p3_ltail with (t := t) (d := d) (m0 := m) (F0 := F);
      first [exact RSP | exact CTX1 | exact RC1 | exact CO | exact NM1 | exact CN | exact RG | exact CS1
            | exact MUF1 | exact WM1 | idtac].
    intros k Hk. reflexivity.
  - (* lead < len: at[lead] == '[' clears cur *)
    apply negb_false_iff in K. unfold bv_ltu in K. rewrite !unsigned_lit in K by lia. apply Z.ltb_lt in K.
    cbv iota.
    assert (RO88 : ro_cells rsegs m1 (Sp + 136) [C8 (Z_to_bv 64 (pf_cur_ptr c cur))])
      by (split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact CS1]).
    assert (WR : wr_at rsegs m1 (Sp + 136) 8).
    { split; [lia|]. split; [lia|]. intros i Hi. destruct ST1' as (_ & _ & STK).
      apply (proj1 (STK (Sp + 136 + i) ltac:(unfold PARSE_FILE_FRAME; lia))). }
    pose proof (wr_at_store_ok rsegs m1 (Sp + 136) 8 0 8 WR ltac:(lia) ltac:(lia)) as HS.
    rewrite Z.add_0_r in HS.
    destruct (p3_read_byte m1 (t + Z.of_nat o) (skipn o s) lead CRt1 ltac:(lia)) as (b & HRb & Eb).
    (* not a1,s7; bltu a1,a0 -> trap (at + lead does not wrap) *)
    step. rewrite ?p3_not by lia.
    step.
    let K2 := fresh "K" in if_cases K2;
      [exfalso; unfold bv_ltu in K2; rewrite ?unsigned_lit in K2 by lia; apply Z.ltb_lt in K2; lia | cbv iota].
    (* add; lbu at[lead]; the mask; ld cur; and; sd cur *)
    do 8 step.
    assert (Hp : 0 <= pf_cur_ptr c cur < 2 ^ 64).
    { unfold pf_cur_ok in CO. destruct cur as [i|]; cbn [pf_cur_ptr]; [|lia].
      unfold rseg_addr, RSEG_SIZE. lia. }
    rewrite (p3_mask b (pf_cur_ptr c cur) Hp), Eb.
    assert (Enth : nth lead (pf_line s o) 0 = nth lead (skipn o s) 0).
    { destruct (L_line_bytes_holds s o NS) as (EL & _ & _). rewrite EL at 1.
      replace (length (pf_line s o)) with len by reflexivity. apply p3_nth_firstn. lia. }
    replace ((lead <? len)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite Enth. cbn [andb].
    assert (Ecur : (if nth lead (skipn o s) 0 =? 91 then 0 else pf_cur_ptr c cur) =
                   pf_cur_ptr c (if nth lead (skipn o s) 0 =? 91 then None else cur))
      by (destruct (_ =? 91); reflexivity).
    rewrite Ecur.
    assert (CO2 : pf_cur_ok rc (if nth lead (skipn o s) 0 =? 91 then None else cur))
      by (destruct (_ =? 91); [exact I | exact CO]).
    set (cur' := if nth lead (skipn o s) 0 =? 91 then None else cur) in *.
    change (Z_to_bv 64 (Sp + 136)) with (wa (Sp + 136)).
    remember (write_to_mem m1 (wa (Sp + 136)) (le8 (Z_to_bv 64 (pf_cur_ptr c cur')))) as m2 eqn:Em2.
    assert (MU2 : munch [(Sp + 136, Sp + 144)] m1 m2).
    { subst m2. apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
      rewrite length_le8. cbn [inside]. left. lia. }
    assert (WM2 : wmono rsegs m1 m2) by (subst m2; apply wmono_write, wmono_refl).
    assert (MI2 : mem_inv rsegs m2) by (subst m2; apply mem_inv_store; [exact MI1 | rewrite length_le8; exact HS]).
    assert (ST2 : stk rsegs m2 lo (Sp + PARSE_FILE_FRAME))
      by (subst m2; apply stk_write; [exact ST1' | lia | rewrite length_le8; lia]).
    assert (TM2 : MemNorm.task_mem rsegs m2).
    { eapply p3_task_frame; [exact TM1 | exact MU2 |]. intros x Hx.
      apply (p3_stk_task m1 lo (Sp + PARSE_FILE_FRAME) TM1 ST1' x). unfold PARSE_FILE_FRAME. lia. }
    assert (MW2 : munch (p3_W lo Sp c [(Sp + 0x88, Sp + 0x90)]) m1 m2).
    { eapply munch_weaken; [|exact MU2]. unfold sub_fp, p3_W. intros x Hx. cbn [outside] in *.
      repeat match goal with H : _ /\ _ |- _ => destruct H end. repeat split; first [exact I | lia]. }
    destruct (p3_env_tr [(Sp + 0x88, Sp + 0x90)] m1 m2 fc fc Sp lo c v t s (or_intror eq_refl) ENV1 TXT1 SPL1 MW2
                MI2 TM2 FRM ST2) as (ENV2 & TXT2 & SPL2).
    pose proof (p3_nm_tr [(Sp + 0x88, Sp + 0x90)] m1 m2 lo Sp c nm (or_intror eq_refl) ltac:(lia) APc' MW2 NM1)
      as NM2.
    assert (RC2 : rconf_at rsegs m2 c rc).
    { eapply p3_rc_tr; [exact RC1 | exact MU2 |]. cbn [disjoint_from].
      unfold SEG_C_SIZE, PARSE_FILE_FRAME in *. repeat split; first [exact I | lia]. }
    assert (CS2 : pf_curslot m2 Sp c cur').
    { unfold pf_curslot, PF_CURSLOT. subst m2. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (MUF2 : munch ((Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c) m m2).
    { eapply munch_trans; [exact MUF1 | eapply munch_weaken; [|exact MU2]].
      unfold sub_fp, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K.
      intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I]. }
    assert (CTX2 : pf_ctx m2 fc Sp lo v c t s o ln d n)
      by exact (conj ENV2 (conj TXT2 (conj SPL2 (conj Ho (conj Hn LC))))).
    eapply p3_ltail with (t := t) (d := d) (m0 := m) (F0 := F);
      first [exact RSP | exact CTX2 | exact RC2 | exact CO2 | exact NM2 | exact CN | exact RG | exact CS2
            | exact MUF2 | idtac].
    + eapply wmono_trans; [exact WM1 | exact WM2].
    + intros k Hk. reflexivity.
Qed.

End P3.

Theorem pf_p3_holds : strspn_contract -> refuse_contract -> S_P3.
Proof.
  intros HSS HRF n. split; intros HT; [apply p3_long | apply p3_neither]; assumption.
Qed.
