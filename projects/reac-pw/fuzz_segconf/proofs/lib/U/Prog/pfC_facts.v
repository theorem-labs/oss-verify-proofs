(** reac-pw/fuzz_segconf, UBSan build (image 1696d6c34ffd): the UBSan port of lib/Prog/pfC_facts.v, the helpers
    shared by the walks of the pieces P7, P8 and P9 of reac_segconf_parse_file (family F3:
    lib/U/Prog/reac_segconf_parse_file_pieces_c.v). No piece is proved here. Same lemma names and the same proofs
    as the plain file, with this build's facts: the image's reserved segments (PFC_RES, read by vm_compute from
    U/Img0's rsegs), SA = SEG_UBSAN (got_guard 0x221b0, guard 0x53820, catalogue 0x21468, image end 0x54088, last
    page 0x55000), the frame 0x420 (PF_SAVE 0x3b8, PF_NAMEBUF 0x3a8), the spill slots (two saved_at lists at
    sp + 0x10 and sp + 0x70 and the c slot sp + 0x90, [pfc_ld_c]), &c->reading in the slot sp + 0x50, and cur in
    the frame slot sp + 0x88 ([pfc_curslot_call], [pfc_ld_cur]). The frame bytes a step may write are [pfc_scr]:
    sp + 0x60 .. 0x70, the cur slot sp + 0x88 .. 0x90 and sp + 0x98 .. PF_SAVE (every frame byte no cut fact names).

    - The image: the reserved segments, and why a block that is blk_noimg is writable and apart from the image.
    - The post weakening: a cut's post (pf_ret / pf_fin) computed from the memory m' and FP map F' of a later machine
      is the post from the earlier m and F, when m' differs from m only inside the function's W and F' agrees with F
      off f10 ([pf_ret_weaken], [pf_fin_weaken]).
    - The transport of a cut's context (pf_env, pf_text, pf_spill, pf_nm_at, pf_curslot, rconf_at, cstr_at) over a
      call or a store that writes only printf's stack below sp, the c block and the frame's scratch bytes
      ([pfc_fw], [pfc_ctx_call] and the pieces it is made of).
    - The line account at the exit cuts ([pfc_hctx_next]: the head context at pf_next s o and the measure). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Export pfC_pure.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c.
Import ListNotations.
Open Scope Z_scope.

(** * The image *)
(** The reserved segments of the image, page-rounded: the four PT_LOADs (as the refuse walk reads them). *)
Definition PFC_RES : list (Z * Z) := [(0x10000, 0x3000); (0x13000, 0xe000); (0x21000, 0x2000); (0x23000, 0x32000)].

Lemma pfc_res_eq : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) = PFC_RES.
Proof. vm_compute. reflexivity. Qed.

Lemma pfc_segs_eq : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs = PFC_RES.
Proof. vm_compute. reflexivity. Qed.

Lemma pfc_noimg_res : forall c n, blk_noimg rsegs c n -> forall B Sz, In (B, Sz) PFC_RES ->
  forall x, c <= x < c + n -> ~ (B <= x < B + Sz).
Proof.
  intros c n H B Sz Hin x Hx. rewrite <- pfc_res_eq in Hin. apply in_map_iff in Hin as (s & Es & Hs).
  injection Es as E1 E2. specialize (H (x - c) ltac:(lia) s Hs). rewrite E1, E2 in H.
  replace (c + (x - c)) with x in H by lia. exact H.
Qed.

Lemma pfc_noimg_sub : forall c N a n, blk_noimg rsegs c N -> c <= a -> a + n <= c + N -> blk_noimg rsegs a n.
Proof.
  intros c N a n H H1 H2 i Hi s Hs. replace (a + i) with (c + (a - c + i)) by lia. apply H; [lia | exact Hs].
Qed.

Lemma pfc_fs_some : forall (sl : list Segment) a n, 0 < n -> find_segment sl a n <> None ->
  exists sg, In sg sl /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  induction sl as [|sg rest IH]; intros a n Hn H; [cbn [find_segment] in H; contradiction|].
  revert H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) a) as [Hb1|Hb1]; cbn [andb];
    [destruct (Z.leb_spec (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) as [Hb2|Hb2]; cbn [andb] |]; intros H.
  - exists sg. split; [left; reflexivity | lia].
  - destruct (IH a n Hn H) as (s & Hs & Hr). exists s. split; [right; exact Hs | exact Hr].
  - destruct (IH a n Hn H) as (s & Hs & Hr). exists s. split; [right; exact Hs | exact Hr].
Qed.

Lemma pfc_res_none : forall x, (forall B Sz, In (B, Sz) PFC_RES -> ~ (B <= x < B + Sz)) ->
  find_segment rsegs x 1 = None.
Proof.
  intros x H. destruct (find_segment rsegs x 1) eqn:E; [|reflexivity]. exfalso.
  assert (Hs : find_segment rsegs x 1 <> None) by congruence.
  destruct (pfc_fs_some rsegs x 1 ltac:(lia) Hs) as (sg & Hin & Hr).
  apply (H (Z.of_N (seg_base sg)) (Z.of_N (seg_size sg))); [|exact Hr].
  rewrite <- pfc_segs_eq. apply in_map_iff. exists sg. split; [reflexivity | exact Hin].
Qed.

(** A present byte of a block no reserved segment covers is in the overlay, so it is writable. *)
Lemma pfc_wr_at_block : forall m a bs, bytes_at rsegs m a bs -> blk_noimg rsegs a (Z.of_nat (length bs)) ->
  wr_at rsegs m a (Z.of_nat (length bs)).
Proof.
  intros m a bs (H0 & H1 & H) Hni. split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hr : mrd rsegs m (wa (a + i)) <> None).
  { replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. rewrite H by lia.
    intros C. apply nth_error_None in C. lia. }
  unfold mrd in Hr. unfold wview. destruct (m (wa (a + i))) as [b|]; [discriminate|].
  exfalso. apply Hr. apply (MemNorm.seg_rom_unmapped rsegs). apply pfc_res_none.
  intros B Sz Hin. unfold wa. rewrite unsigned_lit by lia.
  exact (pfc_noimg_res a _ Hni B Sz Hin (a + i) ltac:(lia)).
Qed.

(** The c block of a cut is writable. *)
Lemma pfc_c_wr : forall m c rc, rconf_at rsegs m c rc -> blk_noimg rsegs c SEG_C_SIZE -> wr_at rsegs m c SEG_C_SIZE.
Proof.
  intros m c rc (bs & HB & HE) Hni. destruct HE as [HL _].
  rewrite <- HL in Hni |- *. exact (pfc_wr_at_block m c bs HB Hni).
Qed.

(** A .rodata byte string from the image. *)
Lemma pfc_ro_str : forall m a l, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  ro_bytes_b rsegs a l = true -> bytes_at rsegs m a l.
Proof. intros m a l MI H0 H1 H. apply ro_bytes_at; auto. apply ro_bytes_b_sound. exact H. Qed.

(** * Bytes kept by a munch *)

Lemma pfc_bytes_munch : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (H0 & H1 & H) MU HO. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite <- (H i Hi). unfold mrd. rewrite (MU (wa (a + Z.of_nat i))); [reflexivity|].
  rewrite wa_unsigned by lia. apply HO. lia.
Qed.

Lemma pfc_cstr_munch : forall W m m' a s, cstr_at rsegs m a s -> munch W m m' ->
  (forall x, a <= x < a + cstr_span a s -> outside W x) -> cstr_at rsegs m' a s.
Proof.
  intros W m m' a s (bs & sl & B & Hz & Hn & Hsl) MU HO.
  set (k := (- (a + Z.of_nat (length s) + 1)) mod 8) in *.
  assert (Hk : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
  assert (Hlen : length bs = length s) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  exists bs, (firstn (Z.to_nat k) sl). split; [|split; [exact Hz|split; [exact Hn|]]].
  - apply (pfc_bytes_munch W m m' a).
    + rewrite <- (firstn_skipn (Z.to_nat k) sl) in B.
      replace (bs ++ ZERO :: firstn (Z.to_nat k) sl ++ skipn (Z.to_nat k) sl)
        with ((bs ++ ZERO :: firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl) in B
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in B. exact (proj1 B).
    + exact MU.
    + intros x Hx. apply HO. unfold cstr_span. fold k.
      rewrite length_app in Hx. cbn [length] in Hx. rewrite length_firstn in Hx. lia.
  - rewrite length_firstn. lia.
Qed.

(** The rest of a C string from offset o is a C string with the same slack (pf_pieces_spec.L_cstr_skipn). *)
Lemma pfc_cstr_skipn : forall m t s o, cstr_at rsegs m t s -> (o <= length s)%nat ->
  cstr_at rsegs m (t + Z.of_nat o) (skipn o s).
Proof.
  intros m t s o (bs & sl & B & Hz & Hn & Hsl) Ho.
  assert (Hlen : length bs = length s) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  exists (skipn o bs), sl. split; [|split; [|split]].
  - rewrite <- (firstn_skipn o bs) in B. rewrite <- app_assoc in B. apply bytes_at_app in B.
    rewrite length_firstn in B. replace (Nat.min o (length bs)) with o in B by lia. exact (proj2 B).
  - rewrite <- Hz. unfold zs. symmetry. apply skipn_map.
  - intros H. apply Hn. rewrite <- (firstn_skipn o s). apply in_or_app. right. exact H.
  - rewrite length_skipn. replace (t + Z.of_nat o + Z.of_nat (length s - o) + 1) with (t + Z.of_nat (length s) + 1)
      by lia. exact Hsl.
Qed.

Lemma pfc_rconf_munch : forall W m m' c rc, rconf_at rsegs m c rc -> munch W m m' ->
  (forall x, c <= x < c + SEG_C_SIZE -> outside W x) -> rconf_at rsegs m' c rc.
Proof.
  intros W m m' c rc (bs & HB & HE) MU HO. exists bs. split; [|exact HE].
  apply (pfc_bytes_munch W m m' c bs HB MU). destruct HE as [HL _]. rewrite HL. exact HO.
Qed.


(** * The post weakening *)
(** The function's write list, as pf_ret states it. *)
Definition pfc_W (sp c : Z) : list ivl :=
  (sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, sp + PARSE_FILE_FRAME) :: RC_PARSE_W c.

Lemma pf_ret_weaken : forall v sp gp tp F F' m m' lo c rcf ms,
  pf_ret v sp gp tp F' m' lo c rcf ms ->
  munch (pfc_W (bv_unsigned sp) c) m m' -> wmono rsegs m m' ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  pf_ret v sp gp tp F m lo c rcf ms.
Proof.
  intros v sp gp tp F F' m m' lo c rcf ms H MU WM HF. unfold pf_ret, ret_post_fp in *.
  destruct H as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F'' & fc'' & m'' &
                 E & FR & HF2 & MU2 & WM2 & MI & TM & ST & Q).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, F'', fc'', m''.
  refine (conj E (conj FR (conj _ (conj _ (conj _ (conj MI (conj TM (conj ST Q)))))))).
  - intros k Hk. rewrite (HF2 k Hk). apply HF, Hk.
  - eapply munch_trans; [exact MU | exact MU2].
  - eapply wmono_trans; [exact WM | exact WM2].
Qed.

Lemma pf_fin_weaken : forall v sp gp tp F F' m m' lo c st ms,
  pf_fin v sp gp tp F' m' lo c st ms ->
  munch (pfc_W (bv_unsigned sp) c) m m' -> wmono rsegs m m' ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  pf_fin v sp gp tp F m lo c st ms.
Proof. intros. unfold pf_fin in *. eapply pf_ret_weaken; eauto. Qed.

(** * The transport of a cut's context *)
(** The frame bytes a step of a piece may write (UBSan frame): every frame byte no cut fact
    names, that is P7's join-loop flags [sp + 0x60, sp + 0x70), the cur slot [sp + 0x88, sp + 0x90) (P4's seg_get,
    P9's `sd zero`) and [sp + 0x98, sp + PF_SAVE) (ntok, role's low and known, model's low, buf, cur_name). The
    spill slots [sp + 0x10, sp + 0x60), [sp + 0x70, sp + 0x88) and the c slot [sp + 0x90, sp + 0x98), the saved
    registers [sp + 0x3b8, sp + 0x420), the text and the image are kept; cur_name is kept when W also avoids
    [sp + 0x3a8, sp + 0x3b8) ([pfc_nm_call]), the cur slot when W avoids it ([pfc_curslot_call]). *)
Definition pfc_scr (sp x : Z) : Prop :=
  sp + 0x60 <= x < sp + 0x70 \/ sp + PF_CURSLOT <= x < sp + PF_CURSLOT + 8 \/ sp + 0x98 <= x < sp + PF_SAVE.

(** The bytes a step of a piece may write: the stack below sp (its callees' frames and printf's), the c block, and
    the frame's scratch bytes. *)
Definition pfc_fw (sp lo c : Z) (W : list ivl) : Prop :=
  forall x, ~ outside W x -> lo <= x < sp \/ c <= x < c + SEG_C_SIZE \/ pfc_scr sp x.

(** The common case: below sp and in the c block only. *)
Lemma pfc_fw_low : forall sp lo c W,
  (forall x, ~ outside W x -> lo <= x < sp \/ c <= x < c + SEG_C_SIZE) -> pfc_fw sp lo c W.
Proof. intros sp lo c W H x Hx. destruct (H x Hx); [left | right; left]; assumption. Qed.

Lemma pfc_fw_out : forall sp lo c W x, pfc_fw sp lo c W ->
  ~ (lo <= x < sp) -> ~ (c <= x < c + SEG_C_SIZE) -> ~ pfc_scr sp x -> outside W x.
Proof.
  intros sp lo c W x FW H1 H2 H3. destruct (pfc_outside_dec W x) as [H|H]; [exact H|].
  exfalso. destruct (FW x H) as [?|[?|?]]; auto.
Qed.

(** The image bytes the context names lie below lo and in a reserved segment. *)
Lemma pfc_img_out : forall sp lo c W x B Sz, pfc_fw sp lo c W -> blk_noimg rsegs c SEG_C_SIZE -> lo <= sp ->
  In (B, Sz) PFC_RES -> B <= x < B + Sz -> x < lo -> outside W x.
Proof.
  intros sp lo c W x B Sz FW Hni Hls Hin Hx Hlo. apply (pfc_fw_out sp lo c W x FW).
  - lia.
  - intros Hc. exact (pfc_noimg_res c SEG_C_SIZE Hni B Sz Hin x Hc Hx).
  - unfold pfc_scr, PF_CURSLOT, PF_SAVE. lia.
Qed.

(** The stack region of a cut lies below the frame, deep enough for refuse and printf. *)
Lemma pfc_env_lo : forall m fc sp lo c v, pf_env m fc sp lo c v ->
  0 <= lo /\ lo + 6032 <= sp /\ sp + 0x420 <= 2 ^ 64 /\ apart c SEG_C_SIZE lo (sp + 0x420) /\
  0x54088 <= lo /\ sp + 0x420 < 2 ^ 63.
Proof.
  intros m fc sp lo c v (_ & _ & Hap & _ & (_ & _ & _ & Hie & Hsp) & _ & ((H0 & H1 & _) & Hdep & _) & _).
  unfold PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME in *.
  assert (Hie' : 0x54088 <= lo) by exact Hie. repeat split; try lia. exact Hap.
Qed.

Lemma pfc_env_call : forall m m' fc fc' sp lo c v W,
  pf_env m fc sp lo c v -> munch W m m' -> wmono rsegs m m' -> pfc_fw sp lo c W ->
  (forall x, pfc_scr sp x -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo sp -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> frm0 fc' ->
  pf_env m' fc' sp lo c v.
Proof.
  intros m m' fc fc' sp lo c v W HENV MU WM FW PR ST' MI' TM' FRM'.
  destruct (pfc_env_lo m fc sp lo c v HENV) as (Lo0 & Lsp & Lhi & _ & Lie & _).
  destruct HENV as
    (Hc0 & Hc16 & Hap & Hni & (Hfrm & Htm & (Hg1 & (g & Hg2)) & Hie & Hsp) & Hcat & (ST & Hdep & Hal & Hrom) & MI & Hsv).
  destruct ST as (Hlo0 & Hhi & STa).
  split; [exact Hc0|]. split; [exact Hc16|]. split; [exact Hap|]. split; [exact Hni|].
  split; [|split; [|split; [|split]]].
  - (* printf_env *)
    split; [exact FRM'|]. split; [exact TM'|]. split; [|split; [exact Hie | exact Hsp]].
    split.
    + apply (pfc_bytes_munch W m m' _ _ Hg1 MU). rewrite length_le8. cbn [sa_got_guard SA SEG_UBSAN].
      intros x Hx. apply (pfc_img_out sp lo c W x 0x21000 0x2000 FW Hni ltac:(lia)); [cbn; tauto | lia | lia].
    + exists g. apply (pfc_bytes_munch W m m' _ _ Hg2 MU). rewrite length_le8. cbn [sa_guard SA SEG_UBSAN].
      intros x Hx. apply (pfc_img_out sp lo c W x 0x23000 0x32000 FW Hni ltac:(lia)); [cbn; tauto | lia | lia].
  - (* cat_img *)
    intros a Ha. rewrite <- (Hcat a Ha). unfold mrd. rewrite (MU (wa a)); [reflexivity|].
    unfold CAT_BYTES, CAT_ROW, CAT_N in Ha. cbn [sa_catalogue SA SEG_UBSAN] in Ha.
    rewrite wa_unsigned by lia.
    apply (pfc_img_out sp lo c W a 0x21000 0x2000 FW Hni ltac:(lia)); [cbn; tauto | lia | lia].
  - (* stack_ok *)
    split; [|split; [exact Hdep | split; [exact Hal | exact Hrom]]].
    apply (stk_merge rsegs m' lo sp (sp + PARSE_FILE_FRAME)); [exact ST' | | unfold PARSE_FILE_FRAME; lia].
    apply (stk_transport rsegs W m m' sp (sp + PARSE_FILE_FRAME)).
    + split; [lia|]. split; [unfold PARSE_FILE_FRAME; lia|]. intros a Ha. apply STa. unfold PARSE_FILE_FRAME in *; lia.
    + exact MU.
    + exact WM.
    + intros x Hx. unfold PARSE_FILE_FRAME in Hx.
      destruct (pfc_outside_dec W x) as [Ho|Ho]; [left; exact Ho | right].
      unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap.
      destruct (FW x Ho) as [H|[H|H]]; [exfalso; lia | exfalso; unfold SEG_C_SIZE in H; lia |].
      destruct (PR x H Ho) as [b Hb]. exists b. unfold mrd in Hb.
      destruct (m' (wa x)) as [b'|] eqn:E; [exact Hb|].
      rewrite (Hrom x ltac:(unfold PARSE_FILE_FRAME; lia)) in Hb. discriminate.
  - exact MI'.
  - (* saved registers *)
    unfold saved_at in *. apply (pfc_bytes_munch W m m' _ _ Hsv MU). rewrite pfc_len_le8s.
    cbn [sv_list length]. intros x Hx. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap.
    apply (pfc_fw_out sp lo c W x FW); unfold pfc_scr, PF_CURSLOT, PF_SAVE, PF_NAMEBUF, SEG_C_SIZE in *; lia.
Qed.

Lemma pfc_text_call : forall m m' sp lo c t s W, pf_text m sp lo c t s -> munch W m m' -> pfc_fw sp lo c W ->
  lo <= sp -> pf_text m' sp lo c t s.
Proof.
  intros m m' sp lo c t s W (Ht0 & HC & Hl & Ha1 & Ha2) MU FW Hls.
  split; [exact Ht0|]. split; [|split; [exact Hl | split; [exact Ha1 | exact Ha2]]].
  apply (pfc_cstr_munch W m m' t s HC MU). intros x Hx.
  assert (Hk : 0 <= (- (t + Z.of_nat (length s) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  unfold cstr_span in Hx, Ha2. unfold apart, PARSE_FILE_FRAME, SEG_C_SIZE in *.
  apply (pfc_fw_out sp lo c W x FW); unfold pfc_scr, PF_CURSLOT, PF_SAVE, SEG_C_SIZE; lia.
Qed.

(** The spill slots: sp + 0x10 .. 0x60, sp + 0x70 .. 0x88 and the c slot sp + 0x90. *)
Lemma pfc_spill_call : forall m m' fc sp lo c v W, pf_env m fc sp lo c v -> pf_spill m sp c -> munch W m m' ->
  pfc_fw sp lo c W -> pf_spill m' sp c.
Proof.
  intros m m' fc sp lo c v W HENV (HS1 & HS2 & HS3) MU FW.
  destruct (pfc_env_lo m fc sp lo c v HENV) as (_ & Lsp & _ & Hap & _).
  unfold apart, SEG_C_SIZE in Hap. unfold saved_at in *.
  split; [|split].
  - apply (pfc_bytes_munch W m m' _ _ HS1 MU). rewrite pfc_len_le8s. cbn [length].
    intros x Hx. apply (pfc_fw_out sp lo c W x FW); unfold pfc_scr, PF_CURSLOT, SEG_C_SIZE, PF_SAVE; lia.
  - apply (pfc_bytes_munch W m m' _ _ HS2 MU). rewrite pfc_len_le8s. cbn [length].
    intros x Hx. apply (pfc_fw_out sp lo c W x FW); unfold pfc_scr, PF_CURSLOT, SEG_C_SIZE, PF_SAVE; lia.
  - apply (pfc_bytes_munch W m m' _ _ HS3 MU). rewrite length_le8.
    intros x Hx. apply (pfc_fw_out sp lo c W x FW); unfold pfc_scr, PF_CURSLOT, PF_CSLOT, SEG_C_SIZE, PF_SAVE in *; lia.
Qed.

Lemma pfc_nm_call : forall m m' fc sp lo c v nm W, pf_env m fc sp lo c v -> pf_nm_at m (sp + PF_NAMEBUF) nm ->
  munch W m m' -> (forall x, sp + PF_NAMEBUF <= x < sp + PF_SAVE -> outside W x) ->
  pf_nm_at m' (sp + PF_NAMEBUF) nm.
Proof.
  intros m m' fc sp lo c v nm W HENV (f & HB & HE) MU HO. exists f. split; [|exact HE].
  apply (pfc_bytes_munch W m m' _ _ HB MU). destruct HE as [HL _]. rewrite HL.
  intros x Hx. apply HO. unfold PF_NAMEBUF, PF_SAVE in *. lia.
Qed.

(** cur in its frame slot sp + 0x88, kept when W avoids the slot. *)
Lemma pfc_curslot_call : forall m m' fc sp lo c v cur W, pf_env m fc sp lo c v -> pf_curslot m sp c cur ->
  munch W m m' -> (forall x, sp + PF_CURSLOT <= x < sp + PF_CURSLOT + 8 -> outside W x) -> pf_curslot m' sp c cur.
Proof.
  intros m m' fc sp lo c v cur W _ H MU HO. unfold pf_curslot in *.
  apply (pfc_bytes_munch W m m' _ _ H MU). rewrite length_le8. exact HO.
Qed.

(** The cur slot as a load (`ld a0, 0x88(sp)`). *)
Lemma pfc_ld_cur : forall m sp c cur, pf_curslot m sp c cur ->
  ov_read_bytes rsegs m (wa (sp + PF_CURSLOT)) 8 = Some (le8 (Z_to_bv 64 (pf_cur_ptr c cur))).
Proof.
  intros m sp c cur H. unfold pf_curslot in H.
  pose proof (bytes_at_ov_read rsegs m _ _ 0 8 H ltac:(rewrite length_le8; lia)) as R.
  replace (sp + PF_CURSLOT + Z.of_nat 0) with (sp + PF_CURSLOT) in R by lia. rewrite R. f_equal.
Qed.

(** The c slot as a load (`ld a0, 0x90(sp)`). *)
Lemma pfc_ld_c : forall m sp c, pf_spill m sp c ->
  ov_read_bytes rsegs m (wa (sp + PF_CSLOT)) 8 = Some (le8 (Z_to_bv 64 c)).
Proof.
  intros m sp c (_ & _ & H).
  pose proof (bytes_at_ov_read rsegs m _ _ 0 8 H ltac:(rewrite length_le8; lia)) as R.
  replace (sp + PF_CSLOT + Z.of_nat 0) with (sp + PF_CSLOT) in R by lia. rewrite R. f_equal.
Qed.

(** The whole mid-line context over one call or store. *)
Lemma pfc_ctx_call : forall m m' fc fc' sp lo v c t s o ln d n W,
  pf_ctx m fc sp lo v c t s o ln d n -> munch W m m' -> wmono rsegs m m' -> pfc_fw sp lo c W ->
  (forall x, pfc_scr sp x -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo sp -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> frm0 fc' ->
  pf_ctx m' fc' sp lo v c t s o ln d n.
Proof.
  intros m m' fc fc' sp lo v c t s o ln d n W (HE & HT & HS & Ho & Hn & HL) MU WM FW PR ST MI TM FR.
  destruct (pfc_env_lo _ _ _ _ _ _ HE) as (_ & Lsp & _).
  split; [eapply pfc_env_call; eauto|]. split; [eapply pfc_text_call; eauto; lia|].
  split; [eapply pfc_spill_call; eauto|]. auto.
Qed.

(** * The line account at the exit cuts *)

(** From a mid-line context, the head/tail context at the next line's offset, and the measure goes down. *)
Lemma pfc_hctx_next : forall m fc sp lo v c t s o ln d n,
  pf_ctx m fc sp lo v c t s o ln d n ->
  pf_hctx m fc sp lo v c t s (pf_next s o) (ln + 1) d /\
  (length (skipn (pf_next s o) s) < length (skipn o s))%nat /\ (length (skipn (pf_next s o) s) < n)%nat.
Proof.
  intros m fc sp lo v c t s o ln d n (HE & HT & HS & Ho & Hn & HL).
  destruct (pfc_next_gt s o Ho) as [G1 G2]. rewrite !length_skipn in *.
  split; [|split; lia].
  split; [exact HE|]. split; [exact HT|]. split; [exact HS|]. split; [exact HL|].
  destruct HT as (_ & HC & _). apply pfc_cstr_skipn; [exact HC | exact G2].
Qed.

(** * Memory: a block patched by a write inside it *)

(** After a callee wrote ws at D inside the block bs at c (its post: the bytes at D, and munch W of everything else
    of the block), the block holds bs patched with ws. *)
Lemma pfc_bytes_patch : forall W m m' c bs D ws, bytes_at rsegs m c bs -> munch W m m' -> bytes_at rsegs m' D ws ->
  c <= D -> D + Z.of_nat (length ws) <= c + Z.of_nat (length bs) ->
  (forall x, c <= x < c + Z.of_nat (length bs) -> ~ (D <= x < D + Z.of_nat (length ws)) -> outside W x) ->
  bytes_at rsegs m' c (upd_bytes bs (Z.to_nat (D - c)) ws).
Proof.
  intros W m m' c bs D ws (H0 & H1 & HB) MU (G0 & G1 & GB) Hc HD HO.
  split; [lia|]. split; [rewrite upd_bytes_length by lia; lia|]. intros i Hi.
  rewrite upd_bytes_length in Hi by lia.
  rewrite pfc_nth_error_upd by lia. pfc_ltb.
  - rewrite <- (HB i Hi). unfold mrd. rewrite (MU (wa (c + Z.of_nat i))); [reflexivity|].
    rewrite wa_unsigned by lia. apply HO; lia.
  - rewrite <- (GB (i - Z.to_nat (D - c))%nat) by lia. f_equal. f_equal. lia.
  - rewrite <- (HB i Hi). unfold mrd. rewrite (MU (wa (c + Z.of_nat i))); [reflexivity|].
    rewrite wa_unsigned by lia. apply HO; lia.
Qed.

(** * .rodata strings *)
Definition PFC_STR_BADMODEL : Z := 0x104e3.   (* SegModel.F_badmodel *)
Definition PFC_STR_SS : Z := 0x1031b.         (* "%s%s" *)
Definition PFC_STR_BAR : Z := 0x105f0.        (* "|" *)
Definition PFC_STR_EMPTY : Z := 0x1038e.      (* "" *)

(** The refusal formats of the pieces P6 .. P9, at their .rodata addresses. *)
Definition PFC_FMTS : list (list Z * Z) :=
  [(F_knock, PF_STR_KNOCK); (F_badrole, PF_STR_BADROLE); (F_badignore, PF_STR_BADIGNORE); (F_nokey, PF_STR_NOKEY);
   (F_badmodel, PFC_STR_BADMODEL)].

Ltac pfc_zle := apply Z.leb_le; vm_compute; reflexivity.

Lemma pfc_fmt_at : forall m f fp, mem_inv rsegs m -> In (f, fp) PFC_FMTS ->
  fp <> 0 /\ cstrz_at rsegs m fp f /\ RO_LO <= fp /\ fp + Z.of_nat (length f) + 1 <= sa_ro_end SA /\
  In f REFUSE_FORMATS.
Proof.
  intros m f fp MI Hin. unfold PFC_FMTS in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as E1 E2; subst f fp;
    (split; [unfold PF_STR_KNOCK, PF_STR_BADROLE, PF_STR_BADIGNORE, PF_STR_NOKEY, PFC_STR_BADMODEL; lia|]);
    (split; [match goal with |- cstrz_at _ _ _ ?F => exists (zb F) end;
             split; [apply pfc_ro_str; [exact MI | pfc_zle | pfc_zle | vm_compute; reflexivity]
                    |split; [vm_compute; reflexivity | apply nulfree_forallb; vm_compute; reflexivity]]|]);
    (split; [pfc_zle|]); (split; [pfc_zle|]);
    unfold REFUSE_FORMATS; cbn [In]; auto 20.
Qed.

(** A literal C string in .rodata as printf's pf_bytes. *)
Lemma pfc_lit_at : forall m a l, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length l) + 1 <= 2 ^ 64 ->
  ro_bytes_b rsegs a (pf_bytes (l ++ [0])) = true -> bytes_at rsegs m a (pf_bytes (l ++ [0])).
Proof.
  intros m a l MI H0 H1 H. apply pfc_ro_str; [exact MI | exact H0 | | exact H].
  unfold pf_bytes. rewrite length_map, length_app. cbn [length]. lia.
Qed.

(** * Refusals at the shared sites: refuse_pre from a cut's context *)
Lemma pfc_cstr_of_enc : forall m a s fb (cap : nat), bytes_at rsegs m a fb -> cstr_enc cap s fb -> a mod 8 = 0 ->
  Z.of_nat cap mod 8 = 0 -> cstr_at rsegs m a s.
Proof.
  intros m a s fb cap B (Hl & Hs & Hn & Hf) Ha Hc.
  unfold zs in Hf. rewrite firstn_map in Hf.
  apply map_eq_app in Hf as (l1 & l2 & E12 & H1 & H2).
  apply map_eq_cons in H2 as (z & tl & Ez & Hz & Htl). apply map_eq_nil in Htl. subst tl l2.
  assert (Ez0 : z = ZERO) by (apply bv_eq; rewrite Hz; reflexivity). subst z.
  pose proof (firstn_skipn (S (length s)) fb) as Efs. rewrite E12 in Efs.
  exists l1, (skipn (S (length s)) fb).
  split; [|split; [exact H1|split; [exact Hn|]]].
  - rewrite <- Efs in B. rewrite <- app_assoc in B. exact B.
  - rewrite length_skipn. Z.div_mod_to_equations. lia.
Qed.

(** cur_name as a C string (16 bytes at an 8-aligned frame address). *)
Lemma pfc_nm_cstr : forall m sp nm, pf_nm_at m (sp + PF_NAMEBUF) nm -> sp mod 16 = 0 ->
  cstr_at rsegs m (sp + PF_NAMEBUF) nm /\ (length nm < 16)%nat.
Proof.
  intros m sp nm (f & HB & HE) Hsp. split; [|exact (proj1 (proj2 HE))].
  apply (pfc_cstr_of_enc m _ nm f 16 HB HE); [unfold PF_NAMEBUF; Z.div_mod_to_equations; lia | reflexivity].
Qed.

Lemma pfc_env_al : forall m fc sp lo c v, pf_env m fc sp lo c v -> sp mod 16 = 0.
Proof.
  intros m fc sp lo c v (_ & _ & _ & _ & _ & _ & (_ & _ & Hal & _) & _). unfold PARSE_FILE_FRAME in Hal.
  Z.div_mod_to_equations. lia.
Qed.

(** The refusal record's forbidden ranges (refuse_pre's va_args_ok W). *)
Definition pfc_refW (lo sp c : Z) (rc : rconf) : list ivl :=
  [(lo, sp); (refusal_addr c (length (rc_refusal rc)), refusal_addr c (length (rc_refusal rc)) + RC_REFUSAL_LEN);
   (c + RC_REFUSED, c + RC_REFUSED + 4)].

Lemma pfc_rconf_nref : forall m c rc, rconf_at rsegs m c rc -> (length (rc_refusal rc) <= 8)%nat.
Proof. intros m c rc (bs & _ & (_ & _ & _ & _ & H & _)). exact H. Qed.

(** A string argument in parse_file's frame. *)
Lemma pfc_va_frame : forall m fc sp lo c v rc a s, pf_env m fc sp lo c v -> rconf_at rsegs m c rc ->
  sp <= a -> a + Z.of_nat (length s) + 8 <= sp + PARSE_FILE_FRAME -> (length s <= 65535)%nat -> cstr_at rsegs m a s ->
  va_arg_ok rsegs m (pfc_refW lo sp c rc) (Z_to_bv 64 a) (AS s).
Proof.
  intros m fc sp lo c v rc a s HENV HRC H1 H2 Hl HC.
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & Hap & Lie & _).
  pose proof (pfc_rconf_nref _ _ _ HRC) as Hn.
  unfold va_arg_ok, pfc_refW, PARSE_FILE_FRAME in *. rewrite unsigned_lit by lia.
  split; [lia|]. split; [exact HC|]. split; [exact Hl|].
  unfold apart_all, apart, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED, SEG_C_SIZE in *.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; lia.
Qed.


(** refuse_pre at a shared site of the line loop: c, lineno = ln + 1, the format in .rodata, the arguments. *)
Lemma pfc_refuse_pre : forall m fc sp lo v c t s o ln d n rc cur nm k f fp va args,
  pf_ctx m fc sp lo v c t s o ln d n -> pf_state m sp c rc cur nm k ->
  In f REFUSE_FORMATS -> conv_kinds f = map arg_is_s args ->
  fp <> 0 -> cstrz_at rsegs m fp f -> RO_LO <= fp -> fp + Z.of_nat (length f) + 1 <= sa_ro_end SA ->
  va_args_ok rsegs m (pfc_refW lo sp c rc) va args ->
  refuse_pre m fc sp lo c (ln + 1) fp va rc (ln + 1) f args.
Proof.
  intros m fc sp lo v c t s o ln d n rc cur nm k f fp va args
    (HENV & HT & HS & Ho & Hn & (Lo & Ls & Ld & Lln)) (HRC & Hcur & Hnm & (Hk1 & Hk2)) Hf Hck Hfp HF HR1 HR2 HVA.
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & Hap & Lie & Lsp63).
  pose proof HENV as (Hc0 & Hc16 & _ & Hni & (Hfrm & Htm & Hssp & Hie & Hsp) & _ & (ST & Hdep & Hal & Hrom) & MI & _).
  destruct HT as (_ & _ & Hsl & _). pose proof (pfc_len65535 s Hsl) as Hsl'.
  pose proof (pfc_next_gt s o Ho) as [G1 G2].
  unfold refuse_pre.
  split; [exact Hc0|]. split; [exact Hc16|]. split; [exact HRC|].
  split; [unfold apart, SEG_C_SIZE in *; lia|]. split; [exact Hni|].
  split; [lia|]. split; [lia|]. split; [reflexivity|].
  split; [exact Hf|]. split; [exact Hck|]. split; [exact Hfp|]. split; [exact HF|]. split; [exact HR1|].
  split; [exact HR2|]. split; [exact HVA|].
  split; [split; [exact Hfrm|]; split; [exact Htm|]; split; [exact Hssp|]; split; [exact Hie | lia]|].
  split; [|exact MI].
  split; [|split; [unfold REFUSE_STACK, PRINTF_K; lia|split; [|intros a Ha; apply Hrom; unfold PARSE_FILE_FRAME; lia]]].
  - exact (proj1 (stk_split rsegs m lo sp (sp + PARSE_FILE_FRAME) ST ltac:(unfold PARSE_FILE_FRAME; lia))).
  - unfold PARSE_FILE_FRAME in Hal. Z.div_mod_to_equations. lia.
Qed.

Lemma pfc_refuse_W_sub : forall sp c rc, sub_fp (refuse_W sp c rc) (pfc_W sp c).
Proof.
  intros sp c rc x Hx. unfold pfc_W, refuse_W, RC_PARSE_W, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K,
    PARSE_FILE_FRAME, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED, RC_NREF, RC_N, RC_OVERFLOW,
    RC_READING, RC_GEN in *.
  cbn [outside] in Hx. destruct (length (rc_refusal rc) <? 8)%nat eqn:E; cbn [app outside].
  - apply Nat.ltb_lt in E. lia.
  - lia.
Qed.

(** * printf calls: the stack region below sp that printf may write is [sp - SNPRINTF_K, sp) *)
Lemma pfc_stk_low : forall m lo sp K, stk rsegs m lo sp -> lo <= sp - K -> 0 <= K -> stk rsegs m (sp - K) sp.
Proof. intros m lo sp K ST H HK. exact (proj2 (stk_split rsegs m lo (sp - K) sp ST ltac:(lia))). Qed.

(** Back to [lo, sp) after a call that wrote only [sp - K, sp) of the stack region. *)
Lemma pfc_stk_back : forall W m m' lo sp K, stk rsegs m lo sp -> munch W m m' -> wmono rsegs m m' ->
  stk rsegs m' (sp - K) sp -> lo <= sp - K -> 0 <= K -> (forall x, lo <= x < sp - K -> outside W x) ->
  stk rsegs m' lo sp.
Proof.
  intros W m m' lo sp K ST MU WM ST' H HK HO.
  apply (stk_merge rsegs m' lo (sp - K) sp); [| exact ST' | lia].
  apply (stk_transport rsegs W m m' lo (sp - K)); [exact (proj1 (stk_split rsegs m lo (sp - K) sp ST ltac:(lia))) | exact MU | exact WM |].
  intros x Hx. left. apply HO. exact Hx.
Qed.

(** A destination in the stack region. *)
Lemma pfc_dst_stk : forall m lo hi D n, stk rsegs m lo hi -> lo <= D -> D + n <= hi -> 0 <= n ->
  exists junk, rw_cells rsegs m D [CB (Z.to_nat n) junk].
Proof.
  intros m lo hi D n ST H1 H2 H3.
  destruct (stk_split rsegs m lo D hi ST ltac:(lia)) as [_ ST1].
  destruct (stk_split rsegs m D (D + n) hi ST1 ltac:(lia)) as [ST2 _].
  destruct (stk_bytes rsegs m D (D + n) ST2 ltac:(lia)) as (bs & Hl & HB).
  exists bs. split; [split|].
  - cbn [cells_wf cell_wf]. split; [lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - destruct ST2 as (S0 & S1 & S2). cbn [cells_size csize]. split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (S2 (D + i) ltac:(lia))).
Qed.

Lemma wr_at_sub_pfc : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) Ha Hn Hl. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

(** A destination inside a present, writable block. *)
Lemma pfc_dst_blk : forall m c bs D n, bytes_at rsegs m c bs -> wr_at rsegs m c (Z.of_nat (length bs)) ->
  c <= D -> D + Z.of_nat n <= c + Z.of_nat (length bs) ->
  rw_cells rsegs m D [CB n (fld (Z.to_nat (D - c)) n bs)].
Proof.
  intros m c bs D n HB HW H1 H2.
  assert (LF : length (fld (Z.to_nat (D - c)) n bs) = n) by (apply pfc_len_fld; lia).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LF | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    destruct HB as (B0 & B1 & B). split; [lia|]. split; [rewrite LF; lia|]. intros i Hi. rewrite LF in Hi.
    unfold fld. rewrite pfc_nth_error_firstn by lia. rewrite pfc_nth_error_skipn.
    rewrite <- B by lia. f_equal. f_equal. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply (wr_at_sub_pfc m c (Z.of_nat (length bs)) D (Z.of_nat n) HW); lia.
Qed.

(** * The exit after a refusal *)
(** refuse writes printf's stack below sp and the c block only. *)
Lemma pfc_refuse_W_low : forall m fc sp lo c v rc, pf_env m fc sp lo c v -> rconf_at rsegs m c rc ->
  forall x, ~ outside (refuse_W sp c rc) x -> lo <= x < sp \/ c <= x < c + SEG_C_SIZE.
Proof.
  intros m fc sp lo c v rc HENV HRC x Hx.
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & _).
  pose proof (pfc_rconf_nref _ _ _ HRC) as Hn.
  assert (Dec : (lo <= x < sp \/ c <= x < c + SEG_C_SIZE) \/ ~ (lo <= x < sp \/ c <= x < c + SEG_C_SIZE))
    by (unfold SEG_C_SIZE; lia).
  destruct Dec as [D|D]; [exact D|]. exfalso. apply Hx.
  unfold refuse_W, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED, RC_NREF, REFUSE_STACK, PRINTF_K,
    SEG_C_SIZE in *.
  destruct (length (rc_refusal rc) <? 8)%nat eqn:E; cbn [app outside]; [apply Nat.ltb_lt in E|];
    repeat split; lia.
Qed.

(** After refuse returned: the tail's context at the next line, the state with one refusal more, the measure, and
    the munch inside the function's W. *)
Lemma pfc_after_refuse : forall m m' fc fc' sp lo v c t s o ln d n rc cur nm f args,
  pf_ctx m fc sp lo v c t s o ln d n -> pf_state m sp c rc cur nm (length (skipn o s)) ->
  munch (refuse_W sp c rc) m m' -> wmono rsegs m m' -> stk rsegs m' lo sp -> mem_inv rsegs m' ->
  MemNorm.task_mem rsegs m' -> frm0 fc' -> rconf_at rsegs m' c (refuse rc (ln + 1) f args) ->
  pf_hctx m' fc' sp lo v c t s (pf_next s o) (ln + 1) d /\
  pf_state m' sp c (refuse rc (ln + 1) f args) cur nm (length (skipn (pf_next s o) s)) /\
  (length (skipn (pf_next s o) s) < n)%nat /\ munch (pfc_W sp c) m m'.
Proof.
  intros m m' fc fc' sp lo v c t s o ln d n rc cur nm f args HCTX (HRC & Hcur & Hnm & Hcnt) MU WM ST MI TM FRM HRC'.
  pose proof HCTX as (HENV & _).
  pose proof (pfc_refuse_W_low m fc sp lo c v rc HENV HRC) as LOW.
  destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & _ & Hap & _).
  assert (FW : pfc_fw sp lo c (refuse_W sp c rc)) by (apply pfc_fw_low; exact LOW).
  assert (PR : forall x, pfc_scr sp x -> ~ outside (refuse_W sp c rc) x ->
                 exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx Ho. exfalso. unfold apart, SEG_C_SIZE, pfc_scr, PF_CURSLOT, PF_SAVE in *. destruct (LOW x Ho); lia. }
  pose proof (pfc_ctx_call m m' fc fc' sp lo v c t s o ln d n _ HCTX MU WM FW PR ST MI TM FRM) as HCTX'.
  destruct (pfc_hctx_next m' fc' sp lo v c t s o ln d n HCTX') as (HH & Hlt & Hn).
  split; [exact HH|]. split; [|split; [exact Hn|]].
  - split; [exact HRC'|]. split; [apply pfc_cur_ok_refuse; exact Hcur|].
    split; [| eapply pfc_cnt_refuse; [exact Hcnt | exact Hlt]].
    apply (pfc_nm_call m m' fc sp lo c v nm _ HENV Hnm MU).
    intros x Hx. destruct (pfc_outside_dec (refuse_W sp c rc) x) as [Ho|Ho]; [exact Ho|].
    exfalso. unfold apart, SEG_C_SIZE, PF_SAVE, PF_NAMEBUF in *. destruct (LOW x Ho); lia.
  - exact (munch_weaken _ _ m m' (pfc_refuse_W_sub sp c rc) MU).
Qed.

(** * printf calls of the pieces *)
(** A word of a saved_at list (spill slots, saved registers) as a load. *)
Lemma pfc_saved_at : forall m a ws i w, saved_at rsegs m a ws -> nth_error ws i = Some w ->
  bytes_at rsegs m (a + 8 * Z.of_nat i) (le8 w).
Proof.
  intros m a ws. revert a. induction ws as [|w0 ws IH]; intros a i w H Hi; [destruct i; discriminate|].
  unfold saved_at in H. cbn [map concat] in H. apply bytes_at_app in H as [H1 H2]. rewrite length_le8 in H2.
  destruct i as [|i]; cbn in Hi.
  - injection Hi as <-. replace (a + 8 * Z.of_nat 0) with a by lia. exact H1.
  - replace (a + 8 * Z.of_nat (S i)) with (a + Z.of_nat 8 + 8 * Z.of_nat i) by lia. apply IH; [exact H2 | exact Hi].
Qed.

Lemma pfc_saved_ld : forall m a ws i w, saved_at rsegs m a ws -> nth_error ws i = Some w ->
  ov_read_bytes rsegs m (wa (a + 8 * Z.of_nat i)) 8 = Some (le8 w).
Proof.
  intros m a ws i w H Hi. pose proof (pfc_saved_at m a ws i w H Hi) as B.
  pose proof (bytes_at_ov_read rsegs m _ _ 0 8 B ltac:(rewrite length_le8; lia)) as R.
  replace (a + 8 * Z.of_nat i + Z.of_nat 0) with (a + 8 * Z.of_nat i) in R by lia.
  rewrite R. f_equal.
Qed.

(** The spill slot sp + 0x50 (&c->reading) as a load. *)
Lemma pfc_ld_reading : forall m sp c, pf_spill m sp c ->
  ov_read_bytes rsegs m (wa (sp + 0x50)) 8 = Some (le8 (Z_to_bv 64 (c + RC_READING))).
Proof.
  intros m sp c H. replace (sp + 0x50) with (sp + 0x10 + 8 * Z.of_nat 8) by lia.
  apply (pfc_saved_ld m (sp + 0x10) _ 8 _ (proj1 H)). reflexivity.
Qed.

(** c->reading as a C string. *)
Lemma pfc_reading_cstr : forall m c rc, rconf_at rsegs m c rc -> c mod 16 = 0 ->
  cstr_at rsegs m (c + RC_READING) (rc_reading rc).
Proof.
  intros m c rc (bs & HB & HE) Hc. destruct HE as (HL & _ & _ & _ & _ & _ & _ & _ & _ & HRD & _).
  unfold SEG_C_SIZE in HL. unfold fldz, RC_READING in *.
  apply (pfc_cstr_of_enc m (c + 16512) _ (fld (Z.to_nat 16512) (Z.to_nat 96) bs) 96);
    [| exact HRD | Z.div_mod_to_equations; lia | reflexivity].
  unfold fld. rewrite <- (firstn_skipn (Z.to_nat 16512) bs) in HB. apply bytes_at_app in HB as [_ HB].
  rewrite length_firstn in HB. replace (Nat.min (Z.to_nat 16512) (length bs)) with (Z.to_nat 16512) in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat 96) (skipn (Z.to_nat 16512) bs)) in HB. apply bytes_at_app in HB as [HB _].
  replace (c + Z.of_nat (Z.to_nat 16512)) with (c + 16512) in HB by lia. exact HB.
Qed.

(** A C string as printf's %s argument (pf_arg_ok), taking exactly the slack the word reads need. *)
Lemma pfc_arg_cstr : forall m S lo D n a s, cstr_at rsegs m a s -> 0 < a ->
  (a + cstr_span a s <= lo \/ S <= a) -> (a + cstr_span a s <= D \/ D + n <= a) ->
  pf_arg_ok m S lo D n (Z_to_bv 64 a) (APtr s).
Proof.
  intros m S lo D n a s (bs & sl & B & Hz & Hn & Hsl) Ha HS HD.
  pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite length_app in BB. cbn [length] in BB.
  assert (Hlen : length bs = length s) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  set (k := (- (a + Z.of_nat (length s) + 1)) mod 8) in *.
  assert (Hk : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
  unfold pf_arg_ok. rewrite unsigned_lit by lia.
  split.
  - rewrite <- Hz. unfold zs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & Hb).
    pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb. split; [|lia].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia]. exfalso. apply Hn. rewrite <- Hz. unfold zs.
    apply in_map_iff. exists b. split; [exact E | exact Hb].
  - exists (firstn (Z.to_nat k) sl).
    assert (Ebs : pf_bytes (s ++ [0]) = bs ++ [ZERO]).
    { unfold pf_bytes. rewrite map_app. rewrite <- Hz. unfold zs. rewrite map_map.
      rewrite map_ext with (g := fun b => b)
        by (intros b; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
      rewrite map_id. reflexivity. }
    rewrite Ebs. unfold cstr_span in *. fold k in HS, HD.
    split; [| split; [rewrite length_firstn; lia | split; [lia |]]].
    + rewrite <- (firstn_skipn (Z.to_nat k) sl) in B.
      replace (bs ++ ZERO :: firstn (Z.to_nat k) sl ++ skipn (Z.to_nat k) sl)
        with ((bs ++ [ZERO] ++ firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl) in B
        by (rewrite <- !app_assoc; reflexivity).
      apply bytes_at_app in B. rewrite <- app_assoc. exact (proj1 B).
    + rewrite length_firstn. replace (Z.of_nat (Nat.min (Z.to_nat k) (length sl))) with k by lia. lia.
Qed.


(** The "%s" format of the provenance and cur_name sites (0x104e0). *)
Lemma pfc_fmt_s : forall m, mem_inv rsegs m -> bytes_at rsegs m PF_STR_S (pf_bytes ([37; 115] ++ [0])).
Proof. intros m MI. apply pfc_lit_at; [exact MI | unfold PF_STR_S; lia | cbn; unfold PF_STR_S; lia | vm_compute; reflexivity]. Qed.

(** What printf asks of the machine, at a cut's sp, with printf's stack [sp - SNPRINTF_K, sp). *)
Lemma pfc_printf_at : forall m fc sp lo c v, pf_env m fc sp lo c v ->
  stk rsegs m (sp - SNPRINTF_K) sp /\ IMG_END <= sp - SNPRINTF_K /\ sp < 2 ^ 63 /\ frm0 fc /\ mem_inv rsegs m /\
  MemNorm.task_mem rsegs m /\ bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\
  (exists canary, bytes_at rsegs m GUARD (le8 canary)).
Proof.
  intros m fc sp lo c v HENV. destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & _ & Lie & Lsp63).
  destruct HENV as (_ & _ & _ & _ & (Hfrm & Htm & (Hg1 & Hg2) & _ & _) & _ & (ST & _) & MI & _).
  split; [apply (pfc_stk_low m lo sp SNPRINTF_K); [exact (proj1 (stk_split rsegs m lo sp (sp + PARSE_FILE_FRAME) ST ltac:(unfold PARSE_FILE_FRAME; lia))) | unfold SNPRINTF_K; lia | unfold SNPRINTF_K; lia]|].
  split; [unfold IMG_END, SNPRINTF_K; lia|]. split; [lia|]. split; [exact Hfrm|]. split; [exact MI|].
  split; [exact Htm|]. split; [exact Hg1 | exact Hg2].
Qed.

(** A printf destination above the image's last page (every frame byte of a cut: sp >= lo + 6032 > 0x55000). *)
Lemma pfc_img_free_hi : forall D n, 0x55000 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs. pose proof pfc_res_eq as E.
  assert (Hin : In (bv_unsigned (fst s), bv_unsigned (snd s)) PFC_RES)
    by (rewrite <- E; apply in_map_iff; exists s; split; [reflexivity | exact Hs]).
  unfold PFC_RES in Hin. destruct Hin as [Q|[Q|[Q|[Q|[]]]]]; injection Q as Q1 Q2; rewrite <- Q1, <- Q2; lia.
Qed.

(** * Frame stores *)
(** Known frame bytes inside the stack region as a printf destination (the old bytes are the junk). *)
Lemma pfc_rw_of_stk : forall m lo hi D f, bytes_at rsegs m D f -> stk rsegs m lo hi -> lo <= D ->
  D + Z.of_nat (length f) <= hi -> rw_cells rsegs m D [CB (length f) f].
Proof.
  intros m lo hi D f HB (S0 & S1 & S2) H1 H2. pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (S2 (D + i) ltac:(lia))).
Qed.

(** A byte of a known block is present. *)
Lemma pfc_bytes_mrd : forall m a bs x, bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a bs x (H0 & H1 & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E.
  - exists b. rewrite <- E. rewrite <- (H (Z.to_nat (x - a))) by lia. f_equal. f_equal. lia.
  - apply nth_error_None in E. lia.
Qed.

(** MemNorm's task_mem survives a write of bytes that were present (the refuse walk's task_mem_munch). *)
Lemma pfc_task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd rsegs m x <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU P x b Hx.
  destruct (pfc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (m x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (MemNorm.seg_rom_unmapped rsegs x Hf).
Qed.

(** The frame [sp, sp + 0x420) of a cut is writable (stack_ok's stk). *)
Lemma pfc_frame_wr : forall m fc sp lo c v, pf_env m fc sp lo c v -> wr_at rsegs m sp PARSE_FILE_FRAME.
Proof.
  intros m fc sp lo c v HENV. destruct (pfc_env_lo _ _ _ _ _ _ HENV) as (Lo0 & Lsp & Lhi & _).
  destruct HENV as (_ & _ & _ & _ & _ & _ & ((S0 & S1 & S2) & _) & _).
  split; [lia|]. split; [unfold PARSE_FILE_FRAME; lia|]. intros i Hi.
  exact (proj1 (S2 (sp + i) ltac:(unfold PARSE_FILE_FRAME in *; lia))).
Qed.

