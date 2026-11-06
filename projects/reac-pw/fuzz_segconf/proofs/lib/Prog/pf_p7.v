(** reac-pw/fuzz_segconf, plain build (image 3776ca44d75c): piece P7 of reac_segconf_parse_file, the model key
    (lib/Prog/reac_segconf_parse_file_pieces_c.v, family F3). MODEL (0x150bc) reaches PROVM
    (0x154ac) when the folded value is a box token, and S9 (0x14f7c) otherwise.

    Code (the plain binary):
      0x150bc lbu a0,0(s7); beqz a0 -> 0x152b8; a2 = 0; a1 = s7 + 1
      0x150cc .. 0x15100  the fold into low = sp + 0x140 (cap 24): low[li] = lower(val[li]), li++ while
                          val[li] <> 0 and li < 23
      0x152b8 .. 0x152c8  low[li] = 0; `jal reac_box_catalogue_by_token` with a0 = low
      0x152cc beqz a0 -> 0x1530c (miss)
      0x152d0 .. 0x15300  hit: snprintf(cur + 0x24, 24, "%s", low); cur->model_set = 1; a0 = cur + 0x40, a1 = 96,
                          a2 = "%s"; `j` PROVM
      0x1530c .. 0x153a8  miss: ntok = 0; `jal reac_box_catalogue(&ntok)`; the join loop at 0x15330 over the 11
                          rows, each `snprintf(known + kn, 240 - kn, "%s%s", ti ? "|" : "", tab[ti].token)` with
                          known = sp + 0x50; `jal refuse(c, lineno, F_badmodel, cur_name, val, known)`; `j` S9

    The spine step is SegModel.r_key's model branch (pf_p7_lemmas.p7_r_key); the shared helpers are
    lib/Prog/pfC_facts.v and lib/Prog/pf_p7_lemmas.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Arr Image Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import printf_facts_c snprintf_c refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_box_catalogue_by_token_c reac_box_catalogue_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import fuzz_catalogue_row_c fuzz_catalogue_row.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfC_facts pf_p7_lemmas.
Import ListNotations.
Open Scope Z_scope.

(** A block at or above the last reserved page of the image is image-free (printf's pf_img_free). *)
Lemma p7_noimg_above : forall a k, 0x54000 <= a -> blk_noimg rsegs a k.
Proof.
  intros a k H i Hi sg Hs.
  assert (Hin : In (bv_unsigned (fst sg), bv_unsigned (snd sg)) PFC_RES).
  { rewrite <- pfc_res_eq. apply in_map_iff. exists sg. split; [reflexivity | exact Hs]. }
  unfold PFC_RES in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as E1 E2; rewrite <- E1, <- E2; lia|]).
  destruct Hin.
Qed.

(** The stack region's bytes are writable. *)
Lemma p7_wr_of_stk : forall m lo hi a k, stk rsegs m lo hi -> lo <= a -> 0 <= k -> a + k <= hi ->
  wr_at rsegs m a k.
Proof.
  intros m lo0 hi a k (H0 & H1 & H) Ha Hk Hle. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

(** The 65535 bound as a nat: the literal is a num_uint application, which lia does not read. *)
Lemma p7_len65535 : forall (l : list Z), Z.of_nat (length l) <= 65535 -> (length l <= 65535)%nat.
Proof. intros l H. apply Nat2Z.inj_le. exact H. Qed.

Section P7.

Variables (sp gp tp s0 s1 s2 s3 s4 s6 s10 s11 : word).
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variables (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z).
Variables (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (n : nat).

Hypothesis HSN : snprintf_contract.
Hypothesis HRF : refuse_contract.
Hypothesis HBT : reac_box_catalogue_by_token_contract.
Hypothesis HBC : reac_box_catalogue_contract.
Hypothesis HPROVM : H_PROVM n.
Hypothesis HS9c : H_S9 n.
Hypothesis HCTX : pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n.
Hypothesis HSTATE : pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)).
Hypothesis HREGS : pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1).
Hypothesis HS6 : s6 = Z_to_bv 64 (pf_cur_ptr c (Some gi)).
Hypothesis HVPat : cstr_at rsegs m vp val.
Hypothesis HVPin : pf_inb (bv_unsigned sp + PF_BUF) vp val.
Hypothesis HKEY : r_key rc (Some gi) nm (ln + 1) (pf_tline s o) =
  match by_token (r_low val 0 24) with
  | None => (refuse rc (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm)
  | Some _ => (r_upd rc gi (rs_with_model (snprintf_s 24 F_s [AS (r_low val 0 24)])
                                          (snprintf_s 96 F_s [AS (rc_reading rc)])), Some gi, nm)
  end.

(** The post of every state of this piece. *)
Definition Post : machine_state -> Prop :=
  pf_fin v sp gp tp F m lo c
    (r_lines (r_key rc (Some gi) nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))).

(** The bytes the piece may write: printf's and refuse's stack below sp, the frame's scratch
    [sp + 0x48, sp + 0x158) (ntok, known, low), and the c block ranges of RC_PARSE_W. *)
Definition WS : list ivl :=
  [(bv_unsigned sp - 6032, bv_unsigned sp); (bv_unsigned sp + 0x48, bv_unsigned sp + 0x158)].
Definition WP : list ivl :=
  [(bv_unsigned sp - 6032, bv_unsigned sp); (bv_unsigned sp + 0x48, bv_unsigned sp + 0x158);
   (c, c + RC_N + 4); (c + RC_REFUSAL, c + RC_OVERFLOW + 4)].

(** The folded value and its length. *)
Definition LW : list Z := r_low val 0 24.
Definition LI : nat := length LW.

(** ** Facts of the entry context *)

Lemma p7_env : pf_env m fc (bv_unsigned sp) lo c v.
Proof. exact (proj1 HCTX). Qed.

Lemma p7_lo :
  0 <= lo /\ lo + 6032 <= bv_unsigned sp /\ bv_unsigned sp + 0x3d0 <= 2 ^ 64 /\
  apart c SEG_C_SIZE lo (bv_unsigned sp + 0x3d0) /\ 0x536e8 <= lo /\ bv_unsigned sp + 0x3d0 < 2 ^ 63.
Proof. exact (pfc_env_lo m fc (bv_unsigned sp) lo c v p7_env). Qed.

Lemma p7_sp16 : bv_unsigned sp mod 16 = 0.
Proof. exact (pfc_env_al m fc (bv_unsigned sp) lo c v p7_env). Qed.

Lemma p7_stk : stk rsegs m lo (bv_unsigned sp + PARSE_FILE_FRAME).
Proof. destruct p7_env as (_ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.

Lemma p7_rom : forall a, lo <= a < bv_unsigned sp + PARSE_FILE_FRAME -> seg_rom rsegs (wa a) = None.
Proof. destruct p7_env as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & H) & _). exact H. Qed.

Lemma p7_mi : mem_inv rsegs m.
Proof. destruct p7_env as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma p7_tm : MemNorm.task_mem rsegs m.
Proof. destruct p7_env as (_ & _ & _ & _ & (_ & H & _) & _). exact H. Qed.

Lemma p7_frm : frm0 fc.
Proof. destruct p7_env as (_ & _ & _ & _ & (H & _) & _). exact H. Qed.

Lemma p7_noimg_c : blk_noimg rsegs c SEG_C_SIZE.
Proof. destruct p7_env as (_ & _ & _ & H & _). exact H. Qed.

Lemma p7_rconf : rconf_at rsegs m c rc.
Proof. exact (proj1 HSTATE). Qed.

Lemma p7_gi : (gi < length (rc_seg rc))%nat.
Proof. exact (proj1 (proj2 HSTATE)). Qed.

Lemma p7_val_nulfree : ~ In 0 val.
Proof. destruct HVPat as (bs & sl & _ & _ & H & _). exact H. Qed.

Lemma p7_LI : LI = Nat.min 23 (length val).
Proof. unfold LI, LW. apply p7_low_len. exact p7_val_nulfree. Qed.

Lemma p7_vpin : bv_unsigned sp + PF_BUF <= vp /\ vp + Z.of_nat (length val) < bv_unsigned sp + PF_BUF + 512.
Proof. exact HVPin. Qed.

(** The low buffer's 24 bytes at the entry memory. *)
Lemma p7_lowbytes : exists LB, bytes_at rsegs m (bv_unsigned sp + 0x140) LB /\ length LB = 24%nat.
Proof.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  destruct (stk_split rsegs m lo (bv_unsigned sp + 0x140) (bv_unsigned sp + PARSE_FILE_FRAME) p7_stk
              ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ ST2].
  destruct (stk_split rsegs m (bv_unsigned sp + 0x140) (bv_unsigned sp + 0x158)
              (bv_unsigned sp + PARSE_FILE_FRAME) ST2 ltac:(unfold PARSE_FILE_FRAME; lia)) as [ST3 _].
  destruct (stk_bytes rsegs m (bv_unsigned sp + 0x140) (bv_unsigned sp + 0x158) ST3 ltac:(lia)) as (LB & HL & HB).
  exists LB. split; [exact HB|]. rewrite HL.
  replace (bv_unsigned sp + 0x158 - (bv_unsigned sp + 0x140)) with 24 by lia. reflexivity.
Qed.

(** The value's bytes at vp: val's bytes and its NUL. *)
Lemma p7_vb : exists VB : list byte,
  bytes_at rsegs m vp VB /\ length VB = S (length val) /\
  (forall i (b : byte), nth_error VB i = Some b -> (i < length val)%nat -> bv_unsigned b = nth i val 0) /\
  (forall i, (i <= length val)%nat -> exists b : byte, nth_error VB i = Some b) /\
  (forall i (b : byte), nth_error VB i = Some b -> (bv_unsigned b = 0 <-> i = length val)).
Proof.
  destruct HVPat as (bs & sl & HB & Hz & Hn & Hsl).
  assert (Hlen : length bs = length val)
    by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  exists (bs ++ [ZERO]).
  assert (HB' : bytes_at rsegs m vp (bs ++ [ZERO])).
  { replace (bs ++ ZERO :: sl) with ((bs ++ [ZERO]) ++ sl) in HB by (rewrite <- app_assoc; reflexivity).
    exact (proj1 (proj1 (bytes_at_app rsegs m vp (bs ++ [ZERO]) sl) HB)). }
  split; [exact HB'|].
  split; [rewrite length_app, Hlen; cbn [length]; lia|].
  assert (Hval : forall i, (i < length val)%nat -> nth i val 0 = bv_unsigned (nth i bs ZERO)).
  { intros i Hi. rewrite <- Hz. unfold zs. rewrite (nth_indep (map bv_unsigned bs) 0 (bv_unsigned ZERO))
      by (rewrite length_map; lia).
    apply map_nth. }
  split.
  { intros i b HN Hi. rewrite nth_error_app1 in HN by lia.
    rewrite (p7_nth_error_some bs ZERO i ltac:(lia)) in HN. injection HN as <-.
    symmetry. apply Hval. exact Hi. }
  split.
  { intros i Hi. exists (nth i (bs ++ [ZERO]) ZERO). apply (p7_nth_error_some (bs ++ [ZERO]) ZERO i).
    rewrite length_app, Hlen. cbn [length]. lia. }
  intros i b HN.
  assert (Hi : (i < length (bs ++ [ZERO]))%nat)
    by (apply (proj1 (nth_error_Some (bs ++ [ZERO]) i)); rewrite HN; discriminate).
  rewrite length_app, Hlen in Hi. cbn [length] in Hi.
  destruct (Nat.eq_dec i (length val)) as [->|Hne].
  - rewrite nth_error_app2 in HN by lia. rewrite Hlen, Nat.sub_diag in HN. cbn [nth_error] in HN.
    injection HN as <-. split; [reflexivity | reflexivity].
  - assert (Hlt : (i < length val)%nat) by lia.
    rewrite nth_error_app1 in HN by lia.
    rewrite (p7_nth_error_some bs ZERO i ltac:(lia)) in HN. injection HN as <-.
    split; [|lia]. intros Hz0. exfalso. apply p7_val_nulfree.
    rewrite <- (Hval i Hlt) in Hz0. rewrite <- Hz0. apply nth_In. lia.
Qed.

(** ** The walk *)
(** The task memory over a munch whose window was present (the refuse walk's task_mem_munch). *)
Lemma p7_task_munch : forall W (m1 m2 : word -> option byte),
  MemNorm.task_mem rsegs m1 -> munch W m1 m2 ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd rsegs m1 x <> None) -> MemNorm.task_mem rsegs m2.
Proof.
  intros W m1 m2 T MU P x b Hx.
  destruct (pfc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (m1 x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (MemNorm.seg_rom_unmapped rsegs x Hf).
Qed.


Lemma p7_fw_WS : pfc_fw (bv_unsigned sp) lo c WS.
Proof.
  destruct p7_lo as (Hlo0 & Hlo1 & _).
  intros x Hx. unfold WS in Hx. cbn [outside] in Hx. unfold PF_SAVE.
  destruct (Z_le_dec (bv_unsigned sp - 6032) x) as [A1|A1];
    destruct (Z_lt_dec x (bv_unsigned sp)) as [A2|A2];
    destruct (Z_le_dec (bv_unsigned sp + 0x48) x) as [A3|A3];
    destruct (Z_lt_dec x (bv_unsigned sp + 0x158)) as [A4|A4];
    try (exfalso; apply Hx; split; [lia | split; [lia | exact I]]); lia.
Qed.

Lemma p7_cat : forall m', munch WS m m' -> cat_img rsegs m' (sa_catalogue SA).
Proof.
  intros m' MU a Ha.
  destruct p7_env as (_ & _ & _ & Hni & _ & Hcat & _).
  destruct p7_lo as (Hlo0 & Hlo1 & _ & _ & Hie & _).
  rewrite <- (Hcat a Ha). unfold mrd. rewrite (MU (wa a)); [reflexivity|].
  unfold CAT_BYTES, CAT_ROW, CAT_N in Ha. cbn [sa_catalogue SA SEG_PLAIN] in Ha.
  rewrite wa_unsigned by lia.
  apply (pfc_img_out (bv_unsigned sp) lo c WS a 0x20000 0x2000 p7_fw_WS Hni ltac:(lia));
    [cbn; tauto | lia | lia].
Qed.

Lemma p7_fw_WP : pfc_fw (bv_unsigned sp) lo c WP.
Proof.
  intros x Hx.
  destruct (pfc_outside_dec WS x) as [O|O]; [|exact (p7_fw_WS x O)].
  right. left. unfold WS in O. cbn [outside] in O. unfold WP in Hx. cbn [outside] in Hx.
  unfold SEG_C_SIZE, RC_N, RC_REFUSAL, RC_OVERFLOW in *.
  destruct (Z_le_dec c x) as [B1|B1]; destruct (Z_lt_dec x (c + 16616)) as [B2|B2]; try lia.
  all: exfalso; apply Hx; repeat split; try exact I; lia.
Qed.

Lemma p7_subW : sub_fp WP (pfc_W (bv_unsigned sp) c).
Proof.
  intros x Hx. unfold pfc_W, RC_PARSE_W, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME,
    RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN in Hx. cbn [outside] in Hx.
  unfold WP, RC_N, RC_REFUSAL, RC_OVERFLOW. cbn [outside].
  repeat split; try exact I; lia.
Qed.

(** The mid-line context and the reader's state at any memory this piece has reached. *)
Lemma p7_ctx_at : forall (m' : word -> option byte) (fc' : bv 32) (W : list ivl),
  pfc_fw (bv_unsigned sp) lo c W ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  stk rsegs m' lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc' ->
  pf_ctx m' fc' (bv_unsigned sp) lo v c t s o ln d n.
Proof.
  intros m' fc' W FW MU WM MI' TM' ST' FR'.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  apply (pfc_ctx_call m m' fc fc' (bv_unsigned sp) lo v c t s o ln d n W HCTX MU WM FW).
  - intros x Hx Ho. destruct ST' as (_ & _ & STa).
    destruct (STa x ltac:(unfold PF_SAVE, PARSE_FILE_FRAME in *; lia)) as [_ H]. exact H.
  - exact (proj1 (stk_split rsegs m' lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST'
                    ltac:(unfold PARSE_FILE_FRAME; lia))).
  - exact MI'.
  - exact TM'.
  - exact FR'.
Qed.

Lemma p7_state_at : forall (m' : word -> option byte), munch WS m m' ->
  pf_state m' (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)).
Proof.
  intros m' MU. destruct HSTATE as (HRC & HCUR & HNM & HCNT).
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  split; [|split; [exact HCUR | split; [|exact HCNT]]].
  - apply (pfc_rconf_munch WS m m' c rc HRC MU).
    intros x Hx. unfold WS. cbn [outside].
    unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap. unfold SEG_C_SIZE in Hx.
    destruct Hap as [Hc|Hc]; (split; [lia | split; [lia | exact I]]).
  - apply (pfc_nm_call m m' fc (bv_unsigned sp) lo c v nm WS p7_env HNM MU).
    intros x Hx. unfold WS. cbn [outside]. unfold PF_NAMEBUF, PF_SAVE in Hx.
    split; [lia | split; [lia | exact I]].
Qed.

(** ** The miss path 0x1530c .. 0x15384: ntok, the catalogue, the join loop *)

(** A register the code set: equal to the value a cut names. *)
Ltac p7m_eq := first [ reflexivity | f_equal; lia | rewrite ?unsigned_lit by lia; f_equal; lia
                     | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].

(** The exit 0x15388 (refuse with the known list, then S9) as the loop meets it: [p7_refuse_exit] without its
    by_token premise. *)
Definition p7m_EXIT : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 : word)
         (m4 : word -> option byte) (fc4 : bv 32) (F4 : bvmap 5 word),
  munch WS m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 -> MemNorm.task_mem rsegs m4 ->
  stk rsegs m4 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc4 ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F4 r = reg_get F r) ->
  cstr_at rsegs m4 (bv_unsigned sp + 0x50) known ->
  s7 = Z_to_bv 64 vp ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F4 (Z_to_bv 64 0x15388) fc4 None m4 (seg_rom rsegs)).

(** The separator's .rodata address: "" (0x1038e) before the first token, "|" (0x105f0) before the others. *)
Definition p7m_sepp (ti : nat) : Z := if (ti =? 0)%nat then 0x1038e else 0x105f0.

(** A .rodata C string, its NUL and the slack to the next 8-byte boundary, checked on the image. *)
Definition p7m_slack (a : Z) (l : list Z) : list byte :=
  match image_bytes rsegs (a + Z.of_nat (length l) + 1)
          (Z.to_nat ((- (a + Z.of_nat (length l) + 1)) mod 8)) with
  | Some sl => sl
  | None => []
  end.

Definition p7m_rochk (a : Z) (l : list Z) : bool :=
  ro_bytes_b rsegs a (pf_bytes l ++ ZERO :: p7m_slack a l) &&
  ((- (a + Z.of_nat (length l) + 1)) mod 8 <=? Z.of_nat (length (p7m_slack a l))) &&
  forallb (fun x => (0 <? x) && (x <? 256)) l &&
  (0 <? a) && (a + Z.of_nat (length l) + 1 + Z.of_nat (length (p7m_slack a l)) <=? 0x20000).

Lemma p7m_ro_cstr : forall (mm : word -> option byte) a l, mem_inv rsegs mm -> p7m_rochk a l = true ->
  cstr_at rsegs mm a l /\ 0 < a /\ a + cstr_span a l <= 0x20000.
Proof.
  intros mm a l MI H. unfold p7m_rochk in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.ltb_lt in H4. apply Z.leb_le in H5.
  rewrite forallb_forall in H3.
  assert (HB : forall x, In x l -> 0 < x < 256).
  { intros x Hx. specialize (H3 x Hx). apply andb_prop in H3 as [Q1 Q2].
    apply Z.ltb_lt in Q1. apply Z.ltb_lt in Q2. lia. }
  assert (Hlen : length (pf_bytes l) = length l) by (unfold pf_bytes; apply length_map).
  split; [|split; [lia | unfold cstr_span; lia]].
  exists (pf_bytes l), (p7m_slack a l). split; [|split; [|split]].
  - apply (pfc_ro_str mm a _ MI); [lia | rewrite length_app, Hlen; cbn [length]; lia | exact H1].
  - change (zs (zb l) = l). apply pfc_zs_zb. apply Forall_forall. intros x Hx.
    specialize (HB x Hx). unfold pfc_zbyte. lia.
  - intros Hin. specialize (HB 0 Hin). lia.
  - exact H2.
Qed.

(** The two %s arguments of pass ti: the separator and token ti, .rodata C strings below printf's stack. *)
Lemma p7m_args_ro : forall (mm : word -> option byte) ti, mem_inv rsegs mm -> (ti <= 10)%nat ->
  (cstr_at rsegs mm (p7m_sepp ti) (p7_sep ti) /\ 0 < p7m_sepp ti /\
   p7m_sepp ti + cstr_span (p7m_sepp ti) (p7_sep ti) <= 0x20000) /\
  (cstr_at rsegs mm (tok_ptr ti) (p7_tok ti) /\ 0 < tok_ptr ti /\
   tok_ptr ti + cstr_span (tok_ptr ti) (p7_tok ti) <= 0x20000).
Proof.
  intros mm ti MI H. split; apply p7m_ro_cstr; try exact MI.
  - unfold p7m_sepp, p7_sep. destruct (ti =? 0)%nat; vm_compute; reflexivity.
  - do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.

(** An 8-byte word of a known block as a load. *)
Lemma p7m_ld8 : forall (mm : word -> option byte) a w, bytes_at rsegs mm a (le8 w) ->
  ov_read_bytes rsegs mm (wa a) 8 = Some (le8 w).
Proof.
  intros mm a w B.
  pose proof (bytes_at_ov_read rsegs mm a (le8 w) 0 8 B ltac:(rewrite length_le8; lia)) as R.
  replace (a + Z.of_nat 0) with a in R by lia. rewrite R. f_equal.
Qed.

(** The stack over a call whose writes inside it are all present afterwards. *)
Lemma p7m_stk_tr : forall W (m1 m2 : word -> option byte) a0 a1, stk rsegs m1 a0 a1 -> munch W m1 m2 ->
  wmono rsegs m1 m2 -> (forall x, a0 <= x < a1 -> outside W x \/ exists b, mrd rsegs m2 (wa x) = Some b) ->
  stk rsegs m2 a0 a1.
Proof.
  intros W m1 m2 a0 a1 (H1 & H2 & H) MU WM HC. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (HC a Ha) as [Ho|Hb']; [|exact Hb'].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(** Row ti's token pointer, read from the table (pin_spec.tok_ptr ti; fuzz_catalogue_row.row_img). *)
Lemma p7m_row_ld : forall (mm : word -> option byte) ti, munch WS m mm -> (ti < 11)%nat ->
  ov_read_bytes rsegs mm (wa (0x20ad0 + 296 * Z.of_nat ti)) 8 = Some (le8 (Z_to_bv 64 (tok_ptr ti))).
Proof.
  intros mm ti MU Hti. apply p7m_ld8.
  pose proof (row_img ti Hti) as E. unfold FUZZ_CATALOGUE in E.
  apply (fcr_bytes_img rsegs mm _ 8 _ E); [lia | lia |].
  intros a Ha. apply (p7_cat mm MU). cbn [sa_catalogue SA SEG_PLAIN]. unfold CAT_BYTES. lia.
Qed.

(** known with its NUL at sp + 0x50 is a C string (its 2 slack bytes are frame bytes). *)
Lemma p7m_known_cstr : forall (mk : word -> option byte),
  stk rsegs mk lo (bv_unsigned sp + PARSE_FILE_FRAME) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x50) (pf_bytes (known ++ [0])) ->
  cstr_at rsegs mk (bv_unsigned sp + 0x50) known.
Proof.
  intros mk ST HBK.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof p7_sp16 as HSP16.
  assert (EK : length known = 77%nat) by exact p7_known_len.
  destruct (stk_split rsegs mk lo (bv_unsigned sp + 158) (bv_unsigned sp + PARSE_FILE_FRAME) ST
              ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ STa].
  destruct (stk_split rsegs mk (bv_unsigned sp + 158) (bv_unsigned sp + 160) (bv_unsigned sp + PARSE_FILE_FRAME)
              STa ltac:(unfold PARSE_FILE_FRAME; lia)) as [STb _].
  destruct (stk_bytes rsegs mk _ _ STb ltac:(lia)) as (sl & Hsl & HSL).
  exists (pf_bytes known), sl. split; [|split; [|split]].
  - unfold pf_bytes in HBK |- *. rewrite map_app in HBK. cbn [map] in HBK.
    replace (map (Z_to_bv 8) known ++ ZERO :: sl) with ((map (Z_to_bv 8) known ++ [Z_to_bv 8 0]) ++ sl)
      by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (bytes_at_app rsegs mk _ _ _)). split; [exact HBK|].
    assert (EA : bv_unsigned sp + 80 + Z.of_nat (length (map (Z_to_bv 8) known ++ [Z_to_bv 8 0]))
                 = bv_unsigned sp + 158) by (rewrite length_app, length_map, EK; cbn [length]; lia).
    rewrite EA. exact HSL.
  - change (zs (zb known) = known). apply pfc_zs_zb.
    pose proof (p7_J_byte 11 ltac:(lia)) as HJB. rewrite p7_J_11 in HJB. exact HJB.
  - exact known_nulfree.
  - rewrite EK, Hsl. Z.div_mod_to_equations. lia.
Qed.

(** The loop head 0x15330 after ti of the 11 tokens: known[0 .. kn) holds their join, s5 = ti + 1,
    s8 = &tab[ti], s9 = kn, a2 = 240, ntok = 11 at sp + 0x48. *)
Definition p7m_LH (ti : nat) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 : word)
         (mk : word -> option byte) (fck : bv 32) (Fk : bvmap 5 word),
  munch WS m mk -> wmono rsegs m mk -> mem_inv rsegs mk -> MemNorm.task_mem rsegs mk ->
  stk rsegs mk lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fck ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get Fk r = reg_get F r) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x48) (le8 (Z_to_bv 64 11)) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x50) (pf_bytes (p7_J ti)) ->
  s7 = Z_to_bv 64 vp -> a2 = Z_to_bv 64 240 -> s5 = Z_to_bv 64 (Z.of_nat ti + 1) ->
  s8 = Z_to_bv 64 (0x20ad0 + 296 * Z.of_nat ti) -> s9 = Z_to_bv 64 (p7_kn ti) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fk (Z_to_bv 64 0x15330) fck None mk (seg_rom rsegs)).

(** 0x15368, back from pass ti's snprintf (a0 = its return value): the exit test, kn += a0, the next row. *)
Lemma p7m_after : p7m_EXIT -> forall ti, (ti <= 10)%nat -> ((ti < 10)%nat -> p7m_LH (S ti)) ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 : word)
         (mk : word -> option byte) (fck : bv 32) (Fk : bvmap 5 word),
  munch WS m mk -> wmono rsegs m mk -> mem_inv rsegs mk -> MemNorm.task_mem rsegs mk ->
  stk rsegs mk lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fck ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get Fk r = reg_get F r) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x48) (le8 (Z_to_bv 64 11)) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x50) (pf_bytes (p7_J (S ti) ++ [0])) ->
  s7 = Z_to_bv 64 vp -> s5 = Z_to_bv 64 (Z.of_nat ti + 1) ->
  s8 = Z_to_bv 64 (0x20ad0 + 296 * Z.of_nat ti) -> s9 = Z_to_bv 64 (p7_kn ti) ->
  a0 = Z_to_bv 64 (p7_kn (S ti) - p7_kn ti) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fk (Z_to_bv 64 0x15368) fck None mk (seg_rom rsegs)).
Proof.
  intros HX ti Hti IH ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 mk fck Fk
         MU WM MI TM ST FR HF HB11 HBJ HS7 -> -> -> ->.
  pose proof (p7_kn_bound ti ltac:(lia)) as Hkn. pose proof (p7_kn_bound (S ti) ltac:(lia)) as Hkn1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  assert (HBJ' : bytes_at rsegs mk (bv_unsigned sp + 0x50) (pf_bytes (p7_J (S ti)))).
  { unfold pf_bytes in HBJ |- *. rewrite map_app in HBJ.
    exact (proj1 (proj1 (bytes_at_app rsegs mk _ _ _) HBJ)). }
  pose proof (p7m_ld8 mk _ _ HB11) as RD.
  zstep. (* 0x15368 addi a2, zero, 0xf0 *)
  zstep. (* 0x1536c ld a1, 0x48(sp) *)
  zstep. (* 0x15370 bgeu s5, a1, 0x15388 *)
  if_cases K; zify_cond K; cbv iota.
  - (* ti = 10: the 11 rows are joined *)
    assert (E10 : ti = 10%nat) by lia. subst ti.
    rewrite p7_J_11 in HBJ.
    eapply HX; [exact MU | exact WM | exact MI | exact TM | exact ST | exact FR | exact HF
               | exact (p7m_known_cstr mk ST HBJ) | exact HS7].
  - zstep. (* 0x15374 add s9, s9, a0 *)
    zstep. (* 0x15378 addi a0, s9, 2 *)
    zstep. (* 0x1537c addi s5, s5, 1 *)
    zstep. (* 0x15380 addi s8, s8, 0x128 *)
    zstep. (* 0x15384 bltu a0, a2, 0x15330 *)
    if_cases K2; zify_cond K2; cbv iota.
    + pose proof (IH ltac:(lia)) as IH'. unfold p7m_LH in IH'.
      eapply IH'; [exact MU | exact WM | exact MI | exact TM | exact ST | exact FR | exact HF | exact HB11
                  | exact HBJ' | exact HS7 | p7m_eq | p7m_eq | p7m_eq | p7m_eq].
    + exfalso. lia.
Qed.

(** 0x15364, pass ti's `jal snprintf(known + kn, 240 - kn, "%s%s", sep, tab[ti].token)`. *)
Lemma p7m_call : p7m_EXIT -> forall ti, (ti <= 10)%nat -> ((ti < 10)%nat -> p7m_LH (S ti)) ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 : word)
         (mk : word -> option byte) (fck : bv 32) (Fk : bvmap 5 word),
  munch WS m mk -> wmono rsegs m mk -> mem_inv rsegs mk -> MemNorm.task_mem rsegs mk ->
  stk rsegs mk lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fck ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get Fk r = reg_get F r) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x48) (le8 (Z_to_bv 64 11)) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x50) (pf_bytes (p7_J ti)) ->
  s7 = Z_to_bv 64 vp -> s5 = Z_to_bv 64 (Z.of_nat ti + 1) ->
  s8 = Z_to_bv 64 (0x20ad0 + 296 * Z.of_nat ti) -> s9 = Z_to_bv 64 (p7_kn ti) ->
  a0 = Z_to_bv 64 (bv_unsigned sp + 80 + p7_kn ti) -> a1 = Z_to_bv 64 (240 - p7_kn ti) ->
  a2 = Z_to_bv 64 0x1031b -> a3 = Z_to_bv 64 (p7m_sepp ti) -> a4 = Z_to_bv 64 (tok_ptr ti) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fk (Z_to_bv 64 0x15364) fck None mk (seg_rom rsegs)).
Proof.
  intros HX ti Hti IH ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 mk fck Fk
         MU WM MI TM ST FR HF HB11 HBJ HS7 -> -> -> -> -> -> -> ->.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (p7_kn_bound ti ltac:(lia)) as Hkn. pose proof (p7_kn_bound (S ti) ltac:(lia)) as Hkn1.
  destruct (p7m_seg ti Hti) as [EJ ELT].
  pose proof (p7_ctx_at mk fck WS p7_fw_WS MU WM MI TM ST FR) as (HENVk & _).
  destruct (pfc_printf_at mk fck (bv_unsigned sp) lo c v HENVk)
    as (STP & HIE & HSP & HFRM & MIk & TMk & HG1 & (can & HG2)).
  destruct (p7m_args_ro mk ti MI Hti) as [(HSC & HSP0 & HSB) (HTC & HTP0 & HTB)].
  set (T := p7_sep ti ++ p7_tok ti) in *.
  assert (HTL : 0 <= Z.of_nat (length T) <= 77) by lia.
  (* 0x15364: jal snprintf *)
  zstep.
  remember (bv_unsigned sp + 80 + p7_kn ti) as D eqn:ED.
  destruct (pfc_dst_stk mk lo (bv_unsigned sp + PARSE_FILE_FRAME) D (240 - p7_kn ti) ST
              ltac:(lia) ltac:(unfold PARSE_FILE_FRAME; lia) ltac:(lia)) as [junk HJ].
  pose proof HSN as HSN0. unfold snprintf_contract in HSN0. cbv zeta in HSN0.
  eapply evt_cut.
  { eapply HSN0 with (lo := bv_unsigned sp - SNPRINTF_K) (fmt := [37; 115; 37; 115]) (ps := [Ps; Ps])
                     (args := [APtr (p7_sep ti); APtr (p7_tok ti)]) (T := T) (junk := junk) (canary := can).
    all: rewrite ?(unsigned_lit 0x1031b), ?(unsigned_lit (240 - p7_kn ti)), ?(unsigned_lit D) by lia.
    all: first
      [ exact HJ | exact STP | exact HIE | exact HSP | exact FR | exact MI | exact TM | exact HG1 | exact HG2
      | (apply pfc_lit_at; [exact MI | lia | cbn [length]; lia | vm_compute; reflexivity])
      | (cbn [pf_args_ok]; split;
         [ apply pfc_arg_cstr; [exact HSC | exact HSP0 | left; unfold SNPRINTF_K; lia | left; lia]
         | split; [apply pfc_arg_cstr; [exact HTC | exact HTP0 | left; unfold SNPRINTF_K; lia | left; lia]
                  | exact I]])
      | (cbn [printf_facts_c.pf_text option_map]; rewrite app_nil_r; reflexivity)
      | reflexivity
      | (apply pfc_img_free_hi; lia)
      | (right; lia)
      | (unfold snprintf_c.RO_LO, snprintf_c.RO_END; cbn [length]; lia)
      | lia
      | (match goal with |- ?G => idtac "P7M-UNSOLVED-SNPRINTF-PREMISE:" G end; fail) ]. }
  intros ms' POST. unfold printf_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' &
                    m' & E & MU' & WM' & MI' & TM' & FRM' & HF' & ST' & HB').
  subst ms'.
  rewrite ?(unsigned_lit (240 - p7_kn ti)), ?(unsigned_lit D) in MU', HB' by lia.
  rewrite firstn_all2 in MU', HB' by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  set (W := [(bv_unsigned sp - SNPRINTF_K, bv_unsigned sp); (D, D + Z.of_nat (length T) + 1)]) in *.
  (* the memory after the call *)
  assert (MUw : munch WS m m').
  { eapply munch_trans; [exact MU|]. eapply (munch_weaken W WS); [|exact MU'].
    intros x Hx. unfold WS in Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
    unfold W, SNPRINTF_K. cbn [outside]. split; [lia | split; [lia | exact I]]. }
  pose proof (wmono_trans rsegs _ _ _ WM WM') as WMw.
  assert (STw : stk rsegs m' lo (bv_unsigned sp + PARSE_FILE_FRAME)).
  { destruct (stk_split rsegs mk lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                ltac:(unfold PARSE_FILE_FRAME; lia)) as [STl STh].
    apply (stk_merge rsegs m' lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME));
      [| | unfold PARSE_FILE_FRAME; lia].
    - apply (pfc_stk_back W mk m' lo (bv_unsigned sp) SNPRINTF_K STl MU' WM' ST');
        [unfold SNPRINTF_K; lia | unfold SNPRINTF_K; lia |].
      intros x Hx. unfold W, SNPRINTF_K in *. cbn [outside]. split; [lia | split; [lia | exact I]].
    - apply (p7m_stk_tr W mk m' _ _ STh MU' WM'). intros x Hx.
      destruct (Z_lt_dec x D) as [L|L].
      + left. unfold W, SNPRINTF_K. cbn [outside]. split; [lia | split; [lia | exact I]].
      + destruct (Z_lt_dec x (D + Z.of_nat (length T) + 1)) as [L2|L2].
        * right. apply (pfc_bytes_mrd m' D _ x HB'). unfold pf_bytes. rewrite length_map, length_app.
          cbn [length]. lia.
        * left. unfold W, SNPRINTF_K. cbn [outside]. split; [lia | split; [lia | exact I]]. }
  assert (HB11' : bytes_at rsegs m' (bv_unsigned sp + 0x48) (le8 (Z_to_bv 64 11))).
  { apply (pfc_bytes_munch W mk m' _ _ HB11 MU'). rewrite length_le8. intros x Hx.
    unfold W, SNPRINTF_K. cbn [outside]. split; [lia | split; [lia | exact I]]. }
  assert (HBJm : bytes_at rsegs m' (bv_unsigned sp + 0x50) (pf_bytes (p7_J ti))).
  { apply (pfc_bytes_munch W mk m' _ _ HBJ MU'). intros x Hx.
    assert (EKN : Z.of_nat (length (pf_bytes (p7_J ti))) = p7_kn ti)
      by (unfold pf_bytes, p7_kn; rewrite length_map; reflexivity).
    rewrite EKN in Hx. unfold W, SNPRINTF_K. cbn [outside]. split; [lia | split; [lia | exact I]]. }
  assert (HBJ' : bytes_at rsegs m' (bv_unsigned sp + 0x50) (pf_bytes (p7_J (S ti) ++ [0]))).
  { rewrite EJ. unfold pf_bytes. rewrite <- app_assoc, map_app.
    apply (proj2 (bytes_at_app rsegs m' _ _ _)). split; [exact HBJm|].
    assert (EA : bv_unsigned sp + 80 + Z.of_nat (length (map (Z_to_bv 8) (p7_J ti))) = D)
      by (rewrite length_map, ED; reflexivity).
    rewrite EA. exact HB'. }
  eapply (p7m_after HX ti Hti IH);
    [exact MUw | exact WMw | exact MI' | exact TM' | exact STw | exact FRM'
    | intros r Hr; rewrite (HF' r Hr); exact (HF r Hr) | exact HB11' | exact HBJ' | exact HS7
    | reflexivity | reflexivity | reflexivity | f_equal; exact ELT].
Qed.

(** 0x1534c, pass ti with a3 = its separator: the token pointer, the arguments, then the call. *)
Lemma p7m_body : p7m_EXIT -> forall ti, (ti <= 10)%nat -> ((ti < 10)%nat -> p7m_LH (S ti)) ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 : word)
         (mk : word -> option byte) (fck : bv 32) (Fk : bvmap 5 word),
  munch WS m mk -> wmono rsegs m mk -> mem_inv rsegs mk -> MemNorm.task_mem rsegs mk ->
  stk rsegs mk lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fck ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get Fk r = reg_get F r) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x48) (le8 (Z_to_bv 64 11)) ->
  bytes_at rsegs mk (bv_unsigned sp + 0x50) (pf_bytes (p7_J ti)) ->
  s7 = Z_to_bv 64 vp -> a2 = Z_to_bv 64 240 -> s5 = Z_to_bv 64 (Z.of_nat ti + 1) ->
  s8 = Z_to_bv 64 (0x20ad0 + 296 * Z.of_nat ti) -> s9 = Z_to_bv 64 (p7_kn ti) ->
  a3 = Z_to_bv 64 (p7m_sepp ti) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fk (Z_to_bv 64 0x1534c) fck None mk (seg_rom rsegs)).
Proof.
  intros HX ti Hti IH ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 mk fck Fk
         MU WM MI TM ST FR HF HB11 HBJ HS7 -> -> -> -> ->.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (p7_kn_bound ti ltac:(lia)) as Hkn.
  pose proof (p7m_row_ld mk ti MU ltac:(lia)) as RD.
  zstep. (* 0x1534c ld a4, 0(s8) *)
  zstep. (* 0x15350 addi a0, sp, 0x50 *)
  zstep. (* 0x15354 add a0, a0, s9 *)
  zstep. (* 0x15358 sub a1, a2, s9 *)
  zstep. (* 0x1535c auipc a2 *)
  zstep. (* 0x15360 addi a2, a2, -0x41 *)
  eapply (p7m_call HX ti Hti IH);
    [exact MU | exact WM | exact MI | exact TM | exact ST | exact FR | exact HF | exact HB11 | exact HBJ
    | exact HS7 | reflexivity | reflexivity | reflexivity | p7m_eq | p7m_eq | p7m_eq | reflexivity | p7m_eq].
Qed.

(** 0x15330, the loop head: the separator ("" for row 0, "|" after), then the pass. *)
Lemma p7m_head : p7m_EXIT -> forall ti, (ti <= 10)%nat -> ((ti < 10)%nat -> p7m_LH (S ti)) -> p7m_LH ti.
Proof.
  intros HX ti Hti IH. unfold p7m_LH.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 mk fck Fk
         MU WM MI TM ST FR HF HB11 HBJ HS7 Ha2 Hs5 Hs8 Hs9.
  subst s5.
  zstep. (* 0x15330 addi a0, zero, 1 *)
  zstep. (* 0x15334 beq s5, a0, 0x15344 *)
  if_cases K; zify_cond K; cbv iota.
  - (* ti = 0: the empty separator *)
    zstep. (* 0x15344 auipc a0 *)
    zstep. (* 0x15348 addi a3, a0, 0x4a *)
    eapply (p7m_body HX ti Hti IH);
      [exact MU | exact WM | exact MI | exact TM | exact ST | exact FR | exact HF | exact HB11 | exact HBJ
      | exact HS7 | exact Ha2 | reflexivity | exact Hs8 | exact Hs9 |].
    unfold p7m_sepp. replace (ti =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). reflexivity.
  - zstep. (* 0x15338 auipc a0 *)
    zstep. (* 0x1533c addi a3, a0, 0x2b8 *)
    zstep. (* 0x15340 j 0x1534c *)
    eapply (p7m_body HX ti Hti IH);
      [exact MU | exact WM | exact MI | exact TM | exact ST | exact FR | exact HF | exact HB11 | exact HBJ
      | exact HS7 | exact Ha2 | reflexivity | exact Hs8 | exact Hs9 |].
    unfold p7m_sepp. replace (ti =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma p7m_LH_all : p7m_EXIT -> forall k ti, (ti + k = 10)%nat -> p7m_LH ti.
Proof.
  intros HX. induction k as [|k IH]; intros ti Hk.
  - apply (p7m_head HX); [lia | intros H; exfalso; lia].
  - apply (p7m_head HX); [lia | intros _; apply IH; lia].
Qed.

(** 0x15310, ntok stored: `reac_box_catalogue(&ntok)` (a0 = the table, ntok = 11), the empty-table test, the
    loop's registers, the loop. *)
Lemma p7m_cat : p7m_EXIT ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 : word)
         (mk : word -> option byte) (fck : bv 32) (Fk : bvmap 5 word),
  munch WS m mk -> wmono rsegs m mk -> mem_inv rsegs mk -> MemNorm.task_mem rsegs mk ->
  stk rsegs mk lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fck ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get Fk r = reg_get F r) ->
  s7 = Z_to_bv 64 vp ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fk (Z_to_bv 64 0x15310) fck None mk (seg_rom rsegs)).
Proof.
  intros HX ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 mk fck Fk MU WM MI TM ST FR HF HS7.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof p7_sp16 as HSP16.
  assert (WRN : wr_at rsegs mk (bv_unsigned sp + 72) 8).
  { apply (p7_wr_of_stk mk lo (bv_unsigned sp + PARSE_FILE_FRAME));
      [exact ST | unfold PARSE_FILE_FRAME; lia | lia | unfold PARSE_FILE_FRAME; lia]. }
  zstep. (* 0x15310 addi a0, sp, 0x48 *)
  zstep. (* 0x15314 jal reac_box_catalogue *)
  eapply evt_cut.
  { eapply HBC with (c := bv_unsigned sp + 72);
      [reflexivity | right; split; [Z.div_mod_to_equations; lia | exact WRN]]. }
  intros ms' (a1' & m5 & Ems & Hc). subst ms'.
  rewrite ret_pc_even by (try lia; reflexivity).
  assert (E0 : (bv_unsigned sp + 72 =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite E0 in Hc. destruct Hc as (HB11 & MUc & WMc & MIc).
  (* the memory after the call *)
  assert (MU5 : munch WS m m5).
  { eapply munch_trans; [exact MU|].
    eapply (munch_weaken [(bv_unsigned sp + 72, bv_unsigned sp + 72 + 8)] WS); [|exact MUc].
    intros x Hx. unfold WS in Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _).
    split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM WMc) as WM5.
  pose proof (MIc MI) as MI5.
  assert (ST5 : stk rsegs m5 lo (bv_unsigned sp + PARSE_FILE_FRAME)).
  { apply (p7m_stk_tr [(bv_unsigned sp + 72, bv_unsigned sp + 72 + 8)] mk m5 _ _ ST MUc WMc).
    intros x Hx. destruct (Z_lt_dec x (bv_unsigned sp + 72)) as [L|L].
    - left. cbn [outside]. split; [lia | exact I].
    - destruct (Z_lt_dec x (bv_unsigned sp + 80)) as [L2|L2].
      + right. apply (pfc_bytes_mrd m5 _ _ x HB11). rewrite length_le8. lia.
      + left. cbn [outside]. split; [lia | exact I]. }
  assert (TM5 : MemNorm.task_mem rsegs m5).
  { apply (p7_task_munch [(bv_unsigned sp + 72, bv_unsigned sp + 72 + 8)] mk m5 TM MUc).
    intros x Hx. cbn [outside] in Hx.
    destruct ST as (_ & _ & STa).
    destruct (STa (bv_unsigned x) ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ (bb & Hbb)].
    replace x with (wa (bv_unsigned x)) by (unfold wa; apply Z_to_bv_bv_unsigned).
    rewrite Hbb. discriminate. }
  pose proof (p7m_ld8 m5 _ _ HB11) as RD.
  subst s7.
  zstep. (* 0x15318 ld a1, 0x48(sp) *)
  zstep. (* 0x1531c addi a2, zero, 0xf0 *)
  zstep. (* 0x15320 beqz a1, 0x15388 *)
  if_cases K; zify_cond K; cbv iota; [exfalso; lia|].
  zstep. (* 0x15324 mv s8, a0 *)
  zstep. (* 0x15328 mv s9, zero *)
  zstep. (* 0x1532c addi s5, zero, 1 *)
  pose proof (p7m_LH_all HX 10 0 eq_refl) as LH0. unfold p7m_LH in LH0.
  eapply LH0; [exact MU5 | exact WM5 | exact MI5 | exact TM5 | exact ST5 | exact FR | exact HF | exact HB11
              | | reflexivity | p7m_eq | p7m_eq | p7m_eq | p7m_eq].
  replace (pf_bytes (p7_J 0)) with (@nil byte) by reflexivity. apply bytes_at_nil. lia.
Qed.

(** 0x152d0, the hit: snprintf(cur->model, 24, "%s", low), model_set = 1, then PROVM. *)
Lemma p7_hit : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 : word)
    (m3 : word -> option byte) (fc3 : bv 32) (F3 : bvmap 5 word) (j : nat),
  by_token LW = Some j ->
  munch WS m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 -> MemNorm.task_mem rsegs m3 ->
  stk rsegs m3 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc3 ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F3 r = reg_get F r) ->
  cstr_at rsegs m3 (bv_unsigned sp + 0x140) LW ->
  s7 = Z_to_bv 64 vp ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             (Z_to_bv 64 512) s10 s11 t3 t4 t5 t6)
        F3 (Z_to_bv 64 0x152d0) fc3 None m3 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 m3 fc3 F3 j
         EBT MU WM MI3 TM3 ST3 FR3 HF3 HLOW HS7.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof p7_sp16 as HSP16. pose proof p7_gi as Hgi.
  pose proof (p7_ctx_at m3 fc3 WS p7_fw_WS MU WM MI3 TM3 ST3 FR3) as HCTX3.
  pose proof (p7_state_at m3 MU) as HST3.
  pose proof (proj1 HCTX3) as HENV3.
  destruct (pfc_printf_at m3 fc3 (bv_unsigned sp) lo c v HENV3) as
    (STp & HIMG & HSP63' & FRM3 & MIp & TMp & HGOT & HGUARDe).
  destruct HGUARDe as [canary HGUARD].
  pose proof HST3 as HST3b. destruct HST3b as (HRC3 & HCUR3 & HNM3 & HCNT3).
  pose proof HRC3 as HRC3b. destruct HRC3b as (bs0 & HBC0 & HENC0).
  assert (HL0 : Z.of_nat (length bs0) = SEG_C_SIZE) by exact (proj1 HENC0).
  unfold SEG_C_SIZE in HL0.
  pose proof (bytes_at_bound rsegs m3 c bs0 HBC0) as HCB. rewrite HL0 in HCB.
  assert (Hgi32 : (gi < 32)%nat) by (pose proof (proj1 (proj2 HENC0)) as H32; lia).
  pose proof (pfc_c_wr m3 c rc HRC3 p7_noimg_c) as WRC.
  assert (WRC0 : wr_at rsegs m3 c (Z.of_nat (length bs0))) by (rewrite HL0; exact WRC).
  assert (HLWn : ~ In 0 LW) by (unfold LW; apply p7_low_nulfree; exact p7_val_nulfree).
  assert (HLWl : (length LW <= 23)%nat)
    by (unfold LW; rewrite p7_low_len by exact p7_val_nulfree; lia).
  assert (HLWb : Forall pfc_zbyte LW).
  { unfold LW. apply p7_low_byte; [exact p7_val_nulfree|].
    destruct HVPat as (bsv & slv & _ & Hz & _). rewrite <- Hz. apply pfc_zs_byte. }
  assert (HSPAN : cstr_span (bv_unsigned sp + 320) LW <= 31).
  { unfold cstr_span.
    pose proof (Z.mod_pos_bound (- (bv_unsigned sp + 320 + Z.of_nat (length LW) + 1)) 8 ltac:(lia)). lia. }
  assert (EFL : Z.of_nat (length F_s) = 2) by (vm_compute; reflexivity).
  assert (EFP : pf_parse F_s = Some [Ps]) by (vm_compute; reflexivity).
  assert (EFB : ro_bytes_b rsegs 0x104e0 (pf_bytes (F_s ++ [0])) = true) by (vm_compute; reflexivity).
  assert (EN : bv_unsigned (Z_to_bv 64 24) = 24) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (c + 356 * Z.of_nat gi + 36)) = c + 356 * Z.of_nat gi + 36)
    by (apply unsigned_lit; lia).
  assert (EF2 : bv_unsigned (Z_to_bv 64 0x104e0) = 0x104e0) by (apply unsigned_lit; lia).
  assert (EA3 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 320)) = bv_unsigned sp + 320)
    by (apply unsigned_lit; lia).
  rewrite HS6. cbn [pf_cur_ptr]. unfold rseg_addr, RSEG_SIZE.
  do 7 zstep.
  pose proof HSN as HSN0. unfold snprintf_contract in HSN0. cbv zeta in HSN0.
  eapply evt_cut.
  { eapply HSN0 with (lo := bv_unsigned sp - SNPRINTF_K) (fmt := F_s) (ps := [Ps])
                     (args := [APtr LW]) (T := LW) (canary := canary)
                     (junk := fld (Z.to_nat (c + 356 * Z.of_nat gi + 36 - c)) 24 bs0).
    - rewrite EF2. apply (pfc_lit_at m3 0x104e0 F_s MI3); [lia | | exact EFB].
      rewrite EFL. lia.
    - rewrite EF2. unfold RO_LO. lia.
    - rewrite EF2, EFL. unfold RO_END. lia.
    - exact EFP.
    - rewrite ED, EN. split; [|exact I].
      rewrite <- EA3. apply pfc_arg_cstr.
      + rewrite EA3. exact HLOW.
      + rewrite EA3. lia.
      + rewrite EA3. right. lia.
      + rewrite EA3. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap.
        destruct Hap as [Hc|Hc]; [right; lia | left; lia].
    - cbn [printf_facts_c.pf_text option_map]. rewrite app_nil_r. reflexivity.
    - rewrite ED, EN. cbn [Z.to_nat].
      exact (pfc_dst_blk m3 c bs0 (c + 356 * Z.of_nat gi + 36) 24 HBC0 WRC0 ltac:(lia)
               ltac:(rewrite HL0; cbn [Z.of_nat]; lia)).
    - rewrite EN. lia.
    - lia.
    - rewrite ED. lia.
    - rewrite ED, EN. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap.
      destruct Hap as [Hc|Hc]; [left; unfold SNPRINTF_K; lia | right; lia].
    - rewrite ED, EN. apply (pfc_noimg_sub c SEG_C_SIZE); [exact p7_noimg_c | lia |].
      unfold SEG_C_SIZE. lia.
    - exact STp.
    - lia.
    - exact HIMG.
    - exact HSP63'.
    - exact FR3.
    - exact MI3.
    - exact TM3.
    - exact HGOT.
    - exact HGUARD. }
  intros ms' (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F4 & fc4 & m4 &
              Ems & MU4 & WM4 & MI4 & TM4 & FR4 & HF4 & ST4 & HD4).
  subst ms'. rewrite ret_pc_even by (try lia; reflexivity).
  rewrite ED, EN in MU4, HD4.
  rewrite (firstn_all2 (n := Z.to_nat (24 - 1)) LW ltac:(cbn [Z.to_nat]; lia)) in MU4, HD4.
  assert (EPB : pf_bytes (LW ++ [0]) = zb LW ++ [ZERO])
    by (unfold pf_bytes, zb; rewrite map_app; reflexivity).
  rewrite EPB in HD4.
  (* the block at m4 *)
  assert (EIDX : Z.to_nat (c + 356 * Z.of_nat gi + 36 - c) = (356 * gi + 36)%nat) by lia.
  assert (HBC4 : bytes_at rsegs m4 c (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO]))).
  { rewrite <- EIDX.
    apply (pfc_bytes_patch _ m3 m4 c bs0 (c + 356 * Z.of_nat gi + 36) (zb LW ++ [ZERO])
             HBC0 MU4 HD4 ltac:(lia)).
    - rewrite HL0, length_app, pfc_len_zb. cbn [length]. lia.
    - intros x Hx Hnx. rewrite HL0 in Hx.
      rewrite length_app, pfc_len_zb in Hnx. cbn [length] in Hnx.
      cbn [outside]. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap. unfold SNPRINTF_K.
      split; [destruct Hap as [Hc|Hc]; lia | split; [lia | exact I]]. }
  (* the counters and the stack at m4 *)
  assert (MUw4 : munch WP m m4).
  { eapply munch_trans.
    - eapply (munch_weaken WS WP m m3); [|exact MU].
      intros x Hx. unfold WP in Hx. cbn [outside] in Hx. unfold WS. cbn [outside].
      split; [lia | split; [lia | exact I]].
    - eapply (munch_weaken _ WP m3 m4); [|exact MU4].
      intros x Hx. unfold WP in Hx. cbn [outside] in Hx. cbn [outside].
      unfold RC_N in Hx. unfold SNPRINTF_K.
      split; [lia | split; [lia | exact I]]. }
  pose proof (wmono_trans rsegs _ _ _ WM WM4) as WMw4.
  assert (ST4f : stk rsegs m4 lo (bv_unsigned sp + PARSE_FILE_FRAME)).
  { assert (ST3lo : stk rsegs m3 lo (bv_unsigned sp)).
    { exact (proj1 (stk_split rsegs m3 lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST3
                      ltac:(unfold PARSE_FILE_FRAME; lia))). }
    assert (ST3hi : stk rsegs m3 (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME)).
    { exact (proj2 (stk_split rsegs m3 lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST3
                      ltac:(unfold PARSE_FILE_FRAME; lia))). }
    assert (ST4lo : stk rsegs m4 lo (bv_unsigned sp)).
    { apply (pfc_stk_back _ m3 m4 lo (bv_unsigned sp) SNPRINTF_K ST3lo MU4 WM4 ST4);
        [unfold SNPRINTF_K; lia | unfold SNPRINTF_K; lia |].
      intros x Hx. cbn [outside]. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap. unfold SNPRINTF_K in *.
      split; [lia | split; [destruct Hap as [Hc|Hc]; lia | exact I]]. }
    assert (ST4hi : stk rsegs m4 (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME)).
    { apply (stk_transport_disjoint rsegs _ m3 m4 _ _ ST3hi MU4 WM4).
      cbn [disjoint_from]. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap. unfold PARSE_FILE_FRAME.
      split; [lia | split; [destruct Hap as [Hc|Hc]; lia | exact I]]. }
    exact (stk_merge rsegs m4 lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST4lo ST4hi
             ltac:(unfold PARSE_FILE_FRAME; lia)). }
  assert (HF4F : forall r : reg, bv_unsigned r <> 10 -> reg_get F4 r = reg_get F r)
    by (intros r Hr; rewrite (HF4 r Hr); exact (HF3 r Hr)).
  (* model_set = 1 *)
  assert (WRC4 : wr_at rsegs m4 c SEG_C_SIZE) by (apply (wr_at_transport rsegs m3 m4 c _ WRC WM4)).
  assert (HS2 : store_ok rsegs m4 (wa (c + 356 * Z.of_nat gi + 60)) 4 = true).
  { pose proof (wr_at_store_ok rsegs m4 c SEG_C_SIZE (356 * Z.of_nat gi + 60) 4%nat WRC4
                  ltac:(lia) ltac:(unfold SEG_C_SIZE; cbn [Z.of_nat]; lia)) as H.
    replace (c + (356 * Z.of_nat gi + 60)) with (c + 356 * Z.of_nat gi + 60) in H by lia. exact H. }
  zstep.
  step.
  assert (HLU : length (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO])) = length bs0).
  { rewrite upd_bytes_length; [reflexivity|]. rewrite length_app, pfc_len_zb. cbn [length]. lia. }
  assert (HBC5 : bytes_at rsegs
            (write_to_mem m4 (wa (c + 356 * Z.of_nat gi + 60)) (le4 (Z_to_bv 64 1))) c
            (upd_bytes (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO])) (356 * gi + 60)
               (le4 (Z_to_bv 64 1)))).
  { pose proof (bytes_at_write_inside rsegs m4 c (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO]))
                  (356 * Z.of_nat gi + 60) (le4 (Z_to_bv 64 1)) HBC4 ltac:(lia)
                  ltac:(rewrite HLU, length_le4; lia)) as H.
    replace (Z.to_nat (356 * Z.of_nat gi + 60)) with (356 * gi + 60)%nat in H by lia.
    replace (c + (356 * Z.of_nat gi + 60)) with (c + 356 * Z.of_nat gi + 60) in H by lia.
    exact H. }
  assert (MU5 : munch WP m (write_to_mem m4 (wa (c + 356 * Z.of_nat gi + 60)) (le4 (Z_to_bv 64 1)))).
  { apply (munch_write WP m m4 (c + 356 * Z.of_nat gi + 60) _ MUw4);
      [lia | rewrite length_le4; lia |].
    unfold WP. cbn [inside]. rewrite length_le4. unfold RC_N. right. right. left. lia. }
  pose proof (wmono_write rsegs m m4 (wa (c + 356 * Z.of_nat gi + 60)) (le4 (Z_to_bv 64 1)) WMw4) as WM5.
  pose proof (stk_write rsegs m4 lo (bv_unsigned sp + PARSE_FILE_FRAME) (c + 356 * Z.of_nat gi + 60)
                (le4 (Z_to_bv 64 1)) ST4f ltac:(lia) ltac:(rewrite length_le4; lia)) as ST5.
  assert (MI5 : mem_inv rsegs (write_to_mem m4 (wa (c + 356 * Z.of_nat gi + 60)) (le4 (Z_to_bv 64 1)))).
  { apply (mem_inv_store rsegs m4 _ _ MI4). rewrite length_le4. exact HS2. }
  assert (TM5 : MemNorm.task_mem rsegs
            (write_to_mem m4 (wa (c + 356 * Z.of_nat gi + 60)) (le4 (Z_to_bv 64 1)))).
  { apply (p7_task_munch [(c + 356 * Z.of_nat gi + 60, c + 356 * Z.of_nat gi + 64)] m4 _ TM4).
    - apply (munch_write _ m4 m4 _ _ (munch_refl _ m4));
        [lia | rewrite length_le4; lia |]. cbn [inside]. rewrite length_le4. left. lia.
    - intros x Hx. cbn [outside] in Hx.
      destruct HBC4 as (_ & _ & HBn).
      assert (Ex : bv_unsigned x = c + Z.of_nat (Z.to_nat (bv_unsigned x - c))) by lia.
      replace x with (wa (c + Z.of_nat (Z.to_nat (bv_unsigned x - c))))
        by (rewrite <- Ex; unfold wa; apply Z_to_bv_bv_unsigned).
      rewrite HBn by (rewrite HLU; lia).
      intros C. apply nth_error_None in C. rewrite HLU in C. lia. }
  (* the reader's state after the two writes *)
  assert (HRC5 : rconf_at rsegs (write_to_mem m4 (wa (c + 356 * Z.of_nat gi + 60)) (le4 (Z_to_bv 64 1)))
            c (pf_prov_mid (PModel LW) rc gi)).
  { exists (upd_bytes (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO])) (356 * gi + 60)
              (le4 (Z_to_bv 64 1))).
    split; [exact HBC5|].
    apply (pfc_enc_model rc bs0 gi LW HENC0 Hgi ltac:(lia) HLWn HLWb). }
  assert (HST5 : pf_state (write_to_mem m4 (wa (c + 356 * Z.of_nat gi + 60)) (le4 (Z_to_bv 64 1)))
            (bv_unsigned sp) c (pf_prov_mid (PModel LW) rc gi) (Some gi) nm (length (skipn o s))).
  { split; [exact HRC5|].
    split; [apply pfc_cur_ok_upd; exact HCUR3|].
    split; [|apply (pfc_cnt_upd rc gi _ (length (skipn o s))); [exact HCNT3 | lia]].
    apply (pfc_nm_call m _ fc (bv_unsigned sp) lo c v nm WP p7_env (proj1 (proj2 (proj2 HSTATE))) MU5).
    intros x Hx. unfold WP. cbn [outside]. unfold PF_NAMEBUF, PF_SAVE in Hx.
    unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap. unfold RC_N, RC_REFUSAL, RC_OVERFLOW.
    destruct Hap as [Hc|Hc]; (split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]). }
  assert (HCTX5 : pf_ctx (write_to_mem m4 (wa (c + 356 * Z.of_nat gi + 60)) (le4 (Z_to_bv 64 1)))
            fc4 (bv_unsigned sp) lo v c t s o ln d n)
    by (apply (p7_ctx_at _ fc4 WP p7_fw_WP MU5 WM5 MI5 TM5 ST5 FR4)).
  (* a0 = &cur->model_file, a1 = 96, a2 = "%s", then PROVM *)
  do 4 zstep.
  unfold Post. rewrite HKEY. unfold LW in EBT. rewrite EBT. cbv iota.
  rewrite (p7_snprintf_low val p7_val_nulfree).
  eapply evt_mono.
  { eapply HPROVM.
    - exact HCTX5.
    - exact HST5.
    - exact HREGS.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  intros ms' Hms'.
  apply (pf_fin_weaken v sp gp tp F F4 m _ lo c _ ms' Hms'
           (munch_weaken WP (pfc_W (bv_unsigned sp) c) m _ p7_subW MU5) WM5 HF4F).
Qed.

Lemma p7_subWS : sub_fp WS (pfc_W (bv_unsigned sp) c).
Proof.
  intros x Hx. unfold pfc_W, RC_PARSE_W, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME,
    RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN in Hx. cbn [outside] in Hx.
  unfold WS. cbn [outside]. split; [lia | split; [lia | exact I]].
Qed.

(** 0x15388, the refusal and the S9 exit: refuse(c, lineno, F_badmodel, cur_name, val, known), `j` S9. *)
Lemma p7_refuse_exit : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 : word)
    (m4 : word -> option byte) (fc4 : bv 32) (F4 : bvmap 5 word),
  by_token LW = None ->
  munch WS m m4 -> wmono rsegs m m4 -> mem_inv rsegs m4 -> MemNorm.task_mem rsegs m4 ->
  stk rsegs m4 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc4 ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F4 r = reg_get F r) ->
  cstr_at rsegs m4 (bv_unsigned sp + 0x50) known ->
  s7 = Z_to_bv 64 vp ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F4 (Z_to_bv 64 0x15388) fc4 None m4 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 m4 fc4 F4
         EBT MU WM MI4 TM4 ST4 FR4 HF4 HKN HS7.
  subst s7.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof p7_sp16 as HSP16.
  pose proof (p7_ctx_at m4 fc4 WS p7_fw_WS MU WM MI4 TM4 ST4 FR4) as HCTX4.
  pose proof (p7_state_at m4 MU) as HST4.
  pose proof (proj1 HCTX4) as HENV4.
  pose proof HST4 as HST4b. destruct HST4b as (HRC4 & HCUR4 & HNM4 & HCNT4).
  (* the line account bounds *)
  assert (HBND : (o < length s)%nat /\ 0 <= ln + 1 <= 65535).
  { pose proof HCTX4 as HC. unfold pf_ctx in HC.
    destruct HC as (_ & HTX & _ & Ho & _ & HLC).
    unfold pf_lctx in HLC. destruct HLC as (HLa & _ & HLb & HLc).
    unfold reac_segconf_parse_file_pieces_c.pf_text in HTX.
    destruct HTX as (_ & _ & HLs & _ & _). pose proof (pfc_len65535 s HLs) as HLsz.
    split; [exact Ho | lia]. }
  destruct HBND as [Ho4 HLN].
  (* c's range *)
  pose proof HRC4 as HRC4b. destruct HRC4b as (bs0 & HBC0 & HENC0).
  assert (HL0 : Z.of_nat (length bs0) = SEG_C_SIZE) by exact (proj1 HENC0).
  unfold SEG_C_SIZE in HL0.
  pose proof (bytes_at_bound rsegs m4 c bs0 HBC0) as HCB. rewrite HL0 in HCB.
  (* the three string arguments *)
  pose proof HREGS as HR. destruct HR as (Hs0 & Hs2 & Hs3 & Hs1 & Hs4 & Hs10 & Hs11).
  assert (ES0 : bv_unsigned s0 = c) by (rewrite Hs0; apply unsigned_lit; lia).
  assert (ES3 : bv_unsigned s3 = ln + 1) by (rewrite Hs3; apply unsigned_lit; lia).
  destruct (pfc_nm_cstr m4 (bv_unsigned sp) nm HNM4 HSP16) as [HNMC HNML].
  destruct p7_vpin as (HVP1 & HVP2). unfold PF_BUF in HVP1, HVP2.
  assert (HVALC : cstr_at rsegs m4 vp val).
  { apply (pfc_cstr_munch WS m m4 vp val HVPat MU).
    intros x Hx. unfold cstr_span in Hx.
    pose proof (Z.mod_pos_bound (- (vp + Z.of_nat (length val) + 1)) 8 ltac:(lia)).
    unfold WS. cbn [outside]. split; [lia | split; [lia | exact I]]. }
  assert (HVALL : (length val <= 65535)%nat) by (apply p7_len65535; lia).
  destruct (pfc_fmt_at m4 F_badmodel PFC_STR_BADMODEL MI4
              ltac:(unfold PFC_FMTS; cbn [In]; right; right; right; right; left; reflexivity))
    as (HFP0 & HFPC & HFPR & HFPE & HFPIN).
  assert (ECK : conv_kinds F_badmodel = map arg_is_s [AS nm; AS val; AS known])
    by (vm_compute; reflexivity).
  do 8 zstep.
  pose proof HRF as HRF0. unfold refuse_contract in HRF0.
  eapply evt_cut.
  { eapply HRF0 with (lo := lo) (ln := ln + 1) (rc := rc) (f := F_badmodel)
                     (args := [AS nm; AS val; AS known]).
    rewrite ES0, ES3, (unsigned_lit 0x104e3) by lia.
    apply (pfc_refuse_pre m4 fc4 (bv_unsigned sp) lo v c t s o ln d n rc (Some gi) nm
             (length (skipn o s)) F_badmodel PFC_STR_BADMODEL _ [AS nm; AS val; AS known]
             HCTX4 HST4 HFPIN ECK HFP0 HFPC HFPR HFPE).
    split; [|split; [|split; [|exact I]]].
    - apply (pfc_va_frame m4 fc4 (bv_unsigned sp) lo c v rc _ nm HENV4 HRC4);
        [unfold PF_NAMEBUF; lia | unfold PF_NAMEBUF, PARSE_FILE_FRAME; lia
         | apply p7_len65535; lia | exact HNMC].
    - apply (pfc_va_frame m4 fc4 (bv_unsigned sp) lo c v rc vp val HENV4 HRC4);
        [lia | unfold PARSE_FILE_FRAME; lia | exact HVALL | exact HVALC].
    - apply (pfc_va_frame m4 fc4 (bv_unsigned sp) lo c v rc _ known HENV4 HRC4);
        [lia | rewrite p7_known_len; unfold PARSE_FILE_FRAME; lia
         | apply p7_len65535; rewrite p7_known_len; lia | exact HKN]. }
  intros ms' (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F5 & fc5 & m5 &
              Ems & FR5 & HF5 & MU5 & WM5 & MI5 & TM5 & ST5 & HRC5).
  subst ms'. rewrite ret_pc_even by (try lia; reflexivity).
  rewrite ES0 in MU5, HRC5.
  destruct (pfc_after_refuse m4 m5 fc4 fc5 (bv_unsigned sp) lo v c t s o ln d n rc (Some gi) nm
              F_badmodel [AS nm; AS val; AS known] HCTX4 HST4 MU5 WM5 ST5 MI5 TM5 FR5 HRC5)
    as (HH5 & HS5 & HM5 & MUW5).
  zstep.
  unfold Post. rewrite HKEY. unfold LW in EBT. rewrite EBT. cbv iota.
  eapply evt_mono.
  { eapply HS9c; [exact HH5 | exact HS5 | exact HM5 | exact HREGS | exact HS6]. }
  intros ms' Hms'.
  apply (pf_fin_weaken v sp gp tp F F5 m m5 lo c _ ms' Hms'
           (munch_trans _ m m4 m5 (munch_weaken WS (pfc_W (bv_unsigned sp) c) m m4 p7_subWS MU) MUW5)
           (wmono_trans rsegs m m4 m5 WM WM5)
           (fun r Hr => eq_trans (HF5 r Hr) (HF4 r Hr))).
Qed.

(** 0x1530c, the miss: the catalogue, the join loop over the 11 tokens, refuse, then S9. *)
Lemma p7_miss : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 : word)
    (m3 : word -> option byte) (fc3 : bv 32) (F3 : bvmap 5 word),
  by_token LW = None ->
  munch WS m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 -> MemNorm.task_mem rsegs m3 ->
  stk rsegs m3 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc3 ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F3 r = reg_get F r) ->
  s7 = Z_to_bv 64 vp ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F3 (Z_to_bv 64 0x1530c) fc3 None m3 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s9 t3 t4 t5 t6 m3 fc3 F3
         EBT MU3 WM3 MI3 TM3 ST3 FR3 HF3 HS7.
  assert (HX : p7m_EXIT).
  { unfold p7m_EXIT. intros. apply p7_refuse_exit; assumption. }
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  assert (WRN : wr_at rsegs m3 (bv_unsigned sp + 0x48) 8).
  { apply (p7_wr_of_stk m3 lo (bv_unsigned sp + PARSE_FILE_FRAME));
      [exact ST3 | unfold PARSE_FILE_FRAME; lia | lia | unfold PARSE_FILE_FRAME; lia]. }
  pose proof (wr_at_store_ok rsegs m3 (bv_unsigned sp + 0x48) 8 0 8%nat WRN ltac:(lia)
                ltac:(cbn [Z.of_nat]; lia)) as HS.
  rewrite Z.add_0_r in HS.
  (* 0x1530c: sd zero, 0x48(sp) (ntok = 0) *)
  step.
  eapply (p7m_cat HX).
  - apply (munch_write WS m m3 (bv_unsigned sp + 0x48)); [exact MU3 | lia | rewrite ?length_le8; lia |].
    unfold WS. rewrite ?length_le8. cbn [inside]. right. left. lia.
  - apply wmono_write. exact WM3.
  - apply mem_inv_store; [exact MI3 |]. rewrite ?length_le8. exact HS.
  - apply (p7_task_munch [(bv_unsigned sp + 0x48, bv_unsigned sp + 0x48 + 8)] m3 _ TM3).
    + apply (munch_write _ m3 m3 _ _ (munch_refl _ m3)); [lia | rewrite ?length_le8; lia |].
      rewrite ?length_le8. cbn [inside]. left. lia.
    + intros x Hx. cbn [outside] in Hx.
      destruct ST3 as (_ & _ & STa).
      destruct (STa (bv_unsigned x) ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ (bb & Hbb)].
      replace x with (wa (bv_unsigned x)) by (unfold wa; apply Z_to_bv_bv_unsigned).
      rewrite Hbb. discriminate.
  - apply stk_write; [exact ST3 | lia | rewrite ?length_le8; lia].
  - exact FR3.
  - exact HF3.
  - exact HS7.
Qed.

(** 0x152bc, the NUL store and the by_token call: a2 = LI and low[0 .. LI) holds the fold. *)
Lemma p7_zstore : forall (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 : word)
    (m1 : word -> option byte) (fc1 : bv 32) (F1 : bvmap 5 word) (LB : list byte),
  munch WS m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> MemNorm.task_mem rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc1 ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x140) LB -> length LB = 24%nat ->
  firstn LI (zs LB) = LW ->
  s7 = Z_to_bv 64 vp ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (Z.of_nat LI)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 512) s10 s11 t3 t4 t5 t6)
        F1 (Z_to_bv 64 0x152bc) fc1 None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 m1 fc1 F1 LB
         MU WM MI1 TM1 ST1 FR1 HF1 HLB HLBlen HINV HS7.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof p7_sp16 as HSP16.
  assert (HLI : (LI <= 23)%nat) by (rewrite p7_LI; lia).
  assert (WRL : wr_at rsegs m1 (bv_unsigned sp + 0x140) 24).
  { apply (p7_wr_of_stk m1 lo (bv_unsigned sp + PARSE_FILE_FRAME));
      [exact ST1 | unfold PARSE_FILE_FRAME; lia | lia | unfold PARSE_FILE_FRAME; lia]. }
  pose proof (wr_at_store_ok rsegs m1 (bv_unsigned sp + 0x140) 24 (Z.of_nat LI) 1%nat WRL
                ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as HS.
  assert (EZ : le1 (Z_to_bv 64 0) = [ZERO]) by reflexivity.
  do 2 zstep.
  step.
  rewrite EZ.
  (* the memory after low[LI] = 0 *)
  assert (HLB2 : bytes_at rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat LI)) [ZERO])
            (bv_unsigned sp + 320) (upd_bytes LB LI [ZERO])).
  { pose proof (bytes_at_write_inside rsegs m1 (bv_unsigned sp + 320) LB (Z.of_nat LI) [ZERO] HLB
                  ltac:(lia) ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H.
    rewrite Nat2Z.id in H. exact H. }
  assert (MU2 : munch WS m (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat LI)) [ZERO])).
  { apply (munch_write WS m m1 (bv_unsigned sp + 320 + Z.of_nat LI) _ MU);
      [lia | cbn [length]; lia |]. unfold WS. cbn [inside length]. right. left. lia. }
  pose proof (wmono_write rsegs m m1 (wa (bv_unsigned sp + 320 + Z.of_nat LI)) [ZERO] WM) as WM2.
  pose proof (stk_write rsegs m1 lo (bv_unsigned sp + PARSE_FILE_FRAME)
                (bv_unsigned sp + 320 + Z.of_nat LI) [ZERO] ST1 ltac:(lia) ltac:(cbn [length]; lia)) as ST2.
  assert (MI2 : mem_inv rsegs (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat LI)) [ZERO])).
  { apply (mem_inv_store rsegs m1 _ _ MI1). cbn [length]. exact HS. }
  assert (HPRES : mrd rsegs m1 (wa (bv_unsigned sp + 320 + Z.of_nat LI)) <> None).
  { destruct HLB as (_ & _ & HLBn). rewrite (HLBn LI ltac:(lia)).
    intros C. apply nth_error_None in C. lia. }
  assert (TM2 : MemNorm.task_mem rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat LI)) [ZERO])).
  { apply (p7_task_munch [(bv_unsigned sp + 320 + Z.of_nat LI, bv_unsigned sp + 320 + Z.of_nat LI + 1)]
             m1 _ TM1).
    - apply (munch_write _ m1 m1 _ _ (munch_refl _ m1)); [lia | cbn [length]; lia |].
      cbn [inside length]. left. lia.
    - intros x Hx. cbn [outside] in Hx.
      assert (Ex : bv_unsigned x = bv_unsigned sp + 320 + Z.of_nat LI) by lia.
      replace x with (wa (bv_unsigned sp + 320 + Z.of_nat LI))
        by (rewrite <- Ex; unfold wa; apply Z_to_bv_bv_unsigned).
      exact HPRES. }
  (* low holds the C string LW *)
  assert (HLOW : cstr_at rsegs (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat LI)) [ZERO])
                   (bv_unsigned sp + 320) LW).
  { exists (firstn LI (upd_bytes LB LI [ZERO])), (skipn (S LI) (upd_bytes LB LI [ZERO])).
    assert (HU : length (upd_bytes LB LI [ZERO]) = 24%nat)
      by (rewrite upd_bytes_length; cbn [length]; lia).
    assert (HNth : nth LI (upd_bytes LB LI [ZERO]) ZERO = ZERO).
    { rewrite (pfc_nth_upd LB LI [ZERO] LI ZERO ltac:(cbn [length]; lia)).
      replace (LI <? LI)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (LI <? LI + length [ZERO])%nat with true
        by (symmetry; apply Nat.ltb_lt; cbn [length]; lia).
      rewrite Nat.sub_diag. reflexivity. }
    assert (HSK : skipn LI (upd_bytes LB LI [ZERO])
                  = ZERO :: skipn (S LI) (upd_bytes LB LI [ZERO])).
    { pose proof (p7_skipn_nth (upd_bytes LB LI [ZERO]) LI ZERO ltac:(lia)) as H.
      rewrite HNth in H. exact H. }
    assert (EFB : firstn LI (upd_bytes LB LI [ZERO]) = firstn LI LB).
    { change (firstn LI (upd_bytes LB LI [ZERO])) with (fld 0 LI (upd_bytes LB LI [ZERO])).
      rewrite (pfc_fld_upd_out LB LI [ZERO] 0 LI ltac:(cbn [length]; lia) ltac:(lia) ltac:(left; lia)).
      reflexivity. }
    split.
    { rewrite <- HSK, firstn_skipn. exact HLB2. }
    split.
    { rewrite EFB, <- HINV. unfold zs. rewrite firstn_map. reflexivity. }
    split; [unfold LW; apply p7_low_nulfree; exact p7_val_nulfree|].
    rewrite length_skipn, HU.
    replace (Z.of_nat (24 - S LI)) with (23 - Z.of_nat LI) by lia.
    replace (Z.of_nat (length LW)) with (Z.of_nat LI) by reflexivity.
    apply p7_slack8; [Z.div_mod_to_equations; lia | lia]. }
  assert (ECP : cat_ptr (sa_catalogue SEG_PLAIN) (by_token LW) =
                match by_token LW with Some i => 0x20ad0 + 296 * Z.of_nat i | None => 0 end)
    by (destruct (by_token LW); reflexivity).
  (* the by_token call *)
  destruct (stk_split rsegs _ lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST2
              ltac:(unfold PARSE_FILE_FRAME; lia)) as [ST2lo ST2hi].
  zstep.
  eapply evt_cut.
  { eapply HBT with (lo := lo) (s := LW).
    rewrite (unsigned_lit (bv_unsigned sp + 320)) by lia.
    split; [lia|]. split; [exact HLOW|]. split; [unfold apart; right; lia|].
    split; [| split; [apply p7_cat; exact MU2 | exact MI2]].
    unfold stack_ok, BY_TOKEN_STACK. split; [exact ST2lo|]. split; [lia|].
    split; [exact HSP16|]. intros a Ha. apply p7_rom. unfold PARSE_FILE_FRAME. lia. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 &
              Ems & MU3 & WM3 & MI3 & ST3 & _).
  subst ms'. rewrite ret_pc_even by (try lia; reflexivity).
  (* the state after by_token *)
  assert (MUw : munch WS m m3).
  { eapply munch_trans; [exact MU2|].
    eapply (munch_weaken [(bv_unsigned sp - BY_TOKEN_STACK, bv_unsigned sp)] WS); [|exact MU3].
    intros x Hx. unfold WS in Hx. cbn [outside] in Hx. unfold BY_TOKEN_STACK. cbn [outside].
    split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM2 WM3) as WMw.
  pose proof (stk_transport_disjoint rsegs _ _ m3 (bv_unsigned sp)
                (bv_unsigned sp + PARSE_FILE_FRAME) ST2hi MU3 WM3
                ltac:(unfold BY_TOKEN_STACK; cbn [disjoint_from]; split; [lia | exact I])) as ST3hi.
  pose proof (stk_merge rsegs m3 lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST3 ST3hi
                ltac:(unfold PARSE_FILE_FRAME; lia)) as ST3f.
  assert (TM3 : MemNorm.task_mem rsegs m3).
  { apply (p7_task_munch [(bv_unsigned sp - BY_TOKEN_STACK, bv_unsigned sp)] _ m3 TM2 MU3).
    intros x Hx. cbn [outside] in Hx. unfold BY_TOKEN_STACK in Hx.
    destruct ST2 as (_ & _ & STa).
    destruct (STa (bv_unsigned x) ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ (bb & Hbb)].
    replace x with (wa (bv_unsigned x)) by (unfold wa; apply Z_to_bv_bv_unsigned).
    rewrite Hbb. discriminate. }
  assert (HLOW3 : cstr_at rsegs m3 (bv_unsigned sp + 320) LW).
  { apply (pfc_cstr_munch [(bv_unsigned sp - BY_TOKEN_STACK, bv_unsigned sp)] _ m3 _ LW HLOW MU3).
    intros x Hx. cbn [outside]. unfold BY_TOKEN_STACK.
    unfold cstr_span in Hx.
    pose proof (Z.mod_pos_bound (- (bv_unsigned sp + 320 + Z.of_nat (length LW) + 1)) 8 ltac:(lia)).
    split; [lia | exact I]. }
  (* the branch on the catalogue answer *)
  rewrite ECP.
  destruct (by_token LW) as [jj|] eqn:EBT.
  - pose proof (p7_by_token_lt LW jj EBT) as Hjj.
    step. if_cases K; zify_cond K; cbv iota.
    + exfalso. lia.
    + refine (p7_hit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jj EBT
                MUw WMw MI3 TM3 ST3f FR1 HF1 HLOW3 HS7).
  - step. if_cases K; zify_cond K; cbv iota.
    + refine (p7_miss _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EBT
                MUw WMw MI3 TM3 ST3f FR1 HF1 HS7).
    + exfalso. apply K. reflexivity.
Qed.

(** 0x150cc, the fold loop: li bytes stored, a0 = val[li] <> 0, a2 = li, a1 = vp + 1. *)
Lemma p7_loop : forall (k li : nat) (ra t0 t1 t2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 : word)
    (b : byte) (m1 : word -> option byte) (fc1 : bv 32) (F1 : bvmap 5 word) (LB : list byte),
  (23 - li <= k)%nat ->
  (li < 23)%nat -> (li < length val)%nat -> bv_unsigned b = nth li val 0 ->
  munch WS m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> MemNorm.task_mem rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc1 ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F1 r = reg_get F r) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x140) LB -> length LB = 24%nat ->
  firstn li (zs LB) = map lower (firstn li val) ->
  s7 = Z_to_bv 64 vp ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (zxb b) (Z_to_bv 64 (vp + 1)) (Z_to_bv 64 (Z.of_nat li))
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 512) s10 s11 t3 t4 t5 t6)
        F1 (Z_to_bv 64 0x150cc) fc1 None m1 (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros li ra t0 t1 t2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 b m1 fc1 F1 LB
           Hk Hli Hlv Hb MU WM MI1 TM1 ST1 FR1 HF1 HLB HLBlen HINV HS7; [lia|].
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (bv_unsigned_in_range 8 b) as RB. change (bv_modulus 8) with 256%Z in RB.
  pose proof (bytes_at_bound rsegs m1 _ _ HLB) as HLBb. rewrite HLBlen in HLBb.
  destruct p7_vb as (VB & HVB & HVBlen & HVBval & HVBsome & HVBz).
  destruct p7_vpin as (HVP1 & HVP2). unfold PF_BUF in HVP1, HVP2.
  (* the value's bytes are kept by this piece's writes *)
  assert (HVB1 : bytes_at rsegs m1 vp VB).
  { apply (pfc_bytes_munch WS m m1 vp VB HVB MU). intros x Hx. rewrite HVBlen in Hx.
    unfold WS. cbn [outside]. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap.
    unfold RC_N, RC_REFUSAL, RC_OVERFLOW.
    destruct Hap as [Hc|Hc]; repeat split; try exact I; lia. }
  (* the folded byte *)
  assert (RL : 0 <= lower (bv_unsigned b) < 256) by (apply p7_lower_range; lia).
  assert (EB : Z_to_bv 64 (bv_unsigned b +
                 Z.shiftl (Z.b2z ((bv_unsigned b + -65) mod 18446744073709551616 <? 26)) 5)
             = zxb (Z_to_bv 8 (lower (bv_unsigned b)))).
  { rewrite (p7_byte_word (lower (bv_unsigned b)) RL). f_equal. apply p7_fold_byte. lia. }
  assert (WRL : wr_at rsegs m1 (bv_unsigned sp + 0x140) 24).
  { apply (p7_wr_of_stk m1 lo (bv_unsigned sp + PARSE_FILE_FRAME));
      [exact ST1 | unfold PARSE_FILE_FRAME; lia | lia | unfold PARSE_FILE_FRAME; lia]. }
  pose proof (wr_at_store_ok rsegs m1 (bv_unsigned sp + 0x140) 24 (Z.of_nat li) 1%nat WRL
                ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as HS.
  do 6 zstep.
  rewrite EB.
  step.
  rewrite le1_zxb.
  (* the new memory and its facts *)
  assert (HLB2 : bytes_at rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])
            (bv_unsigned sp + 320) (upd_bytes LB li [Z_to_bv 8 (lower (bv_unsigned b))])).
  { pose proof (bytes_at_write_inside rsegs m1 (bv_unsigned sp + 320) LB (Z.of_nat li)
                  [Z_to_bv 8 (lower (bv_unsigned b))] HLB ltac:(lia)
                  ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H.
    rewrite Nat2Z.id in H. exact H. }
  assert (MU2 : munch WS m
            (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])).
  { apply (munch_write WS m m1 (bv_unsigned sp + 320 + Z.of_nat li) _ MU);
      [lia | cbn [length]; lia |]. unfold WS. cbn [inside length]. right. left. lia. }
  pose proof (wmono_write rsegs m m1 (wa (bv_unsigned sp + 320 + Z.of_nat li))
                [Z_to_bv 8 (lower (bv_unsigned b))] WM) as WM2.
  pose proof (stk_write rsegs m1 lo (bv_unsigned sp + PARSE_FILE_FRAME)
                (bv_unsigned sp + 320 + Z.of_nat li) [Z_to_bv 8 (lower (bv_unsigned b))] ST1
                ltac:(lia) ltac:(cbn [length]; lia)) as ST2.
  assert (MI2 : mem_inv rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])).
  { apply (mem_inv_store rsegs m1 _ _ MI1). cbn [length]. exact HS. }
  assert (HPRES : mrd rsegs m1 (wa (bv_unsigned sp + 320 + Z.of_nat li)) <> None).
  { destruct HLB as (_ & _ & HLBn). rewrite (HLBn li ltac:(lia)).
    intros C. apply nth_error_None in C. lia. }
  assert (TM2 : MemNorm.task_mem rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])).
  { apply (p7_task_munch [(bv_unsigned sp + 320 + Z.of_nat li, bv_unsigned sp + 320 + Z.of_nat li + 1)]
             m1 _ TM1).
    - apply (munch_write _ m1 m1 _ _ (munch_refl _ m1)); [lia | cbn [length]; lia |].
      cbn [inside length]. left. lia.
    - intros x Hx. cbn [outside] in Hx.
      assert (Ex : bv_unsigned x = bv_unsigned sp + 320 + Z.of_nat li) by lia.
      replace x with (wa (bv_unsigned sp + 320 + Z.of_nat li))
        by (rewrite <- Ex; unfold wa; apply Z_to_bv_bv_unsigned).
      exact HPRES. }
  assert (HVB2 : bytes_at rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 320 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])
            vp VB).
  { apply (bytes_at_write_other rsegs m1 (bv_unsigned sp + 320 + Z.of_nat li)
             [Z_to_bv 8 (lower (bv_unsigned b))] vp VB HVB1);
      [lia | cbn [length]; lia | right; cbn [length]; lia]. }
  (* the invariant after the store *)
  assert (HLEN2 : length (upd_bytes LB li [Z_to_bv 8 (lower (bv_unsigned b))]) = 24%nat)
    by (rewrite upd_bytes_length; cbn [length]; lia).
  assert (HINV2 : firstn (S li) (zs (upd_bytes LB li [Z_to_bv 8 (lower (bv_unsigned b))]))
                  = map lower (firstn (S li) val)).
  { rewrite (firstn_S_snoc li val Hlv), map_app. cbn [map].
    rewrite (firstn_S_snoc li (zs (upd_bytes LB li [Z_to_bv 8 (lower (bv_unsigned b))])))
      by (unfold zs; rewrite length_map, upd_bytes_length; cbn [length]; lia).
    f_equal.
    - rewrite <- HINV. unfold zs. rewrite !firstn_map. f_equal.
      change (firstn li (upd_bytes LB li [Z_to_bv 8 (lower (bv_unsigned b))]))
        with (fld 0 li (upd_bytes LB li [Z_to_bv 8 (lower (bv_unsigned b))])).
      rewrite (pfc_fld_upd_out LB li [Z_to_bv 8 (lower (bv_unsigned b))] 0 li
                 ltac:(cbn [length]; lia) ltac:(lia) ltac:(left; lia)).
      reflexivity.
    - f_equal. unfold zs. change 0%Z with (bv_unsigned ZERO). rewrite map_nth.
      rewrite (pfc_nth_upd LB li [Z_to_bv 8 (lower (bv_unsigned b))] li ZERO ltac:(cbn [length]; lia)).
      replace (li <? li)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (li <? li + length [Z_to_bv 8 (lower (bv_unsigned b))])%nat with true
        by (symmetry; apply Nat.ltb_lt; cbn [length]; lia).
      rewrite Nat.sub_diag. cbn [nth].
      rewrite (p7_unsigned_byte (lower (bv_unsigned b)) RL), Hb. reflexivity. }
  (* the next byte of val *)
  destruct (HVBsome (S li) ltac:(lia)) as [b' Hb'].
  pose proof (bv_unsigned_in_range 8 b') as RB'. change (bv_modulus 8) with 256%Z in RB'.
  assert (RB2 : 0 <= bv_unsigned b' < 2 ^ 64) by lia.
  assert (RD1 : ov_read_bytes rsegs
      (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 320 + Z.of_nat li))
         [Z_to_bv 8 (lower (bv_unsigned b))])
      (Z_to_bv 64 (vp + 1 + Z.of_nat li)) 1 = Some [b']).
  { pose proof (p7_read1 rsegs _ vp VB (S li) b' HVB2 Hb') as H.
    replace (vp + Z.of_nat (S li)) with (vp + 1 + Z.of_nat li) in H by lia.
    exact H. }
  assert (EF : firstn LI val = firstn 23 val).
  { rewrite p7_LI. destruct (Nat.le_gt_cases 23 (length val)) as [Hc|Hc].
    - rewrite Nat.min_l by lia. reflexivity.
    - rewrite Nat.min_r by lia. rewrite (firstn_all2 (n := length val)) by lia.
      rewrite (firstn_all2 (n := 23%nat)) by lia. reflexivity. }
  do 4 zstep.
  if_cases K1; zify_cond K1; cbv iota; rewrite ?(unsigned_lit (bv_unsigned b') RB2) in K1.
  - (* the NUL: the fold ends at S li *)
    assert (E : S li = length val) by (apply (HVBz (S li) b' Hb'); exact K1).
    assert (ELI : LI = S li) by (rewrite p7_LI, <- E; lia).
    replace (Z.of_nat li + 1) with (Z.of_nat LI) by (rewrite ELI; lia).
    refine (p7_zstore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc1 F1 _
              MU2 WM2 MI2 TM2 ST2 FR1 HF1 HLB2 HLEN2 _ HS7).
    rewrite ELI, HINV2, <- ELI, EF. unfold LW. symmetry. apply p7_low_map. exact p7_val_nulfree.
  - (* a byte: either the cap is reached or the loop goes on *)
    assert (E : (S li < length val)%nat).
    { assert (HLe : (S li < length VB)%nat)
        by (apply (proj1 (nth_error_Some VB (S li))); rewrite Hb'; discriminate).
      rewrite HVBlen in HLe.
      destruct (Nat.eq_dec (S li) (length val)) as [Ee|Ee]; [|lia].
      exfalso. apply K1. apply (HVBz (S li) b' Hb'). exact Ee. }
    do 2 zstep.
    if_cases K2; zify_cond K2; cbv iota.
    + (* li + 1 = 23 = LI *)
      assert (ELI : LI = S li).
      { rewrite p7_LI. rewrite Nat.min_l by lia. lia. }
      replace (Z.of_nat li + 1) with (Z.of_nat LI) by (rewrite ELI; lia).
      refine (p7_zstore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc1 F1 _
                MU2 WM2 MI2 TM2 ST2 FR1 HF1 HLB2 HLEN2 _ HS7).
      rewrite ELI, HINV2, <- ELI, EF. unfold LW. symmetry. apply p7_low_map. exact p7_val_nulfree.
    + zstep.
      replace (Z.of_nat li + 1) with (Z.of_nat (S li)) by lia.
      refine (IH (S li) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b' _ fc1 F1 _
                ltac:(lia) ltac:(lia) E (HVBval (S li) b' Hb' E)
                MU2 WM2 MI2 TM2 ST2 FR1 HF1 HLB2 HLEN2 HINV2 HS7).
Qed.

(** 0x150bc, the entry: the first byte of val decides between the empty fold and the loop. *)
Lemma p7_entry : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 : word) (t3 t4 t5 t6 : word),
  s7 = Z_to_bv 64 vp ->
  evt rsegs
    (pf_fin v sp gp tp F m lo c
       (r_lines (r_key rc (Some gi) nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             (Z_to_bv 64 512) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PF_PC_MODEL) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 HS7.
  change (pf_fin v sp gp tp F m lo c
       (r_lines (r_key rc (Some gi) nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
    with Post.
  unfold PF_PC_MODEL.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  destruct p7_vb as (VB & HVB & HVBlen & HVBval & HVBsome & HVBz).
  destruct p7_lowbytes as (LB & HLB & HLBlen).
  destruct (HVBsome 0%nat ltac:(lia)) as [b0 Hb0].
  pose proof (p7_read1 rsegs m vp VB 0%nat b0 HVB Hb0) as RD0.
  cbn [Z.of_nat] in RD0. rewrite Z.add_0_r in RD0.
  subst s7.
  pose proof (munch_refl WS m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b0) as RB0. change (bv_modulus 8) with 256%Z in RB0.
  assert (RB : 0 <= bv_unsigned b0 < 2 ^ 64) by lia.
  step. step.
  if_cases K; zify_cond K; cbv iota; rewrite ?(unsigned_lit (bv_unsigned b0) RB) in K.
  - (* val = [], the fold is empty *)
    assert (Hz : bv_unsigned b0 = 0) by exact K.
    assert (Hnil : val = []).
    { assert (E : (0 = length val)%nat) by (apply (HVBz 0%nat b0 Hb0); exact Hz).
      destruct val as [|x r]; [reflexivity | cbn in E; lia]. }
    step.
    assert (ELI : Z.of_nat LI = 0).
    { rewrite p7_LI, Hnil. cbn [length Nat.min]. reflexivity. }
    rewrite <- ELI.
    apply (p7_zstore ra t0 t1 t2 (zxb b0) a1 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 vp) s8 t3 t4 t5 t6
             m fc F LB MU WM p7_mi p7_tm p7_stk p7_frm (fun k _ => eq_refl) HLB HLBlen
             ltac:(rewrite p7_LI, Hnil; cbn [length Nat.min firstn]; unfold LW; rewrite Hnil; reflexivity)
             eq_refl).
  - (* val <> [], enter the fold loop at li = 0 *)
    assert (Hnz : bv_unsigned b0 <> 0) by exact K.
    assert (Hlt : (0 < length val)%nat).
    { destruct (Nat.eq_dec 0 (length val)) as [E|E]; [|lia].
      exfalso. apply Hnz. apply (HVBz 0%nat b0 Hb0). exact E. }
    step. step.
    apply (p7_loop 23%nat 0%nat ra t0 t1 t2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 vp) s8 t3 t4 t5 t6 b0 m fc F LB
             ltac:(lia) ltac:(lia) Hlt (HVBval 0%nat b0 Hb0 Hlt)
             MU WM p7_mi p7_tm p7_stk p7_frm (fun r _ => eq_refl) HLB HLBlen
             ltac:(cbn [firstn map]; reflexivity) eq_refl).
Qed.

End P7.

Theorem pf_p7_holds : snprintf_contract -> refuse_contract -> reac_box_catalogue_by_token_contract ->
  reac_box_catalogue_contract -> S_P7.
Proof.
  intros HSN HRF HBT HBC. unfold S_P7. intros n HPROVM HS9. unfold H_MODEL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo v c t s rc nm o ln d gi kp vp key val
         HCTX HSTATE HREGS HS9v HS6 HKV HS8 HS7 HNR HMD.
  subst s9.
  destruct HKV as (HSPLIT & HKPat & HKPin & HVPat & HVPin).
  apply (p7_entry sp gp tp s0 s1 s2 s3 s4 s6 s10 s11 F fc m lo v c t s rc nm o ln d gi vp val n
           HSN HRF HBT HBC HPROVM HS9 HCTX HSTATE HREGS HS6 HVPat HVPin
           (p7_r_key rc gi nm (pf_tline s o) key val (ln + 1) HSPLIT HNR HMD)
           ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 HS7).
Qed.
