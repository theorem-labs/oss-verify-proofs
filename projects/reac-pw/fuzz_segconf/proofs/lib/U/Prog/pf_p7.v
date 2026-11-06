(** reac-pw/fuzz_segconf, UBSan build (image 1696d6c34ffd, unstripped twin afc060e3cc9c): piece P7 of
    reac_segconf_parse_file, the model key (lib/U/Prog/reac_segconf_parse_file_pieces_c.v, family F3):
    MODEL (0x156f8) reaches PROVM (0x15b74) when the folded value is a box token, and TAIL (0x156a4)
    after the refusal otherwise. The UBSan twin of lib/Prog/pf_p7.v, written new.

    Code (the UBSan binary, 0x156f8 .. 0x1573c, 0x15908 .. 0x15968, 0x15974 .. 0x15a6c):
      0x156f8 a1 = val[0]; beqz a1 -> 0x15908 (a0 = 0); a0 = 0
      0x15704 .. 0x1573c  the fold into low = sp + 0x190 (cap 24): a2 = val + li; low[li] = lower(a1); trap if
                          a2 == -1 (0x15724, s5 = -1; refuted: val lies in the frame); a1 = val[li + 1]; li++; to
                          0x1590c when a1 == 0 or li > 22
      0x1590c .. 0x15924  trap if ~(sp + 0x190) <u li (0x15910, the spill slot sp + 0x30; refuted); low[li] = 0;
                          `jal reac_box_catalogue_by_token` with a0 = low
      0x15928 beqz a0 -> 0x15974 (miss, lib/U/Prog/pf_p7_miss.v)
      0x1592c .. 0x15968  hit: cur from the slot sp + 0x88, trap if cur & 3 (0x15934; refuted: c mod 16 = 0,
                          356 = 4 * 89); s4 = cur; snprintf(cur + 0x24, 24, "%s" (s7 = 0x104e0), low);
                          cur->model_set = s11 = 1; a0 = cur + 0x40, a1 = 96, a2 = "%s"; `j` PROVM
    The spine step is SegModel.r_key's model branch (pf_p7_lemmas.p7_r_key); the shared helpers are
    lib/U/Prog/pfC_facts.v and lib/Prog/pf_p7_lemmas.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Arr Image Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env printf_facts_c snprintf_c refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_box_catalogue_by_token_c reac_box_catalogue_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import pfC_facts pf_p7_miss.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_p7_lemmas pf_p8_lemmas.
Import ListNotations.
Open Scope Z_scope.

(** The stack region's bytes are writable. *)
Lemma p7u_wr_of_stk : forall m lo hi a k, stk rsegs m lo hi -> lo <= a -> 0 <= k -> a + k <= hi ->
  wr_at rsegs m a k.
Proof.
  intros m lo0 hi a k (H0 & H1 & H) Ha Hk Hle. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

(** UBSan's pointer test `beq a2, s5` with s5 = -1 on a pointer below 2^64 - 1. *)
Lemma p7u_ne_m1 : forall x, 0 <= x < 2 ^ 64 - 1 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite unsigned_lit by lia. apply Z.eqb_neq.
  change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615. lia.
Qed.

(** UBSan's index test `bltu ~p, k` (0x15910) on a buffer p with p + 1 + k <= 2^64. *)
Lemma p7u_not_ltu : forall a k, 0 <= a -> 0 <= k -> a + 1 + k <= 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 (- a - 1)) (Z_to_bv 64 k) = false.
Proof.
  intros a k Ha Hk Hb. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.ltb_ge.
  rewrite (Z.mod_small k) by lia.
  rewrite <- (Z.mod_unique (- a - 1) (2 ^ 64) (-1) (2 ^ 64 - a - 1)) by lia. lia.
Qed.

Section P7U.

Variables (sp gp tp s0 s1 s2 s3 s10 : word).
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variables (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z).
Variables (d : list (list Z)) (gi : nat) (cur vp : Z) (val : list Z) (n : nat).

Hypothesis HSN : snprintf_contract.
Hypothesis HRF : refuse_contract.
Hypothesis HBT : reac_box_catalogue_by_token_contract.
Hypothesis HBC : reac_box_catalogue_contract.
Hypothesis HPROVM : H_PROVM n.
Hypothesis HTAILc : H_TAIL n.
Hypothesis HCTX : pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n.
Hypothesis HSTATE : pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)).
Hypothesis HREGS : pf_regs s0 s1 s2 s3 (Z_to_bv 64 (-1)) s10 (Z_to_bv 64 1) (t + Z.of_nat (pf_next s o)) (ln + 1).
Hypothesis HCS : pf_curslot m (bv_unsigned sp) c (Some gi).
Hypothesis Hcur : cur = rseg_addr c gi.
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

(** The bytes the fold and by_token may write: printf's and the callees' stack below sp, and low. The hit adds
    the c block's seg entries. *)
Definition WS : list ivl :=
  [(bv_unsigned sp - 6032, bv_unsigned sp); (bv_unsigned sp + 0x190, bv_unsigned sp + 0x1a8)].
Definition WP : list ivl :=
  [(bv_unsigned sp - 6032, bv_unsigned sp); (bv_unsigned sp + 0x190, bv_unsigned sp + 0x1a8); (c, c + RC_N + 4)].

(** The folded value and its length. *)
Definition LW : list Z := r_low val 0 24.
Definition LI : nat := length LW.

(** ** Facts of the entry context *)

Lemma p7_env : pf_env m fc (bv_unsigned sp) lo c v.
Proof. exact (proj1 HCTX). Qed.

Lemma p7_lo :
  0 <= lo /\ lo + 6032 <= bv_unsigned sp /\ bv_unsigned sp + 0x420 <= 2 ^ 64 /\
  apart c SEG_C_SIZE lo (bv_unsigned sp + 0x420) /\ 0x54088 <= lo /\ bv_unsigned sp + 0x420 < 2 ^ 63.
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

Lemma p7_gi : (gi < length (rc_seg rc))%nat.
Proof. exact (proj1 (proj2 HSTATE)). Qed.

Lemma p7_val_nulfree : ~ In 0 val.
Proof. destruct HVPat as (bs & sl & _ & _ & H & _). exact H. Qed.

Lemma p7_LI : LI = Nat.min 23 (length val).
Proof. unfold LI, LW. apply p7_low_len. exact p7_val_nulfree. Qed.

Lemma p7_vpin : bv_unsigned sp + PF_BUF <= vp /\ vp + Z.of_nat (length val) < bv_unsigned sp + PF_BUF + 512.
Proof. exact HVPin. Qed.

(** The low buffer's 24 bytes at the entry memory. *)
Lemma p7_lowbytes : exists LB, bytes_at rsegs m (bv_unsigned sp + 0x190) LB /\ length LB = 24%nat.
Proof.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  destruct (stk_split rsegs m lo (bv_unsigned sp + 0x190) (bv_unsigned sp + PARSE_FILE_FRAME) p7_stk
              ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ ST2].
  destruct (stk_split rsegs m (bv_unsigned sp + 0x190) (bv_unsigned sp + 0x1a8)
              (bv_unsigned sp + PARSE_FILE_FRAME) ST2 ltac:(unfold PARSE_FILE_FRAME; lia)) as [ST3 _].
  destruct (stk_bytes rsegs m (bv_unsigned sp + 0x190) (bv_unsigned sp + 0x1a8) ST3 ltac:(lia)) as (LB & HL & HB).
  exists LB. split; [exact HB|]. rewrite HL.
  replace (bv_unsigned sp + 0x1a8 - (bv_unsigned sp + 0x190)) with 24 by lia. reflexivity.
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

(** The spill slot sp + 0x30 (~(sp + 0x190), the operand of the trap test at 0x15910) at a memory the piece
    reached. *)
Lemma p7_lowm_ld : forall m', munch WS m m' ->
  ov_read_bytes rsegs m' (wa (bv_unsigned sp + 48)) 8 = Some (le8 (pf_not (bv_unsigned sp + PF_LOWM))).
Proof.
  intros m' MU. destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof HCTX as (_ & _ & (HS1 & _) & _).
  assert (HS1' : saved_at rsegs m' (bv_unsigned sp + 0x10)
    [Z_to_bv 64 (c + RC_OVERFLOW); Z_to_bv 64 (RSEG_SIZE * 32); Z_to_bv 64 PF_BOX_WORD; Z_to_bv 64 PF_TAP_WORD;
     pf_not (bv_unsigned sp + PF_LOWM); Z_to_bv 64 (c + RC_GEN); pf_not (bv_unsigned sp + PF_LOW); pf_not c;
     Z_to_bv 64 (c + RC_READING); Z_to_bv 64 (c + RC_N)]).
  { unfold saved_at in *. apply (pfc_bytes_munch WS m m' _ _ HS1 MU). rewrite pfc_len_le8s. cbn [length].
    intros x Hx. unfold WS. cbn [outside]. repeat split; try exact I; lia. }
  replace (bv_unsigned sp + 48) with (bv_unsigned sp + 0x10 + 8 * Z.of_nat 4) by lia.
  apply (pfc_saved_ld m' (bv_unsigned sp + 0x10) _ 4 _ HS1'). reflexivity.
Qed.

(** ** The walk *)

Lemma p7_fw_WS : pfc_fw (bv_unsigned sp) lo c WS.
Proof.
  destruct p7_lo as (Hlo0 & Hlo1 & _).
  intros x Hx. unfold WS in Hx. cbn [outside] in Hx. unfold pfc_scr, PF_CURSLOT, PF_SAVE.
  destruct (Z_le_dec (bv_unsigned sp - 6032) x) as [A1|A1];
    destruct (Z_lt_dec x (bv_unsigned sp)) as [A2|A2];
    destruct (Z_le_dec (bv_unsigned sp + 0x190) x) as [A3|A3];
    destruct (Z_lt_dec x (bv_unsigned sp + 0x1a8)) as [A4|A4];
    try (exfalso; apply Hx; split; [lia | split; [lia | exact I]]); lia.
Qed.

Lemma p7_cat : forall m', munch WS m m' -> cat_img rsegs m' (sa_catalogue SA).
Proof.
  intros m' MU a Ha.
  destruct p7_env as (_ & _ & _ & Hni & _ & Hcat & _).
  destruct p7_lo as (Hlo0 & Hlo1 & _ & _ & Hie & _).
  rewrite <- (Hcat a Ha). unfold mrd. rewrite (MU (wa a)); [reflexivity|].
  unfold CAT_BYTES, CAT_ROW, CAT_N in Ha. cbn [sa_catalogue SA SEG_UBSAN] in Ha.
  rewrite wa_unsigned by lia.
  apply (pfc_img_out (bv_unsigned sp) lo c WS a 0x21000 0x2000 p7_fw_WS Hni ltac:(lia));
    [cbn; tauto | lia | lia].
Qed.

Lemma p7_fw_WP : pfc_fw (bv_unsigned sp) lo c WP.
Proof.
  intros x Hx.
  destruct (pfc_outside_dec WS x) as [O|O]; [|exact (p7_fw_WS x O)].
  right. left. unfold WS in O. cbn [outside] in O. unfold WP in Hx. cbn [outside] in Hx.
  unfold SEG_C_SIZE, RC_N in *.
  destruct (Z_le_dec c x) as [B1|B1]; destruct (Z_lt_dec x (c + 16616)) as [B2|B2]; try lia.
  all: exfalso; apply Hx; repeat split; try exact I; lia.
Qed.

Lemma p7_subW : sub_fp WP (pfc_W (bv_unsigned sp) c).
Proof.
  intros x Hx. unfold pfc_W, RC_PARSE_W, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME,
    RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN in Hx. cbn [outside] in Hx.
  unfold WP, RC_N. cbn [outside].
  repeat split; try exact I; lia.
Qed.

Lemma p7_subWS : sub_fp WS (pfc_W (bv_unsigned sp) c).
Proof.
  intros x Hx. unfold pfc_W, RC_PARSE_W, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME in Hx.
  cbn [outside] in Hx. unfold WS. cbn [outside].
  repeat split; try exact I; lia.
Qed.

(** The mid-line context, the reader's state, cur's slot and val at any memory this piece has reached. *)
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
    destruct (STa x ltac:(unfold pfc_scr, PF_CURSLOT, PF_SAVE, PARSE_FILE_FRAME in *; lia)) as [_ H]. exact H.
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

Lemma p7_cs_at : forall (m' : word -> option byte) (W : list ivl), munch W m m' ->
  (forall x, bv_unsigned sp + PF_CURSLOT <= x < bv_unsigned sp + PF_CURSLOT + 8 -> outside W x) ->
  pf_curslot m' (bv_unsigned sp) c (Some gi).
Proof. intros m' W MU HO. exact (pfc_curslot_call m m' fc (bv_unsigned sp) lo c v (Some gi) W p7_env HCS MU HO). Qed.

Lemma p7_val_at : forall (m' : word -> option byte), munch WS m m' -> cstr_at rsegs m' vp val.
Proof.
  intros m' MU. destruct p7_vpin as (HVP1 & HVP2). unfold PF_BUF in HVP1, HVP2.
  apply (pfc_cstr_munch WS m m' vp val HVPat MU). intros x Hx. unfold WS. cbn [outside].
  split; [lia | split; [lia | exact I]].
Qed.

(** The cur slot's word and cur's alignment. *)
Lemma p7_cur : 0 <= cur /\ cur + 356 <= c + SEG_C_SIZE /\ c <= cur /\ cur mod 4 = 0 /\
  cur = c + 356 * Z.of_nat gi.
Proof.
  pose proof HSTATE as (HRC & _). destruct HRC as (bs & HB & HEnc). destruct HEnc as (HL & H32 & _).
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. pose proof p7_gi as Hgi.
  pose proof p7_env as (_ & Hc16 & _).
  assert (E : cur = c + 356 * Z.of_nat gi) by (rewrite Hcur; unfold rseg_addr, RSEG_SIZE; lia).
  unfold SEG_C_SIZE in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact E].
  rewrite E. Z.div_mod_to_equations. lia.
Qed.

Lemma p7_cur_ld : forall m', munch WP m m' ->
  ov_read_bytes rsegs m' (wa (bv_unsigned sp + 136)) 8 = Some (le8 (Z_to_bv 64 cur)).
Proof.
  intros m' MU. destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  assert (HCS' : pf_curslot m' (bv_unsigned sp) c (Some gi)).
  { apply (p7_cs_at m' WP MU). intros x Hx. unfold WP. cbn [outside]. unfold PF_CURSLOT in Hx.
    unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME, RC_N in *.
    destruct Hap as [Hc|Hc]; repeat split; try exact I; lia. }
  pose proof (pfc_ld_cur m' (bv_unsigned sp) c (Some gi) HCS') as X. unfold PF_CURSLOT in X.
  cbn [pf_cur_ptr] in X. rewrite <- Hcur in X. exact X.
Qed.

(** 0x1592c, the hit: cur from its slot, the alignment test, snprintf(cur->model, 24, "%s", low),
    model_set = 1, then PROVM. *)
Lemma p7_hit : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word)
    (m3 : word -> option byte) (fc3 : bv 32) (F3 : bvmap 5 word) (j : nat),
  by_token LW = Some j ->
  munch WS m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 -> MemNorm.task_mem rsegs m3 ->
  stk rsegs m3 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc3 ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F3 r = reg_get F r) ->
  cstr_at rsegs m3 (bv_unsigned sp + 0x190) LW ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (-1)) s6 (Z_to_bv 64 vp) s8
             s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6)
        F3 (Z_to_bv 64 0x1592c) fc3 None m3 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 m3 fc3 F3 j
         EBT MU WM MI3 TM3 ST3 FR3 HF3 HLOW.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  destruct p7_cur as (Hc0 & Hc1 & Hc2 & Hc4 & Ecur).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof p7_sp16 as HSP16. pose proof p7_gi as Hgi.
  assert (MUP : munch WP m m3).
  { eapply (munch_weaken WS WP m m3); [|exact MU].
    intros x Hx. unfold WP in Hx. cbn [outside] in Hx. unfold WS. cbn [outside]. tauto. }
  pose proof (p7_cur_ld m3 MUP) as HRc.
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
  assert (EFL : Z.of_nat (length F_s) = 2) by (vm_compute; reflexivity).
  assert (EFP : pf_parse F_s = Some [Ps]) by (vm_compute; reflexivity).
  assert (EFB : ro_bytes_b rsegs 0x104e0 (pf_bytes (F_s ++ [0])) = true) by (vm_compute; reflexivity).
  assert (EN : bv_unsigned (Z_to_bv 64 24) = 24) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (cur + 36)) = cur + 36) by (apply unsigned_lit; lia).
  assert (EF2 : bv_unsigned (Z_to_bv 64 0x104e0) = 0x104e0) by (apply unsigned_lit; lia).
  assert (EA3 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 400)) = bv_unsigned sp + 400)
    by (apply unsigned_lit; lia).
  (* 0x1592c .. 0x15934: cur from its slot, andi 3, bnez trap *)
  step. step. step. if_cases KA.
  { exfalso. rewrite (p8_and3 cur ltac:(lia) Hc4) in KA. rewrite bv_eqb_refl in KA. cbn [negb] in KA.
    discriminate KA. }
  (* 0x15938 .. 0x15954: s4 = cur, a0 = cur + 0x24, a1 = 24, s7 = a2 = "%s", a3 = low, jal snprintf *)
  do 8 zstep.
  eapply evt_cut.
  { eapply HSN with (lo := bv_unsigned sp - SNPRINTF_K) (fmt := F_s) (ps := [Ps])
                    (args := [APtr LW]) (T := LW) (canary := canary)
                    (junk := fld (Z.to_nat (cur + 36 - c)) 24 bs0).
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
        destruct Hap as [Hc|Hc]; [right; lia | left; unfold cstr_span;
          pose proof (Z.mod_pos_bound (- (bv_unsigned sp + 400 + Z.of_nat (length LW) + 1)) 8 ltac:(lia)); lia].
    - cbn [printf_facts_c.pf_text option_map]. rewrite app_nil_r. reflexivity.
    - rewrite ED, EN. cbn [Z.to_nat].
      exact (pfc_dst_blk m3 c bs0 (cur + 36) 24 HBC0 WRC0 ltac:(lia)
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
  assert (EIDX : Z.to_nat (cur + 36 - c) = (356 * gi + 36)%nat) by lia.
  assert (HBC4 : bytes_at rsegs m4 c (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO]))).
  { rewrite <- EIDX.
    apply (pfc_bytes_patch _ m3 m4 c bs0 (cur + 36) (zb LW ++ [ZERO]) HBC0 MU4 HD4 ltac:(lia)).
    - rewrite HL0, length_app, pfc_len_zb. cbn [length]. lia.
    - intros x Hx Hnx. rewrite HL0 in Hx.
      rewrite length_app, pfc_len_zb in Hnx. cbn [length] in Hnx.
      cbn [outside]. unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap. unfold SNPRINTF_K.
      split; [destruct Hap as [Hc|Hc]; lia | split; [lia | exact I]]. }
  (* the munch, the stack at m4 *)
  assert (MUw4 : munch WP m m4).
  { eapply munch_trans; [exact MUP|].
    eapply (munch_weaken _ WP m3 m4); [|exact MU4].
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
  assert (HS2 : store_ok rsegs m4 (wa (cur + 60)) 4 = true).
  { pose proof (wr_at_store_ok rsegs m4 c SEG_C_SIZE (356 * Z.of_nat gi + 60) 4%nat WRC4
                  ltac:(lia) ltac:(unfold SEG_C_SIZE; cbn [Z.of_nat]; lia)) as H.
    replace (c + (356 * Z.of_nat gi + 60)) with (cur + 60) in H by lia. exact H. }
  zstep.
  assert (HLU : length (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO])) = length bs0).
  { rewrite upd_bytes_length; [reflexivity|]. rewrite length_app, pfc_len_zb. cbn [length]. lia. }
  assert (HBC5 : bytes_at rsegs (write_to_mem m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1))) c
            (upd_bytes (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO])) (356 * gi + 60)
               (le4 (Z_to_bv 64 1)))).
  { pose proof (bytes_at_write_inside rsegs m4 c (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO]))
                  (356 * Z.of_nat gi + 60) (le4 (Z_to_bv 64 1)) HBC4 ltac:(lia)
                  ltac:(rewrite HLU, length_le4; lia)) as H.
    replace (Z.to_nat (356 * Z.of_nat gi + 60)) with (356 * gi + 60)%nat in H by lia.
    replace (c + (356 * Z.of_nat gi + 60)) with (cur + 60) in H by lia.
    exact H. }
  assert (MU5 : munch WP m (write_to_mem m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1)))).
  { apply (munch_write WP m m4 (cur + 60) _ MUw4); [lia | rewrite length_le4; lia |].
    unfold WP. cbn [inside]. rewrite length_le4. unfold RC_N. right. right. left. lia. }
  pose proof (wmono_write rsegs m m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1)) WMw4) as WM5.
  pose proof (stk_write rsegs m4 lo (bv_unsigned sp + PARSE_FILE_FRAME) (cur + 60)
                (le4 (Z_to_bv 64 1)) ST4f ltac:(lia) ltac:(rewrite length_le4; lia)) as ST5.
  assert (MI5 : mem_inv rsegs (write_to_mem m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1)))).
  { apply (mem_inv_store rsegs m4 _ _ MI4). rewrite length_le4. exact HS2. }
  assert (TM5 : MemNorm.task_mem rsegs (write_to_mem m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1)))).
  { apply (pfc_task_mem_munch [(cur + 60, cur + 64)] m4 _ TM4).
    - apply (munch_write _ m4 m4 _ _ (munch_refl _ m4));
        [lia | rewrite length_le4; lia |]. cbn [inside]. rewrite length_le4. left. lia.
    - intros x Hx. apply p8_not_out1 in Hx.
      apply (p8_bytes_present rsegs m4 c _ x HBC4). rewrite HLU. lia. }
  (* the reader's state after the two writes *)
  assert (HRC5 : rconf_at rsegs (write_to_mem m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1)))
            c (pf_prov_mid (PModel LW) rc gi)).
  { exists (upd_bytes (upd_bytes bs0 (356 * gi + 36) (zb LW ++ [ZERO])) (356 * gi + 60)
              (le4 (Z_to_bv 64 1))).
    split; [exact HBC5|].
    apply (pfc_enc_model rc bs0 gi LW HENC0 Hgi ltac:(lia) HLWn HLWb). }
  assert (HST5 : pf_state (write_to_mem m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1)))
            (bv_unsigned sp) c (pf_prov_mid (PModel LW) rc gi) (Some gi) nm (length (skipn o s))).
  { split; [exact HRC5|].
    split; [apply pfc_cur_ok_upd; exact HCUR3|].
    split; [|apply (pfc_cnt_upd rc gi _ (length (skipn o s))); [exact HCNT3 | lia]].
    apply (pfc_nm_call m _ fc (bv_unsigned sp) lo c v nm WP p7_env (proj1 (proj2 (proj2 HSTATE))) MU5).
    intros x Hx. unfold WP. cbn [outside]. unfold PF_NAMEBUF, PF_SAVE in Hx.
    unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in Hap. unfold RC_N.
    destruct Hap as [Hc|Hc]; (split; [lia | split; [lia | split; [lia | exact I]]]). }
  assert (HCTX5 : pf_ctx (write_to_mem m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1)))
            fc4 (bv_unsigned sp) lo v c t s o ln d n)
    by (apply (p7_ctx_at _ fc4 WP p7_fw_WP MU5 WM5 MI5 TM5 ST5 FR4)).
  assert (HCS5 : pf_curslot (write_to_mem m4 (wa (cur + 60)) (le4 (Z_to_bv 64 1))) (bv_unsigned sp) c (Some gi)).
  { apply (p7_cs_at _ WP MU5). intros x Hx. unfold WP. cbn [outside]. unfold PF_CURSLOT in Hx.
    unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME, RC_N in *.
    destruct Hap as [Hc|Hc]; repeat split; try exact I; lia. }
  (* a0 = &cur->model_file, a1 = 96, a2 = "%s", then PROVM *)
  do 4 zstep.
  unfold Post. rewrite HKEY. unfold LW in EBT. rewrite EBT. cbv iota.
  rewrite (p7_snprintf_low val p7_val_nulfree).
  eapply evt_mono.
  { eapply HPROVM.
    - exact HCTX5.
    - exact HST5.
    - exact HREGS.
    - exact HCS5.
    - rewrite <- Hcur. reflexivity.
    - reflexivity.
    - reflexivity. }
  intros ms' Hms'.
  apply (pf_fin_weaken v sp gp tp F F4 m _ lo c _ ms' Hms'
           (munch_weaken WP (pfc_W (bv_unsigned sp) c) m _ p7_subW MU5) WM5 HF4F).
Qed.

(** 0x1590c, the trap test on low + li, the NUL store and the by_token call: a0 = LI and low[0 .. LI) holds the
    fold. *)
Lemma p7_zstore : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word)
    (m1 : word -> option byte) (fc1 : bv 32) (F1 : bvmap 5 word) (LB : list byte),
  munch WS m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> MemNorm.task_mem rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc1 ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x190) LB -> length LB = 24%nat ->
  firstn LI (zs LB) = LW ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat LI)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 (-1)) s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6)
        F1 (Z_to_bv 64 0x1590c) fc1 None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 m1 fc1 F1 LB
         MU WM MI1 TM1 ST1 FR1 HF1 HLB HLBlen HINV.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof p7_sp16 as HSP16.
  assert (HLI : (LI <= 23)%nat) by (rewrite p7_LI; lia).
  pose proof (p7_lowm_ld m1 MU) as HRL. unfold pf_not, PF_LOWM in HRL.
  assert (WRL : wr_at rsegs m1 (bv_unsigned sp + 0x190) 24).
  { apply (p7u_wr_of_stk m1 lo (bv_unsigned sp + PARSE_FILE_FRAME));
      [exact ST1 | unfold PARSE_FILE_FRAME; lia | lia | unfold PARSE_FILE_FRAME; lia]. }
  pose proof (wr_at_store_ok rsegs m1 (bv_unsigned sp + 0x190) 24 (Z.of_nat LI) 1%nat WRL
                ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as HS.
  assert (EZ : le1 (Z_to_bv 64 0) = [ZERO]) by reflexivity.
  (* 0x1590c ld a1, 0x30(sp); 0x15910 bltu a1, a0 -> trap *)
  step. step.
  rewrite (p7u_not_ltu (bv_unsigned sp + 400) (Z.of_nat LI)) by lia. cbv iota.
  (* 0x15914 .. 0x1591c: low[LI] = 0 *)
  do 2 zstep.
  step.
  rewrite EZ.
  (* the memory after low[LI] = 0 *)
  assert (HLB2 : bytes_at rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat LI)) [ZERO])
            (bv_unsigned sp + 400) (upd_bytes LB LI [ZERO])).
  { pose proof (bytes_at_write_inside rsegs m1 (bv_unsigned sp + 400) LB (Z.of_nat LI) [ZERO] HLB
                  ltac:(lia) ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H.
    rewrite Nat2Z.id in H. exact H. }
  assert (MU2 : munch WS m (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat LI)) [ZERO])).
  { apply (munch_write WS m m1 (bv_unsigned sp + 400 + Z.of_nat LI) _ MU);
      [lia | cbn [length]; lia |]. unfold WS. cbn [inside length]. right. left. lia. }
  pose proof (wmono_write rsegs m m1 (wa (bv_unsigned sp + 400 + Z.of_nat LI)) [ZERO] WM) as WM2.
  pose proof (stk_write rsegs m1 lo (bv_unsigned sp + PARSE_FILE_FRAME)
                (bv_unsigned sp + 400 + Z.of_nat LI) [ZERO] ST1 ltac:(lia) ltac:(cbn [length]; lia)) as ST2.
  assert (MI2 : mem_inv rsegs (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat LI)) [ZERO])).
  { apply (mem_inv_store rsegs m1 _ _ MI1). cbn [length]. exact HS. }
  assert (HPRES : mrd rsegs m1 (wa (bv_unsigned sp + 400 + Z.of_nat LI)) <> None).
  { destruct HLB as (_ & _ & HLBn). rewrite (HLBn LI ltac:(lia)).
    intros C. apply nth_error_None in C. lia. }
  assert (TM2 : MemNorm.task_mem rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat LI)) [ZERO])).
  { apply (pfc_task_mem_munch [(bv_unsigned sp + 400 + Z.of_nat LI, bv_unsigned sp + 400 + Z.of_nat LI + 1)]
             m1 _ TM1).
    - apply (munch_write _ m1 m1 _ _ (munch_refl _ m1)); [lia | cbn [length]; lia |].
      cbn [inside length]. left. lia.
    - intros x Hx. apply p8_not_out1 in Hx.
      assert (Ex : bv_unsigned x = bv_unsigned sp + 400 + Z.of_nat LI) by lia.
      replace x with (wa (bv_unsigned sp + 400 + Z.of_nat LI))
        by (rewrite <- Ex; unfold wa; apply Z_to_bv_bv_unsigned).
      exact HPRES. }
  (* low holds the C string LW *)
  assert (HLOW : cstr_at rsegs (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat LI)) [ZERO])
                   (bv_unsigned sp + 400) LW).
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
  assert (ECP : cat_ptr (sa_catalogue SEG_UBSAN) (by_token LW) =
                match by_token LW with Some i => 0x21468 + 296 * Z.of_nat i | None => 0 end)
    by (destruct (by_token LW); reflexivity).
  (* the by_token call *)
  destruct (stk_split rsegs _ lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST2
              ltac:(unfold PARSE_FILE_FRAME; lia)) as [ST2lo ST2hi].
  do 2 zstep.
  eapply evt_cut.
  { eapply HBT with (lo := lo) (s := LW).
    rewrite (unsigned_lit (bv_unsigned sp + 400)) by lia.
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
  { apply (pfc_task_mem_munch [(bv_unsigned sp - BY_TOKEN_STACK, bv_unsigned sp)] _ m3 TM2 MU3).
    intros x Hx. apply p8_not_out1 in Hx. unfold BY_TOKEN_STACK in Hx.
    destruct ST2 as (_ & _ & STa).
    destruct (STa (bv_unsigned x) ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ (bb & Hbb)].
    replace x with (wa (bv_unsigned x)) by (unfold wa; apply Z_to_bv_bv_unsigned).
    rewrite Hbb. discriminate. }
  assert (HLOW3 : cstr_at rsegs m3 (bv_unsigned sp + 400) LW).
  { apply (pfc_cstr_munch [(bv_unsigned sp - BY_TOKEN_STACK, bv_unsigned sp)] _ m3 _ LW HLOW MU3).
    intros x Hx. cbn [outside]. unfold BY_TOKEN_STACK.
    unfold cstr_span in Hx.
    pose proof (Z.mod_pos_bound (- (bv_unsigned sp + 400 + Z.of_nat (length LW) + 1)) 8 ltac:(lia)).
    split; [lia | exact I]. }
  (* the branch on the catalogue answer *)
  rewrite ECP.
  destruct (by_token LW) as [jj|] eqn:EBT.
  - pose proof (p7_by_token_lt LW jj EBT) as Hjj.
    step. if_cases K; zify_cond K; cbv iota.
    + exfalso. lia.
    + refine (p7_hit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jj EBT
                MUw WMw MI3 TM3 ST3f FR1 HF1 HLOW3).
  - step. if_cases K; zify_cond K; cbv iota.
    + (* the miss: lib/U/Prog/pf_p7_miss.v *)
      pose proof (p7_ctx_at m3 fc1 WS p7_fw_WS MUw WMw MI3 TM3 ST3f FR1) as HCTX3.
      pose proof (p7_state_at m3 MUw) as HST3.
      assert (HCS3 : pf_curslot m3 (bv_unsigned sp) c (Some gi)).
      { apply (p7_cs_at m3 WS MUw). intros x Hx. unfold WS. cbn [outside]. unfold PF_CURSLOT in Hx.
        repeat split; try exact I; lia. }
      pose proof (p7_val_at m3 MUw) as HV3.
      unfold Post. rewrite HKEY. unfold LW in EBT. rewrite EBT. cbv iota.
      eapply (p7u_miss HSN HRF HBC n); [exact HTAILc | exact HCTX3 | exact HST3 | exact HREGS | exact HCS3 |
        exact HV3 | exact HVPin | exact (munch_weaken WS (pfc_W (bv_unsigned sp) c) m m3 p7_subWS MUw) |
        exact WMw | exact HF1].
    + exfalso. apply K. reflexivity.
Qed.

(** 0x15704, the fold loop: li bytes stored, a0 = li, a1 = val[li] <> 0. *)
Lemma p7_loop : forall (k li : nat) (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word)
    (b : byte) (m1 : word -> option byte) (fc1 : bv 32) (F1 : bvmap 5 word) (LB : list byte),
  (23 - li <= k)%nat ->
  (li < 23)%nat -> (li < length val)%nat -> bv_unsigned b = nth li val 0 ->
  munch WS m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> MemNorm.task_mem rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + PARSE_FILE_FRAME) -> frm0 fc1 ->
  (forall r : reg, bv_unsigned r <> 10 -> reg_get F1 r = reg_get F r) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x190) LB -> length LB = 24%nat ->
  firstn li (zs LB) = map lower (firstn li val) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat li)) (zxb b) a2
             a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (-1)) s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6)
        F1 (Z_to_bv 64 0x15704) fc1 None m1 (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros li ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 b m1 fc1 F1 LB
           Hk Hli Hlv Hb MU WM MI1 TM1 ST1 FR1 HF1 HLB HLBlen HINV; [lia|].
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (bv_unsigned_in_range 8 b) as RB. change (bv_modulus 8) with 256%Z in RB.
  pose proof (bytes_at_bound rsegs m1 _ _ HLB) as HLBb. rewrite HLBlen in HLBb.
  destruct p7_vb as (VB & HVB & HVBlen & HVBval & HVBsome & HVBz).
  destruct p7_vpin as (HVP1 & HVP2). unfold PF_BUF in HVP1, HVP2.
  (* the value's bytes are kept by this piece's writes *)
  assert (HVB1 : bytes_at rsegs m1 vp VB).
  { apply (pfc_bytes_munch WS m m1 vp VB HVB MU). intros x Hx. rewrite HVBlen in Hx.
    unfold WS. cbn [outside]. repeat split; try exact I; lia. }
  (* the folded byte *)
  assert (RL : 0 <= lower (bv_unsigned b) < 256) by (apply p7_lower_range; lia).
  assert (EB : Z_to_bv 64 (bv_unsigned b +
                 Z.shiftl (Z.b2z ((bv_unsigned b + -65) mod 18446744073709551616 <? 26)) 5)
             = zxb (Z_to_bv 8 (lower (bv_unsigned b)))).
  { rewrite (p7_byte_word (lower (bv_unsigned b)) RL). f_equal. apply p7_fold_byte. lia. }
  assert (WRL : wr_at rsegs m1 (bv_unsigned sp + 0x190) 24).
  { apply (p7u_wr_of_stk m1 lo (bv_unsigned sp + PARSE_FILE_FRAME));
      [exact ST1 | unfold PARSE_FILE_FRAME; lia | lia | unfold PARSE_FILE_FRAME; lia]. }
  pose proof (wr_at_store_ok rsegs m1 (bv_unsigned sp + 0x190) 24 (Z.of_nat li) 1%nat WRL
                ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as HS.
  (* 0x15704 .. 0x1571c: a2 = val + li, a3 = low + li, a1 = lower(val[li]) *)
  do 7 zstep.
  rewrite EB.
  (* 0x15720 sb a1, 0(a3) *)
  step.
  rewrite le1_zxb.
  (* the new memory and its facts *)
  assert (HLB2 : bytes_at rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])
            (bv_unsigned sp + 400) (upd_bytes LB li [Z_to_bv 8 (lower (bv_unsigned b))])).
  { pose proof (bytes_at_write_inside rsegs m1 (bv_unsigned sp + 400) LB (Z.of_nat li)
                  [Z_to_bv 8 (lower (bv_unsigned b))] HLB ltac:(lia)
                  ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H.
    rewrite Nat2Z.id in H. exact H. }
  assert (MU2 : munch WS m
            (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])).
  { apply (munch_write WS m m1 (bv_unsigned sp + 400 + Z.of_nat li) _ MU);
      [lia | cbn [length]; lia |]. unfold WS. cbn [inside length]. right. left. lia. }
  pose proof (wmono_write rsegs m m1 (wa (bv_unsigned sp + 400 + Z.of_nat li))
                [Z_to_bv 8 (lower (bv_unsigned b))] WM) as WM2.
  pose proof (stk_write rsegs m1 lo (bv_unsigned sp + PARSE_FILE_FRAME)
                (bv_unsigned sp + 400 + Z.of_nat li) [Z_to_bv 8 (lower (bv_unsigned b))] ST1
                ltac:(lia) ltac:(cbn [length]; lia)) as ST2.
  assert (MI2 : mem_inv rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])).
  { apply (mem_inv_store rsegs m1 _ _ MI1). cbn [length]. exact HS. }
  assert (HPRES : mrd rsegs m1 (wa (bv_unsigned sp + 400 + Z.of_nat li)) <> None).
  { destruct HLB as (_ & _ & HLBn). rewrite (HLBn li ltac:(lia)).
    intros C. apply nth_error_None in C. lia. }
  assert (TM2 : MemNorm.task_mem rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])).
  { apply (pfc_task_mem_munch [(bv_unsigned sp + 400 + Z.of_nat li, bv_unsigned sp + 400 + Z.of_nat li + 1)]
             m1 _ TM1).
    - apply (munch_write _ m1 m1 _ _ (munch_refl _ m1)); [lia | cbn [length]; lia |].
      cbn [inside length]. left. lia.
    - intros x Hx. apply p8_not_out1 in Hx.
      assert (Ex : bv_unsigned x = bv_unsigned sp + 400 + Z.of_nat li) by lia.
      replace x with (wa (bv_unsigned sp + 400 + Z.of_nat li))
        by (rewrite <- Ex; unfold wa; apply Z_to_bv_bv_unsigned).
      exact HPRES. }
  assert (HVB2 : bytes_at rsegs
            (write_to_mem m1 (wa (bv_unsigned sp + 400 + Z.of_nat li)) [Z_to_bv 8 (lower (bv_unsigned b))])
            vp VB).
  { apply (bytes_at_write_other rsegs m1 (bv_unsigned sp + 400 + Z.of_nat li)
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
  (* 0x15724 beq a2, s5 -> trap: val + li is not -1 *)
  step.
  rewrite (p7u_ne_m1 (vp + Z.of_nat li)) by lia. cbv iota.
  (* the next byte of val *)
  destruct (HVBsome (S li) ltac:(lia)) as [b' Hb'].
  pose proof (bv_unsigned_in_range 8 b') as RB'. change (bv_modulus 8) with 256%Z in RB'.
  assert (RB2 : 0 <= bv_unsigned b' < 2 ^ 64) by lia.
  assert (RD1 : ov_read_bytes rsegs
      (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 400 + Z.of_nat li))
         [Z_to_bv 8 (lower (bv_unsigned b))])
      (Z_to_bv 64 (vp + Z.of_nat li + 1)) 1 = Some [b']).
  { pose proof (p7_read1 rsegs _ vp VB (S li) b' HVB2 Hb') as H.
    replace (vp + Z.of_nat (S li)) with (vp + Z.of_nat li + 1) in H by lia.
    exact H. }
  assert (EF : firstn LI val = firstn 23 val).
  { rewrite p7_LI. destruct (Nat.le_gt_cases 23 (length val)) as [Hc|Hc].
    - rewrite Nat.min_l by lia. reflexivity.
    - rewrite Nat.min_r by lia. rewrite (firstn_all2 (n := length val)) by lia.
      rewrite (firstn_all2 (n := 23%nat)) by lia. reflexivity. }
  (* 0x15728 lbu a1, 1(a2); 0x1572c a0 = li + 1; 0x15730 beqz a1 *)
  do 3 zstep.
  if_cases K1; zify_cond K1; cbv iota; rewrite ?(unsigned_lit (bv_unsigned b') RB2) in K1.
  - (* the NUL: the fold ends at S li *)
    assert (E : S li = length val) by (apply (HVBz (S li) b' Hb'); exact K1).
    assert (ELI : LI = S li) by (rewrite p7_LI, <- E; lia).
    replace (Z.of_nat li + 1) with (Z.of_nat LI) by (rewrite ELI; lia).
    refine (p7_zstore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc1 F1 _
              MU2 WM2 MI2 TM2 ST2 FR1 HF1 HLB2 HLEN2 _).
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
      refine (p7_zstore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc1 F1 _
                MU2 WM2 MI2 TM2 ST2 FR1 HF1 HLB2 HLEN2 _).
      rewrite ELI, HINV2, <- ELI, EF. unfold LW. symmetry. apply p7_low_map. exact p7_val_nulfree.
    + zstep.
      replace (Z.of_nat li + 1) with (Z.of_nat (S li)) by lia.
      refine (IH (S li) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b' _ fc1 F1 _
                ltac:(lia) ltac:(lia) E (HVBval (S li) b' Hb' E)
                MU2 WM2 MI2 TM2 ST2 FR1 HF1 HLB2 HLEN2 HINV2).
Qed.

(** 0x156f8, the entry: the first byte of val decides between the empty fold and the loop. *)
Lemma p7_entry : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 : word) (t3 t4 t5 t6 : word),
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (-1)) s6 (Z_to_bv 64 vp) s8
             s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 PF_PC_MODEL) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6.
  unfold PF_PC_MODEL.
  destruct p7_lo as (Hlo0 & Hlo1 & Hlo2 & Hap & Hie & Hsp63).
  destruct p7_vb as (VB & HVB & HVBlen & HVBval & HVBsome & HVBz).
  destruct p7_lowbytes as (LB & HLB & HLBlen).
  destruct (HVBsome 0%nat ltac:(lia)) as [b0 Hb0].
  pose proof (p7_read1 rsegs m vp VB 0%nat b0 HVB Hb0) as RD0.
  cbn [Z.of_nat] in RD0. rewrite Z.add_0_r in RD0.
  pose proof (munch_refl WS m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b0) as RB0. change (bv_modulus 8) with 256%Z in RB0.
  assert (RB : 0 <= bv_unsigned b0 < 2 ^ 64) by lia.
  step. step.
  if_cases K; zify_cond K; cbv iota; rewrite ?(unsigned_lit (bv_unsigned b0) RB) in K.
  - (* val = [], the fold is empty: 0x15908 a0 = 0 *)
    assert (Hz : bv_unsigned b0 = 0) by exact K.
    assert (Hnil : val = []).
    { assert (E : (0 = length val)%nat) by (apply (HVBz 0%nat b0 Hb0); exact Hz).
      destruct val as [|x r]; [reflexivity | cbn in E; lia]. }
    step.
    assert (ELI : Z.of_nat LI = 0).
    { rewrite p7_LI, Hnil. cbn [length Nat.min]. reflexivity. }
    rewrite <- ELI.
    apply (p7_zstore ra t0 t1 t2 (zxb b0) a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6
             m fc F LB MU WM p7_mi p7_tm p7_stk p7_frm (fun k _ => eq_refl) HLB HLBlen
             ltac:(rewrite p7_LI, Hnil; cbn [length Nat.min firstn]; unfold LW; rewrite Hnil; reflexivity)).
  - (* val <> [], enter the fold loop at li = 0 *)
    assert (Hnz : bv_unsigned b0 <> 0) by exact K.
    assert (Hlt : (0 < length val)%nat).
    { destruct (Nat.eq_dec 0 (length val)) as [E|E]; [|lia].
      exfalso. apply Hnz. apply (HVBz 0%nat b0 Hb0). exact E. }
    step.
    apply (p7_loop 23%nat 0%nat ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 b0 m fc F LB
             ltac:(lia) ltac:(lia) Hlt (HVBval 0%nat b0 Hb0 Hlt)
             MU WM p7_mi p7_tm p7_stk p7_frm (fun r _ => eq_refl) HLB HLBlen
             ltac:(cbn [firstn map]; reflexivity)).
Qed.

End P7U.

Theorem pf_p7_holds : snprintf_contract -> refuse_contract -> reac_box_catalogue_by_token_contract ->
  reac_box_catalogue_contract -> S_P7.
Proof.
  intros HSN HRF HBT HBC. unfold S_P7. intros n HPROVM HTAIL. unfold H_MODEL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo v c t s rc nm o ln d gi kp vp key val
         HCTX HSTATE HREGS HCS HKV HS8 HS7 HNR HMD.
  destruct HKV as (HSPLIT & HKPat & HKPin & HVPat & HVPin).
  pose proof HREGS as (_ & _ & _ & _ & E5 & _ & E11).
  subst s5 s7 s11.
  eapply (p7_entry sp gp tp s0 s1 s2 s3 s10 F fc m lo v c t s rc nm o ln d gi (rseg_addr c gi) vp val n);
    try eassumption; try reflexivity.
  exact (p7_r_key rc gi nm (pf_tline s o) key val (ln + 1) HSPLIT HNR HMD).
Qed.
