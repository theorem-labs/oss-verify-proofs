(** m_file (plain build, image 3776ca44d75c): the lemmas every walk of m_file's pieces shares:
    the loop facts split in three (frame/context, text, model state), their transport across a callee or a frame
    store, the text's bytes, the tail's loop facts for the next line, the post moved back over the line's writes,
    the write-list inclusions, and two call-site lemmas (m_refuse at any of its six sites, snprintf(D, 96, "%s", s)
    at its three sites). Cut text: Prog/mf_cuts.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c mf_cuts
  mfu_facts m_refuse_c printf_facts_c snprintf_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Helpers (prefix mfc_): byte lists, write lists, the image's reserved segments *)
Lemma mfc_zb_zs : forall bs, zb (zs bs) = bs.
Proof.
  unfold zb, zs. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma mfc_zs_byte : forall bs, Forall (fun x => 0 <= x < 256) (zs bs).
Proof.
  intros bs. unfold zs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb. lia.
Qed.

Lemma mfc_firstn_map : forall {A B} (f : A -> B) n l, firstn n (map f l) = map f (firstn n l).
Proof. intros A B f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma mfc_skipn_map : forall {A B} (f : A -> B) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros A B f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma mfc_len_le8s : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia.
Qed.

Lemma mfc_bytes_pre : forall m a (l1 l2 : list byte), bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m a l1.
Proof. intros m a l1 l2 H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma mfc_bytes_sub : forall m a (l : list byte) o k, bytes_at rsegs m a l -> (o + k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat o) (firstn k (skipn o l)).
Proof.
  intros m a l o k B H.
  rewrite <- (firstn_skipn o l) in B. apply bytes_at_app in B as [_ B].
  rewrite length_firstn in B. replace (Nat.min o (length l)) with o in B by lia.
  rewrite <- (firstn_skipn k (skipn o l)) in B. exact (mfc_bytes_pre _ _ _ _ B).
Qed.

(** Bytes outside every range of a write list W' that contains W keep their values. *)
Lemma mfc_bytes_tr : forall W W' m m' a bs, bytes_at rsegs m a bs -> munch W m m' -> sub_fp W W' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W' x) -> bytes_at rsegs m' a bs.
Proof.
  intros W W' m m' a bs (Ha & Hl & H) MU SF HO. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite MU.
  - exact (H i Hi).
  - apply SF. rewrite wa_unsigned by lia. apply HO. lia.
Qed.

Lemma mfc_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi);
    [right; intros [H' _]; lia | left; split; [lia | exact H] ..].
Qed.

Lemma mfc_task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd rsegs m x <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU P x b Hx.
  destruct (mfc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (m x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (MemNorm.seg_rom_unmapped rsegs x Hf).
Qed.

Lemma mfc_outside_in : forall W lo hi x, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  induction W as [|[a b] W IH]; intros lo hi x Ho Hin; [destruct Hin|].
  cbn [outside] in Ho. destruct Ho as [H1 H2]. destruct Hin as [E|Hin].
  - injection E as <- <-. exact H1.
  - exact (IH lo hi x H2 Hin).
Qed.

Lemma mfc_outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[a b] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto.
Qed.

(** A reserved segment of the image that covers [A, B): no byte of a block free of the image lies there. *)
Lemma mfc_resv_cover : forall A B, existsb (fun s : word * word => (bv_unsigned (fst s) <=? A) &&
    (B <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true ->
  forall a n x, blk_noimg rsegs a n -> A <= x < B -> ~ (a <= x < a + n).
Proof.
  intros A B H a n x HN Hx Ha.
  apply existsb_exists in H as (s & Hs & E). apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  apply (HN (x - a) ltac:(lia) s Hs). lia.
Qed.

(** .data.rel.ro, the GOT and .bss of the image ([0x20000, 0x22000) and [0x22000, 0x54000), two reserved
    segments): never in a block free of the image. *)
Lemma mfc_img_out_c : forall a n x, blk_noimg rsegs a n -> 0x20000 <= x < 0x54000 -> ~ (a <= x < a + n).
Proof.
  intros a n x HN Hx. destruct (Z_lt_dec x 0x22000) as [Hlt|Hge].
  - apply (mfc_resv_cover 0x20000 0x22000); [vm_compute; reflexivity | exact HN | lia].
  - apply (mfc_resv_cover 0x22000 0x54000); [vm_compute; reflexivity | exact HN | lia].
Qed.

Lemma mfc_noimg_sub : forall c N a n, blk_noimg rsegs c N -> c <= a -> a + n <= c + N -> blk_noimg rsegs a n.
Proof.
  intros c N a n H H1 H2 i Hi s Hs. replace (a + i) with (c + (a - c + i)) by lia. apply H; [lia | exact Hs].
Qed.

(** struct mconf is 9236 bytes in a 16-aligned block: its slack to the next 8-byte boundary is 4 bytes. *)
Lemma mfc_slack4 : forall a, a mod 16 = 0 -> (- (a + SEG_M_SIZE)) mod 8 = 4.
Proof.
  intros a Ha. unfold SEG_M_SIZE.
  assert (Ec : a = 8 * (a / 8)).
  { assert (H8 : a mod 8 = 0) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
  replace (- (a + 9236)) with ((- 9236) + (- (a / 8)) * 8) by lia.
  rewrite Z.mod_add by lia. vm_compute. reflexivity.
Qed.

Lemma mfc_slack_end : forall m c, c mod 16 = 0 -> blk_slack rsegs m c SEG_M_SIZE -> c + SEG_M_SIZE + 8 <= 2 ^ 64.
Proof.
  intros m c H16 (sl & B & Hsl). rewrite (mfc_slack4 c H16) in Hsl.
  pose proof (bytes_at_bound _ _ _ _ B) as [_ Bl]. unfold SEG_M_SIZE in *.
  assert (Ec : c = 16 * (c / 16)) by (Z.div_mod_to_equations; lia).
  lia.
Qed.

Lemma mfc_sp_mod16 : forall sp sp0, sp + M_FILE_FRAME = sp0 -> sp0 mod 16 = 0 -> sp mod 16 = 0.
Proof.
  intros sp sp0 H1 H2. unfold M_FILE_FRAME in H1.
  replace sp with (sp0 + (-13) * 16) by lia. rewrite Z.mod_add by lia. exact H2.
Qed.

Lemma mfc_slack_tr : forall W W' m m' c, c mod 16 = 0 -> blk_slack rsegs m c SEG_M_SIZE -> munch W m m' ->
  sub_fp W W' -> (forall x, c + SEG_M_SIZE <= x < c + SEG_M_SIZE + 4 -> outside W' x) ->
  blk_slack rsegs m' c SEG_M_SIZE.
Proof.
  intros W W' m m' c H16 (sl & B & Hsl) MU SF HO.
  pose proof (mfc_slack4 c H16) as E4. rewrite E4 in Hsl.
  exists (firstn 4 sl). rewrite E4. split.
  - rewrite <- (firstn_skipn 4 sl) in B. apply mfc_bytes_pre in B.
    apply (mfc_bytes_tr W W' m m' _ _ B MU SF). rewrite length_firstn. intros x Hx. apply HO. lia.
  - rewrite length_firstn. lia.
Qed.

(** The C string at a keeps its bytes when its span [a, a + cstr_span a s) is outside W'. *)
Lemma mfc_cstr_tr : forall W W' m m' a s, cstr_at rsegs m a s -> munch W m m' -> sub_fp W W' ->
  (forall x, a <= x < a + cstr_span a s -> outside W' x) -> cstr_at rsegs m' a s.
Proof.
  intros W W' m m' a s (bs & sl & B & Hz & Hn & Hsl) MU SF HO.
  unfold cstr_span in HO.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hk.
  revert Hk Hsl HO.
  remember ((- (a + Z.of_nat (length s) + 1)) mod 8) as k eqn:Ek.
  intros Hk Hsl HO.
  assert (Hlen : length bs = length s) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  exists bs, (firstn (Z.to_nat k) sl). split; [|split; [exact Hz | split; [exact Hn|]]].
  - rewrite <- (firstn_skipn (Z.to_nat k) sl) in B.
    assert (B' : bytes_at rsegs m a ((bs ++ ZERO :: firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl))
      by (rewrite <- app_assoc; exact B).
    apply mfc_bytes_pre in B'.
    apply (mfc_bytes_tr W W' m m' a _ B' MU SF).
    intros x Hx. apply HO. rewrite length_app in Hx. cbn [length] in Hx. rewrite length_firstn in Hx. lia.
  - rewrite <- Ek, length_firstn. lia.
Qed.

(** The frame cells, the block's slack and the image's bytes lie outside the writes a callee or a store of the
    walk makes: [lo, sp), the scratch cells [sp + 0x20, sp + 0x68) and c. *)
Lemma mfc_out_frame : forall lo sp sp0 c x, sp + M_FILE_FRAME = sp0 -> lo + M_FILE_STACK <= sp0 ->
  apart c (SEG_M_SIZE + 4) lo sp0 -> (sp + 8 <= x < sp + 0x20 \/ sp + 0x68 <= x < sp0) ->
  outside [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)] x.
Proof.
  intros lo sp sp0 c x H1 H2 H3 Hx. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K, apart, SEG_M_SIZE in *.
  cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma mfc_out_slack : forall lo sp sp0 c x, sp + M_FILE_FRAME = sp0 -> lo + M_FILE_STACK <= sp0 ->
  apart c (SEG_M_SIZE + 4) lo sp0 -> c + SEG_M_SIZE <= x < c + SEG_M_SIZE + 4 ->
  outside [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)] x.
Proof.
  intros lo sp sp0 c x H1 H2 H3 Hx. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K, apart, SEG_M_SIZE in *.
  cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma mfc_out_img : forall lo sp sp0 c x, sa_img_end SA <= lo -> lo + M_FILE_STACK <= sp0 ->
  sp + M_FILE_FRAME = sp0 -> blk_noimg rsegs c SEG_M_SIZE -> 0x20000 <= x < 0x536e8 ->
  outside [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)] x.
Proof.
  intros lo sp sp0 c x H1 H2 H3 HN Hx.
  change (sa_img_end SA) with 0x536e8 in H1.
  pose proof (mfc_img_out_c c SEG_M_SIZE x HN ltac:(lia)) as Hc.
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in *.
  cbn [outside]. split; [lia|]. split; [lia|]. split; [exact Hc | exact I].
Qed.

Lemma mfc_W3_W2 : forall lo sp sp0 c, lo <= sp -> sp + 0x68 <= sp0 ->
  sub_fp [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)] [(lo, sp0); (c, c + SEG_M_SIZE)].
Proof.
  intros lo sp sp0 c H1 H2 x Hx. cbn [outside] in *. destruct Hx as (X1 & X2 & _).
  split; [lia|]. split; [lia|]. split; [exact X2 | exact I].
Qed.

(** ** The loop facts in three parts *)
(** The frame and the environment: sp0, the saved registers, the three constant cells, the block c (placement,
    writable, slack), printf's machine, the two tables, the stack region, mem_inv. A callee or a store that writes
    only below sp, in the scratch cells [sp + 0x20, sp + 0x68) (cur and low) or in c keeps it (mf_ctx_transport). *)
Definition mf_ctx (m : word -> option byte) (fc : bv 32) (sp0 sp lo c : Z)
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) : Prop :=
  sp + M_FILE_FRAME = sp0 /\
  saved_at rsegs m (sp + M_FILE_SAVE) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] /\
  cell8 m (sp + 0x8) (c + MC_KNOCK) /\ cell8 m (sp + 0x10) (c + MC_N) /\ cell8 m (sp + 0x18) (c + MC_READING) /\
  c <> 0 /\ c mod 16 = 0 /\ blk_noimg rsegs c SEG_M_SIZE /\
  wr_at rsegs m c SEG_M_SIZE /\ blk_slack rsegs m c SEG_M_SIZE /\ apart c (SEG_M_SIZE + 4) lo sp0 /\
  printf_env m fc lo sp0 /\ cat_img rsegs m (sa_catalogue SA) /\ words_img m /\
  stack_ok rsegs m lo sp0 M_FILE_STACK /\ mem_inv rsegs m.

(** The text left: the C string rest at p, outside the image, apart from the stack region and from c. *)
Definition mf_text (m : word -> option byte) (sp0 lo c p : Z) (rest : list Z) : Prop :=
  p <> 0 /\ blk_noimg rsegs p (Z.of_nat (length rest) + 1) /\ cstr_at rsegs m p rest /\
  apart p (Z.of_nat (length rest) + 8) lo sp0 /\ apart p (cstr_span p rest) c (c + SEG_M_SIZE).

(** The model state: c holds mc, the cur cell holds cur, the bounds. *)
Definition mf_st (m : word -> option byte) (sp c : Z) (mc : mconf) (cur : option nat) (k0 : nat) (line : Z)
    (rest : list Z) : Prop :=
  mconf_at rsegs m c mc /\ cell8 m (sp + 0x20) (cur_ptr c cur) /\ cur_ok mc cur /\
  (k0 <= length (mc_kept mc))%nat /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\
  mc_refused mc + Z.of_nat (length rest) < 2 ^ 32 /\ mc_overflow mc + Z.of_nat (length rest) < 2 ^ 32.

Lemma mf_loop_iff : forall m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 <->
  mf_ctx m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 /\ mf_text m sp0 lo c p rest /\
  mf_st m sp c mc cur k0 line rest.
Proof.
  intros. unfold m_file_loop, mf_ctx, mf_text, mf_st. split; intros H;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** Arithmetic the context gives. *)
Lemma mf_ctx_bounds : forall m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  mf_ctx m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  sa_img_end SA <= lo /\ lo + M_FILE_STACK <= sp0 /\ sp0 < 2 ^ 63 /\ sp0 mod 16 = 0 /\ sp mod 16 = 0 /\
  (c + SEG_M_SIZE + 4 <= lo \/ sp0 <= c) /\ 0 < c /\ c + SEG_M_SIZE + 8 <= 2 ^ 64.
Proof.
  intros m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    (HF & _ & _ & _ & _ & HC0 & HC16 & _ & HWR & HSL & HAP & HENV & _ & _ & HST & _).
  destruct HENV as (_ & _ & _ & HIMG & HSP).
  destruct HST as (_ & HDEP & HSP16 & _).
  destruct HWR as (HWc & _ & _).
  pose proof (mfc_slack_end m c HC16 HSL) as HEND.
  pose proof (mfc_sp_mod16 sp sp0 HF HSP16) as HS16.
  unfold apart in HAP.
  split; [exact HIMG|]. split; [exact HDEP|]. split; [exact HSP|]. split; [exact HSP16|].
  split; [exact HS16|]. split; [lia|]. split; [lia | exact HEND].
Qed.

(** ** Transport *)
(** The new memory is in the task's range when the writes hit only bytes that were present: the stack region,
    the scratch cells and c. *)
Lemma mf_task_mem : forall m m' fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 pend mc W,
  mf_ctx m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 -> mconf_atp rsegs pend m c mc ->
  munch W m m' -> sub_fp W [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)] ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros m m' fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 pend mc W HC HMC MU SF.
  destruct HC as (HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAP & HENV & _ & _ & HST & _).
  destruct HENV as (_ & TM & _ & _ & _).
  destruct HST as ((_ & _ & STK) & HDEP & _ & _).
  destruct HMC as (bs & B & HE). destruct HE as (HLb & _).
  apply (mfc_task_mem_munch W m m' TM MU).
  intros x Hx.
  assert (Hx' : ~ outside [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)] (bv_unsigned x))
    by (intros H; apply Hx; apply SF; exact H).
  cbn [outside] in Hx'.
  assert (E : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HF, HDEP.
  assert (HIN : lo <= bv_unsigned x < sp0 \/ c <= bv_unsigned x < c + SEG_M_SIZE) by lia.
  clear Hx'.
  destruct HIN as [Hs | Hb].
  - destruct (STK (bv_unsigned x) Hs) as [_ (b & Hb')]. rewrite E in Hb'. rewrite Hb'. discriminate.
  - destruct B as (_ & _ & Bb). rewrite <- E.
    replace (bv_unsigned x) with (c + Z.of_nat (Z.to_nat (bv_unsigned x - c))) by lia.
    unfold SEG_M_SIZE in *.
    rewrite Bb by lia. intros C. apply nth_error_None in C. lia.
Qed.

(** The stack region after a callee: the callee keeps [lo, its sp); the frame [sp, sp0) is not in its W. *)
Lemma mf_stk_after : forall m m' lo sp sp0 W,
  stk rsegs m lo sp0 -> munch W m m' -> wmono rsegs m m' -> stk rsegs m' lo sp -> sp <= sp0 ->
  disjoint_from W sp (sp0 - sp) -> stk rsegs m' lo sp0.
Proof.
  intros m m' lo sp sp0 W (S0 & S1 & SS) MU WM (T0 & T1 & TT) Hle DJ.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (Z_lt_dec a sp) as [Hlt|Hge].
  - apply TT. lia.
  - destruct (SS a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
    exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. eapply disjoint_outside; [exact DJ|]. lia.
Qed.

Lemma mf_ctx_transport : forall m m' fc fc' sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 W,
  mf_ctx m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> frm0 fc' ->
  stk rsegs m' lo sp0 ->
  sub_fp W [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)] ->
  mf_ctx m' fc' sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m m' fc fc' sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 W HC MU WM MI TM FRM STK SF.
  pose proof (mf_ctx_bounds m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 HC)
    as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  destruct HC as (HF & HSV & HK1 & HK2 & HK3 & HC0 & HC16 & HNI & HWR & HSL & HAP & HENV & HCAT & HWD & HST & HMI).
  destruct HENV as (_ & _ & (SG1 & g & SG2) & HIMG & HSP).
  destruct HST as (_ & HDEP & HSP16 & HNR).
  unfold mf_ctx.
  split; [exact HF|].
  split.
  { unfold saved_at in *. apply (mfc_bytes_tr W _ m m' _ _ HSV MU SF).
    rewrite mfc_len_le8s. cbn [length]. intros x Hx. apply (mfc_out_frame lo sp sp0 c x HF B2 HAP).
    right. unfold M_FILE_SAVE, M_FILE_FRAME in *. lia. }
  split.
  { unfold cell8 in *. apply (mfc_bytes_tr W _ m m' _ _ HK1 MU SF). rewrite length_le8. intros x Hx.
    apply (mfc_out_frame lo sp sp0 c x HF B2 HAP). left. lia. }
  split.
  { unfold cell8 in *. apply (mfc_bytes_tr W _ m m' _ _ HK2 MU SF). rewrite length_le8. intros x Hx.
    apply (mfc_out_frame lo sp sp0 c x HF B2 HAP). left. lia. }
  split.
  { unfold cell8 in *. apply (mfc_bytes_tr W _ m m' _ _ HK3 MU SF). rewrite length_le8. intros x Hx.
    apply (mfc_out_frame lo sp sp0 c x HF B2 HAP). left. lia. }
  split; [exact HC0|]. split; [exact HC16|]. split; [exact HNI|].
  split; [exact (wr_at_transport rsegs m m' c SEG_M_SIZE HWR WM)|].
  split.
  { apply (mfc_slack_tr W _ m m' c HC16 HSL MU SF). intros x Hx. exact (mfc_out_slack lo sp sp0 c x HF B2 HAP Hx). }
  split; [exact HAP|].
  split.
  { split; [exact FRM|]. split; [exact TM|]. split; [|split; [exact HIMG | exact HSP]].
    split.
    - apply (mfc_bytes_tr W _ m m' _ _ SG1 MU SF). rewrite length_le8. intros x Hx.
      apply (mfc_out_img lo sp sp0 c x HIMG B2 HF HNI). change (sa_got_guard SA) with 0x21818 in Hx. lia.
    - exists g. apply (mfc_bytes_tr W _ m m' _ _ SG2 MU SF). rewrite length_le8. intros x Hx.
      apply (mfc_out_img lo sp sp0 c x HIMG B2 HF HNI). change (sa_guard SA) with 0x52e80 in Hx. lia. }
  split.
  { intros a Ha. pose proof Ha as Ha'. change (sa_catalogue SA) with 0x20ad0 in Ha'. unfold CAT_BYTES in Ha'.
    transitivity (mrd rsegs m (wa a)); [|exact (HCAT a Ha)].
    unfold mrd. rewrite MU; [reflexivity|]. apply SF. rewrite wa_unsigned by lia.
    apply (mfc_out_img lo sp sp0 c a HIMG B2 HF HNI). lia. }
  split.
  { intros a Ha. pose proof Ha as Ha'. unfold M_KEY_WORDS in Ha'.
    transitivity (mrd rsegs m (wa a)); [|exact (HWD a Ha)].
    unfold mrd. rewrite MU; [reflexivity|]. apply SF. rewrite wa_unsigned by lia.
    apply (mfc_out_img lo sp sp0 c a HIMG B2 HF HNI). lia. }
  split; [split; [exact STK|]; split; [exact HDEP|]; split; [exact HSP16 | exact HNR]|].
  exact MI.
Qed.

Lemma mf_text_transport : forall m m' sp0 lo c p rest W,
  mf_text m sp0 lo c p rest -> munch W m m' -> sub_fp W [(lo, sp0); (c, c + SEG_M_SIZE)] ->
  mf_text m' sp0 lo c p rest.
Proof.
  intros m m' sp0 lo c p rest W HT MU SF.
  assert (Hsp : cstr_span p rest <= Z.of_nat (length rest) + 8).
  { destruct HT as (_ & _ & (bs & sl & _ & _ & _ & _) & _ & _). unfold cstr_span.
    pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)). lia. }
  destruct HT as (H0 & HNI & HS & A1 & A2).
  split; [exact H0|]. split; [exact HNI|]. split; [|split; [exact A1 | exact A2]].
  apply (mfc_cstr_tr W [(lo, sp0); (c, c + SEG_M_SIZE)] m m' p rest HS MU SF).
  intros x Hx. cbn [outside]. unfold apart in A1, A2. split; [lia|]. split; [lia | exact I].
Qed.

(** A cell of the frame outside W keeps its bytes (the cur cell across a callee). *)
Lemma cell8_transport : forall m m' a v W,
  cell8 m a v -> munch W m m' -> disjoint_from W a 8 -> cell8 m' a v.
Proof.
  intros m m' a v W H MU D. unfold cell8 in *. eapply bytes_at_transport; [exact H | exact MU |].
  rewrite length_le8. exact D.
Qed.

(** ** The text's bytes *)
Lemma mf_text_props : forall m sp0 lo c p rest, mf_text m sp0 lo c p rest ->
  ~ In 0 rest /\ Forall (fun x => 0 <= x < 256) rest /\ 0 < p /\ p + cstr_span p rest <= 2 ^ 64 /\
  (cstr_span p rest <= Z.of_nat (length rest) + 8).
Proof.
  intros m sp0 lo c p rest (H0 & _ & (bs & sl & B & Hz & Hn & Hsl) & _ & _).
  pose proof (bytes_at_bound _ _ _ _ B) as [Bp Bl].
  rewrite length_app in Bl. cbn [length] in Bl.
  assert (Hlen : length bs = length rest) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)) as Hk.
  split; [exact Hn|]. split; [rewrite <- Hz; apply mfc_zs_byte|].
  split; [lia|]. unfold cstr_span. split; lia.
Qed.

Lemma mfc_nth_text : forall rest (sl : list byte) i, (i <= length rest)%nat ->
  firstn 1 (skipn i (zb rest ++ ZERO :: sl)) = [Z_to_bv 8 (nth i rest 0)].
Proof.
  induction rest as [|x r IH]; intros sl [|i] Hi; cbn [length] in Hi.
  - reflexivity.
  - lia.
  - reflexivity.
  - cbn [zb map app skipn nth]. apply IH. lia.
Qed.

(** Byte i of the text (i = length rest is its NUL). *)
Lemma mf_text_byte : forall m sp0 lo c p rest i, mf_text m sp0 lo c p rest -> (i <= length rest)%nat ->
  ov_read_bytes rsegs m (wa (p + Z.of_nat i)) 1 = Some [Z_to_bv 8 (nth i rest 0)].
Proof.
  intros m sp0 lo c p rest i (H0 & _ & (bs & sl & B & Hz & Hn & Hsl) & _ & _) Hi.
  assert (Hlen : length bs = length rest) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  assert (Ezb : bs = zb rest) by (rewrite <- Hz; symmetry; apply mfc_zb_zs).
  rewrite (bytes_at_ov_read rsegs m p (bs ++ ZERO :: sl) i 1 B) by (rewrite length_app; cbn [length]; lia).
  rewrite Ezb. f_equal. apply mfc_nth_text. exact Hi.
Qed.

(** The k bytes at offset o (a range a callee reads: memchr, ieq, m_find, memcpy, bcmp). *)
Lemma mf_text_bytes : forall m sp0 lo c p rest o k, mf_text m sp0 lo c p rest -> (o + k <= length rest)%nat ->
  bytes_at rsegs m (p + Z.of_nat o) (zb (firstn k (skipn o rest))).
Proof.
  intros m sp0 lo c p rest o k (H0 & _ & (bs & sl & B & Hz & Hn & Hsl) & _ & _) Hok.
  assert (Ezb : bs = zb rest) by (rewrite <- Hz; symmetry; apply mfc_zb_zs).
  rewrite Ezb in B. apply mfc_bytes_pre in B.
  unfold zb. rewrite <- mfc_firstn_map, <- mfc_skipn_map.
  apply mfc_bytes_sub; [exact B|]. rewrite length_map. exact Hok.
Qed.

(** The C string from offset o, with the text's slack (strchr, strlen). *)
Lemma mf_text_cstr : forall m sp0 lo c p rest o, mf_text m sp0 lo c p rest -> (o <= length rest)%nat ->
  cstr_at rsegs m (p + Z.of_nat o) (skipn o rest).
Proof.
  intros m sp0 lo c p rest o (H0 & _ & (bs & sl & B & Hz & Hn & Hsl) & _ & _) Ho.
  assert (Hlen : length bs = length rest) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  exists (skipn o bs), sl. split; [|split; [|split]].
  - rewrite <- (firstn_skipn o bs) in B. rewrite <- app_assoc in B. apply bytes_at_app in B as [_ B].
    rewrite length_firstn in B. replace (Nat.min o (length bs)) with o in B by lia. exact B.
  - rewrite <- Hz. unfold zs. symmetry. apply mfc_skipn_map.
  - intros Hin. apply Hn. rewrite <- (firstn_skipn o rest). apply in_or_app. right. exact Hin.
  - rewrite length_skipn.
    replace (p + Z.of_nat o + Z.of_nat (length rest - o) + 1) with (p + Z.of_nat (length rest) + 1) by lia.
    exact Hsl.
Qed.

(** ** The line (the list facts are Prog/mfu_facts.v: lines_cons, break_nl_spec, mf_rest_lt, mf_line_rest,
    mf_fin_head for the head's post) *)

Lemma mf_next_eq : forall p rest, rest <> [] ->
  (mf_rest rest <> [] -> mf_next p rest = p + Z.of_nat (length (mf_line rest)) + 1) /\
  (mf_next p rest = p + Z.of_nat (length (mf_line rest)) \/ mf_next p rest = p + Z.of_nat (length (mf_line rest)) + 1).
Proof.
  intros p rest _. unfold mf_next.
  destruct (mf_line_rest rest) as [[E L] | (E1 & E2 & L)]; rewrite L.
  - split; [intros _; lia | right; lia].
  - split; [intros H; congruence | left; reflexivity].
Qed.

Lemma mfc_break_skipn : forall s l q, (s = l ++ NL :: q \/ (s = l /\ q = [])) ->
  q = skipn (length s - length q) s /\ (length s - length q <= length s)%nat.
Proof.
  intros s l q [-> | [-> ->]].
  - rewrite length_app. cbn [length].
    replace (length l + S (length q) - length q)%nat with (S (length l)) by lia.
    split; [|lia]. rewrite skipn_app, skipn_all2 by lia.
    replace (S (length l) - length l)%nat with 1%nat by lia. reflexivity.
  - cbn [length]. rewrite Nat.sub_0_r, skipn_all. split; [reflexivity | lia].
Qed.

Lemma mfc_rest_skipn : forall rest, mf_rest rest = skipn (length rest - length (mf_rest rest)) rest /\
  (length rest - length (mf_rest rest) <= length rest)%nat.
Proof.
  intros rest. unfold mf_rest. destruct (break_nl rest) as [l q] eqn:E. cbn [snd].
  apply (mfc_break_skipn rest l q). exact (proj2 (break_nl_spec rest l q E)).
Qed.

Lemma mfc_text_skip : forall m sp0 lo c p rest d, mf_text m sp0 lo c p rest -> (d <= length rest)%nat ->
  mf_text m sp0 lo c (p + Z.of_nat d) (skipn d rest).
Proof.
  intros m sp0 lo c p rest d HT Hd.
  pose proof (mf_text_props _ _ _ _ _ _ HT) as (_ & _ & Hp & _ & _).
  pose proof (mf_text_cstr _ _ _ _ _ _ d HT Hd) as HC.
  destruct HT as (_ & HNI & _ & A1 & A2).
  assert (ES : p + Z.of_nat d + cstr_span (p + Z.of_nat d) (skipn d rest) = p + cstr_span p rest).
  { unfold cstr_span. rewrite length_skipn.
    replace (p + Z.of_nat d + Z.of_nat (length rest - d) + 1) with (p + Z.of_nat (length rest) + 1) by lia. lia. }
  unfold mf_text. rewrite length_skipn.
  split; [lia|]. split; [apply (mfc_noimg_sub p (Z.of_nat (length rest) + 1)); [exact HNI | lia | lia]|].
  split; [exact HC|]. unfold apart in *. split; lia.
Qed.

Lemma mf_text_next : forall m sp0 lo c p rest, mf_text m sp0 lo c p rest -> rest <> [] ->
  mf_text m sp0 lo c (mf_next p rest) (mf_rest rest).
Proof.
  intros m sp0 lo c p rest HT _.
  destruct (mfc_rest_skipn rest) as [Eq Hd]. unfold mf_next.
  set (d := (length rest - length (mf_rest rest))%nat) in *.
  rewrite Eq. exact (mfc_text_skip m sp0 lo c p rest d HT Hd).
Qed.

(** ** The tail: the loop facts for the next line, from the context, the text, and the new state. *)
Lemma mf_tail_loop : forall m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  mf_ctx m fc sp0 sp lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 -> mf_text m sp0 lo c p rest -> rest <> [] ->
  mconf_at rsegs m c mc -> cell8 m (sp + 0x20) (cur_ptr c cur) -> cur_ok mc cur ->
  (k0 <= length (mc_kept mc))%nat ->
  0 <= line -> line + Z.of_nat (length rest) <= 65535 ->
  mc_refused mc + Z.of_nat (length (mf_rest rest)) < 2 ^ 32 ->
  mc_overflow mc + Z.of_nat (length (mf_rest rest)) < 2 ^ 32 ->
  m_file_loop m fc sp0 sp lo c (mf_next p rest) mc cur (line + 1) k0 (mf_rest rest)
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    HC HT Hr HMC HCUR HCOK HK0 HL0 HL1 HR HO.
  pose proof (mf_rest_lt rest Hr) as Hlt.
  apply mf_loop_iff. split; [exact HC|]. split; [exact (mf_text_next m sp0 lo c p rest HT Hr)|].
  unfold mf_st. split; [exact HMC|]. split; [exact HCUR|]. split; [exact HCOK|]. split; [exact HK0|].
  split; [lia|]. split; [lia|]. split; [exact HR | exact HO].
Qed.

(** The counters' room after a line that refused or overflowed at most once. *)
Lemma mf_cnt_next : forall (x x' : Z) rest, rest <> [] ->
  x + Z.of_nat (length rest) < 2 ^ 32 -> x' <= x + 1 -> x' + Z.of_nat (length (mf_rest rest)) < 2 ^ 32.
Proof. intros x x' rest Hr H1 H2. pose proof (mf_rest_lt rest Hr). lia. Qed.

(** ** The post *)
Lemma mf_post_back : forall ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F F1 m m1 lo c k0 mf W1 s,
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) ->
  munch W1 m m1 -> wmono rsegs m m1 -> sub_fp W1 (M_FILE_W (bv_unsigned sp0) c k0 mf) ->
  evt rsegs (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F1 m1 lo c k0 mf) s ->
  evt rsegs (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0 mf) s.
Proof.
  intros ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F F1 m m1 lo c k0 mf W1 s HF MU1 WM1 SF H.
  unfold mf_post in *. eapply evt_mono; [exact H|]. clear H.
  intros ms' HP. unfold ret_void_fp in HP |- *.
  destruct HP as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m'' &
                  E & FRM & FR & MU & WM & MI & TM & ST & Q).
  exists y0, y1, y2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F', fc', m''.
  split; [exact E|]. split; [exact FRM|]. split; [intros k Hk; rewrite (FR k Hk); exact (HF k Hk)|].
  split; [eapply munch_trans; [eapply munch_weaken; [exact SF | exact MU1] | exact MU]|].
  split; [eapply wmono_trans; [exact WM1 | exact WM]|]. split; [exact MI|]. split; [exact TM|].
  split; [exact ST | exact Q].
Qed.

(** ** Write lists *)
Lemma sub_fp_refl : forall W, sub_fp W W.
Proof. intros W x H. exact H. Qed.
Lemma sub_fp_trans : forall W1 W2 W3, sub_fp W1 W2 -> sub_fp W2 W3 -> sub_fp W1 W3.
Proof. intros W1 W2 W3 H12 H23 x Hx. apply H12, H23, Hx. Qed.
Lemma sub_fp_app : forall W1 W2 W, sub_fp W1 W -> sub_fp W2 W -> sub_fp (W1 ++ W2) W.
Proof. intros W1 W2 W H1 H2 x Hx. apply mfc_outside_app. split; [apply H1 | apply H2]; exact Hx. Qed.
Lemma sub_fp_nil : forall W, sub_fp [] W.
Proof. intros W x _. exact I. Qed.
(** One range inside one range of W. *)
Lemma sub_fp_one : forall a b W, (exists lo hi, In (lo, hi) W /\ lo <= a /\ b <= hi) -> sub_fp [(a, b)] W.
Proof.
  intros a b W (lo & hi & Hin & H1 & H2) x Hx. cbn [outside]. split; [|exact I].
  intros Hab. apply (mfc_outside_in W lo hi x Hx Hin). lia.
Qed.

Lemma mf_W_grows : forall sp0 c k0 a b, mf_grows a b -> sub_fp (M_FILE_W sp0 c k0 a) (M_FILE_W sp0 c k0 b).
Proof.
  intros sp0 c k0 a b [G1 G2] x Hx.
  unfold M_FILE_W, mseg_addr, kept_addr, MSEG_SIZE, MC_KEPT, MC_KEPT_LEN, MC_KNOCK in *.
  cbn [outside] in *. destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & _).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(** The line's result inside the final model's W. *)
Lemma mf_W_fin : forall sp0 c k0 st line rest, mf_cur_ok (fst st) (snd st) ->
  sub_fp (M_FILE_W sp0 c k0 (fst st)) (M_FILE_W sp0 c k0 (mf_fin st line rest)).
Proof.
  intros sp0 c k0 st line rest H. apply mf_W_grows. unfold mf_fin.
  exact (proj1 (m_lines_ok (lines (mf_rest rest)) st (line + 1) H)).
Qed.

Lemma mf_W_frame : forall sp0 c k0 mc a b, sp0 - M_FILE_STACK <= a -> b <= sp0 ->
  sub_fp [(a, b)] (M_FILE_W sp0 c k0 mc).
Proof.
  intros sp0 c k0 mc a b H1 H2. apply sub_fp_one. exists (sp0 - M_FILE_STACK), sp0.
  split; [unfold M_FILE_W; cbn [In]; left; reflexivity | lia].
Qed.

Lemma mf_W_counters : forall sp0 c k0 mc, sub_fp [(c + MC_N, c + MC_REFUSED + 4)] (M_FILE_W sp0 c k0 mc).
Proof.
  intros sp0 c k0 mc. apply sub_fp_one. exists (c + MC_N), (c + MC_REFUSED + 4).
  split; [unfold M_FILE_W; cbn [In]; right; right; left; reflexivity | lia].
Qed.

Lemma mf_W_tailfields : forall sp0 c k0 mc, sub_fp [(c + MC_NKEPT, c + MC_READING + 96)] (M_FILE_W sp0 c k0 mc).
Proof.
  intros sp0 c k0 mc. apply sub_fp_one. exists (c + MC_NKEPT), (c + MC_READING + 96).
  split; [unfold M_FILE_W; cbn [In]; right; right; right; right; right; left; reflexivity | lia].
Qed.

Lemma mf_W_seg : forall sp0 c k0 mc gi a len, (gi < length (mc_seg mc))%nat -> 0 <= a -> a + len <= MSEG_SIZE ->
  sub_fp [(mseg_addr c gi + a, mseg_addr c gi + a + len)] (M_FILE_W sp0 c k0 mc).
Proof.
  intros sp0 c k0 mc gi a len H1 H2 H3. apply sub_fp_one. exists c, (mseg_addr c (length (mc_seg mc))).
  split; [unfold M_FILE_W; cbn [In]; right; left; reflexivity|].
  unfold mseg_addr, MSEG_SIZE in *. lia.
Qed.

Lemma mf_W_knock : forall sp0 c k0 mc i, (k0 <= i < length (mc_kept mc))%nat ->
  sub_fp [(c + MC_KNOCK + 4 * Z.of_nat i, c + MC_KNOCK + 4 * Z.of_nat i + 4)] (M_FILE_W sp0 c k0 mc).
Proof.
  intros sp0 c k0 mc i H. apply sub_fp_one.
  exists (c + MC_KNOCK + 4 * Z.of_nat k0), (c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc))).
  split; [unfold M_FILE_W; cbn [In]; right; right; right; right; left; reflexivity | lia].
Qed.

Lemma mfc_refuse_kept : forall mc line knock, Z.of_nat (length (mc_kept mc)) < 8 ->
  length (mc_kept (m_refuse mc line knock)) = S (length (mc_kept mc)).
Proof.
  intros mc line knock H. unfold m_refuse. cbv zeta. cbn [mc_kept].
  destruct (Z.ltb_spec (Z.of_nat (length (mc_kept mc))) 8); [|lia].
  cbn iota. rewrite length_app. cbn [length]. lia.
Qed.

Lemma mf_W_refuse : forall sp0 sp c k0 mc line knock,
  sp0 - M_FILE_STACK <= sp - M_REFUSE_STACK -> sp <= sp0 -> (k0 <= length (mc_kept mc))%nat ->
  sub_fp (m_refuse_W sp c mc) (M_FILE_W sp0 c k0 (m_refuse mc line knock)).
Proof.
  intros sp0 sp c k0 mc line knock H1 H2 H3 x Hx.
  destruct (m_refuse_sizes mc line knock) as [Eseg [L1 L2]].
  unfold M_FILE_W in Hx. rewrite Eseg in Hx. cbn [outside] in Hx.
  destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & _).
  unfold m_refuse_W. destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:E.
  - apply Z.ltb_lt in E. rewrite (mfc_refuse_kept mc line knock E) in X4, X5.
    cbn [app outside].
    unfold kept_addr, MC_KEPT, MC_KEPT_LEN, MC_KNOCK, MC_NKEPT, MC_READING, MC_N, MC_REFUSED in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - cbn [app outside]. unfold MC_N, MC_REFUSED in *.
    split; [lia|]. split; [lia | exact I].
Qed.

(** m_refuse's writes are in the stack region and in c. *)
Lemma mf_refuse_W_in : forall sp lo c mc, lo <= sp - M_REFUSE_STACK ->
  sub_fp (m_refuse_W sp c mc) [(lo, sp); (sp + 0x20, sp + 0x68); (c, c + SEG_M_SIZE)].
Proof.
  intros sp lo c mc H x Hx. cbn [outside] in Hx. destruct Hx as (X1 & X2 & X3 & _).
  unfold m_refuse_W. destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:E; [apply Z.ltb_lt in E|];
    cbn [app outside];
    unfold kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED, SEG_M_SIZE, M_REFUSE_STACK, PRINTF_K in *.
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - split; [lia|]. split; [lia | exact I].
Qed.

(** m_refuse's writes miss a range [a, a + n) of [lo, sp0) above its sp. *)
Lemma mfc_refuse_W_disj : forall Sp sp0 lo c mc a n, apart c (SEG_M_SIZE + 4) lo sp0 -> lo <= a -> a + n <= sp0 ->
  Sp <= a -> disjoint_from (m_refuse_W Sp c mc) a n.
Proof.
  intros Sp sp0 lo c mc a n HAP H1 H2 H3. unfold m_refuse_W.
  destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:E; [apply Z.ltb_lt in E|]; cbn [app disjoint_from];
    unfold apart, SEG_M_SIZE, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED in *.
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - split; [lia|]. split; [lia | exact I].
Qed.

Lemma mfc_env_down : forall m fc lo sp sp0, printf_env m fc lo sp0 -> sp <= sp0 -> printf_env m fc lo sp.
Proof.
  intros m fc lo sp sp0 (F1 & F2 & F3 & F4 & F5) H. split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
  split; [exact F4 | lia].
Qed.

Lemma mfc_stack_down : forall m lo sp sp0, stack_ok rsegs m lo sp0 M_FILE_STACK -> sp + M_FILE_FRAME = sp0 ->
  stack_ok rsegs m lo sp M_REFUSE_STACK.
Proof.
  intros m lo sp sp0 (STK & HD & H16 & HNR) HF.
  pose proof (mfc_sp_mod16 sp sp0 HF H16) as HS16.
  unfold M_FILE_STACK, M_FILE_FRAME, M_REFUSE_STACK, PRINTF_K in *.
  destruct (stk_split rsegs m lo sp sp0 STK ltac:(lia)) as [Hlo _].
  split; [exact Hlo|]. split; [lia|]. split; [exact HS16|]. intros a Ha. apply HNR. lia.
Qed.

Lemma mfc_even4 : forall X, X mod 4 = 0 -> (X + 4) mod 2 = 0.
Proof. intros X H. Z.div_mod_to_equations. lia. Qed.

(** ** m_refuse at a call site X (`jal m_refuse` at X, ra = X + 4): a0 = c, a1 = line. The continuation gets the
    memory after it: the context, the text and the cur cell kept, c holding m_refuse mc line knock. *)
Lemma mf_refuse_call : m_refuse_contract ->
  forall (X : Z) (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo sp0 c line p : Z) (rest : list Z) (w : Z)
         (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (mc : mconf) (knock : bool)
         (Q : machine_state -> Prop),
    0 <= X -> X + 4 < 2 ^ 64 -> X mod 4 = 0 ->
    mf_ctx m fc sp0 (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
    mf_text m sp0 lo c p rest -> cell8 m (bv_unsigned sp + 0x20) w ->
    mconf_atp rsegs knock m c mc ->
    0 <= line <= 65536 -> mc_refused mc + 1 < 2 ^ 32 ->
    (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
            (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       mf_ctx m' fc' sp0 (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
       mf_text m' sp0 lo c p rest -> cell8 m' (bv_unsigned sp + 0x20) w ->
       mconf_at rsegs m' c (m_refuse mc line knock) ->
       munch (m_refuse_W (bv_unsigned sp) c mc) m m' -> wmono rsegs m m' ->
       (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
       evt rsegs Q
         (MS (mkR (Z_to_bv 64 (X + 4)) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 (X + 4)) fc' None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR (Z_to_bv 64 (X + 4)) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 line) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 M_REFUSE) fc None m (seg_rom rsegs)).
Proof.
  intros HR X sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo sp0 c
    line p rest w ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 mc knock Q HX0 HX1 HX4 HC HT HW HMC HL HRF K.
  pose proof (mf_ctx_bounds m fc sp0 (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 HC)
    as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  pose proof HC as (C1 & _ & _ & _ & _ & C6 & C7 & C8 & C9 & C10 & C11 & C12 & _ & _ & C15 & C16).
  pose proof C15 as (STK0 & _).
  assert (HSP : lo <= bv_unsigned sp - M_REFUSE_STACK /\ bv_unsigned sp + 0x68 <= sp0 /\ bv_unsigned sp <= sp0 /\
                lo <= bv_unsigned sp).
  { clear K. unfold M_FILE_STACK, M_FILE_FRAME, M_REFUSE_STACK, PRINTF_K in *. lia. }
  destruct HSP as (HS1 & HS2 & HS3 & HS4).
  assert (Ec : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; unfold SEG_M_SIZE in B8; lia).
  assert (El : bv_unsigned (Z_to_bv 64 line) = line) by (apply unsigned_lit; lia).
  pose proof (HR (Z_to_bv 64 (X + 4)) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 line) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo mc knock) as H.
  rewrite Ec, El in H.
  eapply evt_cut.
  { apply H. clear H K.
    unfold m_refuse_pre.
    split; [exact C6|]. split; [exact C7|]. split; [exact C8|]. split; [exact HMC|]. split; [exact C9|].
    split; [exact C10|]. split; [unfold apart in C11 |- *; lia|]. split; [exact HL|]. split; [exact HRF|].
    split; [exact (mfc_env_down m fc lo (bv_unsigned sp) sp0 C12 HS3)|].
    split; [exact (mfc_stack_down m lo (bv_unsigned sp) sp0 C15 C1) | exact C16]. }
  clear H. intros ms' HP. unfold ret_void_fp in HP.
  destruct HP as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' &
                  -> & FRM & FR & MU & WM & MI & TM & ST & MC).
  rewrite ret_pc_even by (try lia; apply mfc_even4; exact HX4).
  assert (WIN : sub_fp (m_refuse_W (bv_unsigned sp) c mc)
                  [(lo, bv_unsigned sp); (bv_unsigned sp + 0x20, bv_unsigned sp + 0x68); (c, c + SEG_M_SIZE)])
    by (apply mf_refuse_W_in; exact HS1).
  assert (STK' : stk rsegs m' lo sp0).
  { apply (mf_stk_after m m' lo (bv_unsigned sp) sp0 _ STK0 MU WM ST HS3).
    apply (mfc_refuse_W_disj (bv_unsigned sp) sp0 lo c mc); [exact C11 | lia | lia | lia]. }
  apply (K m' F' fc' y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6).
  - exact (mf_ctx_transport m m' fc fc' sp0 (bv_unsigned sp) lo c ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 _
             HC MU WM MI TM FRM STK' WIN).
  - apply (mf_text_transport m m' sp0 lo c p rest _ HT MU).
    eapply sub_fp_trans; [exact WIN | apply mfc_W3_W2; lia].
  - apply (cell8_transport m m' _ w _ HW MU).
    apply (mfc_refuse_W_disj (bv_unsigned sp) sp0 lo c mc); [exact C11 | lia | lia | lia].
  - exact MC.
  - exact MU.
  - exact WM.
  - exact FR.
Qed.

(** ** snprintf(D, 96, "%s", s) (m_file's three sites: 0x14028 the reading, 0x14590 role_file, 0x146d8
    ignore_file): s a C string with its slack, apart from the stack region and from the destination; the 96-byte
    destination writable, outside the image, apart from the stack region. Post: printf_post (the text firstn 95 s
    and its NUL at D). *)
Definition MF_FMT_S : Z := 0x104e0.

(** "%s" and its NUL in .rodata. *)
Lemma mfc_fmt_s_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m MF_FMT_S (pf_bytes ([37; 115] ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold MF_FMT_S; lia | |].
  - change (length (pf_bytes ([37; 115] ++ [0]))) with 3%nat. unfold MF_FMT_S. lia.
  - apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(** A C string with its slack, apart from the stack and the destination, as printf's %s argument (the slack cut to
    the bytes up to the next 8-byte boundary). *)
Lemma mfc_arg_s : forall m Sp lo D n (r : word) s, bv_unsigned r <> 0 -> cstr_at rsegs m (bv_unsigned r) s ->
  apart (bv_unsigned r) (cstr_span (bv_unsigned r) s) lo Sp ->
  apart (bv_unsigned r) (cstr_span (bv_unsigned r) s) D (D + n) ->
  pf_arg_ok m Sp lo D n r (APtr s).
Proof.
  intros m Sp lo D n r s H0 (bs & sl & B & Hz & Hn & Hsl) A1 A2.
  unfold apart, cstr_span in A1, A2.
  pose proof (bv_unsigned_in_range 64 r) as Rr.
  pose proof (Z.mod_pos_bound (- (bv_unsigned r + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hk.
  revert Hk Hsl A1 A2.
  remember ((- (bv_unsigned r + Z.of_nat (length s) + 1)) mod 8) as k eqn:Ek.
  intros Hk Hsl A1 A2.
  assert (EB : pf_bytes (s ++ [0]) = bs ++ [ZERO]).
  { unfold pf_bytes. rewrite map_app, <- Hz. transitivity (zb (zs bs) ++ [ZERO]); [reflexivity|].
    rewrite mfc_zb_zs. reflexivity. }
  cbn [pf_arg_ok]. split.
  - apply Forall_forall. intros x Hx.
    assert (Hx0 : x <> 0) by (intros ->; exact (Hn Hx)).
    rewrite <- Hz in Hx. unfold zs in Hx. apply in_map_iff in Hx as (b & <- & _).
    pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb. lia.
  - exists (firstn (Z.to_nat k) sl). rewrite EB.
    split.
    { rewrite <- (firstn_skipn (Z.to_nat k) sl) in B.
      assert (B' : bytes_at rsegs m (bv_unsigned r)
                     (((bs ++ [ZERO]) ++ firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl))
        by (rewrite <- !app_assoc; exact B).
      exact (mfc_bytes_pre _ _ _ _ B'). }
    split; [rewrite <- Ek, length_firstn; lia|].
    split; [lia|].
    rewrite length_firstn. split; lia.
Qed.

Lemma mf_snprintf_s : snprintf_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : list Z) (junk : list byte),
    bv_unsigned a1 = 96 -> bv_unsigned a2 = MF_FMT_S ->
    bv_unsigned a3 <> 0 -> cstr_at rsegs m (bv_unsigned a3) s -> Z.of_nat (length s) < 2 ^ 31 - 1 ->
    apart (bv_unsigned a3) (cstr_span (bv_unsigned a3) s) lo (bv_unsigned sp) ->
    apart (bv_unsigned a3) (cstr_span (bv_unsigned a3) s) (bv_unsigned a0) (bv_unsigned a0 + 96) ->
    rw_cells rsegs m (bv_unsigned a0) [CB 96 junk] -> bv_unsigned a0 <> 0 ->
    apart (bv_unsigned a0) 96 lo (bv_unsigned sp) -> blk_noimg rsegs (bv_unsigned a0) 96 ->
    printf_env m fc lo (bv_unsigned sp) -> stack_ok rsegs m lo (bv_unsigned sp) PRINTF_K -> mem_inv rsegs m ->
    evt rsegs
      (printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (bv_unsigned a0) (Z.of_nat (length s))
         (firstn 95 s) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros HS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    s junk HA1 HA2 HA3 HSTR HLEN HAP1 HAP2 HCELL HA0 HAP3 HNOIMG HENV HSTK MI.
  destruct HENV as (FRM & TM & (SG1 & g & SG2) & HLO & HSP).
  destruct HSTK as (STK & HK & _ & _).
  pose proof (bv_unsigned_in_range 64 a0) as R0.
  pose proof (HS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc m lo g [37; 115] [Ps] [APtr s] s junk) as H.
  cbv zeta in H. rewrite HA1 in H.
  change (Z.to_nat (96 - 1)) with 95%nat in H. change (Z.to_nat 96) with 96%nat in H.
  apply H; clear H.
  - rewrite HA2. apply mfc_fmt_s_bytes. exact MI.
  - rewrite HA2. unfold MF_FMT_S. apply Z.leb_le. reflexivity.
  - rewrite HA2. unfold MF_FMT_S. apply Z.leb_le. reflexivity.
  - reflexivity.
  - cbn [pf_args_ok]. split; [|exact I]. apply mfc_arg_s; assumption.
  - cbn. rewrite app_nil_r. reflexivity.
  - exact HCELL.
  - lia.
  - exact HLEN.
  - lia.
  - exact HAP3.
  - exact HNOIMG.
  - exact STK.
  - unfold SNPRINTF_K. unfold PRINTF_K in HK. lia.
  - unfold IMG_END. change (sa_img_end SA) with 0x536e8 in HLO. lia.
  - exact HSP.
  - exact FRM.
  - exact MI.
  - exact TM.
  - exact SG1.
  - exact SG2.
Qed.

(** SegModel's text of that call: s itself for |s| < 96. *)
Lemma mfc_fmt_s : forall s, fmt F_s [AS s] = cut_nul s ++ [].
Proof. intros s. vm_compute. reflexivity. Qed.

Lemma mf_snprintf_s_model : forall s, ~ In 0 s -> (length s < 96)%nat -> snprintf_s 96 F_s [AS s] = s.
Proof.
  intros s Hn Hl. unfold snprintf_s. rewrite mfc_fmt_s, app_nil_r, cut_nul_id by exact Hn.
  apply firstn_all2. change (Z.to_nat (96 - 1)) with 95%nat. lia.
Qed.
Lemma mf_snprintf_s_model95 : forall s, ~ In 0 s -> snprintf_s 96 F_s [AS s] = firstn 95 s.
Proof.
  intros s Hn. unfold snprintf_s. rewrite mfc_fmt_s, app_nil_r, cut_nul_id by exact Hn. reflexivity.
Qed.
