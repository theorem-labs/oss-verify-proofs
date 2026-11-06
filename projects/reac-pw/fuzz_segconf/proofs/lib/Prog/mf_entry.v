(** m_file (plain build, image 3776ca44d75c): the piece S_MF_ENTRY of Prog/m_file_c.v (family F3).
    0x13fb4-0x1407c: the prologue (frame 0xd0, the 13 `sd` of ra, s0 .. s11), s2 = text, s0 = c, s1 = c + 0x2000,
    a0 = &c->reading; the label choice at 0x14004 ("reac-pw.conf" = seg_spec.STR_BASE when a2 = NULL);
    snprintf(c->reading, 96, "%s", label) at 0x14028; gen++ (0x1402c-0x14038); *text = 0 goes to the epilogue
    (H_MF_EXIT), else the loop set-up 0x14044-0x14078 and the head 0x1407c (H_MF_HEAD). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Image Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_tok_bridge seg_env
  m_file_c mfu_facts mf_common mfp_mconf printf_facts_c snprintf_c.
Import ListNotations.
Open Scope Z_scope.

(** * Image-free helpers *)

Lemma en_disj_mono : forall W a n n', 0 <= n' <= n -> disjoint_from W a n -> disjoint_from W a n'.
Proof.
  induction W as [|[x y] W IH]; cbn [disjoint_from]; intros a n n' Hn H; [exact I|].
  destruct H as [H1 H2]. split; [lia | eapply IH; eauto].
Qed.

Lemma en_in_firstn : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

(** MemNorm's task_mem after writes whose bytes were all present or in a writable segment before. *)
Lemma en_task_mem : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview rsegs m x <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU H x b E.
  destruct (m x) as [b'|] eqn:E0; [exact (T x b' E0)|].
  assert (Hx : ~ outside W (bv_unsigned x)) by (intros Ho; rewrite (MU x Ho), E0 in E; discriminate E).
  pose proof (H x Hx) as Hw. unfold wview in Hw. rewrite E0 in Hw.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|]; [left; discriminate | contradiction].
Qed.

(** The reserved segments cover [0x10000, 0x54000) without a gap, so a block with no byte in them lies below or
    above it. *)
Definition en_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint en_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => en_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma en_cov_in : forall L cur x, cur <= x < en_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [en_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Lemma en_rsegs_cov : en_cov (en_ivs (segments_reserved rsegs)) 0x10000 = 0x54000.
Proof. vm_compute. reflexivity. Qed.

Lemma en_noimg : forall a n, 0 <= a -> 0 < n -> blk_noimg rsegs a n -> a + n <= 0x10000 \/ 0x54000 <= a.
Proof.
  intros a n Ha Hn F.
  assert (Cv : forall x, 0x10000 <= x < 0x54000 -> exists s, In s (segments_reserved rsegs)
                 /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. rewrite <- en_rsegs_cov in Hx. destruct (en_cov_in _ _ _ Hx) as (a0 & b0 & Hin & Hab).
    unfold en_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s0 & Es & Hs). injection Es as Ea Eb.
    exists s0. split; [exact Hs | lia]. }
  destruct (Z.lt_ge_cases a 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (a + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (Cv 0x10000 ltac:(lia)) as (s0 & Hs & Hx). exfalso.
    apply (F (0x10000 - a) ltac:(lia) s0 Hs). replace (a + (0x10000 - a)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases a 0x54000) as [H2|H2]; [|right; exact H2].
    destruct (Cv a ltac:(lia)) as (s0 & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s0 Hs). rewrite Z.add_0_r. exact Hx.
Qed.

(** A C string whose bytes up to the next 8-byte boundary are not written stays. *)
Lemma en_cstr_transport : forall W m m' a s, cstr_at rsegs m a s -> munch W m m' ->
  disjoint_from W a (cstr_span a s) -> cstr_at rsegs m' a s.
Proof.
  intros W m m' a s HC MU HD.
  destruct (cstr_cut rsegs m a s HC) as (bs & sl & HB & Hz & Hn & _ & Hl & Hsl & _).
  assert (Hk0 : 0 <= (- (a + Z.of_nat (length bs) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  unfold cstr_span in HD. rewrite <- Hl in HD.
  remember ((- (a + Z.of_nat (length bs) + 1)) mod 8) as k eqn:Ek.
  assert (Hk : (Z.to_nat k <= length sl)%nat) by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) sl) in HB.
  replace (bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) sl ++ skipn (Z.to_nat k) sl)
    with ((bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl) in HB
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in HB as [HB _].
  exists bs, (firstn (Z.to_nat k) sl). split; [|split; [exact Hz | split; [exact Hn|]]].
  - eapply bytes_at_transport; [exact HB | exact MU |].
    rewrite length_app. cbn [length]. rewrite firstn_length_le by exact Hk.
    replace (Z.of_nat (length bs + S (Z.to_nat k))) with (Z.of_nat (length bs) + 1 + k) by lia. exact HD.
  - rewrite firstn_length_le by exact Hk. rewrite <- Hl, <- Ek. lia.
Qed.

(** The block slack after a block of n bytes stays when the k bytes after it are not written. *)
Lemma en_slack_transport : forall W m m' a n k, blk_slack rsegs m a n -> munch W m m' ->
  0 <= k -> (- (a + n)) mod 8 <= k -> disjoint_from W (a + n) k -> blk_slack rsegs m' a n.
Proof.
  intros W m m' a n k HS MU Hk0 Hkm HD. destruct HS as (sl & HB & Hl).
  pose proof (Z.mod_pos_bound (- (a + n)) 8 ltac:(lia)) as Hb.
  remember ((- (a + n)) mod 8) as q eqn:Eq.
  assert (Hq : (Z.to_nat q <= length sl)%nat) by lia.
  rewrite <- (firstn_skipn (Z.to_nat q) sl) in HB. apply bytes_at_app in HB as [HB _].
  exists (firstn (Z.to_nat q) sl). split.
  - eapply bytes_at_transport; [exact HB | exact MU |].
    rewrite firstn_length_le by exact Hq. eapply (en_disj_mono _ _ k); [lia | exact HD].
  - rewrite firstn_length_le by exact Hq. lia.
Qed.

(** A range that reads as the image stays so when no byte of it is written. *)
Lemma en_mrd_transport : forall W m m' b n, munch W m m' -> disjoint_from W b n -> 0 <= b -> b + n <= 2 ^ 64 ->
  (forall a, b <= a < b + n -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
  forall a, b <= a < b + n -> mrd rsegs m' (wa a) = seg_rom rsegs (wa a).
Proof.
  intros W m m' b n MU HD H0 H1 H a Ha. rewrite <- (H a Ha). unfold mrd. rewrite MU; [reflexivity|].
  rewrite wa_unsigned by lia. eapply disjoint_outside; [exact HD | lia].
Qed.

(** The first byte of a C string: its first character, or its NUL. *)
Lemma en_cstr_first : forall m p s, cstr_at rsegs m p s ->
  exists b : byte, ov_read_bytes rsegs m (wa (p + Z.of_nat 0)) 1 = Some [b] /\
    (s = [] -> bv_unsigned b = 0) /\ (s <> [] -> bv_unsigned b <> 0).
Proof.
  intros m p s HC.
  destruct (cstr_cut rsegs m p s HC) as (bs & sl & HB & Hz & Hnz & Hn & Hlen & _ & _).
  destruct bs as [|b0 bs].
  - exists ZERO. rewrite (bytes_at_ov_read rsegs m p _ 0 1 HB) by (cbn; lia). cbn.
    split; [reflexivity|]. split; [intros _; reflexivity|]. intros Hs. exfalso. apply Hs. rewrite <- Hz. reflexivity.
  - exists b0. rewrite (bytes_at_ov_read rsegs m p _ 0 1 HB) by (cbn; lia). cbn.
    split; [reflexivity|]. split; [intros Hs; rewrite <- Hz in Hs; discriminate Hs|].
    intros _ E. apply Hnz. rewrite <- Hz. cbn. left. exact E.
Qed.

(** The bytes of the cells after the first ones, and of one 8-byte cell. *)
Lemma en_cells_suffix : forall m A pre post, rw_cells rsegs m A (pre ++ post) ->
  bytes_at rsegs m (A + Z.of_nat (cells_size pre)) (cells_bytes post).
Proof.
  intros m A pre post [[Hwf Hb] _]. apply cells_wf_app in Hwf as [Hw1 _].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hw1. exact Hb.
Qed.

Lemma en_cell8_at : forall m A cs k v a w, rw_cells rsegs m A cs -> cell_at cs k = Some (C8 v) ->
  a = A + Z.of_nat k -> v = w -> bytes_at rsegs m a (le8 w).
Proof.
  intros m A cs k v a w H Hc -> <-.
  destruct (cell_at_split cs k (C8 v) (C8 v) Hc) as (pre & post & -> & Hsz & _).
  pose proof (en_cells_suffix m A pre (C8 v :: post) H) as B. rewrite Hsz in B.
  cbn [cells_bytes cbytes] in B. apply bytes_at_app in B as [B _]. exact B.
Qed.

Lemma en_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma en_ro_str : forall m a l, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  ro_bytes_b rsegs a l = true -> bytes_at rsegs m a l.
Proof. intros m a l MI H0 H1 H. apply ro_bytes_at; auto. apply ro_bytes_b_sound. exact H. Qed.

(** "reac-pw.conf" in .rodata. *)
Lemma en_sbase_at : forall m, mem_inv rsegs m -> cstr_at rsegs m STR_BASE S_base.
Proof.
  intros m MI. exists (zb S_base), [].
  split; [apply en_ro_str;
          [exact MI | unfold STR_BASE; lia
           | change (length (zb S_base ++ [ZERO])) with 13%nat; unfold STR_BASE; lia
           | vm_compute; reflexivity]|].
  split; [vm_compute; reflexivity|]. split; [apply nulfree_forallb; vm_compute; reflexivity|].
  change (length S_base) with 12%nat. unfold STR_BASE. vm_compute. intros H; discriminate H.
Qed.

Lemma en_sbase_len : Z.of_nat (length S_base) = 12.
Proof. vm_compute. reflexivity. Qed.

Lemma en_bytes_forallb : forall l,
  forallb (fun x => (0 <=? x) && (x <? 256)) l = true -> Forall (fun x : Z => 0 <= x < 256) l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. cbn [forallb] in H.
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H0 H1].
  constructor; [apply Z.leb_le in H0; apply Z.ltb_lt in H1; lia | exact (IH H2)].
Qed.

Lemma en_sbase_bytes : Forall (fun x : Z => 0 <= x < 256) S_base.
Proof. apply en_bytes_forallb. vm_compute. reflexivity. Qed.

Lemma en_byte_range : forall n l, Forall (fun x => 0 <= x < 256) l -> Forall (fun x : Z => 0 <= x < 256) (firstn n l).
Proof.
  intros n l H. apply Forall_forall. intros x Hx. rewrite Forall_forall in H. apply H.
  eapply en_in_firstn; exact Hx.
Qed.

Lemma en_nulfree_firstn : forall n (l : list Z), ~ In 0 l -> ~ In 0 (firstn n l).
Proof. intros n l H Hin. apply H. eapply en_in_firstn; exact Hin. Qed.

Lemma en_length_zb : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. apply length_map. Qed.

Lemma en_noimg_sub : forall a n b k, blk_noimg rsegs a n -> a <= b -> b + k <= a + n -> blk_noimg rsegs b k.
Proof.
  intros a n b k H H1 H2 i Hi sg Hs. replace (b + i) with (a + (b - a + i)) by lia. apply H; [lia | exact Hs].
Qed.

Lemma en_cstr_bytes : forall mm a l, cstr_at rsegs mm a l -> Forall (fun x : Z => 0 <= x < 256) l.
Proof.
  intros mm a l (bs & sl & _ & Hz & _ & _). apply Forall_forall. intros x Hx.
  rewrite <- Hz in Hx. unfold zs in Hx. apply in_map_iff in Hx. destruct Hx as (b & Hb & _).
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb. lia.
Qed.

Lemma en_span_bound : forall a l, 0 <= cstr_span a l <= Z.of_nat (length l) + 8.
Proof.
  intros a l. unfold cstr_span.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length l) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma en_nat65535 : Z.of_nat 65535 = 65535.
Proof. vm_compute. reflexivity. Qed.

Lemma en_len_le : forall {A} (l : list A) (n : nat), (length l <= n)%nat -> Z.of_nat (length l) <= Z.of_nat n.
Proof. intros A l n H. lia. Qed.

Lemma en_pf_bytes : forall l, pf_bytes (l ++ [0]) = zb l ++ [ZERO].
Proof. intros l. unfold pf_bytes, zb, ZERO. rewrite map_app. reflexivity. Qed.

(** * The walk *)
Section EN.

Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variables (C T LP lo : Z).
Variable mc : mconf.
Variable s : list Z.
Variable lab : option (list Z).

Local Notation Sp := (bv_unsigned sp).

Hypothesis HPRE : m_file_pre m fc Sp lo C T LP mc s lab.
Hypothesis HSN : snprintf_contract.
Hypothesis HH : forall n, H_MF_HEAD n.
Hypothesis HX : H_MF_EXIT.

Definition LABS : list Z := match lab with Some l => l | None => S_base end.
Definition RD : list Z := snprintf_s 96 F_s [AS LABS].
Definition MC1 : mconf := MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc) (mc_kept mc) (mc_gen mc + 1) RD.
Definition K0 : nat := length (mc_kept mc).
Definition MF : mconf := m_file mc s lab.

Lemma en_mf_unfold : MF = fst (m_lines (MC1, None) 0 (lines s)).
Proof. reflexivity. Qed.

Definition Post : machine_state -> Prop :=
  ret_void_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m (M_FILE_W Sp C K0 MF) lo
    (fun m' => mconf_at rsegs m' C MF).

(** The bytes the whole walk may write: the frame and the callee's stack, and [n_kept, reading + 96) of the block.
    A Notation, not a Definition: the store tactics must see the list. *)
Local Notation WT := [(Sp - 6160, Sp); (C + 9132, C + 9236)].

Ltac en_pre :=
  let HP := fresh "HP" in pose proof HPRE as HP;
  destruct HP as (Hc0 & Hc16 & HNI & HMC & HWR & HSL & HAc & Hgen & Href & Hov & Ht0 & HTNI & HTC & HTlen & HTap &
                  HTapc & HLAB & HLX & (FRM & TM & HSSP & HIE & HS63) & HCAT & HWDS & (ST & HK & HS16 & HROM) & MI);
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HK;
  unfold SA, SEG_PLAIN in HIE; cbn [sa_img_end] in HIE;
  unfold apart, SEG_M_SIZE in HAc;
  unfold apart in HTap; unfold apart, SEG_M_SIZE in HTapc;
  assert (HC0 : 0 <= C /\ C + 9236 <= 2 ^ 64) by
    (let bsC := fresh in let HBC := fresh in let HEC := fresh in
     destruct HMC as (bsC & HBC & HEC);
     let HL := fresh in destruct HEC as (HL & _);
     pose proof (bytes_at_bound rsegs m C bsC HBC); unfold SEG_M_SIZE in *; lia);
  let HI := fresh "HCimg" in
  pose proof (en_noimg C SEG_M_SIZE ltac:(lia) ltac:(unfold SEG_M_SIZE; lia) HNI) as HI;
  unfold SEG_M_SIZE in HI;
  pose proof (u64_range sp) as Rsp.

(** Every byte of WT was present at entry. *)
Lemma en_pres : forall x : word, ~ outside WT (bv_unsigned x) -> wview rsegs m x <> None.
Proof.
  intros x Hx. en_pre.
  destruct (Z_le_dec (Sp - 6160) (bv_unsigned x)) as [A1|A1];
  destruct (Z_lt_dec (bv_unsigned x) Sp) as [A2|A2];
  destruct (Z_le_dec (C + 9132) (bv_unsigned x)) as [B1|B1];
  destruct (Z_lt_dec (bv_unsigned x) (C + 9236)) as [B2|B2];
  try (exfalso; apply Hx; cbn [outside]; split; [lia | split; [lia | exact I]]).
  all: first
    [ destruct ST as (_ & _ & STa); destruct (STa (bv_unsigned x) ltac:(lia)) as [Hw _];
      unfold wa in Hw; rewrite Z_to_bv_lit_self in Hw; exact Hw
    | destruct HWR as (_ & _ & Hwr);
      specialize (Hwr (bv_unsigned x - C) ltac:(unfold SEG_M_SIZE; lia));
      replace (C + (bv_unsigned x - C)) with (bv_unsigned x) in Hwr by lia;
      unfold wa in Hwr; rewrite Z_to_bv_lit_self in Hwr; exact Hwr ].
Qed.

Lemma en_task : forall m', munch WT m m' -> MemNorm.task_mem rsegs m'.
Proof.
  intros m' MU. en_pre. eapply en_task_mem; [exact TM | exact MU | exact en_pres].
Qed.

Lemma en_subfp : sub_fp WT (M_FILE_W Sp C K0 MF).
Proof.
  unfold sub_fp. intros x H.
  unfold M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K, MC_NKEPT, MC_READING in H.
  cbn [outside] in H |- *. destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & _).
  split; [lia | split; [lia | exact I]].
Qed.

Lemma en_post_back : forall (W1 : list ivl) (F1 : bvmap 5 word) (m1 : word -> option byte) (ms : machine_state),
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) ->
  munch W1 m m1 -> wmono rsegs m m1 -> sub_fp W1 (M_FILE_W Sp C K0 MF) ->
  evt rsegs
    (ret_void_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F1 m1 (M_FILE_W Sp C K0 MF) lo
       (fun m' => mconf_at rsegs m' C MF)) ms ->
  evt rsegs Post ms.
Proof.
  intros W1 F1 m1 ms HF MU WM SUB H. eapply evt_mono; [exact H|].
  intros ms' PO. unfold ret_void_fp in PO. unfold Post, ret_void_fp.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' &
                  E & HFr & HFe & MU' & WM' & MI' & TM' & ST' & HQ).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, F', fc', m'.
  split; [exact E|]. split; [exact HFr|].
  split; [intros k Hk; rewrite (HFe k Hk); exact (HF k Hk)|].
  split; [eapply munch_trans; [eapply munch_weaken; [exact SUB | exact MU] | exact MU']|].
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  split; [exact MI'|]. split; [exact TM'|]. split; [exact ST' | exact HQ].
Qed.

(** ** 0x14044-0x1407c: the loop set-up and the head *)
Lemma en_setup : forall (F1 : bvmap 5 word) (fc1 : bv 32) (m3 : word -> option byte)
    (j0 j1 : list byte) (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w1 w3 w4 w5 w6 w7 w8 w9 w10 w11 t3 t4 t5 t6 : word),
  s <> [] ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) -> frm0 fc1 ->
  rw_cells rsegs m3 (Sp + -208)
    [CB 16 j0; C8 (Z_to_bv 64 (C + 8192)); C8 (Z_to_bv 64 (C + 9140)); CB 72 j1;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m3 lo (Sp + -208) ->
  mem_inv rsegs m3 -> munch WT m m3 -> wmono rsegs m m3 ->
  mconf_at rsegs m3 C MC1 -> wr_at rsegs m3 C SEG_M_SIZE ->
  evt rsegs Post
    (MS (mkR ra1 (Z_to_bv 64 (Sp + -208)) gp tp t0 t1 t2 (Z_to_bv 64 C) w1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 T) w3 w4 w5 w6 w7 w8 w9 w10 w11 t3 t4 t5 t6)
        F1 (Z_to_bv 64 0x14044) fc1 None m3 (seg_rom rsegs)).
Proof.
  intros F1 fc1 m3 j0 j1 ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 w1 w3 w4 w5 w6 w7 w8 w9 w10 w11 t3 t4 t5 t6
    Hs HFe HFr FR3 ST3 MI3 MU3 WM3 HMC3 HWR3.
  en_pre.
  pose proof (en_len_le s _ HTlen) as HL65; rewrite en_nat65535 in HL65.
  pose proof (en_span_bound T s) as Hspan.
  assert (Hmod4 : (- (C + 9236)) mod 8 = 4) by (clear - Hc16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(Sp - 208, Sp)] m3) as MUf.
  do 14 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mk end.
  (* the block still holds MC1 *)
  assert (HMCk : mconf_at rsegs mk C MC1).
  { destruct HMC3 as (bsk & HBk & HEk). pose proof HEk as HEk'. destruct HEk' as (HLk & _).
    exists bsk. split; [|exact HEk]. eapply bytes_at_transport; [exact HBk | exact MUf |].
    cbn [disjoint_from]. unfold SEG_M_SIZE in HLk. split; [lia | exact I]. }
  (* the stack region is whole again *)
  pose proof (stk_release rsegs mk lo (Sp + -208) _ ST3 FR3 ltac:(lia)) as STk.
  cbn [cells_size csize Nat.add] in STk.
  replace (Sp + -208 + Z.of_nat 208) with Sp in STk by lia.
  (* the saved registers *)
  pose proof (en_cells_suffix mk (Sp + -208)
                [CB 8 _; C8 _; C8 _; C8 _; C8 _; CB 64 _]
                [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                FR3) as HSV.
  eapply (en_post_back _ F1 mk); [exact HFe | exact MU3 | exact WM3 | exact en_subfp |].
  rewrite en_mf_unfold.
  eapply (HH (S (length s))); [lia | exact Hs | | ].
  - (* m_file_loop *)
    unfold m_file_loop. rewrite (unsigned_lit (Sp + -208)) by lia.
    split; [unfold M_FILE_FRAME; lia|].
    split; [unfold saved_at, M_FILE_SAVE; exact HSV|].
    split; [unfold cell8; eapply (en_cell8_at mk (Sp + -208) _ 8%nat);
            [exact FR3 | cells_cbv; reflexivity | lia | unfold MC_KNOCK; f_equal; lia]|].
    split; [unfold cell8; eapply (en_cell8_at mk (Sp + -208) _ 16%nat);
            [exact FR3 | cells_cbv; reflexivity | lia | unfold MC_N; f_equal; lia]|].
    split; [unfold cell8; eapply (en_cell8_at mk (Sp + -208) _ 24%nat);
            [exact FR3 | cells_cbv; reflexivity | lia | unfold MC_READING; f_equal; lia]|].
    split; [unfold cell8, cur_ptr; eapply (en_cell8_at mk (Sp + -208) _ 32%nat);
            [exact FR3 | cells_cbv; reflexivity | lia | reflexivity]|].
    split; [exact Hc0|]. split; [exact Hc16|]. split; [exact HNI|].
    split; [exact HMCk|]. split; [exact HWR3|].
    split; [eapply (en_slack_transport _ m mk C SEG_M_SIZE 4);
            [exact HSL | exact MU3 | lia | unfold SEG_M_SIZE; lia
             | unfold SEG_M_SIZE; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]]|].
    split; [unfold apart, SEG_M_SIZE; exact HAc|].
    split; [exact I|].
    split; [unfold K0, MC1; cbn [mc_kept]; lia|].
    split; [lia|]. split; [lia|].
    split; [unfold MC1; cbn [mc_refused]; lia|].
    split; [unfold MC1; cbn [mc_overflow]; lia|].
    split; [exact Ht0|]. split; [exact HTNI|].
    split; [eapply en_cstr_transport; [exact HTC | exact MU3 |];
            cbn [disjoint_from]; split; [lia | split; [lia | exact I]]|].
    split; [unfold apart; exact HTap|].
    split; [unfold apart, SEG_M_SIZE; exact HTapc|].
    split.
    { split; [exact HFr|]. split; [eapply en_task; exact MU3|].
      split.
      { destruct HSSP as (HG1 & g & HG2). unfold ssp_ok.
        unfold SA, SEG_PLAIN in HG1, HG2 |- *.
        cbn [sa_got_guard sa_guard] in HG1, HG2 |- *.
        split.
        { eapply bytes_at_transport; [exact HG1 | exact MU3 |].
          rewrite length_le8. cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
        { exists g. eapply bytes_at_transport; [exact HG2 | exact MU3 |].
          rewrite length_le8. cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. } }
      split; [unfold SA, SEG_PLAIN; cbn [sa_img_end]; lia | lia]. }
    split.
    { unfold cat_img in HCAT |- *. unfold SA, SEG_PLAIN in HCAT |- *. cbn [sa_catalogue] in HCAT |- *.
      eapply (en_mrd_transport _ m mk _ CAT_BYTES);
        [exact MU3 | unfold CAT_BYTES; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]
         | lia | unfold CAT_BYTES; lia | exact HCAT]. }
    split.
    { unfold words_img in HWDS |- *.
      eapply (en_mrd_transport _ m mk M_KEY_WORDS 40);
        [exact MU3 | unfold M_KEY_WORDS; cbn [disjoint_from]; split; [lia | split; [lia | exact I]]
         | unfold M_KEY_WORDS; lia | unfold M_KEY_WORDS; lia | exact HWDS]. }
    split; [|exact MI3].
    unfold stack_ok, M_FILE_STACK, M_FILE_FRAME, PRINTF_K.
    split; [exact STk|]. split; [lia|]. split; [lia | exact HROM].
  - (* m_file_regs *)
    unfold m_file_regs, BLANK_MASK.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

(** ** 0x1402c-0x14044: gen++, then the text test *)
Lemma en_after : forall (F1 : bvmap 5 word) (fc1 : bv 32) (m2 : word -> option byte)
    (j0 j1 : list byte) (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get F k) -> frm0 fc1 ->
  rw_cells rsegs m2 (Sp + -208)
    [CB 24 j0; C8 (Z_to_bv 64 (C + 9140)); CB 72 j1;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m2 lo (Sp + -208) ->
  mem_inv rsegs m2 -> munch WT m m2 -> wmono rsegs m m2 ->
  mconf_at rsegs m2 C (mc_set_reading RD mc) -> wr_at rsegs m2 C SEG_M_SIZE ->
  evt rsegs Post
    (MS (mkR ra1 (Z_to_bv 64 (Sp + -208)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 (C + 8192))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 T) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F1 (Z_to_bv 64 0x1402c) fc1 None m2 (seg_rom rsegs)).
Proof.
  intros F1 fc1 m2 j0 j1 ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HFe HFr FR2 ST2 MI2 MU2 WM2 HMC2 HWR2.
  en_pre.
  pose proof (en_span_bound T s) as Hspan.
  pose proof (mconf_rd_gen rsegs false m2 C (mc_set_reading RD mc) HMC2) as RDG.
  cbn [mc_gen mc_set_reading] in RDG. unfold MC_GEN in RDG.
  assert (Hg0 : 0 <= mc_gen mc).
  { destruct HMC as (bsg & _ & HEg). apply (mconf_enc_bounds false mc bsg) in HEg. lia. }
  pose proof (munch_refl [(Sp - 208, Sp)] m2) as MUg.
  do 3 step.
  rewrite (en_sx32_small (mc_gen mc)) by lia.
  pose proof (wr_at_store_ok rsegs m0 C SEG_M_SIZE 9136 4%nat HWR2 ltac:(lia)
                ltac:(unfold SEG_M_SIZE; lia)) as SO.
  step.
  remember (write_to_mem m0 (Z_to_bv 64 (C + 9136)) (le4 (Z_to_bv 64 (mc_gen mc + 1)))) as m3 eqn:Em3.
  assert (MI3 : mem_inv rsegs m3)
    by (rewrite Em3; apply mem_inv_store; [exact MI2 | rewrite length_le4; exact SO]).
  assert (MU3 : munch WT m m3).
  { rewrite Em3. eapply munch_write; [exact MU2 | lia | rewrite length_le4; lia |].
    rewrite length_le4. cbn [inside]. right. left. lia. }
  assert (WM3 : wmono rsegs m m3) by (rewrite Em3; apply wmono_write; exact WM2).
  assert (ST3 : stk rsegs m3 lo (Sp + -208))
    by (rewrite Em3; apply stk_write; [exact ST2 | lia | rewrite length_le4; lia]).
  assert (HWR3 : wr_at rsegs m3 C SEG_M_SIZE) by (rewrite Em3; apply wr_at_write; exact HWR2).
  assert (FR3 : rw_cells rsegs m3 (Sp + -208)
    [CB 16 (firstn 16 j0); C8 (Z_to_bv 64 (C + 8192)); C8 (Z_to_bv 64 (C + 9140)); CB 72 j1;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { rewrite Em3. eapply rw_cells_frame; [exact FR2 | lia | rewrite length_le4; lia |].
    cbn [cells_size csize Nat.add]. rewrite length_le4. lia. }
  assert (HMCg : mconf_at rsegs m0 C (mc_set_reading RD mc)).
  { destruct HMC2 as (bs2 & HB2 & HE2). pose proof HE2 as HE2'. destruct HE2' as (HL2 & _).
    exists bs2. split; [|exact HE2]. eapply bytes_at_transport; [exact HB2 | exact MUg |].
    cbn [disjoint_from]. unfold SEG_M_SIZE in HL2. split; [lia | exact I]. }
  assert (HMC3 : mconf_at rsegs m3 C MC1).
  { rewrite Em3. eapply (mconf_atp_store rsegs false false m0 C (mc_set_reading RD mc) MC1 (C + 9136));
      [exact HMCg | lia | rewrite length_le4; unfold SEG_M_SIZE; lia |].
    intros bs HB. replace (C + 9136 - C) with MC_GEN by (unfold MC_GEN; lia).
    apply (mconf_enc_gen false (mc_set_reading RD mc) bs (mc_gen mc + 1)) in HB; [exact HB | lia]. }
  assert (HTC3 : cstr_at rsegs m3 T s).
  { eapply en_cstr_transport; [exact HTC | exact MU3 |].
    cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
  pose proof (en_cstr_first m3 T s HTC3) as (b & RDb & Hb0 & Hb1).
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  step.
  destruct (list_eq_dec Z.eq_dec s []) as [Hs0|Hsn].
  - (* the text is empty: the epilogue *)
    specialize (Hb0 Hs0).
    step. if_cases K; cbv iota.
    + eapply (en_post_back _ F1 m3); [exact HFe | exact MU3 | exact WM3 | exact en_subfp |].
      pose proof (stk_release rsegs m3 lo (Sp + -208) _ ST3 FR3 ltac:(lia)) as STk.
      cbn [cells_size csize Nat.add] in STk.
      replace (Sp + -208 + Z.of_nat 208) with Sp in STk by lia.
      pose proof (en_cells_suffix m3 (Sp + -208) [CB 16 _; C8 _; C8 _; CB 72 _]
                    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                    FR3) as HSV.
      assert (HMF0 : MF = MC1) by (rewrite en_mf_unfold, Hs0; reflexivity).
      rewrite HMF0.
      eapply HX;
        [rewrite (unsigned_lit (Sp + -208)) by lia; unfold M_FILE_FRAME; lia
         | unfold saved_at, M_FILE_SAVE; rewrite (unsigned_lit (Sp + -208)) by lia; exact HSV
         | exact HFr | exact MI3 | eapply en_task; exact MU3 | exact STk | exact HMC3].
    + exfalso. zify_cond K. rewrite unsigned_lit in K by lia. lia.
  - (* a line follows: the set-up *)
    specialize (Hb1 Hsn).
    step. if_cases K; cbv iota.
    + exfalso. zify_cond K. rewrite unsigned_lit in K by lia. lia.
    + eapply en_setup;
        [exact Hsn | exact HFe | exact HFr | exact FR3 | exact ST3 | exact MI3 | exact MU3 | exact WM3
         | exact HMC3 | exact HWR3].
Qed.

(** ** 0x14018-0x1402c: the snprintf of c->reading *)
Lemma en_call : forall (w : Z) (lab' : list Z) (m1 : word -> option byte) (junk : list byte)
    (t0 t1 t2 a1' a4 a5 a6 a7 t3 t4 t5 t6 : word),
  LABS = lab' -> w <> 0 -> cstr_at rsegs m1 w lab' -> Z.of_nat (length lab') < 2 ^ 31 - 1 ->
  ~ In 0 lab' -> Forall (fun x : Z => 0 <= x < 256) lab' ->
  apart w (cstr_span w lab') lo Sp ->
  apart w (cstr_span w lab') (C + 9140) (C + 9140 + 96) ->
  rw_cells rsegs m1 (Sp + -208)
    [CB 104 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo (Sp + -208) -> mem_inv rsegs m1 ->
  munch WT m m1 -> wmono rsegs m m1 ->
  mconf_at rsegs m1 C mc -> wr_at rsegs m1 C SEG_M_SIZE -> ssp_ok m1 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (Sp + -208)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 (C + 8192))
             (Z_to_bv 64 (C + 9140)) a1' (Z_to_bv 64 LP) (Z_to_bv 64 w) a4 a5 a6 a7
             (Z_to_bv 64 T) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14018) fc None m1 (seg_rom rsegs)).
Proof.
  intros w lab' m1 junk t0 t1 t2 a1' a4 a5 a6 a7 t3 t4 t5 t6
    Elab Hw0 HwC HwL HwN HwB Hwap1 Hwap2 FR1 ST1 MI1 MU1 WM1 HMC1 HWR1 HSSP1.
  en_pre.
  pose proof (en_span_bound w lab') as Hspan.
  unfold apart in Hwap1, Hwap2.
  assert (Hwr : 0 <= w < 2 ^ 64).
  { destruct HwC as (bsw & slw & HBw & _). pose proof (bytes_at_bound rsegs m1 w _ HBw) as HBb.
    rewrite length_app in HBb. cbn [length] in HBb. lia. }
  pose proof (munch_refl [(Sp - 208, Sp)] m1) as MUg.
  do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m0 end.
  assert (HMC0 : mconf_at rsegs m0 C mc).
  { destruct HMC1 as (bsc & HBc & HEc). pose proof HEc as HEc'. destruct HEc' as (HLc & _).
    exists bsc. split; [|exact HEc]. eapply bytes_at_transport; [exact HBc | exact MUg |].
    cbn [disjoint_from]. unfold SEG_M_SIZE in HLc. split; [lia | exact I]. }
  assert (HwC0 : cstr_at rsegs m0 w lab').
  { eapply en_cstr_transport; [exact HwC | exact MUg |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (HSSP0 : ssp_ok m0).
  { destruct HSSP1 as (HG1 & g & HG2). unfold ssp_ok.
    unfold SA, SEG_PLAIN in HG1, HG2 |- *. cbn [sa_got_guard sa_guard] in HG1, HG2 |- *.
    split.
    { eapply bytes_at_transport; [exact HG1 | exact MUg |].
      rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I]. }
    { exists g. eapply bytes_at_transport; [exact HG2 | exact MUg |].
      rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I]. } }
  destruct (mconf_field_cells rsegs false m0 C mc MC_READING HMC0 HWR1
              ltac:(unfold MC_READING; lia) ltac:(unfold MC_READING, SEG_M_SIZE; lia)) as (junkd & FRD).
  unfold MC_READING in FRD.
  destruct (stk_split rsegs m0 lo (Sp - 6160) (Sp + -208) ST1 ltac:(lia)) as [STlo STpf].
  eapply evt_cut.
  { eapply (mf_snprintf_s HSN) with (lo := Sp - 6160) (s := lab') (junk := junkd).
    - apply unsigned_lit; lia.
    - apply unsigned_lit; unfold MF_FMT_S; lia.
    - rewrite unsigned_lit by lia. exact Hw0.
    - rewrite unsigned_lit by lia. exact HwC0.
    - exact HwL.
    - rewrite !unsigned_lit by lia. unfold apart. lia.
    - rewrite !unsigned_lit by lia. unfold apart. lia.
    - rewrite unsigned_lit by lia. exact FRD.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. unfold apart. lia.
    - rewrite unsigned_lit by lia. eapply en_noimg_sub; [exact HNI | lia | unfold SEG_M_SIZE; lia].
    - rewrite unsigned_lit by lia. split; [exact FRM|]. split; [eapply en_task; exact MU1|].
      split; [exact HSSP0|]. split; [unfold SA, SEG_PLAIN; cbn [sa_img_end]; lia | lia].
    - rewrite unsigned_lit by lia. unfold stack_ok, PRINTF_K.
      split; [exact STpf|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
      intros a Ha. apply HROM. lia.
    - exact MI1. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc2 & m2 &
                  E & MUp & WMp & MIp & TMp & FRMp & FEQ & STp & BTp).
  subst ms'.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !(unsigned_lit (C + 9140)) in MUp, BTp by lia.
  rewrite !(unsigned_lit (Sp + -208)) in MUp, STp by lia.
  assert (ERD : RD = firstn 95 lab') by (unfold RD; rewrite Elab; apply mf_snprintf_s_model95; exact HwN).
  pose proof (length_firstn 95 lab') as HLT.
  assert (HLTn : (length (firstn 95 lab') <= 95)%nat) by lia.
  rewrite en_pf_bytes in BTp.
  assert (HLNB : Z.of_nat (length (zb (firstn 95 lab') ++ [ZERO]))
                 = Z.of_nat (length (firstn 95 lab')) + 1)
    by (rewrite length_app, en_length_zb; cbn [length]; lia).
  assert (MU2 : munch WT m m2).
  { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [|exact MUp].
    unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *.
    destruct Hx as (H1 & H2 & _). split; [lia | split; [lia | exact I]]. }
  assert (WM2 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WMp]).
  assert (FR2 : rw_cells rsegs m2 (Sp + -208)
    [CB 24 (firstn 24 junk); C8 (Z_to_bv 64 (C + 9140)); CB 72 (skipn 32 junk);
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR1 | exact MUp | exact WMp |].
    cbn [cells_size csize Nat.add disjoint_from]. split; [lia | split; [lia | exact I]]. }
  assert (ST2 : stk rsegs m2 lo (Sp + -208)).
  { eapply stk_merge; [| exact STp | lia].
    eapply stk_transport_disjoint; [exact STlo | exact MUp | exact WMp |].
    cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
  assert (HWR2 : wr_at rsegs m2 C SEG_M_SIZE) by (eapply wr_at_transport; [exact HWR1 | exact WMp]).
  assert (HMC2 : mconf_at rsegs m2 C (mc_set_reading RD mc)).
  { rewrite ERD.
    eapply (mconf_atp_upd rsegs false false m0 m2 C mc (mc_set_reading (firstn 95 lab') mc) (C + 9140)
              (zb (firstn 95 lab') ++ [ZERO]));
      [exact HMC0 | exact MUp
       | intros x Hx Hox; unfold SEG_M_SIZE in Hx;
         destruct (Z_le_dec (C + 9140) x) as [D1|D1];
         destruct (Z_lt_dec x (C + 9140 + Z.of_nat (length (zb (firstn 95 lab') ++ [ZERO])))) as [D2|D2];
         [lia | exfalso; apply Hox; cbn [outside]; split; [lia | split; [lia | exact I]] ..]
       | exact BTp | lia | unfold SEG_M_SIZE; lia
       | intros bs HB; replace (C + 9140 - C) with MC_READING by (unfold MC_READING; lia);
         apply mconf_enc_reading;
           [exact HB | lia | apply en_nulfree_firstn; exact HwN | apply en_byte_range; exact HwB]]. }
  eapply (en_after Ft fc2 m2);
    [exact FEQ | exact FRMp | exact FR2 | exact ST2 | exact MIp | exact MU2 | exact WM2
     | exact HMC2 | exact HWR2].
Qed.

(** ** 0x13fb4-0x14018: the prologue and the label choice *)
Lemma en_walk : forall (w : Z) (lab' : list Z) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  LABS = lab' -> (LP = 0 -> w = STR_BASE) -> (LP <> 0 -> w = LP) -> 0 <= LP < 2 ^ 64 ->
  w <> 0 -> cstr_at rsegs m w lab' -> Z.of_nat (length lab') < 2 ^ 31 - 1 ->
  ~ In 0 lab' -> Forall (fun x : Z => 0 <= x < 256) lab' ->
  apart w (cstr_span w lab') lo Sp ->
  apart w (cstr_span w lab') (C + 9140) (C + 9140 + 96) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 T) (Z_to_bv 64 LP) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 M_FILE) fc None m (seg_rom rsegs)).
Proof.
  intros w lab' t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Elab Ew0 EwN HLPr Hw0 HwC HwL HwN HwB Hwap1 Hwap2.
  unfold M_FILE.
  en_pre.
  pose proof (en_span_bound w lab') as Hspan.
  destruct (stk_carve rsegs m lo Sp 208 ST ltac:(lia)) as [ST1 [junk FR]].
  change (Z.of_nat 208) with 208 in ST1, FR.
  replace (Sp - 208) with (Sp + -208) in ST1, FR by lia.
  pose proof (munch_refl WT m) as MU.
  pose proof (munch_refl [(Sp - 208, Sp)] m) as MUf.
  pose proof (wmono_refl rsegs m) as WM.
  do 20 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m0 end.
  assert (HMC0 : mconf_at rsegs m0 C mc).
  { destruct HMC as (bsc & HBc & HEc). pose proof HEc as HEc'. destruct HEc' as (HLc & _).
    exists bsc. split; [|exact HEc]. eapply bytes_at_transport; [exact HBc | exact MUf |].
    cbn [disjoint_from]. unfold SEG_M_SIZE in HLc. split; [lia | exact I]. }
  assert (HwC0 : cstr_at rsegs m0 w lab').
  { eapply en_cstr_transport; [exact HwC | exact MUf |].
    cbn [disjoint_from]. unfold apart in Hwap1. split; [lia | exact I]. }
  assert (HSSP0 : ssp_ok m0).
  { destruct HSSP as (HG1 & g & HG2). unfold ssp_ok.
    unfold SA, SEG_PLAIN in HG1, HG2 |- *. cbn [sa_got_guard sa_guard] in HG1, HG2 |- *.
    split.
    { eapply bytes_at_transport; [exact HG1 | exact MUf |].
      rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I]. }
    { exists g. eapply bytes_at_transport; [exact HG2 | exact MUf |].
      rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I]. } }
  destruct (Z.eq_dec LP 0) as [HLP0|HLPn].
  - (* no label: "reac-pw.conf" *)
    pose proof (Ew0 HLP0) as Ew. rewrite Ew in Hw0, HwC0, Hwap1, Hwap2.
    step. if_cases K; cbv iota.
    + do 2 step.
      eapply (en_call STR_BASE lab' m0);
        [exact Elab | exact Hw0 | exact HwC0 | exact HwL | exact HwN | exact HwB | exact Hwap1 | exact Hwap2
         | exact FR | exact ST1 | exact MI | exact MU | exact WM | exact HMC0 | exact HWR | exact HSSP0].
    + exfalso. zify_cond K. try (rewrite unsigned_lit in K by lia). lia.
  - (* a label was given *)
    pose proof (EwN HLPn) as Ew. rewrite Ew in Hw0, HwC0, Hwap1, Hwap2.
    step. if_cases K; cbv iota.
    + exfalso. zify_cond K. try (rewrite unsigned_lit in K by lia). lia.
    + do 2 step.
      eapply (en_call LP lab' m0);
        [exact Elab | exact Hw0 | exact HwC0 | exact HwL | exact HwN | exact HwB | exact Hwap1 | exact Hwap2
         | exact FR | exact ST1 | exact MI | exact MU | exact WM | exact HMC0 | exact HWR | exact HSSP0].
Qed.

End EN.

Theorem mf_entry_holds : snprintf_contract -> S_MF_ENTRY.
Proof.
  intros HSN HH HX. unfold m_file_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    mc s lab HPRE.
  pose proof (Z_to_bv_lit_self a0) as Ea0. pose proof (Z_to_bv_lit_self a1) as Ea1.
  pose proof (Z_to_bv_lit_self a2) as Ea2.
  pose proof (u64_range a2) as Ra2.
  set (C := bv_unsigned a0) in *. set (T := bv_unsigned a1) in *. set (LP := bv_unsigned a2) in *.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  clearbody C T LP. clear Ea0 Ea1 Ea2.
  pose proof HPRE as HP.
  destruct HP as (Hc0 & Hc16 & HNI & HMC & HWR & HSL & HAc & Hgen & Href & Hov & Ht0 & HTNI & HTC & HTlen & HTap &
                  HTapc & HLAB & HLX & (FRM & TM & HSSP & HIE & HS63) & HCAT & HWDS & (ST & HK & HS16 & HROM) & MI).
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HK.
  unfold SA, SEG_PLAIN in HIE. cbn [sa_img_end] in HIE.
  unfold apart, SEG_M_SIZE in HAc.
  assert (HC0 : 0 <= C /\ C + 9236 <= 2 ^ 64).
  { destruct HMC as (bsC & HBC & HEC). destruct HEC as (HL & _).
    pose proof (bytes_at_bound rsegs m C bsC HBC). unfold SEG_M_SIZE in *. lia. }
  pose proof (en_noimg C SEG_M_SIZE ltac:(lia) ltac:(unfold SEG_M_SIZE; lia) HNI) as HCimg.
  unfold SEG_M_SIZE in HCimg.
  destruct lab as [l|].
  - (* the caller's label *)
    destruct HLAB as (HLP0 & HLC). destruct HLX as (HLl & HLap1 & HLap2).
    unfold apart in HLap1, HLap2. unfold MC_READING in HLap2.
    pose proof (en_span_bound LP l) as Hspan.
    eapply (en_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m C T LP lo mc s (Some l)
              HPRE HSN HH HX LP l);
      [reflexivity | intros H; exfalso; exact (HLP0 H) | reflexivity | exact Ra2 | exact HLP0 | exact HLC
       | exact HLl | | eapply en_cstr_bytes; exact HLC | unfold apart; lia | unfold apart; lia].
    destruct HLC as (bsl & sll & _ & _ & Hnn & _). exact Hnn.
  - (* no label: "reac-pw.conf" *)
    cbn in HLAB.
    pose proof (en_span_bound STR_BASE S_base) as Hspan.
    assert (Hsb : cstr_span STR_BASE S_base = 13) by (vm_compute; reflexivity).
    eapply (en_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m C T LP lo mc s None
              HPRE HSN HH HX STR_BASE S_base);
      [reflexivity | intros _; reflexivity | intros H; exfalso; exact (H HLAB) | exact Ra2
       | unfold STR_BASE; lia | exact (en_sbase_at m MI) | rewrite en_sbase_len; lia
       | apply nulfree_forallb; vm_compute; reflexivity | exact en_sbase_bytes
       | unfold apart; rewrite Hsb; unfold STR_BASE; lia
       | unfold apart; rewrite Hsb; unfold STR_BASE; lia].
Qed.
