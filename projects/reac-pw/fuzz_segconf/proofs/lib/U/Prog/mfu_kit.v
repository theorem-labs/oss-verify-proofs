(** m_file (UBSan build, image 1696d6c34ffd): the lemmas the sub-pieces of S_MF_LINE share (cuts
    in U/Prog/mfu_cuts.v). Each sub-piece starts at a cut whose memory [mcut] holds the loop facts of the head
    (m_file_loop with the head's line number [line] and text [rest]). Inside the line it tracks the current memory m
    by [mfu_mid]: no byte written since mcut outside the footprint of the current model state mc (pend: m_key's
    kept_knock[n_kept] = 1 already stored), the writable view kept, mem_inv, the stack region [lo, sp0) present, the
    block holding mc. These are the hypotheses the step automation keeps up to date (munch, wmono, mem_inv, stk) once
    destructed (unfold mfu_W, M_FILE_W in the munch before a frame store, so that `inside` computes), plus the block's
    encoding, which the walk keeps across a block store (the store lemmas of Prog/mfp_mconf.v).

    The lemmas:
    - mfu_mid_init: the cut memory itself.
    - mfu_cut_bytes / mfu_cut_cstr: a byte string of mcut apart from the stack region and from the block (the text)
      is unchanged in m.
    - mfu_tail: the tail 0x146b4 with H_MF_TAIL, from any state of the line (the frame cells it needs at m given).
    - mfu_refuse (CPS): `jal m_refuse` from m_file's frame, a0 = c, a1 = line + 1.
    - mfu_strip (CPS): `jal strip` on two 8-byte scratch cells of the frame holding a byte string of the line.
    - mfu_ieq (CPS): `jal ieq` on a byte string of the line and a word literal of .rodata.
    - mfu_lits: the word literals m_file passes to ieq, and the five words of m_key.words, as C strings.
    - mfu_snprintf_file (CPS): `jal snprintf` 0x148b8, g->role_file or g->ignore_file = c->reading.
    - mfu_stack_call: a callee that writes only below sp (its own frame) keeps mfu_mid. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Image.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec mfu_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import m_refuse_c strip_c ieq_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import mfp_mconf.
Import ListNotations.
Open Scope Z_scope.

(** The footprint of the line so far: M_FILE_W of the current model state, and kept_knock[n_kept] when pending. *)
Definition mfu_W (sp0 c : Z) (k0 : nat) (mc : mconf) (pend : bool) : list ivl :=
  M_FILE_W sp0 c k0 mc ++
  (if pend then [(c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)),
                  c + MC_KNOCK + 4 * Z.of_nat (length (mc_kept mc)) + 4)] else []).

(** The memory m inside a line, from the cut memory mcut. *)
Definition mfu_mid (mcut m : word -> option byte) (sp0 lo c : Z) (k0 : nat) (mc : mconf) (pend : bool) : Prop :=
  munch (mfu_W sp0 c k0 mc pend) mcut m /\ wmono rsegs mcut m /\ mem_inv rsegs m /\ stk rsegs m lo sp0 /\
  mconf_atp rsegs pend m c mc.

(** ** Shared helpers (KitU) *)

Lemma mfu_wa_bv : forall x : word, wa (bv_unsigned x) = x.
Proof. intros x. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

Lemma mfu_munch_comp : forall W W1 W2 (m0 m1 m2 : word -> option byte),
  munch W1 m0 m1 -> munch W2 m1 m2 -> sub_fp W1 W -> sub_fp W2 W -> munch W m0 m2.
Proof.
  intros W W1 W2 m0 m1 m2 H1 H2 S1 S2.
  apply (munch_trans W m0 m1 m2); [exact (munch_weaken W1 W m0 m1 S1 H1) | exact (munch_weaken W2 W m1 m2 S2 H2)].
Qed.

(** sub_fp from containment: each interval of W is empty or inside an interval of W'. *)
Lemma mfu_sub_fp : forall W W',
  Forall (fun iv => snd iv <= fst iv \/ Exists (fun iv' => fst iv' <= fst iv /\ snd iv <= snd iv') W') W ->
  sub_fp W W'.
Proof.
  intros W W' H x Hx. induction H as [|iv W0 Hiv HW IH]; [exact I|].
  destruct iv as [l h]. cbn [outside fst snd] in *. split; [|exact IH].
  destruct Hiv as [E|E]; [lia|]. clear - E Hx.
  induction W' as [|[l' h'] W' IH']; [inversion E|].
  cbn [outside] in Hx. destruct Hx as [N Hx]. apply Exists_cons in E as [E|E].
  - cbn [fst snd] in E. lia.
  - exact (IH' E Hx).
Qed.

(** A stack region after a call: unchanged outside W, and present in m' where W wrote. *)
Lemma mfu_stk_patch : forall (m m' : word -> option byte) W lo hi a b,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' -> stk rsegs m' a b ->
  (forall x, lo <= x < hi -> outside W x \/ a <= x < b) -> stk rsegs m' lo hi.
Proof.
  intros m m' W lo hi a b (H1 & H2 & H) MU WM (_ & _ & H') C. split; [exact H1|]. split; [exact H2|].
  intros x Hx. destruct (H x Hx) as [Hw Hb]. split; [apply WM; exact Hw|].
  destruct (C x Hx) as [O|R]; [|exact (proj2 (H' x R))].
  destruct Hb as [bb Hb]. exists bb. unfold mrd in *. rewrite MU; [exact Hb|].
  rewrite wa_unsigned by lia. exact O.
Qed.

(** A byte of a writable view is a task byte (MemNorm.task_mem's condition) when the memory is task_mem. *)
Lemma mfu_wview_task : forall (m : word -> option byte) (x : word), MemNorm.task_mem rsegs m ->
  wview rsegs m x <> None -> find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m x T W. destruct (m x) as [b|] eqn:E; [exact (T x b E)|].
  left. intros Nf. apply W. unfold wview. rewrite E, Nf. reflexivity.
Qed.

Lemma mfu_some_of_mrd : forall (m : word -> option byte) x, seg_rom rsegs (wa x) = None ->
  (exists b, mrd rsegs m (wa x) = Some b) -> exists b, m (wa x) = Some b.
Proof.
  intros m x N [b H]. exists b. unfold mrd in H. destruct (m (wa x)); [exact H|]. rewrite N in H. discriminate.
Qed.

Lemma mfu_bytes_some : forall (m : word -> option byte) a bs x, bytes_at rsegs m a bs ->
  a <= x < a + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a bs x (_ & _ & H) Hx. pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as E.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:N; [exists b; exact E|].
  apply nth_error_None in N. lia.
Qed.

(** The sizes an encoded state has. *)
Lemma mfu_atp_lens : forall pend (m : word -> option byte) c mc, mconf_atp rsegs pend m c mc ->
  (length (mc_seg mc) <= 32)%nat /\ (length (mc_kept mc) <= 8)%nat.
Proof.
  intros pend m c mc (bs & _ & E). unfold mconf_encp in E. destruct E as (_ & S & _ & _ & _ & _ & K & _).
  split; assumption.
Qed.

Lemma mfu_atp_transport : forall pend (m m' : word -> option byte) c mc W, mconf_atp rsegs pend m c mc ->
  munch W m m' -> disjoint_from W c SEG_M_SIZE -> mconf_atp rsegs pend m' c mc.
Proof.
  intros pend m m' c mc W (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

(** The footprint of the line lies in the frame's stack region or in the block. *)
Lemma mfu_W_disj : forall sp0 c k0 mc pend a n,
  (length (mc_seg mc) <= 32)%nat -> (length (mc_kept mc) <= 8)%nat ->
  apart a n (sp0 - M_FILE_STACK) sp0 -> apart a n c (c + SEG_M_SIZE) ->
  disjoint_from (mfu_W sp0 c k0 mc pend) a n.
Proof.
  intros sp0 c k0 mc pend a n Hs Hk A1 A2. unfold apart in *.
  unfold mfu_W, M_FILE_W, mseg_addr, kept_addr.
  destruct pend; cbn [app disjoint_from];
    unfold MC_N, MC_REFUSED, MC_KEPT, MC_KEPT_LEN, MC_KNOCK, MC_NKEPT, MC_READING, MSEG_SIZE, SEG_M_SIZE in *;
    repeat split; first [exact I | lia].
Qed.

Lemma mfu_out_or_in : forall sp0 c k0 mc pend x,
  (length (mc_seg mc) <= 32)%nat -> (length (mc_kept mc) <= 8)%nat ->
  outside (mfu_W sp0 c k0 mc pend) x \/ (sp0 - M_FILE_STACK <= x < sp0) \/ (c <= x < c + SEG_M_SIZE).
Proof.
  intros sp0 c k0 mc pend x Hs Hk.
  assert (D1 : (sp0 - M_FILE_STACK <= x < sp0) \/ ~ (sp0 - M_FILE_STACK <= x < sp0)) by lia.
  assert (D2 : (c <= x < c + SEG_M_SIZE) \/ ~ (c <= x < c + SEG_M_SIZE)) by lia.
  destruct D1 as [D1|D1]; [right; left; exact D1|]. destruct D2 as [D2|D2]; [right; right; exact D2|].
  left. apply (disjoint_outside _ x 1); [|lia].
  apply mfu_W_disj; [exact Hs | exact Hk | unfold apart; lia | unfold apart; lia].
Qed.

(** Writes inside the frame's stack region stay inside the line's footprint. *)
Lemma mfu_sub_fp_stack : forall W sp0 c k0 mc pend,
  Forall (fun iv => sp0 - M_FILE_STACK <= fst iv /\ snd iv <= sp0) W -> sub_fp W (mfu_W sp0 c k0 mc pend).
Proof.
  intros W sp0 c k0 mc pend H x Hx. unfold mfu_W, M_FILE_W in Hx. cbn [app outside] in Hx.
  destruct Hx as [Hs _]. induction H as [|iv W0 Hiv HW IH]; [exact I|].
  destruct iv as [l h]. cbn [outside fst snd] in *. split; [lia | exact IH].
Qed.

(** A block no byte of which lies in a reserved segment is apart from any range inside one reserved segment
    (noimg_apart of reac_segconf_parse.v). *)
Definition mfu_in_resv (x k : Z) : bool :=
  existsb (fun s => (bv_unsigned (fst s) <=? x) && (x + k <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs).

Lemma mfu_noimg_apart : forall a n x k, blk_noimg rsegs a n -> 0 < n -> 0 < k -> mfu_in_resv x k = true ->
  apart x k a (a + n).
Proof.
  intros a n x k NI Hn Hk E. unfold mfu_in_resv in E. apply existsb_exists in E as (s & Hs & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold apart.
  destruct (Z_le_gt_dec (x + k) a) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (a + n) x) as [L2|L2]; [right; exact L2|].
  exfalso. destruct (Z_le_gt_dec a x) as [L3|L3].
  - apply (NI (x - a) ltac:(lia) s Hs). lia.
  - apply (NI 0 ltac:(lia) s Hs). lia.
Qed.

Lemma mfu_resv_got : mfu_in_resv (sa_got_guard SA) 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mfu_resv_guard : mfu_in_resv (sa_guard SA) 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mfu_resv_cat : mfu_in_resv (sa_catalogue SA) CAT_BYTES = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mfu_resv_words : mfu_in_resv M_KEY_WORDS 40 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mfu_slack4 : forall c, c mod 16 = 0 -> (- (c + SEG_M_SIZE)) mod 8 = 4.
Proof.
  intros c H. unfold SEG_M_SIZE. pose proof (Z.div_mod c 16 ltac:(lia)) as D. rewrite H in D.
  replace (- (c + 9236)) with (4 + (- (2 * (c / 16)) - 1155) * 8) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(** The facts of the cut memory that hold at any memory of the line. *)
Lemma mfu_env : forall mcut m fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    mc pend,
  m_file_loop mcut fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m sp0 lo c k0 mc pend ->
  MemNorm.task_mem rsegs m /\ ssp_ok m /\ cat_img rsegs m (sa_catalogue SA) /\ words_img m /\
  wr_at rsegs m c SEG_M_SIZE /\ blk_slack rsegs m c SEG_M_SIZE /\ stack_ok rsegs m lo sp0 M_FILE_STACK.
Proof.
  intros mcut m fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 mc pend L M.
  destruct M as (MU & WM & MI & ST & AT).
  destruct (mfu_atp_lens _ _ _ _ AT) as [Ls Lk].
  destruct L as (Lsp & SV & C8 & C10 & C18 & C20 & C28 & C30 & C0 & C16 & NI & MA & WR & SL & AP & CO & K0 & L0 &
                 L1 & R1 & O1 & P0 & PNI & CS & AP1 & AP2 & PE & CAT & WI & SO & MI0).
  clear SV C8 C10 C18 C20 C28 C30 MA CO K0 L0 L1 R1 O1 P0 PNI CS AP1 AP2.
  destruct PE as (FRM & TM & SSP & IL & SPH). destruct SO as (STK0 & DEP & S16 & NR).
  assert (LO0 : 0 <= lo) by (destruct STK0 as [? _]; assumption).
  assert (DJ : forall a n, apart a n (sp0 - M_FILE_STACK) sp0 -> apart a n c (c + SEG_M_SIZE) ->
               disjoint_from (mfu_W sp0 c k0 mc pend) a n)
    by (intros a n H1 H2; apply mfu_W_disj; assumption).
  assert (LOW : forall a n, a + n <= sa_img_end SA -> apart a n (sp0 - M_FILE_STACK) sp0)
    by (intros a n H; unfold apart; left; lia).
  assert (NSE : 0 < SEG_M_SIZE) by (unfold SEG_M_SIZE; lia).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* task_mem *)
    intros a b E. destruct (mfu_out_or_in sp0 c k0 mc pend (bv_unsigned a) Ls Lk) as [O|[I1|I2]].
    + rewrite (MU a O) in E. exact (TM a b E).
    + apply (mfu_wview_task mcut a TM).
      destruct STK0 as (_ & _ & SK). destruct (SK (bv_unsigned a) ltac:(lia)) as [Wv _].
      rewrite mfu_wa_bv in Wv. exact Wv.
    + apply (mfu_wview_task mcut a TM).
      destruct WR as (_ & _ & WK). pose proof (WK (bv_unsigned a - c) ltac:(lia)) as Wv.
      replace (c + (bv_unsigned a - c)) with (bv_unsigned a) in Wv by lia. rewrite mfu_wa_bv in Wv. exact Wv.
  - (* ssp_ok *)
    destruct SSP as (G1 & g & G2). split; [|exists g].
    + eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8. apply DJ.
      * apply LOW. cbn [SA SEG_UBSAN sa_got_guard sa_img_end]. lia.
      * exact (mfu_noimg_apart c SEG_M_SIZE (sa_got_guard SA) (Z.of_nat 8) NI NSE ltac:(lia) mfu_resv_got).
    + eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8. apply DJ.
      * apply LOW. cbn [SA SEG_UBSAN sa_guard sa_img_end]. lia.
      * exact (mfu_noimg_apart c SEG_M_SIZE (sa_guard SA) (Z.of_nat 8) NI NSE ltac:(lia) mfu_resv_guard).
  - (* cat_img *)
    intros a Ha. rewrite <- (CAT a Ha). unfold mrd.
    assert (Ha' : 0 <= a < 2 ^ 64) by (cbn [SA SEG_UBSAN sa_catalogue] in Ha; unfold CAT_BYTES in Ha; lia).
    rewrite (MU (wa a)); [reflexivity|]. rewrite wa_unsigned by exact Ha'.
    apply (disjoint_outside _ (sa_catalogue SA) CAT_BYTES); [|exact Ha]. apply DJ.
    + apply LOW. cbn [SA SEG_UBSAN sa_catalogue sa_img_end]. unfold CAT_BYTES. lia.
    + exact (mfu_noimg_apart c SEG_M_SIZE (sa_catalogue SA) CAT_BYTES NI NSE ltac:(unfold CAT_BYTES; lia)
               mfu_resv_cat).
  - (* words_img *)
    intros a Ha. rewrite <- (WI a Ha). unfold mrd.
    assert (Ha' : 0 <= a < 2 ^ 64) by (unfold M_KEY_WORDS in Ha; lia).
    rewrite (MU (wa a)); [reflexivity|]. rewrite wa_unsigned by exact Ha'.
    apply (disjoint_outside _ M_KEY_WORDS 40); [|exact Ha]. apply DJ.
    + apply LOW. cbn [SA SEG_UBSAN sa_img_end]. unfold M_KEY_WORDS. lia.
    + exact (mfu_noimg_apart c SEG_M_SIZE M_KEY_WORDS 40 NI NSE ltac:(lia) mfu_resv_words).
  - exact (wr_at_transport rsegs mcut m c SEG_M_SIZE WR WM).
  - (* blk_slack: its 4 bytes lie between the block and the stack region *)
    destruct SL as (sl & B & Hsl). rewrite (mfu_slack4 c C16) in Hsl.
    exists (firstn 4 sl). rewrite (mfu_slack4 c C16). rewrite length_firstn.
    split; [|lia].
    rewrite <- (firstn_skipn 4 sl) in B. apply bytes_at_app in B as [B _].
    eapply bytes_at_transport; [exact B | exact MU |]. rewrite length_firstn.
    replace (Z.of_nat (Nat.min 4 (length sl))) with 4 by lia.
    apply DJ; unfold apart in *; lia.
  - split; [exact ST|]. split; [exact DEP|]. split; [exact S16|]. exact NR.
Qed.

(** The loop facts the kit uses most. *)
Lemma mfu_loop_basic : forall m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  sp + M_FILE_FRAME = sp0 /\ c <> 0 /\ c mod 16 = 0 /\ blk_noimg rsegs c SEG_M_SIZE /\
  apart c (SEG_M_SIZE + 4) lo sp0 /\ stack_ok rsegs m lo sp0 M_FILE_STACK /\ sa_img_end SA <= lo /\ sp0 < 2 ^ 63.
Proof.
  intros m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 L.
  destruct L as (Lsp & _ & _ & _ & _ & _ & _ & _ & C0 & C16 & NI & _ & _ & _ & AP & _ & _ & _ & _ & _ & _ & _ & _ &
                 _ & _ & _ & PE & _ & _ & SO & _).
  destruct PE as (_ & _ & _ & IL & SPH).
  exact (conj Lsp (conj C0 (conj C16 (conj NI (conj AP (conj SO (conj IL SPH))))))).
Qed.

Lemma mfu_mod8 : forall x q, x = 8 * q -> x mod 8 = 0.
Proof. intros x q ->. rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.

Lemma mfu_sp16 : forall sp sp0, sp + M_FILE_FRAME = sp0 -> sp0 mod 16 = 0 -> sp mod 16 = 0.
Proof.
  intros sp sp0 H S. unfold M_FILE_FRAME in H. replace sp with (sp0 + (-17) * 16) by lia.
  rewrite Z_mod_plus_full. exact S.
Qed.

(** An 8-byte cell of a present stack region, as a writable cell. *)
Lemma mfu_cell_rw : forall (m : word -> option byte) lo hi a v, stk rsegs m lo hi -> lo <= a -> a + 8 <= hi ->
  bytes_at rsegs m a (le8 v) -> rw_cells rsegs m a [C8 v].
Proof.
  intros m lo hi a v (H0 & H1 & H) La Ha B. split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

(** A write apart from a C string's span keeps it (its slack cut to what cstr_at needs). *)
Lemma mfu_cstr_transport : forall W (m m' : word -> option byte) a s,
  cstr_at rsegs m a s -> munch W m m' -> disjoint_from W a (cstr_span a s) -> cstr_at rsegs m' a s.
Proof.
  intros W m m' a s (bs & sl & B & Ez & N & SLK) MU D.
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
  rewrite length_app; cbn [length]. rewrite Lk, Lbs.
  replace (Z.of_nat (length s + S k)) with (cstr_span a s) by (unfold cstr_span; lia). exact D.
Qed.

Lemma mfu_map_skipn : forall {A B} (f : A -> B) k l, map f (skipn k l) = skipn k (map f l).
Proof. intros A B f k. induction k as [|k IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

(** The suffix of a C string from its k-th byte. *)
Lemma mfu_cstr_skipn : forall (m : word -> option byte) a s k, cstr_at rsegs m a s -> (k <= length s)%nat ->
  cstr_at rsegs m (a + Z.of_nat k) (skipn k s).
Proof.
  intros m a s k (bs & sl & B & Ez & N & SLK) Hk.
  assert (Lb : length bs = length s) by (rewrite <- Ez; unfold zs; rewrite length_map; reflexivity).
  exists (skipn k bs), sl.
  rewrite <- (firstn_skipn k bs) in B. rewrite <- app_assoc in B. apply bytes_at_app in B as [_ B].
  rewrite length_firstn in B. replace (Nat.min k (length bs)) with k in B by lia.
  split; [exact B|]. split; [unfold zs in *; rewrite mfu_map_skipn, Ez; reflexivity|].
  split; [intros H; apply N; rewrite <- (firstn_skipn k s); apply in_or_app; right; exact H|].
  rewrite length_skipn. replace (a + Z.of_nat k + Z.of_nat (length s - k)) with (a + Z.of_nat (length s)) by lia.
  exact SLK.
Qed.

Lemma mfu_skipn_app_cons : forall {A} (l : list A) x r, skipn (S (length l)) (l ++ x :: r) = r.
Proof. intros A l x r. induction l as [|y l IH]; [reflexivity|]. cbn [app length skipn]. exact IH. Qed.

(** The text after the line is the text from mf_next on. *)
Lemma mfu_rest_skipn : forall rest,
  mf_rest rest = skipn (length rest - length (mf_rest rest)) rest /\ (length (mf_rest rest) <= length rest)%nat.
Proof.
  intros rest. pose proof (mf_line_rest rest) as H.
  set (l := mf_line rest) in *. set (r := mf_rest rest) in *. clearbody l r.
  destruct H as [[E D]|[E [Q D]]]; rewrite D.
  - split.
    + rewrite E. symmetry. apply mfu_skipn_app_cons.
    + rewrite E, length_app. cbn [length]. lia.
  - subst r. split.
    + rewrite E. symmetry. apply skipn_all.
    + cbn [length]. lia.
Qed.

(** A larger model state has a larger footprint. *)
Lemma mfu_W_grow : forall sp0 c k0 mc mc', mf_grows mc mc' ->
  sub_fp (mfu_W sp0 c k0 mc false) (M_FILE_W sp0 c k0 mc').
Proof.
  intros sp0 c k0 mc mc' [Gs Gk] x Hx. unfold mfu_W, M_FILE_W, mseg_addr, kept_addr in *.
  cbn [app outside] in *.
  destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & _).
  unfold MC_KEPT_LEN, MSEG_SIZE in *.
  repeat split; first [exact I | lia].
Qed.

Lemma mfu_refuse_lens : forall mc l k,
  length (mc_seg (m_refuse mc l k)) = length (mc_seg mc) /\
  length (mc_kept (m_refuse mc l k)) =
    (if Z.of_nat (length (mc_kept mc)) <? 8 then S (length (mc_kept mc)) else length (mc_kept mc)).
Proof.
  intros mc l k. unfold m_refuse. cbv zeta. cbn [mc_seg mc_kept]. split; [reflexivity|].
  destruct (Z.of_nat (length (mc_kept mc)) <? 8); [rewrite length_app; cbn [length]; lia | reflexivity].
Qed.

(** mfu_stack_call's statement, here so that the call lemmas before it can use it. *)
Lemma mfu_stack_keep : forall mcut m m' fcc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    mc pend d,
  m_file_loop mcut fcc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m sp0 lo c k0 mc pend -> 0 <= d <= M_FILE_STACK - M_FILE_FRAME ->
  munch [(sp - d, sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (sp - d) sp ->
  mfu_mid mcut m' sp0 lo c k0 mc pend.
Proof.
  intros mcut m m' fcc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 mc pend d
    L M Hd MU' WM' MI' ST'.
  destruct M as (MU & WM & MI & ST & AT).
  destruct (mfu_loop_basic _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _ L)
    as (Lsp & C0 & C16 & NI & APc & SO0 & IL & SPH).
  destruct SO0 as (STK0 & DEP & S16 & NR).
  unfold M_FILE_FRAME in *.
  split; [|split; [exact (wmono_trans rsegs mcut m m' WM WM')|split; [exact MI'|split]]].
  - apply (mfu_munch_comp _ _ _ mcut m m' MU MU'); [intros x Hx; exact Hx|].
    apply mfu_sub_fp_stack. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
  - apply (mfu_stk_patch m m' [(sp - d, sp)] lo sp0 (sp - d) sp ST MU' WM' ST').
    intros x Hx. destruct (Z_lt_le_dec x (sp - d)) as [H1|H1]; [left; cbn [outside]; split; [lia|exact I]|].
    destruct (Z_lt_le_dec x sp) as [H2|H2]; [right; lia|left; cbn [outside]; split; [lia|exact I]].
  - eapply mfu_atp_transport; [exact AT | exact MU' |]. cbn [disjoint_from]. split; [|exact I].
    unfold apart in APc. lia.
Qed.

Lemma mfu_mid_init : forall m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid m m sp0 lo c k0 mc false.
Proof.
  intros m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 L.
  destruct L as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                 _ & _ & _ & _ & SO & MI).
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact (proj1 SO)|]. exact MA.
Qed.

(** ** The text of the cut is unchanged *)
Lemma mfu_cut_bytes : forall mcut m fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    mc pend a bs,
  m_file_loop mcut fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m sp0 lo c k0 mc pend ->
  bytes_at rsegs mcut a bs -> apart a (Z.of_nat (length bs)) lo sp0 ->
  apart a (Z.of_nat (length bs)) c (c + SEG_M_SIZE) ->
  bytes_at rsegs m a bs.
Proof.
  intros mcut m fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 mc pend a bs
    L M B A1 A2.
  destruct M as (MU & _ & _ & _ & AT). destruct (mfu_atp_lens _ _ _ _ AT) as [Ls Lk].
  destruct (mfu_loop_basic _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _ L)
    as (_ & _ & _ & _ & _ & (_ & DEP & _ & _) & _ & _).
  eapply bytes_at_transport; [exact B | exact MU |].
  apply mfu_W_disj; [exact Ls | exact Lk | unfold apart in *; lia | exact A2].
Qed.

Lemma mfu_cut_cstr : forall mcut m fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    mc pend a s,
  m_file_loop mcut fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m sp0 lo c k0 mc pend ->
  cstr_at rsegs mcut a s -> apart a (Z.of_nat (length s) + 8) lo sp0 -> apart a (cstr_span a s) c (c + SEG_M_SIZE) ->
  cstr_at rsegs m a s.
Proof.
  intros mcut m fc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 mc pend a s
    L M CS A1 A2.
  destruct M as (MU & _ & _ & _ & AT). destruct (mfu_atp_lens _ _ _ _ AT) as [Ls Lk].
  destruct (mfu_loop_basic _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _ L)
    as (_ & _ & _ & _ & _ & (_ & DEP & _ & _) & _ & _).
  eapply mfu_cstr_transport; [exact CS | exact MU |].
  apply mfu_W_disj; [exact Ls | exact Lk | | exact A2].
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  unfold apart, cstr_span in *. lia.
Qed.

(** ** The tail
    From a state of the line with model state (mc', cur') (no knock pending), the frame's fixed cells and the cursor
    cell at m, the counters at most one more than at the cut, and the tail's registers: the cut's post. *)
Lemma mfu_tail : forall n (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fc F : bvmap 5 word) (fcc fc : bv 32) (mcut m : word -> option byte) (lo : Z)
    (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat)
    (rest : list Z) (mc' : mconf) (cur' : option nat),
  H_MF_TAIL n -> (length rest <= n)%nat -> rest <> [] ->
  m_file_loop mcut fcc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m (bv_unsigned sp0) lo c k0 mc' false ->
  saved_at rsegs m (bv_unsigned sp + M_FILE_SAVE) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] ->
  cell8 m (bv_unsigned sp + 0x8) (- 1 - c) -> cell8 m (bv_unsigned sp + 0x10) (c + MC_KNOCK) ->
  cell8 m (bv_unsigned sp + 0x18) (- 1 - (c + MC_KNOCK)) -> cell8 m (bv_unsigned sp + 0x20) (c + MC_READING) ->
  cell8 m (bv_unsigned sp + 0x28) (c + MC_N) -> cell8 m (bv_unsigned sp + 0x30) (cur_ptr c cur') ->
  mf_grows mc mc' -> cur_ok mc' cur' ->
  mc_refused mc' <= mc_refused mc + 1 -> mc_overflow mc' <= mc_overflow mc + 1 ->
  frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get Fc k) ->
  m_file_regs c (mf_next p rest) (line + 1) s0 s2 s3 s4 s6 s7 s8 s9 s10 s11 ->
  evt rsegs (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 Fc mcut lo c k0 (mf_fin (mc', cur') line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 M_FILE_TAIL) fc None m (seg_rom rsegs)).
Proof.
  intros n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fc F fcc fc mcut m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest mc' cur'
    HT Hn Hr L M SV X8 X10 X18 X20 X28 X30 G CO RF OF FRM FR REGS.
  destruct (mfu_env _ _ _ _ _ _ _  _ _ _ _ _ _ _  _ _ _ _ _ _ _  _ _ _ _ _ _ _ L M)
    as (TM & SSP & CAT & WI & WR & SL & SO).
  pose proof M as M0. destruct M0 as (MU & WM & MI & ST & AT).
  pose proof L as L0.
  destruct L0 as (Lsp & _ & _ & _ & _ & _ & _ & _ & C0 & C16 & NI & _ & _ & _ & AP & _ & K0 & LN0 & LN1 & R1 & O1 &
                  P0 & PNI & CS & AP1 & AP2 & PE & _ & _ & _ & _).
  destruct PE as (_ & _ & _ & IL & SPH).
  pose proof G as [Gs Gk].
  destruct (mfu_rest_skipn rest) as [RS RL].
  pose proof (mf_rest_lt rest Hr) as RLT.
  assert (P0' : 0 <= p) by (destruct CS as (bs & sl & B & _); exact (proj1 B)).
  assert (CS0 : cstr_at rsegs mcut (mf_next p rest) (mf_rest rest)).
  { pose proof (mfu_cstr_skipn mcut p rest (length rest - length (mf_rest rest)) CS ltac:(lia)) as H.
    rewrite <- RS in H. exact H. }
  assert (EN : mf_next p rest + Z.of_nat (length (mf_rest rest)) = p + Z.of_nat (length rest))
    by (unfold mf_next; lia).
  assert (AP1' : apart (mf_next p rest) (Z.of_nat (length (mf_rest rest)) + 8) lo (bv_unsigned sp0)).
  { unfold apart in *. unfold mf_next in *. lia. }
  assert (AP2' : apart (mf_next p rest) (cstr_span (mf_next p rest) (mf_rest rest)) c (c + SEG_M_SIZE)).
  { unfold apart, cstr_span in *. rewrite EN.
    set (KK := (- (p + Z.of_nat (length rest) + 1)) mod 8) in *. unfold mf_next in *. lia. }
  assert (CSm : cstr_at rsegs m (mf_next p rest) (mf_rest rest)).
  { eapply mfu_cut_cstr; [exact L | exact M | exact CS0 | exact AP1' | exact AP2']. }
  assert (L' : m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c (mf_next p rest) mc' cur' (line + 1) k0
                 (mf_rest rest) ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11).
  { unfold m_file_loop.
    split; [exact Lsp|]. split; [exact SV|]. split; [exact X8|]. split; [exact X10|]. split; [exact X18|].
    split; [exact X20|]. split; [exact X28|]. split; [exact X30|]. split; [exact C0|]. split; [exact C16|].
    split; [exact NI|]. split; [exact AT|]. split; [exact WR|]. split; [exact SL|]. split; [exact AP|].
    split; [exact CO|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold mf_next; lia|].
    split.
    { intros i Hi s Hs Hin.
      apply (PNI (Z.of_nat (length rest - length (mf_rest rest)) + i) ltac:(lia) s Hs).
      unfold mf_next in Hin. lia. }
    split; [exact CSm|]. split; [exact AP1'|]. split; [exact AP2'|].
    split; [split; [exact FRM|]; split; [exact TM|]; split; [exact SSP|]; split; [exact IL | exact SPH]|].
    split; [exact CAT|]. split; [exact WI|]. split; [exact SO|]. exact MI. }
  assert (LT : (length (mf_rest rest) < n)%nat) by lia.
  pose proof (HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c (mf_next p rest) (line + 1) mc' cur' k0
                (mf_rest rest) LT L' REGS) as E.
  destruct (m_lines_ok (lines (mf_rest rest)) (mc', cur') (line + 1) CO) as [GF _]. cbn [fst] in GF.
  eapply evt_mono; [exact E|]. intros ms' Q.
  unfold ret_void_fp in Q. unfold mfu_post, mf_fin, ret_void_fp.
  destruct Q as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' &
                 m' & Ems & FRM' & FR' & MU' & WM' & MI' & TM' & ST' & Q').
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'.
  split; [exact Ems|]. split; [exact FRM'|].
  split; [intros k Hk; rewrite (FR' k Hk); exact (FR k Hk)|].
  split.
  { apply (mfu_munch_comp _ _ _ mcut m m' MU MU'); [apply mfu_W_grow; exact GF | intros x Hx; exact Hx]. }
  split; [exact (wmono_trans rsegs mcut m m' WM WM')|].
  split; [exact MI'|]. split; [exact TM'|]. split; [exact ST'|]. exact Q'.
Qed.

(** ** m_refuse(c, line + 1) from m_file's frame (sp the frame's sp; no refusal yet in this line). The continuation
    gets the state after it (the refusal's footprint added) and m_refuse's own footprint, to carry its other facts. *)
Lemma mfu_refuse : m_refuse_contract -> forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fcc fc : bv 32) (mcut m : word -> option byte) (lo : Z)
    (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc0 : mconf) (cur : option nat)
    (k0 : nat) (rest : list Z) (mc : mconf) (pend : bool),
  m_file_loop mcut fcc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc0 cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 -> rest <> [] ->
  mfu_mid mcut m (bv_unsigned sp0) lo c k0 mc pend ->
  mf_grows mc0 mc -> mc_refused mc = mc_refused mc0 ->
  frm0 fc -> bv_unsigned a0 = c -> bv_unsigned a1 = line + 1 ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mfu_mid mcut m' (bv_unsigned sp0) lo c k0 (m_refuse mc (line + 1) pend) false ->
     munch (m_refuse_W (bv_unsigned sp) c mc) m m' -> wmono rsegs m m' ->
     frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
     evt rsegs P
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom rsegs))) ->
  evt rsegs P
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 M_REFUSE) fc None m (seg_rom rsegs)).
Proof.
  intros RC P ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fcc fc mcut m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc0 cur k0 rest mc pend
    L Hr M G RE FRM A0 A1 K.
  destruct (mfu_env _ _ _ _ _ _ _  _ _ _ _ _ _ _  _ _ _ _ _ _ _  _ _ _ _ _ _ _ L M)
    as (TM & SSP & CAT & WI & WR & SL & SO).
  pose proof M as M0. destruct M0 as (MU & WM & MI & ST & AT).
  destruct (mfu_atp_lens _ _ _ _ AT) as [Ls Lk].
  pose proof L as L0.
  destruct L0 as (Lsp & _ & _ & _ & _ & _ & _ & _ & C0 & C16 & NI & _ & _ & _ & AP & _ & K0 & LN0 & LN1 & R1 & _ &
                  _ & _ & _ & _ & _ & PE & _ & _ & _ & _).
  destruct PE as (_ & _ & _ & IL & SPH).
  destruct G as [Gs Gk].
  assert (RL1 : (1 <= length rest)%nat) by (destruct rest; [congruence | cbn [length]; lia]).
  destruct SO as (STK & DEP & S16 & NR).
  pose proof (mfu_sp16 _ _ Lsp S16) as SP16.
  unfold M_FILE_FRAME in Lsp.
  assert (FS : M_FILE_STACK = 6224) by (unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia).
  assert (RS : M_REFUSE_STACK = 5952) by (unfold M_REFUSE_STACK, PRINTF_K; lia).
  assert (PRE : m_refuse_pre m fc (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) mc pend).
  { rewrite A0, A1. unfold m_refuse_pre.
    split; [exact C0|]. split; [exact C16|]. split; [exact NI|]. split; [exact AT|]. split; [exact WR|].
    split; [exact SL|]. split; [unfold apart in *; lia|]. split; [lia|]. split; [lia|].
    split; [split; [exact FRM|]; split; [exact TM|]; split; [exact SSP|]; split; [exact IL | lia]|].
    split; [|exact MI].
    split; [exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp0) STK ltac:(lia)))|].
    split; [lia|]. split; [exact SP16|]. intros a Ha. apply NR. lia. }
  pose proof (RC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo mc pend PRE) as E.
  eapply evt_cut; [exact E|]. intros ms' Q. unfold ret_void_fp in Q.
  destruct Q as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' &
                 m' & Ems & FRM' & FR' & MU' & WM' & MI' & TM' & ST' & Q').
  subst ms'. cbv beta in Q'. rewrite A0 in MU', Q'. rewrite A1 in Q'.
  apply K; [|exact MU' | exact WM' | exact FRM' | exact FR'].
  destruct (mfu_refuse_lens mc (line + 1) pend) as [RLs RLk].
  split; [|split; [exact (wmono_trans rsegs mcut m m' WM WM')|split; [exact MI'|split]]].
  - (* the footprint: the line's so far and m_refuse's, both inside the new state's *)
    apply (mfu_munch_comp _ _ _ mcut m m' MU MU').
    + intros x Hx. unfold mfu_W, M_FILE_W, kept_addr, mseg_addr in *. rewrite RLs, RLk in Hx.
      destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:E8; [apply Z.ltb_lt in E8 | apply Z.ltb_ge in E8];
        destruct pend; cbn [app outside] in *;
        unfold MC_N, MC_REFUSED, MC_KEPT, MC_KEPT_LEN, MC_KNOCK, MC_NKEPT, MC_READING, MSEG_SIZE in *;
        repeat split; first [exact I | lia].
    + intros x Hx. unfold mfu_W, M_FILE_W, m_refuse_W, kept_addr, mseg_addr in *. rewrite RLs, RLk in Hx.
      destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:E8; [apply Z.ltb_lt in E8 | apply Z.ltb_ge in E8];
        cbn [app outside] in *;
        unfold MC_N, MC_REFUSED, MC_KEPT, MC_KEPT_LEN, MC_KNOCK, MC_NKEPT, MC_READING, MSEG_SIZE in *;
        repeat split; first [exact I | lia].
  - (* the stack region: m_refuse writes below sp and in the block, apart from [sp, sp0) *)
    apply (mfu_stk_patch m m' (m_refuse_W (bv_unsigned sp) c mc) lo (bv_unsigned sp0) lo (bv_unsigned sp)
             ST MU' WM' ST').
    intros x Hx. destruct (Z_lt_le_dec x (bv_unsigned sp)) as [Hl|Hl]; [right; lia|left].
    unfold m_refuse_W, kept_addr.
    destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:E8; [apply Z.ltb_lt in E8 | apply Z.ltb_ge in E8];
      cbn [app outside];
      unfold apart, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED, SEG_M_SIZE in *;
      repeat split; first [exact I | lia].
  - exact Q'.
Qed.

(** ** strip(sp + ox, sp + oy): the two scratch cells hold sv and ev, the bytes [sv, ev) are l (apart from the stack
    region). After it they hold sv + strip_lead and ev - strip_trail. *)
Lemma mfu_strip : strip_contract -> forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fcc fc : bv 32) (mcut m : word -> option byte) (lo : Z)
    (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc0 : mconf) (cur : option nat)
    (k0 : nat) (rest : list Z) (mc : mconf) (pend : bool) (ox oy sv ev : Z) (l : list byte),
  m_file_loop mcut fcc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc0 cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m (bv_unsigned sp0) lo c k0 mc pend ->
  0x30 <= ox -> ox + 8 <= 0xa8 -> 0x30 <= oy -> oy + 8 <= 0xa8 -> ox mod 8 = 0 -> oy mod 8 = 0 -> ox <> oy ->
  cell8 m (bv_unsigned sp + ox) sv -> cell8 m (bv_unsigned sp + oy) ev ->
  bv_unsigned a0 = bv_unsigned sp + ox -> bv_unsigned a1 = bv_unsigned sp + oy ->
  bytes_at rsegs m sv l -> Z.of_nat (length l) = ev - sv -> 0 < sv <= ev -> ev < 2 ^ 64 ->
  apart sv (ev - sv) lo (bv_unsigned sp0) ->
  (forall (m' : word -> option byte) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mfu_mid mcut m' (bv_unsigned sp0) lo c k0 mc pend ->
     munch [(bv_unsigned sp + ox, bv_unsigned sp + ox + 8); (bv_unsigned sp + oy, bv_unsigned sp + oy + 8)] m m' ->
     wmono rsegs m m' ->
     cell8 m' (bv_unsigned sp + ox) (sv + Z.of_nat (strip_lead (zs l))) ->
     cell8 m' (bv_unsigned sp + oy) (ev - Z.of_nat (strip_trail (zs l))) ->
     evt rsegs P
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3' t4' t5' t6')
           F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs P
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRIP) fc None m (seg_rom rsegs)).
Proof.
  intros SC P ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fcc fc mcut m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc0 cur k0 rest mc pend ox oy sv ev l
    L M OX1 OX2 OY1 OY2 OX8 OY8 NXY CX CY A0 A1 B LL SV EV AP K.
  pose proof M as M0. destruct M0 as (MU & WM & MI & ST & AT).
  destruct (mfu_loop_basic _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _ L)
    as (Lsp & C0 & C16 & NI & APc & SO0 & IL & SPH).
  destruct SO0 as (STK0 & DEP & S16 & NR).
  pose proof (mfu_sp16 _ _ Lsp S16) as SP16.
  unfold M_FILE_FRAME in Lsp.
  assert (FS : M_FILE_STACK = 6224) by (unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia).
  assert (SP8 : bv_unsigned sp = 8 * (2 * (bv_unsigned sp0 / 16) - 34)).
  { pose proof (Z.div_mod (bv_unsigned sp0) 16 ltac:(lia)) as D. rewrite S16 in D. lia. }
  assert (OX : ox = 8 * (ox / 8)) by (pose proof (Z.div_mod ox 8 ltac:(lia)) as D; rewrite OX8 in D; lia).
  assert (OY : oy = 8 * (oy / 8)) by (pose proof (Z.div_mod oy 8 ltac:(lia)) as D; rewrite OY8 in D; lia).
  clear OX8 OY8 S16.
  assert (PRE : strip_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) sv ev l).
  { rewrite A0, A1. unfold strip_pre.
    split; [apply (mfu_mod8 _ (2 * (bv_unsigned sp0 / 16) - 34 + ox / 8)); lia|].
    split; [apply (mfu_mod8 _ (2 * (bv_unsigned sp0 / 16) - 34 + oy / 8)); lia|].
    split; [unfold apart; lia|].
    split; [apply (mfu_cell_rw m lo (bv_unsigned sp0)); [exact ST | lia | lia | exact CX]|].
    split; [unfold apart; lia|].
    split; [apply (mfu_cell_rw m lo (bv_unsigned sp0)); [exact ST | lia | lia | exact CY]|].
    split; [unfold apart; lia|].
    split; [exact SV|]. split; [exact EV|]. split; [exact B|]. split; [exact LL|].
    split; [unfold apart in *; lia|]. split; [unfold apart in *; lia|].
    split; [|exact MI].
    split; [exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp0) ST ltac:(lia)))|].
    split; [unfold STRIP_STACK; lia|]. split; [exact SP16|]. intros a Ha. apply NR. lia. }
  pose proof (SC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo sv ev l PRE) as E.
  eapply evt_cut; [exact E|]. intros ms' Q. unfold ret_void in Q.
  destruct Q as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                 Ems & MU' & WM' & MI' & ST' & Q').
  subst ms'. cbv beta in Q'. rewrite A0, A1 in MU', Q'. destruct Q' as [QX QY].
  apply K; [|exact MU' | exact WM' | exact QX | exact QY].
  split; [|split; [exact (wmono_trans rsegs mcut m m' WM WM')|split; [exact MI'|split]]].
  - apply (mfu_munch_comp _ _ _ mcut m m' MU MU'); [intros x Hx; exact Hx|].
    apply mfu_sub_fp_stack.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  - (* the stack region: below sp from the post, the two cells from their new bytes, the rest unchanged *)
    apply (stk_transport rsegs _ m m' lo (bv_unsigned sp0) ST MU' WM').
    intros x Hx.
    destruct (Z_lt_le_dec x (bv_unsigned sp)) as [Hl|Hl].
    + right. apply mfu_some_of_mrd; [apply NR; lia|]. exact (proj2 (proj2 (proj2 ST') x ltac:(lia))).
    + assert (DX : (bv_unsigned sp + ox <= x < bv_unsigned sp + ox + 8) \/
                   ~ (bv_unsigned sp + ox <= x < bv_unsigned sp + ox + 8)) by lia.
      assert (DY : (bv_unsigned sp + oy <= x < bv_unsigned sp + oy + 8) \/
                   ~ (bv_unsigned sp + oy <= x < bv_unsigned sp + oy + 8)) by lia.
      destruct DX as [DX|DX].
      * right. apply mfu_some_of_mrd; [apply NR; lia|].
        apply (mfu_bytes_some m' _ _ x QX). rewrite length_le8. lia.
      * destruct DY as [DY|DY].
        -- right. apply mfu_some_of_mrd; [apply NR; lia|].
           apply (mfu_bytes_some m' _ _ x QY). rewrite length_le8. lia.
        -- left. cbn [outside]. repeat split; first [exact I | lia].
  - eapply mfu_atp_transport; [exact AT | exact MU' |]. cbn [disjoint_from].
    unfold apart in APc. unfold SEG_M_SIZE in *. repeat split; first [exact I | lia].
Qed.

(** ** ieq(s, n, w): s the n bytes l (apart from the stack region), w a C string of .rodata. *)
Lemma mfu_ieq : ieq_contract -> forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fcc fc : bv 32) (mcut m : word -> option byte) (lo : Z)
    (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc0 : mconf) (cur : option nat)
    (k0 : nat) (rest : list Z) (mc : mconf) (pend : bool) (l : list byte) (w : list Z),
  m_file_loop mcut fcc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc0 cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m (bv_unsigned sp0) lo c k0 mc pend ->
  bv_unsigned a0 <> 0 -> bytes_at rsegs m (bv_unsigned a0) l -> bv_unsigned a1 = Z.of_nat (length l) ->
  apart (bv_unsigned a0) (Z.of_nat (length l)) lo (bv_unsigned sp0) ->
  bv_unsigned a2 <> 0 -> cstr_at rsegs m (bv_unsigned a2) w ->
  RO_LO <= bv_unsigned a2 -> bv_unsigned a2 + Z.of_nat (length w) + 1 <= sa_ro_end SA ->
  (forall (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mfu_mid mcut m' (bv_unsigned sp0) lo c k0 mc pend ->
     munch [(bv_unsigned sp - IEQ_STACK, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
     evt rsegs P
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b2z (ieq (zs l) w))) a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs P
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 IEQ) fc None m (seg_rom rsegs)).
Proof.
  intros IC P ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fcc fc mcut m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc0 cur k0 rest mc pend l w
    L M A0N B A1 AP A2N CW RO1 RO2 K.
  pose proof M as M0. destruct M0 as (MU & WM & MI & ST & AT).
  destruct (mfu_loop_basic _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _  _ _ _ _ _ L)
    as (Lsp & C0 & C16 & NI & APc & SO0 & IL & SPH).
  destruct SO0 as (STK0 & DEP & S16 & NR).
  pose proof (mfu_sp16 _ _ Lsp S16) as SP16.
  unfold M_FILE_FRAME in Lsp.
  assert (FS : M_FILE_STACK = 6224) by (unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia).
  assert (PRE : ieq_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) l w).
  { unfold ieq_pre.
    split; [exact A0N|]. split; [exact B|]. split; [lia|]. split; [unfold apart in *; lia|].
    split; [exact A2N|]. split; [exact CW|].
    split; [unfold apart; left; cbn [SA SEG_UBSAN sa_ro_end sa_img_end] in *; lia|].
    split; [|exact MI].
    split; [exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp0) ST ltac:(lia)))|].
    split; [unfold IEQ_STACK; lia|]. split; [exact SP16|]. intros a Ha. apply NR. lia. }
  pose proof (IC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo l w PRE) as E.
  eapply evt_cut; [exact E|]. intros ms' Q. unfold ret_post in Q.
  destruct Q as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                 Ems & MU' & WM' & MI' & ST' & _).
  subst ms'.
  apply K; [|exact MU' | exact WM'].
  apply (mfu_stack_keep mcut m m' fcc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc0 cur line k0 rest ra0
           e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 mc pend IEQ_STACK L M);
    [unfold IEQ_STACK, M_FILE_FRAME; lia | exact MU' | exact WM' | exact MI' |].
  exact (proj2 (stk_split rsegs m' lo (bv_unsigned sp - IEQ_STACK) (bv_unsigned sp) ST'
                  ltac:(unfold IEQ_STACK; lia))).
Qed.

(** ** The literals: the words m_file's ieq calls name (fuzz_segconf.c:168, 213, 228, 236, 238, 240, 249) and the five
    strings m_key.words points to ("auto" 0x1030e, "master" 0x10548, "slave" 0x1075c, "tap" 0x10470, "box"
    0x10303), as C strings of .rodata in any memory with mem_inv; and the eight bytes of each words[] slot. *)
(** A C string of .rodata, its NUL and the image's bytes up to the next 8-byte boundary (the slack), as one closed
    check: the slack is read from the image (seg_rom), the string's bytes are nonzero byte values. *)
Definition mfu_lit_slack (A : Z) (s : list Z) : list byte :=
  match image_bytes rsegs (A + Z.of_nat (length s) + 1) (Z.to_nat ((- (A + Z.of_nat (length s) + 1)) mod 8)) with
  | Some l => l
  | None => []
  end.

Definition mfu_lit_ok (A : Z) (s : list Z) : bool :=
  (0 <=? A) && (A + Z.of_nat (length s) + 1 + Z.of_nat (length (mfu_lit_slack A s)) <=? 2^64) &&
  forallb (fun z => (0 <? z) && (z <? 256)) s &&
  ((- (A + Z.of_nat (length s) + 1)) mod 8 <=? Z.of_nat (length (mfu_lit_slack A s))) &&
  ro_bytes_b rsegs A (zb s ++ ZERO :: mfu_lit_slack A s).

Lemma mfu_lit_zs : forall s, forallb (fun z => (0 <? z) && (z <? 256)) s = true -> zs (zb s) = s /\ ~ In 0 s.
Proof.
  induction s as [|z s IH]; intros H; [split; [reflexivity | intros []]|].
  cbn [forallb] in H. apply andb_prop in H as [Hz H]. apply andb_prop in Hz as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. destruct (IH H) as [E N]. split.
  - unfold zs, zb in *. cbn [map]. rewrite E. f_equal.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
  - intros [Hin|Hin]; [lia | exact (N Hin)].
Qed.

Lemma mfu_lit_cstr : forall m A s, mem_inv rsegs m -> mfu_lit_ok A s = true -> cstr_at rsegs m A s.
Proof.
  intros m A s MI H. unfold mfu_lit_ok in H.
  apply andb_prop in H as [H R]. apply andb_prop in H as [H K]. apply andb_prop in H as [H F].
  apply andb_prop in H as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in K.
  destruct (mfu_lit_zs s F) as [E N].
  exists (zb s), (mfu_lit_slack A s). split; [|split; [exact E | split; [exact N | exact K]]].
  apply ro_bytes_at; [exact MI | exact H0 | | apply ro_bytes_b_sound; exact R].
  rewrite length_app. cbn [length]. unfold zb. rewrite length_map. lia.
Qed.

Lemma mfu_lits : forall m, mem_inv rsegs m ->
  cstr_at rsegs m 0x10313 S_segment /\ cstr_at rsegs m 0x10298 S_role /\ cstr_at rsegs m 0x10811 S_model /\
  cstr_at rsegs m 0x1054f S_ignore /\ cstr_at rsegs m 0x102a3 S_knock /\ cstr_at rsegs m 0x1042f S_yes /\
  cstr_at rsegs m 0x10517 S_true /\ cstr_at rsegs m 0x10711 S_no /\ cstr_at rsegs m 0x1029d S_false /\
  cstr_at rsegs m 0x1030e S_auto /\ cstr_at rsegs m 0x10548 S_master /\ cstr_at rsegs m 0x1075c S_slave /\
  cstr_at rsegs m 0x10470 S_tap /\ cstr_at rsegs m 0x10303 S_box.
Proof.
  intros m MI.
  repeat match goal with |- _ /\ _ => split end;
    (apply mfu_lit_cstr; [exact MI | vm_compute; reflexivity]).
Qed.

(** The image's bytes from A on are bs (no read-only condition: .data.rel.ro). *)
Fixpoint mfu_lit_img_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom rsegs (wa A) with
      | Some b' => bv_eqb b b' && mfu_lit_img_b (A + 1) bs'
      | None => false
      end
  end.

Lemma mfu_lit_img_sound : forall bs A, mfu_lit_img_b A bs = true ->
  forall i, (i < length bs)%nat -> seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b bs IH]; intros A H i Hi; cbn [length] in Hi; [lia|].
  cbn [mfu_lit_img_b] in H. destruct (seg_rom rsegs (wa A)) as [b'|] eqn:E; [|discriminate H].
  apply andb_prop in H as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E.
  - replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact H2 | lia].
Qed.

Lemma mfu_lit_cell : forall m a v, words_img m -> M_KEY_WORDS <= a -> a + 8 <= M_KEY_WORDS + 40 ->
  mfu_lit_img_b a (le8 (Z_to_bv 64 v)) = true -> cell8 m a v.
Proof.
  intros m a v W H0 H1 B. unfold cell8, bytes_at. rewrite length_le8.
  split; [unfold M_KEY_WORDS in H0; lia|]. split; [unfold M_KEY_WORDS in H1; lia|].
  intros i Hi. rewrite (W (a + Z.of_nat i)) by lia.
  apply mfu_lit_img_sound; [exact B | rewrite length_le8; exact Hi].
Qed.

Lemma mfu_words : forall m, words_img m ->
  cell8 m M_KEY_WORDS 0x1030e /\ cell8 m (M_KEY_WORDS + 8) 0x10548 /\ cell8 m (M_KEY_WORDS + 16) 0x1075c /\
  cell8 m (M_KEY_WORDS + 24) 0x10470 /\ cell8 m (M_KEY_WORDS + 32) 0x10303.
Proof.
  intros m W.
  repeat match goal with |- _ /\ _ => split end;
    (apply mfu_lit_cell; [exact W | lia | lia | vm_compute; reflexivity]).
Qed.

(** Read-only image bytes, with the address bounds, as one closed check. *)
Lemma mfu_lit_ro : forall m A bs, mem_inv rsegs m ->
  (0 <=? A) && (A + Z.of_nat (length bs) <=? 2^64) && ro_bytes_b rsegs A bs = true -> bytes_at rsegs m A bs.
Proof.
  intros m A bs MI H. apply andb_prop in H as [H R]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.leb_le in H1.
  apply ro_bytes_at; [exact MI | exact H0 | exact H1 | apply ro_bytes_b_sound; exact R].
Qed.

(** The role table m_key.role (.rodata 0x10a10): role i is i. *)
Lemma mfu_roles : forall m, mem_inv rsegs m -> forall i, (i < 5)%nat ->
  bytes_at rsegs m (M_KEY_ROLE + 4 * Z.of_nat i) (le4 (Z_to_bv 64 (Z.of_nat i))).
Proof.
  intros m MI i Hi.
  do 5 (destruct i as [|i]; [apply mfu_lit_ro; [exact MI | vm_compute; reflexivity]|]).
  lia.
Qed.

(** ** snprintf(g + off, 96, "%s", c->reading), g = &c->seg[i], off = role_file (0x3c) or ignore_file (0x9c); [upd]
    the field update of seg[i] the step is (role: ms_with_role r, ignore: ms_with_ignore b). *)
Definition mfu_file_ok (off : Z) (upd : list Z -> mseg -> mseg) : Prop :=
  (off = MS_ROLE_FILE /\ exists r, forall f, upd f = ms_with_role r f) \/
  (off = MS_IGNORE_FILE /\ exists b, forall f, upd f = ms_with_ignore b f).

(** Helpers of mfu_snprintf_file (prefix mfu_snp_). *)
Lemma mfu_snp_byte_lit : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma mfu_snp_pfb : forall s, pf_bytes (s ++ [0]) = zb s ++ [ZERO].
Proof. intros s. unfold pf_bytes, zb, ZERO. rewrite map_app. reflexivity. Qed.

Lemma mfu_snp_len_pfb : forall l, length (pf_bytes l) = length l.
Proof. intros l. unfold pf_bytes. apply length_map. Qed.

Lemma mfu_snp_len_zb : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. apply length_map. Qed.

Lemma mfu_snp_mod8 : forall c, c mod 16 = 0 -> c mod 8 = 0.
Proof.
  intros c H. pose proof (Z.div_mod c 16 ltac:(lia)) as E1. pose proof (Z.div_mod c 8 ltac:(lia)) as E2.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as B. lia.
Qed.

(** A string ending by c + 9236 (c 8-aligned), with its slack up to the next 8-byte boundary, ends by c + 9240. *)
Lemma mfu_snp_round : forall c x, c mod 8 = 0 -> x <= c + 9236 -> x + (- x) mod 8 <= c + 9240.
Proof.
  intros c x Hc Hx.
  pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E1.
  pose proof (Z.div_mod c 8 ltac:(lia)) as E2.
  lia.
Qed.

(** The C string at a as printf reads a %s argument: its bytes, its NUL, and exactly the slack to the next 8-byte
    boundary. *)
Lemma mfu_snp_arg_bytes : forall m a l, cstr_at rsegs m a l ->
  exists slack : list byte,
    bytes_at rsegs m a (pf_bytes (l ++ [0]) ++ slack) /\
    Z.of_nat (length slack) = (- (a + Z.of_nat (length l) + 1)) mod 8.
Proof.
  intros m a l (bs & sl & B & Hz & Hn & Hsl).
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length l) + 1)) 8 ltac:(lia)) as MB.
  set (k := Z.to_nat ((- (a + Z.of_nat (length l) + 1)) mod 8)).
  assert (Hk : Z.of_nat k = (- (a + Z.of_nat (length l) + 1)) mod 8) by (unfold k; lia).
  assert (Lk : length (firstn k sl) = k) by (rewrite length_firstn; lia).
  assert (EB : pf_bytes (l ++ [0]) = bs ++ [ZERO]).
  { rewrite mfu_snp_pfb. f_equal. rewrite <- Hz. unfold zb, zs. rewrite map_map.
    transitivity (map (fun x : byte => x) bs); [apply map_ext; intros b; apply mfu_snp_byte_lit | apply map_id]. }
  exists (firstn k sl). split; [|rewrite Lk; exact Hk].
  rewrite EB, <- app_assoc. cbn [app].
  rewrite <- (firstn_skipn k sl) in B.
  replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with ((bs ++ ZERO :: firstn k sl) ++ skipn k sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _]. exact B.
Qed.

Lemma mfu_snp_pos : forall l, ~ In 0 l -> Forall (fun x => 0 <= x < 256) l -> Forall (fun x => 0 < x < 256) l.
Proof.
  intros l N R. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) R x Hx) as Hr.
  cbv beta in Hr. destruct (Z.eq_dec x 0) as [->|Hne]; [contradiction | lia].
Qed.

(** "%s" at 0x104e0 in .rodata. *)
Lemma mfu_snp_fmt_ro : ro_bytes_b rsegs 0x104e0 (pf_bytes ([37; 115] ++ [0])) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mfu_snp_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x104e0 (pf_bytes ([37; 115] ++ [0])).
Proof.
  intros m MI. apply (ro_bytes_at rsegs); [exact MI | lia | rewrite mfu_snp_len_pfb; cbn [length app]; lia |].
  apply (ro_bytes_b_sound rsegs). exact mfu_snp_fmt_ro.
Qed.

Lemma mfu_snp_img_free : forall c D n, blk_noimg rsegs c SEG_M_SIZE -> c <= D -> D + n <= c + SEG_M_SIZE ->
  pf_img_free D n.
Proof.
  intros c D n H H1 H2 j Hj sg Hs. replace (D + j) with (c + (D - c + j)) by lia. apply H; [lia | exact Hs].
Qed.

(** The line's footprint does not depend on which field update of seg[i] the state carries. *)
Lemma mfu_snp_W : forall sp0 c k0 mcx i h1 h2,
  mfu_W sp0 c k0 (m_upd mcx i h1) false = mfu_W sp0 c k0 (m_upd mcx i h2) false.
Proof.
  intros. unfold mfu_W, M_FILE_W, m_upd, m_set_segs. cbn [mc_seg mc_kept]. rewrite !upd_nth_length. reflexivity.
Qed.

(** The call's footprint inside the line's: printf's stack below sp, and [D, E) inside entry i. *)
Lemma mfu_snp_sub : forall sp0 S c k0 mc i off E,
  S + M_FILE_FRAME = sp0 -> (i < length (mc_seg mc))%nat -> 0 <= off -> off + 96 <= MSEG_SIZE ->
  E <= mseg_addr c i + off + 96 ->
  sub_fp [(S - PRINTF_K, S); (mseg_addr c i + off, E)] (mfu_W sp0 c k0 mc false).
Proof.
  intros sp0 S c k0 mc i off E Hs Hi H0 H1 HE x Hx.
  unfold mfu_W, M_FILE_W in Hx. cbn [app outside] in Hx. destruct Hx as (X1 & X2 & _).
  unfold mseg_addr, M_FILE_STACK, M_FILE_FRAME, MSEG_SIZE, PRINTF_K in *.
  cbn [outside]. split; [lia | split; [lia | exact I]].
Qed.

(** Inside the block the call wrote only [D, E). *)
Lemma mfu_snp_blk : forall c lo sp0 S D E x,
  apart c (SEG_M_SIZE + 4) lo sp0 -> lo <= S - PRINTF_K -> S <= sp0 ->
  c <= x < c + SEG_M_SIZE -> ~ outside [(S - PRINTF_K, S); (D, E)] x -> D <= x < E.
Proof.
  intros c lo sp0 S D E x AP H1 H2 Hx Hn.
  destruct (Z_le_gt_dec D x) as [E1|E1]; [destruct (Z_lt_ge_dec x E) as [E2|E2]; [lia|]|];
    exfalso; apply Hn; cbn [outside]; unfold apart in AP; (split; [lia | split; [lia | exact I]]).
Qed.

(** A byte of the stack region is outside the call's footprint or in printf's stack. *)
Lemma mfu_snp_stk : forall c lo sp0 S D E x,
  apart c (SEG_M_SIZE + 4) lo sp0 -> c <= D -> E <= c + SEG_M_SIZE ->
  lo <= x < sp0 -> outside [(S - PRINTF_K, S); (D, E)] x \/ S - PRINTF_K <= x < S.
Proof.
  intros c lo sp0 S D E x AP H1 H2 Hx.
  destruct (Z_le_gt_dec (S - PRINTF_K) x) as [E1|E1]; [destruct (Z_lt_ge_dec x S) as [E2|E2]; [right; lia|]|];
    left; cbn [outside]; unfold apart in AP; (split; [lia | split; [lia | exact I]]).
Qed.

Lemma mfu_snp_weak : forall S D E (m m' : word -> option byte),
  munch [(S - PRINTF_K, S); (D, E)] m m' -> E <= D + 96 -> munch [(S - PRINTF_K, S); (D, D + 96)] m m'.
Proof.
  intros S D E m m' MU HE. apply (munch_weaken [(S - PRINTF_K, S); (D, E)]); [|exact MU].
  intros x Hx. cbn [outside] in *. destruct Hx as (X1 & X2 & _). split; [exact X1 | split; [lia | exact I]].
Qed.

Lemma mfu_snp_upd2 {A} : forall (h1 h2 h : A -> A) i l, (forall x, h2 (h1 x) = h x) ->
  upd_nth i h2 (upd_nth i h1 l) = upd_nth i h l.
Proof.
  intros h1 h2 h i l H. revert i. induction l as [|x l IH]; intros [|i]; cbn;
    [reflexivity | reflexivity | rewrite H; reflexivity | rewrite IH; reflexivity].
Qed.

(** The block's new bytes: the file field of seg[i] holds s and its NUL, the other fields as the update says. *)
Lemma mfu_snp_enc : forall mcx i off upd f0 s bs,
  mfu_file_ok off upd -> (i < length (mc_seg mcx))%nat ->
  (length s < 96)%nat -> ~ In 0 s -> Forall (fun x => 0 <= x < 256) s ->
  mconf_encp false (m_upd mcx i (upd f0)) bs ->
  mconf_encp false (m_upd mcx i (upd s)) (upd_bytes bs (256 * i + Z.to_nat off) (zb s ++ [ZERO])).
Proof.
  intros mcx i off upd f0 s bs FOK Hi L N R E.
  assert (Hl : length (mc_seg (m_upd mcx i (upd f0))) = length (mc_seg mcx))
    by (unfold m_upd, m_set_segs; cbn [mc_seg]; apply upd_nth_length).
  destruct FOK as [[-> (r & Hu)] | [-> (b & Hu)]].
  - assert (EM : m_upd (m_upd mcx i (upd f0)) i (ms_set_role_file s) = m_upd mcx i (upd s)).
    { unfold m_upd, m_set_segs. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading]. f_equal.
      apply mfu_snp_upd2. intros g. rewrite !Hu. reflexivity. }
    rewrite <- EM. apply mconf_enc_seg; [exact E | rewrite Hl; exact Hi | |].
    + rewrite length_app, mfu_snp_len_zb. cbn [length]. change (Z.to_nat MS_ROLE_FILE) with 60%nat. lia.
    + intros fb Hfb. apply mseg_enc_role_file; assumption.
  - assert (EM : m_upd (m_upd mcx i (upd f0)) i (ms_set_ignore_file s) = m_upd mcx i (upd s)).
    { unfold m_upd, m_set_segs. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading]. f_equal.
      apply mfu_snp_upd2. intros g. rewrite !Hu. reflexivity. }
    rewrite <- EM. apply mconf_enc_seg; [exact E | rewrite Hl; exact Hi | |].
    + rewrite length_app, mfu_snp_len_zb. cbn [length]. change (Z.to_nat MS_IGNORE_FILE) with 156%nat. lia.
    + intros fb Hfb. apply mseg_enc_ignore_file; assumption.
Qed.

Lemma mfu_snprintf_file : snprintf_contract -> forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fcc fc : bv 32) (mcut m : word -> option byte) (lo : Z)
    (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc0 : mconf) (cur : option nat)
    (k0 : nat) (rest : list Z) (mcx : mconf) (i : nat) (off : Z) (upd : list Z -> mseg -> mseg) (f0 : list Z),
  m_file_loop mcut fcc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc0 cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m (bv_unsigned sp0) lo c k0 (m_upd mcx i (upd f0)) false ->
  mfu_file_ok off upd -> (i < length (mc_seg mcx))%nat -> frm0 fc ->
  bv_unsigned a0 = mseg_addr c i + off -> bv_unsigned a1 = 96 -> bv_unsigned a2 = 0x104e0 ->
  bv_unsigned a3 = c + MC_READING ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mfu_mid mcut m' (bv_unsigned sp0) lo c k0
       (m_upd mcx i (upd (snprintf_s 96 F_s [AS (mc_reading mcx)]))) false ->
     munch [(bv_unsigned sp - PRINTF_K, bv_unsigned sp); (mseg_addr c i + off, mseg_addr c i + off + 96)] m m' ->
     wmono rsegs m m' ->
     frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
     evt rsegs P
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom rsegs))) ->
  evt rsegs P
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros HSN P ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fcc fc mcut m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc0 cur k0 rest mcx i off upd f0
    LOOP MID FOK Hi FRM Ha0 Ha1 Ha2 Ha3 K.
  destruct (mfu_env mcut m fcc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc0 cur line k0 rest ra0
              e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 (m_upd mcx i (upd f0)) false LOOP MID)
    as (TM & SSP & _ & _ & WRm & BSm & _).
  destruct LOOP as (Hsp & _ & _ & _ & _ & _ & _ & _ & Hc0 & Hc16 & NI & _ & _ & _ & AP & _ & _ & _ & _ & _ & _
                    & _ & _ & _ & _ & _ & PENV & _ & _ & STK0 & _).
  destruct PENV as (_ & _ & _ & HIMG & HSP63).
  destruct STK0 as (_ & HDEP & _ & _).
  destruct MID as (MU & WM & MI & STK & MCA).
  destruct SSP as (G1 & canary & G2).
  unfold M_FILE_FRAME in Hsp. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HDEP.
  change (sa_img_end SA) with 0x54088 in HIMG.
  destruct (mconf_atp_bytes rsegs false m c (m_upd mcx i (upd f0)) MCA) as (bs & BC & ENC & LBS).
  destruct (mconf_enc_bounds false (m_upd mcx i (upd f0)) bs ENC)
    as (_ & LSEG & _ & _ & _ & _ & LRD & NZ & FR & _).
  change (mc_reading (m_upd mcx i (upd f0))) with (mc_reading mcx) in LRD, NZ, FR.
  assert (Lm : length (mc_seg (m_upd mcx i (upd f0))) = length (mc_seg mcx))
    by (unfold m_upd, m_set_segs; cbn [mc_seg]; apply upd_nth_length).
  rewrite Lm in LSEG.
  pose proof BC as (HcN & _ & _).
  assert (Hc8 : c mod 8 = 0) by (apply mfu_snp_mod8; exact Hc16).
  assert (Hoff : 0x3c <= off <= 0x9c)
    by (destruct FOK as [[-> _]|[-> _]]; unfold MS_ROLE_FILE, MS_IGNORE_FILE; lia).
  assert (Hlo' : lo <= bv_unsigned sp - PRINTF_K) by (unfold PRINTF_K; lia).
  assert (Hss : bv_unsigned sp <= bv_unsigned sp0) by lia.
  (* the reading, as printf's %s argument *)
  pose proof (mconf_reading_cstr rsegs false m c (m_upd mcx i (upd f0)) MCA BSm Hc8) as CSR.
  change (mc_reading (m_upd mcx i (upd f0))) with (mc_reading mcx) in CSR.
  destruct (mfu_snp_arg_bytes m (c + MC_READING) (mc_reading mcx) CSR) as (slack & SB & SL).
  pose proof (mfu_snp_round c (c + MC_READING + Z.of_nat (length (mc_reading mcx)) + 1) Hc8
                ltac:(unfold MC_READING; lia)) as RND.
  rewrite <- SL in RND.
  (* the destination field, as writable cells *)
  destruct (mconf_field_cells rsegs false m c (m_upd mcx i (upd f0)) (MSEG_SIZE * Z.of_nat i + off) MCA WRm
              ltac:(unfold MSEG_SIZE; lia) ltac:(unfold MSEG_SIZE, SEG_M_SIZE; lia)) as (junk & CELLS).
  replace (c + (MSEG_SIZE * Z.of_nat i + off)) with (mseg_addr c i + off) in CELLS
    by (unfold mseg_addr, MSEG_SIZE; lia).
  (* the call *)
  pose proof (HSN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (bv_unsigned sp - PRINTF_K) canary [37; 115] [Ps] [APtr (mc_reading mcx)] (mc_reading mcx)
                junk) as HC.
  cbv zeta in HC. rewrite Ha0, Ha1, Ha2 in HC.
  assert (ETw : firstn (Z.to_nat (96 - 1)) (mc_reading mcx) = mc_reading mcx) by (apply firstn_all2; lia).
  rewrite ETw in HC.
  assert (ESN : snprintf_s 96 F_s [AS (mc_reading mcx)] = mc_reading mcx)
    by (apply snprintf_s1; [exact NZ | lia]).
  rewrite ESN in K.
  eapply evt_cut.
  { apply HC.
    - exact (mfu_snp_fmt_at m MI).
    - apply Z.leb_le. vm_compute. reflexivity.
    - apply Z.leb_le. vm_compute. reflexivity.
    - reflexivity.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. rewrite Ha3.
      split; [exact (mfu_snp_pos _ NZ FR)|].
      exists slack. split; [exact SB|].
      split; [rewrite SL; lia|].
      split; [unfold MC_READING; lia|].
      split.
      + pose proof AP as AP'. unfold apart, SEG_M_SIZE in AP'. unfold MC_READING, PRINTF_K in *.
        destruct AP' as [AP'|AP']; [left|right]; lia.
      + right. unfold mseg_addr, MSEG_SIZE, MC_READING. lia.
    - cbn [pf_text option_map]. rewrite app_nil_r. reflexivity.
    - change (Z.to_nat 96) with 96%nat. exact CELLS.
    - lia.
    - lia.
    - unfold mseg_addr, MSEG_SIZE. lia.
    - pose proof AP as AP'. unfold apart, SEG_M_SIZE in AP'. unfold mseg_addr, MSEG_SIZE, PRINTF_K in *.
      destruct AP' as [AP'|AP']; [left|right]; lia.
    - apply (mfu_snp_img_free c); [exact NI | unfold mseg_addr, MSEG_SIZE; lia
                                  | unfold mseg_addr, MSEG_SIZE, SEG_M_SIZE; lia].
    - destruct (stk_split rsegs m lo (bv_unsigned sp - PRINTF_K) (bv_unsigned sp0) STK
                  ltac:(unfold PRINTF_K in *; lia)) as [_ STK1].
      destruct (stk_split rsegs m _ (bv_unsigned sp) _ STK1 ltac:(unfold PRINTF_K in *; lia)) as [STK2 _].
      exact STK2.
    - unfold PRINTF_K, SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact G1.
    - exact G2. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m'
                  & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK2 & STK2 & BY2).
  apply (K m' Ft fc' t0' t1' t2' (Z_to_bv 64 (Z.of_nat (length (mc_reading mcx)))) a1' a2' a3' a4' a5' a6' a7'
           t3' t4' t5' t6').
  - unfold mfu_mid. split; [|split; [|split; [|split]]].
    + apply (mfu_munch_comp _ (mfu_W (bv_unsigned sp0) c k0 (m_upd mcx i (upd f0)) false) _ mcut m m' MU MU2).
      * rewrite (mfu_snp_W (bv_unsigned sp0) c k0 mcx i (upd (mc_reading mcx)) (upd f0)). intros x Hx. exact Hx.
      * apply mfu_snp_sub; [exact Hsp | | lia | unfold MSEG_SIZE; lia | lia].
        unfold m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length. exact Hi.
    + eapply wmono_trans; [exact WM | exact WM2].
    + exact MI2.
    + apply (mfu_stk_patch m m' _ lo (bv_unsigned sp0) (bv_unsigned sp - PRINTF_K) (bv_unsigned sp)
               STK MU2 WM2 STK2).
      intros x Hx. apply (mfu_snp_stk c lo (bv_unsigned sp0)); [exact AP | unfold mseg_addr, MSEG_SIZE; lia
        | unfold mseg_addr, MSEG_SIZE, SEG_M_SIZE; lia | exact Hx].
    + apply (mconf_atp_upd rsegs false false m m' c (m_upd mcx i (upd f0)) (m_upd mcx i (upd (mc_reading mcx)))
               (mseg_addr c i + off) (pf_bytes (mc_reading mcx ++ [0])) _ MCA MU2).
      * intros x Hx Hn.
        pose proof (mfu_snp_blk c lo (bv_unsigned sp0) (bv_unsigned sp) _ _ x AP Hlo' Hss Hx Hn) as Hb.
        rewrite mfu_snp_len_pfb, length_app. cbn [length]. lia.
      * exact BY2.
      * unfold mseg_addr, MSEG_SIZE. lia.
      * rewrite mfu_snp_len_pfb, length_app. cbn [length]. unfold mseg_addr, MSEG_SIZE, SEG_M_SIZE. lia.
      * intros bs' E'. replace (Z.to_nat (mseg_addr c i + off - c)) with (256 * i + Z.to_nat off)%nat
          by (unfold mseg_addr, MSEG_SIZE; lia).
        rewrite mfu_snp_pfb. exact (mfu_snp_enc mcx i off upd f0 (mc_reading mcx) bs' FOK Hi LRD NZ FR E').
  - apply (mfu_snp_weak _ _ _ m m' MU2). lia.
  - exact WM2.
  - exact FRM2.
  - exact FK2.
Qed.

(** ** A callee that writes only its own frame below sp (d bytes: strchr 32, ieq 32, m_find 64,
    fuzz_catalogue_row 48; 0 for strlen, memchr, bcmp) keeps mfu_mid. *)
Lemma mfu_stack_call : forall mcut m m' fcc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    mc pend d,
  m_file_loop mcut fcc sp0 sp lo c p mc0 cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid mcut m sp0 lo c k0 mc pend -> 0 <= d <= M_FILE_STACK - M_FILE_FRAME ->
  munch [(sp - d, sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (sp - d) sp ->
  mfu_mid mcut m' sp0 lo c k0 mc pend.
Proof. exact mfu_stack_keep. Qed.
