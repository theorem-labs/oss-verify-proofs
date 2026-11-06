From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm AllocSlots SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel fmemopen_c fclose_c libreac_fuzz_fopen_c
  pcap_source_struct pcap_source_struct_next pcap_source_open_c pcap_source_close_c pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PGlue PSROcf PContractCF.
Import ListNotations.
Open Scope Z_scope.

(* Frame-record steps for the three reader calls of the fuzz_pcap ubsan slot: pcap_source_open, pcap_source_close
   and pcap_source_next, each through its contract, in the form of ss_malloc_step / ss_free_step. *)

Lemma ps_unch : forall (P : Z -> Prop) W (m m' : word -> option byte), munch W m m' ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) ->
  forall x, 0 <= x < 2 ^ 64 -> ~ P x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof.
  intros P W m m' Hm HW x Hx Hn. apply Hm. rewrite unsigned_lit by exact Hx.
  clear Hm. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|]. split.
  - intros Hy. apply Hn. exact (HW lo hi x (or_introl eq_refl) Hy).
  - apply IH. intros lo' hi' y Hin Hy. exact (HW lo' hi' y (or_intror Hin) Hy).
Qed.

Lemma ps_wr : forall m a f sw o v i pad, rw_cells rsegs m a (ps_cells f sw o v i pad) -> wr_at rsegs m a 24.
Proof. intros m a f sw o v i pad [_ W]. exact W. Qed.

Lemma ps_wr_at : forall m a n x, wr_at rsegs m a n -> a <= x < a + n -> writable_at rsegs m x.
Proof.
  intros m a n x (_ & _ & W) Hx. unfold writable_at. replace x with (a + (x - a)) by lia.
  exact (W (x - a) ltac:(lia)).
Qed.

Lemma ps_ofl_nrelro : forall a, A_OFL_HEAD <= a < A_OFL_HEAD + 8 -> ~ in_globals frame_RELRO a.
Proof.
  intros a Ha (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn [In] in Hin. unfold A_OFL_HEAD in Ha.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

(* The mode field of the stderr FILE (offset 136) is not in RELRO. *)
Lemma ps_relro_nmode : forall a, in_globals frame_RELRO a -> ~ (A_STDERR + 136 <= a < A_STDERR + 140).
Proof.
  intros a (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn [In] in Hin. unfold A_STDERR.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

Lemma sb_free_malloc : forall b n, sb_free (sb_malloc b n) n = b.
Proof. intros [x y z] n. unfold sb_free, sb_malloc. cbn [sb_live sb_bytes sb_cap]. f_equal; lia. Qed.

(* The stderr FILE's bytes: the 136 bytes before the mode field depend on the flags only. *)
Definition SE_PRE (fl : Z) : list byte := cells_bytes (firstn 19 (stderr_cells fl 0)).
Definition SE_POST : list byte := cells_bytes (skipn 20 (stderr_cells 0 0)).

Lemma ps_stderr_split : forall fl md, cells_bytes (stderr_cells fl md) = SE_PRE fl ++ le4 (wz md) ++ SE_POST.
Proof. intros fl md. reflexivity. Qed.

Lemma ps_se_pre_len : forall fl, length (SE_PRE fl) = 136%nat.
Proof. intros fl. reflexivity. Qed.

Lemma ps_se_post_len : length SE_POST = 92%nat.
Proof. reflexivity. Qed.

Lemma ps_errf_same : forall m m' fl md md', errf m fl md -> errf m' fl md' ->
  forall a, A_STDERR <= a < A_STDERR + 232 -> ~ (A_STDERR + 136 <= a < A_STDERR + 140) ->
  mbyte rsegs m' a = mbyte rsegs m a.
Proof.
  intros m m' fl md md' (H1 & _) (H2 & _) a Ha Hn.
  pose proof (ss_cells_bytes m A_STDERR _ H1) as B1. pose proof (ss_cells_bytes m' A_STDERR _ H2) as B2.
  rewrite ps_stderr_split in B1, B2.
  pose proof (ps_se_pre_len fl) as L1. pose proof ps_se_post_len as L2.
  assert (Ea : a = A_STDERR + Z.of_nat (Z.to_nat (a - A_STDERR))) by lia.
  assert (Hi : forall v, (Z.to_nat (a - A_STDERR) < length (SE_PRE fl ++ le4 (wz v) ++ SE_POST))%nat).
  { intros v. rewrite !length_app, length_le4, L1, L2. lia. }
  rewrite Ea. rewrite (sg_bytes_nth rsegs m' _ _ B2 _ (Hi md')), (sg_bytes_nth rsegs m _ _ B1 _ (Hi md)).
  destruct (Nat.lt_ge_cases (Z.to_nat (a - A_STDERR)) 136) as [Hl|Hl].
  - rewrite !nth_error_app1 by lia. reflexivity.
  - rewrite !nth_error_app2 by (rewrite ?L1, ?length_le4; lia). rewrite !length_le4. reflexivity.
Qed.

(* The bytes of a list of global ranges, checked by computation. *)
Definition g_chk (G : list (Z * Z)) (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) G.
Definition g_rng (G : list (Z * Z)) (a n : Z) : bool :=
  forallb (fun i => g_chk G (a + Z.of_nat i)) (seq 0 (Z.to_nat n)).

Lemma g_rng_ok : forall G a n, g_rng G a n = true -> forall x, a <= x < a + n -> in_globals G x.
Proof.
  intros G a n H x Hx. unfold g_rng in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (x - a)) ltac:(apply in_seq; lia)).
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in H by lia.
  unfold g_chk in H. apply existsb_exists in H as ([lo len] & Hin & Hc). cbn [fst snd] in Hc.
  apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  exists lo, len. split; [exact Hin | lia].
Qed.

(* The image covers [IMG_LO, IMG_HI) without gaps: walk the reserved segments. *)
Fixpoint cov_walk (fuel : nat) (x hi : Z) : bool :=
  match fuel with
  | O => hi <=? x
  | S f =>
      if hi <=? x then true else
      match find (fun s => (bv_unsigned (fst s) <=? x) && (x <? bv_unsigned (fst s) + bv_unsigned (snd s)))
              (segments_reserved rsegs) with
      | Some s => cov_walk f (bv_unsigned (fst s) + bv_unsigned (snd s)) hi
      | None => false
      end
  end.

Lemma cov_walk_img : cov_walk 64 IMG_LO IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.

Section PS.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Local Abbreviation API := (APIf rc).
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR (APIf rc)).

Lemma ps_cov_walk : forall fuel x hi, cov_walk fuel x hi = true -> forall a, x <= a < hi -> in_img B a.
Proof.
  induction fuel as [|f IH]; intros x hi H a Ha; cbn [cov_walk] in H.
  - apply Z.leb_le in H. lia.
  - revert H. destruct (hi <=? x) eqn:E1; intros H; [apply Z.leb_le in E1; lia|].
    revert H. match goal with |- context [find ?f ?l] => destruct (find f l) as [s|] eqn:E2 end;
      intros H; [|discriminate].
    apply find_some in E2 as (Hin & Hs). apply andb_prop in Hs as (Hs1 & Hs2).
    apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
    destruct (Z_lt_le_dec a (bv_unsigned (fst s) + bv_unsigned (snd s))) as [Hlt|Hge].
    + apply (ss_img_rng B APIf ra empty FF a (a + 1)); [|lia].
      apply existsb_exists. exists s. split; [exact Hin|].
      apply andb_true_intro. split; apply Z.leb_le; lia.
    + exact (IH _ hi H a ltac:(lia)).
Qed.

Lemma ps_img_cov : forall a, IMG_LO <= a < IMG_HI -> in_img B a.
Proof. exact (ps_cov_walk 64 IMG_LO IMG_HI cov_walk_img). Qed.

(* A heap block of the allocator lies wholly below or wholly above the image. *)
Lemma ps_blk_apart : forall L A mem md a k, MR L A mem md -> In (a, k) (blocks L A) -> 0 < k -> img_apart a k.
Proof.
  intros L A mem md a k HM Hin Hk. unfold img_apart.
  destruct (Z_le_gt_dec (a + k) IMG_LO) as [Hl|Hl]; [left; unfold IMG_LO in Hl; lia|].
  destruct (Z_le_gt_dec IMG_HI a) as [Hh|Hh]; [right; unfold IMG_HI in Hh; lia|].
  exfalso.
  destruct (ss_blk_facts B APIf ra empty FF L A mem md a k (Z.max a IMG_LO - a) HM Hin ltac:(lia))
    as (_ & _ & _ & _ & H5).
  apply H5. replace (a + (Z.max a IMG_LO - a)) with (Z.max a IMG_LO) by lia. apply ps_img_cov.
  unfold IMG_LO, IMG_HI in *. lia.
Qed.

Lemma ps_spZ : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  spZ regs = fsp g /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47.
Proof.
  intros g km hb L A regs mem md HF. destruct HF as (HGV & Hsp & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. assert (HK0 : SLOT_K = 65536) by reflexivity.
  unfold spZ. rewrite Hsp. unfold fsp, SLOT_FRAME. rewrite unsigned_lit by lia. split; [reflexivity | lia].
Qed.

(* The bytes a reader call may write outside the heap: the source struct ps, the allocator's context and the
   head of the open-file list. *)
Definition ps_E (ps a : Z) : Prop :=
  (ps <= a < ps + 24) \/ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) \/ (A_OFL_HEAD <= a < A_OFL_HEAD + 8).

(* A reader call with call_post_k: the frame record at the return and the bytes it keeps. *)
Lemma ps_call_FR : forall g km hb L A regs mem md stk E L' A' regs' mem' md' km' hb' ps,
  FR B APIf ra empty g km hb L A regs mem md ->
  0 <= stk <= SLOT_K - SLOT_FRAME -> fsp g <= ps -> ps + 24 <= g_S g - 104 ->
  call_post_k B MR stk L A regs mem md E L' A' regs' mem' md' ->
  (forall a, E a -> (a < alloc_ceiling /\ ~ in_img B a) \/ ps_E ps a) ->
  (forall a, g_S g - SLOT_K <= a < g_S g -> E a \/ ~ E a) ->
  wr_at rsegs mem' ps 24 ->
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
  ro_agree segs mem' -> st_init_done A' = true -> RESB (g_b g) km' hb' A' ->
  FR B APIf ra empty g km' hb' L' A' regs' mem' md' /\ regs_preserved regs regs' /\
  (forall x, fsp g <= x < g_S g -> ~ (ps <= x < ps + 24) -> mbyte segs mem' x = mbyte segs mem x) /\
  (forall x, img_w x -> ~ (A_OFL_HEAD <= x < A_OFL_HEAD + 8) -> mbyte segs mem' x = mbyte segs mem x) /\
  (stdio_ok mem -> stdio_ok mem') /\ guard_ok mem'.
Proof.
  intros g km hb L A regs mem md stk E L' A' regs' mem' md' km' hb' ps HF Hstk Hp1 Hp2 HC HE HEd HW HB0' HRO' HIN'
    HRS'.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km hb L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. pose proof (ss_errc B APIf ra empty FF) as ERC.
  pose proof (ss_ctx B APIf ra empty FF) as CTX.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  unfold fsp, SLOT_FRAME in *.
  pose proof HC as (MR'' & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  assert (NE : forall a, ~ (a < alloc_ceiling /\ ~ in_img B a) -> ~ (ps <= a < ps + 24) ->
                 ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> ~ E a).
  { intros a H1 H2 H3 H4 Ha. destruct (HE a Ha) as [H|[H|[H|H]]]; tauto. }
  split.
  { apply (ss_FR_call B APIf ra empty FF g km hb L A regs mem md stk E L' A' regs' mem' md' km' hb' HF Hstk HC).
    - intros a Ha. destruct (HE a Ha) as [H|[H|[H|H]]].
      + left. exact H.
      + right. left. lia.
      + right. right. left. exact H.
      + right. right. right. split; [right; left; exact H | exact (ps_ofl_nrelro a H)].
    - exact HEd.
    - intros a Ha Hw. destruct (HE a Ha) as [H|[H|[H|H]]].
      + exfalso. lia.
      + rewrite SEG. exact (ps_wr_at mem' ps 24 a HW H).
      + exfalso. rewrite CTX in H. unfold CTX_SIZE in H. lia.
      + exfalso. unfold A_OFL_HEAD in H. lia.
    - exact HB0'.
    - exact HRO'.
    - exact HIN'.
    - exact HRS'. }
  split; [exact RP'|].
  split.
  { intros x Hx Hnp. apply FR'.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B MR (aa_laws API) L A mem md x HMR Ho). lia.
    - intros Ho. pose proof (mr_owned_low B MR (aa_laws API) L' A' mem' md' x MR'' Ho). lia.
    - unfold scratch_k. rewrite SPZ. lia.
    - apply NE; [intros [H _]; lia | exact Hnp | rewrite CTX; unfold CTX_SIZE; lia | unfold A_OFL_HEAD; lia]. }
  split.
  { intros x Hx Hno. destruct (ss_img_w_facts B APIf ra empty FF x Hx) as (Hi & Hs & Hc & He & Hl & _).
    unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    - right. exact Hi.
    - exact (ss_img_w_owned B APIf ra empty FF L A mem md x HMR Hx).
    - exact (ss_img_w_owned B APIf ra empty FF L' A' mem' md' x MR'' Hx).
    - unfold scratch_k. rewrite SPZ. lia.
    - apply NE; [intros [_ H]; exact (H Hi) | lia | exact Hc | exact Hno]. }
  split.
  { intros HSTD. refine (ss_stdio_keep B APIf ra empty FF L' A' mem mem' md' MR'' HSTD _).
    intros x Hx. destruct (ss_stdio_addr B APIf ra empty FF x Hx) as (Hi & Hs & Hc & He & Hl).
    unfold IMG_LO, IMG_HI in Hl.
    apply FR'.
    - right. exact Hi.
    - intros [Ho|Ho]; [exact (Hc (ax_img (ss_ax B APIf ra empty FF) L A mem md x HMR Hi Ho)) | exact (Hs Ho)].
    - intros [Ho|Ho]; [exact (Hc (ax_img (ss_ax B APIf ra empty FF) L' A' mem' md' x MR'' Hi Ho)) | exact (Hs Ho)].
    - unfold scratch_k. rewrite SPZ. lia.
    - apply NE; [intros [_ H]; exact (H Hi) | lia | exact Hc | unfold A_LIBC, A_OFL_LOCK, A_OFL_HEAD in *; lia]. }
  exact (ss_guard_of_MR B APIf ra empty FF L' A' mem' md' MR'').
Qed.

Hypothesis HCLOSE : pcap_source_close_contract B API.

(* pcap_source_close on an open stream h (a block of the slot's heap blocks): the block is freed. *)
Lemma ps_close_step : forall g km hb1 h hb2 L A regs mem md ps sw olen vtag vid pad b F p o P,
  FR B APIf ra empty g km (hb1 ++ (h, 1304) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (h, 1304) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = wz ps ->
  fsp g <= ps -> ps + 24 <= g_S g - 104 -> ps mod 8 = 0 ->
  rw_cells rsegs mem ps (ps_cells (wz h) sw olen vtag vid pad) ->
  In (b, Z.of_nat (length F)) (hb1 ++ (h, 1304) :: hb2) ->
  mstl mem h b F p (wz 0) (wz 0) -> ofl_one mem h -> stdio_ok mem ->
  (forall L' A' regs' mem' md',
     FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> ~ (ps <= x < ps + 24) -> mbyte segs mem' x = mbyte segs mem x) ->
     (forall a k i, In (a, k) (hb1 ++ hb2) -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
     (forall x, img_w x -> ~ (A_OFL_HEAD <= x < A_OFL_HEAD + 8) -> mbyte segs mem' x = mbyte segs mem x) ->
     rw_cells rsegs mem' ps (ps_cells (wz 0) sw olen vtag vid pad) ->
     ofl_empty mem' -> stdio_ok mem' -> guard_ok mem' -> bytes_at rsegs mem' b F ->
     SRO segs (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md') o P) ->
  SRO segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_CLOSE) mem (seg_rom segs)) md) o P.
Proof.
  intros g km hb1 h hb2 L A regs mem md ps sw olen vtag vid pad b F p o P HF HP HRA H10 Hp1 Hp2 Hp8 HPS HinB HMS
    HOO HSTD HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km _ L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & HIN & _ & _ & _ & _ & _ & HRS & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  unfold fsp, SLOT_FRAME in *.
  assert (Hh : In (h, 1304) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  assert (Hb : In (b, Z.of_nat (length F)) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact HinB. }
  destruct (ss_blk_facts B APIf ra empty FF L A mem md h 1304 0 HMR Hh ltac:(lia)) as (_ & Hh1 & Hh2 & _ & _).
  assert (HNh : forall k, In (h, k) (hb1 ++ hb2 ++ blocks (g_L g) (g_A g)) -> False).
  { intros k Hin.
    destruct (ss_alloc B APIf ra empty FF) as (_ & _ & _ & _ & _ & _ & _ & _ & ND & _).
    pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (ND L A mem md HMR)) as Hnd.
    pose proof (Permutation_map fst HP) as HPf. apply (Permutation_NoDup HPf) in Hnd.
    rewrite !map_app in Hnd. cbn [map fst] in Hnd. rewrite <- app_assoc in Hnd. cbn [app] in Hnd.
    apply NoDup_remove_2 in Hnd. apply Hnd. rewrite <- !map_app. exact (in_map fst _ _ Hin). }
  eapply SR_SRO_bind.
  { refine (HCLOSE L A regs mem md ps h sw olen vtag vid pad b p F (sb_hb (g_b g) (hb1 ++ (h, 1304) :: hb2))
      SEG _ H10 ltac:(lia) Hp8 ltac:(rewrite SPZ; lia) HPS ltac:(lia) _
      (ss_guard_of_MR B APIf ra empty FF L A mem md HMR) HMI HRS).
    - exact (ss_call_pre_k B APIf ra empty g km _ L A regs mem md CLOSE_K HF
               ltac:(unfold CLOSE_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) HRA).
    - intros _. split; [exact Hh|]. split; [exact Hb|]. split; [exact HMS|]. split; [exact HOO | exact HSTD]. }
  intros c' (L' & A' & regs' & mem' & md' & -> & HC & HPS' & HGU' & HRO' & _ & H1).
  destruct (H1 ltac:(lia)) as ((b1 & b2 & Eb & Eb') & Hkept & _ & HINi & _ & HRES' & HOE' & HSTD' & HBF').
  assert (HP' : Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g))).
  { pose proof HP as HP0. rewrite Eb', <- app_assoc. apply (Permutation_app_inv _ _ _ _ (h, 1304)).
    rewrite <- Eb. rewrite <- app_assoc in HP0. cbn [app] in HP0. exact HP0. }
  assert (KB : forall a k i, In (a, k) (hb1 ++ hb2 ++ blocks (g_L g) (g_A g)) -> 0 <= i < k ->
             mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
  { intros a k i Hin Hi. apply (Hkept a k i); [| | exact Hi].
    - apply (Permutation_in _ (Permutation_sym HP)). rewrite <- app_assoc. cbn [app].
      apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; right; exact Hin].
    - intros Ea. cbv beta in Ea. subst a. exact (HNh k Hin). }
  assert (HE : forall a, close_writes ps h a -> (a < alloc_ceiling /\ ~ in_img B a) \/ ps_E ps a).
  { intros a (_ & [[Ha|Ha]|Ha]).
    - right. right. right. exact Ha.
    - left. destruct (ss_blk_facts B APIf ra empty FF L A mem md h 1304 (a - h) HMR Hh ltac:(lia))
        as (_ & _ & _ & _ & H5).
      replace (h + (a - h)) with a in H5 by lia. split; [lia | exact H5].
    - right. left. lia. }
  assert (HEd : forall a, g_S g - SLOT_K <= a < g_S g -> close_writes ps h a \/ ~ close_writes ps h a).
  { intros a _. unfold close_writes, fclose_writes. lia. }
  assert (HB0' : forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
             mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
  { intros a k i Hin Hi. apply (KB a k i); [apply in_or_app; right; apply in_or_app; right; exact Hin | exact Hi]. }
  pose proof (resb_free (g_b g) km (hb1 ++ (h, 1304) :: hb2) (hb1 ++ hb2) A' h 1304
             (Permutation_sym (Permutation_middle hb1 hb2 (h, 1304))) HRES') as HRS'.
  pose proof (ps_call_FR g km (hb1 ++ (h, 1304) :: hb2) L A regs mem md CLOSE_K _ L' A' regs' mem' md' km
              (hb1 ++ hb2) ps HF ltac:(unfold CLOSE_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia)
              ltac:(unfold fsp, SLOT_FRAME; lia) Hp2 HC HE HEd (ps_wr _ _ _ _ _ _ _ _ HPS') HB0' HRO' (HINi HIN)
              HRS') as (HF' & RP' & KF & KI & _ & _).
  apply (HK L' A' regs' mem' md' HF' HP' RP').
  - intros x Hx Hn. apply KF; [unfold fsp, SLOT_FRAME; lia | exact Hn].
  - intros a k i Hin Hi. apply (KB a k i); [|exact Hi].
    apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; apply in_or_app; left; exact Hin].
  - exact KI.
  - exact HPS'.
  - exact HOE'.
  - exact HSTD'.
  - exact HGU'.
  - exact HBF'.
Qed.

(* pcap_source_close on a closed source (h = 0): nothing but the callee's stack window changes. *)
Lemma ps_close_step0 : forall g km hb L A regs mem md ps sw olen vtag vid pad o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = wz ps ->
  fsp g <= ps -> ps + 24 <= g_S g - 104 -> ps mod 8 = 0 ->
  rw_cells rsegs mem ps (ps_cells (wz 0) sw olen vtag vid pad) ->
  (forall regs' mem',
     FR B APIf ra empty g km hb L A regs' mem' md -> regs_preserved regs regs' ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (fsp g - CLOSE_K <= x < fsp g) -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
     rw_cells rsegs mem' ps (ps_cells (wz 0) sw olen vtag vid pad) -> guard_ok mem' ->
     SRO segs (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md) o P) ->
  SRO segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_CLOSE) mem (seg_rom segs)) md) o P.
Proof.
  intros g km hb L A regs mem md ps sw olen vtag vid pad o P HF HP HRA H10 Hp1 Hp2 Hp8 HPS HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km hb L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & HIN & _ & _ & _ & _ & _ & HRS & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  eapply SR_SRO_bind.
  { refine (HCLOSE L A regs mem md ps 0 sw olen vtag vid pad 0 0 [] (sb_hb (g_b g) hb)
      SEG _ H10 ltac:(unfold fsp, SLOT_FRAME in *; lia) Hp8 ltac:(rewrite SPZ; lia) HPS ltac:(lia) _
      (ss_guard_of_MR B APIf ra empty FF L A mem md HMR) HMI HRS).
    - exact (ss_call_pre_k B APIf ra empty g km _ L A regs mem md CLOSE_K HF
               ltac:(unfold CLOSE_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) HRA).
    - intros H. exfalso. exact (H eq_refl). }
  intros c' (L' & A' & regs' & mem' & md' & -> & HC & HPS' & HGU' & HRO' & H0 & _).
  destruct (H0 eq_refl) as (-> & -> & -> & HMU & HRES').
  assert (UN : forall x, 0 <= x < 2 ^ 64 -> ~ (fsp g - CLOSE_K <= x < fsp g) ->
             mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { apply (ps_unch (fun y => fsp g - CLOSE_K <= y < fsp g) _ mem mem' HMU).
    intros lo hi y [E|[]] Hy. injection E as <- <-. rewrite SPZ in Hy. cbv beta. unfold CLOSE_K. lia. }
  assert (HE : forall a, close_writes ps 0 a -> (a < alloc_ceiling /\ ~ in_img B a) \/ ps_E ps a).
  { intros a (Ha & _). exfalso. exact (Ha eq_refl). }
  assert (HEd : forall a, g_S g - SLOT_K <= a < g_S g -> close_writes ps 0 a \/ ~ close_writes ps 0 a).
  { intros a _. right. intros (Ha & _). exact (Ha eq_refl). }
  assert (HB0' : forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
             mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
  { intros a k i Hin Hi.
    destruct (ss_b0_facts B APIf ra empty FF L A mem md hb _ a k i HMR HP Hin Hi) as (H1 & H2 & _).
    unfold mbyte. rewrite UN; [reflexivity | lia |]. unfold fsp, SLOT_FRAME, CLOSE_K in *. lia. }
  pose proof (ps_call_FR g km hb L A regs mem md CLOSE_K _ L A regs' mem' md km hb ps HF
              ltac:(unfold CLOSE_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) Hp1 Hp2 HC HE HEd
              (ps_wr _ _ _ _ _ _ _ _ HPS') HB0' HRO' HIN HRES') as (HF' & RP' & _).
  exact (HK regs' mem' HF' RP' UN HPS' HGU').
Qed.

Hypothesis HOPEN : pcap_source_open_contract B API.

(* pcap_source_open on the file F at b (its length and address in g_file_len): a good file opens the stream h, a
   new heap block; a refused one leaves the heap blocks as they were. *)
Lemma ps_open_step : forall g km hb L A regs mem md ps f sw olen vtag vid pad b F o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = wz ps -> getr regs 11 = wz A_PATH ->
  fsp g <= ps -> ps + 24 <= g_S g - 104 -> ps mod 8 = 0 ->
  rw_cells rsegs mem ps (ps_cells f sw olen vtag vid pad) ->
  bytes_at rsegs mem G_FILE_LEN (le8 (wz (Z.of_nat (length F))) ++ le8 (wz b)) ->
  Z.of_nat (length F) < 2 ^ 26 ->
  ((1 <= length F)%nat -> In (b, Z.of_nat (length F)) hb) -> bytes_at rsegs mem b F ->
  stdio_ok mem -> ofl_empty mem -> room_slots (sb_hb (g_b g) hb) 1304 ->
  (forall L' A' regs' mem' md' h,
     (pcap_good F = true ->
        FR B APIf ra empty g (km + 1) (hb ++ [(h, 1304)]) L' A' regs' mem' md' /\
        Permutation (blocks L' A') ((hb ++ [(h, 1304)]) ++ blocks (g_L g) (g_A g)) /\
        getr regs' 10 = wz 0 /\ h <> 0 /\ h mod 16 = 0 /\
        rw_cells rsegs mem' ps (ps_cells (wz h) (wz (pcap_sw F)) (wz 0) (wz 0) (wz 0) pad) /\
        mstl mem' h b F 24 (wz 0) (wz 0) /\ ofl_one mem' h) ->
     (pcap_good F = false ->
        FR B APIf ra empty g km hb L' A' regs' mem' md' /\
        Permutation (blocks L' A') (hb ++ blocks (g_L g) (g_A g)) /\
        getr regs' 10 = wz (-1) /\
        rw_cells rsegs mem' ps (ps_cells (wz 0) sw (wz 0) (wz 0) (wz 0) pad) /\ ofl_empty mem') ->
     regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> ~ (ps <= x < ps + 24) -> mbyte segs mem' x = mbyte segs mem x) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
     (forall x, img_w x -> ~ (A_OFL_HEAD <= x < A_OFL_HEAD + 8) -> mbyte segs mem' x = mbyte segs mem x) ->
     stdio_ok mem' -> guard_ok mem' -> bytes_at rsegs mem' b F ->
     SRO segs (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md') o P) ->
  SRO segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_OPEN) mem (seg_rom segs)) md) o P.
Proof.
  intros g km hb L A regs mem md ps f sw olen vtag vid pad b F o P HF HP HRA H10 H11 Hp1 Hp2 Hp8 HPS HGF HN26 HBL
    HBF HSTD HOE HROOM HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km hb L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & HIN & _ & _ & _ & _ & _ & HRS & _).
  pose proof (ss_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HF) as (_ & _ & _ & _ & HRO).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  assert (HPATH : bytes_at rsegs mem A_PATH (PATH_STR ++ [Z_to_bv 8 0])).
  { apply (ss_ro_chk_bytes mem A_PATH _ HRO); [vm_compute; reflexivity | unfold A_PATH; lia |].
    change (Z.of_nat (length (PATH_STR ++ [Z_to_bv 8 0]))) with 13. unfold A_PATH. lia. }
  eapply SR_SRO_bind.
  { refine (HOPEN L A regs mem md ps A_PATH b F f sw olen vtag vid pad (sb_hb (g_b g) hb)
      SEG _ H10 ltac:(unfold fsp, SLOT_FRAME in *; lia) Hp8 ltac:(rewrite SPZ; exact Hp1) HPS H11
      ltac:(unfold A_PATH; lia) HPATH _ HGF HN26 _ HSTD HOE (ss_guard_of_MR B APIf ra empty FF L A mem md HMR)
      HMI HRS HROOM).
    - exact (ss_call_pre_k B APIf ra empty g km hb L A regs mem md OPEN_K HF
               ltac:(unfold OPEN_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) HRA).
    - left. rewrite SPZ. unfold A_PATH, OPEN_K, fsp, SLOT_FRAME in *. lia.
    - intros Hn. split; [|exact HBF].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact (HBL Hn). }
  intros c' (L' & A' & regs' & mem' & md' & h & -> & HC & HSTD' & HGU' & HRO' & HBAD & HGOOD).
  assert (HFB : h <> 0 -> fresh_block B h 1304).
  { intros Hn. destruct (pcap_good F) eqn:EG.
    - destruct (HGOOD ltac:(first [exact EG | reflexivity])) as (_ & _ & _ & HF0 & _). exact HF0.
    - destruct (HBAD ltac:(first [exact EG | reflexivity])) as (_ & _ & _ & _ & _ & _ & _ & H0 & H1).
      destruct (Nat.eq_dec (length F) 0) as [E0|E0].
      + exfalso. exact (Hn (proj1 (H0 E0))).
      + destruct (H1 ltac:(lia)) as (_ & HF0 & _). exact HF0. }
  assert (HE : forall a, open_writes B ps h a -> (a < alloc_ceiling /\ ~ in_img B a) \/ ps_E ps a).
  { intros a [(Hn & [Ha|Ha])|[Ha|(_ & Ha)]].
    - right. right. right. exact Ha.
    - left. destruct (HFB Hn) as (F1 & F2 & F3). split; [lia|].
      replace a with (h + (a - h)) by lia. apply F3. lia.
    - right. left. lia.
    - right. right. left. exact Ha. }
  assert (HEd : forall a, g_S g - SLOT_K <= a < g_S g -> open_writes B ps h a \/ ~ open_writes B ps h a).
  { intros a _. unfold open_writes, fopen_writes, fmemopen_writes. lia. }
  destruct (pcap_good F) eqn:EG.
  - destruct (HGOOD ltac:(first [exact EG | reflexivity])) as (R10 & Hh0 & Hh16 & _ & HPS' & (b1 & b2 & Eb' & Eb)
      & Hkept & _ & HIN' & _ & HRES'
      & HMS' & HOO').
    assert (HP' : Permutation (blocks L' A') ((hb ++ [(h, 1304)]) ++ blocks (g_L g) (g_A g))).
    { rewrite Eb', <- app_assoc. cbn [app].
      apply Permutation_trans with ((h, 1304) :: (b1 ++ b2)); [apply Permutation_sym, Permutation_middle|].
      rewrite <- Eb. apply Permutation_trans with ((h, 1304) :: hb ++ blocks (g_L g) (g_A g)); [apply perm_skip; exact HP|].
      apply Permutation_middle. }
    assert (HB0' : forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
               mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
    { intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin. }
    pose proof (resb_malloc (g_b g) (km + 1) hb (hb ++ [(h, 1304)]) A' h 1304
               (Permutation_sym (Permutation_cons_append hb (h, 1304))) HRES') as HRS'.
    pose proof (ps_call_FR g km hb L A regs mem md OPEN_K _ L' A' regs' mem' md' (km + 1) (hb ++ [(h, 1304)]) ps HF
                ltac:(unfold OPEN_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) Hp1 Hp2 HC HE HEd
                (ps_wr _ _ _ _ _ _ _ _ HPS') HB0' HRO' HIN' HRS') as (HF' & RP' & KF & KI & _ & _).
    apply (HK L' A' regs' mem' md' h).
    + intros _. split; [exact HF'|]. split; [exact HP'|]. split; [exact R10|]. split; [exact Hh0|].
      split; [exact Hh16|]. split; [exact HPS'|]. split; [exact HMS' | exact HOO'].
    + intros E. first [discriminate E | rewrite EG in E; discriminate E].
    + exact RP'.
    + exact KF.
    + intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
    + exact KI.
    + exact HSTD'.
    + exact HGU'.
    + destruct HMS' as (fl0 & md0 & q & rb & (bfx & _ & _ & _ & HBF' & _) & _). exact HBF'.
  - destruct (HBAD ltac:(first [exact EG | reflexivity])) as (R10 & HPS' & HOE' & EB & Hkept & _ & _ & H0 & H1).
    assert (HX : st_init_done A' = true /\ RESB (g_b g) km hb A' /\ bytes_at rsegs mem' b F).
    { destruct (Nat.eq_dec (length F) 0) as [E0|E0].
      - destruct (H0 E0) as (_ & _ & -> & _ & HR). split; [exact HIN|]. split; [exact HR|].
        destruct HBF as (X1 & X2 & _). split; [exact X1|]. split; [exact X2|]. intros i Hi. lia.
      - destruct (H1 ltac:(lia)) as (_ & _ & HIN' & HR & HBF'). rewrite sb_free_malloc in HR.
        split; [exact HIN'|]. split; [exact HR | exact HBF']. }
    destruct HX as (HIN' & HRS' & HBF').
    assert (HP' : Permutation (blocks L' A') (hb ++ blocks (g_L g) (g_A g))) by (rewrite EB; exact HP).
    assert (HB0' : forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
               mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
    { intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin. }
    pose proof (ps_call_FR g km hb L A regs mem md OPEN_K _ L' A' regs' mem' md' km hb ps HF
                ltac:(unfold OPEN_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) Hp1 Hp2 HC HE HEd
                (ps_wr _ _ _ _ _ _ _ _ HPS') HB0' HRO' HIN' HRS') as (HF' & RP' & KF & KI & _ & _).
    apply (HK L' A' regs' mem' md' h).
    + intros E. first [discriminate E | rewrite EG in E; discriminate E].
    + intros _. split; [exact HF'|]. split; [exact HP'|]. split; [exact R10|]. split; [exact HPS' | exact HOE'].
    + exact RP'.
    + exact KF.
    + intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
    + exact KI.
    + exact HSTD'.
    + exact HGU'.
    + exact HBF'.
Qed.

Lemma ps_stk_sub : forall m lo hi hi', stk rsegs m lo hi -> hi' <= hi -> stk rsegs m lo hi'.
Proof. intros m lo hi hi' (H1 & H2 & H3) Hh. split; [exact H1|]. split; [lia|]. intros a Ha. apply H3. lia. Qed.

(* Bytes inside RELRO hold the image's bytes. *)
Lemma ps_relro_bytes : forall m a bs, relro B m -> g_rng frame_RELRO a (Z.of_nat (length bs)) = true ->
  ss_rel_chk a bs = true -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m a bs.
Proof.
  intros m a bs HR HG HC H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HR (a + Z.of_nat i) (g_rng_ok _ _ _ HG (a + Z.of_nat i) ltac:(lia))) as E.
  rewrite (ss_segs B APIf ra empty FF) in E.
  rewrite <- (ss_rel_chk_ok bs a HC i Hi). exact E.
Qed.

Hypothesis HNEXT : @pcap_source_next_contract fx.

(* pcap_source_next on the source ps with the record buffer buf (a heap block of the slot apart from the others in
   hr) and the timestamp cell ts (0, or a cell of the slot's frame). The output is the reader's. *)
Lemma ps_next_step : forall g km hb hr L A regs mem md ps buf cap ts h swz b p fl mdv lol lvt lvid pv nx tsv pad bj F
    o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  frm_zero (@YK11.fp_csr fx) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = wz ps -> getr regs 11 = wz buf -> getr regs 12 = wz cap ->
  getr regs 13 = wz ts ->
  fsp g <= ps -> ps + 24 <= g_S g - 104 -> ps mod 8 = 0 ->
  rw_cells rsegs mem ps (ps_cells (wz h) (wz swz) lol lvt lvid pad) ->
  Permutation hb ((buf, Z.max cap 1) :: hr) -> Arr.u8arr rsegs mem buf bj -> Z.of_nat (length bj) = Z.max cap 1 ->
  0 <= cap < 2 ^ 64 ->
  (ts <> 0 -> fsp g <= ts /\ ts + 8 <= g_S g - 104 /\ ts mod 8 = 0 /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\
     rw_cells rsegs mem ts [C8 tsv]) ->
  (h <> 0 -> In (h, 1304) hr /\ In (b, Z.of_nat (length F)) hr /\ mstl mem h b F p pv nx /\ (swz = 0 \/ swz = 1) /\
     Z.of_nat (length F) < 2 ^ 26) ->
  errf mem fl mdv ->
  (forall regs' mem' (Ft : bvmap 5 word) (fc' : bv 32) mdv',
     frm_zero fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get (@YK11.fp_regs fx) k) ->
     FR B APIf ra empty g km hb L A regs' mem' md -> regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> ~ (ps <= x < ps + 24) -> ~ (ts <= x < ts + 8) ->
        mbyte segs mem' x = mbyte segs mem x) ->
     (forall a k i, In (a, k) hr -> a <> h -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
     (forall x, img_w x -> ~ (A_STDERR <= x < A_STDERR + 232) -> mbyte segs mem' x = mbyte segs mem x) ->
     (stdio_ok mem -> stdio_ok mem') -> errf mem' fl mdv' -> guard_ok mem' ->
     (h = 0 -> getr regs' 10 = wz (-1)) ->
     (h <> 0 -> psn_open_post (swz =? 1) F cap p regs' mem' ps buf ts h b swz lol lvt lvid pad pv nx bj tsv) ->
     SRO segs (mkCfg (@YK11.mkst (YK11.mkFP Ft fc') regs' (getr regs 1) mem' (seg_rom segs)) md) o P) ->
  SRO segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_NEXT) mem (seg_rom segs)) md)
    (psn_out h (swz =? 1) F cap p ++ o) P.
Proof.
  intros g km hb hr L A regs mem md ps buf cap ts h swz b p fl mdv lol lvt lvid pv nx tsv pad bj F o P
    HF HP Hfrm HRA H10 H11 H12 H13 Hp1 Hp2 Hp8 HPS HPB HBJ HBN HCAP HTS HH HEF HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km hb L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof (ss_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HF) as (_ & _ & _ & _ & HRO).
  pose proof HF as (HGV & _ & _ & _ & _ & Hstk & _ & Hrel & HMR & _ & _ & _ & Hmd & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HgFd).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  destruct (mr_model B MR (aa_laws API) L A mem md HMR) as (Hhalt & Hlazy & _).
  assert (HPB' : Permutation (blocks L A) ((buf, Z.max cap 1) :: hr ++ blocks (g_L g) (g_A g))).
  { apply (Permutation_trans HP).
    change ((buf, Z.max cap 1) :: hr ++ blocks (g_L g) (g_A g))
      with (((buf, Z.max cap 1) :: hr) ++ blocks (g_L g) (g_A g)).
    apply Permutation_app_tail. exact HPB. }
  assert (Hpw : pairwise ranges_disjoint ((buf, Z.max cap 1) :: hr ++ blocks (g_L g) (g_A g))).
  { exact (ss_pw_perm ranges_disjoint ltac:(intros u v; unfold ranges_disjoint; lia) _ _ HPB'
             (mr_blocks_disjoint B MR (aa_laws API) L A mem md HMR)). }
  assert (HBH : In (buf, Z.max cap 1) hb) by (apply (Permutation_in _ (Permutation_sym HPB)); left; reflexivity).
  assert (HRH : forall x, In x hr -> In x hb)
    by (intros x Hx; apply (Permutation_in _ (Permutation_sym HPB)); right; exact Hx).
  assert (HLA : forall x, In x hb -> In x (blocks L A))
    by (intros x Hx; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hx).
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md buf (Z.max cap 1) HF HP HBH)
    as (HBW & Hbuf1 & Hbuf2 & _).
  assert (HDB : forall a k, In (a, k) hr -> buf + Z.max cap 1 <= a \/ a + k <= buf).
  { intros a k Hin. destruct Hpw as [Hd _]. pose proof (Hd (a, k) ltac:(apply in_or_app; left; exact Hin)) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. exact D. }
  assert (HDH : forall a k a' k', In (a, k) hr -> In (a', k') hr -> a <> a' -> a + k <= a' \/ a' + k' <= a).
  { intros a k a' k' H1 H2 Hne. destruct Hpw as [_ Hpw2].
    destruct (pairwise_in2 ranges_disjoint _ (a, k) (a', k') Hpw2 ltac:(apply in_or_app; left; exact H1)
                ltac:(apply in_or_app; left; exact H2) ltac:(intros E; injection E as E1 _; exact (Hne E1))) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (HHB : h <> 0 -> (forall i, 0 <= i < 1304 -> ~ in_img B (h + i)) /\ 4096 <= h /\ h + 1304 <= alloc_ceiling).
  { intros Hn. destruct (HH Hn) as (Hh & _).
    destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md h 1304 HF HP (HRH _ Hh)) as (W & H1 & H2 & _).
    split; [intros i Hi; exact (proj2 (proj2 (W i Hi))) | lia]. }
  assert (Hh64 : 0 <= h < 2 ^ 64).
  { destruct (Z.eq_dec h 0) as [->|Hn]; [lia|]. destruct (HHB Hn) as (_ & H1 & H2). lia. }
  assert (HHC : h <> 0 -> mstl mem h b F p pv nx /\ (swz = 0 \/ swz = 1) /\ Z.of_nat (length F) < 2 ^ 26 /\
       h + 1304 <= g_S g - SLOT_K /\ b + Z.of_nat (length F) <= g_S g - SLOT_K /\ img_apart h 1304 /\
       (buf + Z.max cap 1 <= h \/ h + 1304 <= buf) /\
       (buf + Z.max cap 1 <= b \/ b + Z.of_nat (length F) <= buf) /\
       (F <> [] -> img_apart b (Z.of_nat (length F)))).
  { intros Hn. destruct (HH Hn) as (Hh & Hb & HMS & Hsw & HF26).
    destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md h 1304 HF HP (HRH _ Hh)) as (_ & H1 & H2 & _).
    destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md b _ HF HP (HRH _ Hb)) as (_ & B1 & B2 & _).
    split; [exact HMS|]. split; [exact Hsw|]. split; [exact HF26|].
    split; [lia|]. split; [lia|].
    split; [exact (ps_blk_apart L A mem md h 1304 HMR (HLA _ (HRH _ Hh)) ltac:(lia))|].
    split; [exact (HDB h 1304 Hh)|]. split; [exact (HDB b _ Hb)|].
    intros HFn. apply (ps_blk_apart L A mem md b _ HMR (HLA _ (HRH _ Hb))).
    destruct F as [|x F']; [contradiction|]. cbn [length]. lia. }
  assert (HTS' : ts <> 0 -> spZ regs <= ts /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\ rw_cells rsegs mem ts [C8 tsv]).
  { intros Hn. destruct (HTS Hn) as (T1 & T2 & T3 & T4 & T5). rewrite SPZ.
    split; [exact T1|]. split; [exact T4 | exact T5]. }
  assert (HG1 : bytes_at rsegs mem A_GOT_STDERR (le8 (wz A_STDERR_VAR))).
  { apply (ps_relro_bytes mem); [exact Hrel | vm_compute; reflexivity | vm_compute; reflexivity |
      unfold A_GOT_STDERR; lia | rewrite length_le8; unfold A_GOT_STDERR; lia]. }
  assert (HG2 : bytes_at rsegs mem A_STDERR_VAR (le8 (wz A_STDERR))).
  { apply (ps_relro_bytes mem); [exact Hrel | vm_compute; reflexivity | vm_compute; reflexivity |
      unfold A_STDERR_VAR; lia | rewrite length_le8; unfold A_STDERR_VAR; lia]. }
  rewrite SEG. rewrite SEG in HK.
  eapply SRO_bind.
  { exact (HNEXT regs mem md ps buf cap ts h swz b p fl mdv (g_S g - SLOT_K) lol lvt lvid pv nx tsv pad bj F
      H10 H11 H12 H13 HRA ltac:(rewrite SPZ; exact Hp1) HPS Hh64 HHC HCAP
      Hbuf1 HBJ HBN (ps_blk_apart L A mem md buf _ HMR (HLA _ HBH) ltac:(lia)) ltac:(lia) HTS' HG1 HG2 HEF
      (ss_guard_of_MR B APIf ra empty FF L A mem md HMR) HRO
      ltac:(rewrite SPZ; exact (ps_stk_sub mem (g_S g - SLOT_K) (g_S g) (fsp g) Hstk ltac:(unfold fsp, SLOT_FRAME; lia)))
      ltac:(rewrite SPZ; unfold NEXT_K, fsp, SLOT_FRAME; lia) ltac:(lia)
      ltac:(rewrite SPZ; unfold fsp, SLOT_FRAME; lia) Hfrm Hhalt Hlazy
      ltac:(destruct Hmd as (vm & ->); exact HgFd)). }
  intros c' (regs' & mem' & Ft & fc' & mdv' & -> & Hfc & HFt & RP & HMU & HWM & HEF' & HGU' & HRO' & HST' & H0 & H1).
  assert (UN : forall x, 0 <= x < 2 ^ 64 ->
     ~ ((fsp g - NEXT_K <= x < fsp g) \/ (A_STDERR <= x < A_STDERR + 232) \/ (ps <= x < ps + 24) \/
        (buf <= x < buf + Z.max cap 1) \/ (ts <> 0 /\ ts <= x < ts + 8) \/ (h <> 0 /\ h <= x < h + 1304)) ->
     mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { destruct (Z.eq_dec h 0) as [Hh0|Hhn].
    - destruct (H0 Hh0) as (_ & HMU0). intros x Hx Hn.
      apply (ps_unch (fun y => fsp g - NEXT_K <= y < fsp g) _ mem mem' HMU0); [|exact Hx|].
      + intros lo hi y [E|[]] Hy. injection E as <- <-. rewrite SPZ in Hy. cbv beta. unfold NEXT_K. lia.
      + intros Hy. apply Hn. left. exact Hy.
    - intros x Hx Hn.
      apply (ps_unch (fun y => (fsp g - NEXT_K <= y < fsp g) \/ (A_STDERR <= y < A_STDERR + 232) \/
        (ps <= y < ps + 24) \/ (buf <= y < buf + Z.max cap 1) \/ (ts <> 0 /\ ts <= y < ts + 8) \/
        (h <> 0 /\ h <= y < h + 1304)) _ mem mem' HMU); [|exact Hx|exact Hn].
      intros lo hi y Hin Hy. cbv beta. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-.
      + left. rewrite SPZ in Hy. exact Hy.
      + right. left. exact Hy.
      + right. right. left. exact Hy.
      + right. right. right. left. exact Hy.
      + right. right. right. right. left. revert Hy. destruct (Z.eqb_spec ts 0) as [T|T]; intros Hy;
          [lia | split; [exact T | exact Hy]].
      + right. right. right. right. right. split; [exact Hhn | exact Hy]. }
  assert (UNI : forall x, in_img B x -> ~ (A_STDERR <= x < A_STDERR + 232) ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hi Hns. pose proof (ss_img_lt B APIf ra empty FF x Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    apply UN; [lia|]. intros [W|[W|[W|[W|[(T & W)|(Hn & W)]]]]].
    - unfold fsp, SLOT_FRAME, NEXT_K in *. lia.
    - exact (Hns W).
    - unfold fsp, SLOT_FRAME in *. lia.
    - destruct (HBW (x - buf) ltac:(lia)) as (_ & _ & Hni). apply Hni.
      replace (buf + (x - buf)) with x by lia. exact Hi.
    - destruct (HTS T) as (T1 & _). unfold fsp, SLOT_FRAME in *. lia.
    - destruct (HHB Hn) as (Hni & _). apply (Hni (x - h)); [lia|]. replace (h + (x - h)) with x by lia. exact Hi. }
  assert (HF' : FR B APIf ra empty g km hb L A regs' mem' md).
  { apply (ss_FR_kr B APIf ra empty FF g km hb L A regs mem md regs' mem' HF HP).
    - exact (RP 2 ltac:(unfold callee_saved; lia)).
    - exact (RP 3 ltac:(unfold callee_saved; lia)).
    - exact (RP 4 ltac:(unfold callee_saved; lia)).
    - intros x Hx Hk. apply UN; [exact Hx|]. intros Hw. apply Hk.
      destruct Hw as [W|[W|[W|[W|[(T & W)|(Hn & W)]]]]].
      + left. unfold fsp, SLOT_FRAME, NEXT_K in *. lia.
      + right. right. apply img_w_iff. left. exact W.
      + left. unfold fsp, SLOT_FRAME in *. lia.
      + right. left. exists buf, (Z.max cap 1). split; [exact HBH | exact W].
      + left. destruct (HTS T) as (T1 & T2 & _). unfold fsp, SLOT_FRAME in *. lia.
      + right. left. exists h, 1304. split; [exact (HRH _ (proj1 (HH Hn))) | exact W].
    - exact HWM.
    - intros a Ha. rewrite <- (Hrel a Ha).
      destruct (ss_relro_img B APIf ra empty FF a Ha) as (Hi & _).
      assert (D : (A_STDERR <= a < A_STDERR + 232) \/ ~ (A_STDERR <= a < A_STDERR + 232)) by lia.
      destruct D as [D|D].
      + rewrite SEG. exact (ps_errf_same mem mem' fl mdv mdv' HEF HEF' a D (ps_relro_nmode a Ha)).
      + unfold mbyte. rewrite (UNI a Hi D). reflexivity. }
  apply (HK regs' mem' Ft fc' mdv' Hfc HFt HF' RP).
  - intros x Hx Hnp Hnt. unfold mbyte. rewrite UN; [reflexivity | unfold fsp, SLOT_FRAME in *; lia |].
    intros [W|[W|[W|[W|[(T & W)|(Hn & W)]]]]].
    + unfold fsp, SLOT_FRAME, NEXT_K in *. lia.
    + unfold A_STDERR in W. unfold fsp, SLOT_FRAME in *. lia.
    + exact (Hnp W).
    + unfold fsp, SLOT_FRAME in *. lia.
    + exact (Hnt W).
    + destruct (HHB Hn) as (_ & H1' & H2'). unfold fsp, SLOT_FRAME in *. lia.
  - intros a k i Hin Hna Hi.
    destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a k HF HP (HRH _ Hin)) as (W0 & A1 & A2 & _).
    destruct (W0 i Hi) as (_ & _ & Hni).
    unfold mbyte. rewrite UN; [reflexivity | lia |].
    intros [W|[W|[W|[W|[(T & W)|(Hn & W)]]]]].
    + unfold fsp, SLOT_FRAME, NEXT_K in *. lia.
    + apply Hni. destruct (ss_img_w_facts B APIf ra empty FF (a + i) (proj2 (img_w_iff (a + i)) (or_introl W)))
        as (Hi' & _). exact Hi'.
    + unfold fsp, SLOT_FRAME in *. lia.
    + destruct (HDB a k Hin) as [D|D]; lia.
    + destruct (HTS T) as (T1 & _). unfold fsp, SLOT_FRAME in *. lia.
    + destruct (HH Hn) as (Hh & _). destruct (HDH a k h 1304 Hin Hh Hna) as [D|D]; lia.
  - intros x Hx Hns. destruct (ss_img_w_facts B APIf ra empty FF x Hx) as (Hi & _).
    unfold mbyte. rewrite (UNI x Hi Hns). reflexivity.
  - intros HSTD. pose proof HF' as (_ & _ & _ & _ & _ & _ & _ & _ & HMR' & _).
    refine (ss_stdio_keep B APIf ra empty FF L A mem mem' md HMR' HSTD _).
    intros x Hx. destruct (ss_stdio_addr B APIf ra empty FF x Hx) as (Hi & _).
    unfold mbyte. rewrite (UNI x Hi ltac:(unfold A_LIBC, A_OFL_LOCK, A_STDERR in *; lia)). reflexivity.
  - exact HEF'.
  - exact HGU'.
  - intros Hh0. exact (proj1 (H0 Hh0)).
  - exact H1.
Qed.


(* Cut-free twins (SROcf) of the three reader steps, through the cut-free reader contracts (PContractCF.v). *)
Hypothesis HCLOSECF : pcap_source_close_contract_cf B API.
Hypothesis HOPENCF : pcap_source_open_contract_cf B API.
Hypothesis HNEXTCF : @pcap_source_next_contract_cf fx.

Lemma ps_close_step_cf : forall g km hb1 h hb2 L A regs mem md ps sw olen vtag vid pad b F p o P,
  FR B APIf ra empty g km (hb1 ++ (h, 1304) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (h, 1304) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = wz ps ->
  fsp g <= ps -> ps + 24 <= g_S g - 104 -> ps mod 8 = 0 ->
  rw_cells rsegs mem ps (ps_cells (wz h) sw olen vtag vid pad) ->
  In (b, Z.of_nat (length F)) (hb1 ++ (h, 1304) :: hb2) ->
  mstl mem h b F p (wz 0) (wz 0) -> ofl_one mem h -> stdio_ok mem ->
  (forall L' A' regs' mem' md',
     FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> ~ (ps <= x < ps + 24) -> mbyte segs mem' x = mbyte segs mem x) ->
     (forall a k i, In (a, k) (hb1 ++ hb2) -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
     (forall x, img_w x -> ~ (A_OFL_HEAD <= x < A_OFL_HEAD + 8) -> mbyte segs mem' x = mbyte segs mem x) ->
     rw_cells rsegs mem' ps (ps_cells (wz 0) sw olen vtag vid pad) ->
     ofl_empty mem' -> stdio_ok mem' -> guard_ok mem' -> bytes_at rsegs mem' b F ->
     SROcf segs (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md') o P) ->
  SROcf segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_CLOSE) mem (seg_rom segs)) md) o P.
Proof.
  intros g km hb1 h hb2 L A regs mem md ps sw olen vtag vid pad b F p o P HF HP HRA H10 Hp1 Hp2 Hp8 HPS HinB HMS
    HOO HSTD HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km _ L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & HIN & _ & _ & _ & _ & _ & HRS & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  unfold fsp, SLOT_FRAME in *.
  assert (Hh : In (h, 1304) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  assert (Hb : In (b, Z.of_nat (length F)) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact HinB. }
  destruct (ss_blk_facts B APIf ra empty FF L A mem md h 1304 0 HMR Hh ltac:(lia)) as (_ & Hh1 & Hh2 & _ & _).
  assert (HNh : forall k, In (h, k) (hb1 ++ hb2 ++ blocks (g_L g) (g_A g)) -> False).
  { intros k Hin.
    destruct (ss_alloc B APIf ra empty FF) as (_ & _ & _ & _ & _ & _ & _ & _ & ND & _).
    pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (ND L A mem md HMR)) as Hnd.
    pose proof (Permutation_map fst HP) as HPf. apply (Permutation_NoDup HPf) in Hnd.
    rewrite !map_app in Hnd. cbn [map fst] in Hnd. rewrite <- app_assoc in Hnd. cbn [app] in Hnd.
    apply NoDup_remove_2 in Hnd. apply Hnd. rewrite <- !map_app. exact (in_map fst _ _ Hin). }
  eapply (SRcf_SROcf_bind B).
  { refine (HCLOSECF L A regs mem md ps h sw olen vtag vid pad b p F (sb_hb (g_b g) (hb1 ++ (h, 1304) :: hb2))
      SEG _ H10 ltac:(lia) Hp8 ltac:(rewrite SPZ; lia) HPS ltac:(lia) _
      (ss_guard_of_MR B APIf ra empty FF L A mem md HMR) HMI HRS).
    - exact (ss_call_pre_k B APIf ra empty g km _ L A regs mem md CLOSE_K HF
               ltac:(unfold CLOSE_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) HRA).
    - intros _. split; [exact Hh|]. split; [exact Hb|]. split; [exact HMS|]. split; [exact HOO | exact HSTD]. }
  intros c' (L' & A' & regs' & mem' & md' & -> & HC & HPS' & HGU' & HRO' & _ & H1).
  destruct (H1 ltac:(lia)) as ((b1 & b2 & Eb & Eb') & Hkept & _ & HINi & _ & HRES' & HOE' & HSTD' & HBF').
  assert (HP' : Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g))).
  { pose proof HP as HP0. rewrite Eb', <- app_assoc. apply (Permutation_app_inv _ _ _ _ (h, 1304)).
    rewrite <- Eb. rewrite <- app_assoc in HP0. cbn [app] in HP0. exact HP0. }
  assert (KB : forall a k i, In (a, k) (hb1 ++ hb2 ++ blocks (g_L g) (g_A g)) -> 0 <= i < k ->
             mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
  { intros a k i Hin Hi. apply (Hkept a k i); [| | exact Hi].
    - apply (Permutation_in _ (Permutation_sym HP)). rewrite <- app_assoc. cbn [app].
      apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; right; exact Hin].
    - intros Ea. cbv beta in Ea. subst a. exact (HNh k Hin). }
  assert (HE : forall a, close_writes ps h a -> (a < alloc_ceiling /\ ~ in_img B a) \/ ps_E ps a).
  { intros a (_ & [[Ha|Ha]|Ha]).
    - right. right. right. exact Ha.
    - left. destruct (ss_blk_facts B APIf ra empty FF L A mem md h 1304 (a - h) HMR Hh ltac:(lia))
        as (_ & _ & _ & _ & H5).
      replace (h + (a - h)) with a in H5 by lia. split; [lia | exact H5].
    - right. left. lia. }
  assert (HEd : forall a, g_S g - SLOT_K <= a < g_S g -> close_writes ps h a \/ ~ close_writes ps h a).
  { intros a _. unfold close_writes, fclose_writes. lia. }
  assert (HB0' : forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
             mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
  { intros a k i Hin Hi. apply (KB a k i); [apply in_or_app; right; apply in_or_app; right; exact Hin | exact Hi]. }
  pose proof (resb_free (g_b g) km (hb1 ++ (h, 1304) :: hb2) (hb1 ++ hb2) A' h 1304
             (Permutation_sym (Permutation_middle hb1 hb2 (h, 1304))) HRES') as HRS'.
  pose proof (ps_call_FR g km (hb1 ++ (h, 1304) :: hb2) L A regs mem md CLOSE_K _ L' A' regs' mem' md' km
              (hb1 ++ hb2) ps HF ltac:(unfold CLOSE_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia)
              ltac:(unfold fsp, SLOT_FRAME; lia) Hp2 HC HE HEd (ps_wr _ _ _ _ _ _ _ _ HPS') HB0' HRO' (HINi HIN)
              HRS') as (HF' & RP' & KF & KI & _ & _).
  apply (HK L' A' regs' mem' md' HF' HP' RP').
  - intros x Hx Hn. apply KF; [unfold fsp, SLOT_FRAME; lia | exact Hn].
  - intros a k i Hin Hi. apply (KB a k i); [|exact Hi].
    apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; apply in_or_app; left; exact Hin].
  - exact KI.
  - exact HPS'.
  - exact HOE'.
  - exact HSTD'.
  - exact HGU'.
  - exact HBF'.
Qed.

Lemma ps_close_step0_cf : forall g km hb L A regs mem md ps sw olen vtag vid pad o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = wz ps ->
  fsp g <= ps -> ps + 24 <= g_S g - 104 -> ps mod 8 = 0 ->
  rw_cells rsegs mem ps (ps_cells (wz 0) sw olen vtag vid pad) ->
  (forall regs' mem',
     FR B APIf ra empty g km hb L A regs' mem' md -> regs_preserved regs regs' ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (fsp g - CLOSE_K <= x < fsp g) -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
     rw_cells rsegs mem' ps (ps_cells (wz 0) sw olen vtag vid pad) -> guard_ok mem' ->
     SROcf segs (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md) o P) ->
  SROcf segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_CLOSE) mem (seg_rom segs)) md) o P.
Proof.
  intros g km hb L A regs mem md ps sw olen vtag vid pad o P HF HP HRA H10 Hp1 Hp2 Hp8 HPS HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km hb L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & HIN & _ & _ & _ & _ & _ & HRS & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  eapply (SRcf_SROcf_bind B).
  { refine (HCLOSECF L A regs mem md ps 0 sw olen vtag vid pad 0 0 [] (sb_hb (g_b g) hb)
      SEG _ H10 ltac:(unfold fsp, SLOT_FRAME in *; lia) Hp8 ltac:(rewrite SPZ; lia) HPS ltac:(lia) _
      (ss_guard_of_MR B APIf ra empty FF L A mem md HMR) HMI HRS).
    - exact (ss_call_pre_k B APIf ra empty g km _ L A regs mem md CLOSE_K HF
               ltac:(unfold CLOSE_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) HRA).
    - intros H. exfalso. exact (H eq_refl). }
  intros c' (L' & A' & regs' & mem' & md' & -> & HC & HPS' & HGU' & HRO' & H0 & _).
  destruct (H0 eq_refl) as (-> & -> & -> & HMU & HRES').
  assert (UN : forall x, 0 <= x < 2 ^ 64 -> ~ (fsp g - CLOSE_K <= x < fsp g) ->
             mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { apply (ps_unch (fun y => fsp g - CLOSE_K <= y < fsp g) _ mem mem' HMU).
    intros lo hi y [E|[]] Hy. injection E as <- <-. rewrite SPZ in Hy. cbv beta. unfold CLOSE_K. lia. }
  assert (HE : forall a, close_writes ps 0 a -> (a < alloc_ceiling /\ ~ in_img B a) \/ ps_E ps a).
  { intros a (Ha & _). exfalso. exact (Ha eq_refl). }
  assert (HEd : forall a, g_S g - SLOT_K <= a < g_S g -> close_writes ps 0 a \/ ~ close_writes ps 0 a).
  { intros a _. right. intros (Ha & _). exact (Ha eq_refl). }
  assert (HB0' : forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
             mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
  { intros a k i Hin Hi.
    destruct (ss_b0_facts B APIf ra empty FF L A mem md hb _ a k i HMR HP Hin Hi) as (H1 & H2 & _).
    unfold mbyte. rewrite UN; [reflexivity | lia |]. unfold fsp, SLOT_FRAME, CLOSE_K in *. lia. }
  pose proof (ps_call_FR g km hb L A regs mem md CLOSE_K _ L A regs' mem' md km hb ps HF
              ltac:(unfold CLOSE_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) Hp1 Hp2 HC HE HEd
              (ps_wr _ _ _ _ _ _ _ _ HPS') HB0' HRO' HIN HRES') as (HF' & RP' & _).
  exact (HK regs' mem' HF' RP' UN HPS' HGU').
Qed.

Lemma ps_open_step_cf : forall g km hb L A regs mem md ps f sw olen vtag vid pad b F o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = wz ps -> getr regs 11 = wz A_PATH ->
  fsp g <= ps -> ps + 24 <= g_S g - 104 -> ps mod 8 = 0 ->
  rw_cells rsegs mem ps (ps_cells f sw olen vtag vid pad) ->
  bytes_at rsegs mem G_FILE_LEN (le8 (wz (Z.of_nat (length F))) ++ le8 (wz b)) ->
  Z.of_nat (length F) < 2 ^ 26 ->
  ((1 <= length F)%nat -> In (b, Z.of_nat (length F)) hb) -> bytes_at rsegs mem b F ->
  stdio_ok mem -> ofl_empty mem -> room_cf md (sb_hb (g_b g) hb) 1304 ->
  (forall L' A' regs' mem' md' h,
     (pcap_good F = true ->
        FR B APIf ra empty g (km + 1) (hb ++ [(h, 1304)]) L' A' regs' mem' md' /\
        Permutation (blocks L' A') ((hb ++ [(h, 1304)]) ++ blocks (g_L g) (g_A g)) /\
        getr regs' 10 = wz 0 /\ h <> 0 /\ h mod 16 = 0 /\
        rw_cells rsegs mem' ps (ps_cells (wz h) (wz (pcap_sw F)) (wz 0) (wz 0) (wz 0) pad) /\
        mstl mem' h b F 24 (wz 0) (wz 0) /\ ofl_one mem' h) ->
     (pcap_good F = false ->
        FR B APIf ra empty g km hb L' A' regs' mem' md' /\
        Permutation (blocks L' A') (hb ++ blocks (g_L g) (g_A g)) /\
        getr regs' 10 = wz (-1) /\
        rw_cells rsegs mem' ps (ps_cells (wz 0) sw (wz 0) (wz 0) (wz 0) pad) /\ ofl_empty mem') ->
     regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> ~ (ps <= x < ps + 24) -> mbyte segs mem' x = mbyte segs mem x) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
     (forall x, img_w x -> ~ (A_OFL_HEAD <= x < A_OFL_HEAD + 8) -> mbyte segs mem' x = mbyte segs mem x) ->
     stdio_ok mem' -> guard_ok mem' -> bytes_at rsegs mem' b F ->
     SROcf segs (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md') o P) ->
  SROcf segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_OPEN) mem (seg_rom segs)) md) o P.
Proof.
  intros g km hb L A regs mem md ps f sw olen vtag vid pad b F o P HF HP HRA H10 H11 Hp1 Hp2 Hp8 HPS HGF HN26 HBL
    HBF HSTD HOE HROOM HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km hb L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & HIN & _ & _ & _ & _ & _ & HRS & _).
  pose proof (ss_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HF) as (_ & _ & _ & _ & HRO).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  assert (HPATH : bytes_at rsegs mem A_PATH (PATH_STR ++ [Z_to_bv 8 0])).
  { apply (ss_ro_chk_bytes mem A_PATH _ HRO); [vm_compute; reflexivity | unfold A_PATH; lia |].
    change (Z.of_nat (length (PATH_STR ++ [Z_to_bv 8 0]))) with 13. unfold A_PATH. lia. }
  eapply (SRcf_SROcf_bind B).
  { refine (HOPENCF L A regs mem md ps A_PATH b F f sw olen vtag vid pad (sb_hb (g_b g) hb)
      SEG _ H10 ltac:(unfold fsp, SLOT_FRAME in *; lia) Hp8 ltac:(rewrite SPZ; exact Hp1) HPS H11
      ltac:(unfold A_PATH; lia) HPATH _ HGF HN26 _ HSTD HOE (ss_guard_of_MR B APIf ra empty FF L A mem md HMR)
      HMI HRS HROOM).
    - exact (ss_call_pre_k B APIf ra empty g km hb L A regs mem md OPEN_K HF
               ltac:(unfold OPEN_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) HRA).
    - left. rewrite SPZ. unfold A_PATH, OPEN_K, fsp, SLOT_FRAME in *. lia.
    - intros Hn. split; [|exact HBF].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact (HBL Hn). }
  intros c' (L' & A' & regs' & mem' & md' & h & -> & HC & HSTD' & HGU' & HRO' & HBAD & HGOOD).
  assert (HFB : h <> 0 -> fresh_block B h 1304).
  { intros Hn. destruct (pcap_good F) eqn:EG.
    - destruct (HGOOD ltac:(first [exact EG | reflexivity])) as (_ & _ & _ & HF0 & _). exact HF0.
    - destruct (HBAD ltac:(first [exact EG | reflexivity])) as (_ & _ & _ & _ & _ & _ & _ & H0 & H1).
      destruct (Nat.eq_dec (length F) 0) as [E0|E0].
      + exfalso. exact (Hn (proj1 (H0 E0))).
      + destruct (H1 ltac:(lia)) as (_ & HF0 & _). exact HF0. }
  assert (HE : forall a, open_writes B ps h a -> (a < alloc_ceiling /\ ~ in_img B a) \/ ps_E ps a).
  { intros a [(Hn & [Ha|Ha])|[Ha|(_ & Ha)]].
    - right. right. right. exact Ha.
    - left. destruct (HFB Hn) as (F1 & F2 & F3). split; [lia|].
      replace a with (h + (a - h)) by lia. apply F3. lia.
    - right. left. lia.
    - right. right. left. exact Ha. }
  assert (HEd : forall a, g_S g - SLOT_K <= a < g_S g -> open_writes B ps h a \/ ~ open_writes B ps h a).
  { intros a _. unfold open_writes, fopen_writes, fmemopen_writes. lia. }
  destruct (pcap_good F) eqn:EG.
  - destruct (HGOOD ltac:(first [exact EG | reflexivity])) as (R10 & Hh0 & Hh16 & _ & HPS' & (b1 & b2 & Eb' & Eb)
      & Hkept & _ & HIN' & _ & HRES'
      & HMS' & HOO').
    assert (HP' : Permutation (blocks L' A') ((hb ++ [(h, 1304)]) ++ blocks (g_L g) (g_A g))).
    { rewrite Eb', <- app_assoc. cbn [app].
      apply Permutation_trans with ((h, 1304) :: (b1 ++ b2)); [apply Permutation_sym, Permutation_middle|].
      rewrite <- Eb. apply Permutation_trans with ((h, 1304) :: hb ++ blocks (g_L g) (g_A g)); [apply perm_skip; exact HP|].
      apply Permutation_middle. }
    assert (HB0' : forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
               mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
    { intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin. }
    pose proof (resb_malloc (g_b g) (km + 1) hb (hb ++ [(h, 1304)]) A' h 1304
               (Permutation_sym (Permutation_cons_append hb (h, 1304))) HRES') as HRS'.
    pose proof (ps_call_FR g km hb L A regs mem md OPEN_K _ L' A' regs' mem' md' (km + 1) (hb ++ [(h, 1304)]) ps HF
                ltac:(unfold OPEN_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) Hp1 Hp2 HC HE HEd
                (ps_wr _ _ _ _ _ _ _ _ HPS') HB0' HRO' HIN' HRS') as (HF' & RP' & KF & KI & _ & _).
    apply (HK L' A' regs' mem' md' h).
    + intros _. split; [exact HF'|]. split; [exact HP'|]. split; [exact R10|]. split; [exact Hh0|].
      split; [exact Hh16|]. split; [exact HPS'|]. split; [exact HMS' | exact HOO'].
    + intros E. first [discriminate E | rewrite EG in E; discriminate E].
    + exact RP'.
    + exact KF.
    + intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
    + exact KI.
    + exact HSTD'.
    + exact HGU'.
    + destruct HMS' as (fl0 & md0 & q & rb & (bfx & _ & _ & _ & HBF' & _) & _). exact HBF'.
  - destruct (HBAD ltac:(first [exact EG | reflexivity])) as (R10 & HPS' & HOE' & EB & Hkept & _ & _ & H0 & H1).
    assert (HX : st_init_done A' = true /\ RESB (g_b g) km hb A' /\ bytes_at rsegs mem' b F).
    { destruct (Nat.eq_dec (length F) 0) as [E0|E0].
      - destruct (H0 E0) as (_ & _ & -> & _ & HR). split; [exact HIN|]. split; [exact HR|].
        destruct HBF as (X1 & X2 & _). split; [exact X1|]. split; [exact X2|]. intros i Hi. lia.
      - destruct (H1 ltac:(lia)) as (_ & _ & HIN' & HR & HBF'). rewrite sb_free_malloc in HR.
        split; [exact HIN'|]. split; [exact HR | exact HBF']. }
    destruct HX as (HIN' & HRS' & HBF').
    assert (HP' : Permutation (blocks L' A') (hb ++ blocks (g_L g) (g_A g))) by (rewrite EB; exact HP).
    assert (HB0' : forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
               mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
    { intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin. }
    pose proof (ps_call_FR g km hb L A regs mem md OPEN_K _ L' A' regs' mem' md' km hb ps HF
                ltac:(unfold OPEN_K, SLOT_K, SLOT_STACK, SLOT_FRAME; lia) Hp1 Hp2 HC HE HEd
                (ps_wr _ _ _ _ _ _ _ _ HPS') HB0' HRO' HIN' HRS') as (HF' & RP' & KF & KI & _ & _).
    apply (HK L' A' regs' mem' md' h).
    + intros E. first [discriminate E | rewrite EG in E; discriminate E].
    + intros _. split; [exact HF'|]. split; [exact HP'|]. split; [exact R10|]. split; [exact HPS' | exact HOE'].
    + exact RP'.
    + exact KF.
    + intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
    + exact KI.
    + exact HSTD'.
    + exact HGU'.
    + exact HBF'.
Qed.

Lemma ps_next_step_cf : forall g km hb hr L A regs mem md ps buf cap ts h swz b p fl mdv lol lvt lvid pv nx tsv pad bj F
    o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  frm_zero (@YK11.fp_csr fx) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = wz ps -> getr regs 11 = wz buf -> getr regs 12 = wz cap ->
  getr regs 13 = wz ts ->
  fsp g <= ps -> ps + 24 <= g_S g - 104 -> ps mod 8 = 0 ->
  rw_cells rsegs mem ps (ps_cells (wz h) (wz swz) lol lvt lvid pad) ->
  Permutation hb ((buf, Z.max cap 1) :: hr) -> Arr.u8arr rsegs mem buf bj -> Z.of_nat (length bj) = Z.max cap 1 ->
  0 <= cap < 2 ^ 64 ->
  (ts <> 0 -> fsp g <= ts /\ ts + 8 <= g_S g - 104 /\ ts mod 8 = 0 /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\
     rw_cells rsegs mem ts [C8 tsv]) ->
  (h <> 0 -> In (h, 1304) hr /\ In (b, Z.of_nat (length F)) hr /\ mstl mem h b F p pv nx /\ (swz = 0 \/ swz = 1) /\
     Z.of_nat (length F) < 2 ^ 26) ->
  errf mem fl mdv ->
  (forall regs' mem' (Ft : bvmap 5 word) (fc' : bv 32) mdv',
     frm_zero fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get (@YK11.fp_regs fx) k) ->
     FR B APIf ra empty g km hb L A regs' mem' md -> regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> ~ (ps <= x < ps + 24) -> ~ (ts <= x < ts + 8) ->
        mbyte segs mem' x = mbyte segs mem x) ->
     (forall a k i, In (a, k) hr -> a <> h -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
     (forall x, img_w x -> ~ (A_STDERR <= x < A_STDERR + 232) -> mbyte segs mem' x = mbyte segs mem x) ->
     (stdio_ok mem -> stdio_ok mem') -> errf mem' fl mdv' -> guard_ok mem' ->
     (h = 0 -> getr regs' 10 = wz (-1)) ->
     (h <> 0 -> psn_open_post (swz =? 1) F cap p regs' mem' ps buf ts h b swz lol lvt lvid pad pv nx bj tsv) ->
     SROcf segs (mkCfg (@YK11.mkst (YK11.mkFP Ft fc') regs' (getr regs 1) mem' (seg_rom segs)) md) o P) ->
  SROcf segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_NEXT) mem (seg_rom segs)) md)
    (psn_out h (swz =? 1) F cap p ++ o) P.
Proof.
  intros g km hb hr L A regs mem md ps buf cap ts h swz b p fl mdv lol lvt lvid pv nx tsv pad bj F o P
    HF HP Hfrm HRA H10 H11 H12 H13 Hp1 Hp2 Hp8 HPS HPB HBJ HBN HCAP HTS HH HEF HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  destruct (ps_spZ g km hb L A regs mem md HF) as (SPZ & HSc & HS47).
  pose proof (ss_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ _ HF) as (_ & _ & _ & _ & HRO).
  pose proof HF as (HGV & _ & _ & _ & _ & Hstk & _ & Hrel & HMR & _ & _ & _ & Hmd & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HgFd).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  destruct (mr_model B MR (aa_laws API) L A mem md HMR) as (Hhalt & Hlazy & _).
  assert (HPB' : Permutation (blocks L A) ((buf, Z.max cap 1) :: hr ++ blocks (g_L g) (g_A g))).
  { apply (Permutation_trans HP).
    change ((buf, Z.max cap 1) :: hr ++ blocks (g_L g) (g_A g))
      with (((buf, Z.max cap 1) :: hr) ++ blocks (g_L g) (g_A g)).
    apply Permutation_app_tail. exact HPB. }
  assert (Hpw : pairwise ranges_disjoint ((buf, Z.max cap 1) :: hr ++ blocks (g_L g) (g_A g))).
  { exact (ss_pw_perm ranges_disjoint ltac:(intros u v; unfold ranges_disjoint; lia) _ _ HPB'
             (mr_blocks_disjoint B MR (aa_laws API) L A mem md HMR)). }
  assert (HBH : In (buf, Z.max cap 1) hb) by (apply (Permutation_in _ (Permutation_sym HPB)); left; reflexivity).
  assert (HRH : forall x, In x hr -> In x hb)
    by (intros x Hx; apply (Permutation_in _ (Permutation_sym HPB)); right; exact Hx).
  assert (HLA : forall x, In x hb -> In x (blocks L A))
    by (intros x Hx; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hx).
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md buf (Z.max cap 1) HF HP HBH)
    as (HBW & Hbuf1 & Hbuf2 & _).
  assert (HDB : forall a k, In (a, k) hr -> buf + Z.max cap 1 <= a \/ a + k <= buf).
  { intros a k Hin. destruct Hpw as [Hd _]. pose proof (Hd (a, k) ltac:(apply in_or_app; left; exact Hin)) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. exact D. }
  assert (HDH : forall a k a' k', In (a, k) hr -> In (a', k') hr -> a <> a' -> a + k <= a' \/ a' + k' <= a).
  { intros a k a' k' H1 H2 Hne. destruct Hpw as [_ Hpw2].
    destruct (pairwise_in2 ranges_disjoint _ (a, k) (a', k') Hpw2 ltac:(apply in_or_app; left; exact H1)
                ltac:(apply in_or_app; left; exact H2) ltac:(intros E; injection E as E1 _; exact (Hne E1))) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (HHB : h <> 0 -> (forall i, 0 <= i < 1304 -> ~ in_img B (h + i)) /\ 4096 <= h /\ h + 1304 <= alloc_ceiling).
  { intros Hn. destruct (HH Hn) as (Hh & _).
    destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md h 1304 HF HP (HRH _ Hh)) as (W & H1 & H2 & _).
    split; [intros i Hi; exact (proj2 (proj2 (W i Hi))) | lia]. }
  assert (Hh64 : 0 <= h < 2 ^ 64).
  { destruct (Z.eq_dec h 0) as [->|Hn]; [lia|]. destruct (HHB Hn) as (_ & H1 & H2). lia. }
  assert (HHC : h <> 0 -> mstl mem h b F p pv nx /\ (swz = 0 \/ swz = 1) /\ Z.of_nat (length F) < 2 ^ 26 /\
       h + 1304 <= g_S g - SLOT_K /\ b + Z.of_nat (length F) <= g_S g - SLOT_K /\ img_apart h 1304 /\
       (buf + Z.max cap 1 <= h \/ h + 1304 <= buf) /\
       (buf + Z.max cap 1 <= b \/ b + Z.of_nat (length F) <= buf) /\
       (F <> [] -> img_apart b (Z.of_nat (length F)))).
  { intros Hn. destruct (HH Hn) as (Hh & Hb & HMS & Hsw & HF26).
    destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md h 1304 HF HP (HRH _ Hh)) as (_ & H1 & H2 & _).
    destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md b _ HF HP (HRH _ Hb)) as (_ & B1 & B2 & _).
    split; [exact HMS|]. split; [exact Hsw|]. split; [exact HF26|].
    split; [lia|]. split; [lia|].
    split; [exact (ps_blk_apart L A mem md h 1304 HMR (HLA _ (HRH _ Hh)) ltac:(lia))|].
    split; [exact (HDB h 1304 Hh)|]. split; [exact (HDB b _ Hb)|].
    intros HFn. apply (ps_blk_apart L A mem md b _ HMR (HLA _ (HRH _ Hb))).
    destruct F as [|x F']; [contradiction|]. cbn [length]. lia. }
  assert (HTS' : ts <> 0 -> spZ regs <= ts /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\ rw_cells rsegs mem ts [C8 tsv]).
  { intros Hn. destruct (HTS Hn) as (T1 & T2 & T3 & T4 & T5). rewrite SPZ.
    split; [exact T1|]. split; [exact T4 | exact T5]. }
  assert (HG1 : bytes_at rsegs mem A_GOT_STDERR (le8 (wz A_STDERR_VAR))).
  { apply (ps_relro_bytes mem); [exact Hrel | vm_compute; reflexivity | vm_compute; reflexivity |
      unfold A_GOT_STDERR; lia | rewrite length_le8; unfold A_GOT_STDERR; lia]. }
  assert (HG2 : bytes_at rsegs mem A_STDERR_VAR (le8 (wz A_STDERR))).
  { apply (ps_relro_bytes mem); [exact Hrel | vm_compute; reflexivity | vm_compute; reflexivity |
      unfold A_STDERR_VAR; lia | rewrite length_le8; unfold A_STDERR_VAR; lia]. }
  rewrite SEG. rewrite SEG in HK.
  eapply SROcf_bind.
  { exact (HNEXTCF regs mem md ps buf cap ts h swz b p fl mdv (g_S g - SLOT_K) lol lvt lvid pv nx tsv pad bj F
      H10 H11 H12 H13 HRA ltac:(rewrite SPZ; exact Hp1) HPS Hh64 HHC HCAP
      Hbuf1 HBJ HBN (ps_blk_apart L A mem md buf _ HMR (HLA _ HBH) ltac:(lia)) ltac:(lia) HTS' HG1 HG2 HEF
      (ss_guard_of_MR B APIf ra empty FF L A mem md HMR) HRO
      ltac:(rewrite SPZ; exact (ps_stk_sub mem (g_S g - SLOT_K) (g_S g) (fsp g) Hstk ltac:(unfold fsp, SLOT_FRAME; lia)))
      ltac:(rewrite SPZ; unfold NEXT_K, fsp, SLOT_FRAME; lia) ltac:(lia)
      ltac:(rewrite SPZ; unfold fsp, SLOT_FRAME; lia) Hfrm Hhalt Hlazy
      ltac:(destruct Hmd as (vm & ->); exact HgFd)). }
  intros c' (regs' & mem' & Ft & fc' & mdv' & -> & Hfc & HFt & RP & HMU & HWM & HEF' & HGU' & HRO' & HST' & H0 & H1).
  assert (UN : forall x, 0 <= x < 2 ^ 64 ->
     ~ ((fsp g - NEXT_K <= x < fsp g) \/ (A_STDERR <= x < A_STDERR + 232) \/ (ps <= x < ps + 24) \/
        (buf <= x < buf + Z.max cap 1) \/ (ts <> 0 /\ ts <= x < ts + 8) \/ (h <> 0 /\ h <= x < h + 1304)) ->
     mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { destruct (Z.eq_dec h 0) as [Hh0|Hhn].
    - destruct (H0 Hh0) as (_ & HMU0). intros x Hx Hn.
      apply (ps_unch (fun y => fsp g - NEXT_K <= y < fsp g) _ mem mem' HMU0); [|exact Hx|].
      + intros lo hi y [E|[]] Hy. injection E as <- <-. rewrite SPZ in Hy. cbv beta. unfold NEXT_K. lia.
      + intros Hy. apply Hn. left. exact Hy.
    - intros x Hx Hn.
      apply (ps_unch (fun y => (fsp g - NEXT_K <= y < fsp g) \/ (A_STDERR <= y < A_STDERR + 232) \/
        (ps <= y < ps + 24) \/ (buf <= y < buf + Z.max cap 1) \/ (ts <> 0 /\ ts <= y < ts + 8) \/
        (h <> 0 /\ h <= y < h + 1304)) _ mem mem' HMU); [|exact Hx|exact Hn].
      intros lo hi y Hin Hy. cbv beta. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-.
      + left. rewrite SPZ in Hy. exact Hy.
      + right. left. exact Hy.
      + right. right. left. exact Hy.
      + right. right. right. left. exact Hy.
      + right. right. right. right. left. revert Hy. destruct (Z.eqb_spec ts 0) as [T|T]; intros Hy;
          [lia | split; [exact T | exact Hy]].
      + right. right. right. right. right. split; [exact Hhn | exact Hy]. }
  assert (UNI : forall x, in_img B x -> ~ (A_STDERR <= x < A_STDERR + 232) ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hi Hns. pose proof (ss_img_lt B APIf ra empty FF x Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    apply UN; [lia|]. intros [W|[W|[W|[W|[(T & W)|(Hn & W)]]]]].
    - unfold fsp, SLOT_FRAME, NEXT_K in *. lia.
    - exact (Hns W).
    - unfold fsp, SLOT_FRAME in *. lia.
    - destruct (HBW (x - buf) ltac:(lia)) as (_ & _ & Hni). apply Hni.
      replace (buf + (x - buf)) with x by lia. exact Hi.
    - destruct (HTS T) as (T1 & _). unfold fsp, SLOT_FRAME in *. lia.
    - destruct (HHB Hn) as (Hni & _). apply (Hni (x - h)); [lia|]. replace (h + (x - h)) with x by lia. exact Hi. }
  assert (HF' : FR B APIf ra empty g km hb L A regs' mem' md).
  { apply (ss_FR_kr B APIf ra empty FF g km hb L A regs mem md regs' mem' HF HP).
    - exact (RP 2 ltac:(unfold callee_saved; lia)).
    - exact (RP 3 ltac:(unfold callee_saved; lia)).
    - exact (RP 4 ltac:(unfold callee_saved; lia)).
    - intros x Hx Hk. apply UN; [exact Hx|]. intros Hw. apply Hk.
      destruct Hw as [W|[W|[W|[W|[(T & W)|(Hn & W)]]]]].
      + left. unfold fsp, SLOT_FRAME, NEXT_K in *. lia.
      + right. right. apply img_w_iff. left. exact W.
      + left. unfold fsp, SLOT_FRAME in *. lia.
      + right. left. exists buf, (Z.max cap 1). split; [exact HBH | exact W].
      + left. destruct (HTS T) as (T1 & T2 & _). unfold fsp, SLOT_FRAME in *. lia.
      + right. left. exists h, 1304. split; [exact (HRH _ (proj1 (HH Hn))) | exact W].
    - exact HWM.
    - intros a Ha. rewrite <- (Hrel a Ha).
      destruct (ss_relro_img B APIf ra empty FF a Ha) as (Hi & _).
      assert (D : (A_STDERR <= a < A_STDERR + 232) \/ ~ (A_STDERR <= a < A_STDERR + 232)) by lia.
      destruct D as [D|D].
      + rewrite SEG. exact (ps_errf_same mem mem' fl mdv mdv' HEF HEF' a D (ps_relro_nmode a Ha)).
      + unfold mbyte. rewrite (UNI a Hi D). reflexivity. }
  apply (HK regs' mem' Ft fc' mdv' Hfc HFt HF' RP).
  - intros x Hx Hnp Hnt. unfold mbyte. rewrite UN; [reflexivity | unfold fsp, SLOT_FRAME in *; lia |].
    intros [W|[W|[W|[W|[(T & W)|(Hn & W)]]]]].
    + unfold fsp, SLOT_FRAME, NEXT_K in *. lia.
    + unfold A_STDERR in W. unfold fsp, SLOT_FRAME in *. lia.
    + exact (Hnp W).
    + unfold fsp, SLOT_FRAME in *. lia.
    + exact (Hnt W).
    + destruct (HHB Hn) as (_ & H1' & H2'). unfold fsp, SLOT_FRAME in *. lia.
  - intros a k i Hin Hna Hi.
    destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a k HF HP (HRH _ Hin)) as (W0 & A1 & A2 & _).
    destruct (W0 i Hi) as (_ & _ & Hni).
    unfold mbyte. rewrite UN; [reflexivity | lia |].
    intros [W|[W|[W|[W|[(T & W)|(Hn & W)]]]]].
    + unfold fsp, SLOT_FRAME, NEXT_K in *. lia.
    + apply Hni. destruct (ss_img_w_facts B APIf ra empty FF (a + i) (proj2 (img_w_iff (a + i)) (or_introl W)))
        as (Hi' & _). exact Hi'.
    + unfold fsp, SLOT_FRAME in *. lia.
    + destruct (HDB a k Hin) as [D|D]; lia.
    + destruct (HTS T) as (T1 & _). unfold fsp, SLOT_FRAME in *. lia.
    + destruct (HH Hn) as (Hh & _). destruct (HDH a k h 1304 Hin Hh Hna) as [D|D]; lia.
  - intros x Hx Hns. destruct (ss_img_w_facts B APIf ra empty FF x Hx) as (Hi & _).
    unfold mbyte. rewrite (UNI x Hi Hns). reflexivity.
  - intros HSTD. pose proof HF' as (_ & _ & _ & _ & _ & _ & _ & _ & HMR' & _).
    refine (ss_stdio_keep B APIf ra empty FF L A mem mem' md HMR' HSTD _).
    intros x Hx. destruct (ss_stdio_addr B APIf ra empty FF x Hx) as (Hi & _).
    unfold mbyte. rewrite (UNI x Hi ltac:(unfold A_LIBC, A_OFL_LOCK, A_STDERR in *; lia)). reflexivity.
  - exact HEF'.
  - exact HGU'.
  - intros Hh0. exact (proj1 (H0 Hh0)).
  - exact H1.
Qed.

End PS.
