(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: what the text_buf and text_of steps
   (LFrTx.v) share.
   - closed facts of the plain image: every reservation starts at or above 0x10000 at a multiple of 8, the
     texts table (0x207f0, 88) and [0x21000, 0x97000) lie in the image, every byte of the first PT_LOAD
     [A_RO_LO, A_RO_END) = [0x10000, 0x11eb4) is read-only with a file byte;
   - the 8-byte round-up the answer's slack runs to, and the bytes past a heap block up to it;
   - the cell views moved between a raw memory and its evt-level view (MemNorm.normalize_cj);
   - ltx_call: the frame step through a callee that hands out at most one block (r, n) (none when r = 0) and
     also writes the slot's own frame cells Es: LFr.LFR at the return with hb' = LFr.opt_hb r n hb, the regions
     lkeep keeps (minus Es) carried between the views, lpost_mem, and lfresh of the block. It runs on
     LFrCall.lfr_call.
   Every constant is link's (the plain image, lib/FrameAPI.v frame_facts_plain through LFr.LFF). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrCall LFrRun.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Closed facts of the plain image
   ========================================================================== *)

(* the reservations start at 0x10000, 0x12000, 0x20000, 0x21000 (page-rounded PT_LOADs) *)
Lemma ltx_res_chk : forallb (fun s => (0x10000 <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) mod 8 =? 0))
  (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ltx_texts_chk : lfr_rng_img A_TEXTS (A_TEXTS + 8 * TEXTS_N) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ltx_hi_chk : lfr_rng_img 0x21000 LF_TOP = true.
Proof. vm_compute. reflexivity. Qed.

(* a byte of the first PT_LOAD: read-only, with a file byte *)
Definition ltx_ro_byte (x : Z) : bool :=
  Mem.ro_addr rsegs (Z_to_bv 64 x) && match seg_rom rsegs (Z_to_bv 64 x) with Some _ => true | None => false end.

Lemma ltx_ro_chk : forallb (fun i => ltx_ro_byte (A_RO_LO + Z.of_nat i)) (seq 0 (Z.to_nat (A_RO_END - A_RO_LO))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ltx_ro_ok : forall x, A_RO_LO <= x < A_RO_END ->
  Mem.ro_addr rsegs (Z_to_bv 64 x) = true /\ exists b, seg_rom rsegs (Z_to_bv 64 x) = Some b.
Proof.
  intros x Hx. pose proof ltx_ro_chk as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (x - A_RO_LO)) ltac:(apply in_seq; unfold A_RO_LO, A_RO_END in *; lia)).
  replace (A_RO_LO + Z.of_nat (Z.to_nat (x - A_RO_LO))) with x in H by lia.
  unfold ltx_ro_byte in H. apply andb_prop in H as [H1 H2]. split; [exact H1|].
  destruct (seg_rom rsegs (Z_to_bv 64 x)) as [b|]; [exists b; reflexivity | discriminate H2].
Qed.

(* ==========================================================================
   2. Arithmetic: the round-up to a multiple of 8
   ========================================================================== *)

Lemma ltx_rup : forall x, x + (- x) mod 8 = 8 * ((x + 7) / 8).
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma ltx_rup_bnd : forall x, x <= 8 * ((x + 7) / 8) <= x + 7.
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma ltx_rup_le : forall x y, x <= y -> y mod 8 = 0 -> 8 * ((x + 7) / 8) <= y.
Proof. intros x y H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma ltx_rup_mono : forall x y, x <= y -> 8 * ((x + 7) / 8) <= 8 * ((y + 7) / 8).
Proof. intros x y H. Z.div_mod_to_equations. lia. Qed.

Lemma ltx_dec2 : forall a x n y m, ((x <= a < x + n) \/ (y <= a < y + m)) \/ ~ ((x <= a < x + n) \/ (y <= a < y + m)).
Proof.
  intros a x n y m.
  destruct (Z_le_gt_dec x a) as [H1|H1]; [destruct (Z_lt_ge_dec a (x + n)) as [H2|H2]|];
    [left; left; lia | |].
  all: destruct (Z_le_gt_dec y a) as [H3|H3]; [destruct (Z_lt_ge_dec a (y + m)) as [H4|H4]|];
    [left; right; lia | right; intros [[Ha Hb]|[Ha Hb]]; lia | right; intros [[Ha Hb]|[Ha Hb]]; lia].
Qed.

Lemma ltx_cj_hi : forall x, LF_TOP <= x < TASK_SIZE -> cj_drop rsegs (Z_to_bv 64 x) = false.
Proof.
  intros x Hx. apply lc_cj_keep; [unfold LF_TOP in Hx; lia|]. apply lc_ro_hi. unfold TASK_SIZE in Hx. lia.
Qed.

(* ==========================================================================
   3. Lists of blocks, memory views
   ========================================================================== *)

Lemma ltx_opt_nz : forall r n hb, r <> 0 -> opt_hb r n hb = (r, n) :: hb.
Proof. intros r n hb H. unfold opt_hb. destruct (Z.eqb_spec r 0); [contradiction | reflexivity]. Qed.

Lemma ltx_opt_incl : forall r n hb x, In x hb -> In x (opt_hb r n hb).
Proof. intros r n hb x H. unfold opt_hb. destruct (r =? 0); [exact H | right; exact H]. Qed.

(* bytes that read Some form a byte list *)
Lemma ltx_bytes_ex : forall n m a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, Mem.mrd rsegs m (Z_to_bv 64 (a + Z.of_nat i)) = Some b) ->
  exists l, length l = n /\ bytes_at rsegs m a l.
Proof.
  induction n as [|n IH]; intros m a H1 H2 H.
  - exists []. split; [reflexivity|]. split; [exact H1|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H O ltac:(lia)) as [b Hb].
    destruct (IH m (a + 1) ltac:(lia) ltac:(lia)) as (l & Hl & Hbl).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as [b' Hb']. exists b'.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb'. }
    exists (b :: l). split; [cbn [length]; rewrite Hl; reflexivity|].
    split; [exact H1|]. split; [cbn [length]; lia|].
    intros [|i] Hi.
    + cbn [nth_error]. exact Hb.
    + cbn [nth_error]. destruct Hbl as (_ & _ & Hbl). cbn [length] in Hi.
      replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply Hbl. lia.
Qed.

(* cells of a raw memory, at addresses its view keeps, are cells of the view *)
Lemma ltx_rw_norm : forall m a cs, ro_agree rsegs m ->
  a + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> cj_drop rsegs (Z_to_bv 64 (a + i)) = false) ->
  rw_cells rsegs m a cs -> rw_cells rsegs (normalize_cj rsegs m) a cs.
Proof.
  intros m a cs Hro Hle Hk [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - apply (bytes_at_normalize_cj_low rsegs m); [exact Hro | rewrite cells_bytes_length by exact Hwf; exact Hle | exact Hb].
  - exact (wr_at_norm_cj rsegs m (normalize_cj rsegs m) a _ (mem_rel_cj_normalize rsegs m Hro) Hw Hk).
Qed.

(* cells of the view are cells of the raw memory *)
Lemma ltx_rw_raw : forall m a cs, ro_agree rsegs m ->
  rw_cells rsegs (normalize_cj rsegs m) a cs -> rw_cells rsegs m a cs.
Proof.
  intros m a cs Hro [[Hwf Hb] Hw]. pose proof (mem_rel_cj_normalize rsegs m Hro) as HR.
  split; [split; [exact Hwf | exact (bytes_at_rel_cj rsegs m _ a _ HR Hb)] | exact (wr_at_rel_cj rsegs m _ a _ HR Hw)].
Qed.

(* above the image a byte that reads Some is present *)
Lemma ltx_present_hi : forall m x b, LF_TOP <= x < 2 ^ 64 -> Mem.mrd rsegs m (Z_to_bv 64 x) = Some b ->
  m (Z_to_bv 64 x) = Some b.
Proof.
  intros m x b Hx H. unfold Mem.mrd in H. destruct (m (Z_to_bv 64 x)) as [b'|] eqn:E; [exact H|].
  exfalso.
  assert (HF : find_segment rsegs (bv_unsigned (Z_to_bv 64 x)) 1 = None).
  { rewrite (MState.unsigned_lit x ltac:(unfold LF_TOP in Hx; lia)).
    destruct (find_segment rsegs x 1) as [seg|] eqn:Es; [|reflexivity].
    pose proof (lfr_find_top x 1 seg Es). unfold LF_TOP in *. lia. }
  match type of H with ?l = _ => assert (Hr : l = None) by exact (MemNorm.seg_rom_unmapped rsegs _ HF) end.
  rewrite Hr in H. discriminate H.
Qed.

(* above the image the bytes a byte list reads are writable *)
Lemma ltx_wr_hi : forall m a bs i, bytes_at rsegs m a bs -> LF_TOP <= a -> (i < length bs)%nat ->
  writable_at rsegs m (a + Z.of_nat i).
Proof.
  intros m a bs i (H0 & H1 & H) Ha Hi. pose proof (H i Hi) as E.
  destruct (nth_error bs i) as [b|] eqn:En; [|apply nth_error_None in En; lia].
  unfold writable_at. rewrite (lfr_wview_hi m (a + Z.of_nat i)) by lia.
  rewrite (ltx_present_hi m (a + Z.of_nat i) b ltac:(lia) E). discriminate.
Qed.

(* ==========================================================================
   4. The image, the heap and the frame step
   ========================================================================== *)

Section TA.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.
Local Notation segs := (ms_segs B).
Local Notation MR := (aa_MR API).

Lemma ltx_segs : ms_segs B = rsegs.
Proof. exact (lc_segs B API FF). Qed.

Lemma ltx_img_lo : forall a, in_img B a -> 0x10000 <= a.
Proof.
  intros a [_ (s & Hs & Hr)]. rewrite ltx_segs in Hs.
  pose proof ltx_res_chk as H. rewrite forallb_forall in H. specialize (H s Hs).
  apply andb_prop in H as [H1 _]. apply Z.leb_le in H1. lia.
Qed.

Lemma ltx_ro_img : forall y, 0 <= y < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 y) = true -> in_img B y.
Proof.
  intros y Hy H. unfold Mem.ro_addr in H. rewrite (MState.unsigned_lit y Hy) in H.
  destruct (find_segment rsegs y 1) as [seg|] eqn:E; [exact (lfr_find_img B y seg ltx_segs E) | discriminate H].
Qed.

(* the bytes past a block up to the next multiple of 8 are not the image's: a reservation that starts there
   starts at a multiple of 8 *)
Lemma ltx_slack_noimg : forall a k x, 1 <= k -> (forall i, 0 <= i < k -> ~ in_img B (a + i)) ->
  a + k <= x < 8 * ((a + k + 7) / 8) -> ~ in_img B x.
Proof.
  intros a k x Hk Hn Hx [Hne (s & Hs & Hr)].
  pose proof ltx_res_chk as H. rewrite forallb_forall in H. pose proof Hs as Hs'. rewrite ltx_segs in Hs'.
  specialize (H s Hs'). apply andb_prop in H as [_ H2]. apply Z.eqb_eq in H2.
  destruct (Z_le_gt_dec (bv_unsigned (fst s)) (a + k - 1)) as [Hb|Hb].
  - apply (Hn (k - 1) ltac:(lia)). split; [exact Hne|]. exists s. split; [exact Hs | lia].
  - clear Hn. Z.div_mod_to_equations. lia.
Qed.

(* a stretch with no image byte and a stretch of image bytes are apart *)
Lemma ltx_apart_img : forall lo1 hi1 lo2 hi2, lo1 < hi1 -> lo2 < hi2 ->
  (forall y, lo1 <= y < hi1 -> ~ in_img B y) -> (forall y, lo2 <= y < hi2 -> in_img B y) ->
  hi1 <= lo2 \/ hi2 <= lo1.
Proof.
  intros lo1 hi1 lo2 hi2 H1 H2 Hn Hi.
  destruct (Z_le_gt_dec hi1 lo2) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec hi2 lo1) as [E'|E']; [right; exact E'|].
  exfalso. apply (Hn (Z.max lo1 lo2)); [lia|]. apply Hi. lia.
Qed.

Lemma ltx_cj_out : forall x, 0 <= x < TASK_SIZE -> ~ in_img B x -> cj_drop rsegs (Z_to_bv 64 x) = false.
Proof.
  intros x Hx Hn. apply lc_cj_keep; [exact Hx|].
  apply (lfr_ro_addr_out B x ltx_segs Hn). unfold TASK_SIZE in Hx. lia.
Qed.

(* the payload, when there is one, is an entry block below the allocator's ceiling (LGV's lib_pre) *)
Lemma ltx_payload : forall g, LGV B API g -> 0 < lg_n g ->
  In (lg_p g, lg_n g) (blocks (lg_L g) (lg_A g)) /\ 4096 <= lg_p g /\ lg_p g + lg_n g <= YM05.alloc_ceiling.
Proof.
  intros g HGV Hn. pose proof HGV as (Hpre & _).
  destruct Hpre as (HP & _). destruct HP as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpay & _).
  destruct Hpay as [(Hn0 & _) | (_ & q & Hq & Hpq)]; [lia|].
  pose proof (mr_blocks_range B MR (aa_laws API) _ _ _ _ q (lg_n g) HM Hq) as (R1 & R2).
  rewrite Hpq in R1, R2. split; [|split; assumption].
  apply blocks_In. exists q. split; [exact Hpq | exact Hq].
Qed.

(* the texts table: the entry's image bytes (LGV's G_img over frame_RELRO), kept by LFR's image clause *)
Lemma ltx_texts_img : forall g hb T L A mem md, LFR B API g hb T L A mem md ->
  G_img_c B [(A_TEXTS, 8 * TEXTS_N)] mem.
Proof.
  intros g hb T L A mem md HF. unfold G_img_c. intros a (lo & len & Hin & Ha).
  destruct Hin as [E|[]]. injection E as <- <-.
  destruct HF as (HGV & _ & _ & _ & _ & _ & _ & Himg & _).
  pose proof HGV as (_ & _ & _ & _ & HGI & _). unfold G_img in HGI.
  pose proof FF as (_ & _ & _ & _ & _ & _ & GU & GO & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP & EOFF & _
    & VML & DBL & _).
  assert (Hlf : lf_img B a).
  { split; [exact (lfr_img_rng B API FF _ _ ltx_texts_chk a Ha)|].
    unfold A_TEXTS, TEXTS_N in Ha.
    split.
    { unfold static_owned, vml_lo, vml_len. rewrite LCK, LIBC, GO, GU, DBR, SCL, SMC, MDC, VML, DBL.
      cbv iota. lia. }
    split; [rewrite CTX; unfold CTX_SIZE; lia|].
    unfold errno_addr. rewrite TP, EOFF. lia. }
  assert (Hng : ~ in_globals llvm_G a).
  { intros (lo' & len' & Hin' & Ha'). unfold A_TEXTS, TEXTS_N in Ha. unfold llvm_G, frame_G in Hin'.
    repeat (destruct Hin' as [Hin'|Hin']; [injection Hin' as <- <-; lia|]). destruct Hin'. }
  destruct (Himg a Hlf Hng) as [E1 _]. rewrite E1.
  apply HGI. exists 0x207b0, 296. split; [unfold frame_RELRO; left; reflexivity | unfold A_TEXTS, TEXTS_N in Ha; lia].
Qed.

(* cells inside the stack window of an LFR state's view are writable there *)
Lemma ltx_rw_win : forall g hb T L A mem md a cs, LFR B API g hb T L A mem md ->
  lg_S g - SLOT_STACK <= a -> a + Z.of_nat (cells_size cs) <= lg_S g ->
  cells_at rsegs (normalize_cj rsegs mem) a cs -> rw_cells rsegs (normalize_cj rsegs mem) a cs.
Proof.
  intros g hb T L A mem md a cs HF H1 H2 Hc. split; [exact Hc|].
  destruct HF as (HGV & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & _).
  destruct (lc_gv B API g HGV) as (HS & _ & HS47 & _). pose proof (@lc_ceil rc) as [HC1 HC2].
  split; [unfold SLOT_STACK, LF_TOP in *; lia|]. split; [lia|].
  intros i Hi. pose proof (Hwin (a + i) ltac:(lia)) as W. rewrite ltx_segs in W.
  pose proof (lc_norm_keep mem (a + i) (ltx_cj_hi (a + i) ltac:(unfold LF_TOP, TASK_SIZE, SLOT_STACK in *; lia)))
    as [_ K].
  exact (proj2 K W).
Qed.

(* a callee's footprint E may be widened *)
Lemma ltx_post_E : forall K L A regs mem md (E E' : Z -> Prop) L' A' regs' mem' md',
  (forall a, E a -> E' a) ->
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  call_post_k B MR K L A regs mem md E' L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E E' L' A' regs' mem' md' HEE (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs He. exact (H8 a Ha Ho Ho' Hs (fun h => He (HEE a h))).
Qed.

(* THE STEP through a callee that hands out at most one block (r, n) (r = 0: none, and then n <= 4096 bytes
   from 0 are its footprint, which nothing the slot keeps meets) and writes the slot's frame cells Es *)
Lemma ltx_call : forall g hb T L A mem md regs K (Es : Z -> Prop) r n L' A' regs' mem' md',
  LFR B API g hb T L A mem md ->
  spZ regs = lg_S g - SLOT_FRAME -> 0 <= K <= SLOT_STACK - SLOT_FRAME ->
  call_post_k B MR K L A regs mem md (fun a => (r <= a < r + n) \/ Es a) L' A' regs' mem' md' ->
  (forall a, Es a -> lg_S g - SLOT_FRAME <= a < lg_S g) ->
  (forall a, Es a \/ ~ Es a) ->
  (forall a, Es a -> writable_at segs mem' a) ->
  ro_agree segs mem' ->
  (r = 0 -> 0 <= n <= 4096 /\ L' = L /\ A' = A) ->
  (r <> 0 -> 1 <= n /\ fresh_block B r n /\
     (exists b1 b2, blocks L' A' = b1 ++ (r, n) :: b2 /\ blocks L A = b1 ++ b2) /\
     res_ok_slots A' (sb_malloc (sb_hb (lg_b g) hb) n) /\
     (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
     st_init_done A' = true) ->
  LFR B API g (opt_hb r n hb) T L' A' mem' md' /\
  lcarry (fun x => lkeep B g hb x /\ ~ Es x) (normalize_cj rsegs mem) (normalize_cj rsegs mem') /\
  lpost_mem g (normalize_cj rsegs mem') /\
  (r <> 0 -> lfresh B g hb r n).
Proof.
  intros g hb T L A mem md regs K Es r n L' A' regs' mem' md' HF Hsp HK HC HEs HEd HEw HRO' H0 H1.
  pose proof ltx_segs as SEG. pose proof (@lc_ceil rc) as [HC1 HC2]. unfold LF_TOP in HC1.
  pose proof HF as (HGV & HM & HW & HBD & HID & _ & _ & _ & _ & Hwin & _ & _ & _ & HRS & HP & HKT & HGI).
  destruct (lc_gv B API g HGV) as (HS & HS16 & HS47 & HM0 & Htb).
  pose proof HC as (HM' & _ & _ & _ & _ & _ & _ & _ & HUB & _).
  (* every live block of A keeps its bytes *)
  assert (HBK : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
             mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
  { intros a k i Hin Hi. apply blocks_In in Hin as (q & <- & Hq).
    apply (HUB q k i Hq); [|exact Hi].
    destruct (Z.eq_dec r 0) as [Hr|Hr].
    - destruct (H0 Hr) as (_ & _ & ->). exact Hq.
    - destruct (H1 Hr) as (_ & _ & _ & _ & Hinc & _). exact (Hinc q k Hq). }
  (* the block handed out is fresh *)
  assert (HFR : r <> 0 -> lfresh B g hb r n).
  { intros Hr. destruct (H1 Hr) as (_ & Hfb & (b1 & b2 & E1 & E2) & _).
    exact (lfr_fresh B API g hb L A L' A' mem' md' b1 b2 r n HGV HP HM' E1 E2 Hr Hfb). }
  (* the block part of the footprint meets nothing lkeep names *)
  assert (HEB : forall a, r <= a < r + n -> 0 <= a < YM05.alloc_ceiling /\ ~ in_img B a /\ ~ lkeep B g hb a).
  { intros a Ha. destruct (Z.eq_dec r 0) as [Hr|Hr].
    - destruct (H0 Hr) as (Hn & _ & _). subst r.
      assert (Hni : ~ in_img B a) by (intros Hi; pose proof (ltx_img_lo a Hi); lia).
      split; [lia|]. split; [exact Hni|].
      intros [Hk|[(Hi & _)|[(t & k & Ht & Hx)|(t & k & Ht & Hx)]]].
      + unfold SLOT_STACK, SLOT_FRAME in *. lia.
      + exact (Hni Hi).
      + assert (Ht' : In (t, k) (blocks L A))
          by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Ht).
        destruct (lc_blk B API FF L A mem md t k (a - t) HM Ht' ltac:(lia)) as (_ & Hl & _). lia.
      + destruct (lc_blk B API FF (lg_L g) (lg_A g) (lg_mem g) (lg_md g) t k (a - t) HM0 Ht ltac:(lia))
          as (_ & Hl & _). lia.
    - pose proof (HFR Hr) as (_ & Hr4 & Hrs & Hri & Hhb & Hb0).
      destruct (H1 Hr) as (_ & (_ & Hrc & _) & _).
      split; [lia|]. split; [replace a with (r + (a - r)) by lia; apply Hri; lia|].
      intros [Hk|[(Hi & _)|[(t & k & Ht & Hx)|(t & k & Ht & Hx)]]].
      + unfold SLOT_STACK, SLOT_FRAME in *. lia.
      + apply (Hri (a - r)); [lia|]. replace (r + (a - r)) with a by lia. exact Hi.
      + destruct (Hhb t k Ht); lia.
      + destruct (Hb0 t k Ht); lia. }
  (* the frame part lies above the ceiling, in the stack window, outside the image *)
  assert (HEsF : forall a, Es a -> YM05.alloc_ceiling <= a /\ ~ in_img B a /\ lg_S g - SLOT_STACK <= a < lg_S g).
  { intros a Ha. pose proof (HEs a Ha) as Hf.
    split; [unfold SLOT_STACK, SLOT_FRAME in *; lia|].
    split; [intros Hi; pose proof (lfr_in_img_top B a SEG Hi); unfold LF_TOP, SLOT_STACK, SLOT_FRAME in *; lia|].
    unfold SLOT_STACK, SLOT_FRAME in *. lia. }
  assert (HnEi : forall a, lf_img B a -> ~ ((r <= a < r + n) \/ Es a)).
  { intros a (Hi & _) [Hb|He]; [exact (proj1 (proj2 (HEB a Hb)) Hi) | exact (proj1 (proj2 (HEsF a He)) Hi)]. }
  assert (P1 : forall a, (fun a => (r <= a < r + n) \/ Es a) a -> YM05.alloc_ceiling <= a ->
             lg_S g - SLOT_STACK <= a < lg_S g).
  { intros a [Hb|He] Hc; [destruct (HEB a Hb) as (H & _); lia | exact (proj2 (proj2 (HEsF a He)))]. }
  assert (P2 : forall a, (fun a => (r <= a < r + n) \/ Es a) a -> lf_img B a -> in_globals llvm_G a).
  { intros a He Hi. exfalso. exact (HnEi a Hi He). }
  assert (P3 : forall a, lg_S g - SLOT_STACK <= a < lg_S g ->
             (fun a => (r <= a < r + n) \/ Es a) a \/ ~ (fun a => (r <= a < r + n) \/ Es a) a).
  { intros a _. cbv beta. destruct (HEd a) as [He|He]; [left; right; exact He|].
    destruct (Z_le_gt_dec r a) as [Ha1|Ha1]; [destruct (Z_lt_ge_dec a (r + n)) as [Ha2|Ha2]|].
    - left. left. lia.
    - right. intros [Hb|Hb]; [lia | exact (He Hb)].
    - right. intros [Hb|Hb]; [lia | exact (He Hb)]. }
  assert (P4 : forall a, (fun a => (r <= a < r + n) \/ Es a) a -> lg_S g - SLOT_STACK <= a < lg_S g ->
             writable_at segs mem' a).
  { intros a [Hb|He] Hw; [exfalso; destruct (HEB a Hb) as (H & _); unfold SLOT_STACK in *; lia | exact (HEw a He)]. }
  assert (P5 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> ~ (fun a => (r <= a < r + n) \/ Es a) (a + i) ->
             mbyte segs mem' (a + i) = mbyte segs mem (a + i)).
  { intros a k i Hin Hi _. exact (HBK a k i Hin Hi). }
  assert (P6 : forall a k i, In (a, k) (blocks (lg_L g) (lg_A g)) -> ~ In (a, k) (lg_T g) -> 0 <= i < k ->
             ~ (fun a => (r <= a < r + n) \/ Es a) (a + i)).
  { intros a k i Hin _ Hi [Hb|He].
    - apply (proj2 (proj2 (HEB (a + i) Hb))). right. right. right. exists a, k. split; [exact Hin | lia].
    - destruct (lc_blk B API FF _ _ _ _ a k i HM0 Hin Hi) as (_ & _ & Hc & _).
      destruct (HEsF _ He) as (Hc' & _). lia. }
  assert (P7 : st_init_done A' = true).
  { destruct (Z.eq_dec r 0) as [Hr|Hr]; [destruct (H0 Hr) as (_ & _ & ->); exact HID|].
    destruct (H1 Hr) as (_ & _ & _ & _ & _ & H). exact H. }
  assert (P9 : res_ok_slots A' (sb_hb (lg_b g) (opt_hb r n hb))).
  { destruct (Z.eq_dec r 0) as [Hr|Hr].
    - destruct (H0 Hr) as (_ & _ & ->). subst r. exact HRS.
    - rewrite (ltx_opt_nz r n hb Hr), sb_hb_cons. destruct (H1 Hr) as (_ & _ & _ & H & _). exact H. }
  assert (P10 : Permutation (blocks L' A') (opt_hb r n hb ++ blocks (lg_L g) (lg_A g))).
  { destruct (Z.eq_dec r 0) as [Hr|Hr].
    - destruct (H0 Hr) as (_ & -> & ->). subst r. exact HP.
    - rewrite (ltx_opt_nz r n hb Hr). destruct (H1 Hr) as (_ & _ & (b1 & b2 & E1 & E2) & _).
      rewrite E1. cbn [app].
      apply Permutation_trans with ((r, n) :: b1 ++ b2); [apply Permutation_sym, Permutation_middle|].
      apply perm_skip. rewrite <- E2. exact HP. }
  assert (P11 : lkept g (opt_hb r n hb) T).
  { destruct HKT as [H|[H [H'|(f & Hf & Hin)]]]; [left; exact H | right; split; [exact H | left; exact H'] |].
    right. split; [exact H|]. right. exists f. split; [exact Hf | apply ltx_opt_incl; exact Hin]. }
  assert (P12 : mf_gi B link_mf T mem').
  { apply (lfr_gi_keep B T mem mem' HGI).
    - intros a Ha. pose proof (lfr_heads_img B API FF a Ha) as Hlf.
      exact (proj1 (lc_frame B API FF g hb T L A mem md regs K _ L' A' mem' md' HF Hsp HK
        (lcall_post_k B API K L A regs mem md _ L' A' regs' mem' md' HC) a (or_intror Hlf) (HnEi a Hlf))).
    - intros f x HT Hx.
      assert (Hin : In (f, MF_BLOCK) (blocks L A))
        by (apply (lc_T_blk B API g hb T L A mem md _ HF); rewrite HT; left; reflexivity).
      pose proof (HBK f MF_BLOCK (x - f) Hin ltac:(unfold MF_ZEROED, MF_BLOCK in *; lia)) as Hb.
      replace (f + (x - f)) with x in Hb by lia. exact Hb. }
  destruct (lfr_call B API FF g hb T L A mem md regs K (fun a => (r <= a < r + n) \/ Es a) L' A' regs' mem' md'
    (opt_hb r n hb) T HF Hsp HK HC P1 P2 P3 P4 P5 P6 P7 HRO' P9 P10 P11 P12) as (HLF & HLC & HPM).
  split; [exact HLF|]. split; [|split; [exact HPM | exact HFR]].
  intros x [Hk HnEs].
  destruct (Z_le_gt_dec r x) as [Hx1|Hx1]; [destruct (Z_lt_ge_dec x (r + n)) as [Hx2|Hx2]|].
  - exfalso. exact (proj2 (proj2 (HEB x (conj Hx1 Hx2))) Hk).
  - apply HLC. split; [exact Hk | intros [Hb|Hb]; [lia | exact (HnEs Hb)]].
  - apply HLC. split; [exact Hk | intros [Hb|Hb]; [lia | exact (HnEs Hb)]].
Qed.

End TA.
