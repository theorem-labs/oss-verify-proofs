(** reac-pw/fuzz_segconf, plain build: the kit of the pieces P4, P5, P6 of reac_segconf_parse_file
    (family F3). lib/U/Prog/pfB_kit.v is the UBSan twin, with the same names and the UBSan
    frame offsets. The build-independent part is lib/Prog/pfB_facts.v.

    The shape. Between the cut a piece enters at (memory m0) and the cut it leaves at (memory m), the piece writes
    only bytes of [pf_Wp sp c] and keeps the machine's invariants: that is [pf_mem m0 m sp lo c]. Every fact of the
    entry cut then transports to m (pf_env_mem, pf_text_mem, pf_spill_mem, pf_nm_at_mem, pf_cstr_mem), the exit
    cut's post is the entry cut's post (pf_fin_weaken, with Exec.evt_mono), and the TAIL exit's context follows
    (pf_tail_ctx). pf_mem is built at the entry by pf_mem_refl and kept by pf_mem_call at each call and by
    pf_mem_store at each store.

    pf_Wp is the write list of the pieces P4, P5, P6: the callees' frames below sp ([sp + PARSE_FILE_FRAME -
    PARSE_FILE_STACK, sp), which is where snprintf's and refuse's own lo must be instantiated, so that their munch
    stays inside it), the frame scratch the pieces P4, P5, P6 write (ntok, role / known low, model low, buf:
    [sp + 0x48, sp + 0x358)) and RC_PARSE_W c. It names neither cur_name nor the spill slots nor the saved-register
    area, which must transport unchanged, and it does NOT cover P9's CNAME site (the snprintf into cur_name at
    sp + 0x358). Measured against the plain binary's disassembly: in 0x14ebc..0x15508 (P4), 0x14ee0..0x15070 (P5)
    and 0x15074..0x154a4 (P6) every store through sp lands in that scratch range (the only `sd .., 0x48(sp)` is
    P7's ntok slot, inside it), and none of P4, P5, P6 writes cur_name, a spill slot or the save area. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfB_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require strcasecmp_c tolower_c.
Import ListNotations.
Open Scope Z_scope.

(** lia over the arithmetic hypotheses only: the cut predicates (pf_env, pf_wok, ...) in the context make lia fail
    ("No applicable tactic"), so every non-arithmetic hypothesis is cleared first. *)
Ltac pf_arith T :=
  lazymatch T with
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac | Peano.le _ _ => idtac | Peano.lt _ _ => idtac
  | ?A /\ ?B => pf_arith A; pf_arith B
  | ?A \/ ?B => pf_arith A; pf_arith B
  | not ?A => pf_arith A
  end.
Ltac pf_prune :=
  repeat match goal with
  | H : ?T |- _ => match type of T with Prop => tryif pf_arith T then fail else clear H end
  end.
Ltac pf_lia := pf_prune; lia.

(** ** The image *)
Lemma pf_rsegs_readable_b : forallb seg_readable rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_rsegs_readable : forall seg, In seg rsegs -> seg_readable seg = true.
Proof. intros seg H. exact (proj1 (forallb_forall _ _) pf_rsegs_readable_b seg H). Qed.

Lemma pf_fs_in_range : forall (sl : list Segment) z lo hi,
  forallb (fun s => (lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi)) sl = true ->
  find_segment sl z 1 <> None -> lo <= z < hi.
Proof.
  induction sl as [|sg rest IH]; intros z lo hi Hall H; cbn [find_segment] in H; [exfalso; apply H; reflexivity|].
  cbn [forallb] in Hall. apply andb_prop in Hall as [H1 H2]. apply andb_prop in H1 as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2.
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) z); cbn [andb] in H;
    [destruct (Z.leb_spec (z + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); [pf_lia|]|];
    eapply IH; eauto.
Qed.

(** The four PT_LOADs of this image cover [0x10000, 344064) and are page-aligned already. *)
Definition pf_segs_in_b : bool :=
  forallb (fun s => (65536 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 344064))
          rsegs.

Lemma pf_segs_in : pf_segs_in_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_fs_range : forall z, find_segment rsegs z 1 <> None -> 65536 <= z < 344064.
Proof. intros z H. exact (pf_fs_in_range rsegs z 65536 344064 pf_segs_in H). Qed.

(** Every address of the image's span lies in one of its reserved (page-rounded) segments. *)
Definition pf_resv_ok (lo hi : Z) : bool :=
  existsb (fun p => (bv_unsigned (fst p) <=? lo) && (hi <=? bv_unsigned (fst p) + bv_unsigned (snd p)))
          (segments_reserved rsegs).

Lemma pf_resv_of : forall lo hi z, pf_resv_ok lo hi = true -> lo <= z < hi ->
  exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) <= z < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  intros lo hi z H Hz. unfold pf_resv_ok in H. apply existsb_exists in H as (s & Hin & Hb).
  apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
  exists s. split; [exact Hin | pf_lia].
Qed.

Lemma pf_resv_b1 : pf_resv_ok 65536 77824 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pf_resv_b2 : pf_resv_ok 77824 131072 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pf_resv_b3 : pf_resv_ok 131072 139264 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pf_resv_b4 : pf_resv_ok 139264 344064 = true. Proof. vm_compute. reflexivity. Qed.

Lemma pf_resv_cover : forall z, 65536 <= z < 344064 ->
  exists s, In s (segments_reserved rsegs) /\ bv_unsigned (fst s) <= z < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  intros z Hz.
  destruct (Z_lt_ge_dec z 77824) as [A|A]; [eapply pf_resv_of; [exact pf_resv_b1 | pf_lia]|].
  destruct (Z_lt_ge_dec z 131072) as [B|B]; [eapply pf_resv_of; [exact pf_resv_b2 | pf_lia]|].
  destruct (Z_lt_ge_dec z 139264) as [C|C]; [eapply pf_resv_of; [exact pf_resv_b3 | pf_lia]|].
  eapply pf_resv_of; [exact pf_resv_b4 | pf_lia].
Qed.

(** A block no reserved segment covers: no byte of it is mapped, so none is read-only and none is an image byte. *)
Lemma pf_blk_fs : forall a n z, blk_noimg rsegs a n -> a <= z < a + n -> find_segment rsegs z 1 = None.
Proof.
  intros a n z BN Hz. destruct (find_segment rsegs z 1) as [sg|] eqn:E; [exfalso|reflexivity].
  destruct (pf_resv_cover z (pf_fs_range z ltac:(congruence))) as (s & Hin & Hb).
  apply (BN (z - a) ltac:(pf_lia) s Hin). pf_lia.
Qed.

Lemma pf_blk_ro : forall a n (x : word), blk_noimg rsegs a n -> a <= bv_unsigned x < a + n ->
  ro_addr rsegs x = false.
Proof. intros a n x BN H. unfold ro_addr. rewrite (pf_blk_fs a n _ BN H). reflexivity. Qed.

Lemma pf_blk_rom : forall a n z, blk_noimg rsegs a n -> 0 <= z < 2 ^ 64 -> a <= z < a + n ->
  seg_rom rsegs (wa z) = None.
Proof.
  intros a n z BN Hz Ha. apply (pfb_rom_none rsegs). rewrite wa_unsigned by pf_lia.
  exact (pf_blk_fs a n z BN Ha).
Qed.

Lemma pf_blk_sub : forall a n a' n', blk_noimg rsegs a n -> a <= a' -> a' + n' <= a + n -> blk_noimg rsegs a' n'.
Proof. intros a n a' n' BN H1 H2 i Hi s Hin Hc. apply (BN (a' - a + i) ltac:(pf_lia) s Hin). pf_lia. Qed.

Lemma pf_blk_apart_img : forall a n, 0 <= a -> 0 < n -> blk_noimg rsegs a n -> a + n <= 65536 \/ 344064 <= a.
Proof.
  intros a n Ha Hn BN.
  destruct (Z_le_gt_dec (a + n) 65536) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec 344064 a) as [R|R]; [exact R|exfalso].
  destruct (pf_resv_cover (Z.max a 65536) ltac:(pf_lia)) as (s & Hin & Hb).
  apply (BN (Z.max a 65536 - a) ltac:(pf_lia) s Hin). pf_lia.
Qed.

(** ** The pieces' write list, and what is true of the frame in every memory of the walk *)
(** The frame scratch the pieces write starts at the ntok slot sp + 0x48 and ends below cur_name. *)
Definition PF_SCRATCH : Z := 0x48.
(** The lo a callee of parse_file is given: the bottom of parse_file's own stack region. *)
Definition PF_LO (sp : Z) : Z := sp + PARSE_FILE_FRAME - PARSE_FILE_STACK.

Definition pf_Wp (sp c : Z) : list ivl :=
  (PF_LO sp, sp) :: (sp + PF_SCRATCH, sp + PF_NAMEBUF) :: RC_PARSE_W c.

(** What holds of this frame and this block in every memory of the walk (no memory occurs in it): the placement
    reader_pre and stack_ok give, and that every byte pf_Wp names is a task byte (MemNorm.task_mem's condition). *)
Definition pf_wok (sp lo c : Z) : Prop :=
  sa_img_end SA <= lo /\ lo + PARSE_FILE_STACK <= sp + PARSE_FILE_FRAME /\
  (sp + PARSE_FILE_FRAME) mod 16 = 0 /\ sp + PARSE_FILE_FRAME < 2 ^ 63 /\
  c <> 0 /\ 0 <= c /\ c + SEG_C_SIZE <= 2 ^ 64 /\ c mod 16 = 0 /\
  apart c SEG_C_SIZE lo (sp + PARSE_FILE_FRAME) /\ blk_noimg rsegs c SEG_C_SIZE /\
  (forall a, lo <= a < sp + PARSE_FILE_FRAME -> seg_rom rsegs (wa a) = None) /\
  (forall x : word, ~ outside (pf_Wp sp c) (bv_unsigned x) ->
     find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE).

Definition pf_mem (m0 m : word -> option byte) (sp lo c : Z) : Prop :=
  pf_wok sp lo c /\ munch (pf_Wp sp c) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  MemNorm.task_mem rsegs m /\ stk rsegs m lo (sp + PARSE_FILE_FRAME).

Lemma pf_mem_wok : forall m0 m sp lo c, pf_mem m0 m sp lo c -> pf_wok sp lo c.
Proof. intros m0 m sp lo c H. exact (proj1 H). Qed.
Lemma pf_mem_munch : forall m0 m sp lo c, pf_mem m0 m sp lo c -> munch (pf_Wp sp c) m0 m.
Proof. intros m0 m sp lo c (_ & H & _). exact H. Qed.
Lemma pf_mem_wmono : forall m0 m sp lo c, pf_mem m0 m sp lo c -> wmono rsegs m0 m.
Proof. intros m0 m sp lo c (_ & _ & H & _). exact H. Qed.
Lemma pf_mem_mi : forall m0 m sp lo c, pf_mem m0 m sp lo c -> mem_inv rsegs m.
Proof. intros m0 m sp lo c (_ & _ & _ & H & _). exact H. Qed.
Lemma pf_mem_tm : forall m0 m sp lo c, pf_mem m0 m sp lo c -> MemNorm.task_mem rsegs m.
Proof. intros m0 m sp lo c (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma pf_mem_stk : forall m0 m sp lo c, pf_mem m0 m sp lo c -> stk rsegs m lo (sp + PARSE_FILE_FRAME).
Proof. intros m0 m sp lo c (_ & _ & _ & _ & _ & H). exact H. Qed.

(** Every number the disjointness proofs need, once. (sa_img_end SEG_PLAIN = 0x536e8 = 341736, the image's top
    0x54000 = 344064, PARSE_FILE_FRAME = 0x3d0 = 976, PARSE_FILE_STACK = 0x3d0 + REFUSE_STACK = 7008.) *)
Lemma pf_wok_nums : forall sp lo c, pf_wok sp lo c ->
  341736 <= lo /\ lo + 7008 <= sp + 976 /\ 0 < c /\
  (c + 16616 <= lo \/ sp + 976 <= c) /\ (c + 16616 <= 65536 \/ 344064 <= c).
Proof.
  intros sp lo c WOK.
  pose proof WOK as (IL & DEP & _ & _ & C0 & Hc0 & _ & _ & APc & BN & _).
  assert (HS : 0 < SEG_C_SIZE) by (unfold SEG_C_SIZE; pf_lia).
  pose proof (pf_blk_apart_img c SEG_C_SIZE Hc0 HS BN) as AP. unfold SEG_C_SIZE in AP.
  assert (Hcp : 0 < c).
  { destruct (proj1 (Z.lt_eq_cases 0 c) Hc0) as [H|H];
      [exact H | exfalso; apply C0; symmetry; exact H]. }
  clear WOK C0 Hc0 BN HS.
  unfold SA, SEG_PLAIN in IL. cbn [sa_img_end] in IL.
  unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in DEP.
  unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in APc.
  split; [exact IL|]. split; [pf_lia|]. split; [exact Hcp|].
  split; [exact APc | exact AP].
Qed.

Ltac pf_goal := unfold pf_Wp, PF_LO, PF_SCRATCH, RC_PARSE_W, refusal_addr, PARSE_FILE_STACK, REFUSE_STACK,
  PRINTF_K, PARSE_FILE_FRAME, RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN,
  RC_REFUSAL_LEN, SEG_C_SIZE, RSEG_SIZE, PF_NAMEBUF, PF_SAVE, PF_BUF, PF_LOW, PF_NSLOT, apart;
  cbn [disjoint_from outside fst snd].
Ltac pf_solve := pf_goal; repeat split; first [exact I | pf_lia].

(** ** Building and keeping pf_mem *)
Lemma pf_stk_task : forall m lo hi (x : word), MemNorm.task_mem rsegs m -> stk rsegs m lo hi ->
  lo <= bv_unsigned x < hi -> find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m lo hi x TM ST Hx. destruct ST as (_ & _ & S). destruct (S _ Hx) as [_ [b Hb]].
  replace (wa (bv_unsigned x)) with x in Hb by (unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  exact (pfb_mrd_task rsegs m x b TM Hb).
Qed.

Lemma pf_c_task : forall m c rc (x : word), MemNorm.task_mem rsegs m -> rconf_at rsegs m c rc ->
  c <= bv_unsigned x < c + SEG_C_SIZE ->
  find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m c rc x TM RC Hx. destruct RC as (bs & B & E). destruct E as [L _].
  pose proof B as (Hc & Hb & H).
  specialize (H (Z.to_nat (bv_unsigned x - c)) ltac:(pf_lia)).
  rewrite Z2Nat.id in H by pf_lia.
  replace (c + (bv_unsigned x - c)) with (bv_unsigned x) in H by pf_lia.
  replace (wa (bv_unsigned x)) with x in H by (unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (nth_error bs (Z.to_nat (bv_unsigned x - c))) as [b|] eqn:Eb;
    [|apply nth_error_None in Eb; pf_lia].
  exact (pfb_mrd_task rsegs m x b TM H).
Qed.

Lemma pf_wok_of : forall m fc sp lo c v rc,
  pf_env m fc sp lo c v -> rconf_at rsegs m c rc -> pf_wok sp lo c.
Proof.
  intros m fc sp lo c v rc ENV RC.
  pose proof ENV as (C0 & C16 & APc & BN & PE & CAT & STK & MI & SV).
  destruct PE as (FRM & TM & SSP & IL & SPH). destruct STK as (ST & DEP & SP16 & NR).
  pose proof RC as (bs & B & E). destruct E as [L _]. pose proof B as (Hc & Hb & _).
  rewrite L in Hb.
  split; [exact IL|]. split; [exact DEP|]. split; [exact SP16|]. split; [exact SPH|].
  split; [exact C0|]. split; [exact Hc|]. split; [exact Hb|]. split; [exact C16|].
  split; [exact APc|]. split; [exact BN|]. split; [exact NR|].
  intros x HX. destruct (pfb_not_outside _ _ HX) as (l & h & Hin & Hr).
  assert (NUM : lo + PARSE_FILE_STACK <= sp + PARSE_FILE_FRAME) by exact DEP.
  unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in NUM.
  unfold pf_Wp, PF_LO, PF_SCRATCH, RC_PARSE_W, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME,
    PF_NAMEBUF, RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN in Hin.
  cbn [In] in Hin.
  destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]; injection Hin as E1 E2; subst l h.
  - apply (pf_stk_task m lo (sp + PARSE_FILE_FRAME) x TM ST); unfold PARSE_FILE_FRAME; pf_lia.
  - apply (pf_stk_task m lo (sp + PARSE_FILE_FRAME) x TM ST); unfold PARSE_FILE_FRAME; pf_lia.
  - apply (pf_c_task m c rc x TM RC); unfold SEG_C_SIZE; pf_lia.
  - apply (pf_c_task m c rc x TM RC); unfold SEG_C_SIZE; pf_lia.
  - apply (pf_c_task m c rc x TM RC); unfold SEG_C_SIZE; pf_lia.
Qed.

Lemma pf_mem_refl : forall m fc sp lo c v rc,
  pf_env m fc sp lo c v -> rconf_at rsegs m c rc -> pf_mem m m sp lo c.
Proof.
  intros m fc sp lo c v rc ENV RC.
  pose proof (pf_wok_of m fc sp lo c v rc ENV RC) as WOK.
  pose proof ENV as (_ & _ & _ & _ & PE & _ & STK & MI & _).
  destruct PE as (_ & TM & _). destruct STK as (ST & _).
  split; [exact WOK|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; [exact MI|]. split; [exact TM | exact ST].
Qed.

(** After a call whose write list lies inside pf_Wp. *)
Lemma pf_mem_call : forall m0 m m' sp lo c (W : list ivl),
  pf_mem m0 m sp lo c -> sub_fp W (pf_Wp sp c) ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> pf_mem m0 m' sp lo c.
Proof.
  intros m0 m m' sp lo c W (WOK & MU & WM & MI & TM & ST) SUB MU' WM' MI'.
  pose proof WOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NR & TOK).
  split; [exact WOK|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [exact SUB | exact MU']]|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact MI'|].
  split.
  - intros x b Hx. destruct (pfb_outside_dec (pf_Wp sp c) (bv_unsigned x)) as [O|O].
    + rewrite (MU' x (SUB _ O)) in Hx. exact (TM x b Hx).
    + exact (TOK x O).
  - eapply pfb_stk_wmono; [exact pf_rsegs_readable | exact NR | exact ST | exact WM'].
Qed.

(** After a store inside pf_Wp. *)
Lemma pf_mem_store : forall m0 m sp lo c a (bs : list byte),
  pf_mem m0 m sp lo c -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  inside (pf_Wp sp c) a (Z.of_nat (length bs)) ->
  store_ok rsegs m (wa a) (length bs) = true ->
  pf_mem m0 (write_to_mem m (wa a) bs) sp lo c.
Proof.
  intros m0 m sp lo c a bs (WOK & MU & WM & MI & TM & ST) Ha Hl Hin SOK.
  pose proof WOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NR & TOK).
  split; [exact WOK|].
  split; [eapply munch_write; [exact MU | pf_lia | pf_lia | exact Hin]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact SOK]|].
  split.
  - intros x b Hx. destruct (write_to_mem_some bs m (wa a) x b Hx) as [H | (i & Hi & Hx')].
    + exact (TM x b H).
    + apply TOK. rewrite Hx'. rewrite (wa_unsigned a) by pf_lia.
      rewrite wa_unsigned by pf_lia.
      eapply inside_not_outside; [exact Hin | pf_lia].
  - eapply stk_write; [exact ST | pf_lia | pf_lia].
Qed.

(** ** The exit cut's post is the entry cut's post *)
Lemma pf_sub_Wp_W : forall sp c, sub_fp (pf_Wp sp c)
  ((sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, sp + PARSE_FILE_FRAME) :: RC_PARSE_W c).
Proof.
  intros sp c. unfold sub_fp. intros x Hx. revert Hx. pf_goal. intros Hx.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; first [exact I | pf_lia].
Qed.

Lemma pf_fin_weaken : forall v sp gp tp (F F' : bvmap 5 word) m0 m lo c st ms,
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  pf_mem m0 m (bv_unsigned sp) lo c ->
  pf_fin v sp gp tp F' m lo c st ms -> pf_fin v sp gp tp F m0 lo c st ms.
Proof.
  intros v sp gp tp F F' m0 m lo c st ms HF PM H.
  pose proof (pf_mem_munch _ _ _ _ _ PM) as MU. pose proof (pf_mem_wmono _ _ _ _ _ PM) as WM.
  unfold pf_fin, pf_ret, ret_post_fp in H |- *.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F2 & fc2 & m2
    & E & FRM2 & FF2 & MU2 & WM2 & MI2 & TM2 & ST2 & Q2).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F2, fc2, m2.
  split; [exact E|]. split; [exact FRM2|].
  split; [intros k Hk; rewrite (FF2 k Hk); exact (HF k Hk)|].
  split.
  { eapply munch_trans; [eapply munch_weaken; [apply pf_sub_Wp_W | exact MU] | exact MU2]. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|].
  split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2 | exact Q2].
Qed.

(** ** Transport of the cut's facts through pf_mem *)
(** Anything of the image, below its end, is outside pf_Wp (the stack region lies above the image, and the block
    is apart from the image: pf_blk_apart_img). *)
Lemma pf_outside_img : forall sp lo c a n, pf_wok sp lo c ->
  65536 <= a -> 0 < n -> a + n <= 341736 -> disjoint_from (pf_Wp sp c) a n.
Proof.
  intros sp lo c a n WOK H1 Hn H2.
  destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & N3 & N4 & N5). pf_solve.
Qed.

Lemma pf_mrd_img : forall m0 m sp lo c a, pf_mem m0 m sp lo c ->
  65536 <= a -> a < 341736 -> m (wa a) = m0 (wa a).
Proof.
  intros m0 m sp lo c a PM H1 H2. apply (pf_mem_munch _ _ _ _ _ PM).
  rewrite wa_unsigned by pf_lia.
  apply (disjoint_outside (pf_Wp sp c) a 1 a);
    [apply (pf_outside_img sp lo c a 1 (pf_mem_wok _ _ _ _ _ PM)); pf_lia | pf_lia].
Qed.

Lemma pf_ssp_mem : forall m0 m sp lo c, ssp_ok m0 -> pf_mem m0 m sp lo c -> ssp_ok m.
Proof.
  intros m0 m sp lo c (G1 & g & G2) PM.
  pose proof (pf_mem_munch _ _ _ _ _ PM) as MU. pose proof (pf_mem_wok _ _ _ _ _ PM) as WOK.
  split; [|exists g];
    (eapply bytes_at_transport; [eassumption | exact MU |]; rewrite length_le8;
     change (Z.of_nat 8) with 8;
     eapply pf_outside_img; [exact WOK | unfold SA, SEG_PLAIN; cbn [sa_got_guard sa_guard]; pf_lia | pf_lia
                             | unfold SA, SEG_PLAIN; cbn [sa_got_guard sa_guard]; pf_lia]).
Qed.

Lemma pf_cat_mem : forall m0 m sp lo c, cat_img rsegs m0 (sa_catalogue SA) -> pf_mem m0 m sp lo c ->
  cat_img rsegs m (sa_catalogue SA).
Proof.
  intros m0 m sp lo c CAT PM a Ha.
  revert Ha. unfold SA, SEG_PLAIN; cbn [sa_catalogue]; unfold CAT_BYTES. intros Ha.
  rewrite <- (CAT a ltac:(unfold SA, SEG_PLAIN; cbn [sa_catalogue]; unfold CAT_BYTES; pf_lia)).
  unfold mrd. rewrite (pf_mrd_img m0 m sp lo c a PM ltac:(pf_lia) ltac:(pf_lia)). reflexivity.
Qed.

Lemma pf_sv_len : forall v, length (concat (map le8 (sv_list v))) = 104%nat.
Proof. intros v. rewrite pfb_concat_le8_length. reflexivity. Qed.

Lemma pf_env_mem : forall m0 m fc0 fc sp lo c v,
  pf_env m0 fc0 sp lo c v -> pf_mem m0 m sp lo c -> frm0 fc -> pf_env m fc sp lo c v.
Proof.
  intros m0 m fc0 fc sp lo c v ENV PM FC.
  pose proof ENV as (C0 & C16 & APc & BN & PE & CAT & STK & MI & SV).
  destruct PE as (_ & _ & SSP & IL & SPH). destruct STK as (_ & DEP & SP16 & NR).
  pose proof (pf_mem_munch _ _ _ _ _ PM) as MU. pose proof (pf_mem_wok _ _ _ _ _ PM) as WOK.
  destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & N3 & N4 & N5).
  split; [exact C0|]. split; [exact C16|]. split; [exact APc|]. split; [exact BN|].
  split.
  { split; [exact FC|]. split; [exact (pf_mem_tm _ _ _ _ _ PM)|].
    split; [exact (pf_ssp_mem m0 m sp lo c SSP PM)|]. split; [exact IL | exact SPH]. }
  split; [exact (pf_cat_mem m0 m sp lo c CAT PM)|].
  split; [split; [exact (pf_mem_stk _ _ _ _ _ PM)|]; split; [exact DEP|]; split; [exact SP16 | exact NR]|].
  split; [exact (pf_mem_mi _ _ _ _ _ PM)|].
  unfold saved_at in SV |- *. eapply bytes_at_transport; [exact SV | exact MU |].
  rewrite pf_sv_len. pf_solve.
Qed.

Lemma pf_text_mem : forall m0 m sp lo c t s,
  pf_text m0 sp lo c t s -> pf_mem m0 m sp lo c -> pf_text m sp lo c t s.
Proof.
  intros m0 m sp lo c t s (T0 & CS & LS & APs & APc) PM.
  pose proof (pf_mem_munch _ _ _ _ _ PM) as MU. pose proof (pf_mem_wok _ _ _ _ _ PM) as WOK.
  destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & N3 & N4 & N5).
  pose proof (pfb_cstr_span_le t s) as SPN.
  split; [exact T0|]. split; [|split; [exact LS | split; [exact APs | exact APc]]].
  eapply pfb_cstr_at_munch_span; [exact CS | exact MU |].
  revert APs APc. pf_goal. intros APs APc. repeat split; first [exact I | pf_lia].
Qed.

Lemma pf_spill_mem : forall m0 m sp lo c, pf_spill m0 sp c -> pf_mem m0 m sp lo c -> pf_spill m sp c.
Proof.
  intros m0 m sp lo c SP PM.
  pose proof (pf_mem_munch _ _ _ _ _ PM) as MU. pose proof (pf_mem_wok _ _ _ _ _ PM) as WOK.
  destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & N3 & N4 & N5).
  unfold pf_spill, saved_at in SP |- *. eapply bytes_at_transport; [exact SP | exact MU |].
  rewrite pfb_concat_le8_length. cbn [length]. change (Z.of_nat (8 * 8)) with 64. pf_solve.
Qed.

Lemma pf_nm_at_mem : forall m0 m sp lo c nm,
  pf_nm_at m0 (sp + PF_NAMEBUF) nm -> pf_mem m0 m sp lo c -> pf_nm_at m (sp + PF_NAMEBUF) nm.
Proof.
  intros m0 m sp lo c nm (f & B & E) PM.
  pose proof (pf_mem_munch _ _ _ _ _ PM) as MU. pose proof (pf_mem_wok _ _ _ _ _ PM) as WOK.
  destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & N3 & N4 & N5).
  exists f. split; [|exact E]. eapply bytes_at_transport; [exact B | exact MU |].
  destruct E as [L _]. rewrite L. change (Z.of_nat 16) with 16. pf_solve.
Qed.

(** A C string in the frame that the piece did not write. *)
Lemma pf_cstr_mem : forall m0 m sp lo c a s,
  cstr_at rsegs m0 a s -> pf_mem m0 m sp lo c -> disjoint_from (pf_Wp sp c) a (cstr_span a s) ->
  cstr_at rsegs m a s.
Proof.
  intros m0 m sp lo c a s CS PM D.
  eapply pfb_cstr_at_munch_span; [exact CS | exact (pf_mem_munch _ _ _ _ _ PM) | exact D].
Qed.

(** ** The TAIL exit *)
Lemma pf_tail_ctx : forall m0 m fc0 fc sp lo v c t s o ln d n,
  pf_ctx m0 fc0 sp lo v c t s o ln d n -> pf_mem m0 m sp lo c -> frm0 fc ->
  pf_hctx m fc sp lo v c t s (pf_next s o) (ln + 1) d /\ (length (skipn (pf_next s o) s) < n)%nat.
Proof.
  intros m0 m fc0 fc sp lo v c t s o ln d n (ENV & TX & SPL & Ho & Hn & LC) PM FC.
  destruct (L_next_holds s o Ho) as (_ & N1 & N2 & _).
  pose proof (pf_text_mem m0 m sp lo c t s TX PM) as TX'.
  rewrite length_skipn in Hn.
  split; [|rewrite length_skipn; pf_lia].
  split; [exact (pf_env_mem m0 m fc0 fc sp lo c v ENV PM FC)|].
  split; [exact TX'|].
  split; [exact (pf_spill_mem m0 m sp lo c SPL PM)|].
  split; [exact LC|].
  destruct TX' as (_ & CS & _). exact (L_cstr_skipn_holds rsegs m t s (pf_next s o) CS N2).
Qed.

(** ** The premises of a callee *)
Lemma pf_sp16 : forall sp lo c, pf_wok sp lo c -> sp mod 16 = 0.
Proof.
  intros sp lo c (_ & _ & H & _). unfold PARSE_FILE_FRAME in H.
  replace (sp + 976) with (sp + 61 * 16) in H by pf_lia. rewrite Z_mod_plus_full in H. exact H.
Qed.

Lemma pf_stk_sp : forall m0 m sp lo c, pf_mem m0 m sp lo c -> stk rsegs m lo sp.
Proof.
  intros m0 m sp lo c PM. pose proof (pf_mem_stk _ _ _ _ _ PM) as ST.
  destruct (pf_wok_nums sp lo c (pf_mem_wok _ _ _ _ _ PM)) as (N1 & N2 & _).
  assert (Hle : lo <= sp <= sp + PARSE_FILE_FRAME) by (unfold PARSE_FILE_FRAME; pf_lia).
  exact (proj1 (stk_split rsegs m lo sp (sp + PARSE_FILE_FRAME) ST Hle)).
Qed.

(** stack_ok at parse_file's sp for any callee depth K and any bottom lo' between lo and sp - K. *)
Lemma pf_stack_ok_at : forall m0 m sp lo c lo' K,
  pf_mem m0 m sp lo c -> 0 <= K -> lo <= lo' -> lo' + K <= sp -> stack_ok rsegs m lo' sp K.
Proof.
  intros m0 m sp lo c lo' K PM H0 H1 H2. pose proof (pf_mem_stk _ _ _ _ _ PM) as ST.
  pose proof (pf_mem_wok _ _ _ _ _ PM) as WOK.
  pose proof WOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NR & _).
  destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & _).
  assert (Hle : lo <= lo' <= sp + PARSE_FILE_FRAME) by (unfold PARSE_FILE_FRAME; pf_lia).
  destruct (stk_split rsegs m lo lo' (sp + PARSE_FILE_FRAME) ST Hle) as [_ ST1].
  assert (Hle2 : lo' <= sp <= sp + PARSE_FILE_FRAME) by (unfold PARSE_FILE_FRAME; pf_lia).
  destruct (stk_split rsegs m lo' sp (sp + PARSE_FILE_FRAME) ST1 Hle2) as [ST2 _].
  split; [exact ST2|]. split; [pf_lia|]. split; [exact (pf_sp16 sp lo c WOK)|].
  intros a Ha. apply NR. unfold PARSE_FILE_FRAME. pf_lia.
Qed.

(** The bottom a callee that prints is given: parse_file's own stack bottom, so that its munch stays in pf_Wp. *)
Lemma pf_lo_callee : forall sp lo c, pf_wok sp lo c ->
  lo <= PF_LO sp /\ PF_LO sp = sp - 6032 /\ 341736 <= PF_LO sp.
Proof.
  intros sp lo c WOK. destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & _).
  unfold PF_LO, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME. repeat split; pf_lia.
Qed.

Lemma pf_printf_env_weaken : forall m fc lo hi lo' hi',
  printf_env m fc lo hi -> lo <= lo' -> hi' <= hi -> printf_env m fc lo' hi'.
Proof.
  intros m fc lo hi lo' hi' (A & B & C & D & E) H1 H2.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [pf_lia | pf_lia].
Qed.

(** ** The c block is writable *)
Lemma pf_c_wr : forall m sp lo c rc, pf_wok sp lo c -> rconf_at rsegs m c rc -> wr_at rsegs m c SEG_C_SIZE.
Proof.
  intros m sp lo c rc WOK (bs & B & E). pose proof WOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BN & _).
  destruct E as [L _]. pose proof B as (Hc & Hb & H). rewrite L in Hb.
  split; [pf_lia|]. split; [pf_lia|]. intros j Hj.
  specialize (H (Z.to_nat j) ltac:(pf_lia)). rewrite Z2Nat.id in H by pf_lia.
  destruct (nth_error bs (Z.to_nat j)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; pf_lia].
  unfold wview. destruct (m (wa (c + j))) as [b'|] eqn:Em; [discriminate|].
  unfold mrd in H. rewrite Em in H.
  rewrite (pf_blk_rom c SEG_C_SIZE (c + j) BN ltac:(pf_lia) ltac:(pf_lia)) in H. discriminate.
Qed.

Lemma pf_c_store_ok : forall m sp lo c rc a (n : nat), pf_wok sp lo c -> rconf_at rsegs m c rc ->
  c <= a -> a + Z.of_nat n <= c + SEG_C_SIZE -> store_ok rsegs m (wa a) n = true.
Proof.
  intros m sp lo c rc a n WOK RC H1 H2.
  pose proof (pf_c_wr m sp lo c rc WOK RC) as WR.
  replace a with (c + (a - c)) by pf_lia. eapply wr_at_store_ok; [exact WR | pf_lia | pf_lia].
Qed.

(** A store into parse_file's frame. *)
Lemma pf_frame_store_ok : forall m0 m sp lo c a (n : nat), pf_mem m0 m sp lo c ->
  lo <= a -> a + Z.of_nat n <= sp + PARSE_FILE_FRAME -> store_ok rsegs m (wa a) n = true.
Proof.
  intros m0 m sp lo c a n PM H1 H2.
  eapply pfb_stk_store_ok; [exact (pf_mem_stk _ _ _ _ _ PM) | exact H1 | exact H2].
Qed.

(** ** The refusal formats in .rodata *)
Definition PF_STR_NONAME : Z := 0x10441.    (* F_noname *)
Definition PF_STR_TOOLONG : Z := 0x102a9.   (* F_toolong *)
Definition PF_STR_BOUND : Z := 0x10817.     (* F_bound *)
Definition PF_STR_TWICE : Z := 0x105aa.     (* F_twice *)
Definition PF_STR_BADMODEL : Z := 0x104e3.  (* F_badmodel *)

(** Every (format, address) pair reac_segconf_parse_file passes to refuse. *)
Definition PF_FMTS : list (list Z * Z) :=
  [(F_long, PF_STR_LONG); (F_notclosed, PF_STR_NOTCLOSED); (F_after, PF_STR_AFTER); (F_unknown, PF_STR_UNKNOWN);
   (F_noname, PF_STR_NONAME); (F_toolong, PF_STR_TOOLONG); (F_bound, PF_STR_BOUND); (F_twice, PF_STR_TWICE);
   (F_neither, PF_STR_NEITHER); (F_outside, PF_STR_OUTSIDE); (F_badrole, PF_STR_BADROLE);
   (F_badignore, PF_STR_BADIGNORE); (F_knock, PF_STR_KNOCK); (F_badmodel, PF_STR_BADMODEL);
   (F_nokey, PF_STR_NOKEY)].

Definition pf_fmt_ok_b (p : list Z * Z) : bool :=
  ro_bytes_b rsegs (snd p) (zb (fst p) ++ [ZERO]) &&
  negb (existsb (Z.eqb 0) (fst p)) &&
  (RO_LO <=? snd p) && (snd p + Z.of_nat (length (fst p)) + 1 <=? sa_ro_end SA) &&
  forallb (fun x => (0 <=? x) && (x <? 256)) (fst p).

Lemma pf_fmts_ok : forallb pf_fmt_ok_b PF_FMTS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_zs_zb : forall l, forallb (fun x => (0 <=? x) && (x <? 256)) l = true -> zs (zb l) = l.
Proof.
  intros l H. apply pfb_zs_zb_range. apply Forall_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) H x Hx) as Hb.
  apply andb_prop in Hb as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. pf_lia.
Qed.

Lemma pf_nz_of_existsb : forall l, existsb (Z.eqb 0) l = false -> ~ In 0 l.
Proof.
  intros l H Hin.
  assert (E : existsb (Z.eqb 0) l = true)
    by (apply existsb_exists; exists 0; split; [exact Hin | reflexivity]).
  congruence.
Qed.

Lemma pf_fmt_at : forall m f fp, mem_inv rsegs m -> In (f, fp) PF_FMTS ->
  cstrz_at rsegs m fp f /\ fp <> 0 /\ RO_LO <= fp /\ fp + Z.of_nat (length f) + 1 <= sa_ro_end SA.
Proof.
  intros m f fp MI Hin.
  pose proof (proj1 (forallb_forall _ _) pf_fmts_ok (f, fp) Hin) as H.
  unfold pf_fmt_ok_b in H. cbn [fst snd] in H.
  apply andb_prop in H as [H HR]. apply andb_prop in H as [H HE].
  apply andb_prop in H as [H HL]. apply andb_prop in H as [HB HZ].
  apply Z.leb_le in HL. apply Z.leb_le in HE. apply negb_true_iff in HZ.
  assert (HS : zs (zb f) = f) by (apply pf_zs_zb; exact HR).
  split; [|split; [unfold RO_LO in HL; pf_lia | split; [exact HL | exact HE]]].
  exists (zb f). split.
  - apply ro_bytes_at; [exact MI | unfold RO_LO in HL; pf_lia
                        | unfold zb; rewrite length_app, length_map; cbn [length];
                          unfold SA, SEG_PLAIN in HE; cbn [sa_ro_end] in HE; pf_lia |].
    apply ro_bytes_b_sound. exact HB.
  - split; [exact HS | apply pf_nz_of_existsb; exact HZ].
Qed.

Ltac pf_in_fmts := unfold REFUSE_FORMATS; cbn [In]; repeat first [ left; reflexivity | right ].

Lemma pf_fmt_refuse : forall f fp, In (f, fp) PF_FMTS -> In f REFUSE_FORMATS.
Proof.
  intros f fp Hin. unfold PF_FMTS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as E1 E2; subst f; pf_in_fmts|]). destruct Hin.
Qed.

(** ** refuse's premise at a call site of the pieces P4, P5, P6 *)
Definition pf_vaW (sp c : Z) (rc : rconf) : list ivl :=
  [(PF_LO sp, sp);
   (refusal_addr c (length (rc_refusal rc)), refusal_addr c (length (rc_refusal rc)) + RC_REFUSAL_LEN);
   (c + RC_REFUSED, c + RC_REFUSED + 4)].

(** The nat numeral 65535 is not unary (Nat.of_num_uint), so lia cannot read it. *)
Lemma pf_le_65535 : forall n : nat, (n <= 2000)%nat -> (n <= 65535)%nat.
Proof. intros n H. apply Nat.le_trans with 2000%nat; [exact H | apply Nat.leb_le; vm_compute; reflexivity]. Qed.

(** A string argument that lies in parse_file's own frame (buf, cur_name, known, low). *)
Lemma pf_va_frame : forall m sp lo c rc (r : word) (s : list Z),
  pf_wok sp lo c -> (length (rc_refusal rc) <= 8)%nat -> cstr_at rsegs m (bv_unsigned r) s ->
  sp <= bv_unsigned r -> bv_unsigned r + Z.of_nat (length s) + 8 <= sp + PARSE_FILE_FRAME ->
  va_arg_ok rsegs m (pf_vaW sp c rc) r (AS s).
Proof.
  intros m sp lo c rc r s WOK Hk CS H1 H2.
  destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & N3 & N4 & N5).
  assert (Hr8 : Z.of_nat (length (rc_refusal rc)) <= 8) by pf_lia.
  revert H2. unfold PARSE_FILE_FRAME. intros H2.
  cbn [va_arg_ok]. split; [pf_lia|].
  split; [exact CS|].
  split; [apply pf_le_65535; pf_lia|].
  unfold apart_all, pf_vaW, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_REFUSED, PF_LO,
    PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME, RSEG_SIZE.
  repeat (apply Forall_cons; [unfold apart; cbn [fst snd]; pf_lia|]). apply Forall_nil.
Qed.

Lemma pf_refuse_pre : forall m0 m fc sp lo c v rc ln f fp k (va : list word) (args : list arg),
  pf_env m0 fc sp lo c v -> pf_mem m0 m sp lo c -> frm0 fc ->
  rconf_at rsegs m c rc -> pf_cnt rc k ->
  0 <= ln < 2 ^ 31 -> In (f, fp) PF_FMTS -> conv_kinds f = map arg_is_s args ->
  va_args_ok rsegs m (pf_vaW sp c rc) va args ->
  refuse_pre m fc sp (PF_LO sp) c ln fp va rc ln f args.
Proof.
  intros m0 m fc sp lo c v rc ln f fp k va args ENV PM FC RC CNT HLN HIN HK HVA.
  pose proof (pf_env_mem m0 m fc fc sp lo c v ENV PM FC) as ENV'.
  pose proof ENV' as (C0 & C16 & APc & BN & PE & _ & _ & MI & _).
  pose proof (pf_mem_wok _ _ _ _ _ PM) as WOK.
  destruct (pf_wok_nums sp lo c WOK) as (N1 & N2 & N3 & N4 & N5).
  destruct (pf_fmt_at m f fp MI HIN) as (FA & FNZ & FLO & FHI).
  destruct CNT as [CNT1 _].
  change (2 ^ 16) with 65536 in CNT1. change (2 ^ 32) with 4294967296 in CNT1.
  assert (CNT2 : rc_refused rc + 1 < 2 ^ 32).
  { change (2 ^ 32) with 4294967296. pose proof (Nat2Z.is_nonneg k). pf_lia. }
  unfold refuse_pre.
  split; [exact C0|]. split; [exact C16|]. split; [exact RC|].
  split; [unfold apart, PF_LO, SEG_C_SIZE, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME; pf_lia|].
  split; [exact BN|].
  split; [exact CNT2|]. split; [exact HLN|]. split; [reflexivity|].
  split; [exact (pf_fmt_refuse f fp HIN)|]. split; [exact HK|].
  split; [exact FNZ|]. split; [exact FA|]. split; [exact FLO|]. split; [exact FHI|].
  split; [exact HVA|].
  split.
  { eapply pf_printf_env_weaken; [exact PE | |];
      unfold PF_LO, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME; pf_lia. }
  split; [|exact MI].
  eapply pf_stack_ok_at; [exact PM | | |];
    unfold PF_LO, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME; pf_lia.
Qed.

(** ** strcasecmp's zero test (strcasecmp_c.v) in the spine's terms *)
Lemma pf_zlower_tolower : forall z, 0 <= z < 256 -> tolower_c.zlower z = SegModel.tolower z.
Proof.
  intros z Hz.
  assert (H : forallb (fun y => Z.eqb (tolower_c.zlower y) (SegModel.tolower y)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat z).
  split; [lia | apply in_seq; lia].
Qed.

Lemma pf_lower_eq_bridge : forall l w, Forall (fun x => 0 <= x < 256) l -> Forall (fun x => 0 <= x < 256) w ->
  ~ In 0 l -> ~ In 0 w ->
  (strcasecmp_c.lower_eq (zb l) (zb w) <-> SegModel.strcasecmp l w = 0).
Proof.
  intros l w Rl Rw Nl Nw. unfold strcasecmp_c.lower_eq.
  change (map bv_unsigned (zb l)) with (zs (zb l)). change (map bv_unsigned (zb w)) with (zs (zb w)).
  rewrite (pfb_zs_zb_range l Rl), (pfb_zs_zb_range w Rw).
  assert (El : map tolower_c.zlower l = map SegModel.tolower l).
  { apply map_ext_in. intros x Hx. apply pf_zlower_tolower. rewrite Forall_forall in Rl. exact (Rl x Hx). }
  assert (Ew : map tolower_c.zlower w = map SegModel.tolower w).
  { apply map_ext_in. intros x Hx. apply pf_zlower_tolower. rewrite Forall_forall in Rw. exact (Rw x Hx). }
  rewrite El, Ew. exact (pfb_strcasecmp_map l w Nl Nw).
Qed.

(** ** The other .rodata strings parse_file passes: printf's formats, the strspn set, the keys and words it gives
    strcasecmp / strncasecmp / bcmp (the same addresses in both images) *)
Definition PF_STR_SS : Z := 0x1031b.       (* F_ss "%s%s" *)
Definition PF_STR_BAR : Z := 0x105f0.      (* "|" *)
Definition PF_STR_EMPTY : Z := 0x1038e.    (* "" *)
Definition PF_STR_SEGMENT : Z := 0x10313.
Definition PF_STR_ROLE : Z := 0x10298.
Definition PF_STR_MODEL : Z := 0x10811.
Definition PF_STR_IGNORE : Z := 0x1054f.
Definition PF_STR_KNOCKW : Z := 0x102a3.   (* "knock", the key *)
Definition PF_STR_YES : Z := 0x1042f.
Definition PF_STR_TRUE : Z := 0x10517.
Definition PF_STR_NO : Z := 0x10711.
Definition PF_STR_FALSE : Z := 0x1029d.
Definition PF_STR_AUTO : Z := 0x1030e.
Definition PF_STR_MASTER : Z := 0x10548.
Definition PF_STR_SLAVE : Z := 0x1075c.

Definition PF_RO : list (list Z * Z) :=
  [(F_s, PF_STR_S); (F_ss, PF_STR_SS); ([124], PF_STR_BAR); ([], PF_STR_EMPTY); ([32; 9; 13], PF_STR_BLANKS);
   (S_base, STR_BASE); (S_segment, PF_STR_SEGMENT); (S_role, PF_STR_ROLE); (S_model, PF_STR_MODEL);
   (S_ignore, PF_STR_IGNORE); (S_knock, PF_STR_KNOCKW); (S_yes, PF_STR_YES); (S_true, PF_STR_TRUE);
   (S_no, PF_STR_NO); (S_false, PF_STR_FALSE); (S_auto, PF_STR_AUTO); (S_master, PF_STR_MASTER);
   (S_slave, PF_STR_SLAVE)].

Lemma pf_ro_ok : forallb pf_fmt_ok_b PF_RO = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_tab_at : forall tab, forallb pf_fmt_ok_b tab = true -> forall m s a, mem_inv rsegs m -> In (s, a) tab ->
  cstrz_at rsegs m a s /\ a <> 0 /\ RO_LO <= a /\ a + Z.of_nat (length s) + 1 <= sa_ro_end SA.
Proof.
  intros tab OK m s a MI Hin.
  pose proof (proj1 (forallb_forall _ _) OK (s, a) Hin) as H.
  unfold pf_fmt_ok_b in H. cbn [fst snd] in H.
  apply andb_prop in H as [H HR]. apply andb_prop in H as [H HE].
  apply andb_prop in H as [H HL]. apply andb_prop in H as [HB HZ].
  apply Z.leb_le in HL. apply Z.leb_le in HE. apply negb_true_iff in HZ.
  assert (HS : zs (zb s) = s) by (apply pf_zs_zb; exact HR).
  split; [|split; [unfold RO_LO in HL; lia | split; [exact HL | exact HE]]].
  exists (zb s). split.
  - apply ro_bytes_at; [exact MI | unfold RO_LO in HL; lia
                        | unfold zb; rewrite length_app, length_map; cbn [length];
                          unfold SA, SEG_PLAIN in HE; cbn [sa_ro_end] in HE; lia |].
    apply ro_bytes_b_sound. exact HB.
  - split; [exact HS | apply pf_nz_of_existsb; exact HZ].
Qed.

Lemma pf_ro_at : forall m s a, mem_inv rsegs m -> In (s, a) PF_RO ->
  cstrz_at rsegs m a s /\ a <> 0 /\ RO_LO <= a /\ a + Z.of_nat (length s) + 1 <= sa_ro_end SA.
Proof. exact (pf_tab_at PF_RO pf_ro_ok). Qed.

(** ** Every callee's stack premise at a call in P4, P5, P6, for a depth K up to refuse's: strchr 32, strncasecmp 48,
    strcasecmp 32, trim TRIM_STACK, refuse REFUSE_STACK, snprintf SNPRINTF_K (5936 <= REFUSE_STACK = 6032). The
    bottom given to a callee that prints is PF_LO sp, so that its munch stays inside pf_Wp. *)
Lemma pf_callee_depth : forall m0 m sp lo c K, pf_mem m0 m sp lo c -> K <= REFUSE_STACK ->
  stk rsegs m lo sp /\ stk rsegs m (PF_LO sp) sp /\ lo <= sp - K /\ PF_LO sp <= sp - K /\
  sa_img_end SA <= PF_LO sp /\ sp < 2 ^ 63.
Proof.
  intros m0 m sp lo c K PM HK.
  pose proof (pf_mem_wok _ _ _ _ _ PM) as WOK. pose proof WOK as (IL & _ & _ & SPH & _).
  destruct (pf_lo_callee sp lo c WOK) as (L1 & L2 & L3).
  pose proof (pf_stk_sp m0 m sp lo c PM) as ST.
  unfold REFUSE_STACK, PRINTF_K in HK. unfold PARSE_FILE_FRAME in SPH.
  assert (Hle : lo <= PF_LO sp <= sp) by lia.
  destruct (stk_split rsegs m lo (PF_LO sp) sp ST Hle) as [_ ST2].
  split; [exact ST|]. split; [exact ST2|]. split; [lia|]. split; [lia|].
  split; [lia | lia].
Qed.

(** A sub-block of c is free of the image (printf_facts_c.pf_img_free is this Prop for the printf destination). *)
Lemma pf_c_img_free : forall sp lo c off n, pf_wok sp lo c -> 0 <= off -> off + n <= SEG_C_SIZE ->
  blk_noimg rsegs (c + off) n.
Proof.
  intros sp lo c off n WOK H1 H2. pose proof WOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BN & _).
  eapply pf_blk_sub; [exact BN | lia | lia].
Qed.
