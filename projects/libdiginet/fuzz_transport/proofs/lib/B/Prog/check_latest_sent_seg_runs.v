(* check_latest_sent_seg_runs: the shapes and the store-transport helpers the five footprint runs of the ASan
   image-B walk of check_latest_sent (fuzz_transport.asan-ubsan, entry 0x848bc, 788 bytes) share. The runs are over
   lib/B/Img0.v rsegs and lib/Lib/ExecF.v evtF:
     check_latest_sent_seg_runs_entry.v  cls_run_entry (0x848bc to the loop head 0x84974 or the epilogue 0x84b4c)
                                          and cls_run_epi (0x84b4c to the return);
     check_latest_sent_seg_runs_pre.v    cls_run_pre (the loop head to the tagged_of entry 0x846a0, the call at
                                          0x84998) and cls_run_mid (tagged_of's return 0x8499c to the bcmp entry
                                          0x42d34, the call at 0x849f0);
     check_latest_sent_seg_runs_post.v   cls_run_post (bcmp's return 0x849f4 to the next loop head or the epilogue).
   The caller-journal glue (check_latest_sent_cgW.v) joins them with the two calls of each round (tagged_of, a program
   leaf, then the bcmp wrapper). Nothing here mentions a journal.

   Each run is continuation-passing: the hypotheses are evtF at the states the run can reach, the conclusion is
   evtF at the state it starts from. A run that writes memory quantifies its continuation over the new memory and
   gives, at that memory: the frame cells, cls_mem (the world, the caller's int at dp, the body, the four
   addressable ranges and cls_wok), munch over cls_W, wmono and YK1b.mem_grows.

   The code map is the header of B/Prog/check_latest_sent_cg.v. Call targets on the pinned image
   (DgnTransportBAddr.v): tagged_of 0x846a0, the bcmp wrapper 0x42d34. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  AsanKA AsanKAProof TWorldB check_state_wake_c check_latest_sent_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_sent_seg_model.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================================================================
   1. The shapes the glue names
   ============================================================================ *)

Definition CLS_FRAME : Z := 160.

(* The constant-pool word at 0x10338 (DgnTransportBCg.v TRANS_K_SENT): 0xcccccccccccccccd, whose low 32 bits are the
   inverse of 5 modulo 2^32. The entry loads it (`ld` at 0x84954) and keeps it in the frame slot sp + 24. *)
Definition CLS_KSENT : Z := 66360.
Definition CLS_KVAL : Z := 14757395258967641293.
Definition cls_kw (m : word -> option byte) : Prop := bytes_at rsegs m CLS_KSENT (le8 (wa CLS_KVAL)).

(* The 20 eight-byte slots of the frame, from sp - 160 upwards, as the loop head holds them: slot 0 is never
   written (j0); slot 1 = (dp & 7) + 3 (0x84960); slot 2 = g_q (0x8496c); slot 3 = the constant-pool word (0x84958);
   slot 4 = g_cmd (0x84950); slot 5 = (bp <> 0) = 1 (0x84938); slot 6 = the shadow address of dp (0x8491c);
   slots 7 .. 19 = s11 .. s0, ra (0x848c0 - 0x848f0). *)
Definition cls_fr (j0 : list byte) (dp : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 j0;
   C8 (Z_to_bv 64 (dp mod 8 + 3)); C8 (Z_to_bv 64 6232192); C8 (Z_to_bv 64 CLS_KVAL);
   C8 (Z_to_bv 64 6180992); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (dp / 8 + 2147450880));
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The frame as the epilogue reads it: the low 56 bytes are whatever the run left there (on the len = 0 exit the
   slots 0 .. 5 are still the stack's junk), the 13 slots above hold the saved registers. *)
Definition cls_fr_e (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 56 j;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The machine registers at the loop head 0x84974. Fixed: sp, s0 = dp, s1 = len, s2 = bp, s7 = 0x7fff8000,
   s9 = pos, s10 = 1023, s11 = 0x5df944 (g_nq + 868). *)
Definition cls_regs_head
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 gp tp : word)
    (spv dp bp len pos : Z) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
      x10 x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 bp) x19 x20 x21 x22 (Z_to_bv 64 2147450880) x24 (Z_to_bv 64 pos)
      (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
      x28 x29 x30 x31.

(* The machine registers at the tagged_of entry 0x846a0 (the `jal` at 0x84998, return address 0x8499c):
   a0 = s5 = bp + pos, a1 = s6 = len - pos. *)
Definition cls_regs_tag
    (x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x20 x24 x28 x29 x30 x31 gp tp : word)
    (spv dp bp len pos : Z) : bvmap 5 word :=
  mkR (Z_to_bv 64 543132) (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
      (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 bp) x19 x20 (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880) x24
      (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
      x28 x29 x30 x31.

(* The machine registers at tagged_of's return 0x8499c: a0 = t (tagged_of's result), the callee-saved registers as
   cls_regs_tag left them, every other register free. *)
Definition cls_regs_tret
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x24 x28 x29 x30 x31 gp tp : word)
    (spv dp bp len pos t : Z) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
      (Z_to_bv 64 t) x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 bp) x19 x20 (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880) x24
      (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
      x28 x29 x30 x31.

(* The machine registers at the bcmp entry 0x42d34 (the `jal` at 0x849f0, return address 0x849f4):
   a0 = bp + pos, a1 = t + 12, a2 = t->len; s3 = t = g_cmd + 40 s, s4 = t->len, s8 = the shadow address of t. *)
Definition cls_regs_call (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp : word)
    (spv dp bp len pos s tl : Z) : bvmap 5 word :=
  mkR (Z_to_bv 64 543220) (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
      (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (6180992 + 40 * s + 12)) (Z_to_bv 64 tl)
      x13 x14 x15 x16 x17
      (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 tl) (Z_to_bv 64 (bp + pos))
      (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
      (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
      x28 x29 x30 x31.

(* The machine registers at the bcmp return 0x849f4: a0 = 0 (the wrapper's result), every other caller-saved
   register free, the callee-saved ones as cls_regs_call left them. *)
Definition cls_regs_post
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp : word)
    (spv dp bp len pos s tl : Z) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
      (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 tl) (Z_to_bv 64 (bp + pos))
      (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
      (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
      x28 x29 x30 x31.

(* The ranges the whole call may write: its frame, g_cmd's payload, g_q's payload, g_nq, the caller's int at dp.
   A superset of the written set; the glue narrows it with the world and the journal. *)
Definition cls_W (spv dp : Z) : list ivl :=
  [(spv, spv + 160); (6180992, 6180992 + 40960); (6232192, 6232192 + 4096);
   (6157792, 6157796); (dp, dp + 4)].

(* The body, shielded from the step tactics' hypothesis transport so that it is never silently dropped. *)
Definition cls_body (m : word -> option byte) (bp : Z) (body : list byte) : Prop :=
  bytes_at rsegs m bp body.

(* What the walk knows about the memory at every cut: the world Bc, the caller's int at dp holding v, the body,
   the four addressable ranges (g_cmd's and g_q's payloads and dp, which the instrumented checks of this code read;
   the body, which tagged_of's checks read), and the writability of everything it stores. *)
Definition cls_mem (m : word -> option byte) (Bc body : list byte) (dp bp len : Z) (v : word) : Prop :=
  tw_at TMAP_B (csw_view m) Bc /\
  rw_cells rsegs m dp [C4 v] /\
  cls_body m bp body /\
  addressable m 6180992 40960 /\
  addressable m 6232192 4096 /\
  addressable m dp 4 /\
  addressable m bp len /\
  cls_wok dp m.

(* [a, a + n) is application memory, in the form check_latest_sent_seg_kit.v cls_wrange_app takes. *)
Definition cls_app (a n : Z) : Prop :=
  (0 <= a /\ a + n <= LOWMEM_END) \/ (HIGHMEM_BEG <= a /\ a + n <= APPMEM_END).

(* The address bounds. spv is the frame's base (the entry sp minus 160). *)
Definition cls_bounds (spv dp bp len : Z) : Prop :=
  0 <= spv /\ spv + 160 <= 2 ^ 64 /\ 0 <= dp /\ dp + 4 <= 2 ^ 64 /\
  0 < bp /\ 0 <= len /\ bp + len <= 2 ^ 64 /\ dp mod 4 = 0.

(* Everything the walk needs about where the frame, dp and the body lie: the frame apart from G's hull, from the
   two runtime cells (GOT_CELL_K 0xa3cf0, CELL_K 0xac678) and from the constant-pool word (0x10338), which the entry
   reads after its first frame stores; dp apart from the pool word (read after the store at dp), from the frame and
   from every range of G; the body apart from the frame, and (when len > 0) from every byte the code stores. *)
Definition cls_off (spv dp bp len : Z) : Prop :=
  (spv + 160 <= TransportGB.G_HARNESS_B_LO \/ TransportGB.G_HARNESS_B_HI <= spv) /\
  (spv + 160 <= 670960 \/ 670968 <= spv) /\
  (spv + 160 <= 706168 \/ 706176 <= spv) /\
  (spv + 160 <= CLS_KSENT \/ CLS_KSENT + 8 <= spv) /\
  (dp + 4 <= CLS_KSENT \/ CLS_KSENT + 8 <= dp) /\
  (dp + 4 <= spv \/ spv + 160 <= dp) /\
  (bp + len <= spv \/ spv + 160 <= bp) /\
  (forall b n, In (b, n) TransportGB.G_HARNESS_B -> dp + 4 <= b \/ b + n <= dp) /\
  (0 < len -> forall s, 0 <= s < 1024 -> bp + len <= 6180992 + 40 * s \/ 6180992 + 40 * s + 4 <= bp) /\
  (0 < len -> bp + len <= 6232192 \/ 6232192 + 4096 <= bp) /\
  (0 < len -> bp + len <= 6157792 \/ 6157792 + 4 <= bp) /\
  (0 < len -> bp + len <= dp \/ dp + 4 <= bp).

(* Every range this code reads or writes, in the footprint (the body is read by tagged_of and bcmp only, not by
   this code). In the code's order: the frame; the two runtime cells that give 0x7fff8000; dp and its shadow byte;
   the constant-pool word; g_cmd's payload and its shadow; g_q's payload and its shadow; g_nq. *)
Definition cls_rng (RNG : ExecF.footprint) (spv dp : Z) : Prop :=
  ExecF.rng RNG spv 160 /\
  ExecF.rng RNG 670960 8 /\
  ExecF.rng RNG 706168 8 /\
  ExecF.rng RNG dp 4 /\
  ExecF.rng RNG (dp / 8 + 2147450880) 1 /\
  ExecF.rng RNG CLS_KSENT 8 /\
  ExecF.rng RNG 6180992 40960 /\
  ExecF.rng RNG 2148223504 5120 /\
  ExecF.rng RNG 6232192 4096 /\
  ExecF.rng RNG 2148229904 512 /\
  ExecF.rng RNG 6157792 4.

(* ============================================================================
   2. Carrying the memory facts over one store
   ============================================================================ *)

Lemma clsr_grow_write : forall (m0 m : word -> option byte) (a : word) (bs : list byte),
  mem_grows m0 m -> mem_grows m0 (write_to_mem m a bs).
Proof. intros m0 m a bs H. exact (mem_grows_trans m0 m _ H (write_to_mem_grows bs m a)). Qed.

Lemma clsr_body_write : forall (m : word -> option byte) (bp : Z) (body : list byte) (a : Z) (bs : list byte),
  cls_body m bp body -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (bp + Z.of_nat (length body) <= a \/ a + Z.of_nat (length bs) <= bp) ->
  cls_body (write_to_mem m (wa a) bs) bp body.
Proof. intros m bp body a bs H Ha Hl Hd. apply (bytes_at_write_other rsegs m a bs bp body H Ha Hl Hd). Qed.

(* An empty body holds at every memory. The one store a run makes before it learns `len <> 0` is the store at
   dp, and cls_off's body conjuncts are guarded by `0 < len`, so that store closes cls_body from this instead. *)
Lemma clsr_body_nil : forall (m m' : word -> option byte) (bp : Z) (body : list byte),
  cls_body m bp body -> length body = 0%nat -> cls_body m' bp body.
Proof.
  intros m m' bp body H Hn. destruct H as (H0 & H1 & _).
  split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite Hn in Hi. lia.
Qed.

(* A store that misses every range of G_HARNESS_B keeps the world; the hull form (the kit's cls_tw_out) is not
   available for dp, which the statement only puts outside G, not outside the hull. *)
Lemma clsr_tw_outG : forall (m : word -> option byte) (Bw : list byte) (a : Z) (bs : list byte),
  tw_at TMAP_B (csw_view m) Bw -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall b n, In (b, n) TransportGB.G_HARNESS_B -> a + Z.of_nat (length bs) <= b \/ b + n <= a) ->
  tw_at TMAP_B (csw_view (write_to_mem m (wa a) bs)) Bw.
Proof.
  intros m Bw a bs HW Ha Hl Hd.
  apply (tw_kept_GB (csw_view m) _ Bw HW).
  intros b n i Hin Hi.
  pose proof (TransportGB.G_HARNESS_B_in_hull (b, n) Hin) as Hh.
  cbn [fst snd] in Hh. unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI in Hh.
  assert (Hr : 0 <= b + i < 2 ^ 64) by lia.
  assert (E : write_to_mem m (wa a) bs (wa (b + i)) = m (wa (b + i))).
  { rewrite (write_to_mem_spec bs m a (wa (b + i))) by lia.
    rewrite (wa_unsigned (b + i) Hr).
    destruct (Z.leb_spec a (b + i)) as [H1|H1];
      destruct (Z.ltb_spec (b + i) (a + Z.of_nat (length bs))) as [H2|H2];
      cbn [andb]; try reflexivity.
    exfalso. destruct (Hd b n Hin); lia. }
  unfold csw_view, mrd. rewrite E. reflexivity.
Qed.

(* A munch of ranges that all miss every range of G_HARNESS_B keeps the world. *)
Lemma clsr_tw_munch : forall (m m' : word -> option byte) (Wq : list ivl) (Bw : list byte),
  tw_at TMAP_B (csw_view m) Bw -> munch Wq m m' ->
  (forall b n i, In (b, n) TransportGB.G_HARNESS_B -> 0 <= i < n -> outside Wq (b + i)) ->
  tw_at TMAP_B (csw_view m') Bw.
Proof.
  intros m m' Wq Bw HW MU Hd.
  apply (tw_kept_GB (csw_view m) _ Bw HW).
  intros b n i Hin Hi.
  pose proof (TransportGB.G_HARNESS_B_in_hull (b, n) Hin) as Hh.
  cbn [fst snd] in Hh. unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI in Hh.
  assert (Hr : 0 <= b + i < 2 ^ 64) by lia.
  unfold csw_view, mrd. rewrite (MU (wa (b + i))); [reflexivity|].
  rewrite (wa_unsigned (b + i) Hr). exact (Hd b n i Hin Hi).
Qed.

(* app_mem of every byte of a range that cls_app places. *)
Lemma clsr_app_byte : forall a n i, cls_app a n -> 0 <= i < n -> app_mem (a + i).
Proof.
  intros a n i H Hi. unfold cls_app, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia.
Qed.

(* the three harness ranges the walk stores into are low application memory *)
Lemma clsr_app_g : forall a, (6180992 <= a < 6180992 + 40960) \/ (6232192 <= a < 6232192 + 4096)
  \/ (6157792 <= a < 6157796) -> app_mem a.
Proof. intros a H. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia. Qed.

(* the goal `forall i, 0 <= i < Z.of_nat (length bs) -> app_mem (a + i)` of the kit's cls_addr_store *)
Ltac cls_app_tac :=
  simpl_sizes; cbn [length];
  let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi;
  first [ apply clsr_app_g; lia
        | lazymatch goal with
          | HA : cls_app ?a ?n |- app_mem (?a + ?k) =>
              replace (a + k) with (a + (k - a + a - a)) by lia; apply (clsr_app_byte a n); [exact HA | lia]
          end
        | match goal with
          | HA : cls_app ?a ?n |- _ =>
              unfold cls_app, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HA;
              unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia
          end ].

(* two words with the same low 4 bytes are the same C4 cell *)
Lemma clsr_c4_swap : forall (mm : word -> option byte) A v v', le4 v = le4 v' ->
  rw_cells rsegs mm A [C4 v] -> rw_cells rsegs mm A [C4 v'].
Proof.
  intros mm A v v' H [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes] in *. rewrite <- H. exact Hb.
  - cbn [cells_size csize] in *. exact Hw.
Qed.

(* the loop head's frame, read as the epilogue's: its low 56 bytes become one blob *)
Lemma clsr_fr_e : forall (mm : word -> option byte) (spv dp : Z) (j0 : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
  length j0 = 8%nat ->
  rw_cells rsegs mm spv (cls_fr j0 dp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  exists j, length j = 56%nat /\ rw_cells rsegs mm spv (cls_fr_e j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros mm spv dp j0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 HJ H.
  pose proof (rw_cells_merge rsegs mm spv []
    [CB 8 j0; C8 (Z_to_bv 64 (dp mod 8 + 3)); C8 (Z_to_bv 64 6232192); C8 (Z_to_bv 64 CLS_KVAL);
     C8 (Z_to_bv 64 6180992); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (dp / 8 + 2147450880))]
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] H) as M.
  exists (cells_bytes [CB 8 j0; C8 (Z_to_bv 64 (dp mod 8 + 3)); C8 (Z_to_bv 64 6232192);
                       C8 (Z_to_bv 64 CLS_KVAL); C8 (Z_to_bv 64 6180992); C8 (Z_to_bv 64 1);
                       C8 (Z_to_bv 64 (dp / 8 + 2147450880))]).
  split.
  - cbn [cells_bytes cbytes]. rewrite !length_app, HJ, !length_le8. reflexivity.
  - exact M.
Qed.
