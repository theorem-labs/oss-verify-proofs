(* check_latest_sent_seg_runs: the ASan image-A machine walk of check_latest_sent (fuzz_transport.asan, entry
   0x84500, 836 bytes), cut into four footprint runs over lib/A/Img0.v rsegs and lib/Lib/ExecF.v evtF. The
   caller-journal glue (A/Prog/check_latest_sent_cgW.v) joins them: cls_run_entry (0x84500 to the loop head or
   the epilogue), cls_run_pre (the loop head to the bcmp entry), cls_run_post (the bcmp return to the next loop
   head or the epilogue) and cls_run_epi (the epilogue to the return). Nothing here mentions a journal.

   Each run is continuation-passing: the hypotheses are evtF at the states the run can reach, the conclusion is
   evtF at the state it starts from. A run that writes memory quantifies its continuation over the new memory and
   gives, at that memory: the frame cells, the stack below the frame, cls_mem (the world, the caller's int at dp,
   the body, the four addressable ranges and cls_wok), munch over cls_W, wmono and YK1b.mem_grows.

   The code map is the header of A/Prog/check_latest_sent_cg.v. The call target of the bcmp wrapper on the pinned
   image is 0x42cf8 (the neutral disassembly of an earlier build says 0x42cf0). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  AsanKA AsanKAProof TWorldG TWorldA check_state_wake_c check_latest_sent_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_latest_sent_seg_model.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================================================================
   1. The shapes the glue names
   ============================================================================ *)

Definition CLS_FRAME : Z := 144.

(* The 18 eight-byte slots of the frame, from sp - 144 upwards, as the loop head holds them: slot 0 is never
   written (j0); slot 1 = (dp & 7) + 3 (0x8458c); slot 2 = g_q (0x84598); slot 3 = the shadow address of dp
   (0x84554); slot 4 = bp (0x8455c); slots 5 .. 17 = s11 .. s0, ra (0x84504 - 0x84534). *)
Definition cls_fr (j0 : list byte) (dp bp : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 j0;
   C8 (Z_to_bv 64 (dp mod 8 + 3)); C8 (Z_to_bv 64 6233088); C8 (Z_to_bv 64 (dp / 8 + 2147450880));
   C8 (Z_to_bv 64 bp);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The frame as the epilogue reads it: the low 40 bytes are whatever the run left there (on the len = 0 exit the
   slots 1 and 2 are still the stack's junk), the 13 slots above hold the saved registers. *)
Definition cls_fr_e (j : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 40 j;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The machine registers at the loop head 0x8459c. Fixed: sp, s0 = dp, s1 = len, s5 = 0x7fff8000,
   s7 = pos, s8 = 0x5df570 (g_nq - 1008), s9 = the running g_nq, s10 = g_cmd, s11 = 0x5df574 (g_ncmd - 1036). *)
Definition cls_regs_head
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 gp tp : word)
    (spv dp len pos nqv : Z) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
      x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 pos)
      (Z_to_bv 64 6157680) (Z_to_bv 64 nqv) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
      x28 x29 x30 x31.

(* The machine registers at the bcmp entry 0x42cf8 (the `jal` at 0x84658, return address 0x8465c). a3 and a4 hold
   the leftovers of the instrumented check of t + 36 and differ between its two paths, so they are free. *)
Definition cls_regs_call (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp : word)
    (spv dp bp len pos nqv s tl : Z) : bvmap 5 word :=
  mkR (Z_to_bv 64 542300) (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
      (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (6181888 + 40 * s + 12)) (Z_to_bv 64 tl)
      x13 x14 x15 x16 x17
      (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 tl) (Z_to_bv 64 2147450880)
      (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
      (Z_to_bv 64 6157680) (Z_to_bv 64 nqv) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
      x28 x29 x30 x31.

(* The machine registers at the bcmp return 0x8465c: a0 = 0 (the wrapper's result), every other caller-saved
   register free, the callee-saved ones as cls_regs_call left them. *)
Definition cls_regs_post
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp : word)
    (spv dp len pos nqv s tl : Z) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
      (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
      (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 tl) (Z_to_bv 64 2147450880)
      (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
      (Z_to_bv 64 6157680) (Z_to_bv 64 nqv) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
      x28 x29 x30 x31.

(* The ranges the whole call may write: its frame, g_cmd's payload, g_q's payload, g_nq, the caller's int at dp.
   A superset of the written set; the glue narrows it with the world and the journal. *)
Definition cls_W (spv dp : Z) : list ivl :=
  [(spv, spv + 144); (6181888, 6181888 + 40960); (6233088, 6233088 + 4096);
   (6158688, 6158692); (dp, dp + 4)].

(* The body, shielded from the step tactics' hypothesis transport so that it is never silently dropped. *)
Definition cls_body (m : word -> option byte) (bp : Z) (body : list byte) : Prop :=
  bytes_at rsegs m bp body.

(* What the walk knows about the memory at every cut: the world Bc, the caller's int at dp holding v, the body,
   the four addressable ranges the instrumented checks read, and the writability of everything it stores. *)
Definition cls_mem (m : word -> option byte) (Bc body : list byte) (dp bp len : Z) (v : word) : Prop :=
  tw_at TMAP_A (csw_view m) Bc /\
  rw_cells rsegs m dp [C4 v] /\
  cls_body m bp body /\
  addressable m 6181888 40960 /\
  addressable m 6233088 4096 /\
  addressable m dp 4 /\
  addressable m bp len /\
  cls_wok dp m.

(* [a, a + n) is application memory, in the form check_latest_sent_seg_kit.v cls_wrange_app takes. *)
Definition cls_app (a n : Z) : Prop :=
  (0 <= a /\ a + n <= LOWMEM_END) \/ (HIGHMEM_BEG <= a /\ a + n <= APPMEM_END).

(* The address bounds. spv is the frame's base (the entry sp minus 144). *)
Definition cls_bounds (spv dp bp len : Z) : Prop :=
  0 <= spv /\ spv + 144 <= 2 ^ 64 /\ 0 <= dp /\ dp + 4 <= 2 ^ 64 /\
  0 < bp /\ 0 <= len /\ bp + len <= 2 ^ 64 /\ dp mod 4 = 0.

(* Everything the walk needs about where the frame, dp and the body lie. The glue gets the first three from
   decode_off_win and the runtime cells' off_stk, the fourth from `forall x, dp <= x < dp + 4 -> ~ inG G_HARNESS x`,
   and the last four from `forall x, bp <= x < bp + len -> ~ cls_wr dp x`: each store's range and the body are
   intervals, so pointwise disjointness is interval disjointness WHENEVER len > 0, which is why those four
   carry the guard `0 < len ->`. An empty body meets nothing, and the only store before the walk learns
   `len <> 0` is the one at dp, which a run closes from `length body = 0%nat` instead. *)
Definition cls_off (spv dp bp len : Z) : Prop :=
  (spv + 144 <= TransportG.G_HARNESS_LO \/ TransportG.G_HARNESS_HI <= spv) /\
  (spv + 144 <= 671888 \/ 671896 <= spv) /\
  (spv + 144 <= 707064 \/ 707072 <= spv) /\
  (dp + 4 <= spv \/ spv + 144 <= dp) /\
  (bp + len <= spv \/ spv + 144 <= bp) /\
  (forall b n, In (b, n) TransportG.G_HARNESS -> dp + 4 <= b \/ b + n <= dp) /\
  (0 < len -> forall s, 0 <= s < 1024 -> bp + len <= 6181888 + 40 * s \/ 6181888 + 40 * s + 4 <= bp) /\
  (0 < len -> bp + len <= 6233088 \/ 6233088 + 4096 <= bp) /\
  (0 < len -> bp + len <= 6158688 \/ 6158688 + 4 <= bp) /\
  (0 < len -> bp + len <= dp \/ dp + 4 <= bp).

(* Every range the code reads or writes, in the footprint. In the code's order: the frame; the two runtime cells
   that give 0x7fff8000; dp and its shadow byte; the body and its shadow bytes; g_cmd's payload and its shadow;
   g_q's payload and its shadow; g_nq; g_ncmd. *)
Definition cls_rng (RNG : ExecF.footprint) (spv dp bp len : Z) : Prop :=
  ExecF.rng RNG spv 144 /\
  ExecF.rng RNG 671888 8 /\
  ExecF.rng RNG 707064 8 /\
  ExecF.rng RNG dp 4 /\
  ExecF.rng RNG (dp / 8 + 2147450880) 1 /\
  ExecF.rng RNG bp len /\
  (forall o, 0 <= o < len -> ExecF.rng RNG ((bp + o) / 8 + 2147450880) 1) /\
  ExecF.rng RNG 6181888 40960 /\
  ExecF.rng RNG 2148223616 5120 /\
  ExecF.rng RNG 6233088 4096 /\
  ExecF.rng RNG 2148230016 512 /\
  ExecF.rng RNG 6158688 4 /\
  ExecF.rng RNG 6158720 4.

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

(* A store that misses every range of G_HARNESS keeps the world; the hull form (the kit's cls_tw_out) is not
   available for dp, which the statement only puts outside G, not outside the hull. *)
Lemma clsr_tw_outG : forall (m : word -> option byte) (Bw : list byte) (a : Z) (bs : list byte),
  tw_at TMAP_A (csw_view m) Bw -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall b n, In (b, n) TransportG.G_HARNESS -> a + Z.of_nat (length bs) <= b \/ b + n <= a) ->
  tw_at TMAP_A (csw_view (write_to_mem m (wa a) bs)) Bw.
Proof.
  intros m Bw a bs HW Ha Hl Hd.
  apply (tw_kept_GA (csw_view m) _ Bw HW).
  intros b n i Hin Hi.
  pose proof (TransportG.G_HARNESS_in_hull (b, n) Hin) as Hh.
  cbn [fst snd] in Hh. unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in Hh.
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

(* app_mem of every byte of a range that cls_app places. *)
Lemma clsr_app_byte : forall a n i, cls_app a n -> 0 <= i < n -> app_mem (a + i).
Proof.
  intros a n i H Hi. unfold cls_app, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia.
Qed.

(* the three harness ranges the walk stores into are low application memory *)
Lemma clsr_app_g : forall a, (6181888 <= a < 6181888 + 40960) \/ (6233088 <= a < 6233088 + 4096)
  \/ (6158688 <= a < 6158692) -> app_mem a.
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

(* The step tactics' hypothesis transport, extended with the facts this walk carries: cls_body, cls_wok,
   addressable and mem_grows. Tac.v states footprint_after_store as a plain Ltac, so it can be redefined; the
   redefinition is Local, so a file that Requires this one keeps the library's own transport. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU;
              [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | MG : mem_grows ?mq m |- _ => apply (clsr_grow_write mq m (wa a) bs) in MG
  | HK : cls_wok ?d m |- _ => apply (cls_wok_write d m (wa a) bs) in HK
  | HB : cls_body m ?p ?bsy |- _ =>
      first [ apply (clsr_body_write m p bsy a bs) in HB; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | fail 100 "store meets the body:" a ]
  | HA : addressable m ?p ?n |- _ =>
      first [ apply (cls_addr_store m p n a bs) in HA; [ | lia | simpl_sizes; slia | cls_app_tac ]
            | fail 100 "store not in application memory:" a ]
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* ============================================================================
   3. The four runs
   ============================================================================ *)

(* ---- the epilogue, 0x847b0 .. 0x847e8 ---- *)
Lemma cls_run_epi : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (spv : Z) (j : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 : word)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  0 <= spv -> spv + 144 <= 2 ^ 64 ->
  rw_cells rsegs m spv (cls_fr_e j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  ExecF.rng RNG spv 144 ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 (spv + 144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m (seg_rom rsegs)) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR y1 (Z_to_bv 64 spv) gp tp t0 t1 t2 y8 y9 a0 a1 a2 a3 a4 a5 a6 a7
              y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6)
        F (Z_to_bv 64 542640) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc spv j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
    gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 H0 H1 FR RG K.
  unfold cls_fr_e in FR.
  do 13 step.
  step.
  try rewrite (unsigned_lit spv) by lia.
  step.
  exact K.
Qed.

(* ---- the entry, 0x84500 .. 0x84598 ---- *)
(* The world over the entry's stores: they all fall in the frame or in dp, and neither meets a range of
   G_HARNESS, so tw_at holds at every memory the run reaches, with the same Bw. *)
Lemma clsr_entry_kept : forall (m m' : word -> option byte) (spv dp : Z) (Bw : list byte),
  tw_at TMAP_A (csw_view m) Bw ->
  munch [(spv, spv + 144); (dp, dp + 4)] m m' ->
  (spv + 144 <= TransportG.G_HARNESS_LO \/ TransportG.G_HARNESS_HI <= spv) ->
  (forall b n, In (b, n) TransportG.G_HARNESS -> dp + 4 <= b \/ b + n <= dp) ->
  tw_at TMAP_A (csw_view m') Bw.
Proof.
  intros m m' spv dp Bw HW MU OG ODG.
  apply (tw_kept_GA (csw_view m) _ Bw HW).
  intros b n i Hin Hi.
  pose proof (TransportG.G_HARNESS_in_hull (b, n) Hin) as Hh.
  cbn [fst snd] in Hh. unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in Hh, OG.
  assert (Hr : 0 <= b + i < 2 ^ 64) by lia.
  unfold csw_view, mrd. rewrite (MU (wa (b + i))); [reflexivity|].
  rewrite (wa_unsigned (b + i) Hr). cbn [outside].
  destruct (ODG b n Hin) as [D|D]; (split; [lia | split; [lia | exact I]]).
Qed.

(* `beqz` of an unsigned 64-bit value *)
Lemma clsr_entry_eqb0 : forall v, 0 <= v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma cls_run_entry : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (lo sp0 bp len dp : Z) (Bw body : list byte) (v0 : word)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  cls_bounds (sp0 - 144) dp bp len -> cls_app (sp0 - 144) 144 -> cls_app dp 4 ->
  cls_off (sp0 - 144) dp bp len -> cls_rng RNG (sp0 - 144) dp bp len ->
  Z.of_nat (length body) = len ->
  lo <= sp0 - 144 ->
  stk rsegs m lo sp0 ->
  asan_cells m ->
  cls_mem m Bw body dp bp len v0 ->
  (* the len = 0 exit, at 0x847b0 *)
  (forall (m' : word -> option byte) (j : list byte) (x10 x11 : word),
     length j = 40%nat ->
     rw_cells rsegs m' (sp0 - 144) (cls_fr_e j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     stk rsegs m' lo (sp0 - 144) ->
     cls_mem m' Bw body dp bp len (Z_to_bv 64 0) ->
     munch (cls_W (sp0 - 144) dp) m m' -> wmono rsegs m m' -> mem_grows m m' ->
     len = 0 ->
     ExecF.evtF rsegs RNG Q
       (MS (mkR ra (Z_to_bv 64 (sp0 - 144)) gp tp t0 t1 t2 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 x10 x11 (Z_to_bv 64 dp) a3 a4 a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 542640) fc None m' (seg_rom rsegs))) ->
  (* the loop head, at 0x8459c, with pos = 0 and nqv = s32_at Bw OFF_g_nq *)
  (forall (m' : word -> option byte) (j0 : list byte)
          (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 : word),
     length j0 = 8%nat ->
     rw_cells rsegs m' (sp0 - 144) (cls_fr j0 dp bp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     stk rsegs m' lo (sp0 - 144) ->
     cls_mem m' Bw body dp bp len (Z_to_bv 64 0) ->
     munch (cls_W (sp0 - 144) dp) m m' -> wmono rsegs m m' -> mem_grows m m' ->
     0 < len ->
     ExecF.evtF rsegs RNG Q
       (MS (cls_regs_head x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 gp tp
              (sp0 - 144) dp len 0 (TW.s32_at Bw TW.OFF_g_nq))
           F (Z_to_bv 64 542108) fc None m' (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 sp0) gp tp t0 t1 t2 s0 s1
              (Z_to_bv 64 bp) (Z_to_bv 64 len) (Z_to_bv 64 dp) a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 541952) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc lo sp0 bp len dp Bw body v0
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HBD HAPs HAPd HOFF HRNG Hlen HLO ST CELLS HMEM KEXIT KHEAD.
  remember (sp0 - 144) as spv eqn:Espv.
  assert (Esp0 : sp0 = spv + 144) by lia. subst sp0. clear Espv.
  unfold cls_bounds in HBD. destruct HBD as (Hspv0 & Hspv1 & Hdp0 & Hdp1 & Hbp0 & Hlen0 & Hbp1 & Hdp4).
  unfold cls_off in HOFF.
  destruct HOFF as (OG & OGOT & OCK & ODF & OBF & ODG & OBC & OBQ & OBN & OBD).
  unfold cls_rng in HRNG.
  destruct HRNG as (RFR & RGOT & RCK & RDP & RSD & RBP & RSB & RCMD & RSCMD & RQ & RSQ & RNQ & RNC).
  unfold cls_mem in HMEM. destruct HMEM as (HW & DPC & HBODY & ADC & ADQ & ADD & ADB & HWOK).
  destruct CELLS as (CK & GCK & _). unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in OG.
  pose proof (munch_refl (cls_W spv dp) m) as MU. unfold cls_W in MU.
  pose proof (munch_refl [(spv, spv + 144); (dp, dp + 4)] m) as MU2.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (mem_grows_refl m) as MG.
  carve_frame 144%nat ST.
  rewrite Z.add_0_r in FR, ST.
  (* 0x84500 addi sp,sp,-144 *)
  step.
  replace (spv + 144 + -144) with spv by lia.
  (* 0x84504 .. 0x84534 the 13 saved registers *)
  do 13 step.
  (* 0x84538 .. 0x84548: s0 = dp, s1 = len, a1 = [0xa4090] = 0xac9f8, s5 = [0xac9f8] = 0x7fff8000 *)
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDG : ov_read_bytes rsegs mm (wa 671888) 8 = Some (le8 (wa 707064)));
    [ replace (wa 671888) with (wa (671888 + 0)) by reflexivity;
      rewrite (bytes_at_read rsegs mm 671888 _ 0 8 GCK ltac:(lia)) by (rewrite length_le8; lia);
      reflexivity | ];
    assert (RDC : ov_read_bytes rsegs mm (wa 707064) 8 = Some (le8 (wa 2147450880)));
    [ replace (wa 707064) with (wa (707064 + 0)) by reflexivity;
      rewrite (bytes_at_read rsegs mm 707064 _ 0 8 CK ltac:(lia)) by (rewrite length_le8; lia);
      reflexivity | ]
  end.
  do 5 step.
  clear RDG RDC CK GCK.
  (* 0x8454c srli a1,a2,3; 0x84550 add a1,a1,s5: a1 = the shadow address of dp *)
  step. rewrite (unsigned_lit dp) by lia. rewrite cls_shr3.
  step.
  (* 0x84554 sd a1,24(sp) *)
  step.
  (* 0x84558 lb a1,0(a1): the shadow byte of dp *)
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (cls_sh_load mm dp 4 0 4 ADD ltac:(lia) ltac:(lia) ltac:(lia)) as (k & MK & SK);
    rewrite Z.add_0_r in MK, SK; change (4 - 1) with 3 in SK; unfold ASAN_K in MK;
    pose proof (rd1 mm _ _ MK) as RDK
  end.
  step.
  clear MK RDK.
  (* 0x8455c sd a0,32(sp) *)
  step.
  (* ---- 0x84564, where the check's two paths meet: a0 is bp or (dp & 7) + 3 ---- *)
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (JOIN : forall x10 : word,
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                x10 (sxb k) (Z_to_bv 64 dp) a3 a4 a5 a6 a7
                s2 s3 s4 (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 542052) fc None mm (seg_rom rsegs)))
  end.
  { intros x10.
    destruct (Z.eq_dec len 0) as [L0|L0].
    - (* len = 0: the empty body holds at every memory, so it is not carried over the store at dp *)
      lazymatch type of HBODY with cls_body ?mm _ _ =>
        assert (HBN : forall m' : word -> option byte, cls_body m' bp body)
          by (intros m'; exact (clsr_body_nil mm m' bp body HBODY ltac:(lia)))
      end.
      clear HBODY.
      (* 0x84564 sw zero,0(s0) *)
      step.
      (* 0x84568 beqz s1,0x847b0: taken, the epilogue *)
      step.
      rewrite (clsr_entry_eqb0 len) by lia. rewrite (proj2 (Z.eqb_eq len 0) L0). cbv iota.
      lazymatch goal with FR : rw_cells _ ?mm spv (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
        pose proof (clsr_entry_kept m mm spv dp Bw HW MU2 OG ODG) as HW';
        pose proof (rw_cells_merge rsegs mm spv [] [c1; c2; c3] rest FR) as FRE;
        pose proof FR as FRW; destruct FRW as [[FRwf _] _]
      end.
      cbn [app cells_size csize Nat.add] in FRE.
      cbn [cells_wf cell_wf] in FRwf.
      lazymatch type of FRE with rw_cells _ ?mm _ (CB _ ?j :: _) =>
        apply (KEXIT mm j x10 (sxb k))
      end.
      + cbn [cells_bytes cbytes]. rewrite !length_app, !length_le8. cbn [length]. lia.
      + exact FRE.
      + exact ST.
      + unfold cls_mem.
        split; [exact HW'|]. split; [exact DPC|]. split; [exact (HBN _)|].
        split; [exact ADC|]. split; [exact ADQ|]. split; [exact ADD|]. split; [exact ADB | exact HWOK].
      + exact MU.
      + exact WMo.
      + exact MG.
      + exact L0.
    - (* len <> 0: the body is off dp *)
      specialize (OBD ltac:(lia)).
      (* 0x84564 sw zero,0(s0) *)
      step.
      (* 0x84568 beqz s1,0x847b0: not taken *)
      step.
      rewrite (clsr_entry_eqb0 len) by lia. rewrite (proj2 (Z.eqb_neq len 0) L0). cbv iota.
      (* 0x8456c .. 0x84578: s7 = 0, s8 = g_nq - 1008, s11 = g_ncmd - 1036, a0 = 0x5e5578 *)
      do 4 step.
      (* 0x8457c lw s9,1008(s8): g_nq, no instrumented check *)
      lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (clsr_entry_kept m mm spv dp Bw HW MU2 OG ODG) as HW';
        pose proof (cls_rd mm Bw TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 4 HW' TMAP_A_g_nq ltac:(lia)
          ltac:(unfold TW.SZ_g_nq; lia)) as RDN
      end.
      unfold TA_g_nq in RDN. rewrite !Z.add_0_r in RDN.
      step. rewrite lw_world. clear RDN HW'.
      (* 0x84580 addi s10,a0,-376; 0x84584 andi a0,s0,7; 0x84588 addi a0,a0,3 *)
      step. step.
      rewrite ?cls_wrap64_7. rewrite (unsigned_lit dp) by lia. rewrite land7.
      step.
      (* 0x8458c sd a0,8(sp) *)
      step.
      (* 0x84590 auipc a0,0x56d; 0x84594 addi a0,a0,1648; 0x84598 sd a0,16(sp) *)
      do 3 step.
      lazymatch goal with FR : rw_cells _ ?mm spv (CB _ ?j0 :: _) |- _ =>
        pose proof (clsr_entry_kept m mm spv dp Bw HW MU2 OG ODG) as HW';
        pose proof FR as FRW; destruct FRW as [[FRwf _] _];
        apply (KHEAD mm j0 ra t0 t1 t2 (Z_to_bv 64 6233088) (sxb k) (Z_to_bv 64 dp) a3 a4 a5 a6 a7
                 s2 s3 s4 s6 t3 t4 t5 t6)
      end.
      + cbn [cells_wf cell_wf] in FRwf. exact (proj1 FRwf).
      + exact FR.
      + exact ST.
      + unfold cls_mem.
        split; [exact HW'|]. split; [exact DPC|]. split; [exact HBODY|].
        split; [exact ADC|]. split; [exact ADQ|]. split; [exact ADD|]. split; [exact ADB | exact HWOK].
      + exact MU.
      + exact WMo.
      + exact MG.
      + lia. }
  (* 0x84560 bnez a1,0x847f4 *)
  step. rewrite sxb_eq0.
  destruct SK as [C|[C Cu]].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply JOIN.
  - rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)). cbn [negb]. cbv iota.
    (* 0x847f4 andi a0,s0,7; 0x847f8 addi a0,a0,3; 0x847fc blt a0,a1,0x84564: the handler goes back *)
    step. step. step.
    rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit dp) by lia.
    rewrite (cls_lts_lit (dp mod 8 + 3) k ltac:(lia)).
    rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
    apply JOIN.
Qed.

(* cls_run_pre joins the two paths of each instrumented check at the instruction after its `bnez`:
   clsr_pre_join r pc J states the goal at pc for every value of register r (the one register the check's
   handler writes), clsr_pre_close r J closes a path that reached pc. clsr_pre_ul turns every
   bv_unsigned (Z_to_bv 64 e) of the walk into e. *)
Ltac clsr_pre_join r pc J :=
  lazymatch goal with |- ExecF.evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    assert (J : forall y : word, ExecF.evtF segs RNG Q (MS (tset p y R) F (Z_to_bv 64 pc) fc rv m ro))
  end.
Ltac clsr_pre_close r J := let w := reg_val r in exact (J w).
Ltac clsr_pre_ul :=
  rewrite ?cls_shr3, ?cls_wrap64_7, ?land7;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      rewrite (unsigned_lit e)
        by (first [lia | split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia])
  end;
  rewrite ?cls_shr3, ?land7.

(* ---- the loop head to the bcmp entry, 0x8459c .. 0x84658 ---- *)
Lemma cls_run_pre : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (spv dp bp len pos nqv s : Z) (Bc body : list byte) (v : word) (j0 : list byte)
    (ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110 : word)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 gp tp : word),
  cls_bounds spv dp bp len -> cls_off spv dp bp len -> cls_rng RNG spv dp bp len ->
  Z.of_nat (length body) = len ->
  Z.of_nat (length Bc) = TW.W_LEN ->
  0 <= pos ->
  (* the conclusions of check_latest_sent_seg_model.v cls_round for this round *)
  3 <= len - pos ->
  TW.u_at body pos 1 = TC.TAG ->
  s = Z.lor (Z.shiftl (TW.u_at body (pos + 2) 1) 7) (TW.u_at body (pos + 1) 1) ->
  0 <= s < TC.CMDS_MAX ->
  s < TW.g_ncmd Bc ->
  TW.Cmd_st Bc s = TC.PENDING ->
  TW.Cmd_len Bc s <= len - pos ->
  rw_cells rsegs m spv (cls_fr j0 dp bp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
  length j0 = 8%nat ->
  cls_mem m Bc body dp bp len v ->
  (forall x13' x14' x15' : word,
     ExecF.evtF rsegs RNG Q
       (MS (cls_regs_call x5 x6 x7 x13' x14' x15' x16 x17 x28 x29 x30 x31 gp tp
              spv dp bp len pos nqv s (TW.Cmd_len Bc s))
           F (Z_to_bv 64 273656) fc None m (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (cls_regs_head x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 gp tp
           spv dp len pos nqv)
        F (Z_to_bv 64 542108) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc spv dp bp len pos nqv s Bc body v j0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 gp tp
    HB HO HR HLb HLc Hpos H3 HTAG Hsdef Hs Hsnc HST HTL FR Hj0 HM K.
  unfold cls_bounds in HB. unfold cls_rng in HR. unfold cls_mem in HM.
  destruct HB as (Hsp0 & Hsp1 & Hdp0 & Hdp1 & Hbp0 & Hlen0 & Hbp1 & Hdp4).
  destruct HR as (Rfr & Rk1 & Rk2 & Rdp & Rdps & Rbody & Rbsh & Rcmd & Rcsh & Rq & Rqsh & Rnq & Rncmd).
  destruct HM as (HW & HDP & HBY & ADC & ADQ & ADD & ADB & HWOK).
  clear HO HLc Rk1 Rk2 Rdp Rdps Rq Rqsh Rnq ADQ ADD HWOK HDP.
  unfold cls_body in HBY. unfold cls_fr in FR. unfold cls_regs_head.
  unfold TC.CMDS_MAX in Hs. unfold TW.g_ncmd in Hsnc.
  pose proof (TWLK.u_at_range body pos 1) as Rb0.
  pose proof (TWLK.u_at_range body (pos + 1) 1) as Rb1.
  pose proof (TWLK.u_at_range body (pos + 2) 1) as Rb2.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in Rb0, Rb1, Rb2.
  pose proof (cls_cmd_len_range Bc s) as Rtl.
  pose proof (cls_cmd_st_range Bc s) as Rst.
  assert (Rsh : 0 <= Z.shiftl (TW.u_at body (pos + 2) 1) 7 < 2 ^ 15)
    by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  (* 0x8459c - 0x845a4: a2 = len - pos; the trap len - pos < 3 *)
  step. clsr_pre_ul.
  step. step.
  rewrite cls_ltu_lit by lia. rewrite (proj2 (Z.ltb_ge _ _) H3). cbn [negb]. cbv iota.
  (* 0x845a8 - 0x845ac: a0 = bp (frame slot 4) + pos *)
  step. step. clsr_pre_ul.
  (* 0x845b0 - 0x845bc: the check of the 1-byte load at bp + pos; its handler 0x84740 writes a3 *)
  destruct (cls_sh_load m bp len pos 1 ADB ltac:(lia) ltac:(lia) ltac:(lia)) as (k0 & MK0 & SK0).
  unfold ASAN_K in MK0. pose proof (rd1 m _ _ MK0) as RD. pose proof (Rbsh pos ltac:(lia)) as RK.
  step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
  clear RD RK MK0.
  clsr_pre_join 13 0x845c0 J1.
  2: { step. rewrite sxb_eq0. destruct SK0 as [C|[C Cu]].
       - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. clsr_pre_close 13 J1.
       - rewrite (proj2 (Z.eqb_neq (bv_signed k0) 0) ltac:(lia)). cbn [negb]. cbv iota.
         step. clsr_pre_ul. step. clsr_pre_ul.
         rewrite (cls_lts_lit ((bp + pos) mod 8) k0) by lia.
         rewrite (proj2 (Z.ltb_lt ((bp + pos) mod 8) (bv_signed k0)) ltac:(lia)). cbn [negb]. cbv iota.
         step. clsr_pre_close 13 J1. }
  intros y13. cbv beta iota delta [tset]. clear SK0.
  (* 0x845c0 - 0x845c8: b[0] = TAG *)
  assert (RB : ov_read_bytes rsegs m (wa (bp + pos)) 1 = Some (TW.sub body pos 1))
    by (apply (bytes_at_read rsegs m bp body pos 1%nat HBY); lia).
  step. clear RB. rewrite ?lbu_world. rewrite HTAG. unfold TC.TAG.
  step. step. rewrite cls_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  (* 0x845cc - 0x845dc: a1 = bp + pos + 1; the check of it; its handler 0x8474c writes a4 *)
  step. clsr_pre_ul.
  destruct (cls_sh_load m bp len (pos + 1) 1 ADB ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & MK1 & SK1).
  replace (bp + (pos + 1)) with (bp + pos + 1) in MK1, SK1 by lia.
  unfold ASAN_K in MK1. pose proof (rd1 m _ _ MK1) as RD. pose proof (Rbsh (pos + 1) ltac:(lia)) as RK.
  replace (bp + (pos + 1)) with (bp + pos + 1) in RK by lia.
  step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
  clear RD RK MK1.
  clsr_pre_join 14 0x845e0 J2.
  2: { step. rewrite sxb_eq0. destruct SK1 as [C|[C Cu]].
       - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. clsr_pre_close 14 J2.
       - rewrite (proj2 (Z.eqb_neq (bv_signed k1) 0) ltac:(lia)). cbn [negb]. cbv iota.
         step. clsr_pre_ul. step. clsr_pre_ul.
         rewrite (cls_lts_lit ((bp + pos + 1) mod 8) k1) by lia.
         rewrite (proj2 (Z.ltb_lt ((bp + pos + 1) mod 8) (bv_signed k1)) ltac:(lia)). cbn [negb]. cbv iota.
         step. clsr_pre_close 14 J2. }
  intros y14. cbv beta iota delta [tset]. clear SK1.
  (* 0x845e0 - 0x845f4: a1 = bp + pos + 2; the check of it around the load of b[1]; its handler 0x84758
     writes a5 *)
  step. clsr_pre_ul.
  destruct (cls_sh_load m bp len (pos + 2) 1 ADB ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & MK2 & SK2).
  replace (bp + (pos + 2)) with (bp + pos + 2) in MK2, SK2 by lia.
  unfold ASAN_K in MK2. pose proof (rd1 m _ _ MK2) as RD. pose proof (Rbsh (pos + 2) ltac:(lia)) as RK.
  replace (bp + (pos + 2)) with (bp + pos + 2) in RK by lia.
  step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
  clear RD RK MK2.
  assert (RB : ov_read_bytes rsegs m (wa (bp + pos + 1)) 1 = Some (TW.sub body (pos + 1) 1)).
  { replace (bp + pos + 1) with (bp + (pos + 1)) by lia.
    apply (bytes_at_read rsegs m bp body (pos + 1) 1%nat HBY); lia. }
  step. clear RB. rewrite ?lbu_world.
  clsr_pre_join 15 0x845f8 J3.
  2: { step. rewrite sxb_eq0. destruct SK2 as [C|[C Cu]].
       - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. clsr_pre_close 15 J3.
       - rewrite (proj2 (Z.eqb_neq (bv_signed k2) 0) ltac:(lia)). cbn [negb]. cbv iota.
         step. clsr_pre_ul. step. clsr_pre_ul.
         rewrite (cls_lts_lit ((bp + pos + 2) mod 8) k2) by lia.
         rewrite (proj2 (Z.ltb_lt ((bp + pos + 2) mod 8) (bv_signed k2)) ltac:(lia)). cbn [negb]. cbv iota.
         step. clsr_pre_close 15 J3. }
  intros y15. cbv beta iota delta [tset]. clear SK2.
  (* 0x845f8: b[2] *)
  assert (RB : ov_read_bytes rsegs m (wa (bp + pos + 2)) 1 = Some (TW.sub body (pos + 2) 1)).
  { replace (bp + pos + 2) with (bp + (pos + 2)) by lia.
    apply (bytes_at_read rsegs m bp body (pos + 2) 1%nat HBY); lia. }
  step. clear RB. rewrite ?lbu_world.
  (* 0x845fc: a4 = g_ncmd, sign-extended *)
  pose proof (cls_rd m Bc TW.OFF_g_ncmd TA_g_ncmd TW.SZ_g_ncmd 0 4 HW TMAP_A_g_ncmd ltac:(lia)
    ltac:(unfold TW.SZ_g_ncmd; lia)) as RD.
  unfold TA_g_ncmd in RD. rewrite !Z.add_0_r in RD.
  step. clear RD. rewrite lw_world.
  (* 0x84600 - 0x84604: s2 = (b[2] << 7) | b[1] = s *)
  step. clsr_pre_ul. step. clsr_pre_ul. rewrite <- Hsdef.
  (* 0x84608: the trap s >= g_ncmd *)
  step. rewrite (cls_ltu_s32 Bc TW.OFF_g_ncmd s ltac:(lia) Hsnc). cbn [negb]. cbv iota.
  (* 0x8460c - 0x84614: s3 = t = g_cmd + 40 s *)
  step. step. clsr_pre_ul. step. clsr_pre_ul.
  replace (s * 40) with (40 * s) by lia.
  (* 0x84618 - 0x84624: the check of the 4-byte load at t, s6 kept; its handler 0x84764 writes a3 *)
  destruct (cls_sh_load m 6181888 40960 (40 * s) 4 ADC ltac:(lia) ltac:(lia) ltac:(lia)) as (k3 & MK3 & SK3).
  unfold ASAN_K in MK3. pose proof (rd1 m _ _ MK3) as RD.
  pose proof (cls_shc RNG (40 * s) Rcsh ltac:(lia)) as RK. unfold ASAN_K in RK.
  step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
  clear RD RK MK3.
  clsr_pre_join 13 0x84628 J4.
  2: { step. rewrite sxb_eq0. destruct SK3 as [C|[C Cu]].
       - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. clsr_pre_close 13 J4.
       - rewrite (proj2 (Z.eqb_neq (bv_signed k3) 0) ltac:(lia)). cbn [negb]. cbv iota.
         step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
         rewrite (cls_lts_lit ((6181888 + 40 * s) mod 8 + 3) k3) by lia.
         rewrite (proj2 (Z.ltb_lt ((6181888 + 40 * s) mod 8 + 3) (bv_signed k3)) ltac:(lia)).
         cbn [negb]. cbv iota.
         step. clsr_pre_close 13 J4. }
  intros y13'. cbv beta iota delta [tset]. clear SK3.
  (* 0x84628 - 0x84630: t->st = PENDING *)
  pose proof (cls_rd m Bc TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s) 4 HW TMAP_A_g_cmd ltac:(lia)
    ltac:(unfold TW.SZ_g_cmd; lia)) as RD.
  unfold TA_g_cmd in RD.
  replace (TW.OFF_g_cmd + 40 * s) with (TW.A_Cmd_st s) in RD by (unfold TW.A_Cmd_st; lia).
  step. clear RD. rewrite lw_world. change (TW.s32_at Bc (TW.A_Cmd_st s)) with (TW.Cmd_st Bc s).
  rewrite HST. unfold TC.PENDING.
  step. step. rewrite cls_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  (* 0x84634 - 0x84644: a1 = t + 36; the check of it; its handler 0x84774 writes a4 *)
  step. clsr_pre_ul.
  destruct (cls_sh_load m 6181888 40960 (40 * s + 36) 1 ADC ltac:(lia) ltac:(lia) ltac:(lia))
    as (k4 & MK4 & SK4).
  replace (6181888 + (40 * s + 36)) with (6181888 + 40 * s + 36) in MK4, SK4 by lia.
  unfold ASAN_K in MK4. pose proof (rd1 m _ _ MK4) as RD.
  pose proof (cls_shc RNG (40 * s + 36) Rcsh ltac:(lia)) as RK. unfold ASAN_K in RK.
  replace (6181888 + (40 * s + 36)) with (6181888 + 40 * s + 36) in RK by lia.
  step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
  clear RD RK MK4.
  clsr_pre_join 14 0x84648 J5.
  2: { step. rewrite sxb_eq0. destruct SK4 as [C|[C Cu]].
       - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. clsr_pre_close 14 J5.
       - rewrite (proj2 (Z.eqb_neq (bv_signed k4) 0) ltac:(lia)). cbn [negb]. cbv iota.
         step. clsr_pre_ul. step. clsr_pre_ul.
         rewrite (cls_lts_lit ((6181888 + 40 * s + 36) mod 8) k4) by lia.
         rewrite (proj2 (Z.ltb_lt ((6181888 + 40 * s + 36) mod 8) (bv_signed k4)) ltac:(lia)).
         cbn [negb]. cbv iota.
         step. clsr_pre_close 14 J5. }
  intros y14'. cbv beta iota delta [tset]. clear SK4.
  (* 0x84648: s4 = t->len *)
  pose proof (cls_rd m Bc TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s + 36) 1 HW TMAP_A_g_cmd ltac:(lia)
    ltac:(unfold TW.SZ_g_cmd; lia)) as RD.
  unfold TA_g_cmd in RD.
  replace (0x5e5400 + (40 * s + 36)) with (6181888 + 40 * s + 36) in RD by lia.
  replace (TW.OFF_g_cmd + (40 * s + 36)) with (TW.A_Cmd_len s) in RD by (unfold TW.A_Cmd_len; lia).
  step. clear RD. rewrite lbu_world. change (TW.u_at Bc (TW.A_Cmd_len s) 1) with (TW.Cmd_len Bc s).
  (* 0x8464c: the trap len - pos < t->len *)
  step. rewrite cls_ltu_lit by lia. rewrite (proj2 (Z.ltb_ge _ _) HTL). cbn [negb]. cbv iota.
  (* 0x84650 - 0x84658: a1 = t + 12, a2 = t->len, the call *)
  step. clsr_pre_ul. step. clsr_pre_ul. step.
  let a3 := reg_val 13 in let a4 := reg_val 14 in let a5 := reg_val 15 in exact (K a3 a4 a5).
Qed.

(* ---- the helpers of cls_run_post ---- *)

(* a munch of [d, d + 4) keeps the world when [d, d + 4) misses every range of G_HARNESS: the store at dp *)
Lemma clsr_post_tw_munch : forall (m m' : word -> option byte) (d : Z) (Bw : list byte),
  tw_at TMAP_A (csw_view m) Bw -> munch [(d, d + 4)] m m' ->
  (forall b n, In (b, n) TransportG.G_HARNESS -> d + 4 <= b \/ b + n <= d) ->
  tw_at TMAP_A (csw_view m') Bw.
Proof.
  intros m m' d Bw HW MU Hd.
  apply (tw_kept_GA (csw_view m) _ Bw HW).
  intros b n i Hin Hi.
  pose proof (TransportG.G_HARNESS_in_hull (b, n) Hin) as Hh.
  cbn [fst snd] in Hh. unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in Hh.
  assert (Hr : 0 <= b + i < 2 ^ 64) by lia.
  assert (E : m' (wa (b + i)) = m (wa (b + i))).
  { apply MU. cbn [outside]. rewrite (wa_unsigned (b + i) Hr).
    split; [destruct (Hd b n Hin); lia | exact I]. }
  unfold csw_view, mrd. rewrite E. reflexivity.
Qed.

(* two words with the same low 4 bytes are the same C4 cell *)
Lemma clsr_post_c4_swap : forall (mm : word -> option byte) A v v', le4 v = le4 v' ->
  rw_cells rsegs mm A [C4 v] -> rw_cells rsegs mm A [C4 v'].
Proof.
  intros mm A v v' H [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. split; exact I.
  - cbn [cells_bytes cbytes] in *. rewrite <- H. exact Hb.
  - cbn [cells_size csize] in *. exact Hw.
Qed.

(* `slli rd,rs,32; srli rd,rd,32` of a word below 2^32 *)
Lemma clsr_post_shl32_shr32 : forall k, 0 <= k < 2 ^ 32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 32))) 32 = k.
Proof.
  intros k Hk. rewrite (unsigned_lit k) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by nia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

(* the loop head's frame, read as the epilogue's: its low 40 bytes become one blob *)
Lemma clsr_post_fr_e : forall (mm : word -> option byte) (spv dp bp : Z) (j0 : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
  length j0 = 8%nat ->
  rw_cells rsegs mm spv (cls_fr j0 dp bp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  exists j, length j = 40%nat /\ rw_cells rsegs mm spv (cls_fr_e j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros mm spv dp bp j0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 HJ H.
  pose proof (rw_cells_merge rsegs mm spv []
    [CB 8 j0; C8 (Z_to_bv 64 (dp mod 8 + 3)); C8 (Z_to_bv 64 6233088);
     C8 (Z_to_bv 64 (dp / 8 + 2147450880)); C8 (Z_to_bv 64 bp)]
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] H) as M.
  exists (cells_bytes [CB 8 j0; C8 (Z_to_bv 64 (dp mod 8 + 3)); C8 (Z_to_bv 64 6233088);
                       C8 (Z_to_bv 64 (dp / 8 + 2147450880)); C8 (Z_to_bv 64 bp)]).
  split.
  - cbn [cells_bytes cbytes]. rewrite !length_app, HJ, !length_le8. reflexivity.
  - exact M.
Qed.

(* before store_done: write the store's address in H the way store_done names it (wa of the goal's address) *)
Ltac clsr_post_fix_addr H :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a _) _) =>
      let E := addr_expr a in
      lazymatch type of H with
      | context [write_to_mem mm (wa ?E0) ?bs0] =>
          replace (write_to_mem mm (wa E0) bs0) with (write_to_mem mm (wa E) bs0) in H
            by (f_equal; unfold wa; f_equal; lia)
      end
  end.

(* ---- the bcmp return to the next loop head or the epilogue, 0x8465c .. 0x846b0, 0x846b4 .. 0x8471c ---- *)
Lemma cls_run_post : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (lo spv dp bp len pos s dispc : Z) (Bc B2 body : list byte) (j0 : list byte)
    (ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110 : word)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp : word),
  cls_bounds spv dp bp len -> cls_app spv 144 -> cls_app dp 4 ->
  cls_off spv dp bp len -> cls_rng RNG spv dp bp len ->
  Z.of_nat (length body) = len ->
  Z.of_nat (length Bc) = TW.W_LEN ->
  0 <= pos -> 3 <= len - pos -> 0 <= TW.g_nq Bc <= TC.CMDS_MAX ->
  0 <= s < TC.CMDS_MAX ->
  TW.Cmd_len Bc s <= len - pos ->
  TC.q_remove_m (TW.set_Cmd_st Bc s TC.SENT) s = Some (B2, tt) ->
  stk rsegs m lo spv -> lo <= spv ->
  rw_cells rsegs m spv (cls_fr j0 dp bp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
  length j0 = 8%nat ->
  cls_mem m Bc body dp bp len (Z_to_bv 64 dispc) ->
  (* the exit, at 0x847b0 *)
  (forall (m' : word -> option byte) (j : list byte) (y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 : word)
          (z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
     length j = 40%nat ->
     rw_cells rsegs m' spv (cls_fr_e j ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
     stk rsegs m' lo spv ->
     cls_mem m' B2 body dp bp len (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display B2 s))) ->
     munch (cls_W spv dp) m m' -> wmono rsegs m m' -> mem_grows m m' ->
     len <= pos + TW.Cmd_len Bc s ->
     ExecF.evtF rsegs RNG Q
       (MS (mkR y1 (Z_to_bv 64 spv) gp tp z5 z6 z7 y8 y9 z10 z11 z12 z13 z14 z15 z16 z17
                 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 z28 z29 z30 z31)
           F (Z_to_bv 64 542640) fc None m' (seg_rom rsegs))) ->
  (* the next round, at the loop head 0x8459c *)
  (forall (m' : word -> option byte) (j0' : list byte)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y22 y28 y29 y30 y31 : word),
     length j0' = 8%nat ->
     rw_cells rsegs m' spv (cls_fr j0' dp bp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
     stk rsegs m' lo spv ->
     cls_mem m' B2 body dp bp len (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display B2 s))) ->
     munch (cls_W spv dp) m m' -> wmono rsegs m m' -> mem_grows m m' ->
     pos + TW.Cmd_len Bc s < len ->
     ExecF.evtF rsegs RNG Q
       (MS (cls_regs_head y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y22 y28 y29 y30 y31 gp tp
              spv dp len (pos + TW.Cmd_len Bc s) (TW.g_nq B2))
           F (Z_to_bv 64 542108) fc None m' (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (cls_regs_post x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp
           spv dp len pos (TW.g_nq Bc) s (TW.Cmd_len Bc s))
        F (Z_to_bv 64 542300) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc lo spv dp bp len pos s dispc Bc B2 body j0
    ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp
    HBD HAS HAD HOFF HRNG HLB HLBc Hpos H3 HNQ Hs HTL HQR ST HLO FR HJ0 HM EXIT HEAD.
  assert (HL : 0 < len) by lia.
  destruct HBD as (Hsp0 & Hsp1 & Hdp0 & Hdp1 & Hbp0 & Hlen0 & Hbp1 & Hdp4).
  destruct HRNG as (RFR & RC1 & RC2 & RDP & RDS & RBP & RBS & RC & RSC & RQ & RSQ & RNQ & RNC).
  destruct HM as (HW & DPc & HB & AC & AQ & AD & AB & HK).
  pose proof HOFF as (_ & _ & _ & _ & _ & HOG & HOB & _ & _ & _).
  unfold TC.CMDS_MAX in HNQ, Hs.
  pose proof (cls_cmd_len_range Bc s) as RTL.
  pose proof (Z.mod_pos_bound dp 8 ltac:(lia)) as Rdp8.
  (* the model: q_remove's loop gives B1q and the count kf, and B2 = set_g_nq B1q kf *)
  destruct (cls_qrm _ _ _ HQR) as (B1q & kf & HQL & HB2). clear HQR.
  rewrite (cls_g_nq_set_st Bc s TC.SENT HLBc ltac:(unfold TC.CMDS_MAX; lia)) in HQL.
  pose proof (cls_len_set_st Bc s TC.SENT HLBc ltac:(unfold TC.CMDS_MAX; lia)) as HL1.
  destruct (cls_q_loop_gen (fun _ => True) (fun _ _ _ _ _ _ => I) _ _ _ _ _ _ _ _ HQL HL1
              ltac:(lia) ltac:(lia) I) as (HLq & _ & Kf1 & Kf2 & _).
  assert (HKF : 0 <= kf <= TW.g_nq Bc) by lia.
  clear Kf1 Kf2.
  assert (HNQ2 : TW.g_nq B2 = kf) by (rewrite HB2; apply cls_g_nq_set_nq; [exact HLq | lia]).
  rewrite HNQ2 in HEAD. subst B2.
  unfold cls_regs_head in HEAD. unfold cls_regs_post.
  pose proof (munch_refl (cls_W spv dp) m) as MU. unfold cls_W in MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (mem_grows_refl m) as MG.
  unfold cls_fr in FR.
  (* ---- 0x84674 .. 0x846b0: g_nq := k, the display, the next round or the exit ---- *)
  assert (TAIL : forall (m3 : word -> option byte) (Bqf : list byte) (kfin : Z)
            (y10 y11 y12 y13 y14 y15 y16 : word),
    Bqf = B1q -> kfin = kf ->
    rw_cells rsegs m3 spv (cls_fr j0 dp bp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
    stk rsegs m3 lo spv ->
    tw_at TMAP_A (csw_view m3) Bqf -> rw_cells rsegs m3 dp [C4 (Z_to_bv 64 dispc)] -> cls_body m3 bp body ->
    addressable m3 6181888 40960 -> addressable m3 6233088 4096 -> addressable m3 dp 4 ->
    addressable m3 bp len -> cls_wok dp m3 ->
    munch (cls_W spv dp) m m3 -> wmono rsegs m m3 -> mem_grows m m3 ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
               y10 y11 y12 y13 y14 y15 y16 x17
               (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
               (Z_to_bv 64 6157680) (Z_to_bv 64 kfin) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
               x28 x29 x30 x31)
          F (Z_to_bv 64 542324) fc None m3 (seg_rom rsegs))).
  { intros m3 Bqf kfin y10 y11 y12 y13 y14 y15 y16 EBq EKf FR3 ST3 HW3 DP3 HB3 AC3 AQ3 AD3 AB3 HK3
      MU3 WMo3 MG3.
    subst Bqf kfin.
    clear FR ST HW DPc HB AC AQ AD AB HK MU WMo MG.
    unfold cls_fr in FR3. unfold cls_W in MU3.
    (* 0x84674: sw s9,1008(s8): g_nq := kf *)
    assert (HS : store_ok rsegs m3 (wa 6158688) 4 = true).
    { apply (cls_wok_store_ok dp m3 6158688 4 HK3); [lia | change (Z.of_nat 4) with 4; lia |].
      intros i Hi. change (Z.of_nat 4) with 4 in Hi. unfold cls_wrange. lia. }
    pose proof HOFF as (O1 & _ & _ & _ & _ & _ & _ & _ & O9 & _). specialize (O9 HL).
    unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in O1.
    pose proof (HOG _ _ (TMAP_A_in_G _ _ _ TMAP_A_g_nq)) as Gn. unfold TA_g_nq, TW.SZ_g_nq in Gn.
    step.
    pose proof (cls_tw_wr4 m3 B1q TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 kf HW3 TMAP_A_g_nq ltac:(lia)
      ltac:(unfold TW.SZ_g_nq; lia)) as HW4.
    unfold TA_g_nq in HW4. rewrite !Z.add_0_r in HW4.
    change (TW.upd B1q TW.OFF_g_nq (TW.put 4 kf)) with (TW.set_g_nq B1q kf) in HW4.
    clsr_post_fix_addr HW4.
    clear HW3.
    store_done.
    clear O1 O9 Gn.
    lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
    (* the state at 0x8469c: the display is in a0, the check of dp is done *)
    assert (DPST : forall z11 z12 : word,
      ExecF.evtF rsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 (Z_to_bv 64 (TW.Cmd_display (TW.set_g_nq B1q kf) s)) z11 z12 y13 y14 y15 y16 x17
                 (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
                 (Z_to_bv 64 6157680) (Z_to_bv 64 kf) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 542364) fc None m4 (seg_rom rsegs))).
    { intros z11 z12.
      (* 0x8469c: lw a1,0(s0) *)
      step.
      (* 0x846a0: or a0,a1,a0 *)
      step.
      (* 0x846a4: add s7,s7,s4 *)
      step.
      (* 0x846a8: sw a0,0(s0); the world is kept through a munch of [dp, dp + 4) *)
      pose proof HOFF as (_ & _ & _ & O4 & _ & _ & _ & _ & _ & O10). specialize (O10 HL).
      pose proof (munch_refl [(dp, dp + 4)] m4) as MUd.
      step.
      lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
      pose proof (clsr_post_tw_munch m4 m5 dp _ HW4 MUd HOG) as HW5.
      clear HW4 MUd O4 O10.
      lazymatch goal with H : rw_cells rsegs m5 dp [C4 ?v] |- _ =>
        pose proof (clsr_post_c4_swap m5 dp v
                      (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display (TW.set_g_nq B1q kf) s)))
                      (cls_disp_le4 _ _) H) as DP5; clear H end.
      (* 0x846ac: bltu s7,s1 *)
      step. rewrite cls_ltu_lit by lia.
      destruct (Z.ltb_spec (pos + TW.Cmd_len Bc s) len) as [Lt|Ge]; cbv iota.
      - apply (HEAD m5 j0);
          [ exact HJ0 | exact FR3 | exact ST3
          | exact (conj HW5 (conj DP5 (conj HB3 (conj AC3 (conj AQ3 (conj AD3 (conj AB3 HK3)))))))
          | exact MU3 | exact WMo3 | exact MG3 | exact Lt ].
      - (* 0x846b0: j 0x847b0 *)
        step.
        destruct (clsr_post_fr_e m5 spv dp bp j0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110 HJ0 FR3)
          as (je & HJe & FRe).
        apply (EXIT m5 je);
          [ exact HJe | exact FRe | exact ST3
          | exact (conj HW5 (conj DP5 (conj HB3 (conj AC3 (conj AQ3 (conj AD3 (conj AB3 HK3)))))))
          | exact MU3 | exact WMo3 | exact MG3 | exact Ge ]. }
    (* the state at 0x8468c: the check of t + 8 is done *)
    assert (BODYD : forall z11 z12 : word,
      ExecF.evtF rsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 (Z_to_bv 64 (6181888 + 40 * s + 8)) z11 z12 y13 y14 y15 y16 x17
                 (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
                 (Z_to_bv 64 6157680) (Z_to_bv 64 kf) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 542348) fc None m4 (seg_rom rsegs))).
    { intros z11 z12.
      (* 0x8468c: ld a1,24(sp): the shadow address of dp *)
      step.
      (* 0x84690: lb a1,0(a1): the shadow byte of dp *)
      destruct (cls_sh_load m4 dp 4 0 4 AD3 ltac:(lia) ltac:(lia) ltac:(lia)) as (kd & MKd & SKd).
      rewrite Z.add_0_r in MKd, SKd. change (4 - 1) with 3 in SKd. unfold ASAN_K in MKd.
      pose proof (rd1 m4 _ _ MKd) as RDd. clear MKd.
      step.
      (* 0x84694: lw a0,0(a0): t->display *)
      pose proof (cls_rd m4 (TW.set_g_nq B1q kf) TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s + 8) 4 HW4
        TMAP_A_g_cmd ltac:(lia) ltac:(unfold TW.SZ_g_cmd; lia)) as RDc.
      unfold TA_g_cmd in RDc.
      replace (6181888 + (40 * s + 8)) with (6181888 + 40 * s + 8) in RDc by lia.
      replace (TW.OFF_g_cmd + (40 * s + 8)) with (TW.A_Cmd_display s) in RDc
        by (unfold TW.A_Cmd_display; lia).
      step. rewrite lw_world. clear RDc.
      change (TW.s32_at (TW.set_g_nq B1q kf) (TW.A_Cmd_display s))
        with (TW.Cmd_display (TW.set_g_nq B1q kf) s).
      (* 0x84698: bnez a1 *)
      step. rewrite sxb_eq0.
      destruct SKd as [C|[C Cu]].
      - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply DPST.
      - rewrite (proj2 (Z.eqb_neq (bv_signed kd) 0) ltac:(lia)). cbn [negb]. cbv iota.
        (* 0x847a0-0x847a4: ld a2,8(sp); blt a2,a1 goes back to the load *)
        step. step.
        rewrite (cls_lts_lit (dp mod 8 + 3) kd ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
        apply DPST. }
    (* 0x84678-0x84688: the check of the 4-byte load at t + 8 *)
    destruct (cls_sh_load m4 6181888 40960 (40 * s + 8) 4 AC3 ltac:(lia) ltac:(lia) ltac:(lia))
      as (k8 & MK8 & SK8).
    replace (6181888 + (40 * s + 8)) with (6181888 + 40 * s + 8) in MK8, SK8 by lia.
    change (4 - 1) with 3 in SK8.
    pose proof (cls_shc RNG (40 * s + 8) RSC ltac:(lia)) as RK8.
    replace (6181888 + (40 * s + 8)) with (6181888 + 40 * s + 8) in RK8 by lia.
    unfold ASAN_K in MK8, RK8.
    pose proof (rd1 m4 _ _ MK8) as RD8. clear MK8.
    step.
    step. rewrite (unsigned_lit (6181888 + 40 * s + 8)) by lia. rewrite cls_shr3.
    step. step.
    step. rewrite sxb_eq0.
    destruct SK8 as [C|[C Cu]].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply BODYD.
    - rewrite (proj2 (Z.eqb_neq (bv_signed k8) 0) ltac:(lia)). cbn [negb]. cbv iota.
      (* 0x84790-0x8479c: the handler goes back to the load *)
      step. step.
      step. rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit (6181888 + 40 * s + 8)) by lia.
      rewrite (cls_lts_lit ((6181888 + 40 * s + 8) mod 8 + 3) k8 ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
      step. apply BODYD. }
  (* ---- 0x846c8 .. 0x8471c: the q_remove loop, i the index, k the count kept ---- *)
  assert (LOOP : forall fuel i k (Bq : list byte) (m3 : word -> option byte) (y11 y14 y15 y16 : word)
            (A0 A3 N2 : Z),
    TC.q_remove_loop fuel Bq s (TW.g_nq Bc) i k = Some (B1q, kf) ->
    0 <= k <= i -> i < TW.g_nq Bc ->
    A0 = 6233088 + 4 * i -> A3 = 6233088 + 4 * i -> N2 = TW.g_nq Bc - i ->
    rw_cells rsegs m3 spv (cls_fr j0 dp bp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
    stk rsegs m3 lo spv ->
    tw_at TMAP_A (csw_view m3) Bq -> rw_cells rsegs m3 dp [C4 (Z_to_bv 64 dispc)] -> cls_body m3 bp body ->
    addressable m3 6181888 40960 -> addressable m3 6233088 4096 -> addressable m3 dp 4 ->
    addressable m3 bp len -> cls_wok dp m3 ->
    munch (cls_W spv dp) m m3 -> wmono rsegs m m3 -> mem_grows m m3 ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
               (Z_to_bv 64 A0) y11 (Z_to_bv 64 N2) (Z_to_bv 64 A3) y14 y15 y16 x17
               (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
               (Z_to_bv 64 6157680) (Z_to_bv 64 k) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
               x28 x29 x30 x31)
          F (Z_to_bv 64 542408) fc None m3 (seg_rom rsegs))).
  { clear FR ST HW DPc HB AC AQ AD AB HK MU WMo MG.
    induction fuel as [|fuel IH];
      intros i k Bq m3 y11 y14 y15 y16 A0 A3 N2 HQi Hki Hinq EA0 EA3 EN2
        FR3 ST3 HW3 DP3 HB3 AC3 AQ3 AD3 AB3 HK3 MU3 WMo3 MG3; [discriminate HQi|].
    destruct (cls_q_step (S fuel) Bq s (TW.g_nq Bc) i k B1q kf HQi Hinq) as (f2 & Ef2 & HiM & HQ2).
    injection Ef2 as <-. unfold TC.CMDS_MAX in HiM.
    (* the state at 0x8470c: a2 -= 1, a0 and a3 += 4, then the loop test *)
    assert (NEXT : forall k' (Bq' : list byte) (m4 : word -> option byte) (z11 z14 z15 z16 : word),
      TC.q_remove_loop fuel Bq' s (TW.g_nq Bc) (i + 1) k' = Some (B1q, kf) -> 0 <= k' <= i + 1 ->
      rw_cells rsegs m4 spv (cls_fr j0 dp bp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
      stk rsegs m4 lo spv ->
      tw_at TMAP_A (csw_view m4) Bq' -> rw_cells rsegs m4 dp [C4 (Z_to_bv 64 dispc)] -> cls_body m4 bp body ->
      addressable m4 6181888 40960 -> addressable m4 6233088 4096 -> addressable m4 dp 4 ->
      addressable m4 bp len -> cls_wok dp m4 ->
      munch (cls_W spv dp) m m4 -> wmono rsegs m m4 -> mem_grows m m4 ->
      ExecF.evtF rsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 (Z_to_bv 64 A0) z11 (Z_to_bv 64 N2) (Z_to_bv 64 A3) z14 z15 z16 x17
                 (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
                 (Z_to_bv 64 6157680) (Z_to_bv 64 k') (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 542476) fc None m4 (seg_rom rsegs))).
    { intros k' Bq' m4 z11 z14 z15 z16 HQ' Hk' FR4 ST4 HW4 DP4 HB4 AC4 AQ4 AD4 AB4 HK4 MU4 WMo4 MG4.
      (* 0x8470c-0x84714 *)
      step. step. step.
      (* 0x84718: bnez a2 *)
      step. rewrite cls_eqb0 by lia.
      destruct (Z.eqb_spec (N2 + -1) 0) as [E0|E0]; cbn [negb]; cbv iota.
      - (* 0x8471c: j 0x84674 *)
        step.
        destruct (cls_q_exit _ _ _ _ _ _ _ _ HQ' ltac:(lia)) as [EB EK].
        apply (TAIL m4 Bq' k');
          [ exact (eq_sym EB) | exact (eq_sym EK) | exact FR4 | exact ST4 | exact HW4 | exact DP4 | exact HB4
          | exact AC4 | exact AQ4 | exact AD4 | exact AB4 | exact HK4 | exact MU4 | exact WMo4 | exact MG4 ].
      - apply (IH (i + 1) k' Bq' m4);
          [ exact HQ' | lia | lia | lia | lia | lia | exact FR4 | exact ST4 | exact HW4 | exact DP4 | exact HB4
          | exact AC4 | exact AQ4 | exact AD4 | exact AB4 | exact HK4 | exact MU4 | exact WMo4 | exact MG4 ]. }
    unfold cls_fr in FR3. unfold cls_W in MU3.
    (* the state at 0x846d8: the check of g_q[i] is done *)
    assert (BODYQ : forall z11 z14 : word,
      ExecF.evtF rsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 (Z_to_bv 64 A0) z11 (Z_to_bv 64 N2) (Z_to_bv 64 A3) z14 y15 y16 x17
                 (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
                 (Z_to_bv 64 6157680) (Z_to_bv 64 k) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 542424) fc None m3 (seg_rom rsegs))).
    { intros z11 z14.
      (* 0x846d8: lw a4,0(a3) = g_q[i] *)
      pose proof (cls_rd m3 Bq TW.OFF_g_q TA_g_q TW.SZ_g_q (4 * i) 4 HW3 TMAP_A_g_q ltac:(lia)
        ltac:(unfold TW.SZ_g_q; lia)) as RDq.
      unfold TA_g_q in RDq. replace (6233088 + 4 * i) with A3 in RDq by lia.
      step. rewrite lw_world. clear RDq.
      pose proof (TWLK.s32_range Bq (TW.OFF_g_q + 4 * i)) as RS1.
      (* 0x846dc: beq a4,s2 *)
      step. rewrite cls_eqb_lit by lia.
      rewrite (cls_s32_eqb Bq (TW.OFF_g_q + 4 * i) s) by lia.
      change (TW.u_at Bq (TW.OFF_g_q + 4 * i) 4) with (TW.Q_at Bq i).
      destruct (Z.eqb_spec (TW.Q_at Bq i) s) as [EQS|EQS]; cbv iota.
      - (* g_q[i] = s: skip, 0x8470c *)
        try rewrite (proj2 (Z.eqb_eq _ _) EQS) in HQ2. cbv beta iota in HQ2.
        apply (NEXT k Bq m3);
          [ exact HQ2 | lia | exact FR3 | exact ST3 | exact HW3 | exact DP3 | exact HB3
          | exact AC3 | exact AQ3 | exact AD3 | exact AB3 | exact HK3 | exact MU3 | exact WMo3 | exact MG3 ].
      - (* copy: 0x846e0 *)
        try rewrite (proj2 (Z.eqb_neq _ _) EQS) in HQ2. cbv beta iota in HQ2.
        (* the state at 0x84704: the check of g_q[k] is done *)
        assert (BODYC : forall z15 z16 : word,
          ExecF.evtF rsegs RNG Q
            (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                     (Z_to_bv 64 A0) (Z_to_bv 64 (6233088 + 4 * k)) (Z_to_bv 64 N2) (Z_to_bv 64 A3)
                     (Z_to_bv 64 (TW.s32_at Bq (TW.OFF_g_q + 4 * i))) z15 z16 x17
                     (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                     (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
                     (Z_to_bv 64 6157680) (Z_to_bv 64 k) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
                     x28 x29 x30 x31)
                F (Z_to_bv 64 542468) fc None m3 (seg_rom rsegs))).
        { intros z15 z16.
          (* 0x84704: addiw s9,s9,1 *)
          step. rewrite cls_addiw by lia.
          (* 0x84708: sw a4,0(a1): g_q[k] := g_q[i] *)
          assert (HS : store_ok rsegs m3 (wa (6233088 + 4 * k)) 4 = true).
          { apply (cls_wok_store_ok dp m3 (6233088 + 4 * k) 4 HK3); [lia | change (Z.of_nat 4) with 4; lia |].
            intros i' Hi'. change (Z.of_nat 4) with 4 in Hi'. unfold cls_wrange. lia. }
          pose proof HOFF as (O1 & _ & _ & _ & _ & _ & _ & O8 & _ & _). specialize (O8 HL).
          unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in O1.
          pose proof (HOG _ _ (TMAP_A_in_G _ _ _ TMAP_A_g_q)) as Gq. unfold TA_g_q, TW.SZ_g_q in Gq.
          step.
          pose proof (cls_tw_wr4 m3 Bq TW.OFF_g_q TA_g_q TW.SZ_g_q (4 * k) (TW.s32_at Bq (TW.OFF_g_q + 4 * i))
            HW3 TMAP_A_g_q ltac:(lia) ltac:(unfold TW.SZ_g_q; lia)) as HW4.
          unfold TA_g_q in HW4.
          replace (TW.upd Bq (TW.OFF_g_q + 4 * k) (TW.put 4 (TW.s32_at Bq (TW.OFF_g_q + 4 * i))))
            with (TW.set_Q_at Bq k (TW.Q_at Bq i)) in HW4
            by (unfold TW.set_Q_at, TW.Q_at; rewrite cls_put_s32; reflexivity).
          clsr_post_fix_addr HW4.
          clear HW3.
          store_done.
          clear O1 O8 Gq.
          lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
          apply (NEXT (k + 1) (TW.set_Q_at Bq k (TW.Q_at Bq i)) m4);
            [ exact HQ2 | lia | exact FR3 | exact ST3 | exact HW4 | exact DP3 | exact HB3
            | exact AC3 | exact AQ3 | exact AD3 | exact AB3 | exact HK3 | exact MU3 | exact WMo3 | exact MG3 ]. }
        (* 0x846e0-0x846f0: a1 = g_q + 4 k *)
        step. step. step. rewrite cls_shl32_shr30 by lia.
        step. step. rewrite ?(unsigned_lit (4 * k)) by lia.
        (* 0x846f4-0x84700: the check of the 4-byte store at g_q + 4 k *)
        destruct (cls_sh_load m3 6233088 4096 (4 * k) 4 AQ3 ltac:(lia) ltac:(lia) ltac:(lia)) as (kk & MKk & SKk).
        change (4 - 1) with 3 in SKk.
        pose proof (cls_shq RNG (4 * k) RSQ ltac:(lia)) as RKk.
        unfold ASAN_K in MKk, RKk.
        pose proof (rd1 m3 _ _ MKk) as RDk. clear MKk.
        step. rewrite (unsigned_lit (6233088 + 4 * k)) by lia. rewrite cls_shr3.
        step. step.
        step. rewrite sxb_eq0.
        destruct SKk as [C|[C Cu]].
        + rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply BODYC.
        + rewrite (proj2 (Z.eqb_neq (bv_signed kk) 0) ltac:(lia)). cbn [negb]. cbv iota.
          (* 0x84730-0x8473c: the handler goes back to the store *)
          step. step.
          step. rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit (6233088 + 4 * k)) by lia.
          rewrite (cls_lts_lit ((6233088 + 4 * k) mod 8 + 3) kk ltac:(lia)).
          rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
          step. apply BODYC. }
    (* 0x846c8-0x846d4: the check of the 4-byte load at g_q + 4 i *)
    destruct (cls_sh_load m3 6233088 4096 (4 * i) 4 AQ3 ltac:(lia) ltac:(lia) ltac:(lia)) as (kq & MKq & SKq).
    replace (6233088 + 4 * i) with A0 in MKq, SKq by lia.
    change (4 - 1) with 3 in SKq.
    pose proof (cls_shq RNG (4 * i) RSQ ltac:(lia)) as RKq.
    replace (6233088 + 4 * i) with A0 in RKq by lia.
    unfold ASAN_K in MKq, RKq.
    pose proof (rd1 m3 _ _ MKq) as RDkq. clear MKq.
    step. rewrite (unsigned_lit A0) by lia. rewrite cls_shr3.
    step. step.
    step. rewrite sxb_eq0.
    destruct SKq as [C|[C Cu]].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply BODYQ.
    - rewrite (proj2 (Z.eqb_neq (bv_signed kq) 0) ltac:(lia)). cbn [negb]. cbv iota.
      (* 0x84720-0x8472c: the handler goes back to the load *)
      step. step.
      step. rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit A0) by lia.
      rewrite (cls_lts_lit (A0 mod 8 + 3) kq ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
      step. apply BODYQ. }
  (* ---- 0x84668 .. 0x846c4: t->st := SENT, then q_remove or the g_nq store ---- *)
  assert (STT : forall y10 y11 : word,
    ExecF.evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
               y10 y11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 s) (Z_to_bv 64 (6181888 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) (Z_to_bv 64 pos)
               (Z_to_bv 64 6157680) (Z_to_bv 64 (TW.g_nq Bc)) (Z_to_bv 64 6181888) (Z_to_bv 64 6157684)
               x28 x29 x30 x31)
          F (Z_to_bv 64 542312) fc None m (seg_rom rsegs))).
  { intros y10 y11.
    (* 0x84668: li a0,2 *)
    step.
    (* 0x8466c: sw a0,0(s3): t->st := SENT *)
    assert (HS : store_ok rsegs m (wa (6181888 + 40 * s)) 4 = true).
    { apply (cls_wok_store_ok dp m (6181888 + 40 * s) 4 HK); [lia | change (Z.of_nat 4) with 4; lia |].
      intros i Hi. change (Z.of_nat 4) with 4 in Hi. unfold cls_wrange. lia. }
    pose proof HOFF as (O1 & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in O1.
    pose proof (HOG _ _ (TMAP_A_in_G _ _ _ TMAP_A_g_cmd)) as Gc. unfold TA_g_cmd, TW.SZ_g_cmd in Gc.
    pose proof (HOB HL s ltac:(lia)) as Bs.
    step.
    pose proof (cls_tw_wr4 m Bc TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * s) 2 HW TMAP_A_g_cmd ltac:(lia)
      ltac:(unfold TW.SZ_g_cmd; lia)) as HW1.
    unfold TA_g_cmd in HW1.
    replace (TW.upd Bc (TW.OFF_g_cmd + 40 * s) (TW.put 4 2)) with (TW.set_Cmd_st Bc s TC.SENT) in HW1
      by (unfold TW.set_Cmd_st, TW.A_Cmd_st, TC.SENT; rewrite Z.add_0_r; reflexivity).
    clsr_post_fix_addr HW1.
    clear HW.
    store_done.
    clear O1 Gc Bs.
    lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* 0x84670: bnez s9 *)
    step. rewrite cls_eqb0 by lia.
    destruct (Z.eqb_spec (TW.g_nq Bc) 0) as [N0|N0]; cbn [negb]; cbv iota.
    - (* g_nq = 0: q_remove keeps nothing, straight to the g_nq store *)
      destruct (cls_q_exit _ _ _ _ _ _ _ _ HQL ltac:(lia)) as [EB EK].
      apply (TAIL m1 (TW.set_Cmd_st Bc s TC.SENT) (TW.g_nq Bc));
        [ exact (eq_sym EB) | lia | exact FR | exact ST | exact HW1 | exact DPc | exact HB
        | exact AC | exact AQ | exact AD | exact AB | exact HK | exact MU | exact WMo | exact MG ].
    - (* 0x846b4-0x846c4: a2 = g_nq, a0 = a3 = g_q, s9 = 0 *)
      step. step. rewrite clsr_post_shl32_shr32 by lia.
      step. step. step.
      apply (LOOP (S (Z.to_nat TC.CMDS_MAX)) 0 0 (TW.set_Cmd_st Bc s TC.SENT) m1);
        [ exact HQL | lia | lia | lia | lia | lia | exact FR | exact ST | exact HW1 | exact DPc | exact HB
        | exact AC | exact AQ | exact AD | exact AB | exact HK | exact MU | exact WMo | exact MG ]. }
  (* ---- 0x8465c: bnez a0, and a0 = 0 ---- *)
  step.
  try (replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity).
  cbn [negb]. cbv iota.
  (* 0x84660-0x84664: the check of the 4-byte store at t, its shadow byte re-read through s6 *)
  destruct (cls_sh_load m 6181888 40960 (40 * s) 4 AC ltac:(lia) ltac:(lia) ltac:(lia)) as (kt & MKt & SKt).
  change (4 - 1) with 3 in SKt. unfold ASAN_K in MKt.
  pose proof (cls_shc RNG (40 * s) RSC ltac:(lia)) as RKt. unfold ASAN_K in RKt.
  pose proof (rd1 m _ _ MKt) as RDt. clear MKt.
  step.
  step. rewrite sxb_eq0.
  destruct SKt as [C|[C Cu]].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply STT.
  - rewrite (proj2 (Z.eqb_neq (bv_signed kt) 0) ltac:(lia)). cbn [negb]. cbv iota.
    (* 0x84780-0x8478c: the handler goes back to the store *)
    step. step.
    step. rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit (6181888 + 40 * s)) by lia.
    rewrite (cls_lts_lit ((6181888 + 40 * s) mod 8 + 3) kt ltac:(lia)).
    rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
    step. apply STT.
Qed.
