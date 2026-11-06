From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL0g YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU SlotSpec SlotGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Slot verbs_receive_c send_message_c check_round_trip_c rec_calls_free_c VerbsB.
Import ListNotations.
Local Open Scope Z_scope.

(* The invariants of the slot's SR walk (LLVMFuzzerTestOneInput, ubsan 0x14060). *)

Definition G_cmd : list (Z * Z) := FrameAPI.frame_G.

Lemma classic_outside : forall W x, outside W x \/ ~ outside W x.
Proof. intros W x. destruct (KindBGlue.kb_outside_dec W x) as [H|H]; [left | right]; exact H. Qed.

(* The allocator bound. Every callee's post gives res_ok_slots A' b' with the cap of its pre (rcap); before a
   call the bound is re-tightened to the live blocks (tb A), whose count and bytes are bounded by the entry
   blocks, the recorder's blocks O (at most O_MAX after deduplication, each at most LMAX + 2 bytes) and the
   message's own blocks X (at most 3, each at most 2^16 bytes). *)
Definition O_MAX : nat := 104.

Definition bsum (l : list (Z * Z)) : Z := fold_right (fun pn acc => snd pn + acc) 0 l.

Definition tb (A : astate) : sbound := SB (nblocks A) (ubytes A) CAPMAX.

Definition rcap (A : astate) : Prop := exists b', res_ok_slots A b' /\ sb_cap b' = CAPMAX.

Definition zz_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. intros l1 l2. unfold bsum. induction l1 as [|x l1 IH]; cbn [fold_right app]; lia. Qed.

Lemma bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' H. unfold bsum. induction H; cbn [fold_right] in *; lia. Qed.

Lemma bsum_nonneg : forall m, (forall x, In x m -> 0 <= snd x) -> 0 <= bsum m.
Proof.
  unfold bsum. induction m as [|y m IH]; intros H; cbn [fold_right]; [lia|].
  pose proof (H y (or_introl eq_refl)). pose proof (IH (fun x Hx => H x (or_intror Hx))). lia.
Qed.

Lemma bsum_le : forall m c, (forall x, In x m -> snd x <= c) -> bsum m <= Z.of_nat (length m) * c.
Proof.
  unfold bsum. induction m as [|y m IH]; intros c H; cbn [fold_right length]; [lia|].
  pose proof (H y (or_introl eq_refl)). pose proof (IH c (fun x Hx => H x (or_intror Hx))). lia.
Qed.

Lemma bsum_incl : forall l m, List.NoDup l -> incl l m -> (forall x, In x m -> 0 <= snd x) -> bsum l <= bsum m.
Proof.
  induction l as [|x l IH]; intros m Hn Hi Hp.
  - pose proof (bsum_nonneg m Hp). unfold bsum at 1. cbn [fold_right]. lia.
  - inversion Hn as [|? ? Hx Hn']; subst.
    assert (Hxm : In x m) by (apply Hi; left; reflexivity).
    destruct (in_split x m Hxm) as (m1 & m2 & ->).
    assert (Hi' : incl l (m1 ++ m2)).
    { intros y Hy. assert (Hy' : In y (m1 ++ x :: m2)) by (apply Hi; right; exact Hy).
      apply in_app_or in Hy'. apply in_or_app.
      destruct Hy' as [H|[H|H]]; [left; exact H | subst y; contradiction | right; exact H]. }
    assert (Hp' : forall z, In z (m1 ++ m2) -> 0 <= snd z).
    { intros z Hz. apply Hp. apply in_app_or in Hz. apply in_or_app.
      destruct Hz as [Hz|Hz]; [left; exact Hz | right; right; exact Hz]. }
    pose proof (IH (m1 ++ m2) Hn' Hi' Hp') as H. rewrite bsum_app in H. rewrite bsum_app.
    unfold bsum in *. cbn [fold_right] in *. lia.
Qed.

Lemma nodup_app_zz : forall (l l' : list (Z * Z)), List.NoDup l -> List.NoDup l' ->
  (forall a, In a l -> ~ In a l') -> List.NoDup (l ++ l').
Proof.
  induction l as [|x l IH]; intros l' H H' D; cbn [app]; [exact H'|].
  inversion H as [|? ? Hx Hl]; subst. constructor.
  - intros Hin. apply in_app_or in Hin.
    destruct Hin as [Hin|Hin]; [exact (Hx Hin) | exact (D x (or_introl eq_refl) Hin)].
  - apply IH; [exact Hl | exact H' | intros a Ha; apply D; right; exact Ha].
Qed.

(* A duplicate-free l containing E and inside E ++ m (m of nonnegative sizes) has at most E's count and bytes plus
   m's. *)
Lemma bound_split : forall (l E m : list (Z * Z)),
  List.NoDup l -> List.NoDup E -> incl E l -> (forall x, In x l -> In x E \/ In x m) ->
  (forall x, In x m -> 0 <= snd x) ->
  (length l <= length E + length m)%nat /\ bsum l <= bsum E + bsum m.
Proof.
  intros l E m Hl HE Hi Hs Hp.
  set (r := List.filter (fun x => if in_dec zz_dec x E then false else true) l).
  assert (Hr : forall x, In x r <-> In x l /\ ~ In x E).
  { intros x. unfold r. rewrite filter_In.
    destruct (in_dec zz_dec x E) as [Hx|Hx]; split; intros [H1 H2]; split;
      try assumption; try discriminate; try contradiction; try reflexivity. }
  assert (Hrn : List.NoDup r) by (apply NoDup_filter; exact Hl).
  assert (Hperm : Permutation l (E ++ r)).
  { apply NoDup_Permutation; [exact Hl | |].
    - apply nodup_app_zz; [exact HE | exact Hrn |]. intros x Hx1 Hx2. apply Hr in Hx2. tauto.
    - intros x. rewrite in_app_iff, Hr. split.
      + intros H. destruct (in_dec zz_dec x E); tauto.
      + intros [H|[H _]]; [apply Hi; exact H | exact H]. }
  assert (Hrm : incl r m).
  { intros x Hx. apply Hr in Hx as [Hx1 Hx2]. destruct (Hs x Hx1) as [H|H]; [contradiction | exact H]. }
  rewrite (Permutation_length Hperm), length_app, (bsum_perm _ _ Hperm), bsum_app.
  pose proof (NoDup_incl_length Hrn Hrm). pose proof (bsum_incl r m Hrn Hrm Hp). split; lia.
Qed.

Lemma nblocks_blocks : forall L A, nblocks A = Z.of_nat (length (blocks L A)).
Proof. intros L A. unfold nblocks, blocks. rewrite length_map. reflexivity. Qed.

Lemma ubytes_blocks : forall L A, ubytes A = bsum (blocks L A).
Proof.
  intros L A. unfold ubytes, bsum, blocks.
  induction (user_blocks A) as [|x l IH]; cbn [fold_right map snd]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma blocks_nonneg : forall L A, WF A -> forall pn, In pn (blocks L A) -> 0 <= snd pn.
Proof.
  intros L A HW pn Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & <- & Hp). cbn [snd].
  destruct (BlocksNodup.user_block_strict A p n HW Hp) as (rg & _ & _ & _ & _ & Hn & _). exact Hn.
Qed.

Lemma blocks_nodup_list : forall L A, stdpp.base.NoDup (map fst (blocks L A)) -> List.NoDup (blocks L A).
Proof.
  intros L A H. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in H. exact (NoDup_map_inv _ _ H).
Qed.

Lemma res_tb : forall (L : layout) A, WF A -> rcap A -> res_ok_slots A (tb A).
Proof.
  intros L A HW (b' & R & C). pose proof (bsum_nonneg _ (blocks_nonneg L A HW)) as Hu.
  rewrite <- ubytes_blocks in Hu. pose proof (nblocks_blocks L A) as Hn.
  destruct R as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & (R8 & R9) & R10 & R11).
  unfold res_ok_slots, tb. cbn [sb_live sb_bytes sb_cap]. rewrite C in *.
  refine (conj R0 (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 _)))))). repeat split; lia.
Qed.

(* Room before a call: the live blocks are the entry blocks E, recorder blocks O and the message's blocks X. *)
Lemma room_tb : forall L A (E O X : list (Z * Z)) (b : sbound),
  WF A -> List.NoDup (blocks L A) -> List.NoDup E -> incl E (blocks L A) ->
  (forall pn, In pn (blocks L A) -> In pn E \/ In pn (O ++ X)) ->
  Z.of_nat (length E) <= 64 -> bsum E <= 2 ^ 28 ->
  (length O <= O_MAX)%nat -> (forall pn, In pn O -> 0 <= snd pn <= LMAX + 2) ->
  (length X <= 3)%nat -> (forall pn, In pn X -> 0 <= snd pn <= 2 ^ 16) ->
  forall b2, sb_cap b2 = CAPMAX -> 0 <= sb_live b2 <= nblocks A + 200 -> 0 <= sb_bytes b2 <= ubytes A + 2 ^ 22 ->
  forall r, 0 <= r <= 2 ^ 22 -> room_slots b2 r.
Proof.
  intros L A E O X b HW Hl HE Hi Hs HEn HEb HOn HOs HXn HXs b2 Hc Hlv Hby r Hr.
  assert (Hp : forall x, In x (O ++ X) -> 0 <= snd x).
  { intros x Hx. apply in_app_or in Hx as [Hx|Hx]; [apply HOs | apply HXs]; exact Hx. }
  destruct (bound_split (blocks L A) E (O ++ X) Hl HE Hi Hs Hp) as [Hlen Hsum].
  rewrite bsum_app in Hsum. rewrite length_app in Hlen.
  pose proof (bsum_le O (LMAX + 2) (fun x Hx => proj2 (HOs x Hx))) as BO.
  pose proof (bsum_le X (2 ^ 16) (fun x Hx => proj2 (HXs x Hx))) as BX.
  rewrite (nblocks_blocks L A) in Hlv. rewrite (ubytes_blocks L A) in Hby.
  unfold O_MAX, LMAX in *.
  apply room_slots_small; [lia | rewrite Hc; unfold CAPMAX; lia | lia | lia].
Qed.

(* At the end: exactly the entry blocks are live, so the entry bound holds again. *)
Lemma res_end : forall L A L0 A0 b, WF A -> rcap A -> List.NoDup (blocks L A) -> List.NoDup (blocks L0 A0) ->
  (forall pn, In pn (blocks L A) <-> In pn (blocks L0 A0)) -> res_ok_slots A0 b -> sb_cap b = CAPMAX ->
  res_ok_slots A b.
Proof.
  intros L A L0 A0 b HW (b' & R & C) Hl HE Hs R0 Hc.
  destruct (bound_split (blocks L A) (blocks L0 A0) [] Hl HE ltac:(intros x Hx; apply Hs; exact Hx)
              ltac:(intros x Hx; left; apply Hs; exact Hx) ltac:(intros x [])) as [Hlen Hsum].
  cbn [length] in Hlen. rewrite <- (ubytes_blocks L A), <- (ubytes_blocks L0 A0) in Hsum.
  unfold bsum in Hsum. cbn [fold_right] in Hsum.
  pose proof (nblocks_blocks L A) as N1. pose proof (nblocks_blocks L0 A0) as N0.
  destruct R as (S0 & S1 & S2 & S3 & S4 & S5 & S6 & S7 & (S8 & S9) & S10 & S11).
  destruct R0 as (T0 & T1 & T2 & T3 & T4 & T5 & T6 & T7 & (T8 & T9) & T10 & T11).
  unfold res_ok_slots. rewrite Hc. rewrite C in S11.
  refine (conj S0 (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 _)))))). repeat split; lia.
Qed.

Section Inv.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

(* The entry: sp S, registers rg, memory mem0, model md0, the allocator state (L0, A0) and the driver's block
   (p0, n0). *)
Variables (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (L0 : layout) (A0 : astate)
  (p0 n0 : Z).

Definition FB : Z := S - 160.

Definition savecells : list cell :=
  SAVE (getr rg 1) (getr rg 8) (getr rg 9) (getr rg 18) (getr rg 19) (getr rg 20) (getr rg 21) (getr rg 22)
    (getr rg 23) (getr rg 24) (getr rg 25) (getr rg 26) (getr rg 27).

(* The memory outside the slot's stack, the errno word, the allocator's own bytes and G is the entry memory
   (lib_post_g's two frame clauses, kept along the walk). *)
Definition sframe (mem : word -> option byte) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B FrameAPI.SLOT_STACK rg a ->
     mbyte rsegs mem a = mbyte rsegs mem0 a /\ (writable_at rsegs mem0 a <-> writable_at rsegs mem a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G_cmd a ->
     mbyte rsegs mem a = mbyte rsegs mem0 a /\ (writable_at rsegs mem0 a <-> writable_at rsegs mem a)).

(* Every block live at entry is live with its entry bytes. *)
Definition eblocks (L : layout) (A : astate) (mem : word -> option byte) : Prop :=
  forall a k, In (a, k) (blocks L0 A0) ->
    In (a, k) (blocks L A) /\ forall i, 0 <= i < k -> mbyte rsegs mem (a + i) = mbyte rsegs mem0 (a + i).

(* The facts that hold at every boundary of the walk between the prologue and the epilogue. *)
Definition CF (fx : FPState) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm md0) /\
  getr regs 2 = Z_to_bv 64 FB /\ getr regs 3 = getr rg 3 /\ getr regs 4 = getr rg 4 /\
  rw_cells rsegs mem (FB + 56) savecells /\
  (forall a, lib_scratch B FrameAPI.SLOT_STACK rg a -> writable_at rsegs mem a) /\
  sframe mem /\
  ro_agree rsegs mem /\ G_img_c B FrameAPI.frame_RELRO mem /\
  eblocks L A mem /\
  frm_zero (@fp_csr fx).

(* The recorder: g_rec holds R (owning the blocks O), SC holds no call, g_quitting holds q; the entry blocks
   are not the recorder's, and every live block is an entry block or the recorder's. *)
Definition RF (L : layout) (A : astate) (mem : word -> option byte) (R : rstate) (O : list (Z * Z)) (q : Z) : Prop :=
  g_rec_rep rsegs L A mem R O /\ r_spill R = (0, []) /\
  Mem.bytes_at rsegs mem CommandModel.G_QUIT (Mem.le4 (Z_to_bv 64 q)) /\ 0 <= q < 2 ^ 32 /\
  (forall a k, In (a, k) (blocks L0 A0) -> ~ In a (map fst O)) /\
  (forall pn, In pn (blocks L A) -> In pn (blocks L0 A0) \/ In pn O).


(* The loop head 0x140fc of message m at cursor (p, n): s7 = m, s2 = p, s1 = n, s8 = MASK, s9 = 32, s11 = -1,
   a2 = 1, a3 = 58 (the code count), a4 = &g_rec. *)
Definition HI (fx : FPState) (m p n : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (R : rstate) (O : list (Z * Z)) (q : Z) : Prop :=
  CF fx L A regs mem md /\ RF L A mem R O q /\ rcap A /\ (length O <= O_MAX)%nat /\
  getr regs 23 = Z_to_bv 64 m /\ getr regs 18 = Z_to_bv 64 p /\ getr regs 9 = Z_to_bv 64 n /\
  getr regs 24 = Z_to_bv 64 MASK /\ getr regs 25 = Z_to_bv 64 32 /\ getr regs 27 = Z_to_bv 64 (2 ^ 64 - 1) /\
  getr regs 12 = Z_to_bv 64 1 /\ getr regs 13 = Z_to_bv 64 58 /\ getr regs 14 = Z_to_bv 64 CommandModel.G_REC /\
  (exists jsv jw, rw_cells rsegs mem FB (LOC0 jsv) /\ rw_cells rsegs mem (FB + 24) [CB 32 jw]) /\
  0 <= m <= 31 /\ 0 < n /\ p0 <= p /\ p + n = p0 + n0.

(* The entry of the second rec_clear (pc 0x15ab4, returning to 0x143ec). *)
Definition XI (fx : FPState) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (R : rstate) (O : list (Z * Z)) (q : Z) : Prop :=
  CF fx L A regs mem md /\ RF L A mem R O q /\ rcap A /\
  getr regs 1 = Z_to_bv 64 0x143ec.

Section Moves.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B MR.
Hypothesis HS : alloc_ceiling + FrameAPI.SLOT_STACK <= S /\ S < 2 ^ 63.
Hypothesis RG2 : spZ rg = S.

Lemma in_img_low' : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof.
  intros a H. pose proof (in_img_low B SEGS a H). pose proof alloc_ceiling_val. lia.
Qed.

Lemma owned_low' : forall L A mem md a, MR L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof. intros L A mem md a HM Ho. exact (mr_owned_low B MR (aa_laws API) L A mem md a HM Ho). Qed.

Lemma img_not_owned : forall L A mem md a, MR L A mem md -> in_img B a -> ~ static_owned B a ->
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L A a.
Proof.
  intros L A mem md a HM Hi Hs Hc [Ho|Ho]; [|exact (Hs Ho)].
  exact (Hc (ax_img AX L A mem md a HM Hi Ho)).
Qed.

(* A callee's frame clause gives the slot's frame facts back, when the callee's stack lies inside the slot's
   stack and its write set lies in G or in low memory outside the image. *)
Lemma sframe_call : forall K L A regs mem md (E : Z -> Prop) L' A' mem' md',
  MR L A mem md -> MR L' A' mem' md' ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
     ~ scratch_k B K regs a -> ~ E a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
  S - FrameAPI.SLOT_STACK <= spZ regs - K -> spZ regs <= S ->
  (forall a, E a -> in_globals G_cmd a \/ (a < alloc_ceiling /\ ~ in_img B a)) ->
  sframe mem -> sframe mem'.
Proof.
  intros K L A regs mem md E L' A' mem' md' HM HM' HF Hk1 Hk2 HE [F1 F2].
  rewrite SEGS in HF. pose proof alloc_ceiling_val as AC.
  split.
  - intros a Ha Hs. destruct (F1 a Ha Hs) as [E1 W1].
    destruct (HF a (or_introl Ha)) as [E2 W2].
    + intros Ho. pose proof (owned_low' _ _ _ _ _ HM Ho). lia.
    + intros Ho. pose proof (owned_low' _ _ _ _ _ HM' Ho). lia.
    + unfold scratch_k. intros [Hx|Hx]; apply Hs; unfold lib_scratch; [left; rewrite RG2; lia | right; exact Hx].
    + intros He. destruct (HE a He) as [Hg|[Hg _]]; [|lia].
      destruct Hg as (lo & len & Hin & Hr). unfold G_cmd, FrameAPI.frame_G in Hin.
      destruct Hin as [Hin|[]]. injection Hin as <- <-. lia.
    + split; [congruence | tauto].
  - intros a Hi Hs Hc He Hg. destruct (F2 a Hi Hs Hc He Hg) as [E1 W1].
    pose proof (in_img_low' a Hi) as Hl.
    destruct (HF a (or_intror Hi)) as [E2 W2].
    + exact (img_not_owned _ _ _ _ _ HM Hi Hs Hc).
    + exact (img_not_owned _ _ _ _ _ HM' Hi Hs Hc).
    + unfold scratch_k. intros [Hx|Hx]; [lia | exact (He Hx)].
    + intros HEa. destruct (HE a HEa) as [Hg'|[_ Hn]]; [exact (Hg Hg') | exact (Hn Hi)].
    + split; [congruence | tauto].
Qed.

(* The same for a Kind A run whose footprint W lies in the slot's stack, in G, or in low memory outside the
   image. *)
Lemma sframe_munch : forall W mem mem',
  munch W mem mem' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     (S - FrameAPI.SLOT_STACK <= a < S) \/ in_globals G_cmd a \/ (a < alloc_ceiling /\ ~ in_img B a)) ->
  sframe mem -> sframe mem'.
Proof.
  intros W mem mem' HW HO [F1 F2].
  assert (K : forall a, 0 <= a < 2 ^ 64 -> outside W a ->
            mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha Ho. split; [exact (KindB.munch_mbyte rsegs W mem mem' a HW Ha Ho)|].
    exact (KindB.munch_writable rsegs W mem mem' a HW Ha Ho). }
  pose proof alloc_ceiling_val as AC.
  split.
  - intros a Ha Hs. destruct (F1 a Ha Hs) as [E1 W1].
    destruct (classic_outside W a) as [Ho|Ho].
    + destruct (K a ltac:(lia) Ho) as [E2 W2]. split; [congruence | tauto].
    + exfalso. destruct (HO a ltac:(lia) Ho) as [Hx|[Hx|[Hx _]]].
      * apply Hs. unfold lib_scratch. left. rewrite RG2. unfold FrameAPI.SLOT_STACK in *. lia.
      * destruct Hx as (lo & len & Hin & Hr). unfold G_cmd, FrameAPI.frame_G in Hin.
        destruct Hin as [Hin|[]]. injection Hin as <- <-. lia.
      * lia.
  - intros a Hi Hs Hc He Hg. destruct (F2 a Hi Hs Hc He Hg) as [E1 W1].
    pose proof (in_img_low' a Hi) as Hl.
    destruct (classic_outside W a) as [Ho|Ho].
    + destruct (K a ltac:(lia) Ho) as [E2 W2]. split; [congruence | tauto].
    + exfalso. destruct (HO a ltac:(lia) Ho) as [Hx|[Hx|[_ Hx]]]; [unfold FrameAPI.SLOT_STACK in *; lia | exact (Hg Hx) | exact (Hx Hi)].
Qed.


Lemma vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma spZ_FB : forall regs, getr regs 2 = Z_to_bv 64 FB -> spZ regs = FB.
Proof.
  intros regs H. unfold spZ. rewrite H. apply unsigned_lit. pose proof alloc_ceiling_val.
  unfold FB, FrameAPI.SLOT_STACK in *. lia.
Qed.

(* CF after a Kind B call made at the slot's frame base. *)
Lemma cf_call : forall fx fx' K L A regs mem md (E : Z -> Prop) L' A' regs' mem' md' regs'',
  CF fx L A regs mem md ->
  MR L' A' mem' md' -> WF A' -> bounded A' -> st_init_done A' = true ->
  regs_preserved regs regs' -> (exists vm', md' = with_vmmaps vm' md) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
     ~ scratch_k B K regs a -> ~ E a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
  (forall a, scratch_k B K regs a -> writable_at (ms_segs B) mem' a) ->
  S - FrameAPI.SLOT_STACK <= FB - K -> 0 <= K ->
  (forall a, E a -> in_globals G_cmd a \/ (a < alloc_ceiling /\ ~ in_img B a)) ->
  ro_agree rsegs mem' -> G_img_c B FrameAPI.frame_RELRO mem' -> eblocks L' A' mem' -> frm_zero (@fp_csr fx') ->
  (forall r, getr regs'' r = getr regs' r) ->
  CF fx' L' A' regs'' mem' md'.
Proof.
  intros fx fx' K L A regs mem md E L' A' regs' mem' md' regs''
    (M & W & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GI & EB & FZ)
    M' W' Bd' I' PR (vm' & Hmd') HF HSc HK1 HK2 HE RO' GI' EB' FZ' RR.
  pose proof alloc_ceiling_val as AC. unfold FrameAPI.SLOT_STACK in *.
  pose proof (spZ_FB regs R2) as SP.
  assert (HFB : FB = S - 160) by reflexivity.
  assert (NE : forall a, alloc_ceiling <= a -> ~ E a).
  { intros a Ha He. destruct (HE a He) as [Hg|[Hg _]]; [|lia].
    destruct Hg as (lo & len & Hin & Hr). unfold G_cmd, FrameAPI.frame_G in Hin.
    destruct Hin as [Hin|[]]. injection Hin as <- <-. lia. }
  assert (HI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (FB - K <= a < FB) ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha Hk. rewrite <- SEGS. apply HF; [left; exact Ha | | | | apply NE; lia].
    - intros Ho. pose proof (owned_low' _ _ _ _ _ M Ho). lia.
    - intros Ho. pose proof (owned_low' _ _ _ _ _ M' Ho). lia.
    - unfold scratch_k. rewrite SP. intros [Hx|Hx]; [exact (Hk Hx) | lia]. }
  split; [exact M'|]. split; [exact W'|]. split; [exact Bd'|]. split; [exact I'|].
  split; [exists vm'; rewrite Hmd', Hmd; apply vm_twice|].
  split; [exact (eq_trans (RR (Z_to_bv 5 2)) (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) R2))|].
  split; [exact (eq_trans (RR (Z_to_bv 5 3)) (eq_trans (PR 3 ltac:(unfold callee_saved; lia)) R3))|].
  split; [exact (eq_trans (RR (Z_to_bv 5 4)) (eq_trans (PR 4 ltac:(unfold callee_saved; lia)) R4))|].
  split.
  { apply (rw_cells_transfer rsegs mem); [exact SV|]. intros i Hi. unfold savecells, SAVE in Hi. cbn in Hi.
    destruct (HI (FB + 56 + i)) as [E1 W1]; [lia | lia |]. split; [exact E1 | tauto]. }
  split.
  { intros a Ha. destruct (Z_le_gt_dec (FB - K) a) as [H1|H1];
      [destruct (Z_lt_ge_dec a FB) as [H2|H2]|].
    - rewrite <- SEGS. apply HSc. unfold scratch_k. left. rewrite SP. lia.
    - destruct Ha as [Ha|Ha]; [|rewrite <- SEGS; apply HSc; right; exact Ha].
      unfold lib_scratch, FrameAPI.SLOT_STACK in *. rewrite RG2 in Ha.
      destruct (HI a ltac:(lia) ltac:(lia)) as [_ W1]. apply W1. apply SW. left. rewrite RG2. exact Ha.
    - destruct Ha as [Ha|Ha]; [|rewrite <- SEGS; apply HSc; right; exact Ha].
      unfold lib_scratch, FrameAPI.SLOT_STACK in *. rewrite RG2 in Ha.
      assert (Ha1 : alloc_ceiling <= a < 2 ^ 64) by lia. assert (Ha2 : ~ (FB - K <= a < FB)) by lia.
      destruct (HI a Ha1 Ha2) as [_ W1]. apply W1. apply SW. left. rewrite RG2. exact Ha. }
  split; [apply (sframe_call K L A regs mem md E L' A' mem' md' M M' HF); [rewrite SP; unfold FrameAPI.SLOT_STACK; lia | rewrite SP; lia | exact HE | exact SF]|].
  split; [exact RO'|]. split; [exact GI'|]. split; [exact EB'|]. exact FZ'.
Qed.

Lemma blocks_range : forall L A mem md a k, MR L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros L A mem md a k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn in Eq. injection Eq as <- <-. exact (mr_blocks_range B MR (aa_laws API) L A mem md q k' HM Hq).
Qed.

Lemma relro_in_img : forall a, in_globals FrameAPI.frame_RELRO a -> in_img B a.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (H : existsb (fun s => (bv_unsigned (fst s) <=? lo) && (lo + len <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
                (segments_reserved rsegs) = true)
    by (destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-; vm_compute; reflexivity).
  apply existsb_exists in H as (sg & Hs & Hc). apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite SEGS; discriminate|]. exists sg. rewrite SEGS. split; [exact Hs | lia].
Qed.

Hypothesis GFREE : forall a, in_globals G_cmd a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GNOWN : forall L A mem md a, MR L A mem md -> in_globals G_cmd a -> ~ owned B L A a.

Lemma blocks_not_img : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn in Eq. injection Eq as <- <-. exact (ax_blocks_img AX L A mem md q k' i HM Hq Hi).
Qed.

(* CF after a Kind A run of footprint W (the stack below the saved registers, G, and low memory outside the
   image, the allocator's bytes and the entry blocks); the blocks it writes stay present. *)
Lemma cf_run : forall fx fx' L A regs mem md W mem' regs',
  CF fx L A regs mem md -> munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     (S - FrameAPI.SLOT_STACK <= a < FB + 56) \/ in_globals G_cmd a \/
     (a < alloc_ceiling /\ ~ in_img B a /\ ~ owned B L A a /\
      forall a0 k, In (a0, k) (blocks L0 A0) -> ~ (a0 <= a < a0 + k))) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ outside W (ptr_addr L p + i) ->
     present mem' (ptr_addr L p + i)) ->
  frm_zero (@fp_csr fx') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  CF fx' L A regs' mem' md.
Proof.
  intros fx fx' L A regs mem md W mem' regs'
    (M & Wf & Bd & I & Hmd & R2 & R3 & R4 & SV & SW & SF & RO & GI & EB & FZ) MU WM RO' HW HP FZ' E2 E3 E4.
  pose proof alloc_ceiling_val as AC. unfold FrameAPI.SLOT_STACK in *.
  assert (HFB : FB = S - 160) by reflexivity.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> outside W a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Ho. apply MU. rewrite unsigned_lit by lia. exact Ho. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> outside W a ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha Ho. split; [exact (KindB.munch_mbyte rsegs W mem mem' a MU Ha Ho)|].
    exact (KindB.munch_writable rsegs W mem mem' a MU Ha Ho). }
  assert (OW : forall a, owned B L A a -> outside W a).
  { intros a Ho. pose proof (owned_low' _ _ _ _ _ M Ho) as Hl.
    destruct (classic_outside W a) as [H|H]; [exact H|]. exfalso.
    destruct (HW a ltac:(lia) H) as [Hx|[Hx|(_ & _ & Hx & _)]]; [lia | exact (GNOWN _ _ _ _ _ M Hx Ho) | exact (Hx Ho)]. }
  split.
  { apply (mr_frame B MR (aa_laws API) L A mem mem' md md M).
    - intros a Ho. pose proof (owned_low' _ _ _ _ _ M Ho). unfold mbyte. rewrite KEEP; [reflexivity | lia | exact (OW a Ho)].
    - intros a Ho [bb Hb]. pose proof (owned_low' _ _ _ _ _ M Ho). exists bb. rewrite KEEP; [exact Hb | lia | exact (OW a Ho)].
    - intros p n i Hin Hi. destruct (mr_blocks B MR (aa_laws API) L A mem md p n i M Hin Hi) as (Hp & H1 & H2 & _).
      destruct (classic_outside W (ptr_addr L p + i)) as [Ho|Ho].
      + destruct Hp as [bb Hb]. exists bb. rewrite KEEP; [exact Hb | lia | exact Ho].
      + exact (HP p n i Hin Hi Ho).
    - reflexivity.
    - exact (proj1 (mr_model B MR (aa_laws API) L A mem md M)).
    - exact (proj1 (proj2 (mr_model B MR (aa_laws API) L A mem md M))).
    - exact (proj2 (proj2 (mr_model B MR (aa_laws API) L A mem md M))). }
  split; [exact Wf|]. split; [exact Bd|]. split; [exact I|]. split; [exact Hmd|].
  split; [rewrite E2; exact R2|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
  split.
  { apply (rw_cells_transfer rsegs mem); [exact SV|]. intros i Hi. unfold savecells, SAVE in Hi. cbn in Hi.
    assert (Ho : outside W (FB + 56 + i)).
    { destruct (classic_outside W (FB + 56 + i)) as [H|H]; [exact H|]. exfalso.
      destruct (HW (FB + 56 + i) ltac:(lia) H) as [Hx|[Hx|(Hx & _)]]; [lia | | lia].
      destruct Hx as (lo & len & Hin & Hr). unfold G_cmd, FrameAPI.frame_G in Hin.
      destruct Hin as [Hin|[]]. injection Hin as <- <-. unfold FB in *. lia. }
    destruct (KB (FB + 56 + i) ltac:(lia) Ho) as [E1 W1]. split; [exact E1 | tauto]. }
  split; [intros a Ha; apply WM; exact (SW a Ha)|].
  split.
  { apply (sframe_munch W mem mem' MU); [|exact SF]. intros a Ha Ho.
    destruct (HW a Ha Ho) as [Hx|[Hx|(Hx & Hy & _)]]; [left; unfold FrameAPI.SLOT_STACK; lia | right; left; exact Hx | right; right; split; assumption]. }
  split; [exact RO'|].
  split.
  { intros a Ha. rewrite <- (GI a Ha).
    pose proof (in_img_low' a (relro_in_img a Ha)) as Hl.
    assert (Ho : outside W a).
    { destruct (classic_outside W a) as [H|H]; [exact H|]. exfalso.
      destruct (HW a ltac:(lia) H) as [Hx|[Hx|(_ & Hx & _)]]; [lia | | exact (Hx (relro_in_img a Ha))].
      destruct Hx as (lo & len & Hin & Hr). unfold G_cmd, FrameAPI.frame_G in Hin.
      destruct Hin as [Hin|[]]. injection Hin as <- <-.
      destruct Ha as (lo' & len' & Hin' & Hr'). destruct Hin' as [Hin'|[Hin'|[]]]; injection Hin' as <- <-; lia. }
    rewrite SEGS. exact (proj1 (KB a ltac:(lia) Ho)). }
  split.
  { intros a k Hin. destruct (EB a k Hin) as [Hb Hk]. split; [exact Hb|]. intros i Hi.
    destruct (blocks_range _ _ _ _ _ _ M Hb) as [Hr1 Hr2].
    assert (Ho : outside W (a + i)).
    { destruct (classic_outside W (a + i)) as [H|H]; [exact H|]. exfalso.
      destruct (HW (a + i) ltac:(lia) H) as [Hx|[Hx|(_ & _ & _ & Hx)]]; [lia | | exact (Hx a k Hin ltac:(lia))].
      exact (blocks_not_img _ _ _ _ _ _ _ M Hb Hi (proj1 (GFREE _ Hx))). }
    rewrite (proj1 (KB (a + i) ltac:(lia) Ho)). exact (Hk i Hi). }
  exact FZ'.
Qed.

End Moves.
End Inv.
