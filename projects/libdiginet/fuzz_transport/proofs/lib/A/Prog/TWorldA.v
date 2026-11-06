(* Image A (fuzz_transport.asan e89be137db17): the table TMAP_A of the world relation (A/Prog/TWorldG.v), one row
   per harness global: (offset in the plain world, base in image A, payload length).
   Bases and payload lengths are image A's own asan_globals descriptors (beg, size; section asan_globals, descriptors
   at 0xa8ec0 .. 0xa9300), equal to the globals' st_value in the image's unstripped twin (86efc3a80314, the same
   allocated sections but the build-id note); a global's symbol size there is the descriptor's size_with_redzone.
   Offsets are TWorld.v's. Payload = TWorld's SZ, except g_fail_next: ONE byte (descriptor size 1); its SZ 4 in the
   world is the byte and 3 bytes of plain padding. The DWARF member layout of every global is the same in the plain,
   ubsan, asan and asan-ubsan builds, so a member at offset d of a global is at base + d here and at OFF + d in the
   world. In address order: g_cfg 0x5df080, g_raw, g_now, g_fail_next, g_last_counter, M, g_nq, g_ncmd, g_rx, g_s,
   GOT, g_rx_send, g_cmd, g_q, g_rx_fail, g_rx_times, g_rx_len, OW 0x5f3060 (payload ends at 0x5f3190).
   Lemmas: TMAP_A_ok (tw_ok, decided), TMAP_A_rows (its world column is TW_ROWS), TMAP_A_acc (every world reader's
   footprint inside one row), TMAP_A_cover, the In fact of each row (TMAP_A_<global>), tw_exists_A; against image A's
   G ranges (A/TransportG.v): TMAP_A_in_G (each row's payload range is a range of G_HARNESS), TMAP_A_G_rows (each
   range of G_HARNESS is a row's payload range), tw_kept_GA (the bytes of G_HARNESS unchanged keep the world),
   TMAP_A_hull (every payload byte in [G_HARNESS_LO, G_HARNESS_HI)), TMAP_A_kept (at the machine's view
   fun a => option_map bv_unsigned (mrd segs m (wa a)): a run that writes only [lo, hi), outside that hull, keeps
   the world: the post of a leaf whose frame lies outside the hull). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import TransportG.
Import ListNotations.
Open Scope Z_scope.

Definition TA_M : Z := 0x5df160.
Definition TA_g_s : Z := 0x5df9c0.
Definition TA_g_cmd : Z := 0x5e5400.
Definition TA_g_q : Z := 0x5f1c00.
Definition TA_g_fail_next : Z := 0x5df120.
Definition TA_g_raw : Z := 0x5df0e0.
Definition TA_g_last_counter : Z := 0x5df140.
Definition TA_g_nq : Z := 0x5df960.
Definition TA_g_ncmd : Z := 0x5df980.
Definition TA_g_rx_send : Z := 0x5e53e0.
Definition TA_g_rx_fail : Z := 0x5f3000.
Definition TA_g_rx_times : Z := 0x5f3020.
Definition TA_g_now : Z := 0x5df100.
Definition TA_g_rx : Z := 0x5df9a0.
Definition TA_g_rx_len : Z := 0x5f3040.
Definition TA_g_cfg : Z := 0x5df080.
Definition TA_GOT : Z := 0x5e52e0.
Definition TA_OW : Z := 0x5f3060.
Definition TMAP_A : list (Z * Z * Z) := [
  (OFF_M, TA_M, SZ_M);
  (OFF_g_s, TA_g_s, SZ_g_s);
  (OFF_g_cmd, TA_g_cmd, SZ_g_cmd);
  (OFF_g_q, TA_g_q, SZ_g_q);
  (OFF_g_fail_next, TA_g_fail_next, 1);
  (OFF_g_raw, TA_g_raw, SZ_g_raw);
  (OFF_g_last_counter, TA_g_last_counter, SZ_g_last_counter);
  (OFF_g_nq, TA_g_nq, SZ_g_nq);
  (OFF_g_ncmd, TA_g_ncmd, SZ_g_ncmd);
  (OFF_g_rx_send, TA_g_rx_send, SZ_g_rx_send);
  (OFF_g_rx_fail, TA_g_rx_fail, SZ_g_rx_fail);
  (OFF_g_rx_times, TA_g_rx_times, SZ_g_rx_times);
  (OFF_g_now, TA_g_now, SZ_g_now);
  (OFF_g_rx, TA_g_rx, SZ_g_rx);
  (OFF_g_rx_len, TA_g_rx_len, SZ_g_rx_len);
  (OFF_g_cfg, TA_g_cfg, SZ_g_cfg);
  (OFF_GOT, TA_GOT, SZ_GOT);
  (OFF_OW, TA_OW, SZ_OW)
].

Lemma TMAP_A_ok : tw_ok TMAP_A.
Proof. apply tw_okb_ok. vm_compute. reflexivity. Qed.

Lemma TMAP_A_rows : map tw_wrow TMAP_A = TW_ROWS.
Proof. reflexivity. Qed.

Lemma TMAP_A_acc : forall a w, In (a, w) TW_ACC -> exists o b n, In (o, b, n) TMAP_A /\ o <= a /\ a + w <= o + n.
Proof. exact (tw_acc_row TMAP_A TMAP_A_rows). Qed.

Lemma TMAP_A_cover : forall x, 0 <= x < W_LEN -> ~ tw_pad x -> exists o b n, In (o, b, n) TMAP_A /\ o <= x < o + n.
Proof. exact (tw_cover TMAP_A TMAP_A_rows). Qed.

Lemma TMAP_A_M : In (OFF_M, TA_M, SZ_M) TMAP_A.
Proof. unfold TMAP_A. left; reflexivity. Qed.
Lemma TMAP_A_g_s : In (OFF_g_s, TA_g_s, SZ_g_s) TMAP_A.
Proof. unfold TMAP_A. do 1 right; left; reflexivity. Qed.
Lemma TMAP_A_g_cmd : In (OFF_g_cmd, TA_g_cmd, SZ_g_cmd) TMAP_A.
Proof. unfold TMAP_A. do 2 right; left; reflexivity. Qed.
Lemma TMAP_A_g_q : In (OFF_g_q, TA_g_q, SZ_g_q) TMAP_A.
Proof. unfold TMAP_A. do 3 right; left; reflexivity. Qed.
Lemma TMAP_A_g_fail_next : In (OFF_g_fail_next, TA_g_fail_next, 1) TMAP_A.
Proof. unfold TMAP_A. do 4 right; left; reflexivity. Qed.
Lemma TMAP_A_g_raw : In (OFF_g_raw, TA_g_raw, SZ_g_raw) TMAP_A.
Proof. unfold TMAP_A. do 5 right; left; reflexivity. Qed.
Lemma TMAP_A_g_last_counter : In (OFF_g_last_counter, TA_g_last_counter, SZ_g_last_counter) TMAP_A.
Proof. unfold TMAP_A. do 6 right; left; reflexivity. Qed.
Lemma TMAP_A_g_nq : In (OFF_g_nq, TA_g_nq, SZ_g_nq) TMAP_A.
Proof. unfold TMAP_A. do 7 right; left; reflexivity. Qed.
Lemma TMAP_A_g_ncmd : In (OFF_g_ncmd, TA_g_ncmd, SZ_g_ncmd) TMAP_A.
Proof. unfold TMAP_A. do 8 right; left; reflexivity. Qed.
Lemma TMAP_A_g_rx_send : In (OFF_g_rx_send, TA_g_rx_send, SZ_g_rx_send) TMAP_A.
Proof. unfold TMAP_A. do 9 right; left; reflexivity. Qed.
Lemma TMAP_A_g_rx_fail : In (OFF_g_rx_fail, TA_g_rx_fail, SZ_g_rx_fail) TMAP_A.
Proof. unfold TMAP_A. do 10 right; left; reflexivity. Qed.
Lemma TMAP_A_g_rx_times : In (OFF_g_rx_times, TA_g_rx_times, SZ_g_rx_times) TMAP_A.
Proof. unfold TMAP_A. do 11 right; left; reflexivity. Qed.
Lemma TMAP_A_g_now : In (OFF_g_now, TA_g_now, SZ_g_now) TMAP_A.
Proof. unfold TMAP_A. do 12 right; left; reflexivity. Qed.
Lemma TMAP_A_g_rx : In (OFF_g_rx, TA_g_rx, SZ_g_rx) TMAP_A.
Proof. unfold TMAP_A. do 13 right; left; reflexivity. Qed.
Lemma TMAP_A_g_rx_len : In (OFF_g_rx_len, TA_g_rx_len, SZ_g_rx_len) TMAP_A.
Proof. unfold TMAP_A. do 14 right; left; reflexivity. Qed.
Lemma TMAP_A_g_cfg : In (OFF_g_cfg, TA_g_cfg, SZ_g_cfg) TMAP_A.
Proof. unfold TMAP_A. do 15 right; left; reflexivity. Qed.
Lemma TMAP_A_GOT : In (OFF_GOT, TA_GOT, SZ_GOT) TMAP_A.
Proof. unfold TMAP_A. do 16 right; left; reflexivity. Qed.
Lemma TMAP_A_OW : In (OFF_OW, TA_OW, SZ_OW) TMAP_A.
Proof. unfold TMAP_A. do 17 right; left; reflexivity. Qed.

Lemma tw_exists_A : forall rd,
  (forall o b n i, In (o, b, n) TMAP_A -> 0 <= i < n -> exists v, rd (b + i) = Some v /\ 0 <= v < 256) ->
  exists Bw, tw_at TMAP_A rd Bw.
Proof. intros rd H. exact (tw_exists TMAP_A rd TMAP_A_ok H). Qed.

Lemma TMAP_A_in_G : forall o b n, In (o, b, n) TMAP_A -> In (b, n) G_HARNESS.
Proof. apply tw_in_G_of. vm_compute. reflexivity. Qed.

Lemma TMAP_A_G_rows : forall b n, In (b, n) G_HARNESS -> exists o, In (o, b, n) TMAP_A.
Proof. apply tw_G_rows_of. vm_compute. reflexivity. Qed.

Lemma tw_kept_GA : forall rd rd' Bw, tw_at TMAP_A rd Bw ->
  (forall b n i, In (b, n) G_HARNESS -> 0 <= i < n -> rd' (b + i) = rd (b + i)) -> tw_at TMAP_A rd' Bw.
Proof. intros rd rd' Bw H Hk. exact (tw_kept_G TMAP_A G_HARNESS rd rd' Bw TMAP_A_in_G H Hk). Qed.

Lemma TMAP_A_hull : forall x, tw_in TMAP_A x -> G_HARNESS_LO <= x < G_HARNESS_HI.
Proof.
  intros x (o & b & n & Hin & Hx). pose proof (G_HARNESS_in_hull (b, n) (TMAP_A_in_G o b n Hin)) as H.
  cbn [fst snd] in H. lia.
Qed.

Lemma TMAP_A_kept {segs : list Segment} : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_A (fun a => option_map (fun x : byte => bv_unsigned x) (mrd segs m (wa a))) Bw ->
  munch [(lo, hi)] m m' -> (hi <= G_HARNESS_LO \/ G_HARNESS_HI <= lo) ->
  tw_at TMAP_A (fun a => option_map (fun x : byte => bv_unsigned x) (mrd segs m' (wa a))) Bw.
Proof.
  intros m m' lo hi Bw H MU D. apply (tw_kept_munch segs m m' TMAP_A _ Bw TMAP_A_ok H MU).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. cbn [outside]. split; [lia | exact I].
Qed.
