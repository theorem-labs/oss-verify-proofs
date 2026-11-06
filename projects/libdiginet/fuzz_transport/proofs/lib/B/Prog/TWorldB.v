(* Image B (fuzz_transport.asan-ubsan 41113a03c82f): the table TMAP_B of the world relation (A/Prog/TWorldG.v), one
   row per harness global: (offset in the plain world, base in image B, payload length).
   Bases and payload lengths are image B's own asan_globals descriptors (beg, size; section asan_globals, descriptors
   at 0xa8b20 .. 0xa8f60), equal to the globals' st_value in the image's unstripped twin (e217cb0a84f1, the same
   allocated sections but the build-id note); a global's symbol size there is the descriptor's size_with_redzone.
   Offsets are TWorld.v's. Payload = TWorld's SZ, except g_fail_next: ONE byte (descriptor size 1); its SZ 4 in the
   world is the byte and 3 bytes of plain padding. The DWARF member layout of every global is the same in the plain,
   ubsan, asan and asan-ubsan builds, so a member at offset d of a global is at base + d here and at OFF + d in the
   world. In address order: g_cfg 0x5ded00, g_raw, g_now, g_fail_next, g_last_counter, M, g_nq, g_ncmd, g_rx, g_s,
   GOT, g_rx_send, g_cmd, g_q, g_rx_fail, g_rx_times, g_rx_len, OW 0x5f2ce0 (payload ends at 0x5f2e10).
   Lemmas: TMAP_B_ok (tw_ok, decided), TMAP_B_rows (its world column is TW_ROWS), TMAP_B_acc (every world reader's
   footprint inside one row), TMAP_B_cover, the In fact of each row (TMAP_B_<global>), tw_exists_B; against image B's
   G ranges (B/TransportGB.v): TMAP_B_in_G (each row's payload range is a range of G_HARNESS_B), TMAP_B_G_rows (each
   range of G_HARNESS_B is a row's payload range), tw_kept_GB (the bytes of G_HARNESS_B unchanged keep the world),
   TMAP_B_hull (every payload byte in [G_HARNESS_B_LO, G_HARNESS_B_HI)), TMAP_B_kept (at the machine's view
   fun a => option_map bv_unsigned (mrd segs m (wa a)): a run that writes only [lo, hi), outside that hull, keeps
   the world: the post of a leaf whose frame lies outside the hull). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
Import ListNotations.
Open Scope Z_scope.

Definition TB_M : Z := 0x5dede0.
Definition TB_g_s : Z := 0x5df640.
Definition TB_g_cmd : Z := 0x5e5080.
Definition TB_g_q : Z := 0x5f1880.
Definition TB_g_fail_next : Z := 0x5deda0.
Definition TB_g_raw : Z := 0x5ded60.
Definition TB_g_last_counter : Z := 0x5dedc0.
Definition TB_g_nq : Z := 0x5df5e0.
Definition TB_g_ncmd : Z := 0x5df600.
Definition TB_g_rx_send : Z := 0x5e5060.
Definition TB_g_rx_fail : Z := 0x5f2c80.
Definition TB_g_rx_times : Z := 0x5f2ca0.
Definition TB_g_now : Z := 0x5ded80.
Definition TB_g_rx : Z := 0x5df620.
Definition TB_g_rx_len : Z := 0x5f2cc0.
Definition TB_g_cfg : Z := 0x5ded00.
Definition TB_GOT : Z := 0x5e4f60.
Definition TB_OW : Z := 0x5f2ce0.
Definition TMAP_B : list (Z * Z * Z) := [
  (OFF_M, TB_M, SZ_M);
  (OFF_g_s, TB_g_s, SZ_g_s);
  (OFF_g_cmd, TB_g_cmd, SZ_g_cmd);
  (OFF_g_q, TB_g_q, SZ_g_q);
  (OFF_g_fail_next, TB_g_fail_next, 1);
  (OFF_g_raw, TB_g_raw, SZ_g_raw);
  (OFF_g_last_counter, TB_g_last_counter, SZ_g_last_counter);
  (OFF_g_nq, TB_g_nq, SZ_g_nq);
  (OFF_g_ncmd, TB_g_ncmd, SZ_g_ncmd);
  (OFF_g_rx_send, TB_g_rx_send, SZ_g_rx_send);
  (OFF_g_rx_fail, TB_g_rx_fail, SZ_g_rx_fail);
  (OFF_g_rx_times, TB_g_rx_times, SZ_g_rx_times);
  (OFF_g_now, TB_g_now, SZ_g_now);
  (OFF_g_rx, TB_g_rx, SZ_g_rx);
  (OFF_g_rx_len, TB_g_rx_len, SZ_g_rx_len);
  (OFF_g_cfg, TB_g_cfg, SZ_g_cfg);
  (OFF_GOT, TB_GOT, SZ_GOT);
  (OFF_OW, TB_OW, SZ_OW)
].

Lemma TMAP_B_ok : tw_ok TMAP_B.
Proof. apply tw_okb_ok. vm_compute. reflexivity. Qed.

Lemma TMAP_B_rows : map tw_wrow TMAP_B = TW_ROWS.
Proof. reflexivity. Qed.

Lemma TMAP_B_acc : forall a w, In (a, w) TW_ACC -> exists o b n, In (o, b, n) TMAP_B /\ o <= a /\ a + w <= o + n.
Proof. exact (tw_acc_row TMAP_B TMAP_B_rows). Qed.

Lemma TMAP_B_cover : forall x, 0 <= x < W_LEN -> ~ tw_pad x -> exists o b n, In (o, b, n) TMAP_B /\ o <= x < o + n.
Proof. exact (tw_cover TMAP_B TMAP_B_rows). Qed.

Lemma TMAP_B_M : In (OFF_M, TB_M, SZ_M) TMAP_B.
Proof. unfold TMAP_B. left; reflexivity. Qed.
Lemma TMAP_B_g_s : In (OFF_g_s, TB_g_s, SZ_g_s) TMAP_B.
Proof. unfold TMAP_B. do 1 right; left; reflexivity. Qed.
Lemma TMAP_B_g_cmd : In (OFF_g_cmd, TB_g_cmd, SZ_g_cmd) TMAP_B.
Proof. unfold TMAP_B. do 2 right; left; reflexivity. Qed.
Lemma TMAP_B_g_q : In (OFF_g_q, TB_g_q, SZ_g_q) TMAP_B.
Proof. unfold TMAP_B. do 3 right; left; reflexivity. Qed.
Lemma TMAP_B_g_fail_next : In (OFF_g_fail_next, TB_g_fail_next, 1) TMAP_B.
Proof. unfold TMAP_B. do 4 right; left; reflexivity. Qed.
Lemma TMAP_B_g_raw : In (OFF_g_raw, TB_g_raw, SZ_g_raw) TMAP_B.
Proof. unfold TMAP_B. do 5 right; left; reflexivity. Qed.
Lemma TMAP_B_g_last_counter : In (OFF_g_last_counter, TB_g_last_counter, SZ_g_last_counter) TMAP_B.
Proof. unfold TMAP_B. do 6 right; left; reflexivity. Qed.
Lemma TMAP_B_g_nq : In (OFF_g_nq, TB_g_nq, SZ_g_nq) TMAP_B.
Proof. unfold TMAP_B. do 7 right; left; reflexivity. Qed.
Lemma TMAP_B_g_ncmd : In (OFF_g_ncmd, TB_g_ncmd, SZ_g_ncmd) TMAP_B.
Proof. unfold TMAP_B. do 8 right; left; reflexivity. Qed.
Lemma TMAP_B_g_rx_send : In (OFF_g_rx_send, TB_g_rx_send, SZ_g_rx_send) TMAP_B.
Proof. unfold TMAP_B. do 9 right; left; reflexivity. Qed.
Lemma TMAP_B_g_rx_fail : In (OFF_g_rx_fail, TB_g_rx_fail, SZ_g_rx_fail) TMAP_B.
Proof. unfold TMAP_B. do 10 right; left; reflexivity. Qed.
Lemma TMAP_B_g_rx_times : In (OFF_g_rx_times, TB_g_rx_times, SZ_g_rx_times) TMAP_B.
Proof. unfold TMAP_B. do 11 right; left; reflexivity. Qed.
Lemma TMAP_B_g_now : In (OFF_g_now, TB_g_now, SZ_g_now) TMAP_B.
Proof. unfold TMAP_B. do 12 right; left; reflexivity. Qed.
Lemma TMAP_B_g_rx : In (OFF_g_rx, TB_g_rx, SZ_g_rx) TMAP_B.
Proof. unfold TMAP_B. do 13 right; left; reflexivity. Qed.
Lemma TMAP_B_g_rx_len : In (OFF_g_rx_len, TB_g_rx_len, SZ_g_rx_len) TMAP_B.
Proof. unfold TMAP_B. do 14 right; left; reflexivity. Qed.
Lemma TMAP_B_g_cfg : In (OFF_g_cfg, TB_g_cfg, SZ_g_cfg) TMAP_B.
Proof. unfold TMAP_B. do 15 right; left; reflexivity. Qed.
Lemma TMAP_B_GOT : In (OFF_GOT, TB_GOT, SZ_GOT) TMAP_B.
Proof. unfold TMAP_B. do 16 right; left; reflexivity. Qed.
Lemma TMAP_B_OW : In (OFF_OW, TB_OW, SZ_OW) TMAP_B.
Proof. unfold TMAP_B. do 17 right; left; reflexivity. Qed.

Lemma tw_exists_B : forall rd,
  (forall o b n i, In (o, b, n) TMAP_B -> 0 <= i < n -> exists v, rd (b + i) = Some v /\ 0 <= v < 256) ->
  exists Bw, tw_at TMAP_B rd Bw.
Proof. intros rd H. exact (tw_exists TMAP_B rd TMAP_B_ok H). Qed.

Lemma TMAP_B_in_G : forall o b n, In (o, b, n) TMAP_B -> In (b, n) G_HARNESS_B.
Proof. apply tw_in_G_of. vm_compute. reflexivity. Qed.

Lemma TMAP_B_G_rows : forall b n, In (b, n) G_HARNESS_B -> exists o, In (o, b, n) TMAP_B.
Proof. apply tw_G_rows_of. vm_compute. reflexivity. Qed.

Lemma tw_kept_GB : forall rd rd' Bw, tw_at TMAP_B rd Bw ->
  (forall b n i, In (b, n) G_HARNESS_B -> 0 <= i < n -> rd' (b + i) = rd (b + i)) -> tw_at TMAP_B rd' Bw.
Proof. intros rd rd' Bw H Hk. exact (tw_kept_G TMAP_B G_HARNESS_B rd rd' Bw TMAP_B_in_G H Hk). Qed.

Lemma TMAP_B_hull : forall x, tw_in TMAP_B x -> G_HARNESS_B_LO <= x < G_HARNESS_B_HI.
Proof.
  intros x (o & b & n & Hin & Hx). pose proof (G_HARNESS_B_in_hull (b, n) (TMAP_B_in_G o b n Hin)) as H.
  cbn [fst snd] in H. lia.
Qed.

Lemma TMAP_B_kept {segs : list Segment} : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_B (fun a => option_map (fun x : byte => bv_unsigned x) (mrd segs m (wa a))) Bw ->
  munch [(lo, hi)] m m' -> (hi <= G_HARNESS_B_LO \/ G_HARNESS_B_HI <= lo) ->
  tw_at TMAP_B (fun a => option_map (fun x : byte => bv_unsigned x) (mrd segs m' (wa a))) Bw.
Proof.
  intros m m' lo hi Bw H MU D. apply (tw_kept_munch segs m m' TMAP_B _ Bw TMAP_B_ok H MU).
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. cbn [outside]. split; [lia | exact I].
Qed.
