(* Support lemmas for case 2 (op_announce, fuzz/fuzz_transport.c:1052-1066, inlined) of the ubsan op loop of
   LLVMFuzzerTestOneInput, proved in U/Prog/T/LLVMFuzzerTestOneInput_op2.v:

   - the list algebra of the model's [upd] the walk needs (a write inside the left / right half of an append,
     two adjacent writes as one);
   - the 40 bytes of llvm_frame's j60 cell at Sp + 0x60 (the announce body[] of :1057 plus 6 bytes of slack):
     the destination cell of a memcpy / memset at an offset inside it, the cell after the call, a direct byte
     store, and the same wrapped around the loop's llvm_mem;
   - the reads the walk makes: a byte of the input buffer, .rodata (the MAC tables and the name strings, through
     mem_inv) and .data.rel.ro (op_announce's NAME pointer table, through relro_img);
   - the arithmetic of the compiler's idioms: andi as a modulus, the ori / andi that picks SPEC_CMD_E0 or
     SPEC_CMD_E1, and the multiply-high by 0x5555555555555556 that is a division by 3;
   - the model: op_announce_m and LLVMFuzzerTestOneInput_op_m's case 2 as one build_and_receive_m. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem
  TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the algebra of upd *)

Lemma op2_upd_app_l : forall (a b v : list byte) k, 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length a) ->
  upd (a ++ b) k v = upd a k v ++ b.
Proof.
  intros a b v k Hk Hl. unfold upd.
  rewrite firstn_app, skipn_app.
  replace (Z.to_nat k - length a)%nat with 0%nat by lia.
  replace (Z.to_nat k + length v - length a)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma op2_upd_app_r : forall (a b v : list byte) k j, 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length b) ->
  j = Z.of_nat (length a) + k ->
  upd (a ++ b) j v = a ++ upd b k v.
Proof.
  intros a b v k j Hk Hl ->. unfold upd.
  rewrite firstn_app, skipn_app.
  rewrite (firstn_all2 a) by lia.
  replace (Z.to_nat (Z.of_nat (length a) + k) - length a)%nat with (Z.to_nat k) by lia.
  rewrite (skipn_all2 a) by lia.
  replace (Z.to_nat (Z.of_nat (length a) + k) + length v - length a)%nat
    with (Z.to_nat k + length v)%nat by lia.
  cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma op2_upd0 : forall (bs v : list byte) n, length v = n -> (n <= length bs)%nat ->
  upd bs 0 v = v ++ skipn n bs.
Proof.
  intros bs v n Hv Hn. unfold upd. cbn [Z.to_nat firstn]. rewrite Hv. reflexivity.
Qed.

Lemma op2_upd_adj : forall (bs v w : list byte) k, 0 <= k ->
  k + Z.of_nat (length v) + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  upd (upd bs k v) (k + Z.of_nat (length v)) w = upd bs k (v ++ w).
Proof.
  intros bs v w k Hk Hl.
  assert (EU : upd bs k v = (firstn (Z.to_nat k) bs ++ v) ++ skipn (Z.to_nat k + length v) bs)
    by (unfold upd; rewrite <- app_assoc; reflexivity).
  assert (LP : length (firstn (Z.to_nat k) bs ++ v) = (Z.to_nat k + length v)%nat)
    by (rewrite app_length, firstn_length; lia).
  unfold upd at 1. rewrite EU.
  replace (Z.to_nat (k + Z.of_nat (length v))) with (length (firstn (Z.to_nat k) bs ++ v)) by lia.
  rewrite firstn_app_exact.
  replace (length (firstn (Z.to_nat k) bs ++ v) + length w)%nat
    with (length (firstn (Z.to_nat k) bs ++ v) + length w)%nat by lia.
  rewrite skipn_app, (skipn_all2 (firstn (Z.to_nat k) bs ++ v)) by lia.
  replace (length (firstn (Z.to_nat k) bs ++ v) + length w - length (firstn (Z.to_nat k) bs ++ v))%nat
    with (length w) by lia.
  rewrite skipn_skipn. cbn [app].
  unfold upd. rewrite app_length.
  replace (Z.to_nat k + (length v + length w))%nat with (length w + (Z.to_nat k + length v))%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma op2_sub0 : forall (v : list byte) n, length v = n -> sub v 0 n = v.
Proof. intros v n H. apply sub_all. exact H. Qed.

(* 0x14038 .. 0x14054: the four sb of "1.37" at body + 15 are op_announce's one upd at SPEC_ANN_VERSION. *)
Lemma op2_v137 : forall (b t : list byte), length b = 34%nat -> length t = 6%nat ->
  upd (upd (upd (upd (b ++ t) 15 (le1 (Z_to_bv 64 49))) 16 (le1 (Z_to_bv 64 46)))
        17 (le1 (Z_to_bv 64 51))) 18 (le1 (Z_to_bv 64 55))
  = upd b 15 ANN_VERSION_137 ++ t.
Proof.
  intros b t Hb Ht.
  assert (L : length (b ++ t) = 40%nat) by (rewrite app_length, Hb, Ht; reflexivity).
  change (le1 (Z_to_bv 64 49)) with [b8 0x31]. change (le1 (Z_to_bv 64 46)) with [b8 0x2e].
  change (le1 (Z_to_bv 64 51)) with [b8 0x33]. change (le1 (Z_to_bv 64 55)) with [b8 0x37].
  replace 16 with (15 + Z.of_nat (length [b8 0x31])) by (cbn [length]; lia).
  rewrite (op2_upd_adj (b ++ t) [b8 0x31] [b8 0x2e] 15) by (cbn [length]; lia).
  cbn [app].
  replace 17 with (15 + Z.of_nat (length [b8 0x31; b8 0x2e])) by (cbn [length]; lia).
  rewrite (op2_upd_adj (b ++ t) [b8 0x31; b8 0x2e] [b8 0x33] 15) by (cbn [length]; lia).
  cbn [app].
  replace 18 with (15 + Z.of_nat (length [b8 0x31; b8 0x2e; b8 0x33])) by (cbn [length]; lia).
  rewrite (op2_upd_adj (b ++ t) [b8 0x31; b8 0x2e; b8 0x33] [b8 0x37] 15) by (cbn [length]; lia).
  cbn [app].
  rewrite (op2_upd_app_l b t [b8 0x31; b8 0x2e; b8 0x33; b8 0x37] 15) by (cbn [length]; lia).
  reflexivity.
Qed.

(* ---------------------------------------------------------------- the bytes of the loop's frame *)

(* the 96 bytes of llvm_frame below the j60 cell (sp+0x00 .. sp+0x5f) *)
Definition op2_pre (Sp : Z) (j10 jio : list byte) : list byte :=
  cells_bytes [C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3)); CB 16 j10;
               C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
               C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))); C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)));
               CB 32 jio].

Lemma op2_pre_len : forall Sp j10 jio, length j10 = 16%nat -> length jio = 32%nat ->
  length (op2_pre Sp j10 jio) = 96%nat.
Proof.
  intros Sp j10 jio H1 H2. unfold op2_pre.
  rewrite cells_bytes_length by (cbn [cells_wf cell_wf]; tauto). reflexivity.
Qed.

Lemma op2_sav_len : forall regs0, length (cells_bytes (llvm_saved regs0)) = 104%nat.
Proof.
  intros regs0. unfold llvm_saved.
  rewrite cells_bytes_length by (cbn [cells_wf cell_wf]; tauto). reflexivity.
Qed.

Lemma op2_frame_size : forall regs0 Sp j10 jio j60,
  cells_size (llvm_frame regs0 Sp j10 jio j60) = 240%nat.
Proof. intros. unfold llvm_frame, llvm_saved. reflexivity. Qed.

Lemma op2_frame_wf : forall regs0 Sp j10 jio j60,
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  cells_wf (llvm_frame regs0 Sp j10 jio j60).
Proof.
  intros regs0 Sp j10 jio j60 H1 H2 H3. unfold llvm_frame, llvm_saved.
  cbn [cells_wf cell_wf app]. tauto.
Qed.

Lemma op2_frame_bytes : forall regs0 Sp j10 jio j60,
  cells_bytes (llvm_frame regs0 Sp j10 jio j60)
  = op2_pre Sp j10 jio ++ j60 ++ cells_bytes (llvm_saved regs0).
Proof.
  intros. unfold llvm_frame. rewrite cells_bytes_app. unfold op2_pre.
  cbn [cells_bytes cbytes]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma op2_frame_blen : forall regs0 Sp j10 jio j60,
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  length (cells_bytes (llvm_frame regs0 Sp j10 jio j60)) = 240%nat.
Proof.
  intros regs0 Sp j10 jio j60 H1 H2 H3.
  rewrite cells_bytes_length by (apply op2_frame_wf; assumption).
  apply op2_frame_size.
Qed.

(* A callee (or a store) that wrote the span [X, X + c) of a byte block and left every other byte of the block
   alone: the block is the model's upd. The shape of TWorldMem.v's wm_fill_out, for a block that is not the
   world. *)
Lemma op2_bytes_fill : forall m m' A bs W X k c src,
  bytes_at rsegs m A bs ->
  munch W m m' ->
  rw_cells rsegs m' X [CB c src] ->
  X = A + k -> 0 <= k -> k + Z.of_nat c <= Z.of_nat (length bs) ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> ~ (X <= x < X + Z.of_nat c) -> outside W x) ->
  bytes_at rsegs m' A (upd bs k src).
Proof.
  intros m m' A bs W X k c src HB MU D -> Hk Hkc OUT.
  destruct HB as (HBa & HBl & HBi).
  destruct D as [[Dwf Db] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  cbn [cells_bytes cbytes] in Db. rewrite app_nil_r in Db. destruct Db as (_ & _ & Dbi).
  assert (LU : length (upd bs k src) = length bs) by (apply length_upd; [exact Hk | rewrite LS; lia]).
  split; [lia|]. split; [rewrite LU; lia|].
  intros i Hi. rewrite LU in Hi.
  rewrite ne_upd by (rewrite ?LS; lia). rewrite LS.
  destruct ((Z.to_nat k <=? i) && (i <? Z.to_nat k + c))%nat eqn:C.
  - apply andb_true_iff in C. destruct C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.ltb_lt in C2.
    rewrite <- Dbi by (rewrite ?LS; lia).
    f_equal. unfold wa. f_equal. lia.
  - rewrite <- HBi by lia.
    unfold mrd. rewrite MU; [reflexivity|].
    rewrite wa_unsigned by lia. apply OUT; [lia|].
    apply andb_false_iff in C. destruct C as [C|C]; [apply Nat.leb_gt in C | apply Nat.ltb_ge in C]; lia.
Qed.

Lemma op2_frame_fill : forall m m' regs0 Sp j10 jio j60 W X k c src,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  munch W m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' X [CB c src] ->
  X = Sp + 96 + k -> 0 <= k -> k + Z.of_nat c <= 40 ->
  (forall x, Sp <= x < Sp + 240 -> ~ (X <= x < X + Z.of_nat c) -> outside W x) ->
  rw_cells rsegs m' Sp (llvm_frame regs0 Sp j10 jio (upd j60 k src)).
Proof.
  intros m m' regs0 Sp j10 jio j60 W X k c src HF H1 H2 H3 MU WMO D EX Hk Hkc OUT.
  pose proof D as D'. destruct D' as [[Dwf _] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  assert (LU : length (upd j60 k src) = 40%nat)
    by (rewrite length_upd; [exact H3 | exact Hk | rewrite LS, H3; lia]).
  pose proof (op2_frame_blen regs0 Sp j10 jio j60 H1 H2 H3) as LB.
  split; [split|].
  - apply op2_frame_wf; assumption.
  - assert (EB : cells_bytes (llvm_frame regs0 Sp j10 jio (upd j60 k src))
               = upd (cells_bytes (llvm_frame regs0 Sp j10 jio j60)) (96 + k) src).
    { rewrite !op2_frame_bytes.
      rewrite (op2_upd_app_r (op2_pre Sp j10 jio) (j60 ++ cells_bytes (llvm_saved regs0)) src k (96 + k));
        [| lia
         | rewrite app_length, H3, op2_sav_len; lia
         | rewrite (op2_pre_len Sp j10 jio H1 H2); lia ].
      rewrite (op2_upd_app_l j60 (cells_bytes (llvm_saved regs0)) src k); [reflexivity | lia | rewrite H3; lia]. }
    rewrite EB.
    apply (op2_bytes_fill m m' Sp (cells_bytes (llvm_frame regs0 Sp j10 jio j60)) W X (96 + k) c src);
      [ destruct HF as [[_ Hb] _]; exact Hb | exact MU | exact D | lia | lia | rewrite LB; lia | ].
    rewrite LB. exact OUT.
  - destruct HF as [_ Hw]. rewrite op2_frame_size in Hw |- *.
    eapply wr_at_transport; [exact Hw | exact WMO].
Qed.

Lemma op2_sub_bytes : forall m a bs (k : Z) q X, bytes_at rsegs m a bs -> 0 <= k ->
  (Z.to_nat k + q <= length bs)%nat -> X = a + k -> bytes_at rsegs m X (sub bs k q).
Proof.
  intros m a bs k q X (Ha & Hl & Hb) Hk Hn ->.
  assert (LS : length (sub bs k q) = q) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite LS; lia|].
  intros i Hi. rewrite LS in Hi. rewrite ne_sub by lia.
  replace (i <? q)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply Hb. lia.
Qed.

Lemma op2_frame_j60 : forall m regs0 Sp j10 jio j60,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  bytes_at rsegs m (Sp + 96) j60.
Proof.
  intros m regs0 Sp j10 jio j60 HF H1 H2 H3.
  destruct HF as [[_ Hb] _]. rewrite op2_frame_bytes in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite (op2_pre_len Sp j10 jio H1 H2) in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

Lemma op2_frame_cell : forall m regs0 Sp j10 jio j60 k n X,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  X = Sp + 96 + k -> 0 <= k -> 0 <= n -> k + n <= 40 ->
  rw_cells rsegs m X [CB (Z.to_nat n) (sub j60 k (Z.to_nat n))].
Proof.
  intros m regs0 Sp j10 jio j60 k n X HF H1 H2 H3 -> Hk Hn Hkn.
  assert (LS : length (sub j60 k (Z.to_nat n)) = Z.to_nat n) by (apply length_sub; rewrite ?H3; lia).
  pose proof (op2_frame_j60 m regs0 Sp j10 jio j60 HF H1 H2 H3) as HJ.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LS | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply (op2_sub_bytes m (Sp + 96) j60 k (Z.to_nat n)); [exact HJ | lia | rewrite H3; lia | lia].
  - destruct HF as [_ (Hw0 & Hw1 & Hw)]. rewrite op2_frame_size in Hw1, Hw.
    cbn [cells_size csize]. rewrite Nat.add_0_r.
    split; [lia|]. split; [lia|].
    intros i Hi. replace (Sp + 96 + k + i) with (Sp + (96 + k + i)) by lia. apply Hw. lia.
Qed.

Lemma op2_frame_store_ok : forall m regs0 Sp j10 jio j60 k (n : nat) a,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  0 <= k -> k + Z.of_nat n <= 40 -> a = Sp + 96 + k ->
  store_ok rsegs m (Z_to_bv 64 a) n = true.
Proof.
  intros m regs0 Sp j10 jio j60 k n a HF Hk Hn ->.
  destruct HF as [_ Hw]. rewrite op2_frame_size in Hw.
  replace (Sp + 96 + k) with (Sp + (96 + k)) by lia.
  exact (wr_at_store_ok rsegs m Sp (Z.of_nat 240) (96 + k) n Hw ltac:(lia) ltac:(lia)).
Qed.

Lemma op2_frame_rd48 : forall m regs0 Sp j10 jio j60 a,
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) ->
  a = wa (Sp + 48) ->
  ov_read_bytes rsegs m a 8 = Some (le8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96)))).
Proof.
  intros m regs0 Sp j10 jio j60 a HF ->.
  exact (rw_cells_read_at rsegs m Sp (llvm_frame regs0 Sp j10 jio j60) 48
           (C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96)))) 8 (wa (Sp + 48)) HF
           ltac:(unfold llvm_frame, llvm_saved; cells_cbv; reflexivity)
           ltac:(reflexivity)
           ltac:(unfold wa; f_equal; lia)).
Qed.

(* ---------------------------------------------------------------- the loop's llvm_mem around those writes *)

Lemma op2_mem_facts : forall data D regs0 m0 Sp lo B m j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 < data /\ data + Z.of_nat (length D) <= lo /\ lo + 9936 <= Sp /\ Sp + 240 <= 2 ^ 63 /\
  W_BASE_UBSAN + W_LEN <= lo /\ Sp mod 16 = 0 /\
  length j10 = 16%nat /\ length jio = 32%nat /\ length j60 = 40%nat /\
  mem_inv rsegs m /\ relro_img m /\ bytes_at rsegs m data D /\
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10 jio j60).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 HM. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & _ & HD & HSP & _ & HLO & HSP2 & HWL & HMI & HRO & _ & _ & _ & _ &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  split; [exact HD0|]. split; [exact HDL|]. split; [exact HLO|]. split; [exact HSP2|].
  split; [exact HWL|]. split; [exact HSP|]. split; [exact HJ1|]. split; [exact HJ2|].
  split; [exact HJ3|]. split; [exact HMI|]. split; [exact HRO|]. split; [exact HD|]. exact HRW.
Qed.

Lemma op2_mem_cell : forall data D regs0 m0 Sp lo B m j10 jio j60 k n X,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  X = Sp + 96 + k -> 0 <= k -> 0 <= n -> k + n <= 40 ->
  rw_cells rsegs m X [CB (Z.to_nat n) (sub j60 k (Z.to_nat n))].
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k n X HM EX Hk Hn Hkn.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & HJ1 & HJ2 & HJ3 & _ & _ & _ & HRW).
  eapply op2_frame_cell;
    [ exact HRW | exact HJ1 | exact HJ2 | exact HJ3 | exact EX | exact Hk | exact Hn | exact Hkn ].
Qed.

Lemma op2_mem_j60 : forall data D regs0 m0 Sp lo B m j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 -> bytes_at rsegs m (Sp + 96) j60.
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 HM.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & HJ1 & HJ2 & HJ3 & _ & _ & _ & HRW).
  eapply op2_frame_j60; [ exact HRW | exact HJ1 | exact HJ2 | exact HJ3 ].
Qed.

Lemma op2_mem_rd48 : forall data D regs0 m0 Sp lo B m j10 jio j60 a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 -> a = wa (Sp + 48) ->
  ov_read_bytes rsegs m a 8 = Some (le8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96)))).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 a HM EA.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRW).
  eapply op2_frame_rd48; [ exact HRW | exact EA ].
Qed.

Lemma op2_mem_store_ok : forall data D regs0 m0 Sp lo B m j10 jio j60 k (n : nat) a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat n <= 40 -> a = Sp + 96 + k ->
  store_ok rsegs m (Z_to_bv 64 a) n = true.
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k n a HM Hk Hn EA.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRW).
  eapply op2_frame_store_ok; [ exact HRW | exact Hk | exact Hn | exact EA ].
Qed.

Lemma op2_mem_in : forall data D regs0 m0 Sp lo B m j10 jio j60 i a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= i -> (Z.to_nat i < length D)%nat -> a = data + i ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 1 = Some [nth (Z.to_nat i) D (b8 0)].
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 i a HM Hi HiD ->.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD & _).
  change (Z_to_bv 64 (data + i)) with (wa (data + i)).
  rewrite (bytes_at_read rsegs m data D i 1 HD Hi ltac:(lia)).
  f_equal. revert HiD. generalize (Z.to_nat i) as j. clear.
  induction D as [|d D IH]; intros [|j] Hj; cbn in Hj; try lia; cbn [skipn firstn nth]; [reflexivity|].
  apply IH. lia.
Qed.

(* relro_img lies below W_BASE_UBSAN (0x21ef8 + 0xd8 <= 0x33300), so a write at or above Sp keeps it. *)
Lemma op2_relro_keep : forall m m' X n, relro_img m -> munch [(X, X + n)] m m' ->
  RELRO_BASE + RELRO_LEN <= X -> relro_img m'.
Proof.
  intros m m' X n HR MU HX i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))).
  - exact (HR i Hi).
  - cbn [outside]. unfold wa.
    rewrite unsigned_lit by (unfold RELRO_BASE, RELRO_LEN in *; lia).
    unfold RELRO_BASE, RELRO_LEN in *. split; [lia | exact I].
Qed.

Lemma op2_mem_fill : forall data D regs0 m0 Sp lo B m m' j10 jio j60 k n src X,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  munch [(X, X + n)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' X [CB (Z.to_nat n) src] ->
  X = Sp + 96 + k -> 0 <= k -> 0 <= n -> k + n <= 40 ->
  llvm_mem data D regs0 m0 Sp lo B m' j10 jio (upd j60 k src).
Proof.
  intros data D regs0 m0 Sp lo B m m' j10 jio j60 k n src X HM MU WMO MI D0 EX Hk Hn Hkn.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & _ & HRO & _ & HRW).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  pose proof D0 as D1. destruct D1 as [[Dwf _] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  unfold llvm_mem in HM |- *.
  destruct HM as (_ & _ & HOW & HD & _ & HSTK & _ & _ & _ & _ & _ & HWM & HFN & HMU & HWMO & _ & _ & _ & _).
  unfold LH_K, LH_FRAME in *.
  assert (LU : length (upd j60 k src) = 40%nat)
    by (rewrite length_upd; [exact HJ3 | exact Hk | rewrite LS, HJ3; lia]).
  split; [exact HD0|]. split; [exact HDL|]. split; [exact HOW|].
  split.
  { eapply bytes_at_transport; [exact HD | exact MU |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split; [exact HSP16|].
  split; [eapply stk_transport_disjoint; [exact HSTK | exact MU | exact WMO |];
          cbn [disjoint_from]; split; [lia | exact I]|].
  split; [lia|]. split; [lia|]. split; [unfold W_BASE_UBSAN, W_LEN; lia|].
  split; [exact MI|].
  split; [eapply op2_relro_keep; [exact HRO | exact MU | unfold RELRO_BASE, RELRO_LEN; lia]|].
  split.
  { eapply rw_cells_transport; [exact HWM | exact MU | exact WMO |].
    rewrite wm_size. cbn [disjoint_from]. unfold W_BASE_UBSAN, W_LEN in *. split; [lia | exact I]. }
  split; [exact HFN|].
  split.
  { eapply munch_trans; [exact HMU|].
    eapply munch_weaken; [| exact MU].
    unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *.
    destruct Hx as (Hx1 & _). split; [intros Hcc; apply Hx1; lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ HWMO WMO)|].
  split; [exact HJ1|]. split; [exact HJ2|]. split; [exact LU|].
  eapply op2_frame_fill;
    [ exact HRW | exact HJ1 | exact HJ2 | exact HJ3 | exact MU | exact WMO | exact D0 | exact EX | exact Hk
    | lia |].
  intros x Hx Hc. cbn [outside].
  split; [intros Hcc; apply Hc; lia | exact I].
Qed.

Lemma op2_mem_store : forall data D regs0 m0 Sp lo B m j10 jio j60 k v a,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  0 <= k -> k + Z.of_nat (length v) <= 40 -> a = Sp + 96 + k ->
  llvm_mem data D regs0 m0 Sp lo B (write_to_mem m (Z_to_bv 64 a) v) j10 jio (upd j60 k v).
Proof.
  intros data D regs0 m0 Sp lo B m j10 jio j60 k v a HM Hk Hn ->.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & _ & HJ1 & HJ2 & HJ3 & HMI & _ & _ & HRW).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  pose proof (op2_mem_store_ok _ _ _ _ _ _ _ _ _ _ _ k (length v) _ HM Hk Hn eq_refl) as HSO.
  pose proof (wm_write_munch m (Sp + 96 + k) v ltac:(lia) ltac:(lia)) as MU.
  pose proof (wmono_write rsegs m m (Z_to_bv 64 (Sp + 96 + k)) v (wmono_refl rsegs m)) as WMO.
  pose proof (mem_inv_store rsegs m (Z_to_bv 64 (Sp + 96 + k)) v HMI HSO) as MI.
  assert (DST : rw_cells rsegs (write_to_mem m (Z_to_bv 64 (Sp + 96 + k)) v) (Sp + 96 + k)
                  [CB (Z.to_nat (Z.of_nat (length v))) v]).
  { rewrite Nat2Z.id. split; [split|].
    - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_write_same; lia.
    - cbn [cells_size csize]. rewrite Nat.add_0_r.
      destruct HRW as [_ (Hw0 & Hw1 & Hw)]. rewrite op2_frame_size in Hw1, Hw.
      split; [lia|]. split; [lia|].
      intros i Hi. apply wview_write_mono.
      replace (Sp + 96 + k + i) with (Sp + (96 + k + i)) by lia. apply Hw. lia. }
  eapply (op2_mem_fill data D regs0 m0 Sp lo B m _ j10 jio j60 k (Z.of_nat (length v)) v (Sp + 96 + k));
    [ exact HM | exact MU | exact WMO | exact MI | exact DST | reflexivity | exact Hk | lia | lia ].
Qed.

(* A callee that wrote nothing (strlen): the loop's memory invariant moves across unchanged. *)
Lemma op2_upd_nil : forall (bs : list byte) k, 0 <= k -> upd bs k [] = bs.
Proof.
  intros bs k Hk. unfold upd. cbn [app length]. rewrite Nat.add_0_r. apply firstn_skipn.
Qed.

Lemma op2_mem_same : forall data D regs0 m0 Sp lo B m m' j10 jio j60,
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  llvm_mem data D regs0 m0 Sp lo B m' j10 jio j60.
Proof.
  intros data D regs0 m0 Sp lo B m m' j10 jio j60 HM MU WMO MI.
  pose proof (op2_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & _ & _ & _ & HJ3 & _ & _ & _ & _).
  unfold W_BASE_UBSAN, W_LEN in HWL.
  assert (MU' : munch [(Sp + 96, Sp + 96 + 0)] m m')
    by (apply (munch_weaken (@nil ivl) [(Sp + 96, Sp + 96 + 0)] m m');
        [unfold sub_fp; intros x _; exact I | exact MU]).
  assert (DST : rw_cells rsegs m' (Sp + 96) [CB (Z.to_nat 0) []]).
  { split; [split|].
    - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
    - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. exfalso. lia. }
  pose proof (op2_mem_fill data D regs0 m0 Sp lo B m m' j10 jio j60 0 0 [] (Sp + 96)
                HM MU' WMO MI DST ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HR.
  rewrite op2_upd_nil in HR by lia. exact HR.
Qed.

(* ---------------------------------------------------------------- reads of the image *)

Lemma op2_img : forall m A bs, mem_inv rsegs m -> ro_bytes_b rsegs A bs = true ->
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m A bs.
Proof.
  intros m A bs MI RB HA HL.
  exact (ro_bytes_at rsegs m A bs MI HA HL (ro_bytes_b_sound rsegs bs A RB)).
Qed.

(* A 6-byte MAC table entry of .rodata, as the machine facts build_and_receive's caller must give. *)
Lemma op2_mac_at : forall m p mac, mem_inv rsegs m -> ro_bytes_b rsegs p mac = true ->
  length mac = 6%nat -> 0 <= p -> p + 6 <= 2 ^ 64 -> lh_mac_at m p mac.
Proof.
  intros m p mac MI RB L6 Hp0 Hp6.
  pose proof (ro_bytes_b_sound rsegs mac p RB) as RBs.
  split; [exact L6|]. split; [exact Hp0|]. split; [lia|].
  split; [exact (ro_bytes_at rsegs m p mac MI Hp0 ltac:(rewrite L6; lia) RBs)|].
  intros i Hi.
  destruct (nth_error mac (Z.to_nat i)) as [b|] eqn:E.
  2:{ apply nth_error_None in E. lia. }
  pose proof (ro_bytes_nth rsegs mac p (Z.to_nat i) b RBs E) as [_ HA].
  unfold wa in HA. replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia. exact HA.
Qed.

Lemma op2_img_nth : forall n a bs i, image_bytes rsegs a n = Some bs -> (i < n)%nat ->
  seg_rom rsegs (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs i H Hi; cbn in H; [lia|].
  destruct (seg_rom rsegs (wa a)) as [b|] eqn:E1; [|discriminate].
  destruct (image_bytes rsegs (a + 1) n) as [bs'|] eqn:E2; [|discriminate].
  injection H as <-. destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E1.
  - rewrite <- (IH (a + 1) bs' i E2 ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

(* .data.rel.ro is mapped read-write (PT_GNU_RELRO is not applied), so its bytes come from relro_img. *)
Lemma op2_relro_at : forall m a bs, relro_img m ->
  RELRO_BASE <= a -> a + Z.of_nat (length bs) <= RELRO_BASE + RELRO_LEN ->
  image_bytes rsegs a (length bs) = Some bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RE H1 H2 HI. unfold RELRO_BASE, RELRO_LEN in H1, H2.
  split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- (op2_img_nth (length bs) a bs i HI Hi).
  replace (a + Z.of_nat i) with (RELRO_BASE + (a + Z.of_nat i - RELRO_BASE)) by (unfold RELRO_BASE; lia).
  apply RE. unfold RELRO_BASE, RELRO_LEN. lia.
Qed.

Lemma op2_notin : forall (l : list byte), forallb (fun b => negb (Z.eqb (bv_unsigned b) 0)) l = true ->
  ~ In (Z_to_bv 8 0) l.
Proof.
  induction l as [|x l IH]; cbn [forallb In]; [tauto|].
  intros H. apply andb_prop in H. destruct H as [H1 H2].
  intros [E|E]; [| exact (IH H2 E)].
  apply negb_true_iff, Z.eqb_neq in H1. apply H1. rewrite E. reflexivity.
Qed.

(* ---------------------------------------------------------------- the compiler's arithmetic *)

Lemma op2_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (Z.of_N 8) with 8 in R. lia.
Qed.

Lemma op2_land1 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof.
  intros x Hx. change (Z.land x 1) with (Z.land x (Z.ones 1)).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma op2_land15 : forall x, 0 <= x -> Z.land x 15 = x mod 16.
Proof.
  intros x Hx. change (Z.land x 15) with (Z.land x (Z.ones 4)).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma op2_orand : forall x, 0 <= x -> Z.land (Z.lor x 224) 225 = Z.lor (Z.land x 1) 224.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ 8 <= i) by lia.
  destruct C as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]];
    try (subst i; destruct (Z.testbit x _); reflexivity).
  rewrite (testbit_high_false 224 8 i) by (cbn; lia).
  rewrite (testbit_high_false 225 8 i) by (cbn; lia).
  rewrite (testbit_high_false 1 8 i) by (cbn; lia).
  destruct (Z.testbit x i); reflexivity.
Qed.

(* 0x13ff4 / 0x14094: cmd = (sel | 0xe0) & 0xe1 is op_announce's `(sel & 1) ? SPEC_CMD_E1 : SPEC_CMD_E0`. *)
Lemma op2_cmd_val : forall x, 0 <= x ->
  Z.land (Z.lor x 224) 225 = (if Z.land x 1 =? 0 then SPEC_CMD_E0 else SPEC_CMD_E1).
Proof.
  intros x Hx. rewrite op2_orand by exact Hx. rewrite (op2_land1 x Hx).
  assert (R : x mod 2 = 0 \/ x mod 2 = 1) by lia.
  destruct R as [E|E]; rewrite E; reflexivity.
Qed.

(* 0x13fe4 mulhu with 0x5555555555555556 = (2^64 + 2) / 3: the quotient of a byte by 3. *)
Lemma op2_div3 : forall x, 0 <= x < 256 -> Z.shiftr (x * 6148914691236517206) 64 = x / 3.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* ---------------------------------------------------------------- the model of op_announce *)

Definition op2_sel (D : list byte) (c1 : fuzz_in) : Z := snd (fuzz_u8_m D c1).
Definition op2_ca (D : list byte) (c1 : fuzz_in) : fuzz_in := fst (fuzz_u8_m D c1).
Definition op2_mac (D : list byte) (c1 : fuzz_in) : Z := snd (fuzz_u8_m D (op2_ca D c1)) mod 16.
Definition op2_cb (D : list byte) (c1 : fuzz_in) : fuzz_in := fst (fuzz_u8_m D (op2_ca D c1)).
Definition op2_name (D : list byte) (c1 : fuzz_in) : Z := snd (fuzz_u8_m D (op2_cb D c1)) mod 3.
Definition op2_c3 (D : list byte) (c1 : fuzz_in) : fuzz_in := fst (fuzz_u8_m D (op2_cb D c1)).

Definition op2_b0 : list byte := repeat (b8 0) 34.
Definition op2_b1 (mac : Z) : list byte :=
  if mac <? 10 then upd op2_b0 mac HOST
  else if mac <? 13 then upd op2_b0 (mac - 10) OTHER else op2_b0.
Definition op2_b2 (mac : Z) : list byte := upd (op2_b1 mac) 15 ANN_VERSION_137.
Definition op2_b3 (mac name : Z) : list byte :=
  upd (op2_b2 mac) 24 (nth (Z.to_nat name) op_announce_NAME []).

Definition op2_cmd (D : list byte) (c1 : fuzz_in) : Z :=
  if Z.land (op2_sel D c1) 1 =? 0 then SPEC_CMD_E0 else SPEC_CMD_E1.
Definition op2_body (D : list byte) (c1 : fuzz_in) : list byte :=
  op2_b3 (op2_mac D c1) (op2_name D c1).

Lemma op2_b0_len : length op2_b0 = 34%nat.
Proof. unfold op2_b0. apply repeat_length. Qed.

Lemma op2_b1_len : forall mac, 0 <= mac < 16 -> length (op2_b1 mac) = 34%nat.
Proof.
  intros mac Hm. unfold op2_b1, HOST, OTHER, bs.
  destruct (Z.ltb_spec mac 10) as [H|H].
  - rewrite length_upd; [exact op2_b0_len | lia |]. cbn [length map]. rewrite op2_b0_len. lia.
  - destruct (Z.ltb_spec mac 13) as [H2|H2]; [| exact op2_b0_len].
    rewrite length_upd; [exact op2_b0_len | lia |]. cbn [length map]. rewrite op2_b0_len. lia.
Qed.

Lemma op2_b2_len : forall mac, 0 <= mac < 16 -> length (op2_b2 mac) = 34%nat.
Proof.
  intros mac Hm. unfold op2_b2, ANN_VERSION_137, bs.
  rewrite length_upd; [apply op2_b1_len; lia | lia |].
  cbn [length map]. rewrite (op2_b1_len mac Hm). lia.
Qed.

Lemma op2_name_len : forall name, 0 <= name < 3 ->
  (Z.of_nat (length (nth (Z.to_nat name) op_announce_NAME [])) <= 8)%Z.
Proof.
  intros name Hn.
  assert (C : name = 0 \/ name = 1 \/ name = 2) by lia.
  assert (L0 : length (nth 0 op_announce_NAME []) = 8%nat) by reflexivity.
  assert (L1 : length (nth 1 op_announce_NAME []) = 8%nat) by reflexivity.
  assert (L2 : length (nth 2 op_announce_NAME []) = 5%nat) by reflexivity.
  destruct C as [E|[E|E]]; subst name;
    [ change (Z.to_nat 0) with 0%nat; rewrite L0
    | change (Z.to_nat 1) with 1%nat; rewrite L1
    | change (Z.to_nat 2) with 2%nat; rewrite L2 ]; lia.
Qed.

Lemma op2_b3_len : forall mac name, 0 <= mac < 16 -> 0 <= name < 3 -> length (op2_b3 mac name) = 34%nat.
Proof.
  intros mac name Hm Hn. unfold op2_b3.
  rewrite length_upd; [apply op2_b2_len; lia | lia |].
  pose proof (op2_name_len name Hn). rewrite (op2_b2_len mac Hm). lia.
Qed.

Lemma op2_announce_eq : forall I B D a c1,
  op_announce_m I B D a c1 =
    match build_and_receive_m I B a SPEC_BCAST DESK 0 0 0 (op2_cmd D c1) (op2_body D c1) with
    | Some (B1, _) => Some (B1, op2_c3 D c1)
    | None => None
    end.
Proof.
  intros I B D a c1.
  unfold op_announce_m, op2_cmd, op2_body, op2_b3, op2_b2, op2_b1, op2_b0,
         op2_sel, op2_name, op2_mac, op2_c3, op2_cb, op2_ca.
  destruct (fuzz_u8_m D c1) as [d1 sel] eqn:E1. cbn [fst snd].
  destruct (fuzz_u8_m D d1) as [d2 mm] eqn:E2. cbn [fst snd].
  destruct (fuzz_u8_m D d2) as [d3 nn] eqn:E3. cbn [fst snd].
  reflexivity.
Qed.

Lemma op2_opm : forall I B A D c k,
  snd (fuzz_u8_m D c) mod 9 = 2 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k =
    match build_and_receive_m I B (A k) SPEC_BCAST DESK 0 0 0
            (op2_cmd D (fst (fuzz_u8_m D c))) (op2_body D (fst (fuzz_u8_m D c))) with
    | Some (B1, _) => Some (B1, (op2_c3 D (fst (fuzz_u8_m D c)), S k))
    | None => None
    end.
Proof.
  intros I B A D c k H2. unfold LLVMFuzzerTestOneInput_op_m.
  destruct (fuzz_u8_m D c) as [c1 opb] eqn:E. cbn [fst snd] in H2 |- *.
  cbv zeta. rewrite H2. cbn [Z.eqb Pos.eqb].
  rewrite (op2_announce_eq I B D (A k) c1).
  destruct (build_and_receive_m I B (A k) SPEC_BCAST DESK 0 0 0 (op2_cmd D c1) (op2_body D c1))
    as [[B1 u]|]; reflexivity.
Qed.
