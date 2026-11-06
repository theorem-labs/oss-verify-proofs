From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0s YK14 YP09 YO0i YO0f YO0d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel KindB.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pl_mfile_cells_size : forall h b n fl pad0 rpos rend prev next mode pad1 pos pad2 ung buf,
  cells_size (mfile_cells h b n fl pad0 rpos rend prev next mode pad1 pos pad2 ung buf) = 1304%nat.
Proof. reflexivity. Qed.

Lemma pl_in_blocks_user : forall L A q k, In (q, k) (blocks L A) ->
  exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = q.
Proof.
  intros L A q k H. unfold blocks in H. apply in_map_iff in H as ([p k'] & E & Hp).
  cbn in E. injection E as E1 E2. subst k'. exists p. split; [exact Hp | exact E1].
Qed.

Lemma pl_in_blocks_of_user : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ H). Qed.

Section Keep.
Variables m m' : word -> option byte.
Variables lo hi : Z.
Hypothesis KEEP : forall a, lo <= a < hi ->
  mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a -> writable_at rsegs m' a).

Lemma kp_bytes_at : forall a bs, bytes_at rsegs m a bs -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  bytes_at rsegs m' a bs.
Proof.
  intros a bs H H1 H2. apply (bytes_at_transfer rsegs m); [exact H|]. intros i Hi. apply KEEP. lia.
Qed.

Lemma kp_rw_cells : forall a cs, rw_cells rsegs m a cs -> lo <= a -> a + Z.of_nat (cells_size cs) <= hi ->
  rw_cells rsegs m' a cs.
Proof.
  intros a cs H H1 H2. apply (rw_cells_transfer rsegs m); [exact H|]. intros i Hi. apply KEEP. lia.
Qed.

Lemma kp_stdio_ok : stdio_ok m -> lo <= A_LIBC -> A_OFL_LOCK + 4 <= hi -> stdio_ok m'.
Proof.
  unfold stdio_ok, A_LIBC, A_OFL_LOCK. intros (S1 & S2 & S3) H1 H2.
  split; [|split]; (eapply kp_bytes_at; [eassumption | lia | cbn [length]; try rewrite length_le4; lia]).
Qed.

Lemma kp_guard_ok : guard_ok m -> lo <= A_GOT_GUARD -> A_GUARD + 8 <= hi -> guard_ok m'.
Proof.
  unfold guard_ok, A_GOT_GUARD, A_GUARD. intros (G1 & g & G2) H1 H2.
  split; [|exists g]; (eapply kp_bytes_at; [eassumption | lia | rewrite length_le8; lia]).
Qed.

Lemma kp_ofl_one : forall h, ofl_one m h -> lo <= A_OFL_HEAD -> A_OFL_HEAD + 8 <= hi -> ofl_one m' h.
Proof.
  unfold ofl_one, A_OFL_HEAD. intros h H H1 H2. eapply kp_rw_cells; [exact H | lia | cbn; lia].
Qed.

Lemma kp_ofl_empty : ofl_empty m -> lo <= A_OFL_HEAD -> A_OFL_HEAD + 8 <= hi -> ofl_empty m'.
Proof.
  unfold ofl_empty, A_OFL_HEAD. intros H H1 H2. eapply kp_rw_cells; [exact H | lia | cbn; lia].
Qed.

Lemma kp_mstl : forall h b Fc p pv nx, mstl m h b Fc p pv nx ->
  lo <= h -> h + 1304 <= hi -> lo <= b -> b + Z.of_nat (length Fc) <= hi -> mstl m' h b Fc p pv nx.
Proof.
  intros h b Fc p pv nx (fl & md & q & rb & HMF & R1 & R2 & R3 & R4) H1 H2 H3 H4.
  exists fl, md, q, rb. refine (conj _ (conj R1 (conj R2 (conj R3 R4)))).
  destruct HMF as (buf & (pad0 & pad1 & pad2 & ung & HC & L1 & L2 & H0 & H16) & Hq & Hrb & HFc & Hb0 & Hd).
  unfold mfile; cbv zeta. exists buf.
  refine (conj _ (conj Hq (conj Hrb (conj (kp_bytes_at _ _ HFc H3 H4) (conj Hb0 Hd))))).
  unfold mfile_raw. exists pad0, pad1, pad2, ung. refine (conj _ (conj L1 (conj L2 (conj H0 H16)))).
  apply (kp_rw_cells _ _ HC H1). rewrite pl_mfile_cells_size. lia.
Qed.

End Keep.

Lemma keep_munch : forall W m m' lo hi, munch W m m' -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> outside W x) ->
  forall a, lo <= a < hi -> mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a -> writable_at rsegs m' a).
Proof.
  intros W m m' lo hi MU H1 H2 HO a Ha. split.
  - apply (munch_mbyte rsegs W m m' a MU); [lia | apply HO; lia].
  - intros Hw. apply (munch_writable rsegs W m m' a MU); [lia | apply HO; lia | exact Hw].
Qed.

Lemma ro_agree_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 20 -> outside W x) -> ro_agree rsegs m'.
Proof.
  intros W m m' RO MU LOW a Ha.
  pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R.
  assert (Hlt : bv_unsigned a < 2 ^ 20).
  { destruct (Z_lt_le_dec (bv_unsigned a) (2 ^ 20)) as [Hl|Hl]; [exact Hl|]. exfalso.
    rewrite <- (Z_to_bv_bv_unsigned a) in Ha. rewrite ro_addr_hi in Ha by lia. discriminate Ha. }
  unfold mrd. rewrite (MU a); [exact (RO a Ha)|]. apply LOW. lia.
Qed.

Lemma pres_mkR : forall (regs R : bvmap 5 word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  Regs6ss.xregs_eqv (mkR x1 (getr regs 2) (getr regs 3) (getr regs 4) x5 x6 x7 (getr regs 8) (getr regs 9)
    x10 x11 x12 x13 x14 x15 x16 x17 (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
    (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) x28 x29 x30 x31) R ->
  regs_preserved regs R.
Proof.
  intros regs R x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 X r Hr.
  unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X) by reflexivity; reflexivity|]).
  subst r; rewrite (getr_of_eqv _ _ _ X) by reflexivity; reflexivity.
Qed.
