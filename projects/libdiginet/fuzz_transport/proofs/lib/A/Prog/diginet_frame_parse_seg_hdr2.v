(* Proof of fp_hdr2_stmt (diginet_frame_parse_segs.v): the footprint run of diginet_frame_parse in image A from
   FP_HDR2 (0x822a0) to FP_SUMQ (0x82430), which stores the ack counter (f + 24, buf[22..25]), retry (f + 28,
   buf[26..27]), cmd (f + 30, buf[28]), num_commands (f + 31, buf[29]), body (f + 32), body_len (f + 40) and
   pad_len (f + 48).

   Each instruction is stepped with StepF's step. Each access side goal is closed from an rng fact for the accessed
   range: buf's bytes, the 64 bytes at f, and for each shadow load at (a >> 3) + ASAN_K the one-byte range that
   fphdr2_shrng1 cuts from the shadow range of buf or of f.
   The error paths (errpath_load1 / store1 / store2 / store4 / store8) are not reached:
   - the shadow byte of each store of f (f + 24, 28, 30, 31 and the granules of f + 32, 40, 48) and of buf + 22
     is 0, because the last byte of its 8-byte granule lies in the addressable range (fphdr2_g0), so the `bnez`
     after its load is not taken;
   - for buf + 23 .. buf + 29 the shadow byte k is 0 or (a mod 8) < k (the addressable premise); when k <> 0 the
     slow path (`andi` 7, `blt`) computes that compare and goes back to the load. The slow path writes one scratch
     register that the code writes again before it reads it; fphdr2_join proves the rest of the run once for any
     value of that register.
   The stores change only [f, f + 64); the shadow bytes lie outside it (fphdr2_shM), so the addressable facts and
   the shadow bytes hold in the memory after the stores. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof DgnTransportSyms
  DgnTransportAddr diginet_frame_parse_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- the arithmetic of the inlined rd16 / rd32 (as the plain walk of the same function) ---- *)

Lemma fphdr2_testbit_split : forall x y k i, 0 <= k -> 0 <= x < 2^k -> 0 <= i ->
  Z.testbit (x + y * 2^k) i = if i <? k then Z.testbit x i else Z.testbit y (i - k).
Proof.
  intros x y k i Hk Hx Hi. destruct (Z.ltb_spec i k) as [L|L].
  - rewrite <- (Z.mod_pow2_bits_low (x + y * 2^k) k i) by lia.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by lia. reflexivity.
  - replace i with ((i - k) + k) at 1 by lia. rewrite <- Z.div_pow2_bits by lia.
    rewrite Z.div_add by (apply Z.pow_nonzero; lia). rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma fphdr2_lor_shl : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
Proof.
  intros x y k Hk Hx Hy. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, fphdr2_testbit_split by lia.
  destruct (Z.ltb_spec i k).
  - rewrite Z.mul_pow2_bits_low by lia. apply orb_false_r.
  - rewrite Z.mul_pow2_bits by lia. rewrite (testbit_high_false x k i) by lia. reflexivity.
Qed.

(* rd16 at index i: (p[0] << 8) | p[1], as slli and or compute it. *)
Lemma fphdr2_pack16 : forall l i,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (Z_to_bv 8 0)))) 8)))
        (bv_unsigned (zxb (nth (S i) l (Z_to_bv 8 0)))) = be16 l i.
Proof.
  intros l i. unfold be16, at8, bz, b8, zxb.
  set (x0 := bv_unsigned (nth i l (Z_to_bv 8 0))).
  set (x1 := bv_unsigned (nth (S i) l (Z_to_bv 8 0))).
  assert (R0 : 0 <= x0 < 256) by apply byte_range.
  assert (R1 : 0 <= x1 < 256) by apply byte_range.
  rewrite (unsigned_lit x0), (unsigned_lit x1) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (x0 * 2^8)) by lia.
  rewrite Z.lor_comm, fphdr2_lor_shl by lia. lia.
Qed.

(* rd32 at index i: the two high bytes or-ed first, then the rd16 of the two low bytes. *)
Lemma fphdr2_pack32 : forall l i,
  Z.lor (bv_unsigned (Z_to_bv 64
          (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth (S i) l (Z_to_bv 8 0)))) 16)))
                 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (Z_to_bv 8 0)))) 24))))))
        (bv_unsigned (Z_to_bv 64 (be16 l (S (S i))))) = be32 l i.
Proof.
  intros l i. unfold be32, be16, at8, bz, b8, zxb.
  set (x0 := bv_unsigned (nth i l (Z_to_bv 8 0))).
  set (x1 := bv_unsigned (nth (S i) l (Z_to_bv 8 0))).
  set (x2 := bv_unsigned (nth (S (S i)) l (Z_to_bv 8 0))).
  set (x3 := bv_unsigned (nth (S (S (S i))) l (Z_to_bv 8 0))).
  assert (R0 : 0 <= x0 < 256) by apply byte_range.
  assert (R1 : 0 <= x1 < 256) by apply byte_range.
  assert (R2 : 0 <= x2 < 256) by apply byte_range.
  assert (R3 : 0 <= x3 < 256) by apply byte_range.
  rewrite (unsigned_lit x0), (unsigned_lit x1) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x1 * 2^16)), (unsigned_lit (x0 * 2^24)) by lia.
  rewrite (fphdr2_lor_shl (x1 * 2^16) x0 24) by lia.
  rewrite (unsigned_lit (x1 * 2^16 + x0 * 2^24)) by lia.
  rewrite (unsigned_lit (x2 * 2^8 + x3)) by lia.
  rewrite Z.lor_comm.
  replace (x1 * 2^16 + x0 * 2^24) with ((x1 + x0 * 2^8) * 2^16) by ring.
  rewrite (fphdr2_lor_shl (x2 * 2^8 + x3) (x1 + x0 * 2^8) 16) by lia. lia.
Qed.

(* srli 3 of an address held as a number. *)
Lemma fphdr2_shr : forall z, 0 <= z < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 z)) 3 = z / 8.
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* ---- shadow bytes ---- *)

Lemma fphdr2_signed0 : forall k : byte, bv_signed k = 0 -> k = Z_to_bv 8 0.
Proof.
  intros k H. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0.
  pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma fphdr2_sh_na : forall x, app_mem x -> ~ app_mem (x / 8 + ASAN_K).
Proof.
  intros x H. unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* The one shadow byte of p + i inside the shadow range of [p, p + n). *)
Lemma fphdr2_shrng1 : forall RNG p n i, fp_shrng RNG p n -> 0 <= p -> 0 <= i < n ->
  ExecF.rng RNG ((p + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG p n i H Hp Hi. unfold fp_shrng, shadow_addr in H.
  assert (L1 : p / 8 <= (p + i) / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : (p + i) / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  apply (rng_sub' _ _ _ _ _ H). lia.
Qed.

(* The shadow byte of p + c is 0 when the last byte of its granule lies in the addressable [p, p + n). *)
Lemma fphdr2_g0 : forall RNG m p n c, addressable m p n -> fp_shrng RNG p n -> 0 <= c -> c + 7 < n ->
  app_mem (p + c) /\ mrd rsegs m (wa ((p + c) / 8 + ASAN_K)) = Some (Z_to_bv 8 0) /\
  ExecF.rng RNG ((p + c) / 8 + ASAN_K) 1.
Proof.
  intros RNG m p n c ADR SH Hc Hn. pose proof ADR as (P0 & N0 & PE & AB).
  pose proof (Z.mod_pos_bound (p + c) 8 ltac:(lia)) as Mp.
  destruct (AB c ltac:(lia)) as (APc & _).
  destruct (AB (c + 7 - (p + c) mod 8) ltac:(lia)) as (_ & k & MK & SK).
  assert (E1 : (p + (c + 7 - (p + c) mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  assert (E2 : (p + (c + 7 - (p + c) mod 8)) / 8 = (p + c) / 8) by (Z.div_mod_to_equations; lia).
  unfold shadow_addr, shadow_ok in MK, SK. rewrite E2 in MK. rewrite E1 in SK.
  split; [exact APc|]. split; [|exact (fphdr2_shrng1 RNG p n c SH P0 ltac:(lia))].
  rewrite MK. f_equal. apply fphdr2_signed0. lia.
Qed.

(* The shadow byte k of p + i: 0, or (p + i) mod 8 < k. *)
Lemma fphdr2_b : forall RNG m p n i, addressable m p n -> fp_shrng RNG p n -> 0 <= i < n ->
  app_mem (p + i) /\ ExecF.rng RNG ((p + i) / 8 + ASAN_K) 1 /\ 0 <= (p + i) mod 8 < 8 /\
  exists k, mrd rsegs m (wa ((p + i) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ ((p + i) mod 8 < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros RNG m p n i ADR SH Hi. pose proof ADR as (P0 & N0 & PE & AB).
  destruct (AB i Hi) as (APi & k & MK & SK). unfold shadow_addr, shadow_ok in MK, SK.
  split; [exact APi|]. split; [exact (fphdr2_shrng1 RNG p n i SH P0 Hi)|].
  split; [apply Z.mod_pos_bound; lia|]. exists k. split; assumption.
Qed.

(* A shadow byte lies outside the 64 bytes at f, so the stores to f leave it. *)
Lemma fphdr2_shM : forall m m' f x k, addressable m f 64 -> app_mem x ->
  mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k -> munch [(f, f + 64)] m m' ->
  mrd rsegs m' (wa (x / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' f x k ADf Ax MK MU.
  pose proof (fphdr2_sh_na x Ax) as N.
  pose proof ADf as (P0 & N0 & PE & AB).
  assert (R : 0 <= x / 8 + ASAN_K < 2^64)
    by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia).
  apply (mrd_tp m m' f (f + 64) _ k MU R); [|exact MK].
  destruct (Z_lt_le_dec (x / 8 + ASAN_K) f) as [L|L]; [left; exact L|].
  destruct (Z_lt_le_dec (x / 8 + ASAN_K) (f + 64)) as [L2|L2]; [|right; exact L2].
  exfalso. destruct (AB (x / 8 + ASAN_K - f) ltac:(lia)) as (Ay & _).
  replace (f + (x / 8 + ASAN_K - f)) with (x / 8 + ASAN_K) in Ay by lia. exact (N Ay).
Qed.

Lemma fphdr2_shR : forall m m' f x k, addressable m f 64 -> app_mem x ->
  mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k -> munch [(f, f + 64)] m m' ->
  ov_read_bytes rsegs m' (wa (x / 8 + ASAN_K)) 1 = Some [k].
Proof. intros m m' f x k ADf Ax MK MU. apply rd1. exact (fphdr2_shM m m' f x k ADf Ax MK MU). Qed.

Lemma fphdr2_addr_tp : forall m m' f p n, munch [(f, f + 64)] m m' -> addressable m f 64 ->
  addressable m p n -> addressable m' p n.
Proof.
  intros m m' f p n MU ADf (P0 & N0 & PE & AB).
  split; [exact P0|]. split; [exact N0|]. split; [exact PE|].
  intros i Hi. destruct (AB i Hi) as (Ap & k & MK & SK).
  split; [exact Ap|]. exists k. split; [|exact SK].
  unfold shadow_addr in *. exact (fphdr2_shM m m' f (p + i) k ADf Ap MK MU).
Qed.

Lemma fphdr2_rw_ext : forall m A cs cs', rw_cells rsegs m A cs -> cs = cs' -> rw_cells rsegs m A cs'.
Proof. intros; subst; assumption. Qed.

(* ---- tactics ---- *)

(* One step, then the shift of an address to its shadow index and the rd16 / rd32 packing in the registers. *)
Ltac fphdr2_norm :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?z)) 3] => rewrite (fphdr2_shr z) by lia
  end;
  rewrite ?fphdr2_pack32, ?fphdr2_pack16.
Ltac fphdr2_st := step; fphdr2_norm.

(* The byte buf[i] at the current memory, read with HB (bytes_at of buf there). *)
Ltac fphdr2_ldb HB i R :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (rd1 mc _ _ (bytes_nth mc _ _ i HB ltac:(lia))) as R;
    let z := eval vm_compute in (Z.of_nat i) in change (Z.of_nat i) with z in R
  end.

(* A `bnez` on a closed shadow value 0: not taken. *)
Ltac fphdr2_nz :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in
      replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* The `bnez` on the shadow byte k of the buf byte at z, and its slow path (`andi` 7, `blt` back to the load
   at the next instruction) when k <> 0: (z mod 8) < k. *)
Ltac fphdr2_bchk k SK z MB :=
  fphdr2_st;
  let C := fresh "C" in let C' := fresh "C'" in
  destruct SK as [C|[C C']];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
    fphdr2_st; fphdr2_st;
    rewrite land7, (unsigned_lit z) by lia;
    rewrite (lts_low (z mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

(* At a check whose slow path writes register r and returns to T (the instruction after the `bnez`): prove the
   run from T once, for any value x of r, and close the check (chk) with it. *)
Ltac fphdr2_join r T chk :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
      let K := fresh "K" in
      enough (K : forall x : word, evtF segs RNG Q (MS (tset p x R) F (Z_to_bv 64 T) fc rv m ro))
        by (chk; let v := reg_val r in exact (K v));
      let x := fresh "x" in intros x;
      let R' := eval cbv beta iota delta [tset] in (tset p x R) in change (tset p x R) with R'
  end.

(* ---- the run ---- *)

Theorem fp_hdr2_holds : fp_hdr2_stmt.
Proof.
  unfold fp_hdr2_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a0 a3 a4 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf f b fj LFJ PRE.
  fp_lits.
  destruct PRE as (FC0 & Hb0 & Hb1 & Hf0 & Hf1 & HB & RW & CS & DJ & ADb & ADf & RGb & RGf & SHb & SHf).
  destruct (fr_code_ok b FC0) as (L30 & _ & NB1 & NB2).
  unfold fp_hdr1_cells in RW. clear CS.
  pose proof (munch_refl [(f, f + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x822a0 add a5, a5, s3; 0x822a4 lb a0: the shadow byte of buf + 22 (0); 0x822a8 bnez a0 *)
  destruct (fphdr2_g0 RNG m buf _ 22 ADb SHb ltac:(lia) ltac:(lia)) as (AP & G & RS).
  fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP G MU) as R. fphdr2_st. clear R.
  fphdr2_st. fphdr2_nz. clear AP G RS.
  (* 0x822ac addi a0, s1, 23; srli a1; add a1; lb a1: the shadow byte k23 of buf + 23; lbu a3 = buf[22] *)
  destruct (fphdr2_b RNG m buf _ 23 ADb SHb ltac:(lia)) as (AP & RS & MB & k23 & MK & SK).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP MK MU) as R. fphdr2_st. clear R.
  fphdr2_ldb HB 22%nat R. fphdr2_st. clear R.
  (* 0x822c0 bnez a1; slow path 0x825b0 andi a4, a0, 7; 0x825b4 blt a4, a1 *)
  fphdr2_join 14 0x8b940 ltac:(fphdr2_bchk k23 SK (buf + 23) MB).
  clear AP RS MB MK SK.
  (* 0x822c4 addi a0, s1, 24; srli a1; add a1; lb a1: k24 of buf + 24; lbu a4 = buf[23] *)
  destruct (fphdr2_b RNG m buf _ 24 ADb SHb ltac:(lia)) as (AP & RS & MB & k24 & MK & SK).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP MK MU) as R. fphdr2_st. clear R.
  fphdr2_ldb HB 23%nat R. fphdr2_st. clear R.
  (* 0x822d8 bnez a1; slow path 0x825bc andi a5, a0, 7; 0x825c0 blt a5, a1 *)
  fphdr2_join 15 0x8b958 ltac:(fphdr2_bchk k24 SK (buf + 24) MB).
  clear AP RS MB MK SK.
  (* 0x822dc addi a1, s1, 25; srli a0; add a0; lb a0: k25 of buf + 25; lbu a5 = buf[24] *)
  destruct (fphdr2_b RNG m buf _ 25 ADb SHb ltac:(lia)) as (AP & RS & MB & k25 & MK & SK).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP MK MU) as R. fphdr2_st. clear R.
  fphdr2_ldb HB 24%nat R. fphdr2_st. clear R.
  (* 0x822f0 bnez a0; slow path 0x825c8 andi a6, a1, 7; 0x825cc blt a6, a0 *)
  fphdr2_join 16 0x8b970 ltac:(fphdr2_bchk k25 SK (buf + 25) MB).
  clear AP RS MB MK SK.
  (* 0x822f4 addi a0, s0, 24; srli a6; add a6; lb a7: the shadow byte of f + 24 (0); lbu a6 = buf[25];
     0x82308 bnez a7 *)
  destruct (fphdr2_g0 RNG m f 64 24 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP G MU) as R. fphdr2_st. clear R.
  fphdr2_ldb HB 25%nat R. fphdr2_st. clear R.
  fphdr2_st. fphdr2_nz. clear AP G RS.
  (* 0x8230c .. 0x82328: a3 = be32 b 22 (slli, slli, slli, or, or, or), a1 = buf + 26, a5 = (buf + 26) / 8 *)
  do 8 fphdr2_st.
  (* 0x8232c sw a3, 0(a0): the ack counter at f + 24 *)
  fphdr2_st.
  (* 0x82330 add a5; 0x82334 lb a0: k26 of buf + 26 *)
  destruct (fphdr2_b RNG m buf _ 26 ADb SHb ltac:(lia)) as (AP & RS & MB & k26 & MK & SK).
  fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP MK MU) as R. fphdr2_st. clear R.
  (* 0x82338 bnez a0; slow path 0x825e8 andi a3, a1, 7; 0x825ec blt a3, a0 *)
  fphdr2_join 13 0x8b9b8 ltac:(fphdr2_bchk k26 SK (buf + 26) MB).
  clear AP RS MB MK SK.
  (* 0x8233c addi a0, s1, 27; srli a1; add a1; lb a1: k27 of buf + 27; lbu a3 = buf[26] *)
  destruct (fphdr2_b RNG m buf _ 27 ADb SHb ltac:(lia)) as (AP & RS & MB & k27 & MK & SK).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP MK MU) as R. fphdr2_st. clear R.
  fphdr2_ldb HB 26%nat R. fphdr2_st. clear R.
  (* 0x82350 bnez a1; slow path 0x825f8 andi a4, a0, 7; 0x825fc blt a4, a1 *)
  fphdr2_join 14 0x8b9d0 ltac:(fphdr2_bchk k27 SK (buf + 27) MB).
  clear AP RS MB MK SK.
  (* 0x82354 addi a1, s0, 28; srli a4; add a4; lb a4: the shadow byte of f + 28 (0); lbu a0 = buf[27];
     0x82368 bnez a4 *)
  destruct (fphdr2_g0 RNG m f 64 28 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP G MU) as R. fphdr2_st. clear R.
  fphdr2_ldb HB 27%nat R. fphdr2_st. clear R.
  fphdr2_st. fphdr2_nz. clear AP G RS.
  (* 0x8236c slli a3; or a3 (retry = be16 b 26); addi a0, s1, 28; 0x82378 sh a3, 0(a1) at f + 28 *)
  do 3 fphdr2_st.
  fphdr2_st.
  (* 0x8237c srli a1, a0, 3; add a1; lb a1: k28 of buf + 28 *)
  destruct (fphdr2_b RNG m buf _ 28 ADb SHb ltac:(lia)) as (AP & RS & MB & k28 & MK & SK).
  do 2 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP MK MU) as R. fphdr2_st. clear R.
  (* 0x82388 bnez a1; slow path 0x82618 andi a3, a0, 7; 0x8261c blt a3, a1 *)
  fphdr2_join 13 0x8ba08 ltac:(fphdr2_bchk k28 SK (buf + 28) MB).
  clear AP RS MB MK SK.
  (* 0x8238c addi a1, s0, 30; srli a3; add a3; lb a3: the shadow byte of f + 30 (0); lbu a0 = buf[28];
     0x823a0 bnez a3 *)
  destruct (fphdr2_g0 RNG m f 64 30 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP G MU) as R. fphdr2_st. clear R.
  fphdr2_ldb HB 28%nat R. fphdr2_st. clear R.
  fphdr2_st. fphdr2_nz. clear AP G RS.
  (* 0x823a4 sb a0, 0(a1): cmd at f + 30 *)
  fphdr2_st. rewrite le1_zxb. mem_after_store.
  (* 0x823a8 addi a0, s1, 29; srli a1; add a1; lb a1: k29 of buf + 29 *)
  destruct (fphdr2_b RNG m buf _ 29 ADb SHb ltac:(lia)) as (AP & RS & MB & k29 & MK & SK).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP MK MU) as R. fphdr2_st. clear R.
  (* 0x823b8 bnez a1; slow path 0x82634 andi a3, a0, 7; 0x82638 blt a3, a1 *)
  fphdr2_join 13 0x8ba38 ltac:(fphdr2_bchk k29 SK (buf + 29) MB).
  clear AP RS MB MK SK.
  (* 0x823bc addi a1, s0, 31; srli a3; add a3; lb a3: the shadow byte of f + 31 (0); lbu a0 = buf[29];
     0x823d0 bnez a3 *)
  destruct (fphdr2_g0 RNG m f 64 31 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP G MU) as R. fphdr2_st. clear R.
  fphdr2_ldb HB 29%nat R. fphdr2_st. clear R.
  fphdr2_st. fphdr2_nz. clear AP G RS.
  (* 0x823d4 sb a0, 31(s0): num_commands at f + 31 *)
  fphdr2_st. rewrite le1_zxb. mem_after_store.
  (* 0x823d8 addi a0, s0, 32; srli a1; add a1; lbu a1: the shadow byte of the granule of f + 32 (0);
     0x823e8 bnez a1 *)
  destruct (fphdr2_g0 RNG m f 64 32 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP G MU) as R. fphdr2_st. clear R.
  fphdr2_st. fphdr2_nz. clear AP G RS.
  (* 0x823ec addi a1, s1, 30; addi a0, s0, 40; 0x823f4 sd a1, 32(s0): body at f + 32 *)
  do 3 fphdr2_st.
  (* 0x823f8 srli a3, a0, 3; add a3; lbu a3: the granule of f + 40 (0); 0x82404 bnez a3 *)
  destruct (fphdr2_g0 RNG m f 64 40 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 2 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP G MU) as R. fphdr2_st. clear R.
  fphdr2_st. fphdr2_nz. clear AP G RS.
  (* 0x82408 addi a3, s4, -16; addi a0, s0, 48; 0x82410 sd a3, 40(s0): body_len at f + 40 *)
  do 3 fphdr2_st.
  (* 0x82414 srli a4, a0, 3; add a4; lbu a4: the granule of f + 48 (0); 0x82420 bnez a4 *)
  destruct (fphdr2_g0 RNG m f 64 48 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 2 fphdr2_st.
  pose proof (fphdr2_shR m _ f _ _ ADf AP G MU) as R. fphdr2_st. clear R.
  fphdr2_st. fphdr2_nz. clear AP G RS.
  (* 0x82424 sub a4, s2, s4; addi a4, -14; 0x8242c sd a4, 0(a0): pad_len at f + 48 *)
  do 3 fphdr2_st.
  (* 0x82430: a1 = buf + 30, a2 = the sum, a3 = body_len; the 64 bytes at f hold fp_hdr_cells *)
  apply evtF_done. hnf.
  do 6 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  unfold fp_body_pre.
  refine (conj FC0 (conj Hb0 (conj Hb1 (conj Hf0 (conj Hf1 (conj HB (conj _ (conj eq_refl (conj DJ
    (conj (fphdr2_addr_tp _ _ _ _ _ MU ADf ADb) (conj (fphdr2_addr_tp _ _ _ _ _ MU ADf ADf)
    (conj RGb (conj RGf (conj SHb SHf)))))))))))))).
  eapply fphdr2_rw_ext; [exact RW|].
  unfold fp_hdr_cells. rewrite ?skipn_skipn.
  repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end.
  all: first [ reflexivity
             | unfold fr_cmd, fr_ncmds, at8; rewrite b8_bz; reflexivity
             | f_equal; rewrite !unsigned_lit by lia; unfold fr_pad_len, fr_body_len; f_equal; lia ].
Qed.
