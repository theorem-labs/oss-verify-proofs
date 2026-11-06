(* Proof of fp_hdr3_stmt (diginet_frame_parse_segs.v): the footprint run of diginet_frame_parse in image B from
   FP_RD2R (0x8225c, the return from the second rd32 call) to the diginet_sum16 call (0x823a4, `jal` 0x81e30,
   ra = FP_SUMR 0x823a8). It stores the ack counter (f + 24, rd32's result), retry (f + 28, buf[26..27]), cmd
   (f + 30, buf[28]), num_commands (f + 31, buf[29]), body (f + 32), body_len (f + 40) and pad_len (f + 48), and
   calls diginet_sum16 with a0 = buf + 30, a1 = body_len.

   Each instruction is stepped with StepF's step. Each access side goal is closed from an rng fact for the accessed
   range: buf's bytes, the 64 bytes at f, and for each shadow load at (a >> 3) + ASAN_K the one-byte range that
   fpbhdr3_shrng1 cuts from the shadow range of buf or of f.
   The errpath_* calls (errpath_load1 / store1 / store2 / store4 / store8, in the slow-path block 0x824c8 ..
   0x82588) are not reached:
   - the shadow byte of each store of f (f + 24, 28, 30, 31 and the granules of f + 32, 40, 48) is 0, because the
     last byte of its 8-byte granule lies in the addressable range (fpbhdr3_g0), so the `bnez` after its load is
     not taken;
   - for buf + 26 .. buf + 29 the shadow byte k is 0 or (a mod 8) < k (the addressable premise); when k <> 0 the
     slow path (`andi` 7, `blt`) computes that compare and goes back to the instruction after the `bnez`. The slow
     path writes one scratch register that the code writes again before it reads it; fpbhdr3_join proves the rest
     of the run once for any value of that register.
   The UBSan branches to the unimp word 0x82428 are not taken:
   - 0x82278, 0x822d8, 0x82310 `li a2,-K; bltu a2,s3` (s3 = buf + 14) and 0x82348 `bltu a2,s2` (s2 = buf): taken
     only when buf + 14 (or buf) is above 2^64 - K, refuted by buf + length b <= 2^47;
   - 0x82284 `addi a0,s2,26; li a1,-1; beq a0,a1`: taken only when buf + 26 = 2^64 - 1, refuted the same way.
   The `sw` at 0x82274 stores the low 32 bits of rd32's sign-extended result; they are the bytes of the ack counter
   (fpbhdr3_le4_sx32), so the cell at f + 24 is C4 of fr_ack b (fpbhdr3_rw_c4).
   The stores change only [f, f + 64); the shadow bytes lie outside it (fpbhdr3_shM), so the addressable facts and
   the shadow bytes hold in the memory after the stores. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof DgnTransportBSyms
  DgnTransportBAddr diginet_frame_parse_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- the arithmetic of rd16 (slli and or) ---- *)

Lemma fpbhdr3_testbit_split : forall x y k i, 0 <= k -> 0 <= x < 2^k -> 0 <= i ->
  Z.testbit (x + y * 2^k) i = if i <? k then Z.testbit x i else Z.testbit y (i - k).
Proof.
  intros x y k i Hk Hx Hi. destruct (Z.ltb_spec i k) as [L|L].
  - rewrite <- (Z.mod_pow2_bits_low (x + y * 2^k) k i) by lia.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by lia. reflexivity.
  - replace i with ((i - k) + k) at 1 by lia. rewrite <- Z.div_pow2_bits by lia.
    rewrite Z.div_add by (apply Z.pow_nonzero; lia). rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma fpbhdr3_lor_shl : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
Proof.
  intros x y k Hk Hx Hy. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, fpbhdr3_testbit_split by lia.
  destruct (Z.ltb_spec i k).
  - rewrite Z.mul_pow2_bits_low by lia. apply orb_false_r.
  - rewrite Z.mul_pow2_bits by lia. rewrite (testbit_high_false x k i) by lia. reflexivity.
Qed.

(* rd16 at index i: (p[0] << 8) | p[1], as slli and or compute it. *)
Lemma fpbhdr3_pack16 : forall l i,
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
  rewrite Z.lor_comm, fpbhdr3_lor_shl by lia. lia.
Qed.

(* srli 3 of an address held as a number. *)
Lemma fpbhdr3_shr : forall z, 0 <= z < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 z)) 3 = z / 8.
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* ---- the store of rd32's result ---- *)

(* `sw` stores the low 32 bits; sign extension from bit 31 leaves them. *)
Lemma fpbhdr3_le4_sx32 : forall v : word, le4 (sx32 v) = le4 v.
Proof.
  intros v. unfold le4, sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (bv_unsigned v)) 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

(* A C4 cell holds the same bytes for two words of the same low 32 bits. *)
Lemma fpbhdr3_rw_c4 : forall m A pre post v v',
  rw_cells rsegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells rsegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre post v v' [[WF BA] WR] E. split; [split|].
  - apply cells_wf_app in WF. apply cells_wf_app. cbn [cells_wf cell_wf] in *. tauto.
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite <- E. exact BA.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact WR.
Qed.

(* ---- shadow bytes ---- *)

Lemma fpbhdr3_signed0 : forall k : byte, bv_signed k = 0 -> k = Z_to_bv 8 0.
Proof.
  intros k H. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0.
  pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma fpbhdr3_sh_na : forall x, app_mem x -> ~ app_mem (x / 8 + ASAN_K).
Proof.
  intros x H. unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* The one shadow byte of p + i inside the shadow range of [p, p + n). *)
Lemma fpbhdr3_shrng1 : forall RNG p n i, fp_shrng RNG p n -> 0 <= p -> 0 <= i < n ->
  ExecF.rng RNG ((p + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG p n i H Hp Hi. unfold fp_shrng, shadow_addr in H.
  assert (L1 : p / 8 <= (p + i) / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : (p + i) / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  apply (rng_sub' _ _ _ _ _ H). lia.
Qed.

(* The shadow byte of p + c is 0 when the last byte of its granule lies in the addressable [p, p + n). *)
Lemma fpbhdr3_g0 : forall RNG m p n c, addressable m p n -> fp_shrng RNG p n -> 0 <= c -> c + 7 < n ->
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
  split; [exact APc|]. split; [|exact (fpbhdr3_shrng1 RNG p n c SH P0 ltac:(lia))].
  rewrite MK. f_equal. apply fpbhdr3_signed0. lia.
Qed.

(* The shadow byte k of p + i: 0, or (p + i) mod 8 < k. *)
Lemma fpbhdr3_b : forall RNG m p n i, addressable m p n -> fp_shrng RNG p n -> 0 <= i < n ->
  app_mem (p + i) /\ ExecF.rng RNG ((p + i) / 8 + ASAN_K) 1 /\ 0 <= (p + i) mod 8 < 8 /\
  exists k, mrd rsegs m (wa ((p + i) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ ((p + i) mod 8 < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros RNG m p n i ADR SH Hi. pose proof ADR as (P0 & N0 & PE & AB).
  destruct (AB i Hi) as (APi & k & MK & SK). unfold shadow_addr, shadow_ok in MK, SK.
  split; [exact APi|]. split; [exact (fpbhdr3_shrng1 RNG p n i SH P0 Hi)|].
  split; [apply Z.mod_pos_bound; lia|]. exists k. split; assumption.
Qed.

(* A shadow byte lies outside the 64 bytes at f, so the stores to f leave it. *)
Lemma fpbhdr3_shM : forall m m' f x k, addressable m f 64 -> app_mem x ->
  mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k -> munch [(f, f + 64)] m m' ->
  mrd rsegs m' (wa (x / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' f x k ADf Ax MK MU.
  pose proof (fpbhdr3_sh_na x Ax) as N.
  pose proof ADf as (P0 & N0 & PE & AB).
  assert (R : 0 <= x / 8 + ASAN_K < 2^64)
    by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia).
  apply (mrd_tp m m' f (f + 64) _ k MU R); [|exact MK].
  destruct (Z_lt_le_dec (x / 8 + ASAN_K) f) as [L|L]; [left; exact L|].
  destruct (Z_lt_le_dec (x / 8 + ASAN_K) (f + 64)) as [L2|L2]; [|right; exact L2].
  exfalso. destruct (AB (x / 8 + ASAN_K - f) ltac:(lia)) as (Ay & _).
  replace (f + (x / 8 + ASAN_K - f)) with (x / 8 + ASAN_K) in Ay by lia. exact (N Ay).
Qed.

Lemma fpbhdr3_shR : forall m m' f x k, addressable m f 64 -> app_mem x ->
  mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k -> munch [(f, f + 64)] m m' ->
  ov_read_bytes rsegs m' (wa (x / 8 + ASAN_K)) 1 = Some [k].
Proof. intros m m' f x k ADf Ax MK MU. apply rd1. exact (fpbhdr3_shM m m' f x k ADf Ax MK MU). Qed.

Lemma fpbhdr3_addr_tp : forall m m' f p n, munch [(f, f + 64)] m m' -> addressable m f 64 ->
  addressable m p n -> addressable m' p n.
Proof.
  intros m m' f p n MU ADf (P0 & N0 & PE & AB).
  split; [exact P0|]. split; [exact N0|]. split; [exact PE|].
  intros i Hi. destruct (AB i Hi) as (Ap & k & MK & SK).
  split; [exact Ap|]. exists k. split; [|exact SK].
  unfold shadow_addr in *. exact (fpbhdr3_shM m m' f (p + i) k ADf Ap MK MU).
Qed.

Lemma fpbhdr3_rw_ext : forall m A cs cs', rw_cells rsegs m A cs -> cs = cs' -> rw_cells rsegs m A cs'.
Proof. intros; subst; assumption. Qed.

(* ---- tactics ---- *)

(* One step, then the shift of an address to its shadow index and the rd16 packing in the registers. *)
Ltac fpbhdr3_norm :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?z)) 3] => rewrite (fpbhdr3_shr z) by lia
  end;
  rewrite ?fpbhdr3_pack16.
Ltac fpbhdr3_st := step; fpbhdr3_norm.

(* The byte buf[i] at the current memory, read with HB (bytes_at of buf there). *)
Ltac fpbhdr3_ldb HB i R :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (rd1 mc _ _ (bytes_nth mc _ _ i HB ltac:(lia))) as R;
    let z := eval vm_compute in (Z.of_nat i) in change (Z.of_nat i) with z in R
  end.

(* A `bnez` on a closed shadow value 0: not taken. *)
Ltac fpbhdr3_nz :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in
      replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* A UBSan branch to the unimp word: taken only past the bound buf + length b <= 2^47. *)
Ltac fpbhdr3_ub :=
  let H := fresh "HU" in
  if_cases H;
  [ exfalso; zify_cond H;
    first [ lia | rewrite ?unsigned_lit in H by lia; lia
          | rewrite ?unsigned_lit_wrap in H; Z.div_mod_to_equations; lia ]
  | ].

(* The `bnez` on the shadow byte k of the buf byte at z, and its slow path (`andi` 7, `blt` back to the
   instruction after the `bnez`) when k <> 0: (z mod 8) < k. *)
Ltac fpbhdr3_bchk k SK z MB :=
  fpbhdr3_st;
  let C := fresh "C" in let C' := fresh "C'" in
  destruct SK as [C|[C C']];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
    fpbhdr3_st; fpbhdr3_st;
    rewrite land7, (unsigned_lit z) by lia;
    rewrite (lts_low (z mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

(* At a check whose slow path writes register r and returns to T (the instruction after the `bnez`): prove the
   run from T once, for any value x of r, and close the check (chk) with it. *)
Ltac fpbhdr3_join r T chk :=
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

Theorem fp_hdr3_holds : fp_hdr3_stmt.
Proof.
  unfold fp_hdr3_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf f b fj LFJ PRE.
  fp_lits.
  destruct PRE as (FC0 & Hb0 & Hb1 & Hf0 & Hf1 & HB & RW & CS & DJ & ADb & ADf & RGb & RGf & SHb & SHf).
  destruct (fr_code_ok b FC0) as (L30 & _ & NB1 & NB2).
  unfold fp_hdr2_cells in RW. clear CS.
  pose proof (munch_refl [(f, f + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x8225c addi a1, s0, 24; srli a2; add a2; 0x82268 lb a2: the shadow byte of f + 24 (0); 0x8226c bnez a2 *)
  destruct (fpbhdr3_g0 RNG m f 64 24 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP G MU) as R. fpbhdr3_st. clear R.
  fpbhdr3_st. fpbhdr3_nz. clear AP G RS.
  (* 0x82270 li a2, -13; 0x82274 sw a0, 0(a1): the ack counter at f + 24; 0x82278 bltu a2, s3 (UBSan) *)
  do 2 fpbhdr3_st.
  fpbhdr3_st. fpbhdr3_ub.
  (* 0x8227c addi a0, s2, 26; li a1, -1; 0x82284 beq a0, a1 (UBSan) *)
  do 2 fpbhdr3_st.
  fpbhdr3_st. fpbhdr3_ub.
  (* 0x82288 srli a1, a0, 3; add a1; 0x82290 lb a1: k26 of buf + 26 *)
  destruct (fpbhdr3_b RNG m buf _ 26 ADb SHb ltac:(lia)) as (AP & RS & MB & k26 & MK & SK).
  do 2 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP MK MU) as R. fpbhdr3_st. clear R.
  (* 0x82294 bnez a1; slow path 0x824dc andi a2, a0, 7; 0x824e0 blt a2, a1 *)
  fpbhdr3_join 12 0x8b440 ltac:(fpbhdr3_bchk k26 SK (buf + 26) MB).
  clear AP RS MB MK SK.
  (* 0x82298 addi a1, s2, 27; srli a2; add a2; lb a3: k27 of buf + 27; 0x822a8 lbu a2 = buf[26] *)
  destruct (fpbhdr3_b RNG m buf _ 27 ADb SHb ltac:(lia)) as (AP & RS & MB & k27 & MK & SK).
  do 3 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP MK MU) as R. fpbhdr3_st. clear R.
  fpbhdr3_ldb HB 26%nat R. fpbhdr3_st. clear R.
  (* 0x822ac bnez a3; slow path 0x824e8 andi a0, a1, 7; 0x824ec blt a0, a3 *)
  fpbhdr3_join 10 0x8b458 ltac:(fpbhdr3_bchk k27 SK (buf + 27) MB).
  clear AP RS MB MK SK.
  (* 0x822b0 addi a0, s0, 28; srli a3; add a3; lb a3: the shadow byte of f + 28 (0); 0x822c0 lbu a1 = buf[27];
     0x822c4 bnez a3 *)
  destruct (fpbhdr3_g0 RNG m f 64 28 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP G MU) as R. fpbhdr3_st. clear R.
  fpbhdr3_ldb HB 27%nat R. fpbhdr3_st. clear R.
  fpbhdr3_st. fpbhdr3_nz. clear AP G RS.
  (* 0x822c8 slli a2; or a1 (retry = be16 b 26); li a2, -15; 0x822d4 sh a1, 0(a0) at f + 28;
     0x822d8 bltu a2, s3 (UBSan) *)
  do 4 fpbhdr3_st.
  fpbhdr3_st. fpbhdr3_ub.
  (* 0x822dc addi a0, s2, 28; srli a1; add a1; lb a1: k28 of buf + 28 *)
  destruct (fpbhdr3_b RNG m buf _ 28 ADb SHb ltac:(lia)) as (AP & RS & MB & k28 & MK & SK).
  do 3 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP MK MU) as R. fpbhdr3_st. clear R.
  (* 0x822ec bnez a1; slow path 0x82508 andi a2, a0, 7; 0x8250c blt a2, a1 *)
  fpbhdr3_join 12 0x8b498 ltac:(fpbhdr3_bchk k28 SK (buf + 28) MB).
  clear AP RS MB MK SK.
  (* 0x822f0 addi a1, s0, 30; srli a2; add a2; lb a2: the shadow byte of f + 30 (0); 0x82300 lbu a0 = buf[28];
     0x82304 bnez a2 *)
  destruct (fpbhdr3_g0 RNG m f 64 30 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP G MU) as R. fpbhdr3_st. clear R.
  fpbhdr3_ldb HB 28%nat R. fpbhdr3_st. clear R.
  fpbhdr3_st. fpbhdr3_nz. clear AP G RS.
  (* 0x82308 li a2, -16; 0x8230c sb a0, 0(a1): cmd at f + 30; 0x82310 bltu a2, s3 (UBSan) *)
  fpbhdr3_st.
  fpbhdr3_st. rewrite le1_zxb. mem_after_store.
  fpbhdr3_st. fpbhdr3_ub.
  (* 0x82314 addi a0, s2, 29; srli a1; add a1; lb a1: k29 of buf + 29 *)
  destruct (fpbhdr3_b RNG m buf _ 29 ADb SHb ltac:(lia)) as (AP & RS & MB & k29 & MK & SK).
  do 3 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP MK MU) as R. fpbhdr3_st. clear R.
  (* 0x82324 bnez a1; slow path 0x82524 andi a2, a0, 7; 0x82528 blt a2, a1 *)
  fpbhdr3_join 12 0x8b4d0 ltac:(fpbhdr3_bchk k29 SK (buf + 29) MB).
  clear AP RS MB MK SK.
  (* 0x82328 addi a1, s0, 31; srli a2; add a2; lb a2: the shadow byte of f + 31 (0); 0x82338 lbu a0 = buf[29];
     0x8233c bnez a2 *)
  destruct (fpbhdr3_g0 RNG m f 64 31 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP G MU) as R. fpbhdr3_st. clear R.
  fpbhdr3_ldb HB 29%nat R. fpbhdr3_st. clear R.
  fpbhdr3_st. fpbhdr3_nz. clear AP G RS.
  (* 0x82340 li a2, -31; 0x82344 sb a0, 0(a1): num_commands at f + 31; 0x82348 bltu a2, s2 (UBSan) *)
  fpbhdr3_st.
  fpbhdr3_st. rewrite le1_zxb. mem_after_store.
  fpbhdr3_st. fpbhdr3_ub.
  (* 0x8234c addi a0, s0, 32; srli a1; add a1; lbu a1: the shadow byte of the granule of f + 32 (0);
     0x8235c bnez a1 *)
  destruct (fpbhdr3_g0 RNG m f 64 32 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 3 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP G MU) as R. fpbhdr3_st. clear R.
  fpbhdr3_st. fpbhdr3_nz. clear AP G RS.
  (* 0x82360 addi a0, s2, 30; addi a1, s0, 40; 0x82368 sd a0, 32(s0): body at f + 32 *)
  do 3 fpbhdr3_st.
  (* 0x8236c srli a2, a1, 3; add a2; lbu a2: the granule of f + 40 (0); 0x82378 bnez a2 *)
  destruct (fpbhdr3_g0 RNG m f 64 40 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 2 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP G MU) as R. fpbhdr3_st. clear R.
  fpbhdr3_st. fpbhdr3_nz. clear AP G RS.
  (* 0x8237c addi a1, s6, -16; addi a2, s0, 48; 0x82384 sd a1, 40(s0): body_len at f + 40 *)
  do 3 fpbhdr3_st.
  (* 0x82388 srli a3, a2, 3; add a3; lbu a3: the granule of f + 48 (0); 0x82394 bnez a3 *)
  destruct (fpbhdr3_g0 RNG m f 64 48 ADf SHf ltac:(lia) ltac:(lia)) as (AP & G & RS).
  do 2 fpbhdr3_st.
  pose proof (fpbhdr3_shR m _ f _ _ ADf AP G MU) as R. fpbhdr3_st. clear R.
  fpbhdr3_st. fpbhdr3_nz. clear AP G RS.
  (* 0x82398 sub a2, s1, s6; addi a2, -14; 0x823a0 sd a2, 48(s0): pad_len at f + 48 *)
  do 3 fpbhdr3_st.
  (* 0x823a4 jal diginet_sum16: ra = 0x823a8, a0 = buf + 30, a1 = body_len *)
  fpbhdr3_st.
  (* the 64 bytes at f hold fp_hdr_cells; the cell of the ack counter after fpbhdr3_le4_sx32 *)
  apply evtF_done. hnf.
  do 7 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  unfold fp_body_pre.
  refine (conj FC0 (conj Hb0 (conj Hb1 (conj Hf0 (conj Hf1 (conj HB (conj _ (conj eq_refl (conj DJ
    (conj (fpbhdr3_addr_tp _ _ _ _ _ MU ADf ADb) (conj (fpbhdr3_addr_tp _ _ _ _ _ MU ADf ADf)
    (conj RGb (conj RGf (conj SHb SHf)))))))))))))).
  unfold fp_hdr_cells.
  eapply (fpbhdr3_rw_c4 _ _ [_; _; _; _; _; _; _] _ (sx32 (Z_to_bv 64 (fr_ack b))));
    [| apply fpbhdr3_le4_sx32].
  cbn [app].
  eapply fpbhdr3_rw_ext; [exact RW|].
  rewrite ?skipn_skipn.
  repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end.
  all: first [ reflexivity
             | unfold fr_cmd, fr_ncmds, at8; rewrite b8_bz; reflexivity
             | f_equal; rewrite !unsigned_lit by lia; unfold fr_pad_len, fr_body_len; f_equal; lia ].
Qed.
