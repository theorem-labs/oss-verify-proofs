(* Proof of fp_hdr1_stmt (diginet_frame_parse_segs.v): the run of diginet_frame_parse in fuzz_frame.asan-ubsan
   from FP_RET2 (0x8218c) to the first rd32 call (`jal` 0x8258c at 0x82230, ra = FP_RD1R 0x82234), stepped with
   StepF's step. It stores the EtherType 0x885f at f + 12, numbytes (s6) at f + 16 and the sum be16 b 16 (buf[16],
   buf[17]) at f + 18, sets s4 = f + 18, s7 = ((f + 18) >> 3) + ASAN_K (fp_sh18 f) and a0 = buf + 18.
   Each load or store of buf or f follows the check of its shadow byte k at (a >> 3) + ASAN_K. The addressable
   premises give k = 0 or (a mod 8) + size - 1 < k (fpbhdr1_shk), so each check passes, directly or through the
   compare of its slow path (0x82464, 0x82474, 0x82484, 0x82490, 0x824a0), and no errpath_* call is reached. Both
   ways of a check reach the same pc with the same state but one scratch register (fpbhdr1_merge cuts the run there).
   The three UBSan branches to the unimp word 0x82428 are not taken: 0x821c8 and 0x82228 (`bltu` of 2^64 - 3 and
   2^64 - 5 against s3 = buf + 14) and 0x821d4 (`beq` of buf + 16 and 2^64 - 1) would need buf + 16 > 2^64 - 6,
   against fp_body_pre's buf + length b <= 2^47.
   The stores write only [f, f + 64); the shadow bytes of buf and f lie outside it (fpbhdr1_sh_out), so the
   addressable facts and the bytes of buf (f and buf are disjoint) hold at the new memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_segs.
Import ListNotations.
Open Scope Z_scope.

(* ---- the shadow bytes ---- *)

(* The shadow byte of the granule of p + j, for an access of s bytes (1 <= s <= 8) inside the addressable range
   [p, p + n): 0, or (p + j) mod 8 + s - 1 < k, the compare of the slow path. When the access runs past its
   granule, the granule's last byte lies in the range, so k = 0. *)
Lemma fpbhdr1_shk : forall m p n j s, addressable m p n -> 0 <= j -> j + s <= n -> 1 <= s <= 8 ->
  app_mem (p + j) /\
  exists k, mrd rsegs m (wa ((p + j) / 8 + ASAN_K)) = Some k /\
            (bv_signed k = 0 \/ ((p + j) mod 8 + (s - 1) < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m p n j s (P0 & N0 & PE & AB) Hj Hjs Hs.
  destruct (AB j ltac:(lia)) as (APP & _).
  split; [exact APP|].
  pose proof (Z.mod_pos_bound (p + j) 8 ltac:(lia)) as MB.
  destruct (Z_le_gt_dec ((p + j) mod 8 + (s - 1)) 7) as [LE|GT].
  - destruct (AB (j + (s - 1)) ltac:(lia)) as (_ & k & MK & SK).
    assert (E1 : (p + (j + (s - 1))) / 8 = (p + j) / 8) by (Z.div_mod_to_equations; lia).
    assert (E2 : (p + (j + (s - 1))) mod 8 = (p + j) mod 8 + (s - 1)) by (Z.div_mod_to_equations; lia).
    unfold shadow_addr in MK. unfold shadow_ok in SK. rewrite E1 in MK. rewrite E2 in SK.
    exists k. split; [exact MK|]. lia.
  - destruct (AB (j + (7 - (p + j) mod 8)) ltac:(lia)) as (_ & k & MK & SK).
    assert (E1 : (p + (j + (7 - (p + j) mod 8))) / 8 = (p + j) / 8) by (Z.div_mod_to_equations; lia).
    assert (E2 : (p + (j + (7 - (p + j) mod 8))) mod 8 = 7) by (Z.div_mod_to_equations; lia).
    unfold shadow_addr in MK. unfold shadow_ok in SK. rewrite E1 in MK. rewrite E2 in SK.
    exists k. split; [exact MK|]. lia.
Qed.

(* The shadow byte of an application address lies outside the 64 bytes at f (application memory). *)
Lemma fpbhdr1_sh_out : forall m f x, addressable m f 64 -> app_mem x ->
  0 <= x / 8 + ASAN_K < 2^64 /\ (x / 8 + ASAN_K < f \/ f + 64 <= x / 8 + ASAN_K).
Proof.
  intros m f x (P0 & N0 & PE & AB) Ax.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
  assert (Q : 0 <= x / 8 /\ 8 * (x / 8) <= x) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  set (q := x / 8) in *.
  split; [lia|].
  destruct (Z_lt_ge_dec (q + 2147450880) f) as [L|L]; [left; exact L|].
  destruct (Z_lt_ge_dec (q + 2147450880) (f + 64)) as [L2|L2]; [|right; lia].
  exfalso. destruct (AB (q + 2147450880 - f) ltac:(lia)) as (Ay & _).
  replace (f + (q + 2147450880 - f)) with (q + 2147450880) in Ay by lia.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ay. lia.
Qed.

(* A shadow byte read on m reads the same after stores into [f, f + 64). *)
Lemma fpbhdr1_sh_tp : forall m m' f x k, munch [(f, f + 64)] m m' -> addressable m f 64 -> app_mem x ->
  mrd rsegs m (wa (x / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (x / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' f x k MU AF Ax H. destruct (fpbhdr1_sh_out m f x AF Ax) as (R & O).
  exact (mrd_tp m m' f (f + 64) _ k MU R O H).
Qed.

(* The addressable facts carry across stores into [f, f + 64). *)
Lemma fpbhdr1_addr_tp : forall m m' f p n, munch [(f, f + 64)] m m' -> addressable m f 64 ->
  addressable m p n -> addressable m' p n.
Proof.
  intros m m' f p n MU AF (P0 & N0 & PE & AB). split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (AB i Hi) as (APP & k & MK & SK). split; [exact APP|]. exists k. split; [|exact SK].
  unfold shadow_addr in *. exact (fpbhdr1_sh_tp m m' f (p + i) k MU AF APP MK).
Qed.

(* The shadow byte of p + i, 0 <= i < n, lies in the shadow range of [p, p + n). *)
Lemma fpbhdr1_shrng : forall RNG p n i, 0 <= i < n -> fp_shrng RNG p n ->
  ExecF.rng RNG ((p + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG p n i Hi H. unfold fp_shrng, shadow_addr in H. eapply rng_sub'; [exact H|].
  Z.div_mod_to_equations. lia.
Qed.

(* ---- the sum: rd16 of buf[16], buf[17] ---- *)

Lemma fpbhdr1_testbit_split : forall x y k i, 0 <= k -> 0 <= x < 2^k -> 0 <= i ->
  Z.testbit (x + y * 2^k) i = if i <? k then Z.testbit x i else Z.testbit y (i - k).
Proof.
  intros x y k i Hk Hx Hi. destruct (Z.ltb_spec i k) as [L|L].
  - rewrite <- (Z.mod_pow2_bits_low (x + y * 2^k) k i) by lia.
    rewrite Z.mod_add by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by lia. reflexivity.
  - replace i with ((i - k) + k) at 1 by lia. rewrite <- Z.div_pow2_bits by lia.
    rewrite Z.div_add by (apply Z.pow_nonzero; lia). rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma fpbhdr1_lor_shl : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
Proof.
  intros x y k Hk Hx Hy. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, fpbhdr1_testbit_split by lia.
  destruct (Z.ltb_spec i k).
  - rewrite Z.mul_pow2_bits_low by lia. apply orb_false_r.
  - rewrite Z.mul_pow2_bits by lia. rewrite (testbit_high_false x k i) by lia. reflexivity.
Qed.

(* rd16 at index i: (p[0] << 8) | p[1], as slli and or compute it. *)
Lemma fpbhdr1_pack16 : forall l i,
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
  rewrite Z.lor_comm, fpbhdr1_lor_shl by lia. lia.
Qed.

Lemma fpbhdr1_cells_ext : forall m A cs cs', rw_cells rsegs m A cs -> cs = cs' -> rw_cells rsegs m A cs'.
Proof. intros; subst; assumption. Qed.

(* A register value w with U : bv_unsigned w = z is the word of z. *)
Lemma fpbhdr1_word : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros w z U. rewrite <- U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* ---- tactics ---- *)

(* Cut the run at pc cont: the goal at a check, then the run from cont with register r of the current state
   replaced by any value X (both ways of the check reach cont with states that differ only in r). *)
Ltac fpbhdr1_merge r cont X :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
      let t := eval cbv beta iota delta [tset] in (fun x : word => tset p x R) in
      let K := fresh "K" in
      enough (K : forall x : word, evtF segs RNG Q (MS (t x) F (Z_to_bv 64 cont) fc rv m ro));
      [ cbv beta in K | intros X; cbv beta ]
  end.

(* Name the register value x + c (an address) as w, with U : bv_unsigned w = bv_unsigned x + c. *)
Ltac fpbhdr1_gen x c w U :=
  assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned x + c)) = bv_unsigned x + c) by (apply unsigned_lit; lia);
  let Ew := fresh "Ew" in
  remember (Z_to_bv 64 (bv_unsigned x + c)) as w eqn:Ew; clear Ew.

(* The memory of the current state. *)
Ltac fpbhdr1_mem := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mk _) => mk end.

(* The load of the shadow byte k at h (h = (x >> 3) + ASAN_K of an address x): read on m, carried to the current
   memory across the stores into [f, f + 64). *)
Ltac fpbhdr1_shload h k MK AP RS :=
  let M := fresh "M" in let R := fresh "R" in let RH := fresh "RH" in
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH;
  lazymatch goal with
  | MU : munch [(?F0, _)] ?m0 _, ADF : addressable ?m0 ?F0 64 |- _ =>
      pose proof (fpbhdr1_sh_tp _ _ _ _ k MU ADF AP MK) as M
  end;
  unfold ASAN_K in M;
  pose proof (rdw0 _ h _ _ M ltac:(lia)) as R; step; clear R M RH.

(* The load of buf[i] at the register value v = buf + i. *)
Ltac fpbhdr1_ldw v i :=
  let mk := fpbhdr1_mem in
  let F := fresh "F" in let R := fresh "R" in let RW := fresh "RW" in
  lazymatch goal with
  | BB : bytes_at _ mk ?A _, RB : ExecF.rng _ ?A _ |- _ =>
      pose proof (bytes_nth _ _ _ i BB ltac:(lia)) as F;
      let z := eval vm_compute in (Z.of_nat i) in change (Z.of_nat i) with z in F;
      pose proof (rng_sub' _ _ _ (bv_unsigned v) 1 RB ltac:(lia)) as RW
  end;
  pose proof (rdw0 _ v _ _ F ltac:(lia)) as R; step; clear R F RW.

(* The branch on the shadow byte (bnez): not taken when k = 0; taken to the slow path otherwise. *)
Ltac fpbhdr1_bnez SK :=
  rewrite sxb_eq0;
  lazymatch goal with |- context [bv_signed ?k =? 0] =>
    let C := fresh "C" in let C7 := fresh "C7" in
    destruct SK as [C|[C C7]];
    [ rewrite (proj2 (Z.eqb_eq (bv_signed k) 0) C); cbn [negb]
    | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb] ]
  end.

(* The compare of the slow path (blt): (a mod 8) + size - 1 < k, back to the access. *)
Ltac fpbhdr1_slow U :=
  rewrite land7, U;
  lazymatch goal with
  | |- context [bv_lts (Z_to_bv 64 ?x) (sxb ?k)] =>
      rewrite (lts_low x k ltac:(lia)), (proj2 (Z.ltb_lt x (bv_signed k)) ltac:(lia)); cbn [negb]
  end.

(* The store of n bytes at the register value w = f + k is allowed: the 64 bytes at f are writable. *)
Ltac fpbhdr1_hs w U k n :=
  let mk := fpbhdr1_mem in
  lazymatch goal with
  | HC : rw_cells _ mk ?A _ |- _ =>
      assert (HS : store_ok rsegs mk w n = true)
        by (rewrite <- (Z_to_bv_bv_unsigned w), U;
            exact (wr_at_store_ok rsegs mk A 64 k n (proj2 HC) ltac:(lia) ltac:(lia)))
  end.

(* After a store at f + kn through a register: the address as wa (f + kn), then the cells at f updated and the
   facts carried across the store. *)
Ltac fpbhdr1_store kn :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mk ?a ?bs) ?ro) =>
      lazymatch goal with
      | HC : rw_cells _ mk ?A _ |- _ =>
          replace (write_to_mem mk a bs) with (write_to_mem mk (wa (A + Z.of_nat kn)) bs)
            by (f_equal; unfold wa; first [ f_equal; lia | rewrite <- (Z_to_bv_bv_unsigned a); f_equal; lia ])
      end;
      mem_after_store
  end.

(* A UBSan branch to the unimp word, taken (H): an address computed from buf past 2^64 - 6, against
   buf + length b <= 2^47. *)
Ltac fpbhdr1_ub H :=
  exfalso; zify_cond H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 (bv_unsigned ?w + ?c))] =>
      rewrite (unsigned_lit (bv_unsigned w + c)) in H by lia
  end;
  first [ lia | rewrite ?unsigned_lit_wrap in H; Z.div_mod_to_equations; lia ].

Theorem fp_hdr1_holds : fp_hdr1_stmt.
Proof.
  unfold fp_hdr1_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf f b fj
    LFJ PRE.
  destruct PRE as (FC0 & Hb0 & Hb1 & Hf0 & Hf1 & BB & HC & CS & DJ & ADB & ADF & RB & RF & RSB & RSF).
  pose proof (fr_code_ok b FC0) as (L30 & ET & N16 & NL).
  fp_lits.
  (* the shadow bytes of the five checked accesses, on m, and their footprint *)
  destruct (fpbhdr1_shk m f 64 12 2 ADF ltac:(lia) ltac:(lia) ltac:(lia)) as (AP12 & k12 & MK12 & SK12).
  destruct (fpbhdr1_shk m f 64 16 2 ADF ltac:(lia) ltac:(lia) ltac:(lia)) as (AP16 & k16 & MK16 & SK16).
  destruct (fpbhdr1_shk m f 64 18 2 ADF ltac:(lia) ltac:(lia) ltac:(lia)) as (AP18 & k18 & MK18 & SK18).
  destruct (fpbhdr1_shk m buf (Z.of_nat (length b)) 16 1 ADB ltac:(lia) ltac:(lia) ltac:(lia))
    as (APb16 & kb16 & MKb16 & SKb16).
  destruct (fpbhdr1_shk m buf (Z.of_nat (length b)) 17 1 ADB ltac:(lia) ltac:(lia) ltac:(lia))
    as (APb17 & kb17 & MKb17 & SKb17).
  pose proof (fpbhdr1_shrng RNG f 64 12 ltac:(lia) RSF) as RS12.
  pose proof (fpbhdr1_shrng RNG f 64 16 ltac:(lia) RSF) as RS16.
  pose proof (fpbhdr1_shrng RNG f 64 18 ltac:(lia) RSF) as RS18.
  pose proof (fpbhdr1_shrng RNG buf (Z.of_nat (length b)) 16 ltac:(lia) RSB) as RSb16.
  pose proof (fpbhdr1_shrng RNG buf (Z.of_nat (length b)) 17 ltac:(lia) RSB) as RSb17.
  (* f and buf as the words in s0 and s2 *)
  assert (Uf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (Ub : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  set (wF := Z_to_bv 64 f) in *. set (wB := Z_to_bv 64 buf) in *. clearbody wF wB.
  subst f buf.
  unfold fp_copy_cells in HC. unfold ASAN_K in *.
  pose proof (Z.mod_pos_bound (bv_unsigned wF + 12) 8 ltac:(lia)) as MB12.
  pose proof (Z.mod_pos_bound (bv_unsigned wF + 16) 8 ltac:(lia)) as MB16.
  pose proof (Z.mod_pos_bound (bv_unsigned wF + 18) 8 ltac:(lia)) as MB18.
  pose proof (Z.mod_pos_bound (bv_unsigned wB + 16) 8 ltac:(lia)) as MBb16.
  pose proof (Z.mod_pos_bound (bv_unsigned wB + 17) 8 ltac:(lia)) as MBb17.
  pose proof (munch_refl [(bv_unsigned wF, bv_unsigned wF + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x8218c addi a0, s0, 12; 0x82190 srli a1, a0, 3; 0x82194 add a1, a1, s5; 0x82198 lb a1: the shadow byte
     of f + 12 *)
  step. fpbhdr1_gen wF 12 w12 U12.
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 H12.
  fpbhdr1_shload h12 k12 MK12 AP12 RS12.
  (* 0x8219c bnez a1; slow path 0x82464 andi a2, a0, 7; addi a2, a2, 1; blt a2, a1 back to 0x821a0 *)
  fpbhdr1_merge 12 0x8b348 x2.
  { step. fpbhdr1_bnez SK12; [apply K | do 3 step; fpbhdr1_slow U12; apply K]. }
  (* 0x821a0 lui a1, 9; 0x821a4 addi a0, s0, 16; 0x821a8 addi a1, a1, -1953; 0x821ac sh a1, 12(s0): the
     EtherType 0x885f at f + 12 *)
  step. step. fpbhdr1_gen wF 16 w16 U16.
  step. step.
  (* 0x821b0 srli a1, a0, 3; 0x821b4 add a1, a1, s5; 0x821b8 lb a1: the shadow byte of f + 16 *)
  step. gen_shr w16 g16 G16. rewrite U16 in G16.
  step. gen_addi g16 h16 H16.
  fpbhdr1_shload h16 k16 MK16 AP16 RS16.
  (* 0x821bc bnez a1; slow path 0x82474 andi a2, a0, 7; addi a2, a2, 1; blt a2, a1 back to 0x821c0 *)
  fpbhdr1_merge 12 0x8b368 x3.
  { step. fpbhdr1_bnez SK16; [apply K | do 3 step; fpbhdr1_slow U16; apply K]. }
  (* 0x821c0 li a1, -3; 0x821c4 sh s6, 0(a0): numbytes at f + 16 *)
  step.
  fpbhdr1_hs w16 U16 16 2%nat.
  step. clear HS. fpbhdr1_store 16%nat.
  (* 0x821c8 bltu a1, s3: UBSan, taken when 2^64 - 3 < buf + 14 *)
  step. if_cases HU1; [fpbhdr1_ub HU1|].
  (* 0x821cc addi a0, s2, 16; 0x821d0 li a1, -1; 0x821d4 beq a0, a1: UBSan, taken when buf + 16 = 2^64 - 1 *)
  step. fpbhdr1_gen wB 16 v16 V16.
  step. step. if_cases HU2; [fpbhdr1_ub HU2|].
  (* 0x821d8 srli a1, a0, 3; 0x821dc add a1, a1, s5; 0x821e0 lb a1: the shadow byte of buf + 16 *)
  step. gen_shr v16 gb16 GB16. rewrite V16 in GB16.
  step. gen_addi gb16 hb16 HB16.
  fpbhdr1_shload hb16 kb16 MKb16 APb16 RSb16.
  (* 0x821e4 bnez a1; slow path 0x82484 andi a2, a0, 7; blt a2, a1 back to 0x821e8 *)
  fpbhdr1_merge 12 0x8b390 x4.
  { step. fpbhdr1_bnez SKb16; [apply K | do 2 step; fpbhdr1_slow V16; apply K]. }
  (* 0x821e8 addi a1, s2, 17; 0x821ec srli a2, a1, 3; 0x821f0 add a2, a2, s5; 0x821f4 lb a2: the shadow byte of
     buf + 17; 0x821f8 lbu a0, 0(a0): buf[16] *)
  step. fpbhdr1_gen wB 17 v17 V17.
  step. gen_shr v17 gb17 GB17. rewrite V17 in GB17.
  step. gen_addi gb17 hb17 HB17.
  fpbhdr1_shload hb17 kb17 MKb17 APb17 RSb17.
  fpbhdr1_ldw v16 16%nat.
  (* 0x821fc bnez a2; slow path 0x82490 andi a3, a1, 7; blt a3, a2 back to 0x82200 *)
  fpbhdr1_merge 13 0x8b3a8 x5.
  { step. fpbhdr1_bnez SKb17; [apply K | do 2 step; fpbhdr1_slow V17; apply K]. }
  (* 0x82200 addi s4, s0, 18; 0x82204 srli s7, s4, 3; 0x82208 add s7, s7, s5; 0x8220c lb a2, 0(s7): the shadow
     byte of f + 18; 0x82210 lbu a1, 0(a1): buf[17] *)
  step. fpbhdr1_gen wF 18 w18 U18.
  step. gen_shr w18 g18 G18. rewrite U18 in G18.
  step. gen_addi g18 h18 H18.
  fpbhdr1_shload h18 k18 MK18 AP18 RS18.
  fpbhdr1_ldw v17 17%nat.
  (* 0x82214 bnez a2; slow path 0x824a0 andi a3, s4, 7; addi a3, a3, 1; blt a3, a2 back to 0x82218 *)
  fpbhdr1_merge 13 0x8b3c0 x6.
  { step. fpbhdr1_bnez SK18; [apply K | do 3 step; fpbhdr1_slow U18; apply K]. }
  (* 0x82218 slli a0, a0, 8; 0x8221c or a0, a0, a1: the sum be16 b 16; 0x82220 li a1, -5; 0x82224 sh a0, 0(s4):
     the sum at f + 18 *)
  step. step. rewrite ?fpbhdr1_pack16.
  step.
  fpbhdr1_hs w18 U18 18 2%nat.
  step. clear HS. fpbhdr1_store 18%nat.
  (* 0x82228 bltu a1, s3: UBSan, taken when 2^64 - 5 < buf + 14 *)
  step. if_cases HU3; [fpbhdr1_ub HU3|].
  (* 0x8222c addi a0, s2, 18; 0x82230 jal rd32 *)
  step. step.
  (* at rd32: s4 = f + 18, s7 = fp_sh18 f; the 64 bytes at f hold fp_hdr1_cells *)
  rewrite (fpbhdr1_word w18 _ U18).
  assert (E7 : bv_unsigned h18 = fp_sh18 (bv_unsigned wF)) by (rewrite H18, G18; unfold fp_sh18, ASAN_K; lia).
  rewrite (fpbhdr1_word h18 _ E7).
  apply evtF_done. hnf.
  do 8 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  unfold fp_body_pre.
  split; [exact FC0|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact BB|].
  split.
  { eapply fpbhdr1_cells_ext; [exact HC|]. unfold fp_hdr1_cells. rewrite ?skipn_skipn. cbn [Nat.add].
    rewrite ET. unfold fr_sum. reflexivity. }
  split; [reflexivity|]. split; [exact DJ|].
  split; [exact (fpbhdr1_addr_tp _ _ _ _ _ MU ADF ADB)|].
  split; [exact (fpbhdr1_addr_tp _ _ _ _ _ MU ADF ADF)|].
  split; [exact RB|]. split; [exact RF|]. split; [exact RSB | exact RSF].
Qed.
