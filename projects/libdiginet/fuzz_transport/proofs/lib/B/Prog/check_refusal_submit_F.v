From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_refusal_submit_c check_refusal_submit_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module DS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* Proof of check_refusal_submit_contract_F (image B, entry 0x8640c, frame 32 bytes), with StepF's step: each
   access side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportBList.v, the 87 slots of check_refusal_submit, AF_check_refusal_submit = 0x516c):
     0x8640c-0x86418  addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp): the frame, carved from stk.
     0x8641c-0x86420  a3 = cp & 3; cp mod 4 = 0 gives 0, so bnez a3 does not go to the unimp word 0x86544.
     0x86424-0x8642c  the 8-byte loads of GOT_CELL_K and CELL_K (asan_cells): a5 = 0x7fff8000.
     0x86430-0x86440  a3 = cp + 24 and the check of the byte load there (a4 = its signed shadow byte k; k <> 0
                      goes to 0x86548, where a6 = (cp + 24) & 7 and a6 < k comes back to 0x86444).
     0x86444-0x8644c  t1 = len = c[24]; len < 4 (unsigned) goes to 0x8650c, no system command.
     0x86450-0x8646c  a6 = 0; a7 = 2^64 - 1 - cp; t0 = cp + 3; t1 = len - 3; t2 = cp + 1; t3 = 0xf0; t4 = 0x13;
                      t5 = 0x70.
     0x86470-0x864e0  the loop for i = 0 .. len - 4, with a6 = i counted up: the three unsigned compares with a7
                      (0x86470, 0x86494, 0x864b8, each to the unimp word), the three byte loads c[i], c[i + 1],
                      c[i + 3], each preceded by its shadow check (0x864e4, 0x864f0, 0x864fc are the k <> 0 ways,
                      which come back to the load); a hit (F0 13 xx 70) goes to 0x86528, the last miss to 0x8650c.
     0x8650c-0x86510  (no system command) a0 = -10; rc = -10 would go to the trap path 0x8653c.
     0x86514-0x86524  ld ra; ld s0; ld s1; addi sp,sp,32; ret: the one return, reached by both returning paths.
     0x86528-0x86538  (a system command) a0 = -10; rc <> -10 goes to the trap path; a0 = g_s.queued, the 4-byte
                      load at CHECK_REFUSAL_SUBMIT_QUEUED; a0 <> a2 goes to the trap path, a0 = a2 to 0x86514.
   Why the other paths never run:
     - the branch at 0x86420 to the unimp word: cp & 3 = cp mod 4 = 0 (land3);
     - the branches at 0x86470, 0x86494, 0x864b8 to the unimp word: a7 = 2^64 - 1 - cp, and i + 3 < len <= 32
       with cp + 32 <= APPMEM_END = 2^47 (addressable m cp 32), so i, i and i + 3 are all below a7;
     - the four calls of __asan_report_load1 (0x86554, 0x86564, 0x8655c, 0x86508): each is reached only when the
       signed shadow byte k of a loaded byte a is not 0 and a mod 8 >= k. Every loaded byte lies in [cp, cp + 32),
       and addressable m cp 32 gives, for each, k = 0 or a mod 8 < k (shadow1 below), so each check passes;
     - the trap path (0x8653c, and the unimp word 0x86544 after the call of abort): with no system command it
       needs rc = -10, with a system command rc <> -10 or a g_s.queued other than a2.
       check_refusal_submit_m Bw c rc before = Some _ rules out each case.
   The loop is spec_system_at (zs c) len (DgnSpec.v:255-268), walked by induction on the remaining iteration
   count len - 3 - i with the invariant system_at_loop (zs c) len i (Z.to_nat len) = spec_system_at (zs c) len.
   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payload ranges (off_stk premise), so TMAP_B_kept gives tw_at of the
   same Bw at the new memory. *)

(* ---- the reads and the instrumented-check facts, over image B's rsegs (copies of lib/A/Prog/AsanKAProof.v) ---- *)

Lemma rd1 : forall m a b, mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. rewrite ov_rdn, rdn_unfold, H. reflexivity. Qed.

Lemma rdw0 : forall m (w : word) a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w 1 = Some [b].
Proof. intros m w a b H E. rewrite <- (Z_to_bv_bv_unsigned w), E. apply rd1. exact H. Qed.

Lemma mrd_tp : forall m m' lo hi a b, munch [(lo, hi)] m m' -> 0 <= a < 2^64 -> (a < lo \/ hi <= a) ->
  mrd rsegs m (wa a) = Some b -> mrd rsegs m' (wa a) = Some b.
Proof.
  intros m m' lo hi a b MU Ha Hd H. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma bytes_nth : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  mrd rsegs m (wa (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros m a bs i (H0 & H1 & H) Hi. rewrite H by exact Hi. apply nth_error_nth'. exact Hi.
Qed.

Lemma bytes_tp : forall m m' lo hi a bs, munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.

Lemma byte_signed_range : forall k : byte, -128 <= bv_signed k < 128.
Proof.
  intros k. pose proof (bv_signed_in_range 8 k ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
  change (2 ^ Z.of_N 8 / 2) with 128 in R. lia.
Qed.

Lemma sxb_eq0 : forall k : byte, bv_eqb (sxb k) (Z_to_bv 64 0) = (bv_signed k =? 0).
Proof.
  intros k. unfold sxb, bv_eqb. pose proof (byte_signed_range k).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.eqb_spec (bv_signed k) 0) as [E|E].
  - rewrite E. reflexivity.
  - apply Z.eqb_neq. change (0 mod 2^64) with 0. Z.div_mod_to_equations. lia.
Qed.

Lemma lts_low : forall (x : Z) (k : byte), 0 <= x < 8 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. exact (Z.land_ones x 3 ltac:(lia)). Qed.

(* the alignment test at 0x8641c: andi a3,a0,3 *)
Lemma land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. exact (Z.land_ones x 2 ltac:(lia)). Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Ltac gen_addi x w U := match goal with
  | |- context [Some (Z_to_bv 64 (bv_unsigned x + ?c))] =>
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned x + c)) = bv_unsigned x + c)
        by (apply unsigned_lit; first [lia | Z.div_mod_to_equations; lia]);
      remember (Z_to_bv 64 (bv_unsigned x + c)) as w eqn:Ew; clear Ew
  end.

Ltac gen_shr x w U := match goal with
  | |- context [Some (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3))] =>
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3)) = bv_unsigned x / 8)
        by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; apply unsigned_lit;
            pose proof (bv_unsigned_in_range 64 x) as Rx; unfold bv_modulus in Rx;
            change (2 ^ Z.of_N 64) with (2^64) in Rx;
            split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
      remember (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3)) as w eqn:Ew; clear Ew
  end.

(* ---- the bytes of c, as the model reads them ---- *)

(* the machine's zero-extended byte load, in the model's at8 form *)
Lemma zxb_at8 : forall (l : list byte) (n : nat), zxb (nth n l (Z_to_bv 8 0)) = Z_to_bv 64 (DS.at8 l n).
Proof. reflexivity. Qed.

Lemma at8_range : forall (l : list byte) (n : nat), 0 <= DS.at8 l n < 256.
Proof. intros l n. unfold DS.at8, DS.bz. apply byte_range. Qed.

(* the model reads c as a list Z (zs c); the machine reads one byte at a time *)
Lemma byte_at_zs : forall (l : list byte) (i : Z), DS.byte_at (TW.zs l) i = DS.at8 l (Z.to_nat i).
Proof.
  intros l i. unfold DS.byte_at, TW.zs, DS.at8, DS.bz.
  change 0 with (bv_unsigned (DS.b8 0)) at 1. apply map_nth.
Qed.

(* a one-byte read of the argument block *)
Lemma rdc : forall m p (l : list byte) (n : nat) (a : Z),
  bytes_at rsegs m p l -> (n < length l)%nat -> a = p + Z.of_nat n ->
  ov_read_bytes rsegs m (wa a) 1 = Some [nth n l (Z_to_bv 8 0)].
Proof. intros m p l n a H Hn ->. apply rd1. apply (bytes_nth m p l n H Hn). Qed.

(* ---- spec_system_at's loop (DgnSpec.v:255-268, spec.h:264-270): the three bytes it tests at i ---- *)

Definition hit3 (b : list Z) (i : Z) : bool :=
  (DS.byte_at b i =? 240) && (DS.byte_at b (i + 1) =? DS.SPEC_MAKER)
  && (DS.byte_at b (i + 3) =? DS.SPEC_FN_SYSTEM).

Lemma hit3_at : forall (l : list byte) (i : Z),
  hit3 (TW.zs l) i = (DS.at8 l (Z.to_nat i) =? 240) && (DS.at8 l (Z.to_nat (i + 1)) =? 19)
                     && (DS.at8 l (Z.to_nat (i + 3)) =? 112).
Proof. intros l i. unfold hit3. rewrite !byte_at_zs. reflexivity. Qed.

(* the fuel is any number of iterations the loop can still run *)
Lemma sal_fuel : forall f1 f2 b len i, 0 <= i ->
  (Z.to_nat (len - i) <= f1)%nat -> (Z.to_nat (len - i) <= f2)%nat ->
  DS.system_at_loop b len i f1 = DS.system_at_loop b len i f2.
Proof.
  induction f1 as [|f1 IH]; intros f2 b len i Hi H1 H2.
  - destruct f2 as [|f2]; [reflexivity|].
    cbn [DS.system_at_loop]. replace (i + 3 <? len) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - destruct f2 as [|f2].
    + cbn [DS.system_at_loop]. replace (i + 3 <? len) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + cbn [DS.system_at_loop]. destruct (Z.ltb_spec (i + 3) len) as [L|L]; [|reflexivity].
      destruct ((DS.byte_at b i =? 240) && (DS.byte_at b (i + 1) =? DS.SPEC_MAKER)
                && (DS.byte_at b (i + 3) =? DS.SPEC_FN_SYSTEM)); [reflexivity|].
      apply IH; lia.
Qed.

(* i + 3 >= len: the C loop condition fails, the answer is -1 *)
Lemma sal_end : forall b len i f, ~ (i + 3 < len) -> DS.system_at_loop b len i f = -1.
Proof.
  intros b len i f H. destruct f as [|f]; [reflexivity|].
  cbn [DS.system_at_loop]. replace (i + 3 <? len) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* no F0 13 xx 70 at i: the loop goes on at i + 1 *)
Lemma sal_miss : forall b len i f, 0 <= i -> (Z.to_nat (len - i) <= f)%nat -> i + 3 < len ->
  hit3 b i = false -> DS.system_at_loop b len i f = DS.system_at_loop b len (i + 1) f.
Proof.
  intros b len i f Hi Hf Hlt Hm. destruct f as [|f]; [cbn in Hf; lia|].
  rewrite (sal_fuel (S f) f b len (i + 1)) by lia.
  cbn [DS.system_at_loop]. replace (i + 3 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold hit3 in Hm. rewrite Hm. reflexivity.
Qed.

(* F0 13 xx 70 at i: the loop answers i *)
Lemma sal_hit : forall b len i f, (Z.to_nat (len - i) <= f)%nat -> i + 3 < len ->
  hit3 b i = true -> DS.system_at_loop b len i f = i.
Proof.
  intros b len i f Hf Hlt Hm. destruct f as [|f]; [cbn in Hf; lia|].
  cbn [DS.system_at_loop]. replace (i + 3 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold hit3 in Hm. rewrite Hm. reflexivity.
Qed.

(* ---- bltu / beq / bne of two Z values in a register ---- *)

Lemma ltu_zz : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma eqb_ss : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|Hne]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply Hne. revert E. Z.div_mod_to_equations. lia.
Qed.

(* ---- the shadow map of a 1-byte load ---- *)

(* The shadow byte that the check of a 1-byte load at p reads, and the fact the check needs from it: it is 0,
   or larger than the offset of p in its 8-byte granule. *)
Lemma shadow1 : forall m p, addr_byte m p ->
  exists k : byte, mrd rsegs m (wa (p / 8 + 2147450880)) = Some k
                   /\ (bv_signed k = 0 \/ p mod 8 < bv_signed k).
Proof.
  intros m p (AP & k & MK & OK). unfold shadow_addr, ASAN_K in MK. exists k.
  split; [exact MK|]. unfold shadow_ok in OK. lia.
Qed.

(* A shadow byte of application memory is not a byte of a 32-byte frame of application memory, so the frame
   stores keep every shadow byte the checks read. *)
Lemma addr_byte_tp : forall (m m' : word -> option byte) lo hi a,
  munch [(lo, hi)] m m' -> app_mem lo -> app_mem (hi - 1) -> lo < hi -> hi <= lo + 32 ->
  addr_byte m a -> addr_byte m' a.
Proof.
  intros m m' lo hi a MU AL AH LH HL AB.
  pose proof AB as (AP & k & MK & OK). unfold shadow_addr, ASAN_K in MK.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AL, AH, AP.
  split; [exact (proj1 AB)|]. exists k. split; [|exact OK].
  unfold shadow_addr, ASAN_K.
  apply (mrd_tp m m' lo hi (a / 8 + 2147450880) k MU); [Z.div_mod_to_equations; lia | | exact MK].
  Z.div_mod_to_equations; lia.
Qed.

Lemma addressable_tp : forall (m m' : word -> option byte) lo hi p n,
  munch [(lo, hi)] m m' -> app_mem lo -> app_mem (hi - 1) -> lo < hi -> hi <= lo + 32 ->
  addressable m p n -> addressable m' p n.
Proof.
  intros m m' lo hi p n MU AL AH LH HL (P0 & N0 & PE & AB).
  split; [exact P0|]. split; [exact N0|]. split; [exact PE|].
  intros i Hi. apply (addr_byte_tp m m' lo hi); try assumption. apply AB. exact Hi.
Qed.

Theorem check_refusal_submit_holds_F : check_refusal_submit_contract_F.
Proof.
  unfold check_refusal_submit_contract_F, CHECK_REFUSAL_SUBMIT, CHECK_REFUSAL_SUBMIT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw Bw' cp c rc before.
  intros A0 A1 A2 RCr BFr CPp CP4 HC LC HW HM ST HLO HOFF CELLS APS1 APS2 DGC DCK DCP AW RFR RGC RCK RSW RCB RQ.
  subst a0 a1 a2.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (bytes_at_bound rsegs m cp c HC) as CB0. rewrite LC in CB0.
  pose proof AW as (_ & _ & CPE & _). unfold APPMEM_END in CPE.
  destruct CELLS as (CK & GCK & _).
  rewrite check_refusal_submit_queued_at in RQ.
  unfold off_stk in HOFF, DGC, DCK, DCP.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APS1, APS2.
  unfold CELL_K, ASAN_K in CK.
  unfold GOT_CELL_K, CELL_K in GCK.
  unfold GOT_CELL_K in DGC, RGC.
  unfold CELL_K in DCK, RCK.
  unfold shadow_addr, ASAN_K in RSW.

  (* ---- the model: len = c[24] <= 32, Bw' = Bw, and the abort test as one boolean ---- *)
  pose proof (at8_range c 24%nat) as LR.
  unfold TC.check_refusal_submit_m in HM.
  rewrite LC in HM.
  change ((32 <? 25)%nat) with false in HM.
  change (Z.of_nat 32) with 32 in HM.
  cbn [orb] in HM.
  destruct (Z.ltb_spec 32 (DS.at8 c 24%nat)) as [LH|LH]; [discriminate HM|].
  cbv iota in HM.
  remember (DS.at8 c 24%nat) as len eqn:ELEN.
  remember (if 0 <=? DS.spec_system_at (TW.zs c) len
            then negb (rc =? DS.SPEC_E_REFUSED) || negb (TW.S_queued Bw =? before)
            else rc =? DS.SPEC_E_REFUSED) as COND eqn:ECOND.
  destruct COND; [discriminate HM|].
  cbv iota in HM.
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
    as HB.
  cbv beta iota in HB.
  subst Bw'. clear HM.
  symmetry in ECOND. unfold DS.SPEC_E_REFUSED in ECOND.

  (* ---- the world bytes of g_s.queued, as raw memory ---- *)
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 18144 4
                TMAP_B_ok HW TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as BQ.
  change (TB_g_s + 18144) with 6176032 in BQ.
  change (TW.OFF_g_s + 18144) with TW.A_S_queued in BQ.
  assert (LQ : length (TW.sub Bw TW.A_S_queued 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_S_queued, TW.OFF_g_s; lia|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.A_S_queued, TW.OFF_g_s, TW.W_LEN. lia. }

  (* keep the bytes_at facts off transport_chunks: they are carried past the three frame stores by hand *)
  pose proof (conj HC (conj BQ (conj CK GCK))) as HIDE. clear HC BQ CK GCK.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lazymatch goal with |- evtF _ _ ?Q _ => set (QQ := Q) end.
  carve_frame 32%nat ST.

  (* ---- 0x8640c-0x86418: the frame and the stores of ra, s0 and s1 ---- *)
  step. step. step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; try rename m1 into m0 end.
  destruct HIDE as (HC & BQ & CK & GCK).
  pose proof (bytes_tp m m0 _ _ cp c MU1 ltac:(rewrite LC; lia) HC) as HC0.
  pose proof (bytes_tp m m0 _ _ 6176032 (TW.sub Bw TW.A_S_queued 4) MU1 ltac:(rewrite LQ; lia) BQ) as BQ0.
  pose proof (bytes_tp m m0 _ _ 706168 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as CK0.
  pose proof (bytes_tp m m0 _ _ 670960 (le8 (wa 706168)) MU1 ltac:(rewrite length_le8; lia) GCK) as GCK0.
  clear HC BQ CK GCK.
  pose proof (addressable_tp m m0 _ _ cp 32 MU1 APS1 APS2 ltac:(lia) ltac:(lia) AW) as AW0.
  clear AW.
  (* the reads the walk needs from those bytes *)
  assert (RDG : ov_read_bytes rsegs m0 (wa 670960) 8 = Some (le8 (wa 706168))).
  { replace (wa 670960) with (wa (670960 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 670960 _ 0 8 GCK0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 706168) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 706168) with (wa (706168 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 706168 _ 0 8 CK0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDQ : ov_read_bytes rsegs m0 (wa 6176032) 4 = Some (TW.sub Bw TW.A_S_queued 4)).
  { replace (wa 6176032) with (wa (6176032 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6176032 _ 0 4 BQ0 ltac:(lia)) by (rewrite LQ; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite LQ. lia. }
  clear CK0 GCK0 BQ0.

  (* ---- the epilogue 0x86514-0x86524, reached by both returning paths ---- *)
  assert (EPI : forall (x1 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    evtF rsegs RNG QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9
               x10 (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
               x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86514) fc None m0 (seg_rom rsegs))).
  { intros x1 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31.
    (* ld ra,24(sp); ld s0,16(sp); ld s1,8(sp): the values stored at entry *)
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    (* addi sp,sp,32; ret *)
    step. step.
    apply evtF_done. unfold QQ. do 14 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM|]. split; [exact ST|]. split; [reflexivity|].
    exact (@TMAP_B_kept rsegs m m0 _ _ Bw HW MU1 ltac:(unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia)). }

  (* ---- 0x8650c-0x86510: no system command; rc <> -10, so the trap path is not taken ---- *)
  assert (NOSYS : DS.spec_system_at (TW.zs c) len = -1 ->
    forall (x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9
               x10 (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
               x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8650c) fc None m0 (seg_rom rsegs))).
  { intros SA x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31.
    rewrite SA in ECOND. change (0 <=? -1) with false in ECOND. cbv iota in ECOND.
    (* li a0,-10 ; beq a1,a0 *)
    step. step.
    rewrite (eqb_ss rc (-10) ltac:(lia) ltac:(lia)), ECOND. cbv iota.
    apply EPI. }

  (* ---- the shadow byte of cp + 24 ---- *)
  pose proof AW0 as (AWp & AWn & AWe & AB).
  destruct (shadow1 m0 (cp + 24) (AB 24 ltac:(lia))) as (k24 & MK24 & SK24).
  pose proof (RSW 24 ltac:(lia)) as RS24.
  pose proof (Z.mod_pos_bound (cp + 24) 8 ltac:(lia)) as MB24.

  (* ---- 0x86444 onwards: len, the loop, the two abort tests ---- *)
  assert (K1 : forall x16 : word,
    evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1
               (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
               (Z_to_bv 64 (cp + 24)) (sxb k24) (Z_to_bv 64 2147450880) x16 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x86444) fc None m0 (seg_rom rsegs))).
  { intros x16.
    (* 0x86444 lbu t1,0(a3): t1 = len *)
    pose proof (rdc m0 cp c 24%nat (cp + 24) HC0 ltac:(rewrite LC; lia) ltac:(reflexivity)) as RD24.
    step. clear RD24.
    rewrite (zxb_at8 c 24%nat), <- ELEN.
    (* 0x86448 li a3,4 ; 0x8644c bltu t1,a3 *)
    step. step.
    rewrite (ltu_zz len 4 ltac:(lia) ltac:(lia)).
    destruct (Z.ltb_spec len 4) as [L4|L4]; cbv iota.
    - (* len < 4: the C loop never runs *)
      apply NOSYS. unfold DS.spec_system_at. apply sal_end. lia.
    - (* len >= 4: the loop, i = 0 .. len - 4 *)
      assert (LOOP : forall (n : nat) (i : Z) (x8 x9 x13 x14 x31 : word),
        Z.of_nat n = len - 3 - i -> 0 <= i -> i + 3 < len ->
        DS.system_at_loop (TW.zs c) len i (Z.to_nat len) = DS.spec_system_at (TW.zs c) len ->
        evtF rsegs RNG QQ
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                   (Z_to_bv 64 (cp + 3)) (Z_to_bv 64 (len + -3)) (Z_to_bv 64 (cp + 1)) x8 x9
                   (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                   x13 x14 (Z_to_bv 64 2147450880) (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - cp))
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                   (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) x31)
              F (Z_to_bv 64 0x86470) fc None m0 (seg_rom rsegs))).
      { induction n as [|n IH]; intros i x8 x9 x13 x14 x31 Hn Hi Hlt INV; [lia|].
        pose proof (at8_range c (Z.to_nat i)) as Ri.
        pose proof (at8_range c (Z.to_nat (i + 1))) as Ri1.
        pose proof (at8_range c (Z.to_nat (i + 3))) as Ri3.
        (* the miss way: on to i + 1, or out of the loop with no system command *)
        assert (NEXT : forall (y8 y9 y13 y14 y31 : word), hit3 (TW.zs c) i = false ->
          evtF rsegs RNG QQ
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                     (Z_to_bv 64 (cp + 3)) (Z_to_bv 64 (len + -3)) (Z_to_bv 64 (cp + 1)) y8 y9
                     (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                     y13 y14 (Z_to_bv 64 2147450880) (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - cp))
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) y31)
                F (Z_to_bv 64 0x864d8) fc None m0 (seg_rom rsegs))).
        { intros y8 y9 y13 y14 y31 MISS.
          (* 0x864d8 addi a6,a6,1 ; 0x864dc bne t1,a6 *)
          step. step.
          rewrite (eqb_ss (len + -3) (i + 1) ltac:(lia) ltac:(lia)).
          destruct (Z.eqb_spec (len + -3) (i + 1)) as [Z0|Z0]; cbn [negb].
          - (* i was len - 4: the loop is done (0x864e0 j 0x8650c), there is no system command *)
            step.
            apply NOSYS.
            rewrite <- INV. rewrite (sal_miss (TW.zs c) len i (Z.to_nat len) ltac:(lia) ltac:(lia) Hlt MISS).
            apply sal_end. lia.
          - apply (IH (i + 1)); try lia.
            rewrite <- INV. symmetry.
            apply (sal_miss (TW.zs c) len i (Z.to_nat len)); [lia | lia | lia | exact MISS]. }
        (* 0x86470 bltu a7,a6: i <= 2^64 - 1 - cp, the branch to the unimp word is not taken *)
        step.
        rewrite (ltu_zz (18446744073709551615 - cp) i ltac:(lia) ltac:(lia)),
                (proj2 (Z.ltb_ge (18446744073709551615 - cp) i) ltac:(lia)). cbv iota.
        (* 0x86474 add a3,a0,a6: a3 = cp + i *)
        step.
        (* the shadow byte of cp + i *)
        destruct (shadow1 m0 (cp + i) (AB i ltac:(lia))) as (ki & MKi & SKi).
        pose proof (RSW i ltac:(lia)) as RSi.
        pose proof (Z.mod_pos_bound (cp + i) 8 ltac:(lia)) as MBi.
        assert (K2 : forall y31 : word,
          evtF rsegs RNG QQ
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                     (Z_to_bv 64 (cp + 3)) (Z_to_bv 64 (len + -3)) (Z_to_bv 64 (cp + 1)) x8 x9
                     (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                     (Z_to_bv 64 (cp + i)) (sxb ki) (Z_to_bv 64 2147450880) (Z_to_bv 64 i)
                     (Z_to_bv 64 (18446744073709551615 - cp))
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) y31)
                F (Z_to_bv 64 0x86488) fc None m0 (seg_rom rsegs))).
        { intros y31.
          (* 0x86488 add t6,t2,a6: t6 = cp + 1 + i *)
          step.
          (* 0x8648c lbu a4,-1(t6): a4 = c[i] *)
          pose proof (rdc m0 cp c (Z.to_nat i) (cp + 1 + i + -1) HC0 ltac:(rewrite LC; lia)
                        ltac:(rewrite Z2Nat.id by lia; lia)) as RDi.
          step. clear RDi.
          rewrite (zxb_at8 c (Z.to_nat i)).
          (* 0x86490 bne a4,t3 *)
          step.
          rewrite (eqb_ss (DS.at8 c (Z.to_nat i)) 240 ltac:(lia) ltac:(lia)).
          destruct (Z.eqb_spec (DS.at8 c (Z.to_nat i)) 240) as [B0|B0]; cbn [negb].
          2: { apply NEXT. rewrite hit3_at, (proj2 (Z.eqb_neq _ _) B0). reflexivity. }
          (* 0x86494 bgeu a6,a7: i < 2^64 - 1 - cp, the branch to the unimp word is not taken *)
          step.
          rewrite (ltu_zz i (18446744073709551615 - cp) ltac:(lia) ltac:(lia)),
                  (proj2 (Z.ltb_lt i (18446744073709551615 - cp)) ltac:(lia)). cbn [negb].
          (* 0x86498 addi a4,a3,1: a4 = cp + i + 1, and its shadow check *)
          step.
          pose proof (AB (i + 1) ltac:(lia)) as ABi1.
          pose proof (RSW (i + 1) ltac:(lia)) as RSi1.
          replace (cp + (i + 1)) with (cp + i + 1) in ABi1, RSi1 by lia.
          destruct (shadow1 m0 (cp + i + 1) ABi1) as (ki1 & MKi1 & SKi1).
          pose proof (Z.mod_pos_bound (cp + i + 1) 8 ltac:(lia)) as MBi1.
          assert (K3 : forall y9 : word,
            evtF rsegs RNG QQ
              (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                       (Z_to_bv 64 (cp + 3)) (Z_to_bv 64 (len + -3)) (Z_to_bv 64 (cp + 1)) (sxb ki1) y9
                       (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                       (Z_to_bv 64 (cp + i)) (Z_to_bv 64 (cp + i + 1)) (Z_to_bv 64 2147450880) (Z_to_bv 64 i)
                       (Z_to_bv 64 (18446744073709551615 - cp))
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) (Z_to_bv 64 (cp + 1 + i)))
                  F (Z_to_bv 64 0x864ac) fc None m0 (seg_rom rsegs))).
          { intros y9.
            (* 0x864ac lbu a4,0(t6): a4 = c[i + 1] *)
            pose proof (rdc m0 cp c (Z.to_nat (i + 1)) (cp + 1 + i) HC0 ltac:(rewrite LC; lia)
                          ltac:(rewrite Z2Nat.id by lia; lia)) as RDi1.
            step. clear RDi1.
            rewrite (zxb_at8 c (Z.to_nat (i + 1))).
            (* 0x864b0 bne a4,t4 *)
            step.
            rewrite (eqb_ss (DS.at8 c (Z.to_nat (i + 1))) 19 ltac:(lia) ltac:(lia)).
            destruct (Z.eqb_spec (DS.at8 c (Z.to_nat (i + 1))) 19) as [B1|B1]; cbn [negb].
            2: { apply NEXT. rewrite hit3_at, (proj2 (Z.eqb_eq _ _) B0), (proj2 (Z.eqb_neq _ _) B1).
                 reflexivity. }
            (* 0x864b4 addi a4,a6,3 ; 0x864b8 bltu a7,a4: i + 3 <= 2^64 - 1 - cp, not taken *)
            step. step.
            rewrite (ltu_zz (18446744073709551615 - cp) (i + 3) ltac:(lia) ltac:(lia)),
                    (proj2 (Z.ltb_ge (18446744073709551615 - cp) (i + 3)) ltac:(lia)). cbv iota.
            (* 0x864bc add a4,t0,a6: a4 = cp + 3 + i, and its shadow check *)
            step.
            pose proof (AB (i + 3) ltac:(lia)) as ABi3.
            pose proof (RSW (i + 3) ltac:(lia)) as RSi3.
            replace (cp + (i + 3)) with (cp + 3 + i) in ABi3, RSi3 by lia.
            destruct (shadow1 m0 (cp + 3 + i) ABi3) as (ki3 & MKi3 & SKi3).
            pose proof (Z.mod_pos_bound (cp + 3 + i) 8 ltac:(lia)) as MBi3.
            assert (K4 : forall y14 : word,
              evtF rsegs RNG QQ
                (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                         (Z_to_bv 64 (cp + 3)) (Z_to_bv 64 (len + -3)) (Z_to_bv 64 (cp + 1)) (sxb ki3) y9
                         (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                         (Z_to_bv 64 (cp + i)) y14 (Z_to_bv 64 2147450880) (Z_to_bv 64 i)
                         (Z_to_bv 64 (18446744073709551615 - cp))
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                         (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) (Z_to_bv 64 (cp + 1 + i)))
                    F (Z_to_bv 64 0x864d0) fc None m0 (seg_rom rsegs))).
            { intros y14.
              (* 0x864d0 lbu a3,2(t6): a3 = c[i + 3] *)
              pose proof (rdc m0 cp c (Z.to_nat (i + 3)) (cp + 1 + i + 2) HC0 ltac:(rewrite LC; lia)
                            ltac:(rewrite Z2Nat.id by lia; lia)) as RDi3.
              step. clear RDi3.
              rewrite (zxb_at8 c (Z.to_nat (i + 3))).
              (* 0x864d4 beq a3,t5 *)
              step.
              rewrite (eqb_ss (DS.at8 c (Z.to_nat (i + 3))) 112 ltac:(lia) ltac:(lia)).
              destruct (Z.eqb_spec (DS.at8 c (Z.to_nat (i + 3))) 112) as [B3|B3]; cbv iota.
              2: { apply NEXT. rewrite hit3_at, (proj2 (Z.eqb_eq _ _) B0), (proj2 (Z.eqb_eq _ _) B1),
                     (proj2 (Z.eqb_neq _ _) B3). reflexivity. }
              (* a hit at i: the model says rc = -10 and g_s.queued = before *)
              assert (SA : DS.spec_system_at (TW.zs c) len = i).
              { rewrite <- INV. apply sal_hit; [lia | lia|].
                rewrite hit3_at, (proj2 (Z.eqb_eq _ _) B0), (proj2 (Z.eqb_eq _ _) B1),
                  (proj2 (Z.eqb_eq _ _) B3). reflexivity. }
              rewrite SA, (proj2 (Z.leb_le 0 i) ltac:(lia)) in ECOND. cbv iota in ECOND.
              apply orb_false_iff in ECOND as [E1 E2].
              apply negb_false_iff in E1. apply negb_false_iff in E2. apply Z.eqb_eq in E2.
              (* 0x86528 li a0,-10 ; 0x8652c bne a1,a0 *)
              step. step.
              rewrite (eqb_ss rc (-10) ltac:(lia) ltac:(lia)), E1. cbn [negb].
              (* 0x86530-0x86534: a0 = g_s.queued *)
              step. step.
              rewrite lw_world.
              assert (SQ : TW.s32_at Bw TW.A_S_queued = bv_swrap 32 before).
              { unfold TW.s32_at. rewrite <- E2. reflexivity. }
              rewrite SQ.
              (* 0x86538 beq a0,a2 *)
              step. rewrite bv_eqb_refl. cbv iota.
              apply EPI. }
            (* 0x864c0-0x864cc: the shadow check of cp + 3 + i *)
            step. gen_shr (Z_to_bv 64 (cp + 3 + i)) g3 G3.
            rewrite (unsigned_lit (cp + 3 + i) ltac:(lia)) in G3.
            step. gen_addi g3 h3 H3.
            pose proof (rng_sub' RNG _ _ (bv_unsigned h3) 1 RSi3 ltac:(lia)) as RH3.
            pose proof (rdw0 m0 h3 _ _ MKi3 ltac:(lia)) as R3.
            step. clear R3.
            step. rewrite sxb_eq0.
            destruct SKi3 as [C3|C3].
            + rewrite (proj2 (Z.eqb_eq _ _) C3). cbn [negb]. apply K4.
            + rewrite (proj2 (Z.eqb_neq (bv_signed ki3) 0) ltac:(lia)). cbn [negb].
              (* 0x864fc andi a4,a4,7 ; 0x86500 blt a4,s0 *)
              step. rewrite land7, (unsigned_lit (cp + 3 + i) ltac:(lia)).
              step. rewrite (lts_low ((cp + 3 + i) mod 8) ki3 ltac:(lia)),
                            (proj2 (Z.ltb_lt _ _) C3). cbv iota.
              apply K4. }
          (* 0x8649c-0x864a8: the shadow check of cp + i + 1 *)
          step. gen_shr (Z_to_bv 64 (cp + i + 1)) g1 G1.
          rewrite (unsigned_lit (cp + i + 1) ltac:(lia)) in G1.
          step. gen_addi g1 h1 H1.
          pose proof (rng_sub' RNG _ _ (bv_unsigned h1) 1 RSi1 ltac:(lia)) as RH1.
          pose proof (rdw0 m0 h1 _ _ MKi1 ltac:(lia)) as R1.
          step. clear R1.
          step. rewrite sxb_eq0.
          destruct SKi1 as [C1|C1].
          + rewrite (proj2 (Z.eqb_eq _ _) C1). cbn [negb]. apply K3.
          + rewrite (proj2 (Z.eqb_neq (bv_signed ki1) 0) ltac:(lia)). cbn [negb].
            (* 0x864f0 andi s1,a4,7 ; 0x864f4 blt s1,s0 *)
            step. rewrite land7, (unsigned_lit (cp + i + 1) ltac:(lia)).
            step. rewrite (lts_low ((cp + i + 1) mod 8) ki1 ltac:(lia)),
                          (proj2 (Z.ltb_lt _ _) C1). cbv iota.
            apply K3. }
        (* 0x86478-0x86484: the shadow check of cp + i *)
        step. gen_shr (Z_to_bv 64 (cp + i)) gi Gi.
        rewrite (unsigned_lit (cp + i) ltac:(lia)) in Gi.
        step. gen_addi gi hi Hi'.
        pose proof (rng_sub' RNG _ _ (bv_unsigned hi) 1 RSi ltac:(lia)) as RHi.
        pose proof (rdw0 m0 hi _ _ MKi ltac:(lia)) as Ri'.
        step. clear Ri'.
        step. rewrite sxb_eq0.
        destruct SKi as [Ci|Ci].
        + rewrite (proj2 (Z.eqb_eq _ _) Ci). cbn [negb]. apply K2.
        + rewrite (proj2 (Z.eqb_neq (bv_signed ki) 0) ltac:(lia)). cbn [negb].
          (* 0x864e4 andi t6,a3,7 ; 0x864e8 blt t6,a4 *)
          step. rewrite land7, (unsigned_lit (cp + i) ltac:(lia)).
          step. rewrite (lts_low ((cp + i) mod 8) ki ltac:(lia)), (proj2 (Z.ltb_lt _ _) Ci). cbv iota.
          apply K2. }
      (* 0x86450-0x8646c: the loop's set-up; a7 = the bitwise not of cp *)
      do 8 step.
      rewrite (unsigned_lit cp ltac:(lia)), (zb_lxor_ones cp ltac:(lia)).
      apply (LOOP (Z.to_nat (len - 3)) 0); try lia.
      reflexivity. }

  (* ---- 0x8641c-0x86420: a3 = cp & 3 = cp mod 4 = 0, so bnez does not go to the unimp word ---- *)
  step. step.
  rewrite (unsigned_lit cp ltac:(lia)), land3, CP4, bv_eqb_refl. cbn [negb].
  (* ---- 0x86424-0x86430: the runtime cells (a5 = 0x7fff8000), a3 = cp + 24 ---- *)
  step. step. step. step.
  (* ---- 0x86434-0x86440: the shadow check of cp + 24 ---- *)
  step. gen_shr (Z_to_bv 64 (cp + 24)) g24 G24.
  rewrite (unsigned_lit (cp + 24) ltac:(lia)) in G24.
  step. gen_addi g24 h24 H24.
  pose proof (rng_sub' RNG _ _ (bv_unsigned h24) 1 RS24 ltac:(lia)) as RH24.
  pose proof (rdw0 m0 h24 _ _ MK24 ltac:(lia)) as R24.
  step. clear R24.
  step. rewrite sxb_eq0.
  destruct SK24 as [C24|C24].
  - rewrite (proj2 (Z.eqb_eq _ _) C24). cbn [negb]. apply K1.
  - rewrite (proj2 (Z.eqb_neq (bv_signed k24) 0) ltac:(lia)). cbn [negb].
    (* 0x86548 andi a6,a3,7 ; 0x8654c blt a6,a4 *)
    step. rewrite land7, (unsigned_lit (cp + 24) ltac:(lia)).
    step. rewrite (lts_low ((cp + 24) mod 8) k24 ltac:(lia)), (proj2 (Z.ltb_lt _ _) C24). cbv iota.
    apply K1.
Qed.

Print Assumptions check_refusal_submit_holds_F.
