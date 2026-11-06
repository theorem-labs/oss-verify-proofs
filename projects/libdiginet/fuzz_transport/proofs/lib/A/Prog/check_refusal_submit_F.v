From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_refusal_submit_c check_refusal_submit_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module DS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* Proof of check_refusal_submit_contract_F (image A, entry 0x86110, frame 16 bytes), with StepF's step: each
   access side goal is closed from an rng fact for the accessed range.

   The walk (listing DgnTransportList.v, the 72 slots of TS_check_refusal_submit):
     0x86110-0x86114  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x86118-0x86120  the 8-byte loads of GOT_CELL_K and CELL_K (asan_cells): a4 = 0x7fff8000.
     0x86124-0x86134  a3 = cp + 24 and the check of the byte load there (a5 = its signed shadow byte k; k <> 0
                      goes to 0x86214, where a6 = (cp + 24) & 7 and a6 < k comes back to 0x86138).
     0x86138-0x86140  a6 = len = c[24]; len < 4 (unsigned) goes to 0x861e4, no system command.
     0x86144-0x86154  a5 = cp + 1; a6 = len - 3; a7 = 0xf0; t0 = 0x13; t1 = 0x70.
     0x86158-0x861b8  the loop for i = 0 .. len - 4, with a0 = cp + i, a5 = cp + i + 1, a6 = len - 3 - i: the
                      three byte loads c[i], c[i + 1], c[i + 3], each preceded by its shadow check (0x861bc,
                      0x861c8, 0x861d4 are the k <> 0 ways, which come back to the load); a hit (F0 13 xx 70)
                      goes to 0x861f8, the last miss to 0x861e4.
     0x861e4-0x861e8  (no system command) a0 = -10; rc = -10 would go to the trap path 0x8620c.
     0x861ec-0x861f4  ld ra,8(sp); addi sp,sp,16; ret: the one return, reached by both returning paths.
     0x861f8-0x86208  (a system command) a0 = -10; rc <> -10 goes to the trap path; a0 = g_s.queued, the 4-byte
                      load at CHECK_REFUSAL_SUBMIT_QUEUED; a0 <> a2 goes to the trap path, a0 = a2 to 0x861ec.
   Why the other paths never run:
     - the four calls of __asan_report_load1 (0x861e0, 0x86220, 0x86224, 0x8622c): each is reached only when the
       signed shadow byte k of a loaded byte a is not 0 and a mod 8 >= k. Every loaded byte lies in [cp, cp + 32),
       and addressable m cp 32 gives, for each, k = 0 or a mod 8 < k (shadow1 below), so each check passes;
     - the trap path (0x8620c): with no system command it needs rc = -10, with a system command rc <> -10 or a
       g_s.queued other than a2. check_refusal_submit_m Bw c rc before = Some _ rules out each case.
   The loop is spec_system_at (zs c) len (DgnSpec.v:255-268), walked by induction on the remaining iteration
   count with the invariant system_at_loop (zs c) len i (Z.to_nat len) = spec_system_at (zs c) len.
   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) of the 18 payload ranges (off_stk premise), so TMAP_A_kept gives tw_at of the
   same Bw at the new memory. *)

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

(* A shadow byte of application memory is not a byte of a 16-byte frame of application memory, so the frame
   store keeps every shadow byte the checks read. *)
Lemma addr_byte_tp : forall (m m' : word -> option byte) lo hi a,
  munch [(lo, hi)] m m' -> app_mem lo -> app_mem (hi - 1) -> lo < hi -> hi <= lo + 16 ->
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
  munch [(lo, hi)] m m' -> app_mem lo -> app_mem (hi - 1) -> lo < hi -> hi <= lo + 16 ->
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
  destruct CELLS as (CK & GCK & _).
  rewrite check_refusal_submit_queued_at in RQ.
  unfold off_stk in HOFF, DGC, DCK, DCP.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
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
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 18144 4
                TMAP_A_ok HW TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as BQ.
  change (TA_g_s + 18144) with 6176928 in BQ.
  change (TW.OFF_g_s + 18144) with TW.A_S_queued in BQ.
  assert (LQ : length (TW.sub Bw TW.A_S_queued 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.A_S_queued, TW.OFF_g_s; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.A_S_queued, TW.OFF_g_s, TW.W_LEN. lia. }

  (* keep the bytes_at facts off transport_chunks: they are carried past the ra store by hand *)
  pose proof (conj HC (conj BQ (conj CK GCK))) as HIDE. clear HC BQ CK GCK.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lazymatch goal with |- evtF _ _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.

  (* ---- 0x86110-0x86114: the frame and the store of ra ---- *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct HIDE as (HC & BQ & CK & GCK).
  pose proof (bytes_tp m m0 _ _ cp c MU1 ltac:(rewrite LC; lia) HC) as HC0.
  pose proof (bytes_tp m m0 _ _ 6176928 (TW.sub Bw TW.A_S_queued 4) MU1 ltac:(rewrite LQ; lia) BQ) as BQ0.
  pose proof (bytes_tp m m0 _ _ 707064 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as CK0.
  pose proof (bytes_tp m m0 _ _ 671888 (le8 (wa 707064)) MU1 ltac:(rewrite length_le8; lia) GCK) as GCK0.
  clear HC BQ CK GCK.
  pose proof (addressable_tp m m0 _ _ cp 32 MU1 APS1 APS2 ltac:(lia) ltac:(lia) AW) as AW0.
  clear AW.
  (* the reads the walk needs from those bytes *)
  assert (RDG : ov_read_bytes rsegs m0 (wa 671888) 8 = Some (le8 (wa 707064))).
  { replace (wa 671888) with (wa (671888 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 671888 _ 0 8 GCK0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 707064) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 707064) with (wa (707064 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 707064 _ 0 8 CK0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDQ : ov_read_bytes rsegs m0 (wa 6176928) 4 = Some (TW.sub Bw TW.A_S_queued 4)).
  { replace (wa 6176928) with (wa (6176928 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 6176928 _ 0 4 BQ0 ltac:(lia)) by (rewrite LQ; lia).
    cbn [Z.to_nat skipn]. apply f_equal. apply firstn_all2. rewrite LQ. lia. }
  clear CK0 GCK0 BQ0.

  (* ---- the epilogue 0x861ec-0x861f4, reached by both returning paths ---- *)
  assert (EPI : forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 : word),
    evtF rsegs RNG QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
               x10 (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
               x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x861ec) fc None m0 (seg_rom rsegs))).
  { intros x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x28.
    step.
    release_frame FR ST (bv_unsigned sp).
    step. step.
    apply evtF_done. unfold QQ. do 11 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM|]. split; [exact ST|]. split; [reflexivity|].
    exact (TMAP_A_kept m m0 _ _ Bw HW MU1 ltac:(unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia)). }

  (* ---- 0x861e4-0x861e8: no system command; rc <> -10, so the trap path is not taken ---- *)
  assert (NOSYS : DS.spec_system_at (TW.zs c) len = -1 ->
    forall (x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 : word),
    evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
               x10 (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
               x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x861e4) fc None m0 (seg_rom rsegs))).
  { intros SA x5 x6 x7 x10 x13 x14 x15 x16 x17 x28.
    rewrite SA in ECOND. change (0 <=? -1) with false in ECOND. cbv iota in ECOND.
    step. step.
    rewrite (eqb_ss rc (-10) ltac:(lia) ltac:(lia)), ECOND. cbv iota.
    apply EPI. }

  (* ---- the shadow byte of cp + 24 ---- *)
  pose proof AW0 as (AWp & AWn & AWe & AB).
  destruct (shadow1 m0 (cp + 24) (AB 24 ltac:(lia))) as (k24 & MK24 & SK24).
  pose proof (RSW 24 ltac:(lia)) as RS24.
  pose proof (Z.mod_pos_bound (cp + 24) 8 ltac:(lia)) as MB24.

  (* ---- 0x86138 onwards: len, the loop, the two abort tests ---- *)
  assert (K1 : forall x16 : word,
    evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
               (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
               (Z_to_bv 64 (cp + 24)) (Z_to_bv 64 2147450880) (sxb k24) x16 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x86138) fc None m0 (seg_rom rsegs))).
  { intros x16.
    (* 0x86138 lbu a6,0(a3): a6 = len *)
    pose proof (rdc m0 cp c 24%nat (cp + 24) HC0 ltac:(rewrite LC; lia) ltac:(reflexivity)) as RD24.
    step. clear RD24.
    rewrite (zxb_at8 c 24%nat), <- ELEN.
    (* 0x8613c li a3,4 ; 0x86140 bltu a6,a3 *)
    step. step.
    rewrite (ltu_zz len 4 ltac:(lia) ltac:(lia)).
    destruct (Z.ltb_spec len 4) as [L4|L4]; cbv iota.
    - (* len < 4: the C loop never runs *)
      apply NOSYS. unfold DS.spec_system_at. apply sal_end. lia.
    - (* len >= 4: the loop, i = 0 .. len - 4 *)
      assert (LOOP : forall (n : nat) (i : Z) (x7 x13 x28 : word),
        Z.of_nat n = len - 3 - i -> 0 <= i -> i + 3 < len ->
        DS.system_at_loop (TW.zs c) len i (Z.to_nat len) = DS.spec_system_at (TW.zs c) len ->
        evtF rsegs RNG QQ
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 19) (Z_to_bv 64 112) x7 s0 s1
                   (Z_to_bv 64 (cp + i)) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                   x13 (Z_to_bv 64 2147450880) (Z_to_bv 64 (cp + i + 1)) (Z_to_bv 64 (len - 3 - i))
                   (Z_to_bv 64 240) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
              F (Z_to_bv 64 0x86158) fc None m0 (seg_rom rsegs))).
      { induction n as [|n IH]; intros i x7 x13 x28 Hn Hi Hlt INV; [lia|].
        pose proof (at8_range c (Z.to_nat i)) as Ri.
        pose proof (at8_range c (Z.to_nat (i + 1))) as Ri1.
        pose proof (at8_range c (Z.to_nat (i + 3))) as Ri3.
        (* the miss way: on to i + 1, or out of the loop with no system command *)
        assert (NEXT : forall (y7 y13 y28 : word), hit3 (TW.zs c) i = false ->
          evtF rsegs RNG QQ
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 19) (Z_to_bv 64 112) y7 s0 s1
                     (Z_to_bv 64 (cp + i)) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                     y13 (Z_to_bv 64 2147450880) (Z_to_bv 64 (cp + i + 1)) (Z_to_bv 64 (len - 3 - i))
                     (Z_to_bv 64 240) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
                F (Z_to_bv 64 0x861a8) fc None m0 (seg_rom rsegs))).
        { intros y7 y13 y28 MISS.
          (* 0x861a8 addi a0,a0,1 ; 0x861ac addi a6,a6,-1 ; 0x861b0 addi a5,a5,1 ; 0x861b4 bnez a6 *)
          step. step. step. step.
          rewrite (eqb_ss (len - 3 - i + -1) 0 ltac:(lia) ltac:(lia)).
          destruct (Z.eqb_spec (len - 3 - i + -1) 0) as [Z0|Z0]; cbn [negb].
          - (* i was len - 4: the loop is done, there is no system command *)
            step.
            apply NOSYS.
            rewrite <- INV. rewrite (sal_miss (TW.zs c) len i (Z.to_nat len) ltac:(lia) ltac:(lia) Hlt MISS).
            apply sal_end. lia.
          - replace (cp + i + 2) with (cp + (i + 1) + 1) by lia.
            replace (cp + i + 1) with (cp + (i + 1)) by lia.
            replace (len - 3 - i + -1) with (len - 3 - (i + 1)) by lia.
            apply (IH (i + 1)); try lia.
            rewrite <- INV. symmetry.
            apply (sal_miss (TW.zs c) len i (Z.to_nat len)); [lia | lia | lia | exact MISS]. }
        (* the shadow byte of cp + i *)
        destruct (shadow1 m0 (cp + i) (AB i ltac:(lia))) as (ki & MKi & SKi).
        pose proof (RSW i ltac:(lia)) as RSi.
        pose proof (Z.mod_pos_bound (cp + i) 8 ltac:(lia)) as MBi.
        assert (K2 : forall y7 : word,
          evtF rsegs RNG QQ
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 19) (Z_to_bv 64 112) y7 s0 s1
                     (Z_to_bv 64 (cp + i)) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                     (sxb ki) (Z_to_bv 64 2147450880) (Z_to_bv 64 (cp + i + 1)) (Z_to_bv 64 (len - 3 - i))
                     (Z_to_bv 64 240) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
                F (Z_to_bv 64 0x86168) fc None m0 (seg_rom rsegs))).
        { intros y7.
          (* 0x86168 lbu a3,-1(a5): a3 = c[i] *)
          pose proof (rdc m0 cp c (Z.to_nat i) (cp + i) HC0 ltac:(rewrite LC; lia)
                        ltac:(rewrite Z2Nat.id by lia; reflexivity)) as RDi.
          step. clear RDi.
          rewrite (zxb_at8 c (Z.to_nat i)).
          (* 0x8616c bne a3,a7 *)
          step.
          rewrite (eqb_ss (DS.at8 c (Z.to_nat i)) 240 ltac:(lia) ltac:(lia)).
          destruct (Z.eqb_spec (DS.at8 c (Z.to_nat i)) 240) as [B0|B0]; cbn [negb].
          2: { apply NEXT. rewrite hit3_at, (proj2 (Z.eqb_neq _ _) B0). reflexivity. }
          (* 0x86170 addi a3,a0,1: a3 = cp + i + 1, and its shadow check *)
          step.
          pose proof (AB (i + 1) ltac:(lia)) as ABi1.
          pose proof (RSW (i + 1) ltac:(lia)) as RSi1.
          replace (cp + (i + 1)) with (cp + i + 1) in ABi1, RSi1 by lia.
          destruct (shadow1 m0 (cp + i + 1) ABi1) as (ki1 & MKi1 & SKi1).
          pose proof (Z.mod_pos_bound (cp + i + 1) 8 ltac:(lia)) as MBi1.
          assert (K3 : forall y28 : word,
            evtF rsegs RNG QQ
              (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 19) (Z_to_bv 64 112)
                       (sxb ki1) s0 s1
                       (Z_to_bv 64 (cp + i)) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                       (Z_to_bv 64 (cp + i + 1)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (cp + i + 1))
                       (Z_to_bv 64 (len - 3 - i)) (Z_to_bv 64 240)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
                  F (Z_to_bv 64 0x86184) fc None m0 (seg_rom rsegs))).
          { intros y28.
            (* 0x86184 lbu a3,0(a5): a3 = c[i + 1] *)
            pose proof (rdc m0 cp c (Z.to_nat (i + 1)) (cp + i + 1) HC0 ltac:(rewrite LC; lia)
                          ltac:(rewrite Z2Nat.id by lia; lia)) as RDi1.
            step. clear RDi1.
            rewrite (zxb_at8 c (Z.to_nat (i + 1))).
            (* 0x86188 bne a3,t0 *)
            step.
            rewrite (eqb_ss (DS.at8 c (Z.to_nat (i + 1))) 19 ltac:(lia) ltac:(lia)).
            destruct (Z.eqb_spec (DS.at8 c (Z.to_nat (i + 1))) 19) as [B1|B1]; cbn [negb].
            2: { apply NEXT. rewrite hit3_at, (proj2 (Z.eqb_eq _ _) B0), (proj2 (Z.eqb_neq _ _) B1).
                 reflexivity. }
            (* 0x8618c addi a3,a0,3: a3 = cp + i + 3, and its shadow check *)
            step.
            pose proof (AB (i + 3) ltac:(lia)) as ABi3.
            pose proof (RSW (i + 3) ltac:(lia)) as RSi3.
            replace (cp + (i + 3)) with (cp + i + 3) in ABi3, RSi3 by lia.
            destruct (shadow1 m0 (cp + i + 3) ABi3) as (ki3 & MKi3 & SKi3).
            pose proof (Z.mod_pos_bound (cp + i + 3) 8 ltac:(lia)) as MBi3.
            assert (K4 : forall z28 : word,
              evtF rsegs RNG QQ
                (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 19) (Z_to_bv 64 112)
                         (sxb ki3) s0 s1
                         (Z_to_bv 64 (cp + i)) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                         (Z_to_bv 64 (cp + i + 3)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (cp + i + 1))
                         (Z_to_bv 64 (len - 3 - i)) (Z_to_bv 64 240)
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 t4 t5 t6)
                    F (Z_to_bv 64 0x861a0) fc None m0 (seg_rom rsegs))).
            { intros z28.
              (* 0x861a0 lbu a3,2(a5): a3 = c[i + 3] *)
              pose proof (rdc m0 cp c (Z.to_nat (i + 3)) (cp + i + 3) HC0 ltac:(rewrite LC; lia)
                            ltac:(rewrite Z2Nat.id by lia; lia)) as RDi3.
              step. clear RDi3.
              rewrite (zxb_at8 c (Z.to_nat (i + 3))).
              (* 0x861a4 beq a3,t1 *)
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
              (* 0x861f8 li a0,-10 ; 0x861fc bne a1,a0 *)
              step. step.
              rewrite (eqb_ss rc (-10) ltac:(lia) ltac:(lia)), E1. cbn [negb].
              (* 0x86200-0x86204: a0 = g_s.queued *)
              step. step.
              rewrite lw_world.
              assert (SQ : TW.s32_at Bw TW.A_S_queued = bv_swrap 32 before).
              { unfold TW.s32_at. rewrite <- E2. reflexivity. }
              rewrite SQ.
              (* 0x86208 beq a0,a2 *)
              step. rewrite bv_eqb_refl. cbv iota.
              apply EPI. }
            (* 0x86190-0x8619c: the shadow check of cp + i + 3 *)
            step. gen_shr (Z_to_bv 64 (cp + i + 3)) g3 G3.
            rewrite (unsigned_lit (cp + i + 3) ltac:(lia)) in G3.
            step. gen_addi g3 h3 H3.
            pose proof (rng_sub' RNG _ _ (bv_unsigned h3) 1 RSi3 ltac:(lia)) as RH3.
            pose proof (rdw0 m0 h3 _ _ MKi3 ltac:(lia)) as R3.
            step. clear R3.
            step. rewrite sxb_eq0.
            destruct SKi3 as [C3|C3].
            + rewrite (proj2 (Z.eqb_eq _ _) C3). cbn [negb]. apply K4.
            + rewrite (proj2 (Z.eqb_neq (bv_signed ki3) 0) ltac:(lia)). cbn [negb].
              (* 0x861d4 andi t3,a3,7 ; 0x861d8 blt t3,t2 *)
              step. rewrite land7, (unsigned_lit (cp + i + 3) ltac:(lia)).
              step. rewrite (lts_low ((cp + i + 3) mod 8) ki3 ltac:(lia)),
                            (proj2 (Z.ltb_lt _ _) C3). cbv iota.
              apply K4. }
          (* 0x86174-0x86180: the shadow check of cp + i + 1 *)
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
            (* 0x861c8 andi t3,a3,7 ; 0x861cc bge t3,t2 *)
            step. rewrite land7, (unsigned_lit (cp + i + 1) ltac:(lia)).
            step. rewrite (lts_low ((cp + i + 1) mod 8) ki1 ltac:(lia)),
                          (proj2 (Z.ltb_lt _ _) C1). cbn [negb].
            (* 0x861d0 j 0x86184 *)
            step.
            apply K3. }
        (* 0x86158-0x86164: the shadow check of cp + i *)
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
          (* 0x861bc andi t2,a0,7 ; 0x861c0 bge t2,a3 *)
          step. rewrite land7, (unsigned_lit (cp + i) ltac:(lia)).
          step. rewrite (lts_low ((cp + i) mod 8) ki ltac:(lia)), (proj2 (Z.ltb_lt _ _) Ci). cbn [negb].
          (* 0x861c4 j 0x86168 *)
          step.
          apply K2. }
      (* 0x86144-0x86154: the loop's set-up *)
      do 5 step.
      replace (Z_to_bv 64 cp) with (Z_to_bv 64 (cp + 0)) by (f_equal; lia).
      replace (cp + 1) with (cp + 0 + 1) by lia.
      replace (len + -3) with (len - 3 - 0) by lia.
      apply (LOOP (Z.to_nat (len - 3)) 0); try lia.
      reflexivity. }

  (* ---- 0x86118-0x86134: the runtime cells, a3 = cp + 24 and its shadow check ---- *)
  step. step. step. step.
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
    (* 0x86214 andi a6,a3,7 ; 0x86218 blt a6,a5 *)
    step. rewrite land7, (unsigned_lit (cp + 24) ltac:(lia)).
    step. rewrite (lts_low ((cp + 24) mod 8) k24 ltac:(lia)), (proj2 (Z.ltb_lt _ _) C24). cbv iota.
    apply K1.
Qed.

Print Assumptions check_refusal_submit_holds_F.
