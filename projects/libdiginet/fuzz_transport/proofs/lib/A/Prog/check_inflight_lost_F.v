From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  check_inflight_lost_c check_inflight_lost_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_inflight_lost_contract_F (image A, entry 0x852e4, frame 16 bytes, 42 words), step for step with
   StepF's step: each access side goal is closed from the rng fact of the accessed range.

   The walk (listing DgnTransportList.v, slots 4128-4169), with the model steps of the plain walk
   lib/Prog/T/check_inflight_lost.v:
     0x852e4-0x852e8  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x852ec-0x852f0  auipc a1; addi a3: a3 = 0x5df160, the base of M.
     0x852f4          lw a1,96(a3): M.fly.on (0x5df1c0). 0x852f8 beqz a1: not taken (M.fly.on <> 0).
     0x852fc-0x85304  auipc a1; ld a1 (GOT_CELL_K 0xa4090); ld a2,0(a1) (CELL_K 0xac9f8): a2 = 0x7fff8000.
     0x85308-0x85318  a1 = p + 64; the shadow check of the 4-byte load at p + 64 (srli, add, lb, bnez), with the
                      handler 0x85368-0x85370 (andi 7, addi 3, blt) going back to 0x8531c.
     0x8531c          lw a1,0(a1): n->counter. 0x85320 lw a4,104(a3): M.fly.counter. 0x85324 bne: not taken.
     0x85328          lw a1,108(a3): M.fly.retries. 0x8532c-0x85330 auipc a3; lw a3: g_cfg.max_retries
                      (0x5df0a0). 0x85334 bne: not taken.
     0x85338-0x85348  a0 = p + 68; the shadow check of the 2-byte load at p + 68, with the handler
                      0x8537c-0x85384 (andi 7, addi 1, blt) going back to 0x8534c.
     0x8534c          lhu a0,0(a0): n->retry. 0x85350 bne a1,a0: not taken.
     0x85354-0x8535c  ld ra,8(sp); addi sp,sp,16; ret.

   Why no error path is reached:
   - __asan_report_load4 (0x85378) and __asan_report_load2 (0x85388): `addressable` gives each check's shadow byte
     k = 0, or k above (x mod 8) + (w - 1) for the w-byte load at x (shadow_of_load): the bnez falls through, or the
     handler's blt is taken back to the load.
   - __asan_handle_no_return / abort (0x85360 / 0x85364), the target of the four model tests at 0x852f8, 0x85324,
     0x85334 and 0x85350: check_inflight_lost_m Bw n = Some (Bw', tt) gives M.fly.on <> 0,
     n_counter n = M.fly.counter, M.fly.retries = g_cfg.max_retries and n_retry n = g_cfg.max_retries (cil_model);
     by the world relation the four world loads are TWorld's s32_at of Bw (lw_world), the loaded counter is
     s32 of n_counter n (lw_put) and the loaded retry is n_retry n (lhu_put, with 0 <= n_retry n < 2^16), so every
     test compares equal words.

   The one store is the ra store at sp - 8 (0x852e8): it is in the frame, so the two fields, the two cells, the four
   world words and the two shadow bytes keep their values (off_stk; app_mem of the frame ends, and shadow memory is
   not application memory), and the frame lies outside the hull of the harness globals, so the world relation holds
   after the run with the same Bw (TMAP_A_kept). *)

(* ============================================================================
   The model premise, as the facts the four tests compare
   ============================================================================ *)

Lemma cil_model : forall B n B',
  TC.check_inflight_lost_m B n = Some (B', tt) ->
  TW.M_fly_on B <> 0 /\ TI.n_counter n = TW.M_fly_counter B /\ TW.M_fly_retries B = TW.Cfg_max_retries B /\
  TI.n_retry n = TW.Cfg_max_retries B /\ B' = B.
Proof.
  intros B n B' HM. unfold TC.check_inflight_lost_m, TC.truth in HM.
  destruct (TW.M_fly_on B =? 0) eqn:E1; cbv beta iota delta [negb orb] in HM; [discriminate HM|].
  destruct (TI.n_counter n =? TW.M_fly_counter B) eqn:E2; cbv beta iota delta [negb orb] in HM; [|discriminate HM].
  destruct (TW.M_fly_retries B =? TW.Cfg_max_retries B) eqn:E3; cbv beta iota delta [negb orb] in HM;
    [|discriminate HM].
  destruct (TI.n_retry n =? TW.Cfg_max_retries B) eqn:E4; cbv beta iota delta [negb orb] in HM; [|discriminate HM].
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) HM)
    as HB.
  cbv beta iota in HB.
  apply Z.eqb_neq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. apply Z.eqb_eq in E4.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. symmetry. exact HB.
Qed.

(* ============================================================================
   Register values and branch conditions
   ============================================================================ *)

(* a non-negative 32-bit value below 2^31 is its own signed reading *)
Lemma swrap32_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* lw of the field bytes put 4 v: the signed 32-bit reading of v *)
Lemma lw_put : forall v, 0 <= v < 2^32 ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word (TW.put 4 v))) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
  intros v Hv. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, TWorldLemmas.bytes_le_to_Z_put.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2^32)) by lia.
  f_equal. apply bv_wrap_small. unfold bv_modulus. change (Z.of_N 64) with 64. lia.
Qed.

(* lhu of the field bytes put 2 v, 0 <= v < 2^16: v *)
Lemma lhu_put : forall v, 0 <= v < 2^16 ->
  zext 64 (bv_extract 0 16 (le_bytes_to_word (TW.put 2 v))) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, TWorldLemmas.bytes_le_to_Z_put.
  change (8 * Z.of_nat 2) with 16. rewrite (Z.mod_small v (2^16)) by lia.
  rewrite bv_wrap_small by (unfold bv_modulus; change (Z.of_N 64) with 64; lia).
  change (Z.of_N 16) with 16. apply Z.mod_small. exact Hv.
Qed.

(* beqz on a non-zero sign-extended 32-bit value: not taken *)
Lemma eqb0_s32 : forall v, -2^31 <= v < 2^31 -> v <> 0 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv N. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* `blt` of (x & 7) + (w - 1) with the shadow byte *)
Lemma lts_lit : forall (x : Z) (k : byte), -2^63 <= x < 2^63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

(* a test the walk does not take: its condition is false *)
Local Ltac br_false tac :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac]
  end.

(* ============================================================================
   Memory facts across the ra store
   ============================================================================ *)

(* The ASan check of a w-byte load at A + o reads the shadow byte of A + o and compares it with
   (A + o) mod 8 + (w - 1). The byte at A + o + min (w - 1) (7 - (A + o) mod 8) lies in the load and in the granule
   of A + o, so its shadow byte is the one the check reads: either 0, or above (A + o) mod 8 + (w - 1). *)
Lemma shadow_of_load : forall (m : word -> option byte) (A n o w : Z),
  addressable m A n -> 0 <= o -> 0 < w -> o + w <= n ->
  exists k : byte,
    mrd rsegs m (wa ((A + o) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ ((A + o) mod 8 + (w - 1) < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m A n o w (HA & HN & HE & AB) Ho Hw Hon.
  pose proof (Z.mod_pos_bound (A + o) 8 ltac:(lia)) as MB.
  destruct (Z_le_dec ((A + o) mod 8 + (w - 1)) 7) as [LE|GT].
  - destruct (AB (o + (w - 1)) ltac:(lia)) as (APP & k & MK & SK).
    exists k. unfold shadow_addr in MK. unfold shadow_ok in SK.
    assert (D : (A + (o + (w - 1))) / 8 = (A + o) / 8) by (Z.div_mod_to_equations; lia).
    assert (E : (A + (o + (w - 1))) mod 8 = (A + o) mod 8 + (w - 1)) by (Z.div_mod_to_equations; lia).
    rewrite D in MK. rewrite E in SK. split; [exact MK | exact SK].
  - destruct (AB (o + (7 - (A + o) mod 8)) ltac:(lia)) as (APP & k & MK & SK).
    exists k. unfold shadow_addr in MK. unfold shadow_ok in SK.
    assert (D : (A + (o + (7 - (A + o) mod 8))) / 8 = (A + o) / 8) by (Z.div_mod_to_equations; lia).
    assert (E : (A + (o + (7 - (A + o) mod 8))) mod 8 = 7) by (Z.div_mod_to_equations; lia).
    rewrite D in MK. rewrite E in SK. split; [exact MK|].
    left. destruct SK as [K0|K]; [exact K0 | lia].
Qed.

(* bytes off the written range [lo, hi) read the same after the run, as the load step reads them *)
Lemma rd_tp : forall (m m' : word -> option byte) lo hi a bs (n : nat),
  munch [(lo, hi)] m m' -> length bs = n -> a + Z.of_nat n <= lo \/ hi <= a ->
  bytes_at rsegs m a bs -> ov_read_bytes rsegs m' (wa a) n = Some bs.
Proof.
  intros m m' lo hi a bs n MU L D H.
  pose proof (bytes_tp m m' lo hi a bs MU ltac:(rewrite L; exact D) H) as H'.
  replace (wa a) with (wa (a + 0)) by (rewrite Z.add_0_r; reflexivity).
  rewrite (bytes_at_read rsegs m' a bs 0 n H' ltac:(lia)) by (rewrite L; change (Z.to_nat 0) with 0%nat; lia).
  change (Z.to_nat 0) with 0%nat. cbn [skipn]. f_equal. apply firstn_all2. lia.
Qed.

(* ============================================================================
   The two shadow checks (the registers the code never writes are section variables)
   ============================================================================ *)

Section Walk.
Variables (RNG : ExecF.footprint) (Q : machine_state -> Prop)
  (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte).

Local Notation ST pc x0 x1 x2 x3 x4 x5 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 x2 x3 x4 x5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* 0x8530c-0x85318 (and the handler 0x85368-0x85370): the shadow check of the 4-byte load at a1 = P *)
Lemma sc4F : forall (x0 x3 x4 x5 : word) (k : byte) (P : Z),
  0 <= P < 2^64 ->
  mrd rsegs mm (wa (P / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ (P mod 8 + 3 < bv_signed k /\ bv_signed k <= 7)) ->
  ExecF.rng RNG (P / 8 + 2147450880) 1 ->
  (forall x4' x5' : word,
     ExecF.evtF rsegs RNG Q (ST 0x8531c x0 (Z_to_bv 64 P) (Z_to_bv 64 2147450880) x3 x4' x5')) ->
  ExecF.evtF rsegs RNG Q (ST 0x8530c x0 (Z_to_bv 64 P) (Z_to_bv 64 2147450880) x3 x4 x5).
Proof.
  intros x0 x3 x4 x5 k P HP M SK RK CONT.
  pose proof (Z.mod_pos_bound P 8 ltac:(lia)) as MB.
  step. gen_shr (Z_to_bv 64 P) g G. rewrite (unsigned_lit P ltac:(lia)) in G.
  step. gen_addi g h H.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RK ltac:(lia)) as RH.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step.
    rewrite land7, (unsigned_lit P ltac:(lia)), (lts_lit (P mod 8 + 3) k ltac:(lia)),
            (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* 0x8533c-0x85348 (and the handler 0x8537c-0x85384): the shadow check of the 2-byte load at a0 = P *)
Lemma sc2F : forall (x1 x3 x4 x5 : word) (k : byte) (P : Z),
  0 <= P < 2^64 ->
  mrd rsegs mm (wa (P / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ (P mod 8 + 1 < bv_signed k /\ bv_signed k <= 7)) ->
  ExecF.rng RNG (P / 8 + 2147450880) 1 ->
  (forall x2' x3' : word,
     ExecF.evtF rsegs RNG Q (ST 0x8534c (Z_to_bv 64 P) x1 x2' x3' x4 x5)) ->
  ExecF.evtF rsegs RNG Q (ST 0x8533c (Z_to_bv 64 P) x1 (Z_to_bv 64 2147450880) x3 x4 x5).
Proof.
  intros x1 x3 x4 x5 k P HP M SK RK CONT.
  pose proof (Z.mod_pos_bound P 8 ltac:(lia)) as MB.
  step. gen_shr (Z_to_bv 64 P) g G. rewrite (unsigned_lit P ltac:(lia)) in G.
  step. gen_addi g h H.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RK ltac:(lia)) as RH.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|[C Cu]].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step.
    rewrite land7, (unsigned_lit P ltac:(lia)), (lts_lit (P mod 8 + 1) k ltac:(lia)),
            (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

End Walk.

(* ============================================================================
   The function
   ============================================================================ *)

Theorem check_inflight_lost_holds_F : check_inflight_lost_contract_F.
Proof.
  unfold check_inflight_lost_contract_F, CHECK_INFLIGHT_LOST, CHECK_INFLIGHT_LOST_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p lo n Bw Bw' HP0 HP8 HRT BC BR HW HM ST HLO HOFF CELLS APS1 APS2 DG DC D64 AD64 D68 AD68
    RFR RFO RGOT RCELL RS64 R64 RFC RFT RMX RS68 R68.
  (* the model: the four tests' facts, and Bw' = Bw *)
  destruct (cil_model Bw n Bw' HM) as (ON & CTR & RET & RTY & ->). clear HM.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_fly_on) as RON.
  assert (RCN : 0 <= TI.n_counter n < 2^32).
  { rewrite CTR. unfold TW.M_fly_counter.
    pose proof (TWorldLemmas.u_at_range Bw TW.A_M_fly_counter 4) as R.
    change (2 ^ (8 * Z.of_nat 4)) with (2^32) in R. exact R. }
  assert (E64 : bv_swrap 32 (TI.n_counter n) = TW.s32_at Bw TW.A_M_fly_counter)
    by (unfold TW.s32_at; rewrite CTR; reflexivity).
  assert (E108 : TW.s32_at Bw TW.A_M_fly_retries = TW.s32_at Bw TW.A_Cfg_max_retries).
  { unfold TW.s32_at. change (TW.u_at Bw TW.A_M_fly_retries 4) with (TW.M_fly_retries Bw).
    rewrite RET. reflexivity. }
  assert (E68 : TW.s32_at Bw TW.A_M_fly_retries = TI.n_retry n).
  { unfold TW.s32_at. change (TW.u_at Bw TW.A_M_fly_retries 4) with (TW.M_fly_retries Bw).
    rewrite RET, <- RTY. apply swrap32_small. lia. }
  clear CTR RET RTY.
  (* the ranges of the stack, the fields and the cells *)
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  unfold off_stk in DG, DC, D64, D68. unfold GOT_CELL_K, CELL_K in DG, DC, RGOT, RCELL.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG in APS1, APS2.
  pose proof AD64 as (_ & _ & HE64 & _). pose proof AD68 as (_ & _ & HE68 & _).
  unfold APPMEM_END in HE64, HE68.
  rewrite check_inflight_lost_fly_on_at in RFO.
  rewrite check_inflight_lost_fly_counter_at in RFC.
  rewrite check_inflight_lost_fly_retries_at in RFT.
  rewrite check_inflight_lost_max_retries_at in RMX.
  (* the two shadow bytes the checks read *)
  destruct (shadow_of_load m (p + 64) 4 0 4 AD64 ltac:(lia) ltac:(lia) ltac:(lia)) as (k64 & M64 & S64).
  destruct (shadow_of_load m (p + 68) 2 0 2 AD68 ltac:(lia) ltac:(lia) ltac:(lia)) as (k68 & M68 & S68).
  rewrite Z.add_0_r in M64, S64, M68, S68.
  unfold ASAN_K in M64, M68.
  unfold shadow_addr, ASAN_K in RS64, RS68.
  (* the four world words, as raw memory *)
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 96 4 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BON.
  change (TA_M + 96) with 6156736 in BON. change (TW.OFF_M + 96) with TW.A_M_fly_on in BON.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 104 4 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BFC.
  change (TA_M + 104) with 6156744 in BFC. change (TW.OFF_M + 104) with TW.A_M_fly_counter in BFC.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 108 4 TMAP_A_ok HW TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BFT.
  change (TA_M + 108) with 6156748 in BFT. change (TW.OFF_M + 108) with TW.A_M_fly_retries in BFT.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 32 4 TMAP_A_ok HW TMAP_A_g_cfg
    ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) as BMX.
  change (TA_g_cfg + 32) with 6156448 in BMX. change (TW.OFF_g_cfg + 32) with TW.A_Cfg_max_retries in BMX.
  assert (LW : forall k, 0 <= k -> k + 4 <= TW.W_LEN -> length (TW.sub Bw k 4) = 4%nat).
  { intros k Hk Hk4. apply TWorldLemmas.length_sub; [exact Hk|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.W_LEN in Hk4 |- *. lia. }
  (* keep the world's bytes and the fields off transport_chunks: they are transported by hand past the ra store *)
  pose proof (conj (conj BON BFC) (conj (conj BFT BMX) (conj BC BR))) as HIDE.
  clear BON BFC BFT BMX BC BR.
  (* the frame *)
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x852e4 addi sp,sp,-16; 0x852e8 sd ra,8(sp) *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* the loaded bytes after the store of ra *)
  destruct HIDE as [[BON BFC] [[BFT BMX] [BC BR]]].
  pose proof (rd_tp m m0 _ _ 6156736 (TW.sub Bw TW.A_M_fly_on 4) 4 MU1
    (LW TW.A_M_fly_on ltac:(unfold TW.A_M_fly_on, TW.OFF_M; lia) ltac:(unfold TW.A_M_fly_on, TW.OFF_M, TW.W_LEN; lia))
    ltac:(lia) BON) as RDON.
  pose proof (rd_tp m m0 _ _ 6156744 (TW.sub Bw TW.A_M_fly_counter 4) 4 MU1
    (LW TW.A_M_fly_counter ltac:(unfold TW.A_M_fly_counter, TW.OFF_M; lia) ltac:(unfold TW.A_M_fly_counter, TW.OFF_M, TW.W_LEN; lia))
    ltac:(lia) BFC) as RDFC.
  pose proof (rd_tp m m0 _ _ 6156748 (TW.sub Bw TW.A_M_fly_retries 4) 4 MU1
    (LW TW.A_M_fly_retries ltac:(unfold TW.A_M_fly_retries, TW.OFF_M; lia) ltac:(unfold TW.A_M_fly_retries, TW.OFF_M, TW.W_LEN; lia))
    ltac:(lia) BFT) as RDFT.
  pose proof (rd_tp m m0 _ _ 6156448 (TW.sub Bw TW.A_Cfg_max_retries 4) 4 MU1
    (LW TW.A_Cfg_max_retries ltac:(unfold TW.A_Cfg_max_retries, TW.OFF_g_cfg; lia)
          ltac:(unfold TW.A_Cfg_max_retries, TW.OFF_g_cfg, TW.W_LEN; lia))
    ltac:(lia) BMX) as RDMX.
  pose proof (rd_tp m m0 _ _ (p + 64) (TW.put 4 (TI.n_counter n)) 4 MU1 (TWorldLemmas.length_put 4 _) ltac:(lia) BC) as RD64.
  pose proof (rd_tp m m0 _ _ (p + 68) (TW.put 2 (TI.n_retry n)) 2 MU1 (TWorldLemmas.length_put 2 _) ltac:(lia) BR) as RD68.
  clear BON BFC BFT BMX BC BR LW.
  pose proof CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_tp m m0 _ _ 0xa4090 (le8 (wa 0xac9f8)) 8 MU1 (length_le8 _) ltac:(lia) GCK) as RDG.
  pose proof (rd_tp m m0 _ _ 0xac9f8 (le8 (wa 0x7fff8000)) 8 MU1 (length_le8 _) ltac:(lia) CK) as RDC.
  clear CK GCK.
  assert (N64 : mrd rsegs m0 (wa ((p + 64) / 8 + 2147450880)) = Some k64)
    by (eapply mrd_tp; [exact MU1 | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact M64]).
  assert (N68 : mrd rsegs m0 (wa ((p + 68) / 8 + 2147450880)) = Some k68)
    by (eapply mrd_tp; [exact MU1 | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact M68]).
  clear M64 M68.
  (* 0x852ec auipc a1; 0x852f0 addi a3,a1: a3 = &M *)
  step. step.
  (* 0x852f4 lw a1,96(a3): M.fly.on *)
  step. rewrite lw_world. clear RDON.
  (* 0x852f8 beqz a1: M.fly.on <> 0 *)
  step. br_false ltac:(exact (eqb0_s32 _ RON ON)).
  (* 0x852fc auipc a1; 0x85300 ld a1 (GOT_CELL_K); 0x85304 ld a2,0(a1) (CELL_K): a2 = 0x7fff8000 *)
  step. step. step.
  (* 0x85308 addi a1,a0,64 *)
  step. try rewrite (unsigned_lit p) by lia.
  (* 0x8530c-0x85318: the shadow check of the 4-byte load at p + 64 *)
  eapply sc4F with (k := k64) (P := p + 64); [lia | exact N64 | exact S64 | exact RS64 |]. intros x4a x5a.
  (* 0x8531c lw a1,0(a1): n->counter *)
  step. rewrite (lw_put (TI.n_counter n) RCN). clear RD64.
  (* 0x85320 lw a4,104(a3): M.fly.counter *)
  step. rewrite lw_world. clear RDFC.
  (* 0x85324 bne a1,a4 *)
  step. br_false ltac:(rewrite E64, bv_eqb_refl; reflexivity).
  (* 0x85328 lw a1,108(a3): M.fly.retries *)
  step. rewrite lw_world. clear RDFT.
  (* 0x8532c auipc a3; 0x85330 lw a3: g_cfg.max_retries *)
  step. step. rewrite lw_world. clear RDMX.
  (* 0x85334 bne a1,a3 *)
  step. br_false ltac:(rewrite E108, bv_eqb_refl; reflexivity).
  (* 0x85338 addi a0,a0,68 *)
  step. try rewrite (unsigned_lit p) by lia.
  (* 0x8533c-0x85348: the shadow check of the 2-byte load at p + 68 *)
  eapply sc2F with (k := k68) (P := p + 68); [lia | exact N68 | exact S68 | exact RS68 |]. intros x2b x3b.
  (* 0x8534c lhu a0,0(a0): n->retry *)
  step. rewrite (lhu_put (TI.n_retry n) HRT). clear RD68.
  (* 0x85350 bne a1,a0 *)
  step. br_false ltac:(rewrite E68, bv_eqb_refl; reflexivity).
  (* 0x85354 ld ra,8(sp); 0x85358 addi sp,sp,16; 0x8535c ret *)
  step. step. step.
  apply evtF_done. do 7 eexists. split; [reflexivity|].
  split; [exact MU1|].
  split; [match goal with W' : wmono _ m m0 |- _ => exact W' end|].
  split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  split; [reflexivity|].
  apply (@TMAP_A_kept rsegs m m0 _ _ Bw HW MU1). unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
Qed.

Print Assumptions check_inflight_lost_holds_F.
