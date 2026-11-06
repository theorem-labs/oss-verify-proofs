From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_inflight_acked_c check_inflight_acked_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_inflight_acked_contract_F (image A, entry 0x85240, frame 16 bytes), with StepF's step: each data
   access is closed from the rng premise of exactly the range it touches.

   The walk (listing DgnTransportList.v, slots 4087-4127):
     0x85240-0x85244  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x85248-0x85254  auipc a1; auipc a2; lw a1 (GOT.acked at 0x5e53b8); addi a2: a2 = 0x5f3060, the base of OW.
     0x85258          lw a3,216(a2): OW.acked at 0x5f3138.
     0x8525c          blt a3,a1: to the trap path when OW.acked < GOT.acked.
     0x85260-0x85268  the 8-byte loads of GOT_CELL_K and CELL_K (asan_cells): a3 = 0x7fff8000.
     0x8526c-0x8527c  a1 = p + 64; the shadow byte k of p + 64 (lb at ((p + 64) >> 3) + 0x7fff8000); bnez k.
     0x852c0-0x852c8  k <> 0: a5 = ((p + 64) & 7) + 3 and blt a5,k back to the load.
     0x85280-0x85288  lw a1,0(a1): n->counter; lw a4,224(a2): OW.acked_counter at 0x5f3140; bne a1,a4: trap path.
     0x8528c-0x8529c  a0 = p + 68; the shadow byte k of p + 68; bnez k.
     0x852d4-0x852dc  k <> 0: a3 = ((p + 68) & 7) + 1 and blt a3,k back to the load.
     0x852a0-0x852a8  lhu a0,0(a0): n->retry; lw a1,228(a2): OW.acked_retry at 0x5f3144; bne a1,a0: trap path.
     0x852ac-0x852b4  ld ra,8(sp); addi sp,sp,16; ret.
   Why the other paths never run:
     - the trap path 0x852b8 / 0x852bc (__asan_handle_no_return, abort): the model premise
       check_inflight_acked_m Bw n = Some (Bw', tt) gives GOT_acked Bw <= OW_acked Bw, n_counter n =
       OW_acked_counter Bw and n_retry n = OW_acked_retry Bw (cia_model). cia_world turns the world relation into
       the four loaded words: the blt compares the GOT and OW words, which the model orders; the loaded counter,
       sign-extended, is the same word as the loaded OW.acked_counter, and the zero-extended 2-byte retry
       (n_retry n < 2^16) is the same word as the sign-extended OW.acked_retry. So no branch to the trap is taken.
     - the error paths 0x852d0 (__asan_report_load4) and 0x852e0 (__asan_report_load2): cia_shadow derives, from
       addressable m (p + 64) 4 / addressable m (p + 68) 2, that the shadow byte k is 0 or (a mod 8) + n - 1 < k,
       so the blt at 0x852c8 / 0x852dc is always taken.
   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) (off_stk premise), so tw_at holds of the same Bw (cia_kept).

   What the kernel pays at Qed, measured on this walk (MEM=24g; the walk itself costs 14 s and 0.8 GB):
     - every step leaves a change_no_check conversion for the kernel to redo at Qed, and the post rides unchanged
       through all of them. Written out, the post's tw_at conjunct makes the kernel unfold tw_at, whose first
       field is length Bw = Z.to_nat W_LEN (W_LEN = 0x10050): it builds Z.to_nat 65616 as a unary nat once per
       step. The walk is therefore run with the post held as the opaque variable Q.
     - the same happens for a world term left in a register or in a hypothesis of the walk: TW.sub Bw A 4 and
       TW.s32_at Bw A unfold to firstn / skipn of Z.to_nat A. Deriving those facts here and hiding the terms
       behind `remember` does NOT help, because the proof of each derived fact still mentions the world term and
       the kernel re-expands it. cia_world below proves all of them once, behind its own Qed, and hands the walk
       existential witnesses: opaque variables with no body, which no conversion can expand. *)

(* The model premise as the facts the three branches test. *)
Lemma cia_model : forall B n B', TC.check_inflight_acked_m B n = Some (B', tt) ->
  TW.GOT_acked B <= TW.OW_acked B /\ TI.n_counter n = TW.OW_acked_counter B /\
  TI.n_retry n = TW.OW_acked_retry B /\ B' = B.
Proof.
  intros B n B' HM. unfold TC.check_inflight_acked_m in HM.
  destruct (Z.ltb_spec (TW.OW_acked B) (TW.GOT_acked B)) as [E1|E1]; cbn [orb negb] in HM; [discriminate HM|].
  destruct (Z.eqb_spec (TI.n_counter n) (TW.OW_acked_counter B)) as [E2|E2]; cbn [orb negb] in HM;
    [|discriminate HM].
  destruct (Z.eqb_spec (TI.n_retry n) (TW.OW_acked_retry B)) as [E3|E3]; cbn [orb negb] in HM;
    [|discriminate HM].
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) HM)
    as HB.
  cbv beta iota in HB.
  split; [lia|]. split; [exact E2|]. split; [exact E3|]. symmetry. exact HB.
Qed.

Lemma cia_swrap32 : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31). Z.div_mod_to_equations. lia.
Qed.

(* The struct's two fields as the byte lists the loads read. *)
Lemma cia_put4 : forall c, 0 <= c < 2^32 -> TW.put 4 c = le4 (Z_to_bv 64 c).
Proof. intros c Hc. unfold TW.put, le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma cia_put2 : forall r, 0 <= r < 2^16 -> TW.put 2 r = le2 (Z_to_bv 64 r).
Proof. intros r Hr. unfold TW.put, le2. rewrite unsigned_lit by lia. reflexivity. Qed.

(* The world fields at the numerals the offsets compute (TWorld.v: OFF_GOT = 0xfe3c = 65084,
   OFF_OW = 0xff20 = 65312), and the image address of each, as equations over closed Z. The walk and cia_world
   move to these numerals by `rewrite`, never by `unfold <accessor> in <hypothesis>` and never by `change`:
   leaving the kernel a conversion between a world accessor and its definition costs 24 GB at Qed (measured;
   the plain walk lib/Prog/T/check_inflight_acked.v records the same at its lines 16-18). *)
Lemma cia_got : forall B, TW.s32_at B 65300 = TW.GOT_acked B.
Proof.
  intros B. unfold TW.GOT_acked, TW.A_GOT_acked, TW.OFF_GOT.
  replace (65084 + 216) with 65300 by reflexivity. reflexivity.
Qed.
Lemma cia_ow : forall B, TW.s32_at B 65528 = TW.OW_acked B.
Proof.
  intros B. unfold TW.OW_acked, TW.A_OW_acked, TW.OFF_OW.
  replace (65312 + 216) with 65528 by reflexivity. reflexivity.
Qed.
Lemma cia_owc : forall B, TW.u_at B 65536 4 = TW.OW_acked_counter B.
Proof.
  intros B. unfold TW.OW_acked_counter, TW.A_OW_acked_counter, TW.OFF_OW.
  replace (65312 + 224) with 65536 by reflexivity. reflexivity.
Qed.
Lemma cia_owr : forall B, TW.u_at B 65540 4 = TW.OW_acked_retry B.
Proof.
  intros B. unfold TW.OW_acked_retry, TW.A_OW_acked_retry, TW.OFF_OW.
  replace (65312 + 228) with 65540 by reflexivity. reflexivity.
Qed.

(* the same move for the offsets tw_bytes_at leaves, and for the image addresses the loads compute *)
Lemma cia_off_got : TW.OFF_GOT + 216 = 65300. Proof. reflexivity. Qed.
Lemma cia_off_owa : TW.OFF_OW + 216 = 65528. Proof. reflexivity. Qed.
Lemma cia_off_owc : TW.OFF_OW + 224 = 65536. Proof. reflexivity. Qed.
Lemma cia_off_owr : TW.OFF_OW + 228 = 65540. Proof. reflexivity. Qed.
Lemma cia_got_addr : TA_GOT + 216 = 0x5e53b8. Proof. reflexivity. Qed.
Lemma cia_owa_addr : TA_OW + 216 = 0x5f3138. Proof. reflexivity. Qed.
Lemma cia_owc_addr : TA_OW + 224 = 0x5f3140. Proof. reflexivity. Qed.
Lemma cia_owr_addr : TA_OW + 228 = 0x5f3144. Proof. reflexivity. Qed.

(* The two register-level facts the compares need. Both are world-free. *)
Lemma cia_sx32 : forall c, 0 <= c < 2 ^ 32 -> sx32 (Z_to_bv 64 c) = Z_to_bv 64 (bv_swrap 32 c).
Proof. intros c Hc. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma cia_zx16 : forall r, 0 <= r < 2 ^ 16 -> zx16 (Z_to_bv 64 r) = Z_to_bv 64 r.
Proof.
  intros r Hr. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* Everything the walk needs of the world, proved here and handed over as witnesses: opaque variables that no
   conversion can expand, so the walk's own proof term holds no TW.sub / TW.s32_at at all. *)
Lemma cia_world : forall (m : word -> option byte) (Bw : list byte) (n : TI.ntc),
  tw_at TMAP_A (csw_view m) Bw ->
  TW.GOT_acked Bw <= TW.OW_acked Bw ->
  TI.n_counter n = TW.OW_acked_counter Bw ->
  TI.n_retry n = TW.OW_acked_retry Bw ->
  0 <= TI.n_retry n < 2 ^ 16 ->
  exists (bGA bOA bOC bOR : list byte) (vGA vOA vOC vOR : Z),
    bytes_at rsegs m 0x5e53b8 bGA /\ length bGA = 4%nat /\
    bytes_at rsegs m 0x5f3138 bOA /\ length bOA = 4%nat /\
    bytes_at rsegs m 0x5f3140 bOC /\ length bOC = 4%nat /\
    bytes_at rsegs m 0x5f3144 bOR /\ length bOR = 4%nat /\
    sext 64 (bv_extract 0 32 (le_bytes_to_word bGA)) = Z_to_bv 64 vGA /\
    sext 64 (bv_extract 0 32 (le_bytes_to_word bOA)) = Z_to_bv 64 vOA /\
    sext 64 (bv_extract 0 32 (le_bytes_to_word bOC)) = Z_to_bv 64 vOC /\
    sext 64 (bv_extract 0 32 (le_bytes_to_word bOR)) = Z_to_bv 64 vOR /\
    -2^31 <= vGA < 2^31 /\ -2^31 <= vOA < 2^31 /\ vGA <= vOA /\
    0 <= TI.n_counter n < 2 ^ 32 /\
    vOC = bv_swrap 32 (TI.n_counter n) /\
    vOR = TI.n_retry n.
Proof.
  intros m Bw n HW M1 CTR RTY HRT.
  (* to the numerals, by rewriting with the four equations above *)
  rewrite <- cia_got, <- cia_ow in M1.
  rewrite <- cia_owc in CTR. rewrite <- cia_owr in RTY.
  assert (LW : forall k, 0 <= k -> k + 4 <= TW.W_LEN -> length (TW.sub Bw k 4) = 4%nat).
  { intros k Hk Hk4. apply TWorldLemmas.length_sub; [exact Hk|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.W_LEN in *. lia. }
  assert (RC : 0 <= TI.n_counter n < 2 ^ 32).
  { rewrite CTR. pose proof (TWorldLemmas.u_at_range Bw 65536 4) as R.
    change (8 * Z.of_nat 4) with 32 in R. lia. }
  exists (TW.sub Bw 65300 4), (TW.sub Bw 65528 4), (TW.sub Bw 65536 4), (TW.sub Bw 65540 4).
  exists (TW.s32_at Bw 65300), (TW.s32_at Bw 65528), (TW.s32_at Bw 65536), (TW.s32_at Bw 65540).
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_GOT TA_GOT TW.SZ_GOT 216 4 TMAP_A_ok HW TMAP_A_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as BGA.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_OW TA_OW TW.SZ_OW 216 4 TMAP_A_ok HW TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BOA.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_OW TA_OW TW.SZ_OW 224 4 TMAP_A_ok HW TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BOC.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_OW TA_OW TW.SZ_OW 228 4 TMAP_A_ok HW TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BOR.
  rewrite cia_got_addr, cia_off_got in BGA.
  rewrite cia_owa_addr, cia_off_owa in BOA.
  rewrite cia_owc_addr, cia_off_owc in BOC.
  rewrite cia_owr_addr, cia_off_owr in BOR.
  split; [exact BGA|]. split; [apply LW; unfold TW.W_LEN; lia|].
  split; [exact BOA|]. split; [apply LW; unfold TW.W_LEN; lia|].
  split; [exact BOC|]. split; [apply LW; unfold TW.W_LEN; lia|].
  split; [exact BOR|]. split; [apply LW; unfold TW.W_LEN; lia|].
  split; [exact (lw_world Bw 65300)|].
  split; [exact (lw_world Bw 65528)|].
  split; [exact (lw_world Bw 65536)|].
  split; [exact (lw_world Bw 65540)|].
  split; [exact (TWorldLemmas.s32_range Bw 65300)|].
  split; [exact (TWorldLemmas.s32_range Bw 65528)|].
  split; [exact M1|].
  split; [exact RC|].
  split.
  - unfold TW.s32_at. rewrite CTR. reflexivity.
  - unfold TW.s32_at. rewrite RTY. apply cia_swrap32.
    pose proof (TWorldLemmas.u_at_range Bw 65540 4) as R.
    change (8 * Z.of_nat 4) with 32 in R. rewrite <- RTY. lia.
Qed.

(* All the bytes bs at a, read at once. *)
Lemma cia_rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* The same read at a register value w whose number is a. *)
Lemma cia_rdw : forall m (w : word) a bs n, bytes_at rsegs m a bs -> length bs = n -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w n = Some bs.
Proof.
  intros m w a bs n H L E. rewrite <- (Z_to_bv_bv_unsigned w), E.
  change (Z_to_bv 64 a) with (wa a). apply cia_rd_all; assumption.
Qed.

(* The shadow byte that the check of an n-byte load at a reads (1 <= n <= 8), and the fact the check needs from it:
   it is 0, or larger than the offset of the access's last byte in a's 8-byte granule. *)
Lemma cia_shadow : forall m a n, 1 <= n <= 8 -> addressable m a n ->
  app_mem a /\ exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\
                         (bv_signed k = 0 \/ a mod 8 + (n - 1) < bv_signed k).
Proof.
  intros m a n Hn (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP & k & MK & _). rewrite Z.add_0_r in APP, MK.
  split; [exact APP|]. exists k. unfold shadow_addr in MK. split; [exact MK|].
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB.
  (* the last byte of [a, a + n) in a's granule: a + n - 1, or the granule's byte 7 when the range crosses *)
  set (i := Z.min (n - 1) (7 - a mod 8)).
  assert (Hi : 0 <= i < n) by (unfold i; lia).
  destruct (AB i Hi) as (_ & ki & MKi & SKi).
  assert (E : (a + i) / 8 = a / 8).
  { unfold i. clear - MB Hn P0. Z.div_mod_to_equations. lia. }
  unfold shadow_addr in MKi. rewrite E, MK in MKi. injection MKi as Ek. subst ki.
  assert (Em : (a + i) mod 8 = a mod 8 + i).
  { unfold i. clear - MB Hn P0. Z.div_mod_to_equations. lia. }
  unfold shadow_ok in SKi. rewrite Em in SKi. unfold i in SKi. lia.
Qed.

(* A shadow byte of an application address lies outside a 16-byte frame of application memory. *)
Lemma cia_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 16 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

(* The signed compare of a small non-negative value with a sign-extended shadow byte. *)
Lemma cia_lts_small : forall (x : Z) (k : byte), 0 <= x < 2^63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

(* blt on two sign-extended 32-bit values is the signed comparison of the values. *)
Lemma cia_lts : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.

(* The kit's TMAP_A_kept at the leaf form's view. It is stated over the raw view lambda, so applying it to a
   csw_view goal makes the unifier unfold tw_at, and the length field then evaluates Z.to_nat W_LEN into a
   65616-deep unary nat. Unfolding csw_view first makes both sides syntactically equal. *)
Lemma cia_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_A (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_LO \/ TG.G_HARNESS_HI <= lo) ->
  tw_at TMAP_A (csw_view m') Bw.
Proof.
  intros m m' lo hi Bw H MU D. unfold csw_view in *.
  exact (TMAP_A_kept (segs:=rsegs) m m' lo hi Bw H MU D).
Qed.

Theorem check_inflight_acked_holds_F : check_inflight_acked_contract_F.
Proof.
  unfold check_inflight_acked_contract_F, CHECK_INFLIGHT_ACKED, CHECK_INFLIGHT_ACKED_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo n Bw Bw' HP0 HP8 HRT B64 B68 HW HM ST HLO HOFF CELLS APW1 APW2 DGOT DCELL D64 A64 D68 A68
    RFR RGA ROA RGOT RCELL RS64 RF64 ROC RS68 RF68 ROR.
  (* the model, then the world: cia_world's witnesses are opaque, so no TW.sub / TW.s32_at enters this proof *)
  destruct (cia_model Bw n Bw' HM) as (M1 & CTR & RTY & ->). clear HM.
  destruct (cia_world m Bw n HW M1 CTR RTY HRT)
    as (bGA & bOA & bOC & bOR & vGA & vOA & vOC & vOR &
        BGA & LGA & BOA & LOA & BOC & LOC & BOR & LOR &
        EGA & EOA & EOC & EOR & RvG & RvA & MLE & RC & HvOC & HvOR).
  clear M1 CTR RTY.
  rewrite (cia_put4 _ RC) in B64. rewrite (cia_put2 _ HRT) in B68.
  (* the rng premises at the addresses the loads compute *)
  rewrite check_inflight_acked_got_acked_at in RGA.
  rewrite check_inflight_acked_ow_acked_at in ROA.
  rewrite check_inflight_acked_ow_counter_at in ROC.
  rewrite check_inflight_acked_ow_retry_at in ROR.
  (* the shadow bytes of the two fields and what the checks need of them *)
  destruct (cia_shadow m (p + 64) 4 ltac:(lia) A64) as (APP64 & k64 & MK64 & SK64).
  destruct (cia_shadow m (p + 68) 2 ltac:(lia) A68) as (APP68 & k68 & MK68 & SK68).
  pose proof A64 as (_ & _ & E64 & _). pose proof A68 as (_ & _ & E68 & _). clear A64 A68.
  unfold off_stk in DGOT, DCELL, D64, D68.
  unfold GOT_CELL_K, CELL_K in DGOT, DCELL, RGOT, RCELL.
  unfold shadow_addr, ASAN_K in RS64, RS68.
  unfold APPMEM_END in E64, E68.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  (* the argument register: p as a word, read back by the code *)
  remember (Z_to_bv 64 p) as a0 eqn:E0.
  assert (U0 : bv_unsigned a0 = p) by (subst a0; apply unsigned_lit; lia).
  clear E0. subst p.
  (* keep the bytes off transport_chunks: they are transported by hand past the ra store *)
  destruct CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (conj B64 (conj B68 (conj CK (conj GCK (conj BGA (conj BOA (conj BOC BOR))))))) as KEEP.
  clear B64 B68 CK GCK BGA BOA BOC BOR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* The post rides unchanged through every step, and the kernel redoes each step's conversion at Qed. Written
     out, its tw_at conjunct makes the kernel unfold tw_at, whose length field evaluates Z.to_nat W_LEN into a
     65616-deep unary nat, once per step. Held as the variable Q it is inert. *)
  match goal with |- ExecF.evtF ?sg ?RN ?QQ ?st => remember QQ as Q eqn:EQQ end.
  carve_frame 16%nat ST.
  (* 0x85240-0x85244: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ =>
    rename MU' into MU1; first [constr_eq m1 m0 | rename m1 into m0] end.
  destruct KEEP as (B64 & B68 & CK & GCK & BGA & BOA & BOC & BOR).
  assert (B64' : bytes_at rsegs m0 (bv_unsigned a0 + 64) (le4 (Z_to_bv 64 (TI.n_counter n))))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le4; lia | exact B64]).
  assert (B68' : bytes_at rsegs m0 (bv_unsigned a0 + 68) (le2 (Z_to_bv 64 (TI.n_retry n))))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le2; lia | exact B68]).
  assert (GCK0 : bytes_at rsegs m0 0xa4090 (le8 (wa 0xac9f8)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact GCK]).
  assert (CK0 : bytes_at rsegs m0 0xac9f8 (le8 (wa 0x7fff8000)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact CK]).
  assert (BGA0 : bytes_at rsegs m0 0x5e53b8 bGA)
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LGA; lia | exact BGA]).
  assert (BOA0 : bytes_at rsegs m0 0x5f3138 bOA)
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LOA; lia | exact BOA]).
  assert (BOC0 : bytes_at rsegs m0 0x5f3140 bOC)
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LOC; lia | exact BOC]).
  assert (BOR0 : bytes_at rsegs m0 0x5f3144 bOR)
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LOR; lia | exact BOR]).
  clear B64 B68 CK GCK BGA BOA BOC BOR.
  pose proof (cia_shadow_tp m m0 _ _ _ k64 MU1 ltac:(lia) APW1 APW2 APP64 MK64) as M64.
  pose proof (cia_shadow_tp m m0 _ _ _ k68 MU1 ltac:(lia) APW1 APW2 APP68 MK68) as M68.
  unfold ASAN_K in M64, M68. clear MK64 MK68.
  (* 0x85248-0x85254: a1 = GOT.acked; a2 = the base of OW *)
  pose proof (cia_rd_all m0 _ _ 4 BGA0 LGA) as R. step. step. step. clear R. step.
  rewrite EGA.
  (* 0x85258: a3 = OW.acked *)
  pose proof (cia_rd_all m0 _ _ 4 BOA0 LOA) as R. step. clear R.
  rewrite EOA.
  (* 0x8525c: blt a3,a1 is not taken: GOT.acked <= OW.acked *)
  step. if_cases BR.
  { exfalso. rewrite (cia_lts vOA vGA RvA RvG) in BR. apply Z.ltb_lt in BR. lia. }
  (* 0x85260-0x85268: a3 = the shadow offset 0x7fff8000 *)
  pose proof (cia_rd_all m0 _ _ 8 GCK0 (length_le8 _)) as R. step. step. clear R.
  pose proof (cia_rd_all m0 _ _ 8 CK0 (length_le8 _)) as R. step. clear R.
  (* 0x8526c-0x8527c: the shadow byte of p + 64 *)
  step. gen_addi a0 w64 U64.
  pose proof (rng_sub' _ _ _ (bv_unsigned w64) 4 RF64 ltac:(lia)) as RW64.
  step. gen_shr w64 g64 G64. rewrite U64 in G64.
  step. gen_addi g64 h64 H64.
  pose proof (rng_sub' _ _ _ (bv_unsigned h64) 1 RS64 ltac:(lia)) as RH64.
  pose proof (rdw0 m0 h64 _ _ M64 ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 64) 8 ltac:(lia)) as MB64.
  destruct SK64 as [C|C];
    [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
    | assert (C' : (bv_unsigned a0 + 64) mod 8 + 3 < bv_signed k64) by lia;
      rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k64) 0) ltac:(lia)); cbn [negb];
      step; step; step;
      rewrite land7, U64, (cia_lts_small ((bv_unsigned a0 + 64) mod 8 + 3) k64 ltac:(lia)),
        (proj2 (Z.ltb_lt _ _) C'); cbn [negb] ].
  (* 0x85280-0x85288: a1 = n->counter, a4 = OW.acked_counter, the same word *)
  all: pose proof (cia_rdw m0 w64 _ _ 4 B64' (length_le4 _) U64) as R; step; clear R.
  all: rewrite (cia_sx32 _ RC).
  all: pose proof (cia_rd_all m0 _ _ 4 BOC0 LOC) as R; step; clear R.
  all: rewrite EOC, HvOC.
  all: step; if_cases BR2; [exfalso; rewrite bv_eqb_refl in BR2; cbn [negb] in BR2; discriminate BR2 |].
  (* 0x8528c-0x8529c: the shadow byte of p + 68 *)
  all: step; gen_addi a0 w68 U68.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w68) 2 RF68 ltac:(lia)) as RW68.
  all: step; gen_shr w68 g68 G68.
  all: rewrite U68 in G68.
  all: step; gen_addi g68 h68 H68.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h68) 1 RS68 ltac:(lia)) as RH68.
  all: pose proof (rdw0 m0 h68 _ _ M68 ltac:(lia)) as R; step; clear R.
  all: step.
  all: pose proof (Z.mod_pos_bound (bv_unsigned a0 + 68) 8 ltac:(lia)) as MB68.
  all: destruct SK68 as [C2|C2];
    [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C2); cbn [negb]
    | assert (C2' : (bv_unsigned a0 + 68) mod 8 + 1 < bv_signed k68) by lia;
      rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k68) 0) ltac:(lia)); cbn [negb];
      step; step; step;
      rewrite land7, U68, (cia_lts_small ((bv_unsigned a0 + 68) mod 8 + 1) k68 ltac:(lia)),
        (proj2 (Z.ltb_lt _ _) C2'); cbn [negb] ].
  (* 0x852a0-0x852a8: a0 = n->retry, a1 = OW.acked_retry, the same word *)
  all: pose proof (cia_rdw m0 w68 _ _ 2 B68' (length_le2 _) U68) as R; step; clear R.
  all: rewrite (cia_zx16 _ HRT).
  all: pose proof (cia_rd_all m0 _ _ 4 BOR0 LOR) as R; step; clear R.
  all: rewrite EOR, HvOR.
  all: step; if_cases BR3; [exfalso; rewrite bv_eqb_refl in BR3; cbn [negb] in BR3; discriminate BR3 |].
  (* 0x852ac-0x852b4: ld ra; addi sp; ret *)
  all: step; step; step.
  (* the walk is over: restore the post and drop the read facts, so that its unifications stay small (never
     eassumption on these goals: it unifies them against tw_at, whose length field evaluates Z.to_nat W_LEN
     into a 65616-deep unary nat) *)
  all: clear BGA0 BOA0 BOC0 BOR0 B64' B68' GCK0 CK0 LGA LOA LOC LOR EGA EOA EOC EOR M64 M68.
  all: apply evtF_done; rewrite EQQ; cbv beta.
  all: do 7 eexists; split; [reflexivity|].
  all: split; [exact MU1|].
  all: split; [exact WM|].
  all: split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  all: split; [reflexivity|].
  (* The frame lies outside the hull: the off_stk premise, split by hand. Not `lia`: the kit's lia prunes every
     hypothesis that is not plain arithmetic (LiaTwx2.v zt_plain_arith has no case for `or`), so it drops HOFF,
     its first two branches fail, and its third runs an unpruned Zify.zify that saturates the shadow checks'
     div / mod atoms with euclidean equations (24 GB, killed at the MEM cap). *)
  all: apply (cia_kept m m0 _ _ Bw HW MU1); unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI.
  all: destruct HOFF as [HOFF|HOFF]; [right | left]; exact HOFF.
Qed.

Print Assumptions check_inflight_acked_holds_F.
