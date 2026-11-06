(* Proof of diginet_sum16_contract_F (diginet_sum16_F_c.v): fuzz_frame.asan-ubsan, image B, entry 0x81e30, frame 16
   bytes. The run is walked with StepF's step. Each data access is closed from the rng premise of exactly the range it
   touches: the frame for the store and the load of ra, the two cells for the loads at 0x81e44 and 0x81e48, and in the
   loop, before the 1-byte shadow load at 0x81e74 and the 1-byte load at 0x81e7c, an rng fact for that one byte (a
   sub-range of the shadow range or of [p, p + n)).
   When n = 0 the branch at 0x81e3c goes to 0x81ea8 at once and the result is 0 = lib_sum16 [].
   When n <> 0 the loop (Lemma sum16_loop) runs one turn for each byte. In the turn for byte i the three UBSan checks
   are not taken: 0x81e58 (p + i < p) and 0x81e64 ((p <> 0) = (p + i = 0)) because p + i < 2^64 does not wrap and
   p <> 0 (the premise, for bb not empty), 0x81e68 (p = 0) because p <> 0. The shadow byte k of p + i is 0 or
   (p + i) mod 8 < k (addressable), so
   the code goes on to the byte load (0x81e78, 0x81e9c) and never reaches the call at 0x81ea4. a3 holds the sum of
   the bytes read, mod 2^64; after the last turn 0x81ea8-0x81eac keep its low 16 bits, which is lib_sum16 bb. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof diginet_sum16_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_sum16_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The sum of the first i + 1 bytes. *)
Lemma sum16_firstn_S : forall (l : list byte) (i : nat), (i < length l)%nat ->
  sum_bytes (firstn (S i) l) = sum_bytes (firstn i l) + bz (nth i l (Z_to_bv 8 0)).
Proof.
  induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [firstn sum_bytes nth].
  - rewrite firstn_O. cbn [sum_bytes]. lia.
  - rewrite IH by lia. lia.
Qed.

(* 0x81ea8 slli a0,a3,0x30 then 0x81eac srli a0,a0,0x30: the low 16 bits of a3. *)
Lemma sum16_low16 : forall w : word,
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 48))) 48)
  = Z_to_bv 64 (bv_unsigned w mod 2^16).
Proof.
  intros w. f_equal. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2^64) in R.
  rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* lib_sum16 from the sum mod 2^64. *)
Lemma sum16_lib_mod64 : forall l, lib_sum16 l = (sum_bytes l mod 2^64) mod 2^16.
Proof. intros l. unfold lib_sum16. Z.div_mod_to_equations. lia. Qed.

(* The shadow byte of p + i, i < n, lies in the shadow range of [p, p + n). *)
Lemma sum16_shadow_rng : forall RNG p n i, 0 <= p -> 0 <= i < n ->
  ExecF.rng RNG (p / 8 + ASAN_K) ((p + n - 1) / 8 + ASAN_K - (p / 8 + ASAN_K) + 1) ->
  ExecF.rng RNG ((p + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG p n i Hp Hi H. eapply rng_sub'; [exact H|]. Z.div_mod_to_equations. lia.
Qed.

(* A shadow byte of an application address lies outside a 16-byte frame of application memory. *)
Lemma sum16_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 16 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

(* The loop at 0x81e58, at the turn for byte i with S k turns left: a0 = p, a1 = S k, a2 = a6 = p + i, a3 = the sum
   of the first i bytes mod 2^64, a4 = the shadow offset 0x7fff8000, a5 = 1 (p <> 0). The run reaches 0x81ea8 with
   a3 = the sum of all the bytes mod 2^64, memory unchanged; K is the rest of the run from there. *)
Lemma sum16_loop : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop) (k : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bb : list byte) (i : nat),
  (i + S k)%nat = length bb ->
  0 < p -> p + Z.of_nat (length bb) <= 2^64 ->
  bv_unsigned a0 = p ->
  bv_unsigned a1 = Z.of_nat (S k) ->
  bv_unsigned a2 = p + Z.of_nat i ->
  bv_unsigned a3 = sum_bytes (firstn i bb) mod 2^64 ->
  a5 = Z_to_bv 64 1 ->
  bv_unsigned a6 = p + Z.of_nat i ->
  (forall j, (j < length bb)%nat -> mrd rsegs m (wa (p + Z.of_nat j)) = Some (nth j bb (Z_to_bv 8 0))) ->
  (forall j, (j < length bb)%nat -> exists kj : byte,
     mrd rsegs m (wa ((p + Z.of_nat j) / 8 + ASAN_K)) = Some kj /\ shadow_ok (p + Z.of_nat j) (bv_signed kj)) ->
  ExecF.rng RNG p (Z.of_nat (length bb)) ->
  ExecF.rng RNG (p / 8 + ASAN_K) ((p + Z.of_nat (length bb) - 1) / 8 + ASAN_K - (p / 8 + ASAN_K) + 1) ->
  (forall t0' a1' a2' a3' a6' a7' : word, bv_unsigned a3' = sum_bytes bb mod 2^64 ->
     ExecF.evtF rsegs RNG Q
       (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 a1' a2' a3' (Z_to_bv 64 2147450880) (Z_to_bv 64 1) a6' a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x8b050) fc None m (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 2147450880) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8b000) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q k. induction k as [|k IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bb i
      HL HP HE U0 U1 U2 U3 E5 U6 BN SH RP RS K; subst a5.
  all: assert (Hi : (i < length bb)%nat) by lia.
  all: destruct (SH i Hi) as (ki & MK & SK).
  all: pose proof (BN i Hi) as MB.
  all: pose proof (sum16_shadow_rng RNG p (Z.of_nat (length bb)) (Z.of_nat i) ltac:(lia) ltac:(lia) RS) as RH.
  all: pose proof (rng_sub' _ _ _ (p + Z.of_nat i) 1 RP ltac:(lia)) as RB.
  all: unfold shadow_ok, ASAN_K in *.
  all: pose proof (Z.mod_pos_bound (p + Z.of_nat i) 8 ltac:(lia)) as MB8.
  all: assert (SL : v_sltiu a2 1 = Z_to_bv 64 0)
         by (unfold v_sltiu; rewrite U2; change (bv_wrap 64 1) with 1;
             replace (p + Z.of_nat i <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
  (* UBSan check 1: 0x81e58 bltu a2,a0 (to the unimp word at 0x81ebc when p + i < p) *)
  all: step; if_cases HU1; zify_cond HU1; rewrite ?U0, ?U2 in HU1; [exfalso; lia|].
  (* UBSan check 2: 0x81e5c seqz a7,a2; 0x81e60 xor a7,a5,a7; 0x81e64 beqz a7 *)
  all: step; rewrite ?SL.
  all: step.
  all: step; if_cases HU2; [exfalso; revert HU2; vm_compute; discriminate|].
  (* UBSan check 3: 0x81e68 beqz a0 *)
  all: step; if_cases HU3; zify_cond HU3; rewrite ?U0 in HU3; [exfalso; lia|].
  (* the shadow byte: 0x81e6c srli a7,a2,3; 0x81e70 add a7,a7,a4; 0x81e74 lb a7,0(a7); 0x81e78 bnez a7 *)
  all: step; gen_shr a2 g G.
  all: rewrite U2 in G.
  all: step; gen_addi g h H.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RH ltac:(lia)) as RH'.
  all: pose proof (rdw0 m h _ _ MK ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK as [C|[C Cu]].
  all: lazymatch type of C with
       | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
       | _ =>
           rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed ki) 0) ltac:(lia)); cbn [negb];
           (* 0x81e98 andi t0,a2,7; 0x81e9c blt t0,a7 (back to the byte load when (p + i) mod 8 < k) *)
           step; step;
           rewrite land7, U2, (lts_low ((p + Z.of_nat i) mod 8) ki MB8), (proj2 (Z.ltb_lt _ _) C); cbn [negb]
       end.
  (* the byte: 0x81e7c lbu a7,0(a6); 0x81e80 a1 - 1; 0x81e84 a2 + 1; 0x81e88 a3 + the byte; 0x81e8c a6 + 1 *)
  all: pose proof (rng_sub' _ _ _ (bv_unsigned a6) 1 RB ltac:(lia)) as RW.
  all: pose proof (rdw0 m a6 _ _ MB ltac:(lia)) as R; step; clear R.
  all: remember (nth i bb (Z_to_bv 8 0)) as b eqn:Eb.
  all: step; step; step; step.
  (* 0x81e90 bnez a1 *)
  all: step.
  all: assert (ES : sum_bytes (firstn (S i) bb) = sum_bytes (firstn i bb) + bv_unsigned b)
         by (rewrite sum16_firstn_S by exact Hi; rewrite <- Eb; reflexivity).
  all: assert (U3' : bv_unsigned (Z_to_bv 64 (bv_unsigned a3 + bv_unsigned (zxb b)))
                     = sum_bytes (firstn (S i) bb) mod 2^64)
         by (rewrite unsigned_lit_wrap, U3; unfold zxb; rewrite zxb_u, ES, Z.add_mod_idemp_l by lia; reflexivity).
  1, 2: (* the last turn: a1 - 1 = 0, 0x81e94 j 0x81ea8 *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with false by (rewrite U1; vm_compute; reflexivity) end;
        cbv iota; step;
        apply K;
        assert (EL : firstn (S i) bb = bb) by (replace (S i) with (length bb) by lia; apply firstn_all);
        rewrite EL in U3'; exact U3'.
  (* another turn: a1 - 1 <> 0, back to 0x81e58 *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
         replace c with true
           by (rewrite U1; unfold bv_eqb; rewrite !unsigned_lit by lia;
               replace (Z.of_nat (S (S k)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
               reflexivity) end.
  all: cbv iota.
  all: eapply IH with (i := S i) (p := p) (bb := bb);
       [ lia | lia | lia | exact U0
       | rewrite U1, unsigned_lit by lia; lia
       | rewrite U2, unsigned_lit by lia; lia
       | exact U3'
       | reflexivity
       | rewrite U6, unsigned_lit by lia; lia
       | exact BN | exact SH | exact RP | exact RS | exact K ].
Qed.

Theorem diginet_sum16_holds_F : diginet_sum16_contract_F.
Proof.
  unfold diginet_sum16_contract_F, DIGINET_SUM16, DIGINET_SUM16_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bb
    lo HP BA ST HLO DP APS1 APS2 CELLS DG DC AM RFR RGOT RCELL RP RSH.
  pose proof (bytes_at_bound rsegs m p bb BA) as BB.
  (* p <> 0 is given for a non-empty bb only: as a length fact, so lia reads it *)
  assert (HPw : (0 < length bb)%nat -> p <> 0) by (intros Hl; apply HP; intros E; subst bb; cbn in Hl; lia).
  clear HP.
  (* the bytes of bb as mrd facts on m: the store of ra at 0x81e34 drops bytes_at, whose range may meet the frame
     when bb = [] *)
  assert (BN : forall j, (j < length bb)%nat -> mrd rsegs m (wa (p + Z.of_nat j)) = Some (nth j bb (Z_to_bv 8 0)))
    by (intros j Hj; exact (bytes_nth m p bb j BA Hj)).
  clear BA.
  remember (Z_to_bv 64 p) as a0 eqn:E0.
  assert (LB : 0 <= Z.of_nat (length bb) < 2^64) by lia.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  carve_frame 16%nat ST.
  (* 0x81e30 addi sp,sp,-16; 0x81e34 sd ra,8(sp) *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ =>
    rename MU' into MU1; first [constr_eq m1 m0 | rename m1 into m0] end.
  (* 0x81e38 li a3,0; 0x81e3c beqz a1 *)
  step. step.
  if_cases HZ.
  - (* n = 0: 0x81ea8 slli; 0x81eac srli (a0 = 0); 0x81eb0 ld ra; 0x81eb4 addi sp; 0x81eb8 ret *)
    zify_cond HZ.
    assert (E : bb = []) by (destruct bb as [|x bb']; [reflexivity | cbn [length] in HZ; lia]).
    subst bb.
    do 5 step. apply evtF_done.
    do 9 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    release_frame FR ST (bv_unsigned sp). exact ST.
  - zify_cond HZ.
    assert (NE : bb <> []) by (intro E; subst bb; apply HZ; reflexivity).
    assert (HP : p <> 0) by (apply HPw; destruct bb; [contradiction | cbn; lia]).
    specialize (DP NE). specialize (AM NE). specialize (RGOT NE). specialize (RCELL NE).
    specialize (RP NE).
    specialize (RSH NE).
    assert (U0 : bv_unsigned a0 = p) by (subst a0; apply unsigned_lit; lia).
    clear E0.
    destruct CELLS as (CK & GCK & _).
    destruct AM as (P0 & N0 & PE & AB).
    unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *.
    pose proof (bytes_tp m m0 _ _ 670960 (le8 (wa 706168)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
    pose proof (bytes_tp m m0 _ _ 706168 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
    assert (RDG : ov_read_bytes rsegs m0 (wa 670960) 8 = Some (le8 (wa 706168))).
    { replace (wa 670960) with (wa (670960 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m0 670960 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    assert (RDS : ov_read_bytes rsegs m0 (wa 706168) 8 = Some (le8 (wa 2147450880))).
    { replace (wa 706168) with (wa (706168 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m0 706168 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    clear GOT0 SV0 GCK CK.
    (* the bytes and their shadow bytes on m0: [p, p + n) lies outside the frame (off_stk), and a shadow byte of
       an application address lies outside the frame (app_mem) *)
    assert (BN0 : forall j, (j < length bb)%nat ->
                  mrd rsegs m0 (wa (p + Z.of_nat j)) = Some (nth j bb (Z_to_bv 8 0))).
    { intros j Hj. apply (mrd_tp m m0 _ _ _ _ MU1); [lia | lia | exact (BN j Hj)]. }
    assert (SH0 : forall j, (j < length bb)%nat -> exists kj : byte,
                  mrd rsegs m0 (wa ((p + Z.of_nat j) / 8 + ASAN_K)) = Some kj /\
                  shadow_ok (p + Z.of_nat j) (bv_signed kj)).
    { intros j Hj. destruct (AB (Z.of_nat j) ltac:(lia)) as (APP & kj & MK & SK).
      exists kj. split; [| exact SK].
      unfold shadow_addr in MK.
      exact (sum16_shadow_tp m m0 _ _ _ _ MU1 ltac:(lia) APS1 APS2 APP MK). }
    clear BN AB.
    (* 0x81e40 auipc a2; 0x81e44 ld a2 (GOT_CELL_K); 0x81e48 ld a4 (CELL_K); 0x81e4c snez a5,a0; 0x81e50 mv a6,a0;
       0x81e54 mv a2,a0 *)
    step. step. step. step. step. step.
    assert (EK : length bb = S (Nat.pred (length bb))) by (destruct bb; [contradiction | reflexivity]).
    (* the loop, then 0x81ea8 slli; 0x81eac srli; 0x81eb0 ld ra; 0x81eb4 addi sp; 0x81eb8 ret *)
    eapply sum16_loop with (k := Nat.pred (length bb)) (i := 0%nat) (p := p) (bb := bb);
      [ lia | lia | lia | exact U0
      | rewrite unsigned_lit by lia; lia
      | rewrite U0; lia
      | rewrite unsigned_lit by lia; reflexivity
      | unfold v_sltu, c_ltu; destruct (bv_ltu (Z_to_bv 64 0) a0) eqn:EL; [reflexivity|];
        exfalso; zify_cond EL; rewrite ?U0 in EL; lia
      | rewrite U0; lia
      | exact BN0 | exact SH0 | exact RP | exact RSH | ].
    intros t0' a1' a2' a3' a6' a7' U3'.
    step. step.
    rewrite sum16_low16, U3', <- sum16_lib_mod64.
    step. step. step.
    apply evtF_done.
    do 9 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
