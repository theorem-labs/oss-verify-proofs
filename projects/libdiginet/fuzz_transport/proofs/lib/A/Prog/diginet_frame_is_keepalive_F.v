(* Modified by Theorem Labs, 2026-10: proof of diginet_frame_is_keepalive_contract_F (image A), in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_nosh.v; the functional steps follow proofs/libdiginet/fuzz_frame/lib/Prog/diginet_frame_is_keepalive.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof diginet_frame_is_keepalive_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_is_keepalive_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(* Proof of diginet_frame_is_keepalive_contract_F (image A, entry 0x81fc0, frame 16). The run is walked with StepF's
   step. Each data access is closed from the rng premise of exactly the range it touches: the frame for the store and
   load of ra, the two image cells, the shadow byte and the byte of f + 30, and, under the premise's condition,
   those of f + 40, f + 32 and body. Each shadow byte comes from the addressable premise of its range: for the 1-byte
   loads it is 0 or a mod 8 < k <= 7, so the compare at 0x82058 / 0x82068 goes back to the load; for the 8-byte loads
   the range runs to the end of its granule, so the byte is 0 and the branch at 0x82004 / 0x82024 is not taken. The
   four error-path calls (0x82064, 0x82070, 0x82078, 0x8207c) are therefore never reached. *)

(* All the bytes bs at a, read at once. *)
Lemma ka_rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* The same read at a register value w whose number is a. *)
Lemma ka_rdw : forall m (w : word) a bs n, bytes_at rsegs m a bs -> length bs = n -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w n = Some bs.
Proof.
  intros m w a bs n H L E. rewrite <- (Z_to_bv_bv_unsigned w), E.
  change (Z_to_bv 64 a) with (wa a). apply ka_rd_all; assumption.
Qed.

(* A byte whose signed value is 0 is 0. *)
Lemma ka_signed0 : forall k : byte, bv_signed k = 0 -> bv_unsigned k = 0.
Proof.
  intros k H. pose proof (byte_range k) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  replace (2 ^ Z.of_N 8) with 256 in H by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of a 1-byte addressable range. *)
Lemma ka_addr1 : forall m a, addressable m a 1 ->
  0 <= a /\ a + 1 <= APPMEM_END /\ app_mem a /\
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\
            (bv_signed k = 0 \/ (a mod 8 < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m a (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP & k & MK & SK).
  rewrite Z.add_0_r in APP, MK, SK. unfold shadow_addr in MK. unfold shadow_ok in SK.
  split; [lia|]. split; [lia|]. split; [exact APP|]. exists k. split; [exact MK | exact SK].
Qed.

(* The shadow byte of an 8-byte addressable range is 0: the range holds the last byte of its first granule. *)
Lemma ka_addr8 : forall m a, addressable m a 8 ->
  0 <= a /\ a + 8 <= APPMEM_END /\ app_mem a /\
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\ bv_unsigned k = 0.
Proof.
  intros m a (P0 & N0 & PE & AB).
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB.
  destruct (AB 0 ltac:(lia)) as (APP & _). rewrite Z.add_0_r in APP.
  destruct (AB (7 - a mod 8) ltac:(lia)) as (_ & k & MK & SK).
  assert (E : (a + (7 - a mod 8)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
  assert (M7 : (a + (7 - a mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  unfold shadow_addr in MK. rewrite E in MK. unfold shadow_ok in SK. rewrite M7 in SK.
  split; [lia|]. split; [lia|]. split; [exact APP|]. exists k. split; [exact MK|].
  destruct SK as [S0 | [S1 S2]]; [apply ka_signed0; exact S0 | lia].
Qed.

(* A shadow byte of an application address lies outside a 16-byte frame of application memory. *)
Lemma ka_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 16 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

Theorem diginet_frame_is_keepalive_holds_F : diginet_frame_is_keepalive_contract_F.
Proof.
  unfold diginet_frame_is_keepalive_contract_F, DIGINET_FRAME_IS_KEEPALIVE, DIGINET_FRAME_IS_KEEPALIVE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f cmd body lo bb HF0 HCMD HBD BCMD BFB BBB ST HLO CELLS APW1 APW2 DGOT DCELL D30 A30 C40 C32
    RFR RGOT RCELL R30 RS30 R40 RS40 R32 RS32 RB RSB.
  remember (Z_to_bv 64 f) as a0 eqn:E0.
  assert (U0 : bv_unsigned a0 = f) by (subst a0; apply unsigned_lit; lia).
  clear E0. subst f.
  pose proof (bytes_at_bound rsegs m _ _ BBB) as BBb.
  (* the byte facts stay on m: the store of ra would transport or drop them *)
  assert (KEEP : bytes_at rsegs m (bv_unsigned a0 + 30) [b8 cmd] /\
                 bytes_at rsegs m (bv_unsigned a0 + 32)
                   (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) /\
                 bytes_at rsegs m body bb) by (split; [|split]; assumption).
  clear BCMD BFB BBB.
  destruct (ka_addr1 m _ A30) as (P30 & E30 & APP30 & k30 & MK30 & SK30). clear A30.
  unfold off_stk in DGOT, DCELL, D30.
  unfold GOT_CELL_K, CELL_K in DGOT, DCELL, RGOT, RCELL.
  unfold shadow_addr, ASAN_K in RS30.
  unfold APPMEM_END in E30.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ =>
    rename MU' into MU1; first [constr_eq m1 m0 | rename m1 into m0] end.
  pose proof CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  assert (GCK0 : bytes_at rsegs m0 671888 (le8 (wa 707064)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact GCK]).
  assert (CK0 : bytes_at rsegs m0 707064 (le8 (wa 2147450880)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact CK]).
  pose proof (ka_rd_all m0 _ _ 8 GCK0 (length_le8 _)) as RDG.
  pose proof (ka_rd_all m0 _ _ 8 CK0 (length_le8 _)) as RDS.
  clear GCK0 CK0 GCK CK.
  pose proof (ka_shadow_tp m m0 _ _ _ k30 MU1 ltac:(lia) APW1 APW2 APP30 MK30) as M30. unfold ASAN_K in M30.
  destruct KEEP as (BCMD & BFB & BBB).
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + 30) _ MU1 ltac:(lia) ltac:(lia) (bytes_one m _ _ BCMD)) as F30.
  step. if_cases HZ.
  { exfalso. zify_cond HZ. lia. }
  step. step. step.
  step. gen_addi a0 w30 U30.
  pose proof (rng_sub' _ _ _ (bv_unsigned w30) 1 R30 ltac:(lia)) as RW30.
  step. gen_shr w30 g30 G30.
  rewrite U30 in G30.
  step. gen_addi g30 h30 H30.
  pose proof (rng_sub' _ _ _ (bv_unsigned h30) 1 RS30 ltac:(lia)) as RH30.
  pose proof (rdw0 m0 h30 _ _ M30 ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 30) 8 ltac:(lia)) as MB30.
  assert (UC : bv_unsigned (b8 cmd) = cmd) by (exact (bz_b8 cmd HCMD)).
  destruct SK30 as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k30) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U30, (lts_low ((bv_unsigned a0 + 30) mod 8) k30 MB30), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: pose proof (rdw0 m0 w30 _ _ F30 ltac:(lia)) as R; step; clear R.
  all: step; if_cases Ka; zify_cond Ka; rewrite ?zxb_u, ?UC in Ka.
  (* cmd <> 0: 0x82048 returns 0 *)
  1, 3: assert (KA : cmd <> 0) by (first [exact Ka | Z.div_mod_to_equations; lia]);
        assert (W : keepalive_of cmd (Z.of_nat (length bb)) bb = false)
          by (unfold keepalive_of; rewrite (proj2 (Z.eqb_neq _ _) KA); reflexivity);
        do 4 step; apply evtF_done; rewrite W; do 5 eexists; split; [reflexivity|]; split; [eassumption|];
        split; [eassumption|]; release_frame FR ST (bv_unsigned sp); exact ST.
  (* cmd = 0 *)
  all: assert (KA : cmd = 0) by (first [exact Ka | Z.div_mod_to_equations; lia]); clear Ka; rename KA into Ka.
  all: destruct (C40 Ka) as (D40 & A40); specialize (R40 Ka); specialize (RS40 Ka).
  all: unfold off_stk in D40.
  all: destruct (ka_addr8 m _ A40) as (P40 & E40 & APP40 & k40 & MK40 & K40).
  all: unfold shadow_addr, ASAN_K in RS40; unfold APPMEM_END in E40.
  all: pose proof (ka_shadow_tp m m0 _ _ _ k40 MU1 ltac:(lia) APW1
         APW2
         APP40 MK40) as M40; unfold ASAN_K in M40.
  all: apply bytes_at_app in BFB; destruct BFB as [BW1 BW2]; rewrite length_le8 in BW2;
       change (Z.of_nat 8) with 8 in BW2; replace (bv_unsigned a0 + 32 + 8) with (bv_unsigned a0 + 40) in BW2 by lia.
  all: assert (BL0 : bytes_at rsegs m0 (bv_unsigned a0 + 40) (le8 (Z_to_bv 64 (Z.of_nat (length bb)))))
         by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact BW2]).
  all: step; gen_addi a0 w40 U40.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w40) 8 R40 ltac:(lia)) as RW40.
  all: step; gen_shr w40 g40 G40.
  all: rewrite U40 in G40.
  all: step; gen_addi g40 h40 H40.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h40) 1 RS40 ltac:(lia)) as RH40.
  all: pose proof (rdw0 m0 h40 _ _ M40 ltac:(lia)) as R; step; clear R.
  all: step; if_cases HS40; [exfalso; zify_cond HS40; rewrite ?zxb_u in HS40; first [lia | Z.div_mod_to_equations; lia] |].
  all: pose proof (ka_rdw m0 w40 _ _ 8 BL0 (length_le8 _) ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Kb; zify_cond Kb.
  (* blen <> 1: 0x82048 returns 0 *)
  1, 3: assert (N1 : Z.of_nat (length bb) <> 1)
          by (first [ intro E; rewrite E in Kb; apply Kb; reflexivity
                    | rewrite ?unsigned_lit in Kb by lia; lia
                    | rewrite ?unsigned_lit_wrap in Kb; Z.div_mod_to_equations; lia ]);
        assert (W : keepalive_of cmd (Z.of_nat (length bb)) bb = false)
          by (unfold keepalive_of; rewrite Ka, (proj2 (Z.eqb_neq _ _) N1); reflexivity);
        do 4 step; apply evtF_done; rewrite W; do 5 eexists; split; [reflexivity|]; split; [eassumption|];
        split; [eassumption|]; release_frame FR ST (bv_unsigned sp); exact ST.
  (* blen = 1 *)
  all: assert (N1 : Z.of_nat (length bb) = 1)
         by (first [ lia | Z.div_mod_to_equations; lia | rewrite ?unsigned_lit in Kb by lia; lia
                   | rewrite ?unsigned_lit_wrap in Kb; Z.div_mod_to_equations; lia ]).
  all: destruct (C32 Ka N1) as (D32 & A32 & DB & AB1);
       specialize (R32 Ka N1); specialize (RS32 Ka N1); specialize (RB Ka N1); specialize (RSB Ka N1).
  all: unfold off_stk in D32, DB.
  all: destruct (ka_addr8 m _ A32) as (P32 & E32 & APP32 & k32 & MK32 & K32).
  all: destruct (ka_addr1 m _ AB1) as (PB & EB & APPB & kb & MKB & SKB).
  all: unfold shadow_addr, ASAN_K in RS32, RSB; unfold APPMEM_END in E32, EB.
  all: pose proof (ka_shadow_tp m m0 _ _ _ k32 MU1 ltac:(lia) APW1
         APW2
         APP32 MK32) as M32; unfold ASAN_K in M32.
  all: pose proof (ka_shadow_tp m m0 _ _ _ kb MU1 ltac:(lia) APW1
         APW2
         APPB MKB) as MB0; unfold ASAN_K in MB0.
  all: assert (BP0 : bytes_at rsegs m0 (bv_unsigned a0 + 32) (le8 (Z_to_bv 64 body)))
         by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact BW1]).
  all: pose proof (bytes_nth m _ bb 0 BBB ltac:(lia)) as FB; change (Z.of_nat 0) with 0 in FB; rewrite Z.add_0_r in FB.
  all: pose proof (mrd_tp m m0 _ _ body _ MU1 ltac:(lia) ltac:(lia) FB) as FB0.
  all: step; gen_addi a0 w32 U32.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w32) 8 R32 ltac:(lia)) as RW32.
  all: step; gen_shr w32 g32 G32.
  all: rewrite U32 in G32.
  all: step; gen_addi g32 h32 H32.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h32) 1 RS32 ltac:(lia)) as RH32.
  all: pose proof (rdw0 m0 h32 _ _ M32 ltac:(lia)) as R; step; clear R.
  all: step; if_cases HS32; [exfalso; zify_cond HS32; rewrite ?zxb_u in HS32; first [lia | Z.div_mod_to_equations; lia] |].
  all: pose proof (ka_rdw m0 w32 _ _ 8 BP0 (length_le8 _) ltac:(lia)) as R; step; clear R.
  all: remember (Z_to_bv 64 body) as wb eqn:EWB.
  all: assert (UB : bv_unsigned wb = body) by (subst wb; apply unsigned_lit; lia).
  all: clear EWB.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned wb) 1 RB ltac:(lia)) as RWB.
  all: step; gen_shr wb gb GB.
  all: rewrite UB in GB.
  all: step; gen_addi gb hb HB.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned hb) 1 RSB ltac:(lia)) as RHB.
  all: pose proof (rdw0 m0 hb _ _ MB0 ltac:(lia)) as R; step; clear R.
  all: step.
  all: pose proof (Z.mod_pos_bound body 8 ltac:(lia)) as MBB.
  all: destruct SKB as [C'|[C' Cu']].
  1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
  all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)); cbn [negb]; step; step;
         rewrite land7, UB, (lts_low (body mod 8) kb MBB), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
  all: remember (nth 0 bb (Z_to_bv 8 0)) as b eqn:Eb.
  all: pose proof (rdw0 m0 wb _ _ FB0 ltac:(lia)) as R; step; clear R.
  all: do 5 step; apply evtF_done.
  all: assert (A0 : v_sltiu (zxb b) 1 = Z_to_bv 64 (if keepalive_of cmd (Z.of_nat (length bb)) bb then 1 else 0))
         by (unfold v_sltiu, zxb; rewrite zxb_u; change (bv_wrap 64 1) with 1;
             unfold keepalive_of, at8, bz, b8; rewrite <- Eb, Ka, N1, !Z.eqb_refl; cbn [andb];
             pose proof (byte_range b) as Xb; destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E];
             [ rewrite E; reflexivity
             | rewrite (proj2 (Z.eqb_neq _ _) E), (proj2 (Z.ltb_ge (bv_unsigned b) 1)) by lia; reflexivity ]).
  all: rewrite A0; do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
  all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.
