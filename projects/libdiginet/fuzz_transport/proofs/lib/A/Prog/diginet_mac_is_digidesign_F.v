(* Modified by Theorem Labs, 2026-10: proof of diginet_mac_is_digidesign_contract_F (fuzz_frame.asan, image A) in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_nosh.v, for three bytes and the result DgnSpec.oui_of. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof diginet_mac_is_digidesign_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_mac_is_digidesign_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of diginet_mac_is_digidesign_contract_F (image A, entry 0x81f14, frame 16 bytes), step for step with
   StepF's step. Each access side goal is closed from an rng fact for exactly the accessed range: before the shadow
   byte load at h = ((mac + i) >> 3) + ASAN_K (i = 0, 1, 2) the proof adds rng RNG h 1 (a sub-range of the shadow
   range), and before the byte load at mac + i it adds rng RNG (mac + i) 1 (a sub-range of [mac, mac + 3)).
   The branch at 0x81f1c (a0 = 0) is not taken: mac <> 0. Each shadow byte k is 0 or (mac + i) mod 8 < k
   (addressable), so the error path goes back to the byte load (0x81f9c, 0x81fa8, 0x81fb8) and no errpath_load1 call
   is reached. *)

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the bytes [a, a + n). *)
Lemma mac_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Theorem diginet_mac_is_digidesign_holds_F : diginet_mac_is_digidesign_contract_F.
Proof.
  unfold diginet_mac_is_digidesign_contract_F, DIGINET_MAC_IS_DIGIDESIGN, DIGINET_MAC_IS_DIGIDESIGN_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mac l
    lo HMAC HLEN BA ST HLO DM APS1 APS2 CELLS DG DC AM RFR RGOT RCELL RMAC RSH.
  pose proof BA as (BA0 & BA1 & _).
  (* the 3 bytes as mrd facts on m: the store at 0x81f18 drops bytes_at for l, whose bytes past mac + 3 may lie in
     the frame *)
  pose proof (bytes_nth m _ l 0 BA ltac:(lia)) as BN0.
  pose proof (bytes_nth m _ l 1 BA ltac:(lia)) as BN1.
  pose proof (bytes_nth m _ l 2 BA ltac:(lia)) as BN2.
  clear BA.
  assert (U0 : bv_unsigned (Z_to_bv 64 mac) = mac) by (apply unsigned_lit; lia).
  set (a0 := Z_to_bv 64 mac) in *. clearbody a0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  carve_frame 16%nat ST.
  (* 0x81f14 addi sp; 0x81f18 sd ra; 0x81f1c beqz a0 *)
  step. step. step. if_cases HZ.
  - (* a0 = 0: excluded by mac <> 0 *)
    zify_cond HZ. exfalso. lia.
  - zify_cond HZ. clear HZ.
    pose proof (mac_shadow_byte_rng RNG mac 3 0 ltac:(lia) RSH) as RS0.
    pose proof (mac_shadow_byte_rng RNG mac 3 1 ltac:(lia) RSH) as RS1.
    pose proof (mac_shadow_byte_rng RNG mac 3 2 ltac:(lia) RSH) as RS2.
    rewrite Z.add_0_r in RS0.
    clear RSH.
    destruct CELLS as (CK & GCK & _).
    destruct AM as (P0 & N0 & PE & AB).
    destruct (AB 0 ltac:(lia)) as (APP0 & k0 & MK0 & SK0).
    destruct (AB 1 ltac:(lia)) as (APP1 & k1 & MK1 & SK1).
    destruct (AB 2 ltac:(lia)) as (APP2 & k2 & MK2 & SK2).
    clear AB.
    unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, shadow_ok in *. unfold ASAN_K in *.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP0, APP1, APP2, APS1, APS2, PE.
    rewrite Z.add_0_r in APP0, MK0, SK0.
    match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
    pose proof (bytes_tp m m0 _ _ 671888 (le8 (wa 707064)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
    pose proof (bytes_tp m m0 _ _ 707064 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
    assert (RDG : ov_read_bytes rsegs m0 (wa 671888) 8 = Some (le8 (wa 707064))).
    { replace (wa 671888) with (wa (671888 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m0 671888 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    assert (RDS : ov_read_bytes rsegs m0 (wa 707064) 8 = Some (le8 (wa 2147450880))).
    { replace (wa 707064) with (wa (707064 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m0 707064 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    pose proof (mrd_tp m m0 _ _ (mac / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK0) as M0.
    pose proof (mrd_tp m m0 _ _ ((mac + 1) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK1) as M1.
    pose proof (mrd_tp m m0 _ _ ((mac + 2) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK2) as M2.
    pose proof (mrd_tp m m0 _ _ (mac + Z.of_nat 0) _ MU1 ltac:(lia) ltac:(lia) BN0) as F0.
    pose proof (mrd_tp m m0 _ _ (mac + Z.of_nat 1) _ MU1 ltac:(lia) ltac:(lia) BN1) as F1.
    pose proof (mrd_tp m m0 _ _ (mac + Z.of_nat 2) _ MU1 ltac:(lia) ltac:(lia) BN2) as F2.
    change (Z.of_nat 0) with 0 in F0. change (Z.of_nat 1) with 1 in F1. change (Z.of_nat 2) with 2 in F2.
    rewrite Z.add_0_r in F0.
    pose proof (Z.mod_pos_bound mac 8 ltac:(lia)) as MB0.
    pose proof (Z.mod_pos_bound (mac + 1) 8 ltac:(lia)) as MB1.
    pose proof (Z.mod_pos_bound (mac + 2) 8 ltac:(lia)) as MB2.
    (* byte 0: 0x81f20 auipc; 0x81f24 ld (GOT_CELL_K); 0x81f28 ld (CELL_K); 0x81f2c srli; 0x81f30 add; 0x81f34 lb;
       0x81f38 bnez *)
    step. step. step.
    step. gen_shr a0 g0 G0.
    rewrite U0 in G0.
    step. gen_addi g0 h0 H0.
    pose proof (rng_sub' _ _ _ (bv_unsigned h0) 1 RS0 ltac:(lia)) as RH0.
    pose proof (rng_sub' _ _ _ (bv_unsigned a0) 1 RMAC ltac:(lia)) as RW0.
    pose proof (rdw0 m0 h0 _ _ M0 ltac:(lia)) as R. step. clear R.
    step.
    destruct SK0 as [C0|[C0 Cu0]].
    1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C0); cbn [negb].
    2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k0) 0) ltac:(lia)); cbn [negb]; step; step;
       rewrite land7, U0, (lts_low (mac mod 8) k0 MB0), (proj2 (Z.ltb_lt _ _) C0); cbn [negb].
    all: remember (nth 0 l (Z_to_bv 8 0)) as b0 eqn:E0.
    all: remember (nth 1 l (Z_to_bv 8 0)) as b1 eqn:E1.
    all: remember (nth 2 l (Z_to_bv 8 0)) as b2 eqn:E2.
    (* 0x81f3c lbu a1,0(a0); 0x81f40 bnez a1 *)
    all: pose proof (rdw0 m0 a0 _ _ F0 ltac:(lia)) as R; step; clear R.
    all: step; if_cases HC0; zify_cond HC0; try unfold zxb in HC0; rewrite ?zxb_u in HC0.
    (* bnez taken (byte 0 is not 00): 0x81f88 li a0,0; 0x81f8c ld ra; 0x81f90 addi sp; 0x81f94 ret *)
    all: lazymatch type of HC0 with
         | bv_unsigned _ = 0 => idtac
         | _ =>
             assert (W : oui_of l = false)
               by (unfold oui_of, at8, bz, b8; rewrite <- E0;
                   destruct (Z.eqb_spec (bv_unsigned b0) 0); [lia | reflexivity]);
             do 4 step; apply evtF_done; rewrite W; do 5 eexists; split; [reflexivity|]; split; [eassumption|];
             split; [eassumption|]; release_frame FR ST (bv_unsigned sp); exact ST
         end.
    (* byte 1: 0x81f44 addi; 0x81f48 srli; 0x81f4c add; 0x81f50 lb; 0x81f54 bnez *)
    all: step; gen_addi a0 w1 U1.
    all: rewrite U0 in U1.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned w1) 1 RMAC ltac:(lia)) as RW1.
    all: step; gen_shr w1 g1 G1.
    all: rewrite U1 in G1.
    all: step; gen_addi g1 h1 H1.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned h1) 1 RS1 ltac:(lia)) as RH1.
    all: pose proof (rdw0 m0 h1 _ _ M1 ltac:(lia)) as R; step; clear R.
    all: step.
    all: destruct SK1 as [C1|[C1 Cu1]].
    all: lazymatch type of C1 with
         | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C1); cbn [negb]
         | _ =>
             rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k1) 0) ltac:(lia)); cbn [negb]; step; step;
             rewrite land7, U1, (lts_low ((mac + 1) mod 8) k1 MB1), (proj2 (Z.ltb_lt _ _) C1); cbn [negb]
         end.
    (* 0x81f58 lbu a1,0(a1); 0x81f5c li a3,160; 0x81f60 bne a1,a3 *)
    all: pose proof (rdw0 m0 w1 _ _ F1 ltac:(lia)) as R; step; clear R.
    all: step; step; if_cases HC1; zify_cond HC1; try unfold zxb in HC1; rewrite ?zxb_u in HC1.
    (* bne taken (byte 1 is not a0): 0x81f88 li a0,0; 0x81f8c ld ra; 0x81f90 addi sp; 0x81f94 ret *)
    all: lazymatch type of HC1 with
         | bv_unsigned _ = 160 => idtac
         | _ =>
             assert (W : oui_of l = false)
               by (unfold oui_of, at8, bz, b8; rewrite <- E0, <- E1;
                   destruct (Z.eqb_spec (bv_unsigned b0) 0); [| lia];
                   destruct (Z.eqb_spec (bv_unsigned b1) 160); [lia | reflexivity]);
             do 4 step; apply evtF_done; rewrite W; do 5 eexists; split; [reflexivity|]; split; [eassumption|];
             split; [eassumption|]; release_frame FR ST (bv_unsigned sp); exact ST
         end.
    (* byte 2: 0x81f64 addi; 0x81f68 srli; 0x81f6c add; 0x81f70 lb; 0x81f74 bnez *)
    all: step; gen_addi a0 w2 U2.
    all: rewrite U0 in U2.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned w2) 1 RMAC ltac:(lia)) as RW2.
    all: step; gen_shr w2 g2 G2.
    all: rewrite U2 in G2.
    all: step; gen_addi g2 h2 H2.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned h2) 1 RS2 ltac:(lia)) as RH2.
    all: pose proof (rdw0 m0 h2 _ _ M2 ltac:(lia)) as R; step; clear R.
    all: step.
    all: destruct SK2 as [C2|[C2 Cu2]].
    all: lazymatch type of C2 with
         | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C2); cbn [negb]
         | _ =>
             rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k2) 0) ltac:(lia)); cbn [negb]; step; step;
             rewrite land7, U2, (lts_low ((mac + 2) mod 8) k2 MB2), (proj2 (Z.ltb_lt _ _) C2); cbn [negb]
         end.
    (* 0x81f78 lbu a0,0(a0); 0x81f7c addi a0,a0,-126; 0x81f80 seqz; 0x81f84 j; 0x81f8c ld ra; 0x81f90 addi sp;
       0x81f94 ret *)
    all: pose proof (rdw0 m0 w2 _ _ F2 ltac:(lia)) as R; step; clear R.
    all: do 6 step; apply evtF_done.
    all: lazymatch goal with |- context [v_sltiu (Z_to_bv 64 ?X) 1] =>
           assert (A0 : v_sltiu (Z_to_bv 64 X) 1 = Z_to_bv 64 (if oui_of l then 1 else 0))
             by (unfold v_sltiu, oui_of, at8, bz, b8; try unfold zxb; rewrite <- E0, <- E1, <- E2;
                 rewrite ?zxb_u, HC0, HC1;
                 pose proof (byte_range b2) as X2;
                 destruct (Z.eq_dec (bv_unsigned b2) 126) as [E|E];
                 [ rewrite E; vm_compute; reflexivity
                 | rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r;
                   rewrite unsigned_lit_wrap; change (bv_wrap 64 1) with 1;
                   replace ((bv_unsigned b2 + -126) mod 2 ^ 64 <? 1) with false; [reflexivity|];
                   symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia ]);
           rewrite A0
         end.
    all: do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
    all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.
