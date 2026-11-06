From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_frame_inspect_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of reac_frame_inspect_contract_F (A image, entry 0x812dc). It follows reac_frame_inspect.v step for step,
   with StepF's step. Each access side goal is closed from an rng fact for exactly the accessed range: before the
   shadow byte load at h = ((a0 + off) >> 3) + ASAN_K the proof adds rng RNG h 1 (a sub-range of the shadow range),
   and before the byte load at w = a0 + off it adds rng RNG w 1 (a sub-range of the buffer). *)

Ltac wf_false :=
  unfold inspect_result, inspect_wf, inspect_byte;
  repeat match goal with
  | E : ?b = nth ?i ?bs (Z_to_bv 8 0) |- context [nth ?i ?bs (Z_to_bv 8 0)] => rewrite <- E
  end;
  repeat match goal with
  | Q : bv_unsigned ?b = ?c |- context [bv_unsigned ?b =? ?c] => rewrite (proj2 (Z.eqb_eq (bv_unsigned b) c) Q)
  | Q : bv_unsigned ?b <> ?c |- context [bv_unsigned ?b =? ?c] => rewrite (proj2 (Z.eqb_neq (bv_unsigned b) c) Q)
  | Q : ?x = 1492 |- context [?x =? 1492] => rewrite (proj2 (Z.eqb_eq x 1492) Q)
  end;
  reflexivity.

Ltac exit0 FR ST sp :=
  let W := fresh "W" in
  match goal with |- context [inspect_result ?l ?bs] => assert (W : inspect_result l bs = 0) by wf_false end;
  do 6 step; apply evtF_done; rewrite W; do 5 eexists; split; [reflexivity|]; split; [eassumption|];
  split; [eassumption|]; release_frame FR ST (bv_unsigned sp); exact ST.

(* After the beqz on shadow byte k, the path k = 0 and the path k <> 0 (andi, blt) meet at the same pc in the same
   state but for one scratch register: the andi destination, which the postcondition quantifies (an a1'..a4' slot).
   v is what that register holds on the path k = 0. sk_join proves the meeting point once, for every value x of the
   register, and closes both paths with it: each shadow check leaves one goal. (A plain destruct of SK doubles the
   goals at each check, 64 at the end of this proof: 268 s for this file against 24 s with the join.) *)
Ltac sk_join a0 off U k SK MB v x :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      lazymatch eval pattern v in R with
      | ?Rf _ =>
          let T := eval cbv beta in (forall x : word, evtF segs RNG Q (MS (Rf x) F (Z_to_bv 64 pc) fc rv m ro)) in
          let HJ := fresh "HJ" in
          assert (HJ : T);
          [ intros x
          | let C := fresh "C" in let Cu := fresh "Cu" in
            destruct SK as [C|[C Cu]];
            [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]; exact (HJ v)
            | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
              rewrite land7, U, (lts_low ((bv_unsigned a0 + off) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C);
              cbn [negb]; exact (HJ _) ] ]
      end
  end.

(* The shadow check of the byte at w = a0 + off: g = w >> 3, h = g + ASAN_K, load k at h, beqz k, then sk_join.
   RB / RS: the rng facts of the buffer and of this shadow byte; v / x as in sk_join. *)
Ltac shadow_pass a0 m0 off w g h U G H M k SK MB RB RS v x :=
  step; gen_addi a0 w U;
  let RW := fresh "RW" in pose proof (rng_sub' _ _ _ (bv_unsigned w) 1 RB ltac:(lia)) as RW;
  step; gen_shr w g G; rewrite U in G;
  step; gen_addi g h H;
  let RH := fresh "RH" in pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH;
  let R := fresh "R" in pose proof (rdw0 m0 h _ _ M ltac:(lia)) as R; step; clear R;
  step;
  sk_join a0 off U k SK MB v x.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the buffer [a, a + n). *)
Lemma inspect_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Theorem reac_frame_inspect_holds_F : reac_frame_inspect_contract_F.
Proof.
  unfold reac_frame_inspect_contract_F, REAC_FRAME_INSPECT, REAC_FRAME_INSPECT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    lo ST HLO HB RFR RGOT RCELL RBUF RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  destruct (Z.eq_dec (bv_unsigned a1) 1492) as [EL|NL].
  2: { clear RGOT RCELL RBUF RSH.
       carve_frame 16%nat ST.
       step. step. step. step. if_true.
       assert (W : inspect_result (bv_unsigned a1) bs = 0).
       { unfold inspect_result, inspect_wf. rewrite (proj2 (Z.eqb_neq _ _) NL). reflexivity. }
       do 6 step. apply evtF_done. rewrite W. do 5 eexists. split; [reflexivity|]. split; [eassumption|].
       split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST. }
  specialize (RGOT EL). specialize (RCELL EL). specialize (RBUF EL). specialize (RSH EL).
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 12 ltac:(lia) RSH) as RS12.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 13 ltac:(lia) RSH) as RS13.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 1490 ltac:(lia) RSH) as RS90.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 1491 ltac:(lia) RSH) as RS91.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 14 ltac:(lia) RSH) as RS14.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 15 ltac:(lia) RSH) as RS15.
  clear RSH.
  destruct (HB EL) as (LEN & BA & D0 & APS1 & APS2 & CELLS & SRW & DG & DS & ADR).
  destruct CELLS as (CK & GCK & _).
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 12 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
  destruct (AB 13 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
  destruct (AB 1490 ltac:(lia)) as (APP90 & k90 & MK90 & SK90).
  destruct (AB 1491 ltac:(lia)) as (APP91 & k91 & MK91 & SK91).
  destruct (AB 14 ltac:(lia)) as (APP14 & k14 & MK14 & SK14).
  destruct (AB 15 ltac:(lia)) as (APP15 & k15 & MK15 & SK15).
  unfold off_stk, GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
  unfold ASAN_K in RS12, RS13, RS90, RS91, RS14, RS15.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APP90, APP91, APP14, APP15, APS1, APS2.
  pose proof BA as (BA0 & BA1 & _).
  rewrite LEN in BA1. change (Z.of_nat 1492) with 1492 in BA1.
  pose proof (conj BA (conj CK GCK)) as PK. clear BA CK GCK.
  carve_frame 16%nat ST.
  step. step.
  destruct PK as (BA & CK & GCK).
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  pose proof (bytes_tp m m0 _ _ 625984 (le8 (wa 658872)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 658872 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 625984) 8 = Some (le8 (wa 658872))).
  { replace (wa 625984) with (wa (625984 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 625984 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 658872) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 658872) with (wa (658872 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 658872 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  (* A shadow address lies outside the stack frame: only Ra0, Rsp, APPi, APS1 and APS2 matter. The clear keeps
     Z.div_mod_to_equations and lia off the other disjunctions and div/mod terms of the context (without it these
     six lines took 277 s of the file's 547 s). *)
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP12 APS1 APS2; Z.div_mod_to_equations; lia) MK12) as M12.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP13 APS1 APS2; Z.div_mod_to_equations; lia) MK13) as M13.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 1490) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP90 APS1 APS2; Z.div_mod_to_equations; lia) MK90) as M90.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 1491) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP91 APS1 APS2; Z.div_mod_to_equations; lia) MK91) as M91.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 14) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP14 APS1 APS2; Z.div_mod_to_equations; lia) MK14) as M14.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 15) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP15 APS1 APS2; Z.div_mod_to_equations; lia) MK15) as M15.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 1490) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 1490 BA ltac:(lia))) as F90.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 1491) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 1491 BA ltac:(lia))) as F91.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 14) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 14 BA ltac:(lia))) as F14.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 15) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 15 BA ltac:(lia))) as F15.
  change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
  change (Z.of_nat 1490) with 1490 in F90. change (Z.of_nat 1491) with 1491 in F91.
  change (Z.of_nat 14) with 14 in F14. change (Z.of_nat 15) with 15 in F15.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 1490 bs (Z_to_bv 8 0)) as b90 eqn:E90.
  remember (nth 1491 bs (Z_to_bv 8 0)) as b91 eqn:E91.
  remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
  remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 12) 8 ltac:(lia)) as MB12.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 13) 8 ltac:(lia)) as MB13.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 1490) 8 ltac:(lia)) as MB90.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 1491) 8 ltac:(lia)) as MB91.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 14) 8 ltac:(lia)) as MB14.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 15) 8 ltac:(lia)) as MB15.
  step. step. if_false.
  step. step. step.
  shadow_pass a0 m0 12 w12 g12 h12 U12 G12 H12 M12 k12 SK12 MB12 RBUF RS12 a4 x12.
  all: pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Q12; zify_cond Q12; rewrite zxb_u in Q12.
  all: try (exit0 FR ST sp).
  all: shadow_pass a0 m0 13 w13 g13 h13 U13 G13 H13 M13 k13 SK13 MB13 RBUF RS13 x12 x13.
  all: pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Q13; zify_cond Q13; rewrite zxb_u in Q13.
  all: try (exit0 FR ST sp).
  all: shadow_pass a0 m0 1490 w90 g90 h90 U90 G90 H90 M90 k90 SK90 MB90 RBUF RS90 x13 x90.
  all: pose proof (rdw0 m0 w90 _ _ F90 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Q90; zify_cond Q90; rewrite zxb_u in Q90.
  all: try (exit0 FR ST sp).
  all: shadow_pass a0 m0 1491 w91 g91 h91 U91 G91 H91 M91 k91 SK91 MB91 RBUF RS91 x90 x91.
  all: pose proof (rdw0 m0 w91 _ _ F91 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Q91; zify_cond Q91; rewrite zxb_u in Q91.
  all: try (exit0 FR ST sp).
  all: shadow_pass a0 m0 14 w14 g14 h14 U14 G14 H14 M14 k14 SK14 MB14 RBUF RS14 x91 x14.
  all: step; gen_addi a0 w15 U15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w15) 1 RBUF ltac:(lia)) as RW15.
  all: step; gen_shr w15 g15 G15.
  all: rewrite U15 in G15.
  all: step; gen_addi g15 h15 H15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h15) 1 RS15 ltac:(lia)) as RH15.
  all: pose proof (rdw0 m0 h15 _ _ M15 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw m0 a0 14 _ _ F14 ltac:(lia)) as R; step; clear R.
  all: step.
  all: sk_join a0 15 U15 k15 SK15 MB15 g15 x15.
  all: pose proof (rdw0 m0 w15 _ _ F15 ltac:(lia)) as R; step; clear R.
  all: do 9 step; apply evtF_done.
  all: assert (V : inspect_result (bv_unsigned a1) bs = 2^32 + (bv_unsigned b14 + 256 * bv_unsigned b15))
         by (unfold inspect_result, inspect_wf, inspect_counter, inspect_byte;
             rewrite EL, <- E12, <- E13, <- E90, <- E91, <- E14, <- E15, Q12, Q13, Q90, Q91; reflexivity).
  all: rewrite V; unfold zxb; rewrite !zxb_u.
  all: pose proof (byte_range b14) as X14; pose proof (byte_range b15) as X15.
  all: rewrite lor_bytes16, lor_pow32 by lia.
  all: replace (bv_unsigned b14 + 256 * bv_unsigned b15 + 4294967296)
         with (2^32 + (bv_unsigned b14 + 256 * bv_unsigned b15)) by lia.
  all: do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
  all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

(* The footprint form implies the old contract: take the footprint that allows every access. *)
Corollary reac_frame_inspect_holds_of_F : reac_frame_inspect_contract.
Proof.
  unfold reac_frame_inspect_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST HLO HB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  apply (ExecF.evtF_evt rsegs RNG_all).
  pose proof reac_frame_inspect_holds_F as H. unfold reac_frame_inspect_contract_F in H.
  apply H; [exact ST | exact HLO | exact HB | | | | |].
  - apply rng_all; unfold REAC_FRAME_INSPECT_FRAME in *; lia.
  - intros _. apply rng_all; unfold GOT_CELL_K; lia.
  - intros _. apply rng_all; unfold CELL_K; lia.
  - intros EL. destruct (HB EL) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P0 & N0 & PE & _).
    apply rng_all; unfold APPMEM_END in PE; lia.
  - intros EL. destruct (HB EL) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P0 & N0 & PE & _).
    unfold shadow_addr, ASAN_K, APPMEM_END in *. apply rng_all; Z.div_mod_to_equations; lia.
Qed.
