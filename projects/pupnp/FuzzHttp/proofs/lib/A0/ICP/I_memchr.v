(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit F_rip F_gates M_memchrZ.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition imemchr_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A c n : Z) (buf : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (memchr_res A c n buf)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ bytes_at asegs m' A buf.

Section Proofs.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (A c n lo : Z) (buf : list byte).
  Notation r := (memchr_res A c n buf).
  Notation sz := (if r =? 0 then n else r - A + 1).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo q.
  Hypothesis LO : lo <= q - 2128 - 80.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Hypothesis IE : icpt_env m.
  Hypothesis BUF : bytes_at asegs m A buf.
  Hypothesis OK : memchr_ok A c n buf.
  Hypothesis SEPS : A + Z.of_nat (length buf) <= lo \/ q <= A.
  Hypothesis WIN : cwin A sz.
  Hypothesis WIN2 : A + sz < 2^47.
  Hypothesis ACC : accessible m A sz.
  Hypothesis RDB : sh_readable m A sz.
  Hypothesis NSZ : sz <= 2^43.
  Hypothesis RC : 0 <= c < 256.
  Hypothesis RN : 0 <= n < 2^64.

  Notation APOST := (imemchr_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m).

  Definition INVX (mc : mem) : Prop :=
    (exists jk, rw_cells asegs mc (q + -2128) [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (q + -2128)
    /\ munch [(lo, q)] m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ bytes_at asegs mc A buf.
  Definition INV (mc : mem) : Prop :=
    INVX mc /\ env_shadow mc /\ env_layout mc /\ accessible mc A sz /\ sh_readable mc A sz.

  #[using="LO KLO Q64 WIN WIN2 RC RN"] Lemma BL : 0 <= A /\ 0 <= sz /\ A + sz < 2^47 /\ 0 <= lo /\ q < 2^64 /\ lo <= q - 2208 /\ 17594333495296 <= lo.
  Proof. destruct WIN as [Hn W]. lia. Qed.

  Ltac invx_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & BUF1).
  Ltac inv_open H :=
    let IX := fresh "IX" in
    destruct H as (IX & (GOT1 & SHB1) & (LG1 & LC1) & ACC1 & RDB1); invx_open IX.

  #[using="LO KLO Q64 WIN WIN2 ACC RDB RC RN"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (q + -2128) [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (q + -2128) -> munch [(lo, q)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    bytes_at asegs mc A buf -> icpt_env mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 BUF1 IE1. pose proof BL as BL0.
    assert (HO : forall s, 0x7fff7000 <= s < 0x10007fff8000 -> outside [(lo, q)] s) by (intros s Hs; cbn [outside]; lia).
    split; [split; [exists jk; exact FR|]; repeat (split; [assumption|]); assumption|].
    split; [exact (ie_shadow _ IE1)|]. split; [exact (ie_layout _ IE1)|].
    split; [eapply accessible_munch; [exact ACC| exact MU1| exact WIN| intros s Hs; apply HO; lia]|].
    eapply sh_readable_munch; [exact RDB| exact MU1| exact WIN| exact HO].
  Qed.

  #[using="LO KLO Q64 WIN WIN2 RC RN"] Lemma LX : forall mc x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INVX mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 x8 x9 (wz r) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x469ec) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. invx_open IV.
    do 10 zstep.
    release_frame FR ST1 q. finish.
  Qed.

  #[using="LO KLO Q64 WIN WIN2 RC RN"] Lemma LWL : forall mc (k : nat) (cur : Z) x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc -> 1 <= sz <= 64 ->
    Z.to_nat (sh (A + sz - 1) - cur) = k -> sh A <= cur < sh (A + sz - 1) ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 x8 x9 (wz r) (wz cur) (wz (2147450880 + Z.shiftr (A + sz + -1) 3)) (wz 0) x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x46afc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    revert cur x14 Hk Hc. induction k as [|k IH]; intros cur x14 Hk Hc; [exfalso; lia|].
    assert (SL : sh (A + sz - 1) = 2147450880 + Z.shiftr (A + sz + -1) 3) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (A + sz + -1) with (A + sz - 1) by lia; lia).
    pose proof (sh_div8 (A + sz - 1)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc A sz cur ACC1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX. exact (proj1 IV0).
  Qed.

  #[using="LO KLO Q64 WIN WIN2 RC RN"] Lemma LWS : forall mc x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc -> 1 <= sz <= 64 ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 x8 x9 (wz r) (wz (2147450880 + Z.shiftr A 3)) (wz (2147450880 + Z.shiftr (A + sz + -1) 3)) (wz (A + sz + -1)) x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x46ae0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    destruct (acc_byte_rd mc A sz (A + sz + -1) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((A + sz + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (A + sz + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX. exact (proj1 IV0).
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      rewrite !shiftr3_div in *. replace (A + sz - 1) with (A + sz + -1) by lia. unfold sh, SHADOW_OFF.
      assert (0 <= A / 8 < 2^44 /\ 0 <= (A + sz + -1) / 8 < 2^44) as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite !Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="LO KLO Q64 SEPS WIN WIN2 NSZ RC RN"] Lemma LB : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
    INV mc ->
    evt asegs APOST
      (MS (mkR x1 (wz (q + -2128)) gp tp x5 x6 x7 (wz q) (wz sz) (wz r) x11 x12 x13 x14 x15 x16 x17
               (wz A) x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x469a4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof BL as BL0. pose proof IV as IV0. inv_open IV.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact (proj1 IV0). }
      assert (N65 : 64 < sz) by (clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      do 4 zstep.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WIN as [_ W]; unfold rwin; lia | exact ACC1 | lia |].
      do 3 zstep. lit_branch.
      eapply LX. unfold INVX. split; [eexists; eassumption|]. repeat (split; [eassumption|]). assumption.
    -
      assert (N1 : 1 <= sz <= 64) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg 14%Z RDB1 A w1 P1. probe8_reg 15%Z RDB1 (A + sz + -1) w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; eassumption.
      + eapply LX; exact (proj1 IV0).
  Qed.

  #[using="q m lo LO Q64 BUF RC RN"] Lemma r_range : r = 0 \/ (A <= r < A + n /\ r < 2^64).
  Proof.
    unfold memchr_res. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [right| left; reflexivity].
    destruct (find_byte_Some _ _ _ E) as (Hi & _). rewrite firstn_length in Hi.
    pose proof (bytes_at_bound _ _ _ _ BUF) as AB. lia.
  Qed.

  #[using="MI ST LO KLO Q64 IE BUF OK SEPS WIN WIN2 ACC RDB NSZ RC RN"] Lemma imemchr_body : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, a0 = wz A -> a1 = wz c -> a2 = wz n ->
    evt asegs APOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A0_memchr) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros -> -> ->. unfold A0_memchr. pose proof BL as BL0.
    pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO' : lo <= q - 2128) by lia.
    pose proof ST as ST0. ihide BUF.
    carve_frame 2128%nat ST0.
    zstep. do 10 zstep. do 4 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (icpt_env_stack lo q m m1 IE MU WM ltac:(lia)) as IE1;
      assert (BUF1 : bytes_at asegs m1 A buf)
        by (iunhide BUF; eapply bytes_at_transport; [exact BUF| exact MU| cbn [disjoint_from]; lia])
    end.
    call inited_spec; [assumption | exact (ie_inited _ IE1) |].
    zstep. lit_branch. zstep.
    call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ IE1) |].
    clear IE1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
        pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
    pose proof (ie_real_str _ IE1) as (_ & RS1 & _).
    do 7 zstep.
    call memchr_specZ; [ exact BUF1 | exact OK | assumption | lia | lia | lia |].
    zstep. lit_branch.
    clear IE1 RS1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU' : munch [(lo, q)] m m1, WM' : wmono asegs m m1 |- _ =>
        pose proof (icpt_env_stack lo q m m1 IE MU' WM' ltac:(lia)) as IE1 end end.
    pose proof r_range as RR.
    zstep. if_cases KR; zify_cond KR.
    -
      assert (ESZ : sz = r - A + 1) by (destruct (Z.eqb_spec r 0); [exfalso; lia| reflexivity]).
      do 3 zstep. rewrite zb_lxor_ones by lia. do 3 zstep. if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
      replace (Z_to_bv 64 (r - A + 1)) with (Z_to_bv 64 sz) by (rewrite ESZ; reflexivity).
      eapply LB.
      match goal with P : stk asegs _ lo (q + -2128) |- _ => eapply inv_of; [ eassumption | exact P | eassumption | eassumption | eassumption | eassumption | exact IE1 ] end.
    -
      assert (ESZ : sz = n) by (destruct (Z.eqb_spec r 0); [reflexivity| exfalso; lia]).
      zstep. rewrite zb_lxor_ones by lia. do 3 zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      replace (Z_to_bv 64 n) with (Z_to_bv 64 sz) by (rewrite ESZ; reflexivity).
      eapply LB.
      match goal with P : stk asegs _ lo (q + -2128) |- _ => eapply inv_of; [ eassumption | exact P | eassumption | eassumption | eassumption | eassumption | exact IE1 ] end.
  Qed.
End Proofs.

Lemma memchr_i_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A c n : Z) (buf : list byte) (lo : Z),
  bytes_at asegs m A buf -> memchr_ok A c n buf ->
  accessible m A (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) ->
  sh_readable m A (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) ->
  icpt_env m -> cwin A (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) ->
  A + (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) < 2^47 ->
  (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) <= 2^43 ->
  stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - 2208 -> q < 2^64 ->
  (A + Z.of_nat (length buf) <= lo \/ q <= A) ->
  mem_inv asegs m -> a0 = wz A -> a1 = wz c -> a2 = wz n -> 0 <= c < 256 -> 0 <= n < 2^64 ->
  evt asegs (imemchr_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_memchr) fc None m (seg_rom asegs)).
Proof. cbv zeta. intros. eapply imemchr_body; try eassumption. lia. Qed.
