(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes AKit AKit2 ARep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import APoisonR_iface F_rsrvshadow RT_stubs.
Import Exc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition flush_entry := 0x5e120.
End CANSEC1.
Abbreviation FLUSH_STACK := 64.

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma mem_to_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p : Z),
  mem_inv asegs m -> poison_cells m ->
  (0 <= p /\ p + 1 <= 0x7fff8000 \/ 0x10007fff8000 <= p) -> p <= 0x7fffffffffff ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a1' a2' a3' a4' a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (shad p)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e16c) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros MI PC PLO PHI RA RIMG.
  destruct PC as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  do 3 step.
  do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.
  2: do 6 step.
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].
  2: do 3 step; do 2 zstep.
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].
  2: step; if_cases K5; zify_cond K5; [exfalso; lia|].
  all: do 2 zstep.
  all: change (2147450880 + Z.shiftr p 3) with (shad p).
  all: step.
  all: apply evtF_done; do 8 eexists; reflexivity.
Qed.

Definition flush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma adec_madvise_Some : forall addr len rsp a, adec_madvise addr len rsp = Some a ->
  a = 0 /\ exists ci, rsp = mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 len)] [] [] ci.
Proof.
  intros addr len [r ws zs us cs ci] a H. unfold adec_madvise in H.
  destruct ws; [| discriminate]. destruct zs as [| [a0 n0] [| ? ?]]; try discriminate. destruct us; [| discriminate]. destruct cs; [| discriminate].
  destruct (bv_unsigned r =? 0) eqn:E1; [| discriminate]. destruct (bv_unsigned a0 =? addr) eqn:E2; [| discriminate].
  destruct (bv_unsigned n0 =? len) eqn:E3; [| discriminate]. cbn in H. injection H as <-. split; [reflexivity|]. exists ci.
  apply Z.eqb_eq in E1, E2, E3. rewrite <- (Z_to_bv_bv_unsigned r), <- (Z_to_bv_bv_unsigned a0), <- (Z_to_bv_bv_unsigned n0), E1, E2, E3. reflexivity.
Qed.

Section STUB.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).
Lemma rt_madvise_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len : Z) (x13 x14 x15 x17 : word),
  rw_cells asegs m 0xd1558 [C8 (Z_to_bv 64 1)] -> rng RNG 0xd1558 8 ->
  @implF node asegs (at_nodeA asegs) fst _ RNG (enode (NMadvise addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMadvise addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (eff_ret rsp)))) (Z_to_bv 64 len) (Z_to_bv 64 4) (Z_to_bv 64 4) x14 x15 (Z_to_bv 64 233))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 4) x13 x14 x15 x17)
        F (Z_to_bv 64 0x70888) fc None m (seg_rom asegs)).
Proof.
  intros fst RNG X dec addr len x13 x14 x15 x17 SEALED RS. unfold rt_regs. apply implF_enode.
  step. step. step. if_lit.
  step. step. if_lit.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step. rewrite Z.add_0_r. step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.
End STUB.

Lemma outside_miss : forall (W : list (Z * Z)) A N x, Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= x < A + N -> outside W x.
Proof.
  induction W as [|[l h] W IH]; intros A N x HW Hx; cbn [outside]; [exact I|].
  inversion HW as [|? ? H1 H2]; subst. cbn [fst snd] in H1. split; [lia| eapply IH; eassumption].
Qed.
Lemma rw_zeros_survive : forall (m m' : amem) A N lo hi (W : list (Z * Z)),
  rw_cells asegs m A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))] ->
  munch ((lo, hi) :: W) m m' -> wmono asegs m m' ->
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W ->
  (lo < hi -> rw_cells asegs m' lo [CB (Z.to_nat (hi - lo)) (repeat (Z_to_bv 8 0) (Z.to_nat (hi - lo)))]) ->
  0 <= N ->
  rw_cells asegs m' A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))].
Proof.
  intros m m' A N lo hi W [[Hwf Hb] Hw] MU WM HW ZN N0. split; [split; [exact Hwf|]|].
  - destruct Hb as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    pose proof (H i Hi) as Hi0. pose proof H1 as H1'. cbn [cells_bytes cbytes] in Hi, Hi0, H1' |- *.
    rewrite app_nil_r in Hi, Hi0, H1' |- *. rewrite repeat_length in Hi, H1'.
    destruct (Z_lt_dec (A + Z.of_nat i) lo) as [L|L]; [| destruct (Z_le_dec hi (A + Z.of_nat i)) as [G|G]].
    + unfold mrd in *. rewrite (MU (wa (A + Z.of_nat i))); [exact Hi0|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia|]. eapply outside_miss; [exact HW| lia].
    + unfold mrd in *. rewrite (MU (wa (A + Z.of_nat i))); [exact Hi0|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia|]. eapply outside_miss; [exact HW| lia].
    + destruct (ZN ltac:(lia)) as [[_ (Z0 & Z1 & ZB)] _]. cbn [cells_bytes cbytes] in Z1, ZB. rewrite app_nil_r in Z1, ZB. rewrite repeat_length in Z1, ZB.
      pose proof (ZB (Z.to_nat (A + Z.of_nat i - lo)) ltac:(lia)) as ZBi.
      replace (lo + Z.of_nat (Z.to_nat (A + Z.of_nat i - lo))) with (A + Z.of_nat i) in ZBi by lia.
      rewrite ZBi. rewrite nth_error_repeat by lia. symmetry. apply nth_error_repeat. exact Hi.
  - destruct Hw as (W0 & W1 & Hw). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM, Hw, Hi.
Qed.

Lemma rw_zeros_absorb : forall (m : amem) a n A N,
  0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 ->
  rw_cells asegs m A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))] ->
  rw_cells asegs (apply_zeros m [(wa a, Z_to_bv 64 n)]) A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))].
Proof.
  intros m a n A N Ha Hn Han [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - destruct Hb as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    pose proof (H i Hi) as Hi0. cbn [cells_bytes cbytes] in Hi, Hi0 |- *. rewrite app_nil_r in Hi, Hi0 |- *.
    rewrite repeat_length in Hi. pose proof H1 as H1'. cbn [cells_bytes cbytes] in H1'. rewrite app_nil_r, repeat_length in H1'.
    destruct (Z_lt_dec (A + Z.of_nat i) a) as [L|L]; [| destruct (Z_le_dec (a + n) (A + Z.of_nat i)) as [G|G]].
    + unfold mrd in *. rewrite (zeros_outside m a n Ha Hn Han) by (rewrite wa_unsigned by lia; lia). exact Hi0.
    + unfold mrd in *. rewrite (zeros_outside m a n Ha Hn Han) by (rewrite wa_unsigned by lia; lia). exact Hi0.
    + unfold mrd. rewrite (zeros_inside m a n Ha Hn Han) by (rewrite wa_unsigned by lia; lia).
      symmetry. apply nth_error_repeat. exact Hi.
  - apply (wr_at_zeros asegs m a n Ha Hn Han). exact Hw.
Qed.

Definition fl_beg (mb : Z) : Z := Z.land ((shad mb + 4095) mod 18446744073709551616) 18446744073709547520.
Definition fl_end (mb ms : Z) : Z := Z.land (shad (mb + ms) mod 18446744073709551616) 18446744073709547520.

Lemma flush_mad_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  fl_beg mb < fl_end mb ms ->
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMadvise (fl_beg mb) (fl_end mb ms - fl_beg mb)) rsp RNG RNG' ->
      munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp); (fl_beg mb, fl_end mb ms)]%Z m m' -> wmono asegs m m' ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
      rw_cells asegs m' (fl_beg mb) [CB (Z.to_nat (fl_end mb ms - fl_beg mb)) (repeat (Z_to_bv 8 0) (Z.to_nat (fl_end mb ms - fl_beg mb)))] ->
      implS asegs RNG' (K 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMadvise (fl_beg mb) (fl_end mb ms - fl_beg mb)) (adec_madvise (fl_beg mb) (fl_end mb ms - fl_beg mb))) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 flush_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI PC PRM RR -> -> MLO MPOS MCE RA RIMG RSTK PAGE KONT.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => a = 0 /\ exists rsp m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fstepS (NMadvise (fl_beg mb) (fl_end mb ms - fl_beg mb)) rsp RNG RNG'
               /\ munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp); (fl_beg mb, fl_end mb ms)]%Z m m' /\ wmono asegs m m'
               /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
               /\ rw_cells asegs m' (fl_beg mb) [CB (Z.to_nat (fl_end mb ms - fl_beg mb)) (repeat (Z_to_bv 8 0) (Z.to_nat (fl_end mb ms - fl_beg mb)))]
               /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' (-> & PO). destruct_exs PO. destruct PO as (HF & MU' & WM' & MI' & ST' & ZF' & ->).
       eapply KONT; [exact HF | exact MU' | exact WM' | exact MI' | exact ST' | exact ZF']. }

  assert (FB : AIMG_HI <= fl_beg mb /\ fl_end mb ms <= 0x10007fff8000 /\ 0 <= fl_beg mb /\ fl_end mb ms < 2^64).
  { unfold fl_beg, fl_end. pose proof atop_range as ATR0. unfold ablk, AIMG_HI, KLS in MLO.
    assert (S1 : 0 <= shad mb + 4095 < 2^64) by (rewrite shad_div; unfold ASHOFF; clear -MLO MPOS MCE ATR0; Z.div_mod_to_equations; lia).
    assert (S2 : 0 <= shad (mb + ms) < 2^64) by (rewrite shad_div; unfold ASHOFF; clear -MLO MPOS MCE ATR0; Z.div_mod_to_equations; lia).
    change 18446744073709551616 with (2^64). rewrite (Z.mod_small _ _ S1), (Z.mod_small _ _ S2), (land_m4096 _ S1), (land_m4096 _ S2).
    rewrite !shad_div in *. unfold ASHOFF, AIMG_HI in *. clear -MLO MPOS MCE ATR0 S1 S2. Z.div_mod_to_equations. lia. }
  destruct FB as (FB1 & FB2 & FB3 & FB4).
  iprefix.

    unfold flush_entry in *. word_range sp SPR. unfold ablk, AIMG_HI, KLS in MLO. pose proof atop_range as ATR.
  pose proof PRM as PRM0. destruct PRM0 as (GPG & PGSZ & MLIM & F216 & F240 & CAN & LPG).
  pose proof (munch_refl [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp); (fl_beg mb, fl_end mb ms)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.

  assert (SEAL : rw_cells asegs m 0xd1558 [C8 (Z_to_bv 64 1)]).
  { eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xd1558 (le8 (Z_to_bv 64 1)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  carve_frame 32%nat ST.
  do 5 step.
  step. step.
  step.
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_cons; [cbn [fst]; exact FB1 | apply Forall_nil]]]. }
  cbv beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & ->).
  replace (ret_pc (Z_to_bv 64 385344)) with (Z_to_bv 64 385344 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. zstep.
  setreg 10 (Z_to_bv 64 (mb + ms)) ltac:(f_equal; clear; lia).
  step.
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_cons; [cbn [fst]; exact FB1 | apply Forall_nil]]]. }
  cbv beta. intros ms' (b1' & b2' & b3' & b4' & b5' & b6' & b7' & u0' & ->).
  replace (ret_pc (Z_to_bv 64 385356)) with (Z_to_bv 64 385356 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. step.
  do 5 step.
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.
  carve_frame 32%nat ST.
  do 5 step.
  step. step. step. step.
  step. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep. zstep.
  step. if_cases KR; zify_cond KR.
  { exfalso. unfold fl_beg, fl_end in PAGE. clear -KR PAGE. lia. }
  zstep. step.
  do 5 step.
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.

  assert (RO0 : forall x : word, (fl_beg mb <= bv_unsigned x < fl_beg mb + (fl_end mb ms - fl_beg mb))%Z -> ro_addr asegs x = false).
  { intros x Hx. apply ref_ro_addr_false. right. unfold AIMG_HI in FB1. clear -Hx FB1. lia. }
  icallk rt_madvise_stubP.
  1: exact SEAL.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_madvise_Some _ _ _ _ Hdec) as (-> & ci & ->).
  cbn [eff_ret]. rewrite eff_mem_zeros. unfold rt_regs.
  sys_mem_zeros.
  apply evtF_done. split; [reflexivity|].
  eexists (_ : resp). do 16 eexists. split; [exact HF|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| reflexivity].
Qed.

Lemma flush_none_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  fl_end mb ms <= fl_beg mb ->
  evtF asegs RNG (flush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 flush_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI PC PRM RR -> -> MLO MPOS MCE RA RIMG RSTK NOPAGE.
  unfold flush_entry in *. word_range sp SPR. unfold ablk, AIMG_HI, KLS in MLO. pose proof atop_range as ATR.
  pose proof PRM as PRM0. destruct PRM0 as (GPG & PGSZ & MLIM & F216 & F240 & CAN & LPG).
  pose proof (munch_refl [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.

  assert (SEAL : rw_cells asegs m 0xd1558 [C8 (Z_to_bv 64 1)]).
  { eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xd1558 (le8 (Z_to_bv 64 1)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  carve_frame 32%nat ST.
  do 5 step.
  step. step.
  step.
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & ->).
  replace (ret_pc (Z_to_bv 64 385344)) with (Z_to_bv 64 385344 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. zstep.
  setreg 10 (Z_to_bv 64 (mb + ms)) ltac:(f_equal; clear; lia).
  step.
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (b1' & b2' & b3' & b4' & b5' & b6' & b7' & u0' & ->).
  replace (ret_pc (Z_to_bv 64 385356)) with (Z_to_bv 64 385356 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. step.
  do 5 step.
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.
  carve_frame 32%nat ST.
  do 5 step.
  step. step. step. step.
  step. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep. zstep.
  step. if_cases KR; zify_cond KR.
  -
    do 5 step.
    lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
      lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
    step.
    apply evtF_done. unfold flush_post. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
  - exfalso. unfold fl_beg, fl_end in NOPAGE. clear -KR NOPAGE. lia.
Qed.

Lemma flush_beg_fl : forall mb, 0 <= mb < 2^62 -> flush_beg mb = fl_beg mb.
Proof.
  intros mb H. unfold flush_beg, fl_beg, shad, ASHOFF, SHADOW_OFF, rup, PG.
  set (X := 0x7fff8000 + Z.shiftr mb 3).
  assert (S1 : 0 <= X + 4095 < 2^64) by (unfold X; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  change 18446744073709551616 with (2^64). rewrite (Z.mod_small _ _ S1), (land_m4096 _ S1).
  replace (X + 4096 - 1) with (X + 4095) by lia.
  pose proof (Z.div_mod (X + 4095) 4096 ltac:(lia)). lia.
Qed.
Lemma flush_end_fl : forall mb ms, 0 <= mb + ms < 2^62 -> flush_end mb ms = fl_end mb ms.
Proof.
  intros mb ms H. unfold flush_end, fl_end, shad, ASHOFF, SHADOW_OFF, rdn, PG.
  set (X := 0x7fff8000 + Z.shiftr (mb + ms) 3).
  assert (S2 : 0 <= X < 2^64) by (unfold X; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  change 18446744073709551616 with (2^64). rewrite (Z.mod_small _ _ S2), (land_m4096 _ S2).
  pose proof (Z.div_mod X 4096 ltac:(lia)). lia.
Qed.

Lemma flush_shadow_spec : forall RNG {R} (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp); (fl_beg mb, fl_end mb ms)]%Z m m' -> wmono asegs m m' ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
      (fl_beg mb < fl_end mb ms -> rw_cells asegs m' (fl_beg mb) [CB (Z.to_nat (fl_end mb ms - fl_beg mb)) (repeat (Z_to_bv 8 0) (Z.to_nat (fl_end mb ms - fl_beg mb)))]) ->
      implS asegs RNG (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (flush_shadow mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 flush_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI PC PRM RR A0 A1 MLO MPOS MCE RA RIMG RSTK KONT.
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). pose proof atop_range as ATR.
  unfold flush_shadow. cbv zeta.
  rewrite (flush_beg_fl mb) by (clear -ML2 ML4 MPOS; lia). rewrite (flush_end_fl mb ms) by (clear -ML2 ML4 MPOS; lia).
  destruct (Z.ltb_spec (fl_beg mb) (fl_end mb ms)) as [PAGE|NOPAGE].
  - rewrite aembed_vis. cbn [aev_tree].
    eapply (flush_mad_spec RNG (fun z => aembed ATOP (if z =? 0 then k else aundef_ UBadAnswer k)) Q) with (mb := mb) (ms := ms) (lo := lo);
      try eassumption.
    intros rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU WM MI' ST' ZF'.
    destruct HF as [HA _]. cbn in HA. subst RNG'.
    cbv beta. change (0 =? 0) with true. cbv iota.
    eapply KONT; [exact MU | exact WM | exact MI' | exact ST' | intros _; exact ZF'].
  - iprefix.
    eapply evtF_cut.
    { eapply (flush_none_spec RNG) with (mb := mb) (ms := ms) (lo := lo); try eassumption. }
    cbv beta. intros ms' PO. unfold flush_post in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & ST').
    apply evtF_done. eapply KONT; [| exact WM | exact MI' | exact ST' | intros C; exfalso; clear -C NOPAGE; lia].
    eapply munch_weaken; [| exact MU]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia.
Qed.

End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import APoisonR_iface.TwinB F_rsrvshadow.TwinB RT_stubs.TwinB.
Import Exc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition flush_entry := 0x5eab0.
End CANSEC1.
Abbreviation FLUSH_STACK := 64.

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma mem_to_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p : Z),
  mem_inv bsegs m -> poison_cells m ->
  (0 <= p /\ p + 1 <= 0x7fff8000 \/ 0x10007fff8000 <= p) -> p <= 0x7fffffffffff ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a1' a2' a3' a4' a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (shad p)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5eafc) fc None m (seg_rom bsegs)).
Proof.
  intros until p. intros MI PC PLO PHI RA RIMG.
  destruct PC as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  do 3 step.
  do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.
  2: do 6 step.
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].
  2: do 3 step; do 2 zstep.
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].
  2: step; if_cases K5; zify_cond K5; [exfalso; lia|].
  all: do 2 zstep.
  all: change (2147450880 + Z.shiftr p 3) with (shad p).
  all: step.
  all: apply evtF_done; do 8 eexists; reflexivity.
Qed.

Definition flush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma adec_madvise_Some : forall addr len rsp a, adec_madvise addr len rsp = Some a ->
  a = 0 /\ exists ci, rsp = mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 len)] [] [] ci.
Proof.
  intros addr len [r ws zs us cs ci] a H. unfold adec_madvise in H.
  destruct ws; [| discriminate]. destruct zs as [| [a0 n0] [| ? ?]]; try discriminate. destruct us; [| discriminate]. destruct cs; [| discriminate].
  destruct (bv_unsigned r =? 0) eqn:E1; [| discriminate]. destruct (bv_unsigned a0 =? addr) eqn:E2; [| discriminate].
  destruct (bv_unsigned n0 =? len) eqn:E3; [| discriminate]. cbn in H. injection H as <-. split; [reflexivity|]. exists ci.
  apply Z.eqb_eq in E1, E2, E3. rewrite <- (Z_to_bv_bv_unsigned r), <- (Z_to_bv_bv_unsigned a0), <- (Z_to_bv_bv_unsigned n0), E1, E2, E3. reflexivity.
Qed.

Section STUB.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).
Lemma rt_madvise_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len : Z) (x13 x14 x15 x17 : word),
  rw_cells bsegs m 0xd3670 [C8 (Z_to_bv 64 1)] -> rng RNG 0xd3670 8 ->
  @implF node bsegs (at_nodeA bsegs) fst _ RNG (enode (NMadvise addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMadvise addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (eff_ret rsp)))) (Z_to_bv 64 len) (Z_to_bv 64 4) (Z_to_bv 64 4) x14 x15 (Z_to_bv 64 233))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom bsegs)))
    (MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 4) x13 x14 x15 x17)
        F (Z_to_bv 64 0x71218) fc None m (seg_rom bsegs)).
Proof.
  intros fst RNG X dec addr len x13 x14 x15 x17 SEALED RS. unfold rt_regs. apply implF_enode.
  step. step. step. if_lit.
  step. step. if_lit.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step. rewrite Z.add_0_r. step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.
End STUB.

Lemma outside_miss : forall (W : list (Z * Z)) A N x, Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= x < A + N -> outside W x.
Proof.
  induction W as [|[l h] W IH]; intros A N x HW Hx; cbn [outside]; [exact I|].
  inversion HW as [|? ? H1 H2]; subst. cbn [fst snd] in H1. split; [lia| eapply IH; eassumption].
Qed.
Lemma rw_zeros_survive : forall (m m' : amem) A N lo hi (W : list (Z * Z)),
  rw_cells bsegs m A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))] ->
  munch ((lo, hi) :: W) m m' -> wmono bsegs m m' ->
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W ->
  (lo < hi -> rw_cells bsegs m' lo [CB (Z.to_nat (hi - lo)) (repeat (Z_to_bv 8 0) (Z.to_nat (hi - lo)))]) ->
  0 <= N ->
  rw_cells bsegs m' A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))].
Proof.
  intros m m' A N lo hi W [[Hwf Hb] Hw] MU WM HW ZN N0. split; [split; [exact Hwf|]|].
  - destruct Hb as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    pose proof (H i Hi) as Hi0. pose proof H1 as H1'. cbn [cells_bytes cbytes] in Hi, Hi0, H1' |- *.
    rewrite app_nil_r in Hi, Hi0, H1' |- *. rewrite repeat_length in Hi, H1'.
    destruct (Z_lt_dec (A + Z.of_nat i) lo) as [L|L]; [| destruct (Z_le_dec hi (A + Z.of_nat i)) as [G|G]].
    + unfold mrd in *. rewrite (MU (wa (A + Z.of_nat i))); [exact Hi0|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia|]. eapply outside_miss; [exact HW| lia].
    + unfold mrd in *. rewrite (MU (wa (A + Z.of_nat i))); [exact Hi0|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia|]. eapply outside_miss; [exact HW| lia].
    + destruct (ZN ltac:(lia)) as [[_ (Z0 & Z1 & ZB)] _]. cbn [cells_bytes cbytes] in Z1, ZB. rewrite app_nil_r in Z1, ZB. rewrite repeat_length in Z1, ZB.
      pose proof (ZB (Z.to_nat (A + Z.of_nat i - lo)) ltac:(lia)) as ZBi.
      replace (lo + Z.of_nat (Z.to_nat (A + Z.of_nat i - lo))) with (A + Z.of_nat i) in ZBi by lia.
      rewrite ZBi. rewrite nth_error_repeat by lia. symmetry. apply nth_error_repeat. exact Hi.
  - destruct Hw as (W0 & W1 & Hw). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM, Hw, Hi.
Qed.

Lemma rw_zeros_absorb : forall (m : amem) a n A N,
  0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 ->
  rw_cells bsegs m A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))] ->
  rw_cells bsegs (apply_zeros m [(wa a, Z_to_bv 64 n)]) A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))].
Proof.
  intros m a n A N Ha Hn Han [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - destruct Hb as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    pose proof (H i Hi) as Hi0. cbn [cells_bytes cbytes] in Hi, Hi0 |- *. rewrite app_nil_r in Hi, Hi0 |- *.
    rewrite repeat_length in Hi. pose proof H1 as H1'. cbn [cells_bytes cbytes] in H1'. rewrite app_nil_r, repeat_length in H1'.
    destruct (Z_lt_dec (A + Z.of_nat i) a) as [L|L]; [| destruct (Z_le_dec (a + n) (A + Z.of_nat i)) as [G|G]].
    + unfold mrd in *. rewrite (zeros_outside m a n Ha Hn Han) by (rewrite wa_unsigned by lia; lia). exact Hi0.
    + unfold mrd in *. rewrite (zeros_outside m a n Ha Hn Han) by (rewrite wa_unsigned by lia; lia). exact Hi0.
    + unfold mrd. rewrite (zeros_inside m a n Ha Hn Han) by (rewrite wa_unsigned by lia; lia).
      symmetry. apply nth_error_repeat. exact Hi.
  - apply (wr_at_zeros bsegs m a n Ha Hn Han). exact Hw.
Qed.

Definition fl_beg (mb : Z) : Z := Z.land ((shad mb + 4095) mod 18446744073709551616) 18446744073709547520.
Definition fl_end (mb ms : Z) : Z := Z.land (shad (mb + ms) mod 18446744073709551616) 18446744073709547520.

Lemma flush_mad_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  fl_beg mb < fl_end mb ms ->
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMadvise (fl_beg mb) (fl_end mb ms - fl_beg mb)) rsp RNG RNG' ->
      munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp); (fl_beg mb, fl_end mb ms)]%Z m m' -> wmono bsegs m m' ->
      mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) ->
      rw_cells bsegs m' (fl_beg mb) [CB (Z.to_nat (fl_end mb ms - fl_beg mb)) (repeat (Z_to_bv 8 0) (Z.to_nat (fl_end mb ms - fl_beg mb)))] ->
      implS bsegs RNG' (K 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMadvise (fl_beg mb) (fl_end mb ms - fl_beg mb)) (adec_madvise (fl_beg mb) (fl_end mb ms - fl_beg mb))) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 flush_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI PC PRM RR -> -> MLO MPOS MCE RA RIMG RSTK PAGE KONT.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => a = 0 /\ exists rsp m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fstepS (NMadvise (fl_beg mb) (fl_end mb ms - fl_beg mb)) rsp RNG RNG'
               /\ munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp); (fl_beg mb, fl_end mb ms)]%Z m m' /\ wmono bsegs m m'
               /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
               /\ rw_cells bsegs m' (fl_beg mb) [CB (Z.to_nat (fl_end mb ms - fl_beg mb)) (repeat (Z_to_bv 8 0) (Z.to_nat (fl_end mb ms - fl_beg mb)))]
               /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' (-> & PO). destruct_exs PO. destruct PO as (HF & MU' & WM' & MI' & ST' & ZF' & ->).
       eapply KONT; [exact HF | exact MU' | exact WM' | exact MI' | exact ST' | exact ZF']. }

  assert (FB : AIMG_HI <= fl_beg mb /\ fl_end mb ms <= 0x10007fff8000 /\ 0 <= fl_beg mb /\ fl_end mb ms < 2^64).
  { unfold fl_beg, fl_end. pose proof atop_range as ATR0. unfold ablk, AIMG_HI, KLS in MLO.
    assert (S1 : 0 <= shad mb + 4095 < 2^64) by (rewrite shad_div; unfold ASHOFF; clear -MLO MPOS MCE ATR0; Z.div_mod_to_equations; lia).
    assert (S2 : 0 <= shad (mb + ms) < 2^64) by (rewrite shad_div; unfold ASHOFF; clear -MLO MPOS MCE ATR0; Z.div_mod_to_equations; lia).
    change 18446744073709551616 with (2^64). rewrite (Z.mod_small _ _ S1), (Z.mod_small _ _ S2), (land_m4096 _ S1), (land_m4096 _ S2).
    rewrite !shad_div in *. unfold ASHOFF, AIMG_HI in *. clear -MLO MPOS MCE ATR0 S1 S2. Z.div_mod_to_equations. lia. }
  destruct FB as (FB1 & FB2 & FB3 & FB4).
  iprefix.

    unfold flush_entry in *. word_range sp SPR. unfold ablk, AIMG_HI, KLS in MLO. pose proof atop_range as ATR.
  pose proof PRM as PRM0. destruct PRM0 as (GPG & PGSZ & MLIM & F216 & F240 & CAN & LPG).
  pose proof (munch_refl [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp); (fl_beg mb, fl_end mb ms)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  assert (SEAL : rw_cells bsegs m 0xd3670 [C8 (Z_to_bv 64 1)]).
  { eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xd3670 (le8 (Z_to_bv 64 1)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  carve_frame 32%nat ST.
  do 5 step.
  step. step.
  step.
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_cons; [cbn [fst]; exact FB1 | apply Forall_nil]]]. }
  cbv beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & ->).
  replace (ret_pc (Z_to_bv 64 387792)) with (Z_to_bv 64 387792 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. zstep.
  setreg 10 (Z_to_bv 64 (mb + ms)) ltac:(f_equal; clear; lia).
  step.
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_cons; [cbn [fst]; exact FB1 | apply Forall_nil]]]. }
  cbv beta. intros ms' (b1' & b2' & b3' & b4' & b5' & b6' & b7' & u0' & ->).
  replace (ret_pc (Z_to_bv 64 387804)) with (Z_to_bv 64 387804 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. step.
  do 5 step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.
  carve_frame 32%nat ST.
  do 5 step.
  step. step. step. step.
  step. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep. zstep.
  step. if_cases KR; zify_cond KR.
  { exfalso. unfold fl_beg, fl_end in PAGE. clear -KR PAGE. lia. }
  zstep. step.
  do 5 step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.

  assert (RO0 : forall x : word, (fl_beg mb <= bv_unsigned x < fl_beg mb + (fl_end mb ms - fl_beg mb))%Z -> ro_addr bsegs x = false).
  { intros x Hx. apply ref_ro_addr_false. right. unfold AIMG_HI in FB1. clear -Hx FB1. lia. }
  icallk rt_madvise_stubP.
  1: exact SEAL.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_madvise_Some _ _ _ _ Hdec) as (-> & ci & ->).
  cbn [eff_ret]. rewrite eff_mem_zeros. unfold rt_regs.
  sys_mem_zeros.
  apply evtF_done. split; [reflexivity|].
  eexists (_ : resp). do 16 eexists. split; [exact HF|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| reflexivity].
Qed.

Lemma flush_none_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  fl_end mb ms <= fl_beg mb ->
  evtF bsegs RNG (flush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 flush_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI PC PRM RR -> -> MLO MPOS MCE RA RIMG RSTK NOPAGE.
  unfold flush_entry in *. word_range sp SPR. unfold ablk, AIMG_HI, KLS in MLO. pose proof atop_range as ATR.
  pose proof PRM as PRM0. destruct PRM0 as (GPG & PGSZ & MLIM & F216 & F240 & CAN & LPG).
  pose proof (munch_refl [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  assert (SEAL : rw_cells bsegs m 0xd3670 [C8 (Z_to_bv 64 1)]).
  { eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xd3670 (le8 (Z_to_bv 64 1)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  carve_frame 32%nat ST.
  do 5 step.
  step. step.
  step.
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & ->).
  replace (ret_pc (Z_to_bv 64 387792)) with (Z_to_bv 64 387792 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. zstep.
  setreg 10 (Z_to_bv 64 (mb + ms)) ltac:(f_equal; clear; lia).
  step.
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (b1' & b2' & b3' & b4' & b5' & b6' & b7' & u0' & ->).
  replace (ret_pc (Z_to_bv 64 387804)) with (Z_to_bv 64 387804 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. step.
  do 5 step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.
  carve_frame 32%nat ST.
  do 5 step.
  step. step. step. step.
  step. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep. zstep.
  step. if_cases KR; zify_cond KR.
  -
    do 5 step.
    lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -32) _ |- _ =>
      lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
    step.
    apply evtF_done. unfold flush_post. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
  - exfalso. unfold fl_beg, fl_end in NOPAGE. clear -KR NOPAGE. lia.
Qed.

Lemma flush_beg_fl : forall mb, 0 <= mb < 2^62 -> flush_beg mb = fl_beg mb.
Proof.
  intros mb H. unfold flush_beg, fl_beg, shad, ASHOFF, SHADOW_OFF, rup, PG.
  set (X := 0x7fff8000 + Z.shiftr mb 3).
  assert (S1 : 0 <= X + 4095 < 2^64) by (unfold X; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  change 18446744073709551616 with (2^64). rewrite (Z.mod_small _ _ S1), (land_m4096 _ S1).
  replace (X + 4096 - 1) with (X + 4095) by lia.
  pose proof (Z.div_mod (X + 4095) 4096 ltac:(lia)). lia.
Qed.
Lemma flush_end_fl : forall mb ms, 0 <= mb + ms < 2^62 -> flush_end mb ms = fl_end mb ms.
Proof.
  intros mb ms H. unfold flush_end, fl_end, shad, ASHOFF, SHADOW_OFF, rdn, PG.
  set (X := 0x7fff8000 + Z.shiftr (mb + ms) 3).
  assert (S2 : 0 <= X < 2^64) by (unfold X; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  change 18446744073709551616 with (2^64). rewrite (Z.mod_small _ _ S2), (land_m4096 _ S2).
  pose proof (Z.div_mod X 4096 ltac:(lia)). lia.
Qed.

Lemma flush_shadow_spec : forall RNG {R} (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp); (fl_beg mb, fl_end mb ms)]%Z m m' -> wmono bsegs m m' ->
      mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) ->
      (fl_beg mb < fl_end mb ms -> rw_cells bsegs m' (fl_beg mb) [CB (Z.to_nat (fl_end mb ms - fl_beg mb)) (repeat (Z_to_bv 8 0) (Z.to_nat (fl_end mb ms - fl_beg mb)))]) ->
      implS bsegs RNG (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (flush_shadow mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 flush_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI PC PRM RR A0 A1 MLO MPOS MCE RA RIMG RSTK KONT.
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). pose proof atop_range as ATR.
  unfold flush_shadow. cbv zeta.
  rewrite (flush_beg_fl mb) by (clear -ML2 ML4 MPOS; lia). rewrite (flush_end_fl mb ms) by (clear -ML2 ML4 MPOS; lia).
  destruct (Z.ltb_spec (fl_beg mb) (fl_end mb ms)) as [PAGE|NOPAGE].
  - rewrite aembed_vis. cbn [aev_tree].
    eapply (flush_mad_spec RNG (fun z => aembed ATOP (if z =? 0 then k else aundef_ UBadAnswer k)) Q) with (mb := mb) (ms := ms) (lo := lo);
      try eassumption.
    intros rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU WM MI' ST' ZF'.
    destruct HF as [HA _]. cbn in HA. subst RNG'.
    cbv beta. change (0 =? 0) with true. cbv iota.
    eapply KONT; [exact MU | exact WM | exact MI' | exact ST' | intros _; exact ZF'].
  - iprefix.
    eapply evtF_cut.
    { eapply (flush_none_spec RNG) with (mb := mb) (ms := ms) (lo := lo); try eassumption. }
    cbv beta. intros ms' PO. unfold flush_post in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & ST').
    apply evtF_done. eapply KONT; [| exact WM | exact MI' | exact ST' | intros C; exfalso; clear -C NOPAGE; lia].
    eapply munch_weaken; [| exact MU]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia.
Qed.

End CANSEC2.
End TwinB.
