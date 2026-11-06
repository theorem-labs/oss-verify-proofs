(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep AMalloc_iface F_apoison F_annot F_annot_sg F_annot_grow APoisonR_iface I_asan_memmove I_asan_memset.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac AU_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import ShadowTac AM_kitA AM_kitB AM_kitC AM_model AM_annotw AM_strctor AM_valloc AM_vdealloc AM_construct.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
Definition bxa (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxa P) in H end.
Local Ltac pose_hr i SHVi :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) i ltac:(lia) VSHx) as H;
      unfold bxa in SHVi; rewrite <- SHVi in H; box SHVi end end.
Local Ltac pose_hr0 SHV :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSHx) as H; rewrite Z.add_0_r in H;
      unfold bxa in SHV; rewrite SHV in H; box SHV end end.

Section CANSEC1. Context {rc : runConstT}.
Definition AVASSIGN : Z := 0xb29c4.
Definition AVASSIGN_STACK : Z := 80 + AVALLOC_STACK.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition annotw_s54_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (shad beg + 6, shad beg + shlen (rup8 n))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (vpat n 54)].

Lemma annotw_shrink_to54 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg n lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 n ->
  rw_cells asegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + 54)); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 n <= V) ->
  beg mod 8 = 0 -> 54 <= n <= 2^40 ->
  ablk beg (beg + rup8 n) -> beg + rup8 n <= 2^47 ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (block_shadow_bytes n)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 n)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF asegs RNG (annotw_s54_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_SHRINK) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST CEIL LO SPH PC AC GOT SHB Ha0 Ha1 VEC VSH V8 VBLK VDJ AL NH KH HE FULL RIMG RSTK RSH RV RVS.
  pose proof atop_range as ATR. unfold ANNOTW_STACK in LO.
  pose proof (ablk_lin _ _ KH) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NH; Z.div_mod_to_equations; lia).
  assert (AR : exists G, shlen (rup8 n) = G /\ 7 <= G /\ 8 * G <= n + 7 /\ 0 <= G)
    by (exists (shlen (rup8 n)); unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - NH; Z.div_mod_to_equations; lia).
  destruct AR as (G & EG & G7 & G8 & G0).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - KH1 KH3 NH ATR G8 R8B; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold annotw_s54_post. rewrite EG in FULL, RSH |- *.
  destruct (Z.eq_dec n 54) as [E54|NE].
  - (* [comment removed for export] *)
    subst n. rewrite <- vpat_tight in FULL.
    eapply evtF_mono.
    + eapply (annotw_shrink_nop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg 54 54 lo);
        first [ exact MI | exact ST | exact CEIL | exact LO | exact SPH | exact PC | exact AC | exact GOT | exact SHB | exact Ha0 | exact Ha1 | exact VEC | exact VSH
              | exact V8 | exact VBLK | exact RIMG | exact RSTK | exact RV | exact RVS | (clear - KH1; lia) | (clear; lia) | (clear - KH4 R8B; lia) | lia ].
    + cbv beta. unfold annotw_nop_post. intros ms' P.
      destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU & WM & MI' & ST').
      do 15 eexists. exists m'. split; [reflexivity|].
      split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
      split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
      eapply rw_cells_transport; [exact FULL| exact MU| exact WM|].
      cbn [disjoint_from cells_size csize fst snd]. rewrite ?Nat.add_0_r, ?Z2Nat.id by lia. unfold ANNOTW_STACK in *. clear - SHBB LO CEIL ATR G0. lia.
  - (* [comment removed for export] *)
    eapply evtF_mono.
    + eapply (annotw_shrink_sg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n n 54 lo (block_shadow_bytes n));
        first [ exact MI | exact ST | exact CEIL | exact LO | exact SPH | exact PC | exact AC | exact GOT | exact SHB | exact Ha0 | exact Ha1 | exact VEC | exact VSH
              | exact V8 | exact VBLK | exact VDJ | exact AL | exact KH | exact HE | exact RIMG | exact RSTK | exact RV | exact RVS
              | (rewrite EG; exact FULL) | (rewrite EG; exact RSH) | (apply bsb_hsb; clear - NH; lia) | (clear - NH; lia) | (clear - NE NH; lia) | lia ].
    + cbv beta. unfold annotw_sg_post. intros ms' P.
      destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU & WM & MI' & ST' & OUT).
      rewrite sg_out_tight in OUT by (clear - NE NH; lia). rewrite EG in OUT.
      do 15 eexists. exists m'. split; [reflexivity|].
      split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; change (54 / 8) with 6; intros; lia|].
      split; [exact WM|]. split; [exact MI'|]. split; [exact ST'| exact OUT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition avassign_inplace_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (V beg n P lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (V + 8, V + 16); (beg, beg + 54); (shad beg, shad beg + granules n)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + 54)); C8 (Z_to_bv 64 (beg + n))]
    /\ rw_cells asegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (shad beg) [CB (Z.to_nat (granules n)) (vpat n 54)]
    /\ rw_cells asegs m' beg [CB 54 errmsg]
    /\ bytes_at asegs m' P errmsg
    (* [comment removed for export] *)
    /\ (exists m1, munch [(lo, bv_unsigned sp); (V + 8, V + 16); (beg, beg + 54)] m m1 /\ wmono asegs m m1
          /\ munch [(lo, bv_unsigned sp); (shad beg + 6, shad beg + granules n)] m1 m' /\ wmono asegs m1 m').

(* [comment removed for export] *)
Definition win_facts (RNG : footprint) (m : amem) (D k : Z) : Prop :=
  app_blk D (D + k) /\ unpoisoned m D (D + k) /\ rng RNG D k
  /\ exists RLO RHI, (RLO <= D /\ D + k <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)
     /\ wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Lemma avassign_inplace : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg n P lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AVASSIGN_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 (P + 54) -> a3 = Z_to_bv 64 54 ->
  (* [comment removed for export] *)
  rw_cells asegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n)); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + n <= V) ->
  (* [comment removed for export] *)
  ablock_range beg n -> 54 <= n <= AREQMAX ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  wr_at asegs m beg n -> win_facts RNG m beg 54 ->
  (* [comment removed for export] *)
  bytes_at asegs m P errmsg -> ablock_range P 56 -> win_facts RNG m P 54 -> (beg + n <= P \/ P + 56 <= beg) -> (V + 24 <= P \/ P + 56 <= V) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (n + 7)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF asegs RNG (avassign_inplace_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V beg n P lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AVASSIGN) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LOA LOS SPH PC AC GOT RIC SHB INI LAY -> -> -> -> VEC VSH V8 VBLK DJ BR NR FULL WT WFD SRC PBR WFS DJP DJPV RIMG RSTK RSB RV RVS.
  unfold AVASSIGN, AVASSIGN_STACK, AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK in *. pose proof atop_range as ATR. unfold AREQMAX in NR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
  assert (AL : beg mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
  assert (ANS : beg + n <= 0x7fff7000 \/ 0x10007fff8000 <= beg) by (unfold ablk, AIMG_HI, KLS in BR1; clear - BR1; lia).
  pose proof PBR as (PR1 & PR2 & PR3 & PR4). pose proof (ablk_lin _ _ PR1) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
  assert (PNS : P + 56 <= 0x7fff7000 \/ 0x10007fff8000 <= P) by (unfold ablk, AIMG_HI, KLS in PR1; clear - PR1; lia).
  assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NR; Z.div_mod_to_equations; lia).
  pose proof (ablk_rup8 _ _ BR1 AL ltac:(lia)) as BRU. pose proof (ablk_lin _ _ BRU) as (_ & _ & BU3 & BU4).
  assert (DJ8 : V + 24 <= beg \/ beg + rup8 n <= V)
    by (destruct DJ as [D|D]; [left; exact D| right]; clear - D V8 AL R8B NR; unfold rup8, rdn8 in *; Z.div_mod_to_equations; lia).
  assert (AR : exists G, shlen (rup8 n) = G /\ G = granules n /\ 7 <= G /\ 8 * G <= n + 7 /\ shlen (n + 7) = G)
    by (exists (shlen (rup8 n)); rewrite <- granules_rup8 by lia; unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - NR; Z.div_mod_to_equations; lia).
  destruct AR as (G & EG & EGG & G7 & G8 & EG7).
  rewrite <- EGG in FULL. rewrite EG7 in RSB.   (* [comment removed for export] *)
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHV16 : Z.shiftr (V + 16) 3 + 2147450880 = shad V + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - BL1 BU3 NR ATR G8 R8B; Z.div_mod_to_equations; lia).
  assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V)
    by (rewrite SHV; unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - DJ8 V8 AL G8 R8B NR G7; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (ADJV : shad V + 3 <= beg \/ beg + n <= shad V) by (clear - ANS SHVB; lia).
  assert (ADJA : shad beg + G <= beg \/ beg + n <= shad beg) by (clear - ANS SHBB; lia).
  assert (ADJP : shad beg + G <= P \/ P + 56 <= shad beg) by (clear - PNS SHBB; lia).
  assert (ADJPV : shad V + 3 <= P \/ P + 56 <= shad V) by (clear - PNS SHVB; lia).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC2 : rng RNG (Z.shiftr (V + 16) 3 + 2147450880) 1) by (rewrite SHV16; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8; box SHV16.
  (* [comment removed for export] *)
  pose proof (munch_refl [(lo, bv_unsigned sp); (V + 8, V + 16); (beg, beg + 54); (shad beg, shad beg + G)] m) as MU.
  pose proof (munch_refl [(lo, bv_unsigned sp); (V + 8, V + 16); (beg, beg + 54)] m) as MUA.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box SRC.
  carve_frame 80%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.             (* [comment removed for export] *)
  pose_hr 2 SHV16. pose_hr0 SHV.
  astep. astep.                           (* [comment removed for export] *)
  zstep. zstep.                           (* [comment removed for export] *)
  astep. astep.                           (* [comment removed for export] *)
  zstep. zstep.                           (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  try replace (beg + n - beg) with n by lia.
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K NR; lia]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  pose_hr 1 SHV8.
  astep. astep.                           (* [comment removed for export] *)
  zstep. zstep.                           (* [comment removed for export] *)
  try replace (beg + n - beg) with n by lia.
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K NR; lia]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  try replace (P + 54 - P) with 54 by lia.
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MIx : mem_inv asegs mm, MUAx : munch [(lo, _); (V + 8, _); (beg, _)] m mm, WMx : wmono asegs m mm, WTx : wr_at asegs mm beg n |- _ =>
    (* [comment removed for export] *)
    destruct (rw_cells_of_wr_at asegs mm beg 54 (wr_at_sub asegs mm beg n beg 54 WTx ltac:(lia) ltac:(lia)) (no_image_asan beg (beg + 54) ltac:(lia)) ltac:(lia)) as (jk & LJ & BLKj);
    change (Z.to_nat 54) with 54%nat in BLKj;
    unfold bxa in SRC;
    assert (SRC1 : bytes_at asegs mm P errmsg)
      by (eapply bytes_at_transport; [exact SRC| exact MUAx| cbn [disjoint_from]; rewrite errmsg_len; clear - LOA ATR PL3 DJPV DJP NR; lia]);
    assert (WFD1 : win_facts RNG mm beg 54)
      by (destruct WFD as (X1 & X2 & X3 & RLOd & RHId & X4 & X5 & X6); split; [exact X1|]; split;
          [eapply unpoisoned_munch; [exact X2| exact MUAx|]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; clear - LOA ATR BL1 BL3 ANS VNS VLO AL NR; Z.div_mod_to_equations; lia|];
          split; [exact X3|]; exists RLOd, RHId; split; [exact X4|]; split; [eapply wr_at_transport; [exact X5| exact WMx]| exact X6]);
    assert (WFS1 : win_facts RNG mm P 54)
      by (destruct WFS as (X1 & X2 & X3 & RLOs & RHIs & X4 & X5 & X6); split; [exact X1|]; split;
          [eapply unpoisoned_munch; [exact X2| exact MUAx|]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; clear - LOA ATR PL1 PL3 PNS VNS VLO ANS BL1 PR4 NR DJP; Z.div_mod_to_equations; lia|];
          split; [exact X3|]; exists RLOs, RHIs; split; [exact X4|]; split; [eapply wr_at_transport; [exact X5| exact WMx]| exact X6]);
    box SRC;
    destruct WFD1 as (APPd & UNPd & RWd & RLOd & RHId & HUd & WHd & RHd);
    destruct WFS1 as (APPs & UNPs & RWs & RLOs & RHIs & HUs & WHs & RHs);
    name_sp sp (-80)%Z;
    eapply evtF_cut;
    [ eapply (asan_memmove_spec RNG) with (lo := lo) (src := errmsg) (RLO1 := RLOs) (RHI1 := RHIs) (RLO2 := RLOd) (RHI2 := RHId);
      rewrite ?Hsp; rewrite ?unsigned_lit by lia; change (Z.to_nat 54) with 54%nat;
      first [ exact SRC1 | exact APPd | exact UNPd | exact RWd | exact HUd | exact WHd | exact RHd | exact APPs | exact UNPs | exact RWs | exact HUs | exact WHs | exact RHs
            | exact RIMG | exact errmsg_len | eassumption
            | (unfold KHIGH; clear - LOA ATR; lia)
            | (clear - DJP NR; lia)
            | (left; clear - PL3 LOA ATR LOS; lia)
            | (left; clear - BL3 LOA ATR; lia)
            | (eapply rng_sub'; [exact RSTK| clear - LOS LOA LO0; lia])
            | (clear; lia) | lia ]
    | cbv beta; unfold asan_memmove_post; rewrite ?Hsp; rewrite ?unsigned_lit by lia; change (Z.to_nat 54) with 54%nat;
      clear APPd UNPd RWd HUd WHd RHd APPs UNPs RWs HUs WHs RHs SRC1; post_call asegs mm ]
    end end.
  all: rewrite ?unsigned_lit in * by lia.
  try unname_sp.
  (* [comment removed for export] *)
  pose_hr 1 SHV8. pose_hr0 SHV.
  astep. astep.                           (* [comment removed for export] *)
  astep. astep.                           (* [comment removed for export] *)
  zstep. zstep.                           (* [comment removed for export] *)
  zstep. zstep.                           (* [comment removed for export] *)
  try replace (beg + n - beg) with n by lia.
  zstep.                                  (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  box VNS. box ANS. box PNS. box DJ. box DJ8. box DJP. box DJPV. box SHDJ. box ADJV. box ADJA. box ADJP. box ADJPV.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                                  (* [comment removed for export] *)
  unfold bxa in VNS, ANS, PNS, DJ, DJ8, DJP, DJPV, SHDJ, ADJV, ADJA, ADJP, ADJPV.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _, FULLx : rw_cells asegs mm (shad beg) _, STx : stk asegs mm lo _, MIx : mem_inv asegs mm,
                        MUAx : munch [(lo, _); (V + 8, _); (beg, _)] m mm |- _ =>
    assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp); (V + 8, V + 16); (beg, beg + 54); (shad beg, shad beg + G)])
      by (repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LOA ATR VLO BL1; lia);
    pose proof (poison_cells_frame _ _ _ PC MU WM HWI) as PCa;
    pose proof (annot_cells_frame _ _ _ AC MU WM HWI) as ACa;
    pose proof WM as WMA; box MUAx; box WMA;
    pose proof (munch_refl [(lo, bv_unsigned sp); (shad beg + 6, shad beg + G)] mm) as MUB;
    pose proof (wmono_refl asegs mm) as WMB;
    eapply evtF_cut;
    [ eapply (annotw_shrink_to54 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n lo);
      first [ exact MIx | exact STx | exact PCa | exact ACa | exact VECx | exact VSHx | exact V8 | exact VBLK | exact DJ8 | exact AL | exact BRU | exact RIMG | exact RSTK | exact RV | exact RVS | reflexivity
            | (rewrite EG; exact FULLx) | (rewrite EG; exact RSB) | eassumption
            | (unfold ANNOTW_STACK; clear - LOS; lia) | (clear - NR; lia) | (clear - BU4; lia) | lia ]
    | cbv beta; unfold annotw_s54_post, ANNOTW_STACK; rewrite ?EG; clear PCa ACa HWI; post_call asegs mm ]
    end end.
  (* [comment removed for export] *)
  apply evtF_done. unfold avassign_inplace_post. rewrite <- EGG. unfold bxa in SRC.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with MUx : munch _ m mm, WMx : wmono asegs m mm, MIx : mem_inv asegs mm, STx : stk asegs mm lo _,
                        VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _, OUTx : rw_cells asegs mm (shad beg) [CB _ (vpat _ _)], BLKx : rw_cells asegs mm beg _,
                        MUBx : munch _ ?m1 mm, WMBx : wmono asegs ?m1 mm |- _ =>
    do 15 eexists; exists mm; split; [reflexivity|];
    split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact STx|]; split; [exact VECx|]; split; [exact VSHx|]; split; [exact OUTx|]; split; [exact BLKx|];
    split; [eapply bytes_at_transport; [exact SRC| exact MUx| cbn [disjoint_from]; rewrite errmsg_len; clear - LOA ATR PL3 ADJP DJP DJPV NR; lia]|];
    exists m1; unfold bxa in MUA, WMA; split; [exact MUA|]; split; [exact WMA|]; split; [exact MUBx| exact WMBx]
    end end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition avassign_realloc_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (V P lo : Z) (pv : AsanCtrl.aptr) (m : amem) (b' : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : amem) (A : Z) (p' : AsanCtrl.aptr),
    b' = Some p' /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aps_rest s' = aps_rest s
    /\ ablock_range A 54
    /\ aheap_pres_x CI (lb_remove pv LB) (bv_unsigned sp) V 24 m m'
    /\ AHEAP AI L RNG' (aps_m s') (HB p' A 54 :: lb_remove pv LB) m'
    /\ rw_cells asegs m' V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 54)); C8 (Z_to_bv 64 (A + 54))]
    /\ rw_cells asegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' A [CB 54 errmsg]
    /\ rw_cells asegs m' (shad A) [CB 7 (block_shadow_bytes 54)]
    /\ bytes_at asegs m' P errmsg
    /\ rng RNG' A 54 /\ rng RNG' (shad A) 7.

Definition avassign_realloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (lo V beg n P : Z) (pv ps : AsanCtrl.aptr) (cls FA FN RLO2 RHI2 : Z),
  AHEAP AI L RNG (aps_m s) LB m -> In (HB pv beg n) LB -> In (HB ps P 56) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AVASSIGN_STACK ->
  bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  In (mkABlock (ABFake cls) FA FN) LB -> FA <= V -> V + 24 <= FA + FN -> V mod 8 = 0 -> ablk V (V + 24) ->
  rw_cells asegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n)); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  FA <= RLO2 -> RLO2 <= V -> V + 24 <= RHI2 -> RHI2 <= FA + FN -> RLO2 mod 64 = 0 -> RHI2 mod 64 = 0 ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  0 < n < 54 ->
  (* [comment removed for export] *)
  rw_cells asegs m P [CB 54 errmsg] ->
  In [AFREE_PC; AVDEALLOC_RET] (al_U L) -> In [AMALLOC_PC; AOPNEW_RET] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  aps_ok L s ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 (P + 54) -> a3 = Z_to_bv 64 54 ->
  implMA RNG (odeleteA (Some pv) ;;; (p' <- opnewA 54 ;; mret (Some p'))) s
        (avassign_realloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB V P lo pv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AVASSIGN) fc None m (seg_rom asegs)).

Section Proof.
  Hypothesis OD : opdelete_stmtA AI.
  Hypothesis ONTA : opnew_stmtA AI.
  Hypothesis AI_kind : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
  Hypothesis AI_premap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> premap_cells m.

  Theorem avassign_realloc_proof : avassign_realloc_stmt.
  Proof.
    unfold avassign_realloc_stmt. intros until RHI2.
    intros AH HIN HSIN MI ST LOA LOS STOP SP16 TP FIN FV1 FV2 V8 VBLK VEC VSH Q1 Q2 Q3 Q4 Q5 Q6 WR2 RR2 NR STRB HUD HUN RSTK RI RV RVS AOK -> -> -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AVASSIGN_STACK, AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK in LOS. pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH FIN) as FB. cbn [ab_addr ab_size] in FB.
    pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO, FB.
    assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (NRB & BRB & _).
    pose proof BRB as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HSIN) as (_ & PRB & _).
    pose proof PRB as (PR1 & PR2 & PR3 & PR4). pose proof (ablk_lin _ _ PR1) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
    assert (PNS : P + 56 <= 0x7fff7000 \/ 0x10007fff8000 <= P) by (unfold ablk, AIMG_HI, KLS in PR1; clear - PR1; lia).
    assert (NEB : HB pv beg n <> HB ps P 56) by (intros E; injection E; clear - NR; lia).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HIN HSIN NEB) as DJB. cbn [ab_addr ab_size] in DJB.
    assert (PVS : pv <> ps).
    { intros E. subst ps. pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND.
      clear - ND HIN HSIN NEB. revert ND HIN HSIN. induction LB as [|b LB IH]; intros ND HIN HSIN; [destruct HIN|].
      change (hb_ids (b :: LB)) with ((match ab_kind b with ABHeap p => [p] | ABFake _ => [] end) ++ hb_ids LB) in ND.
      destruct HIN as [EB|HIN]; destruct HSIN as [ES|HSIN].
      - apply NEB. rewrite <- EB, <- ES. reflexivity.
      - subst b. cbn [ab_kind app] in ND. apply NoDup_cons_iff in ND as [NI _]. apply NI. exact (hb_ids_in pv P 56 LB HSIN).
      - subst b. cbn [ab_kind app] in ND. apply NoDup_cons_iff in ND as [NI _]. apply NI. exact (hb_ids_in pv beg n LB HIN).
      - apply IH; [| exact HIN| exact HSIN]. destruct b as [[q|c] bA bn]; cbn [ab_kind app] in ND; first [apply NoDup_cons_iff in ND as [_ ND']; exact ND' | exact ND]. }
    assert (HSIN' : In (HB ps P 56) (lb_remove pv LB)) by (apply lb_remove_keep_heap; [exact HSIN| intros E; apply PVS; symmetry; exact E]).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH FIN HSIN ltac:(discriminate)) as DJPV. cbn [ab_addr ab_size] in DJPV.
    assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
    assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
    assert (SHV16 : Z.shiftr (V + 16) 3 + 2147450880 = shad V + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
    assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
    box SHV; box SHV8; box SHV16.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH) as (GOT & _ & _ & SHB & _).
    assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (unfold bxa in SHV; rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
    assert (ACC2 : rng RNG (Z.shiftr (V + 16) 3 + 2147450880) 1) by (unfold bxa in SHV16; rewrite SHV16; eapply rng_sub'; [exact RVS| lia]).
    unfold odeleteA, HarnessM.odelete, HarnessM.opdelete, opnewA, HarnessM.opnew in |- *.
    apply implMA_from_evtF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 80%nat ST.
    unfold AVASSIGN.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.             (* [comment removed for export] *)
    pose_hr 2 SHV16. pose_hr0 SHV.
    astep. astep.                           (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    astep. astep.                           (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    try replace (beg + n - beg) with n by lia.
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K NR; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done.
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MUx : munch _ m mx, WMx : wmono asegs m mx |- _ =>
      assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx) by (eapply AHEAP_stack_frame; [exact AH| exact MUx| exact WMx| repeat constructor; cbn; lia]);
      pose proof (aheap_pres_x_of_munch CI (lb_remove pv LB) (bv_unsigned sp) V 24 _ m mx MUx WMx) as HPX1;
      box MUx; box WMx
      end end.
    lazymatch type of HPX1 with ?PREM -> _ =>
      assert (OUT1 : PREM)
        by (intros a Ha Hc Hx; cbn [outside]; pose proof (aclient_lo_or_sp AI _ _ _ _ (lb_remove pv LB) _ _ a AH ltac:(intros b Hb; exact (lb_remove_sub _ _ _ Hb)) Hc); clear - H Hx LOA; lia);
      specialize (HPX1 OUT1); clear OUT1 end.
    name_sp sp (-80)%Z.
    eapply implMA_bind.
    { eapply (avdealloc_proof AI OD AI_kind AI_premap) with (lo := lo) (L := L) (LB := LB) (V := V) (beg := beg) (n := n) (pv := pv) (cls := cls) (FA := FA) (FN := FN) (RLO2 := RLO2) (RHI2 := RHI2);
        try reflexivity; rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [ exact AH1 | exact HIN | exact TP | exact FIN | exact V8 | exact VBLK | exact Q1 | exact Q2 | exact Q3 | exact Q4 | exact Q5 | exact Q6 | exact WR2 | exact RR2 | exact HUD | exact RI | exact RV | exact RVS | exact AOK | eassumption
              | (unfold AVDEALLOC_STACK, AFREE_STACK; clear - LOS; lia)
              | (clear - STOP; lia)
              | (clear - SP16 RSP LOS LOA ATR; Z.div_mod_to_equations; lia)
              | (eapply rng_sub'; [exact RSTK| clear - LOS LOA STOP LO0; lia])
              | lia ]. }
    cbv beta. intros [] sA RNG1 ms1 PO1.
    destruct PO1 as (FLE1 & u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & mA & -> & MI1 & ST1 & ARS1 & HPXd & AHd & VECd & VSHd).
    rewrite ?Hsp in ST1, HPXd. rewrite ?unsigned_lit in ST1, HPXd by lia.
    unname_sp. retlit.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs ?mo (bv_unsigned sp + -80) ?cs |- _ =>
      assert (FR1 : rw_cells asegs mA (bv_unsigned sp + -80) cs)
        by (eapply (aheap_pres_x_rw_cells CI); [exact HPXd| exact FRx| apply aclient_range_stack; cbn; clear - VHI LOA ATR STOP LY3; lia| cbn; clear - VHI LOA LOS ATR; lia]); clear FRx end.
    lazymatch goal with SBx : rw_cells asegs ?mo P [CB 54 errmsg] |- _ =>
      assert (STRB1 : rw_cells asegs mA P [CB 54 errmsg])
        by (eapply (aheap_pres_x_rw_cells CI); [exact HPXd| exact SBx| right; left; exists (HB ps P 56); split; [exact HSIN'| cbn; lia]| cbn; clear - DJPV FV1 FV2; lia]); clear SBx end.
    pose proof (rng_fp_le _ _ _ _ FLE1 RSTK) as RSTK1. pose proof (rng_fp_le _ _ _ _ FLE1 RV) as RV1. pose proof (rng_fp_le _ _ _ _ FLE1 RVS) as RVS1. pose proof (rng_fp_le _ _ _ _ FLE1 RI) as RI1.
    pose proof (lb_remove_keep_fake pv cls FA FN LB FIN) as FIN1.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AHd) as (GOT1 & _ & _ & SHB1 & _).
    assert (ACC0' : rng RNG1 (Z.shiftr V 3 + 2147450880) 1) by (eapply rng_fp_le; [exact FLE1| exact ACC0]).
    assert (ACC2' : rng RNG1 (Z.shiftr (V + 16) 3 + 2147450880) 1) by (eapply rng_fp_le; [exact FLE1| exact ACC2]).
    clear AH1 ACC0 ACC2.
    repeat match goal with H : rw_cells asegs ?mo _ _ |- _ => lazymatch mo with mA => fail | _ => clear H end end.
    repeat match goal with H : stk asegs ?mo _ _ |- _ => lazymatch mo with mA => fail | _ => clear H end end.
    repeat match goal with H : mem_inv asegs ?mo |- _ => lazymatch mo with mA => fail | _ => clear H end end.
    (* [comment removed for export] *)
    apply implMA_from_evtF.
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia| clear K]).   (* [comment removed for export] *)
    pose_hr 2 SHV16. pose_hr0 SHV.
    astep. astep.                           (* [comment removed for export] *)
    astep. astep.                           (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    fold_lits.
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; rewrite ?unsigned_lit_wrap in K; revert K; clear; intros K; Z.div_mod_to_equations; lia]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done.
    name_sp sp (-80)%Z.
    eapply implMA_bind.
    { eapply (avalloc_proof AI ONTA) with (lo := lo) (L := L) (LB := lb_remove pv LB) (V := V) (n := 54) (cls := cls) (FA := FA) (FN := FN);
        try reflexivity; rewrite ?Hsp; rewrite ?unsigned_lit by lia;
        first [ exact AHd | exact TP | exact FIN1 | exact V8 | exact VBLK | exact HUN | exact RI1 | exact RV1 | exact RVS1 | eassumption
              | (unfold AVALLOC_STACK, OPNEW_STACK_A, AMALLOC_STACK; clear - LOS; lia)
              | (clear - STOP; lia)
              | (clear - SP16 RSP LOS LOA ATR; Z.div_mod_to_equations; lia)
              | (eapply rng_sub'; [exact RSTK1| clear - LOS LOA STOP LO0; lia])
              | (eapply aps_ok_rest; [exact ARS1| exact AOK])
              | (clear; lia) | lia ]. }
    cbv beta. intros p' sB RNG2 ms2 PO2.
    destruct PO2 as (FLE2 & v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & mqB & mB & A & jk & -> & MI2 & ST2 & ARS2 & BR & HPR2 & AH2 & MIq & MU12 & WM12
                    & VEC2 & VSH2 & BLK2 & OUT2 & RA & RSA).
    rewrite ?Hsp in ST2, HPR2, MU12. rewrite ?unsigned_lit in ST2, HPR2, MU12 by lia.
    unname_sp. retlit.
    apply implMA_ret.
    change (Z.to_nat (granules 54)) with 7%nat in OUT2. change (shlen (54 + 7)) with 7 in RSA. change (granules 54) with 7 in MU12.
    pose proof (rng_fp_le _ _ _ _ FLE2 RSTK1) as RSTK2. pose proof (rng_fp_le _ _ _ _ FLE2 RV1) as RV2. pose proof (rng_fp_le _ _ _ _ FLE2 RVS1) as RVS2. pose proof (rng_fp_le _ _ _ _ FLE2 RI1) as RI2.
    pose proof BR as (NB1 & NB2 & NB3 & NB4). pose proof (ablk_lin _ _ NB1) as (NL1 & NL2 & NL3 & NL4). unfold AIMG_HI in NL1.
    assert (AL : A mod 8 = 0) by (clear - NB4; Z.div_mod_to_equations; lia).
    assert (ANS : A + 56 <= 0x7fff7000 \/ 0x10007fff8000 <= A) by (unfold ablk, AIMG_HI, KLS in NB1; clear - NB1 NB4; Z.div_mod_to_equations; lia).
    assert (SHAB : 0x7fff8000 <= shad A /\ shad A + 7 <= 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; clear - NL1 NL3 ATR; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH2 FIN1) as DJ1. cbn [ab_addr ab_size] in DJ1.
    pose proof (new_blk_apart AI _ _ _ _ _ _ _ _ _ AH2 HSIN') as DJ2. cbn [ab_addr ab_size] in DJ2.
    assert (SHDJ : shad V + 3 <= shad A \/ shad A + 7 <= shad V)
      by (unfold bxa in SHV; rewrite SHV; unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - DJ1 FV1 FV2 V8 AL; Z.div_mod_to_equations; lia).
    assert (ADJPA : shad A + 7 <= P \/ P + 56 <= shad A) by (clear - PNS SHAB; lia).
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells asegs mA (bv_unsigned sp + -80) ?cs |- _ =>
      assert (FRq : rw_cells asegs mqB (bv_unsigned sp + -80) cs) by (eapply aheap_pres_rw_cells; [exact HPR2| exact FRx| apply aclient_range_stack; cbn; lia]);
      assert (FR2 : rw_cells asegs mB (bv_unsigned sp + -80) cs)
        by (eapply rw_cells_transport; [exact FRq| exact MU12| exact WM12| cbn [disjoint_from cells_size csize Nat.add]; clear - LOA LOS VHI SHAB ATR RSP; lia]);
      clear FRx FRq end.
    assert (STRBq : rw_cells asegs mqB P [CB 54 errmsg])
      by (eapply aheap_pres_rw_cells; [exact HPR2| exact STRB1| right; left; exists (HB ps P 56); split; [exact HSIN'| cbn; lia]]).
    assert (STRB2 : rw_cells asegs mB P [CB 54 errmsg])
      by (eapply rw_cells_transport; [exact STRBq| exact MU12| exact WM12| cbn [disjoint_from cells_size csize Nat.add]; clear - LOA ATR PL3 DJPV FV1 FV2 ADJPA; lia]).
    clear STRB1.
    (* [comment removed for export] *)
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_introl eq_refl)) as (_ & _ & _ & _ & BSH & WRA & _ & ARENA).
    destruct (AI_kind _ _ _ _ _ _ _ _ AH2 (or_introl eq_refl)) as (ch & LIVE & CSZ & UBEG & KIND).
    pose proof (cells_of_ablock_shadow mqB A 54 ltac:(lia) ltac:(lia) ltac:(lia) BSH) as FULL1. change (Z.to_nat (granules 54)) with 7%nat in FULL1.
    destruct (blk_window_facts AI _ _ _ _ _ _ _ _ P 54 AH2 (or_intror HSIN') ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & UNPsq & RWs & _).
    assert (UNPs2 : unpoisoned mB P (P + 54))
      by (eapply unpoisoned_munch; [exact UNPsq| exact MU12|]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
          clear - LOA ATR PL1 PL3 PNS VNS VLO DJ2 NL1 NL3 AL PR4 FV1 FV2 DJPV; Z.div_mod_to_equations; lia).
    assert (WRA2 : wr_at asegs mB A 54) by (eapply wr_at_transport; [exact WRA| exact WM12]).
    (* [comment removed for export] *)
    assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp + -80); (V, V + 24); (shad A, shad A + 7)])
      by (repeat constructor; cbn; unfold AIMG_HI; clear - LOA ATR VLO SHAB; lia).
    pose proof (poison_cells_frame _ _ _ (poison_cells_of_aheap AI _ _ _ _ _ AH2) MU12 WM12 HWI) as PC2.
    pose proof (annot_cells_frame _ _ _ (annot_cells_of_aheap AI _ _ _ _ _ AH2 (hrt_cells_of_aheap AI _ _ _ _ _ AH2)) MU12 WM12 HWI) as AC2.
    pose proof (artcells_frame _ _ _ (AI_rtcells AI _ _ _ _ _ AH2) MU12 WM12 HWI) as ART2.
    pose proof (premap_cells_frameA _ _ _ (AI_premap _ _ _ _ _ AH2) MU12 WM12 HWI) as PRM2.
    pose proof (arelro_munchA _ _ _ (arelro_of_aheap AI _ _ _ _ _ AH2) MU12 HWI) as RR2'.
    pose proof (client_rt_of_aheap AI _ _ _ _ _ AH2) as (GOT2 & _ & _ & SHB2 & _).
    assert (GOT2' : rt_got mB) by (eapply rw_cells_transport; [exact GOT2| exact MU12| exact WM12| cbn [disjoint_from cells_size csize Nat.add]; clear - LOA ATR VLO SHAB; lia]).
    assert (SHB2' : rt_shbase mB) by (eapply rw_cells_transport; [exact SHB2| exact MU12| exact WM12| cbn [disjoint_from cells_size csize Nat.add]; clear - LOA ATR VLO SHAB; lia]).
    assert (ARENA2 : exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + 54 + 64 <= RHI
               /\ rng RNG2 (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs mB (shad RLO) (shlen (RHI - RLO)))
      by (destruct ARENA as (RLO & RHI & X1 & X2 & X3 & X4 & X5 & X6); exists RLO, RHI; repeat (split; [assumption|]); eapply wr_at_transport; [exact X6| exact WM12]).
    box MU12. box WM12.
    (* [comment removed for export] *)
    box VNS. box PNS. box ANS. box DJB. box DJPV. box DJ1. box DJ2. box SHDJ. box ADJPA.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.             (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
    lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR2 H (bv_unsigned sp) end.
    zstep.                                  (* [comment removed for export] *)
    unfold bxa in VNS, PNS, ANS, DJB, DJPV, DJ1, DJ2, SHDJ, ADJPA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _, OUTx : rw_cells asegs mm (shad A) [CB 7 (repeat _ _)], STx : stk asegs mm lo _, MIx : mem_inv asegs mm, SBx : rw_cells asegs mm P [CB 54 errmsg] |- _ =>
      eapply evtF_cut;
      [ eapply (ce_spec RNG2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm V A P lo) with (st := aps_m sB) (p := p') (ch := ch);
        first [ exact MIx | exact STx | exact PC2 | exact AC2 | exact ART2 | exact PRM2 | exact RR2' | exact GOT2' | exact SHB2' | exact VECx | exact VSHx | exact OUTx
              | exact UNPs2 | exact WRA2 | exact LIVE | exact CSZ | exact UBEG | exact KIND | exact ARENA2 | exact V8 | exact VBLK | exact BR | exact PRB | exact RI2 | exact RV2 | exact RVS2 | exact RA | exact RSA | exact RWs
              | (destruct SBx as [[_ SBb] _]; cbn [cells_bytes cbytes app] in SBb; rewrite app_nil_r in SBb; exact SBb)
              | (clear - LOS; lia) | (clear - STOP LY3 RSP; lia)
              | (clear - DJ1 FV1 FV2; lia) | (clear - DJPV FV1 FV2; lia) | (clear - DJ2; lia)
              | (eapply rng_sub'; [exact RSTK2| clear - LOS LOA STOP LO0; lia])
              | (eapply rng_fp_le; [exact FLE2| exact RWs])
              | (destruct (AI_block AI _ _ _ _ _ _ _ _ AH2 (or_intror HSIN')) as (_ & _ & _ & X & _); change (shlen (56 + 7)) with 7 in X; exact X)
              | lia ]
      | cbv beta; unfold ce_post ]
      end end.
    intros ms3 PO3.
    destruct PO3 as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & mC & -> & MU23 & WM23 & MI3 & ST3 & VEC3 & VSH3 & FULL3 & BLK3 & SRC3).
    unfold AM_construct.VSH, AM_construct.FULL in VSH3, FULL3.
    apply evtF_done. unfold avassign_realloc_post.
    split; [eapply fp_le_trans; [exact FLE1| exact FLE2]|].
    (* [comment removed for export] *)
    unfold bxa in MU12, WM12.
    assert (MU13 : munch [(shad A, shad A + 7); (lo, bv_unsigned sp); (V, V + 24); (A, A + 54)] mqB mC).
    { eapply munch_trans.
      - eapply munch_weaken; [| exact MU12]. unfold sub_fp. cbn [outside]. intros x (X1 & X2 & X3 & X4 & _). clear - X1 X2 X3 X4. lia.
      - eapply munch_weaken; [| exact MU23]. unfold sub_fp. cbn [outside]. intros x (X1 & X2 & X3 & X4 & _). clear - X1 X2 X3 X4. lia. }
    assert (MU3 : munch [(lo, bv_unsigned sp); (V, V + 24); (A, A + 54)] mqB mC)
      by (eapply (munch_unwrite _ mqB mC (shad A) (shad A + 7) 7%nat (block_shadow_bytes 54)); [exact MU13| cbn; lia| exact FULL1| exact FULL3| clear - SHAB; lia| clear - SHAB; cbn; lia]).
    assert (WM3 : wmono asegs mqB mC) by (eapply wmono_trans; [exact WM12| exact WM23]).
    assert (AH3 : AHEAP AI L RNG2 (aps_m sB) (HB p' A 54 :: lb_remove pv LB) mC).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [apply aclient_range_stack; cbn; clear - LOA STOP LY3; lia|].
      constructor; [eapply aclient_range_fake; [right; exact FIN1| cbn; lia| cbn; lia]|].
      constructor; [right; left; exists (HB p' A 54); split; [left; reflexivity| cbn; lia]| constructor]. }
    do 15 eexists. exists mC, A, p'. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [rewrite ARS2; exact ARS1|]. split; [exact BR|].
    split.
    { (* [comment removed for export] *)
      eapply aheap_pres_x_trans; [exact HPX1|]. eapply aheap_pres_x_trans.
      { eapply (aheap_pres_x_weaken CI); [exact HPXd| clear - LOS; lia| intros b Hb; exact Hb| intros a _ Hx; exact Hx]. }
      eapply aheap_pres_x_trans.
      { eapply (aheap_pres_x_of_pres CI); [exact HPR2| clear - LOS; lia| intros b Hb; exact Hb]. }
      eapply aheap_pres_x_of_munch; [exact MU3| exact WM3|].
      intros a Ha Hc Hx. cbn [outside].
      pose proof (aclient_lo_or_sp AI _ _ _ _ (lb_remove pv LB) _ _ a AH2 ltac:(intros b Hb; right; exact Hb) Hc) as Y1.
      assert (HSP0 : ATOP <= bv_unsigned sp) by (clear - LOA LOS; lia).
      pose proof (fresh_not_client AI _ _ _ _ _ _ _ _ _ a AH2 HSP0 Hc) as Y2.
      clear - Y1 Y2 Hx LOA LOS. lia. }
    split; [exact AH3|]. split; [exact VEC3|]. split; [exact VSH3|]. split; [exact BLK3|]. split; [exact FULL3|]. split; [exact SRC3|].
    split; [exact RA| exact RSA].
  Qed.
End Proof.
End S.
End CANSEC1.
