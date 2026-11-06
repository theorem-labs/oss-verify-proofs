(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow SysStepF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ABytes ARep AModelFacts F_memset F_apoison F_m2s F_annot F_annot_sg APoisonR_iface F_annot_grow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_parts_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AKit AKit2 FsKit ShadowTac AU_steptac AU_h_kit AAnnot_iface AM_kitB AM_annotw.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
Definition bxf (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxf P) in H end.
(* [comment removed for export] *)
Local Ltac pose_hr i SHVi :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) i ltac:(lia) VSHx) as H;
      unfold bxf in SHVi; rewrite <- SHVi in H; box SHVi end end.
Local Ltac pose_hr0 SHV :=
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VSHx : rw_cells asegs mm (shad ?V) [C1 _; C1 _; C1 _] |- _ =>
      let H := fresh "HR" in pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSHx) as H; rewrite Z.add_0_r in H;
      unfold bxf in SHV; rewrite SHV in H; box SHV end end.

Section CANSEC1. Context {rc : runConstT}.
Definition AVDTORF : Z := 0xb2804.
Definition AVDTORF_STACK : Z := 32 + ANNOTW_STACK.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition annotw_clr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (shad beg, shad beg + shlen (rup8 n))] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 n))))].

Lemma annotw_shrink_clr : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg n k lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 k ->
  rw_cells asegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 n <= V) ->
  beg mod 8 = 0 -> 0 < n <= 2^40 -> 0 <= k <= n ->
  ablk beg (beg + rup8 n) -> beg + rup8 n <= 2^47 ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (vpat n k)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 n)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF asegs RNG (annotw_clr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_SHRINK) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST CEIL LO SPH PC AC GOT SHB Ha0 Ha1 VEC VSH V8 VBLK VDJ AL NH KK KH HE FULL RIMG RSTK RSH RV RVS.
  pose proof atop_range as ATR. unfold ANNOTW_STACK in LO.
  pose proof (ablk_lin _ _ KH) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NH; Z.div_mod_to_equations; lia).
  assert (AR : exists G, shlen (rup8 n) = G /\ 0 <= G /\ 8 * G <= n + 7 /\ shlen (rup8 k) <= G /\ 0 <= shlen (rup8 k))
    by (exists (shlen (rup8 n)); unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - NH KK; Z.div_mod_to_equations; lia).
  destruct AR as (G & EG & G0 & G8 & GKG & GK0).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - KH1 KH3 NH ATR G8 R8B; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold annotw_clr_post. rewrite EG in FULL, RSH |- *.
  assert (VEC0 : rw_cells asegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + 0)); C8 (Z_to_bv 64 (beg + n))])
    by (eapply rw_cells_recast; [exact VEC| cbn; repeat split; exact I| cbn [cells_bytes cbytes app]; rewrite Z.add_0_r; reflexivity| reflexivity]).
  destruct (Z.eq_dec k 0) as [K0|KP].
  - (* [comment removed for export] *)
    subst k. rewrite vpat_zero, <- granules_rup8, EG in FULL by lia.
    eapply evtF_mono.
    + eapply (annotw_shrink_nop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n 0 lo);
        first [ exact MI | exact ST | exact CEIL | exact LO | exact SPH | exact PC | exact AC | exact GOT | exact SHB | exact Ha0 | exact Ha1 | exact VEC0 | exact VSH
              | exact V8 | exact VBLK | exact RIMG | exact RSTK | exact RV | exact RVS | (clear - KH1; lia) | (clear - NH; lia) | (clear - KH4 R8B; lia) | lia ].
    + cbv beta. unfold annotw_nop_post. intros ms' P.
      destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU & WM & MI' & ST').
      do 15 eexists. exists m'. split; [reflexivity|].
      split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
      split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
      eapply rw_cells_transport; [exact FULL| exact MU| exact WM|].
      cbn [disjoint_from cells_size csize fst snd]. rewrite ?Nat.add_0_r, ?Z2Nat.id by lia. unfold ANNOTW_STACK in *. clear - SHBB LO CEIL ATR G0. lia.
  - (* [comment removed for export] *)
    eapply evtF_mono.
    + eapply (annotw_shrink_sg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n k 0 lo (vpat n k));
        first [ exact MI | exact ST | exact CEIL | exact LO | exact SPH | exact PC | exact AC | exact GOT | exact SHB | exact Ha0 | exact Ha1 | exact VEC0 | exact VSH
              | exact V8 | exact VBLK | exact VDJ | exact AL | exact KH | exact HE | exact RIMG | exact RSTK | exact RV | exact RVS
              | (rewrite EG; exact FULL) | (rewrite EG; exact RSH) | (apply vpat_hsb; clear - KP KK; lia) | (clear - NH; lia) | (clear - KP KK; lia) | lia ].
    + cbv beta. unfold annotw_sg_post. intros ms' P.
      destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU & WM & MI' & ST' & OUT).
      rewrite sg_out_clear, <- granules_rup8, EG in OUT by lia.
      do 15 eexists. exists m'. split; [reflexivity|].
      split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; change (0 / 8) with 0; intros; lia|].
      split; [exact WM|]. split; [exact MI'|]. split; [exact ST'| exact OUT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition avdtorf_null_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma avdtorf_null : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (X V lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp + 16 <= 2^47 ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 X ->
  bv_unsigned sp <= X -> X + 8 <= 2^47 -> X mod 8 = 0 ->
  rw_cells asegs m X [C8 (Z_to_bv 64 V)] ->
  rw_cells asegs m (Z.shiftr X 3 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m V [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  rng RNG X 8 -> rng RNG (Z.shiftr X 3 + 2147450880) 1 ->
  evtF asegs RNG (avdtorf_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AVDTORF) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LOA LOS SPH GOT SHB -> XLO XHI X8 FX FSH VEC VSH V8 VBLK RIMG RSTK RV RVS RX RXS.
  unfold AVDTORF. pose proof atop_range as ATR.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SXB : 0x7fff8000 <= Z.shiftr X 3 + 2147450880 /\ Z.shiftr X 3 + 2147450880 + 1 <= ATOP)
    by (rewrite !Z.shiftr_div_pow2 by lia; clear - XLO XHI ATR RSP; Z.div_mod_to_equations; lia).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  box SHV.
  unfold avdtorf_null_post.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  pose_hr0 SHV.
  zstep. zstep. astep. astep.             (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep. zstep. astep. astep.             (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; clear - K; lia]).   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                                  (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition avdtorf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (V beg n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 beg) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 AOPDEL_SZ) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (V + 8, V + 16); (shad beg, shad beg + granules n)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n))]
    /\ rw_cells asegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (shad beg) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)]
    (* [comment removed for export] *)
    /\ (exists m1, munch [(lo, bv_unsigned sp); (V + 8, V + 16)] m m1 /\ wmono asegs m m1
          /\ munch [(lo, bv_unsigned sp); (shad beg, shad beg + granules n)] m1 m' /\ wmono asegs m1 m').

Lemma avdtorf_live : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (X V beg n k lo : Z) (st : astate) (p : AsanCtrl.aptr) (ch : achunk),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AVDTORF_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> artcells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 X ->
  (* [comment removed for export] *)
  bv_unsigned sp <= X -> X + 8 <= 2^47 -> X mod 8 = 0 ->
  rw_cells asegs m X [C8 (Z_to_bv 64 V)] ->
  rw_cells asegs m (Z.shiftr X 3 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + k)); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + n <= V) ->
  (* [comment removed for export] *)
  ablock_range beg n -> 0 < n <= AREQMAX -> 0 <= k <= n ->
  (a_live st) !! p = Some ch -> chunk_size ch = n -> (is_primary n = false -> beg = chunk_user_beg ch) -> achunk_kind_ok ch n ->
  rw_cells asegs m (shad beg) [CB (Z.to_nat (granules n)) (vpat n k)] ->
  (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= beg /\ beg + n + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (n + 7)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  rng RNG X 8 -> rng RNG (Z.shiftr X 3 + 2147450880) 1 ->
  evtF asegs RNG (avdtorf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V beg n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AVDTORF) fc None m (seg_rom asegs)).
Proof.
  intros until ch. intros MI ST LOA LOS SPH PC AC ART PRM RR GOT SHB -> XLO XHI X8 FX FSH VEC VSH V8 VBLK DJ BR NR KK LIVE CSZ UBEG KIND FULL ARENA RIMG RSTK RSB RV RVS RX RXS.
  unfold AVDTORF, AVDTORF_STACK, ANNOTW_STACK in *. pose proof atop_range as ATR. unfold AREQMAX in NR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
  assert (AL : beg mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
  assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NR; Z.div_mod_to_equations; lia).
  pose proof (ablk_rup8 _ _ BR1 AL ltac:(lia)) as BRU. pose proof (ablk_lin _ _ BRU) as (_ & _ & BU3 & BU4).
  assert (DJ8 : V + 24 <= beg \/ beg + rup8 n <= V)
    by (destruct DJ as [D|D]; [left; exact D| right]; clear - D V8 AL R8B NR; unfold rup8, rdn8 in *; Z.div_mod_to_equations; lia).
  assert (AR : exists G, shlen (rup8 n) = G /\ G = granules n /\ n / 8 <= G /\ 0 <= n / 8 /\ 8 * G <= n + 7 /\ shlen (n + 7) = G)
    by (exists (shlen (rup8 n)); rewrite <- granules_rup8 by lia; unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - NR; Z.div_mod_to_equations; lia).
  destruct AR as (G & EG & EGG & GNG & N80 & G8 & EG7).
  rewrite <- EGG in FULL. rewrite EG7 in RSB. unfold avdtorf_post. rewrite <- EGG.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHV16 : Z.shiftr (V + 16) 3 + 2147450880 = shad V + 2) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - BL1 BU3 NR ATR G8 R8B; Z.div_mod_to_equations; lia).
  assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V)
    by (rewrite SHV; unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - DJ8 V8 AL G8 R8B NR GNG N80; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (SXB : shad beg + G <= Z.shiftr X 3 + 2147450880 /\ Z.shiftr X 3 + 2147450880 + 1 <= ATOP
                /\ 0x7fff8000 <= Z.shiftr X 3 + 2147450880 /\ Z.shiftr X 3 + 2147450880 + 1 <= 0x10007fff8000)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - XLO XHI ATR RSP LOA LOS BU3 G8 R8B NR; Z.div_mod_to_equations; lia).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC2 : rng RNG (Z.shiftr (V + 16) 3 + 2147450880) 1) by (rewrite SHV16; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8; box SHV16.
  (* [comment removed for export] *)
  pose proof (munch_refl [(lo, bv_unsigned sp); (V + 8, V + 16); (shad beg, shad beg + G)] m) as MU.
  pose proof (munch_refl [(lo, bv_unsigned sp); (V + 8, V + 16)] m) as MUA.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  pose_hr0 SHV. pose_hr 1 SHV8.
  zstep. zstep. astep. astep.             (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep. zstep. astep. astep.             (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K BL1 BL4 NR; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep. astep. astep.      (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  try replace (beg + k - beg) with k by lia.
  zstep.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VECx : rw_cells asegs mm V _ |- _ =>
    assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp); (V + 8, V + 16); (shad beg, shad beg + G)])
      by (repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LOA ATR VLO; lia);
    pose proof (poison_cells_frame _ _ _ PC MU WM HWI) as PC1;
    pose proof (annot_cells_frame _ _ _ AC MU WM HWI) as AC1;
    pose proof WM as WMA; box MUA; box WMA;
    pose proof (munch_refl [(lo, bv_unsigned sp); (shad beg, shad beg + G)] mm) as MUB;
    pose proof (wmono_refl asegs mm) as WMB;
    name_sp sp (-32)%Z;
    eapply evtF_cut;
    [ eapply (annotw_shrink_clr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n k lo);
      first [ exact PC1 | exact AC1 | exact VECx | exact V8 | exact VBLK | exact DJ8 | exact AL | exact BRU | exact BU3 | exact RIMG | exact RV | exact RVS | reflexivity
            | (rewrite Hsp; eassumption) | (rewrite EG; exact FULL) | (rewrite EG; exact RSB) | eassumption
            | (rewrite Hsp; unfold ANNOTW_STACK; clear - LOS; lia) | (rewrite Hsp; clear - RSP LOS LOA ATR SPH; lia)
            | (rewrite Hsp; eapply rng_sub'; [exact RSTK| clear - LOS LOA LO0; lia])
            | (clear - NR; lia) | (clear - KK; lia) | lia ]
    | cbv beta; unfold annotw_clr_post, ANNOTW_STACK; rewrite ?EG; clear PC1 AC1 HWI; post_call asegs mm ]
    end end.
  unname_sp.
  (* [comment removed for export] *)
  astep. astep.                           (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VECx : rw_cells asegs mm V _, OUTx : rw_cells asegs mm (shad beg) [CB _ (repeat _ _)] |- _ =>
    assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp); (V + 8, V + 16); (shad beg, shad beg + G)])
      by (repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LOA ATR VLO; lia);
    pose proof (poison_cells_frame _ _ _ PC MU WM HWI) as PC1;
    pose proof (annot_cells_frame _ _ _ AC MU WM HWI) as AC1;
    pose proof (artcells_frame _ _ _ ART MU WM HWI) as ART1;
    pose proof (premap_cells_frameA _ _ _ PRM MU WM HWI) as PRM1;
    pose proof (arelro_munchA _ _ _ RR MU HWI) as RR1;
    assert (ARENA1 : exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= beg /\ beg + n + 64 <= RHI
               /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs mm (shad RLO) (shlen (RHI - RLO)))
      by (destruct ARENA as (RLO & RHI & X1 & X2 & X3 & X4 & X5 & X6); exists RLO, RHI; repeat (split; [assumption|]); eapply wr_at_transport; [exact X6| exact WM]);
    name_sp sp (-32)%Z;
    eapply evtF_cut;
    [ eapply (annotw_delete_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n lo st p ch);
      first [ exact PC1 | exact AC1 | exact ART1 | exact PRM1 | exact RR1 | exact VECx | exact V8 | exact VBLK | exact DJ8 | exact BR | exact LIVE | exact CSZ | exact UBEG | exact KIND
            | exact ARENA1 | exact RIMG | exact RV | exact RVS | reflexivity
            | (rewrite Hsp; eassumption) | (rewrite EG; exact OUTx) | (rewrite EG; exact RSB) | eassumption
            | (rewrite Hsp; unfold ANNOTW_STACK; clear - LOS; lia) | (rewrite Hsp; clear - RSP LOS LOA ATR SPH; lia)
            | (unfold AREQMAX; clear - NR; lia)
            | (rewrite Hsp; eapply rng_sub'; [exact RSTK| clear - LOS LOA LO0; lia])
            | lia ]
    | cbv beta; unfold annotw_grow_post, ANNOTW_STACK; rewrite ?EG; clear PC1 AC1 ART1 PRM1 RR1 ARENA1 HWI; post_call asegs mm ]
    end end.
  unname_sp.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with BODY : rw_cells asegs mm (shad beg) [CB _ (repeat _ _)], LAST : (n mod 8 <> 0 -> rw_cells asegs mm _ [C1 _]) |- _ =>
    pose proof (bsb_cells_join mm (shad beg) n ltac:(lia) BODY LAST) as FULL3; rewrite <- EGG in FULL3; clear BODY LAST
    end end.
  pose_hr0 SHV. pose_hr 2 SHV16.
  astep. astep.                           (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep. zstep. astep. astep.             (* [comment removed for export] *)
  zstep. zstep. zstep. astep. astep.      (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  try replace (beg + n - beg) with n by lia.
  zstep. zstep. zstep. zstep. zstep.      (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                                  (* [comment removed for export] *)
  apply evtF_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with MUx : munch _ m mm, WMx : wmono asegs m mm, MIx : mem_inv asegs mm, STx : stk asegs mm lo _,
                        VECx : rw_cells asegs mm V _, VSHx : rw_cells asegs mm (shad V) _, OUTx : rw_cells asegs mm (shad beg) _,
                        MUBx : munch _ ?m1 mm, WMBx : wmono asegs ?m1 mm |- _ =>
    do 13 eexists; exists mm; split; [reflexivity|];
    split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact STx|]; split; [exact VECx|]; split; [exact VSHx|]; split; [exact OUTx|];
    exists m1; unfold bxf in MUA, WMA; split; [exact MUA|]; split; [exact WMA|]; split; [exact MUBx| exact WMBx]
    end end.
Qed.
End CANSEC1.
