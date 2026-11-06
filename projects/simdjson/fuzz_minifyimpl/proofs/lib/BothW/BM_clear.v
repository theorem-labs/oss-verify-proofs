(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow SysStepF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ABytes AModelFacts F_memset F_apoison F_m2s F_annot F_annot_sg APoisonR_iface F_annot_grow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit AKit2 FsKit ShadowTac AU_steptac AU_h_kit AAnnot_iface AM_kitB AM_annotw.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
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
Definition bxq (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxq P) in H end.

Section CANSEC1. Context {rc : runConstT}.
Definition ACLEAR : Z := 0xb2f48.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition annotw_clr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (shad beg, shad beg + shlen (rup8 n))] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 n))))].

Lemma annotw_shrink_clr : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg n k lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 k ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 n <= V) ->
  beg mod 8 = 0 -> 0 < n <= 2^40 -> 0 <= k <= n ->
  ablk beg (beg + rup8 n) -> beg + rup8 n <= 2^47 ->
  rw_cells bsegs m (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (vpat n k)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 n)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (annotw_clr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOTW_SHRINK) fc None m (seg_rom bsegs)).
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
  assert (VEC0 : rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + 0)); C8 (Z_to_bv 64 (beg + n))])
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
Definition aclear_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (V beg n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (V + 8, V + 16); (shad beg, shad beg + shlen (rup8 n))] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + n))]
    /\ rw_cells bsegs m' (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 n))))]
    (* [comment removed for export] *)
    /\ (exists m1, munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (V + 8, V + 16)] m m1 /\ wmono bsegs m m1
          /\ munch [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (shad beg, shad beg + shlen (rup8 n))] m1 m' /\ wmono bsegs m1 m').

Lemma aclear : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V beg n k lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOTW_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  poison_cells m -> annot_cells m -> rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + k)); C8 (Z_to_bv 64 (beg + n))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= beg \/ beg + rup8 n <= V) ->
  beg mod 8 = 0 -> 0 < n <= 2^40 -> 0 <= k <= n ->
  ablk beg (beg + rup8 n) -> beg + rup8 n <= 2^47 ->
  rw_cells bsegs m (shad beg) [CB (Z.to_nat (shlen (rup8 n))) (vpat n k)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 n)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  evtF bsegs RNG (aclear_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V beg n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACLEAR) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO SPH PC AC GOT SHB -> VEC VSH V8 VBLK VDJ AL NH KK KH HE FULL RIMG RSTK RSH RV RVS.
  unfold ACLEAR in *. pose proof atop_range as ATR.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  pose proof (ablk_lin _ _ KH) as (KH1 & KH2 & KH3 & KH4). unfold AIMG_HI in KH1.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NH; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  (* [comment removed for export] *)
  assert (AR : exists G, shlen (rup8 n) = G /\ 0 <= G /\ 8 * G <= n + 7)
    by (exists (shlen (rup8 n)); unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - NH; Z.div_mod_to_equations; lia).
  destruct AR as (G & EG & G0 & G8).
  unfold aclear_post. rewrite EG in FULL, RSH |- *.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad beg /\ shad beg + G <= 0x10007fff8000)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - KH1 KH3 NH ATR G8 G0 R8B; Z.div_mod_to_equations; lia).
  assert (SHDJ : shad V + 3 <= shad beg \/ shad beg + G <= shad V)
    by (rewrite SHV; unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - VDJ V8 AL G8 G0 R8B NH; Z.div_mod_to_equations; lia).
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC0 : rng RNG (Z.shiftr V 3 + 2147450880) 1) by (rewrite <- SHV; eapply rng_sub'; [exact RVS| lia]).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (V + 8, V + 16); (shad beg, shad beg + G)] m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - ANNOTW_STACK, bv_unsigned sp); (V + 8, V + 16)] m) as MUA.
  pose proof (wmono_refl bsegs m) as WM.
  unfold ANNOTW_STACK in LO, MU, MUA.
  carve_frame 16%nat ST.
  zstep. zstep.               (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh3_read mm (shad V) 0 ltac:(lia) VSH) as HR0; rewrite Z.add_0_r in HR0; unfold bxq in SHV; rewrite SHV in HR0; box SHV;
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSH) as HR1; unfold bxq in SHV8; rewrite <- SHV8 in HR1; box SHV8
  end.
  zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep. zstep. zstep.        (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  astep. astep.               (* [comment removed for export] *)
  zstep. zstep.               (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K;
    [ clear K
    | zstep; zstep; zstep; zstep;      (* [comment removed for export] *)
      zstep; (let K2 := fresh "Kz" in if_cases K2; zify_cond K2; [exfalso; clear - K K2 KH1 KH4 R8B NH KK; ubdec K2; lia| clear K K2]) ]).
  all: astep; astep.          (* [comment removed for export] *)
  all: zstep.                 (* [comment removed for export] *)
  all: try replace (beg + k - beg) with k by lia.
  all: zstep.                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         pose proof WM as WMA; box MUA; box WMA;
         pose proof (munch_refl [(bv_unsigned sp - 2736, bv_unsigned sp); (shad beg, shad beg + G)] mm) as MUB;
         pose proof (wmono_refl bsegs mm) as WMB end.
  all: zstep; zstep.          (* [comment removed for export] *)
  all: lazymatch goal with H : stk bsegs _ ?lox _ |- _ => release_frame FR H (bv_unsigned sp) end.   (* [comment removed for export] *)
  all: zstep.                 (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with VECx : rw_cells bsegs mm ?Vx [C8 _; C8 _; C8 _] |- _ =>
    assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(bv_unsigned sp - 2736, bv_unsigned sp); (V + 8, V + 16); (shad beg, shad beg + G)])
      by (repeat constructor; cbn; unfold AIMG_HI; clear - SHBB LO CEIL ATR VLO; lia);
    pose proof (poison_cells_frame _ _ _ PC MU WM HWI) as PCx;
    pose proof (annot_cells_frame _ _ _ AC MU WM HWI) as ACx;
    eapply evtF_cut;
    [ eapply (annotw_shrink_clr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V beg n k lo);
      first [ exact PCx | exact ACx | exact VECx | exact V8 | exact VBLK | exact VDJ | exact AL | exact KH | exact HE | exact RIMG | exact RV | exact RVS | exact CEIL
            | reflexivity | (rewrite EG; exact FULL) | (rewrite EG; exact RSH) | eassumption
            | (unfold ANNOTW_STACK; clear - LO; lia) | (clear - SPH; lia)
            | (clear - NH; lia) | (clear - KK; lia) | (f_equal; lia) | lia ]
    | cbv beta; unfold annotw_clr_post, ANNOTW_STACK; rewrite ?EG; clear PCx ACx HWI; post_call bsegs mm ]
    end end.
  all: finish.
  all: match goal with MUBx : munch [_; (shad _, _)] ?mid _, WMBx : wmono bsegs ?mid' _ |- _ =>
         constr_eq mid mid'; exists mid; unfold bxq in MUA, WMA; split; [exact MUA|]; split; [exact WMA|]; split; [exact MUBx| exact WMBx] end.
Qed.
End CANSEC1.
