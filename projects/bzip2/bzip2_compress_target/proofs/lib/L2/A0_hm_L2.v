(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import RT_iface D_defs D_kit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCHuff BzArrD CmpMem CmpHmKit AsanKit A0_cmp_hmV A0_cmp_hmZ.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Module KMem := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib.Mem.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition xF (X : hmenv) (F' : bvmap 5 word) (fc' : bv 32) : hmenv :=
  HE (he_ra X) (he_sp X) (he_gp X) (he_tp X) (he_s0 X) (he_s1 X) (he_s2 X) (he_s3 X) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (he_s8 X)
     (he_s9 X) (he_s10 X) (he_s11 X) F' fc' (he_El X) (he_Ef X) (he_lb X) (he_fb X) (he_A X) (he_NL X) (he_NF X) (he_lo X) (he_qsp X) (he_qf X)
     (he_len X) (he_freq X) (he_Jl X) (he_Jf X) (he_sv X) (he_m0 X).

Section HML2.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Variable X : hmenv. Variable Y : ahenv. Variables Jh Jw Jp : list byte.
Hypothesis XOK : hmenv_ok X. Hypothesis YOK : ahenv_ok X Y. Hypothesis YSX : ahenv_sepx X Y.
Hypothesis AX : sanchor (ah_FB Y) (ah_SHF Y).

Lemma xF_ok : forall F' fc', hmenv_ok (xF X F' fc').
Proof. intros. exact XOK. Qed.
Lemma xF_aok : forall F' fc', ahenv_ok (xF X F' fc') Y.
Proof. intros. exact YOK. Qed.
Lemma xF_sepx : forall F' fc', ahenv_sepx (xF X F' fc') Y.
Proof. intros. exact YSX. Qed.

Notation usp := (bv_unsigned (he_sp X)). Notation P := (ah_P Y). Notation FB := (ah_FB Y). Notation SHF := (ah_SHF Y).
Notation HP := (ah_HP Y). Notation WT := (ah_WT Y). Notation PR := (ah_PR Y).
Notation A := (he_A X). Notation El := (he_El X). Notation lb := (he_lb X). Notation fb := (he_fb X). Notation NL := (he_NL X).
Notation gp := (he_gp X). Notation tp := (he_tp X). Notation lo := (he_lo X).
Notation Jl := (he_Jl X). Notation len0 := (he_len X). Notation freq := (he_freq X).
Notation Wr := [(El + lb, El + lb + A); (HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)].
Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 :=
  (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 2) (Z_to_bv 64 17) (Z_to_bv 64 (A + 1)) s5 (Z_to_bv 64 HP) (Z_to_bv 64 WT) (Z_to_bv 64 (El + lb - 1)) (Z_to_bv 64 PR)
       (Z_to_bv 64 A) (Z_to_bv 64 2147450880) t3 t4 t5 t6).

(* [comment removed for export] *)
Definition hmI (m : mem) (h w p len : zarr) (v96 v104 : word) : Prop :=
  u32arr a0segs m HP (ovw h Jh 260) /\ u32arr a0segs m WT (ovw w Jw 516) /\ u32arr a0segs m PR (ovw p Jp 516) /\
  u8arr a0segs m El (ovb len Jl NL) /\ rw_cells a0segs m (P + 8) (SLh X Y v96 v104) /\
  bytes_at a0segs m (SHF + 4) (repeat z8 130) /\ bytes_at a0segs m (SHF + 150) (repeat z8 258) /\ bytes_at a0segs m (SHF + 424) (repeat z8 258).

Variables (Σ : rts RT) (PMc : Model -> Prop) (fr : list (Z * nat)) (pl nl : Z) (m0 : mem).
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Hypothesis FRM : rt_frames RT Σ = (FB, 7%nat) :: fr.
Hypothesis LIV : In (pl, nl) (rt_live RT Σ). Hypothesis LIV1 : pl <= El. Hypothesis LIV2 : El + NL + 7 <= pl + nl.
Hypothesis LOW : rt_sp0 RT Σ - STACK_WIN <= lo. Hypothesis LOR : lo + RT_STACK <= P. Hypothesis SPT : usp + 16 <= USTACK_TOP.
Hypothesis SPA : P mod 16 = 0.

(* [comment removed for export] *)
Definition hmAG (m m' : mem) : Prop := agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) P x /\ outside Wr x) m m'.

(* [comment removed for export] *)
Ltac agr AG :=
  eapply agree_sub; [exact AG|]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbv beta in *;
  rewrite ?length_firstn, ?length_skipn, ?ovw_length_nat, ?ovb_length_nat, ?repeat_length in Hx;
  cbn [NCells.cells_size NCells.csize SLh Nat.add] in Hx; lia.

(* [comment removed for export] *)
Definition hmQD (m1 : mem) (s : hmst) (v96 v104 : word) F1 fc1 (ms : machine_state) : Prop :=
  exists (m2 : mem) hF wF pF (t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
    ms = MS (RR (Z_to_bv 64 0x9dd7c) t0 t1 t2 (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6)
            F1 (Z_to_bv 64 0x559e4) fc1 None m2 (seg_rom a0segs)
    /\ hs_done (hm_round A 17 lb s) = true
    /\ u32arr a0segs m2 HP (ovw hF Jh 260) /\ u32arr a0segs m2 WT (ovw wF Jw 516) /\ u32arr a0segs m2 PR (ovw pF Jp 516)
    /\ u8arr a0segs m2 El (ovb (hs_len (hm_round A 17 lb s)) Jl NL) /\ rw_cells a0segs m2 (P + 8) (SLh X Y v96 v104)
    /\ NMem.mem_inv a0segs m2 /\ munch Wr m1 m2 /\ wmono a0segs m1 m2.
Definition hmQL (m1 : mem) (s : hmst) (v96 v104 : word) F1 fc1 (ms : machine_state) : Prop :=
  exists (m2 : mem) (t0 t1 t2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
    ms = MS (RR (Z_to_bv 64 0x9d404) t0 t1 t2 (Z_to_bv 64 (PR + 4)) (Z_to_bv 64 255) (Z_to_bv 64 (A * 4)) a3 a4 a5 a6 a7 s5 t3 t4 t5 t6)
            F1 (Z_to_bv 64 0x52ea0) fc1 None m2 (seg_rom a0segs)
    /\ hs_done (hm_round A 17 lb s) = false
    /\ u32arr a0segs m2 HP (ovw (hr_h0 (hm_round A 17 lb s)) Jh 260) /\ u32arr a0segs m2 WT (ovw (hr_w0 (hm_round A 17 lb s)) Jw 516)
    /\ u32arr a0segs m2 PR (ovw (hr_p0 (hm_round A 17 lb s)) Jp 516)
    /\ u8arr a0segs m2 El (ovb (hs_len (hm_round A 17 lb s)) Jl NL) /\ rw_cells a0segs m2 (P + 8) (SLh X Y v96 v104)
    /\ NMem.mem_inv a0segs m2 /\ munch Wr m1 m2 /\ wmono a0segs m1 m2.

Lemma hm_rounds_cps : forall (f r : nat) (m : mem) (v96 v104 : word) F fc (t0 t1 t2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
  let s := hp_rs len0 freq lb fb A r in
  hm_exec len0 freq lb fb A r -> hs_done (hm_rounds f A 17 lb s) = true ->
  (forall r', hm_exec len0 freq lb fb A r' -> round_facts A (hp_rs len0 freq lb fb A r')) ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P ->
  hmI m (hr_h0 s) (hr_w0 s) (hr_p0 s) (hs_len s) v96 v104 -> hmAG m0 m ->
  cps asegs (ASTA RT Σ PMc (eq (MS (RR (Z_to_bv 64 0x9d404) t0 t1 t2 (Z_to_bv 64 (PR + 4)) (Z_to_bv 64 255) (Z_to_bv 64 (A * 4)) a3 a4 a5 a6 a7 s5 t3 t4 t5 t6)
                                       F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))))
    (fun c => exists (m' : mem) hF wF pF F' fc' (t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
       ASTA RT Σ PMc (eq (MS (RR (Z_to_bv 64 0x9dd7c) t0 t1 t2 (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6)
                             F' (Z_to_bv 64 0x559e4) fc' None m' (seg_rom a0segs))) c
       /\ ART RT Σ m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo P
       /\ hmI m' hF wF pF (hs_len (hm_rounds f A 17 lb s)) v96 v104 /\ hmAG m0 m').
Proof.
  induction f as [|f IH]; intros r m v96 v104 F fc t0 t1 t2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 s EX DN FACTS ART0 MI0 ST0 HI AG0.
  { exfalso. subst s. cbn [hm_rounds] in DN. rewrite (EX r (le_n r)) in DN. discriminate. }
  intros T c Hc Hk.
  hmenv_open XOK. ahenv_open YOK.
  destruct HI as (HEAP & WGT & PAR & LEN & SL & SHH & SHW & SHP).
  assert (INF : In (FB, 7%nat) (rt_frames RT Σ)) by (rewrite FRM; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m FB 7 ART0 INF) as (FR0 & FR1 & FR2 & FR3). change (fs_size 7) with 8192 in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  (* [comment removed for export] *)
  destruct (par_before_memset a0segs m PR (hr_p0 s) Jp 516 A PAR ltac:(lia) ltac:(lia)) as (PAR0 & PARj & PAR2).
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (MSET Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (PR + 4) (A * 4) (Z_to_bv 8 255) lo FDO MST).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold CEILh in *. pose proof alloc_ceiling_range. lia.
    - lia.
    - (* [comment removed for export] *)
      destruct AX as [AX1 AX2].
      pose proof (acc_of_zero_shadow a0segs m FB SHF 424 258 AX1 AX2 ltac:(lia) ltac:(lia) SHP) as ACCP.
      split; [intros _; split|split].
      + apply (acc_sub a0segs m _ _ _ _ ACCP); lia.
      + right; left. exists FB, 7%nat. change (fs_size 7) with 8192. split; [exact INF| lia].
      + intros i Hi. right; right; right; left. exists FB, 7%nat. change (fs_size 7) with 8192. split; [exact INF|].
        lia.
      + destruct PARj as [_ W]. cbn [NCells.cells_size NCells.csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia.
        replace (A * 4) with (4 * A) by lia. exact W.
    - exact ART0.
    - exact MI0.
    - unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST0|]. split; [exact LOW|]. split; [exact LOR|]. split; [lia| exact SPA]. }
  intros c1 Hc1. unfold icpt_post in Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & BY1) & Hc1'). clear Hc1.
  destruct RS1 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite unsigned_lit in ST1, PRES1 by lia.
  rewrite (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib.MState.ret_pc_even 0x9d404 ltac:(lia) eq_refl) in Hc1'.
  (* [comment removed for export] *)
  pose proof (af_fshadow_apart RT AF Σ m FB 7 ART0 INF) as (_ & FSF). pose proof (FSF FB 7%nat INF) as FSELF. change (fs_size 7) with 8192 in FSELF.
  destruct AX as [AX1 AX2].
  assert (SHFB : shad FB = SHF) by (unfold shad, SHB; lia).
  assert (SHFE : shad (FB + 8192) = SHF + 1024) by (unfold shad, SHB; rewrite AX2; clear - AX1; Z.div_mod_to_equations; lia).
  rewrite SHFB, SHFE in FSELF.
  assert (AGF : agree_on (fun x => FB <= x < FB + 8184 /\ ~ (PR + 4 <= x < PR + 4 + A * 4)) m m1).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES1). intros x [Hx Hn]. split; [| exact Hn].
    right; right; right; left. exists FB, 7%nat. change (fs_size 7) with 8192. split; [exact INF| lia]. }
  assert (AGS : agree_on (fun x => P <= x < USTACK_TOP) m m1).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES1). intros x Hx. split; [left; exact Hx| unfold STACK_WIN, USTACK_TOP in *; lia]. }
  assert (AGL : agree_on (fun x => pl <= x < pl + nl) m m1).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES1). intros x Hx. split; [right; right; left; exists pl, nl; split; [exact LIV| exact Hx]|].
    destruct (FR3 pl nl LIV); lia. }
  assert (AGH : agree_on (fun x => SHF <= x < SHF + 1024) m m1).
  { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES1). intros x Hx. split; [| lia].
    right; right; right; right. exists FB, 7%nat. change (fs_size 7) with 8192. rewrite SHFB, SHFE. split; [exact INF| exact Hx]. }
  (* [comment removed for export] *)
  pose proof (n_u32arr_agree a0segs m m1 HP _ HEAP ltac:(agr AGF)) as HEAP1.
  pose proof (n_u32arr_agree a0segs m m1 WT _ WGT ltac:(agr AGF)) as WGT1.
  pose proof (n_u32arr_agree a0segs m m1 PR _ PAR0 ltac:(agr AGF)) as PAR01.
  pose proof (n_u32arr_agree a0segs m m1 _ _ PAR2 ltac:(agr AGF)) as PAR21.
  pose proof (n_u8arr_agree a0segs m m1 El _ LEN ltac:(agr AGL)) as LEN1.
  pose proof (n_rw_cells_agree a0segs m m1 _ _ SL ltac:(agr AGS)) as SL1.
  pose proof (bytes_at_agree a0segs m m1 _ _ SHH ltac:(agr AGH)) as SHH1.
  pose proof (bytes_at_agree a0segs m m1 _ _ SHW ltac:(agr AGH)) as SHW1.
  pose proof (bytes_at_agree a0segs m m1 _ _ SHP ltac:(agr AGH)) as SHP1.
  (* [comment removed for export] *)
  assert (PARm : rw_cells a0segs m1 (PR + 4) [CB (Z.to_nat (4 * A)) (repeat (Z_to_bv 8 255) (Z.to_nat (4 * A)))]).
  { replace (A * 4) with (4 * A) in BY1 by lia. split; [split|].
    - cbn. split; [apply repeat_length| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY1.
    - destruct PARj as [_ W]. exact (wr_at_transport a0segs m m1 _ _ W WM1). }
  pose proof (u32arr_m1_init a0segs m1 (PR + 4) A PARm ltac:(lia)) as PAR11.
  pose proof (par_after_fill a0segs m1 PR (hr_p0 s) Jp 516 A PAR01 PAR11 PAR21 ltac:(lia) ltac:(lia)) as PARn.
  (* [comment removed for export] *)
  pose proof (af_frames_hi RT AF Σ m1 FB 7 ART1 INF) as FHI. change (fs_size 7) with 8192 in FHI.
  pose proof (af_live_offshadow RT AF Σ m1 pl nl ART1 LIV) as LHI.
  destruct (af_live_slack RT AF Σ m1 pl nl ART1 LIV) as (slack & _ & _ & LTOP).
  destruct (af_acc_live RT AF Σ m1 pl nl ART1 LIV) as [(PL0 & _ & _) ACCL].
  assert (AFP : app_fp Wr).
  { cbn [app_fp]. unfold SH_LO, SH_HI. repeat split; lia. }
  assert (TOP47 : rt_sp0 RT Σ - STACK_WIN <= 2^47) by (unfold STACK_WIN, USTACK_TOP in *; lia).
  assert (SHl : shzW a0segs Wr m1 El (El + NL)).
  { apply (shzW_of_acc a0segs Wr m1 pl nl El (El + NL) ACCL AFP); [lia| lia| lia|]. clear - LIV2. Z.div_mod_to_equations. lia. }
  pose proof (acc_of_zero_shadow a0segs m1 FB SHF 4 130 AX1 AX2 ltac:(lia) ltac:(lia) SHH1) as ACCH.
  pose proof (acc_of_zero_shadow a0segs m1 FB SHF 150 258 AX1 AX2 ltac:(lia) ltac:(lia) SHW1) as ACCW.
  pose proof (acc_of_zero_shadow a0segs m1 FB SHF 424 258 AX1 AX2 ltac:(lia) ltac:(lia) SHP1) as ACCP1.
  assert (SHh : shzW a0segs Wr m1 HP (HP + 1040)).
  { apply (shzW_of_acc a0segs Wr m1 _ _ HP (HP + 1040) ACCH AFP); [lia| lia| lia|]. clear - YHP AX1. Z.div_mod_to_equations. lia. }
  assert (SHw : shzW a0segs Wr m1 WT (WT + 2064)).
  { apply (shzW_of_acc a0segs Wr m1 _ _ WT (WT + 2064) ACCW AFP); [lia| lia| lia|]. clear - YWT AX1. Z.div_mod_to_equations. lia. }
  assert (SHp : shzW a0segs Wr m1 PR (PR + 2064)).
  { apply (shzW_of_acc a0segs Wr m1 _ _ PR (PR + 2064) ACCP1 AFP); [lia| lia| lia|]. clear - YPR AX1. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T c1 (l1_lift RT AF Σ PMc (fun ms => hmQD m1 s v96 v104 F1 fc1 ms \/ hmQL m1 s v96 v104 F1 fc1 ms) _ MST
            (A0_hm_round (xF X F1 fc1) Y _ Jh Jw Jp (xF_ok F1 fc1) (xF_aok F1 fc1) (xF_sepx F1 fc1) s v96 v104 m1 m1
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (FACTS r EX) HEAP1 WGT1 PARn LEN1 SL1 (kmem_inv_N _ _ MI1) (munch_refl _ _) (wmono_refl _ _) SHl SHh SHw SHp _ _)) Hc1' _).
  { (* [comment removed for export] *)
    intros m2 hF wF pF x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 DNr H1 H2 H3 H4 H5 H6 H7 H8.
    apply evt_done. left. exists m2, hF, wF, pF, x5, x6, x7, x12, x13, x14, x15, x16, x17, x21, x28, x29, x30, x31.
    split; [reflexivity|]. split; [exact DNr|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    split; [exact H5|]. split; [exact H6|]. split; [exact H7| exact H8]. }
  { (* [comment removed for export] *)
    intros m2 x5 x6 x7 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31. cbv zeta. intros DNr H1 H2 H3 H4 H5 H6 H7 H8.
    apply evt_done. right. exists m2, x5, x6, x7, x13, x14, x15, x16, x17, x21, x28, x29, x30, x31.
    split; [reflexivity|]. split; [exact DNr|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    split; [exact H5|]. split; [exact H6|]. split; [exact H7| exact H8]. }
  intros c2 Hc2.
  pose proof (EX r (le_n r)) as NDr. fold s in NDr.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & QQ & Hc2'). clear Hc2.
  (* [comment removed for export] *)
  assert (COMMON : forall m2, NMem.mem_inv a0segs m2 -> munch Wr m1 m2 -> wmono a0segs m1 m2 ->
            ART RT Σ m2 /\ KMem.mem_inv asegs m2 /\ stk asegs m2 lo P /\ hmAG m0 m2
            /\ bytes_at a0segs m2 (SHF + 4) (repeat z8 130) /\ bytes_at a0segs m2 (SHF + 150) (repeat z8 258) /\ bytes_at a0segs m2 (SHF + 424) (repeat z8 258)).
  { intros m2 NMI2 MU2 WM2.
    pose proof (af_fshadow_apart RT AF Σ m1 FB 7 ART1 INF) as (FSL & _). pose proof (FSL pl nl LIV) as FSLV. change (fs_size 7) with 8192 in FSLV.
    rewrite SHFB, SHFE in FSLV.
    assert (AGO : agree_on (fun x => outside Wr x) m1 m2) by (intros a Ha; exact (MU2 a Ha)).
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - apply (art_of_munch RT AF Σ m1 m2 Wr P ART1 ltac:(lia) MU2 WM2). per_interval.
      + right; right; left. exists pl, nl. split; [exact LIV| lia].
      + right; right; right; left. exists FB, 7%nat. change (fs_size 7) with 8192. split; [exact INF| lia].
      + right; right; right; left. exists FB, 7%nat. change (fs_size 7) with 8192. split; [exact INF| lia].
      + right; right; right; left. exists FB, 7%nat. change (fs_size 7) with 8192. split; [exact INF| lia].
    - apply (kmem_inv_munch asegs Wr m1 m2 MI1 MU2 NMI2). cbn [fp_below]. unfold KMem.UTOP, STACK_WIN, USTACK_TOP in *. repeat split; lia.
    - apply (stk_agree_nw asegs m1 m2 lo P ST1). eapply agree_sub; [exact AGO|]. intros x Hx. cbv beta in *. cbn [outside]. unfold CEILh in *. repeat split; lia.
    - intros a [Ha Ho]. rewrite (MU2 a Ho). rewrite (PRES1 a Ha); [exact (AG0 a (conj Ha Ho))|]. cbn [outside] in Ho. lia.
    - apply (bytes_at_agree a0segs m1 m2 _ _ SHH1). eapply agree_sub; [exact AGO|]. intros x Hx. cbv beta in *. rewrite repeat_length in Hx. cbn [outside]. repeat split; lia.
    - apply (bytes_at_agree a0segs m1 m2 _ _ SHW1). eapply agree_sub; [exact AGO|]. intros x Hx. cbv beta in *. rewrite repeat_length in Hx. cbn [outside]. repeat split; lia.
    - apply (bytes_at_agree a0segs m1 m2 _ _ SHP1). eapply agree_sub; [exact AGO|]. intros x Hx. cbv beta in *. rewrite repeat_length in Hx. cbn [outside]. repeat split; lia. }
  destruct QQ as [QD|QL].
  - (* [comment removed for export] *)
    destruct QD as (m2 & hF & wF & pF & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x21 & x28 & x29 & x30 & x31 & -> & DNr & H1 & H2 & H3 & H4 & H5 & NMI2 & MU2 & WM2).
    destruct (COMMON m2 NMI2 MU2 WM2) as (ART2 & MI2 & ST2 & AG2 & S1 & S2 & S3).
    apply Hk. exists m2, hF, wF, pF, F1, fc1, x5, x6, x7, x12, x13, x14, x15, x16, x17, x21, x28, x29, x30, x31.
    split; [exact Hc2'|]. split; [exact ART2|]. split; [exact MI2|]. split; [exact ST2|]. split; [| exact AG2].
    rewrite hm_rounds_S, NDr, hm_rounds_stay by exact DNr.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact S1|]. split; [exact S2| exact S3].
  - (* [comment removed for export] *)
    destruct QL as (m2 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x21 & x28 & x29 & x30 & x31 & -> & DNr & H1 & H2 & H3 & H4 & H5 & NMI2 & MU2 & WM2).
    destruct (COMMON m2 NMI2 MU2 WM2) as (ART2 & MI2 & ST2 & AG2 & S1 & S2 & S3).
    rewrite hm_rounds_S, NDr in DN.
    assert (EX' : hm_exec len0 freq lb fb A (S r)).
    { intros r' Hr'. destruct (Nat.eq_dec r' (S r)) as [->|NE]; [| apply EX; lia]. rewrite hp_rs_S. fold s. exact DNr. }
    refine (cps_realizes asegs _ _ T c2 (IH (S r) m2 v96 v104 F1 fc1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 EX' _ FACTS ART2 MI2 ST2 _ AG2) Hc2' _).
    + rewrite hp_rs_S. fold s. exact DN.
    + rewrite hp_rs_S. fold s. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact S1|]. split; [exact S2| exact S3].
    + intros c3 Hc3. apply Hk. rewrite hp_rs_S in Hc3. fold s in Hc3. rewrite hm_rounds_S, NDr. exact Hc3.
Qed.
End HML2.
