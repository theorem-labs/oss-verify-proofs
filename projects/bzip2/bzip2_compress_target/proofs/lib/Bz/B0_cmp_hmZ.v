(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCHuff BzArrD CmpMem CmpCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFsKit0 CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0 B0_cmp_hmV B0_cmp_hmA B0_cmp_hmC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section B0HM.
  Variable X : hmenv. Variable Y : ahenv. Variable Q : machine_state -> Prop.
  Variables Jh Jw Jp : list byte.
  Hypothesis XOK : hmenv_ok X. Hypothesis YOK : ahenv_ok X Y. Hypothesis YSX : ahenv_sepx X Y.
  Notation usp := (bv_unsigned (he_sp X)). Notation P := (ah_P Y). Notation FB := (ah_FB Y). Notation SHF := (ah_SHF Y).
  Notation HP := (ah_HP Y). Notation WT := (ah_WT Y). Notation PR := (ah_PR Y).
  Notation A := (he_A X). Notation El := (he_El X). Notation Ef := (he_Ef X). Notation lb := (he_lb X). Notation fb := (he_fb X).
  Notation gp := (he_gp X). Notation tp := (he_tp X). Notation F := (he_F X). Notation fc := (he_fc X).
  Notation Jf := (he_Jf X). Notation freq := (he_freq X). Notation NF := (he_NF X).
  Notation Jl := (he_Jl X). Notation NL := (he_NL X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  (* [comment removed for export] *)
  Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 PR) (Z_to_bv 64 516) (Z_to_bv 64 515) (NOT PR) (Z_to_bv 64 259) (NOT WT) (Z_to_bv 64 WT) (NOT HP) (Z_to_bv 64 HP) cSB t3 t4 t5 t6).
  (* [comment removed for export] *)
  Notation RQ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 cSB t3 t4 t5 t6).
  (* [comment removed for export] *)

  Notation len0 := (he_len X).
  Notation Wr := [(El + lb, El + lb + A); (HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064); (P + 72, P + 152)]%Z.
  Notation W3 := [(HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064); (P + 136, P + 152)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_rounds : forall (f r : nat) (me m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v136 v144 v160 v168 : word),
    let s := hp_rs len0 freq lb fb A r in
    hm_exec len0 freq lb fb A r -> hs_done (hm_rounds f A 17 lb s) = true ->
    (forall r', hm_exec len0 freq lb fb A r' -> round_facts A (hp_rs len0 freq lb fb A r')) ->
    u32arr b0segs m HP (ovw (hs_heap s) Jh 260) -> u32arr b0segs m WT (ovw (hs_weight s) Jw 516) -> u32arr b0segs m PR (ovw (hs_parent s) Jp 516) ->
    u8arr b0segs m El (ovb (hs_len s) Jl NL) -> rw_cells b0segs m (P + 24) (SLb X Y v136 v144 v160 v168) -> mem_inv b0segs m ->
    munch Wr me m -> wmono b0segs me m ->
    shzW b0segs Wr me El (El + NL) -> shzW b0segs Wr me HP (HP + 1040) -> shzW b0segs Wr me WT (WT + 2064) -> shzW b0segs Wr me PR (PR + 2064) ->
    (forall m' hF wF pF (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 u136 u144 : word),
      u32arr b0segs m' HP (ovw hF Jh 260) -> u32arr b0segs m' WT (ovw wF Jw 516) -> u32arr b0segs m' PR (ovw pF Jp 516) ->
      u8arr b0segs m' El (ovb (hs_len (hm_rounds f A 17 lb s)) Jl NL) -> rw_cells b0segs m' (P + 24) (SLb X Y u136 u144 v160 v168) -> mem_inv b0segs m' ->
      munch Wr me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa8bd8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa81e0) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH].
    { intros r me m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v136 v144 v160 v168 s EX DN. exfalso. subst s. cbn [hm_rounds] in DN. rewrite (EX r ltac:(lia)) in DN. discriminate. }
    intros r me m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v136 v144 v160 v168 s EX DN FACTS HEAP WGT PAR LEN SLB MI MU WM SHl SHh SHw SHp K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX.
    pose proof (EX r ltac:(lia)) as NDr. fold s in NDr.
    rewrite hm_rounds_S, NDr in DN, K.
    cps_destruct (FACTS r EX) as (RW & RCB & RPAR). fold s in RW, RCB, RPAR.
    pose proof (ovw_length (hs_heap s) Jh 260 ltac:(lia)) as LH. pose proof (ovw_length (hs_weight s) Jw 516 ltac:(lia)) as LW. pose proof (ovw_length (hs_parent s) Jp 516 ltac:(lia)) as LP.
    pose proof (ovb_length (hs_len s) Jl NL ltac:(lia)) as LL.
    unfold SLb in SLB.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok b0segs m HP _ 0 _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO1.
    wstep. try change (Z_to_le_bytes 4 0) with (le4 (Z_to_bv 64 0)). store_addr (HP + 4 * 0)%Z. ovw_store HEAP 0%Z 0%Z wval_lit.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok b0segs mm WT _ 0 _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    wstep. try change (Z_to_le_bytes 4 0) with (le4 (Z_to_bv 64 0)). store_addr (WT + 4 * 0)%Z. ovw_store WGT 0%Z 0%Z wval_lit.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok b0segs mm PR _ 0 _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO3 end.
    wstep. store_addr (PR + 4 * 0)%Z. ovw_store PAR 0%Z (-2)%Z (rewrite unsigned_lit_mod32; reflexivity).
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|]. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    enter_with (B0_hm_fill X Y Q Jh Jw Jp XOK YOK YSX (Z.to_nat A) 1 (hr_h0 s) (hr_w0 s) (hr_p0 s) m1 m1);
      [st_eq| lia| lia| lia| | exact HEAP| exact WGT| exact PAR| exact SLB| assumption| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs Wr _ me m1); [exact SHh| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wr _ me m1); [exact SHw| exact MU| a_sub_fp| lia| lia] |].
    { replace (1 - 1)%Z with 0%Z by lia. apply hw_round0; [lia| exact RW]. }
    intros hf m2 q10 q12 q13 q14 q15 q16 q17 Ehf HWf HEAP2 WGT2 PAR2 SLB2 MI2 MU2 WM2.
    clear HEAP WGT PAR SLB. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
    assert (HPf : hpar (pneg (hr_p0 s) 1 (Z.to_nat A)) A) by (unfold hr_p0; apply hpar_round0; lia).
    replace (1 - 1)%Z with 0%Z in Ehf by lia.
    unfold SLb in SLB2.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; lia|].
    wstep. wstep; if_cases K2; zify_cond_z K2; [|exfalso; lia].
    (* [comment removed for export] *)
    brun_to 0xa84d8%Z.
    enter_with (B0_hm_combine X Y Q Jh Jw Jp XOK YOK YSX (Z.to_nat (A - 1)) hf (hr_w0 s) (pneg (hr_p0 s) 1 (Z.to_nat A)) A A m2 m2);
      [st_eq| lia| lia| lia| lia| lia| exact HWf| exact HPf| | exact HEAP2| exact WGT2| exact PAR2| exact SLB2| exact MI2| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs Wr W3 me m2); [exact SHh| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wr W3 me m2); [exact SHw| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wr W3 me m2); [exact SHp| exact MU| a_sub_fp| lia| lia] |].
    { intros j Hj. rewrite Ehf. change (rf_cb (hr_cb A s j)). apply RCB. lia. }
    intros h' w' par' nN' m3 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 u136 u144 IT HnN' HW' HP' HEAP3 WGT3 PAR3 SLB3 MI3 MU3 WM3.
    clear HEAP2 WGT2 PAR2 SLB2 MI2. transport_after_call b0segs m2 m3 MU3 WM3. clear MU3 WM3.
    assert (CF : hr_cf A s = HMS h' w' par' 1 nN').
    { unfold hr_cf, hr_cb, hr_c0. rewrite <- Ehf. exact IT. }
    unfold SLb in SLB3.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K3; zify_cond_z K3; [exfalso; lia|]. wstep. wstep.
    enter_with (B0_hm_lens X Y Q Jp XOK YOK YSX (Z.to_nat A) 1 (hs_len s) par' false nN' m3 m3);
      [st_eq| lia| lia| lia| lia| exact HP'| | exact LEN| exact PAR3| exact SLB3| exact MI3| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs Wr _ me m3); [exact SHl| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wr _ me m3); [exact SHp| exact MU| a_sub_fp| lia| lia] |].
    { intros xk Hxk. pose proof (RPAR xk ltac:(lia)) as PC. rewrite CF in PC. cbn [hm_parent] in PC. replace (2 * A - 1)%Z with nN' in PC by lia. exact PC. }
    intros len' tl' m4 z10 z13 z14 z15 EL LEN4 PAR4 SLB4 MI4 MU4 WM4.
    clear LEN PAR3 SLB3 MI3. transport_after_call b0segs m3 m4 MU4 WM4. clear MU4 WM4.
    assert (RND : hm_round A 17 lb s = if tl' then HMST len' h' (hr_wr A s) par' false else HMST len' h' w' par' true).
    { rewrite hm_round_eq by lia. unfold hr_lens. rewrite CF. cbn [hm_parent hm_heap hm_weight]. rewrite <- EL. destruct tl'; reflexivity. }
    (* [comment removed for export] *)
    wstep. replace (Z.land (Z.b2z tl') 255) with (Z.b2z tl') by (destruct tl'; reflexivity).
    wstep; if_cases Kt; zify_cond_z Kt.
    - destruct tl'; [exfalso; cbn in Kt; lia|].
      rewrite RND in K. rewrite hm_rounds_stay in K by reflexivity. cbn [hs_len] in K.
      enter_with (K m4 h' w' par' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u136 u144); [st_eq| exact HEAP3| exact WGT3| exact PAR4| exact LEN4| exact SLB4| exact MI4| exact MU| exact WM].
    - destruct tl'; [|exfalso; cbn in Kt; lia].
      rewrite RND in K, DN.
      unfold SLb in SLB4.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      pose proof HW' as HW0. cps_destruct HW0 as (_ & _ & _ & WWf).
      enter_with (B0_hm_rescale X Y Q Jw XOK YOK YSX (Z.to_nat A) 1 w' m4 m4);
        [st_eq| lia| lia| lia| intros xk Hxk; apply WWf; lia| exact WGT3| exact MI4| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub b0segs Wr _ me m4); [exact SHw| exact MU| a_sub_fp| lia| lia] |].
      intros m5 u14 u15 u16 WGT5 MI5 MU5 WM5.
      clear WGT3 MI4. transport_after_call b0segs m4 m5 MU5 WM5. clear MU5 WM5.
      assert (EWR : hm_rescale (Z.to_nat A) w' 1 = hr_wr A s) by (unfold hr_wr; rewrite CF; reflexivity). rewrite EWR in WGT5.
      (* [comment removed for export] *)
      enter_with (IH (S r) me m5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u136 u144 v160 v168);
        [st_eq| | | exact FACTS| | | | | exact SLB4| exact MI5| exact MU| exact WM| exact SHl| exact SHh| exact SHw| exact SHp|].
      + intros r' Hr'. destruct (Nat.eq_dec r' (S r)) as [->|NE]; [|apply EX; lia]. rewrite hp_rs_S. fold s. rewrite RND. reflexivity.
      + rewrite hp_rs_S. fold s. rewrite RND. exact DN.
      + rewrite hp_rs_S. fold s. rewrite RND. cbn [hs_heap]. exact HEAP3.
      + rewrite hp_rs_S. fold s. rewrite RND. cbn [hs_weight]. exact WGT5.
      + rewrite hp_rs_S. fold s. rewrite RND. cbn [hs_parent]. exact PAR4.
      + rewrite hp_rs_S. fold s. rewrite RND. cbn [hs_len]. exact LEN4.
      + intros m' hF wF pF. rewrite hp_rs_S. fold s. rewrite RND. exact (K m' hF wF pF).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_body : forall (m : word -> option byte) (v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 : word),
    hm_facts len0 freq lb fb A ->
    rw_cells b0segs m (P + 24) [C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 (SHF + 424)); C8 (Z_to_bv 64 (SHF + 150)); C8 (Z_to_bv 64 (SHF + 4));
                                C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 A); C8 v104; C8 v112; C8 (Z_to_bv 64 17); C8 v128;
                                C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168; C8 (Z_to_bv 64 FB)] ->
    u32arr b0segs m HP (ovw znew Jh 260) -> u32arr b0segs m WT (ovw znew Jw 516) -> u32arr b0segs m PR (ovw znew Jp 516) ->
    u8arr b0segs m El (ovb len0 Jl NL) -> u32arr b0segs m Ef (ovw freq Jf NF) -> mem_inv b0segs m ->
    shzW b0segs Wr m El (El + NL) -> shzW b0segs Wr m HP (HP + 1040) -> shzW b0segs Wr m WT (WT + 2064) -> shzW b0segs Wr m PR (PR + 2064) ->
    shzW b0segs Wr m Ef (Ef + 4 * NF) ->
    (forall m' hF wF pF (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 u136 u144 : word),
      rw_cells b0segs m' (P + 24) (SLb X Y u136 u144 v160 v168) ->
      u32arr b0segs m' HP (ovw hF Jh 260) -> u32arr b0segs m' WT (ovw wF Jw 516) -> u32arr b0segs m' PR (ovw pF Jp 516) ->
      u8arr b0segs m' El (ovb (hs_len (hm_rounds 40 A 17 lb (hp_rs len0 freq lb fb A 0))) Jl NL) -> u32arr b0segs m' Ef (ovw freq Jf NF) -> mem_inv b0segs m' ->
      munch Wr m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RB (Z_to_bv 64 0xa8be4) t0 t1 t2 (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RQ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7
                         (Z_to_bv 64 (FB + 1200)) s9 (Z_to_bv 64 (Ef + 4 * fb)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa80a4) fc None m (seg_rom b0segs)).
  Proof.
    intros m v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 HMF SL HEAP WGT PAR LEN FREQ MI SHl SHh SHw SHp SHf K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX.
    destruct HMF as [DN RFACTS].
    pose proof (munch_refl Wr m) as MU. pose proof (wmono_refl b0segs m) as WM.
    pose proof (ovw_length znew Jh 260 ltac:(lia)) as LH. pose proof (ovw_length znew Jw 516 ltac:(lia)) as LW. pose proof (ovw_length znew Jp 516 ltac:(lia)) as LP.
    pose proof (ovw_length freq Jf NF ltac:(lia)) as LF. pose proof (ovb_length len0 Jl NL ltac:(lia)) as LL.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep; flags. wstep.
    replace (Z.land (Ef + 4 * fb) 3) with 0%Z by (rewrite XEF4; replace (4 * he_qf X + 4 * fb)%Z with (4 * (he_qf X + fb))%Z by lia; symmetry; apply land3_mul4; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep; flags. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    enter_with (B0_hm_winit X Y Q Jw XOK YOK YSX (Z.to_nat A) 0 znew m m);
      [st_eq| lia| lia| lia| exact WGT| exact FREQ| exact MI| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs Wr _ m m); [exact SHw| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wr _ m m); [exact SHf| exact MU| a_sub_fp| lia| lia] |].
    intros m2 y5 y6 WGT2 FREQ2 MI2 MU2 WM2.
    clear WGT FREQ MI. transport_after_call b0segs m m2 MU2 WM2. clear MU2 WM2.
    change (hm_winit (Z.to_nat A) znew freq fb 0) with (hp_W0 freq fb A) in WGT2.
    pose proof (ovw_length (hp_W0 freq fb A) Jw 516 ltac:(lia)) as LW2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep; flags.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. lit_store. wstep. wstep.
    replace (Z.land 18446744073709551615 A) with A by (rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    (* [comment removed for export] *)
    wstep. wstep. rewrite slli32_srli32. wstep. wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
    assert (SLB : rw_cells b0segs m5 (P + 24) (SLb X Y v136 v144 v160 v168)).
    { unfold SLb. replace (A + 1 - 1)%Z with A in SL by lia. replace (FB + 1200 + 4)%Z with (WT + 4)%Z in SL by lia. replace (El + lb + -1)%Z with (El + lb - 1)%Z in SL by lia. exact SL. }
    clear SL.
    enter_with (B0_hm_rounds 40%nat 0%nat m5 m5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v136 v144 v160 v168);
      [st_eq| | exact DN| exact RFACTS| exact HEAP| exact WGT2| exact PAR| exact LEN| exact SLB| assumption| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs Wr _ m m5); [exact SHl| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wr _ m m5); [exact SHh| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wr _ m m5); [exact SHw| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wr _ m m5); [exact SHp| exact MU| a_sub_fp| lia| lia] |].
    { intros r' Hr'. replace r' with 0%nat by lia. reflexivity. }
    intros m6 hF wF pF u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 u136 u144 HEAP6 WGT6 PAR6 LEN6 SLB6 MI6 MU6 WM6.
    clear HEAP WGT2 PAR LEN SLB. transport_after_call b0segs m5 m6 MU6 WM6. clear MU6 WM6.
    (* [comment removed for export] *)
    pose proof SLB6 as SLu. unfold SLb in SLu.
    wstep. wstep. wstep.
    enter_with (K m6 hF wF pF _ _ _ _ _ _ _ _ _ _ _ _ _ u136 u144); [st_eq| exact SLB6| exact HEAP6| exact WGT6| exact PAR6| exact LEN6| exact FREQ2| exact MI6| exact MU| exact WM].
  Qed.
End B0HM.

End ACeilS1.
