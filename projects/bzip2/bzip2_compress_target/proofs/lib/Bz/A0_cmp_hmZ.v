(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCHuff BzArrD CmpMem CmpCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFsKit0 CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut A0_cmp_hmV A0_cmp_hmA A0_cmp_hmC.
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

Section A0HM.
  Variable X : hmenv. Variable Y : ahenv. Variable Q : machine_state -> Prop.
  Variables Jh Jw Jp : list byte.
  Hypothesis XOK : hmenv_ok X. Hypothesis YOK : ahenv_ok X Y. Hypothesis YSX : ahenv_sepx X Y.
  Notation usp := (bv_unsigned (he_sp X)). Notation P := (ah_P Y).
  Notation HP := (ah_HP Y). Notation WT := (ah_WT Y). Notation PR := (ah_PR Y).
  Notation A := (he_A X). Notation El := (he_El X). Notation Ef := (he_Ef X). Notation lb := (he_lb X). Notation fb := (he_fb X).
  Notation gp := (he_gp X). Notation tp := (he_tp X). Notation F := (he_F X). Notation fc := (he_fc X).
  Notation Jf := (he_Jf X). Notation freq := (he_freq X). Notation NF := (he_NF X).
  Notation Jl := (he_Jl X). Notation NL := (he_NL X).
  Notation cSB := (Z_to_bv 64 2147450880).
  (* [comment removed for export] *)
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 2) (Z_to_bv 64 17) (Z_to_bv 64 (A + 1)) s5 (Z_to_bv 64 HP) (Z_to_bv 64 WT) (Z_to_bv 64 (El + lb - 1)) (Z_to_bv 64 PR)
         (Z_to_bv 64 A) cSB t3 t4 t5 t6).
  Notation Wh := [(HP, HP + 1040)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Notation len0 := (he_len X).
  Notation SHF := (ah_SHF Y).
  Notation Wr := [(El + lb, El + lb + A); (HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hm_round : forall (s : hmst) (v96 v104 : word) (me m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
    round_facts A s ->
    u32arr a0segs m HP (ovw (hr_h0 s) Jh 260) -> u32arr a0segs m WT (ovw (hr_w0 s) Jw 516) ->
    u32arr a0segs m PR (ovw (pneg (hr_p0 s) 1 (Z.to_nat A)) Jp 516) ->
    u8arr a0segs m El (ovb (hs_len s) Jl NL) -> rw_cells a0segs m (P + 8) (SLh X Y v96 v104) -> mem_inv a0segs m ->
    munch Wr me m -> wmono a0segs me m ->
    shzW a0segs Wr me El (El + NL) -> shzW a0segs Wr me HP (HP + 1040) -> shzW a0segs Wr me WT (WT + 2064) -> shzW a0segs Wr me PR (PR + 2064) ->
    (* [comment removed for export] *)
    (forall m' hF wF pF (t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
      hs_done (hm_round A 17 lb s) = true ->
      u32arr a0segs m' HP (ovw hF Jh 260) -> u32arr a0segs m' WT (ovw wF Jw 516) -> u32arr a0segs m' PR (ovw pF Jp 516) ->
      u8arr a0segs m' El (ovb (hs_len (hm_round A 17 lb s)) Jl NL) -> rw_cells a0segs m' (P + 8) (SLh X Y v96 v104) -> mem_inv a0segs m' ->
      munch Wr me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR (Z_to_bv 64 0x9dd7c) t0 t1 t2 (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x559e4) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (t0 t1 t2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
      let s' := hm_round A 17 lb s in
      hs_done s' = false ->
      u32arr a0segs m' HP (ovw (hr_h0 s') Jh 260) -> u32arr a0segs m' WT (ovw (hr_w0 s') Jw 516) -> u32arr a0segs m' PR (ovw (hr_p0 s') Jp 516) ->
      u8arr a0segs m' El (ovb (hs_len s') Jl NL) -> rw_cells a0segs m' (P + 8) (SLh X Y v96 v104) -> mem_inv a0segs m' ->
      munch Wr me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR (Z_to_bv 64 0x9d404) t0 t1 t2 (Z_to_bv 64 (PR + 4)) (Z_to_bv 64 255) (Z_to_bv 64 (A * 4)) a3 a4 a5 a6 a7 s5 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6) F (Z_to_bv 64 0x9d404) fc None m (seg_rom a0segs)).
  Proof.
    intros s v96 v104 me m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 FACTS HEAP WGT PAR LEN SL MI MU WM SHl SHh SHw SHp KD KL.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX.
    cps_destruct FACTS as (RW & RCB & RPAR).
    pose proof (ovw_length (hr_h0 s) Jh 260 ltac:(lia)) as LH. pose proof (ovw_length (hr_w0 s) Jw 516 ltac:(lia)) as LW.
    pose proof (ovb_length (hs_len s) Jl NL ltac:(lia)) as LL.
    unfold SLh in SL.
    (* [comment removed for export] *)
    wstep. wstep.
    enter_with (A0_hm_fill X Y Q Jh Jw XOK YOK YSX (Z.to_nat A) 1 (hr_h0 s) (hr_w0 s) m m);
      [st_eq| lia| lia| lia| | exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl| | |].
    { replace (1 - 1)%Z with 0%Z by lia. apply hw_round0; [lia| exact RW]. }
    { eapply (shzW_sub a0segs Wr _ me m); [exact SHh| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shzW_sub a0segs Wr _ me m); [exact SHw| exact MU| a_sub_fp| lia| lia]. }
    intros hf m2 q10 q11 q14 q15 q16 q17 Ehf HWf HEAP2 WGT2 MI2 MU2 WM2.
    clear HEAP WGT MI. transport_after_call a0segs m m2 MU2 WM2. clear MU2 WM2.
    assert (HPf : hpar (pneg (hr_p0 s) 1 (Z.to_nat A)) A) by (unfold hr_p0; apply hpar_round0; lia).
    replace (1 - 1)%Z with 0%Z in Ehf by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [|exfalso; lia].
    (* [comment removed for export] *)
    wstep. wstep; if_cases K2; zify_cond_z K2; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep. wstep.
    enter_with (A0_hm_combine X Y Q Jh Jw Jp XOK YOK YSX (Z.to_nat (A - 1)) hf (hr_w0 s) (pneg (hr_p0 s) 1 (Z.to_nat A)) A A m2 m2);
      [st_eq| lia| lia| lia| lia| lia| exact HWf| exact HPf| | exact HEAP2| exact WGT2| exact PAR| exact MI2| apply munch_refl| apply wmono_refl| | | |].
    { intros j Hj. rewrite Ehf. change (rf_cb (hr_cb A s j)). apply RCB. lia. }
    { eapply (shzW_sub a0segs Wr _ me m2); [exact SHh| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shzW_sub a0segs Wr _ me m2); [exact SHw| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shzW_sub a0segs Wr _ me m2); [exact SHp| exact MU| a_sub_fp| lia| lia]. }
    intros h' w' par' nN' m3 y1 y6 y7 y10 y11 y12 y16 y17 y21 y28 y29 y30 y31 IT HnN' HW' HP' HEAP3 WGT3 PAR3 MI3 MU3 WM3.
    clear HEAP2 WGT2 PAR MI2. transport_after_call a0segs m2 m3 MU3 WM3. clear MU3 WM3.
    assert (CF : hr_cf A s = HMS h' w' par' 1 nN').
    { unfold hr_cf, hr_cb, hr_c0. rewrite <- Ehf. exact IT. }
    (* [comment removed for export] *)
    wstep. wstep; if_cases K3; zify_cond_z K3; [|exfalso; lia].
    (* [comment removed for export] *)
    wstep. wstep.
    enter_with (A0_hm_lens X Y Q Jp XOK YOK YSX (Z.to_nat A) 1 (hs_len s) par' false nN' m3 m3);
      [st_eq| lia| lia| lia| lia| exact HP'| | exact LEN| exact PAR3| exact MI3| apply munch_refl| apply wmono_refl| | |].
    { intros xk Hxk. pose proof (RPAR xk ltac:(lia)) as PC. rewrite CF in PC. cbn [hm_parent] in PC. replace (2 * A - 1)%Z with nN' in PC by lia. exact PC. }
    { eapply (shzW_sub a0segs Wr _ me m3); [exact SHl| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shzW_sub a0segs Wr _ me m3); [exact SHp| exact MU| a_sub_fp| lia| lia]. }
    intros len' tl' m4 z10 z13 z14 EL LEN4 PAR4 MI4 MU4 WM4.
    clear LEN PAR3 MI3. transport_after_call a0segs m3 m4 MU4 WM4. clear MU4 WM4.
    assert (RND : hm_round A 17 lb s = if tl' then HMST len' h' (hr_wr A s) par' false else HMST len' h' w' par' true).
    { rewrite hm_round_eq by lia. unfold hr_lens. rewrite CF. cbn [hm_parent hm_heap hm_weight]. rewrite <- EL. destruct tl'; reflexivity. }
    (* [comment removed for export] *)
    wstep. replace (Z.land (Z.b2z tl') 255) with (Z.b2z tl') by (destruct tl'; reflexivity).
    wstep; if_cases Kt; zify_cond_z Kt.
    - (* [comment removed for export] *)
      destruct tl'; [exfalso; cbn in Kt; lia|].
      wstep. wstep. wstep.
      enter_with (KD m4 h' w' par' _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| rewrite RND; reflexivity| exact HEAP3| exact WGT3| exact PAR4| rewrite RND; cbn [hs_len]; exact LEN4| exact SL| exact MI4| exact MU| exact WM].
    - destruct tl'; [|exfalso; cbn in Kt; lia].
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      pose proof HW' as HW0. cps_destruct HW0 as (_ & _ & _ & WWf).
      enter_with (A0_hm_rescale X Y Q Jw XOK YOK YSX (Z.to_nat A) 1 w' m4 m4);
        [st_eq| lia| lia| lia| intros xk Hxk; apply WWf; lia| exact WGT3| exact MI4| apply munch_refl| apply wmono_refl| |].
      { eapply (shzW_sub a0segs Wr _ me m4); [exact SHw| exact MU| a_sub_fp| lia| lia]. }
      intros m5 u13 u14 WGT5 MI5 MU5 WM5.
      clear WGT3 MI4. transport_after_call a0segs m4 m5 MU5 WM5. clear MU5 WM5.
      assert (EWR : hm_rescale (Z.to_nat A) w' 1 = hr_wr A s) by (unfold hr_wr; rewrite CF; reflexivity). rewrite EWR in WGT5.
      pose proof (ovw_length (hr_wr A s) Jw 516 ltac:(lia)) as LW5. pose proof (ovw_length h' Jh 260 ltac:(lia)) as LH5. pose proof (ovw_length par' Jp 516 ltac:(lia)) as LP5.
      (* [comment removed for export] *)
      pose proof (u32arr_store_ok a0segs m5 HP _ 0 _ HEAP3 ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO1.
      wstep. try change (Z_to_le_bytes 4 0) with (le4 (Z_to_bv 64 0)). store_addr (HP + 4 * 0)%Z. ovw_store HEAP3 0%Z 0%Z wval_lit.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok a0segs mm WT _ 0 _ WGT5 ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. try change (Z_to_le_bytes 4 0) with (le4 (Z_to_bv 64 0)). store_addr (WT + 4 * 0)%Z. ovw_store WGT5 0%Z 0%Z wval_lit.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok a0segs mm PR _ 0 _ PAR4 ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO3 end.
      wstep. store_addr (PR + 4 * 0)%Z. ovw_store PAR4 0%Z (-2)%Z (rewrite unsigned_lit_mod32; reflexivity).
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (KL mm _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| rewrite RND; reflexivity| | | | | exact SL| assumption| exact MU| exact WM].
      + rewrite RND. unfold hr_h0. cbn [hs_heap]. exact HEAP3.
      + rewrite RND. unfold hr_w0. cbn [hs_weight]. exact WGT5.
      + rewrite RND. unfold hr_p0. cbn [hs_parent]. exact PAR4.
      + rewrite RND. cbn [hs_len]. exact LEN4.
  Qed.
End A0HM.

End ACeilS1.
