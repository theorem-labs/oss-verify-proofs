(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCHuff BzCHuffF1 BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0 CmpHmKit S0_cmp_hmA S0_cmp_hmB DecTac2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpHmKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_hmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_hmB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Strategy 1000 [upheap_loop downheap_loop hm_depth hm_rounds hm_winit hm_fill fill_h pneg hm_combine hm_lens hm_rescale hm_round hbMakeCodeLengths].
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0HM.
  Variable X : hmenv. Variable Q : machine_state -> Prop.
  Variables Jh Jw Jp : list byte.
  Hypothesis XOK : hmenv_ok X.
  Notation usp := (bv_unsigned (he_sp X)). Notation p := (bv_unsigned (he_sp X) - 5296)%Z.
  Notation A := (he_A X). Notation El := (he_El X). Notation Ef := (he_Ef X). Notation lb := (he_lb X). Notation fb := (he_fb X).
  Notation gp := (he_gp X). Notation tp := (he_tp X). Notation F := (he_F X). Notation fc := (he_fc X).
  Notation Jf := (he_Jf X). Notation freq := (he_freq X). Notation NF := (he_NF X).
  Notation Jl := (he_Jl X). Notation NL := (he_NL X). Notation len0 := (he_len X).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 (p - 32)) gp tp t0 t1 t2 (NOT (p + 24)) (NOT (p + 2088)) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (El + lb)) (Z_to_bv 64 (p + 4152)) (Z_to_bv 64 515) (Z_to_bv 64 (p + 2088)) (Z_to_bv 64 (p + 24))
         (Z_to_bv 64 (A + 1)) (Z_to_bv 64 516) (Z_to_bv 64 259) (NOT (p + 4152)) (Z_to_bv 64 129) t3 t4 t5 t6).
  Notation RA := (Z_to_bv 64 17).
  Notation SC := ([C8 (Z_to_bv 64 17); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 2060); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (El + lb - 1))]).
  Notation Wr := ([(El + lb, El + lb + A); (p + 24, p + 5192)])%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_rounds : forall (f r : nat) (me m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    let s := hp_rs len0 freq lb fb A r in
    hm_exec len0 freq lb fb A r -> hs_done (hm_rounds f A 17 lb s) = true ->
    (forall r', hm_exec len0 freq lb fb A r' -> round_facts A (hp_rs len0 freq lb fb A r')) ->
    u32arr s0segs m (p + 4152) (ovw (hs_heap s) Jh 260) -> u32arr s0segs m (p + 2088) (ovw (hs_weight s) Jw 516) -> u32arr s0segs m (p + 24) (ovw (hs_parent s) Jp 516) ->
    u8arr s0segs m El (ovb (hs_len s) Jl NL) -> rw_cells s0segs m (p - 32 + 8) SC -> mem_inv s0segs m ->
    munch Wr me m -> wmono s0segs me m ->
    (forall m' hF wF pF (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      u32arr s0segs m' (p + 4152) (ovw hF Jh 260) -> u32arr s0segs m' (p + 2088) (ovw wF Jw 516) -> u32arr s0segs m' (p + 24) (ovw pF Jp 516) ->
      u8arr s0segs m' El (ovb (hs_len (hm_rounds f A 17 lb s)) Jl NL) -> rw_cells s0segs m' (p - 32 + 8) SC -> mem_inv s0segs m' ->
      munch Wr me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x241c4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x23ce4) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH].
    { intros r me m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s EX DN. exfalso. subst s. cbn [hm_rounds] in DN. rewrite (EX r ltac:(lia)) in DN. discriminate. }
    intros r me m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s EX DN FACTS HEAP WGT PAR LEN SCc MI MU WM K.
    hmenv_open XOK.
    pose proof (EX r ltac:(lia)) as NDr. fold s in NDr.
    rewrite hm_rounds_S, NDr in DN, K.
    cps_destruct (FACTS r EX) as (RW & RCB & RPAR). fold s in RW, RCB, RPAR.
    pose proof (ovw_length (hs_heap s) Jh 260 ltac:(lia)) as LH. pose proof (ovw_length (hs_weight s) Jw 516 ltac:(lia)) as LW. pose proof (ovw_length (hs_parent s) Jp 516 ltac:(lia)) as LP.
    pose proof (ovb_length (hs_len s) Jl NL ltac:(lia)) as LL.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ 0 _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO1.
    wstep. try change (Z_to_le_bytes 4 0) with (le4 (Z_to_bv 64 0)). store_addr (p + 4152 + 4 * 0)%Z. ovw_store HEAP 0%Z 0%Z wval_lit.
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 2088) _ 0 _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    wstep. try change (Z_to_le_bytes 4 0) with (le4 (Z_to_bv 64 0)). store_addr (p + 2088 + 4 * 0)%Z. ovw_store WGT 0%Z 0%Z wval_lit.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 24) _ 0 _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO3 end.
    wstep. store_addr (p + 24 + 4 * 0)%Z. ovw_store PAR 0%Z (-2)%Z (rewrite unsigned_lit_mod32; reflexivity).
    change (zset (hs_heap s) 0 0) with (hr_h0 s) in HEAP. change (zset (hs_weight s) 0 0) with (hr_w0 s) in WGT. change (zset (hs_parent s) 0 (-2)) with (hr_p0 s) in PAR.
    (* [comment removed for export] *)
    wstep. wstep; if_false_z.
    wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    enter_with (S0_hm_fill X Q Jh Jw Jp XOK (Z.to_nat A) 1 (hr_h0 s) (hr_w0 s) (hr_p0 s) m1 m1);
      [st_eq| lia| lia| lia| | exact HEAP| exact WGT| exact PAR| exact SCc| exact MI| apply munch_refl| apply wmono_refl|].
    { replace (1 - 1)%Z with 0%Z by lia. apply hw_round0; [lia| exact RW]. }
    intros hf m2 q10 q11 q12 q13 q14 q15 q16 q17 Ehf HWf HEAP2 WGT2 PAR2 SC2 MI2 MU2 WM2.
    clear HEAP WGT PAR SCc MI. rename SC2 into SCc. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
    assert (HPf : hpar (pneg (hr_p0 s) 1 (Z.to_nat A)) A) by (unfold hr_p0; apply hpar_round0; lia).
    replace (1 - 1)%Z with 0%Z in Ehf by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_false_z.
    (* [comment removed for export] *)
    wstep. wstep; if_true_z.
    wstep. wstep; if_false_z.
    (* [comment removed for export] *)
    wstep. wstep.
    enter_with (S0_hm_combine X Q Jh Jw Jp XOK (Z.to_nat (A - 1)) hf (hr_w0 s) (pneg (hr_p0 s) 1 (Z.to_nat A)) A A m2 m2);
      [st_eq| lia| lia| lia| lia| lia| exact HWf| exact HPf| | exact HEAP2| exact WGT2| exact PAR2| exact MI2| apply munch_refl| apply wmono_refl|].
    { intros j Hj. rewrite Ehf. change (rf_cb (hr_cb A s j)). apply RCB. lia. }
    intros h' w' par' nN' m3 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 IT HnN' HW' HP' HEAP3 WGT3 PAR3 MI3 MU3 WM3.
    clear HEAP2 WGT2 PAR2 MI2. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    assert (CF : hr_cf A s = HMS h' w' par' 1 nN').
    { unfold hr_cf, hr_cb, hr_c0. rewrite <- Ehf. exact IT. }
    (* [comment removed for export] *)
    wstep. wstep; if_false_z.
    (* [comment removed for export] *)
    wstep. wstep.
    enter_with (S0_hm_lens X Q Jp XOK (Z.to_nat A) 1 (hs_len s) par' false nN' m3 m3);
      [st_eq| lia| lia| lia| lia| exact HP'| | exact LEN| exact PAR3| exact SCc| exact MI3| apply munch_refl| apply wmono_refl|].
    { intros xk Hxk. pose proof (RPAR xk ltac:(lia)) as PC. rewrite CF in PC. cbn [hm_parent] in PC. replace (2 * A - 1)%Z with nN' in PC by lia. exact PC. }
    intros len' tl' m4 z12 z13 z14 z15 EL LEN4 PAR4 SC4 MI4 MU4 WM4.
    clear LEN PAR3 SCc MI3. rename SC4 into SCc. transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    assert (RND : hm_round A 17 lb s = if tl' then HMST len' h' (hr_wr A s) par' false else HMST len' h' w' par' true).
    { rewrite hm_round_eq by lia. unfold hr_lens. rewrite CF. cbn [hm_parent hm_heap hm_weight]. rewrite <- EL. destruct tl'; reflexivity. }
    (* [comment removed for export] *)
    wstep. replace (Z.land (Z.b2z tl') 255) with (Z.b2z tl') by (destruct tl'; reflexivity).
    wstep; if_cases Kt; zify_cond_z Kt.
    - (* [comment removed for export] *)
      destruct tl'; [exfalso; cbn in Kt; lia|].
      rewrite RND in K. rewrite hm_rounds_stay in K by reflexivity. cbn [hs_len] in K.
      enter_with (K m4 h' w' par' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact HEAP3| exact WGT3| exact PAR4| exact LEN4| exact SCc| exact MI4| exact MU| exact WM].
    - destruct tl'; [|exfalso; cbn in Kt; lia].
      rewrite RND in K, DN.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      pose proof HW' as HW0. cps_destruct HW0 as (_ & _ & _ & WWf).
      enter_with (S0_hm_rescale X Q Jw XOK (Z.to_nat A) 1 w' m4 m4);
        [st_eq| lia| lia| lia| intros xk Hxk; apply WWf; lia| exact WGT3| exact MI4| apply munch_refl| apply wmono_refl|].
      intros m5 u10 u11 u12 u13 u14 WGT5 MI5 MU5 WM5.
      clear WGT3 MI4. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
      assert (EWR : hm_rescale (Z.to_nat A) w' 1 = hr_wr A s) by (unfold hr_wr; rewrite CF; reflexivity). rewrite EWR in WGT5.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (S r) me mm) end;
        [st_eq| | | exact FACTS| | | | | exact SCc| exact MI5| exact MU| exact WM|].
      + intros r' Hr'. destruct (Nat.eq_dec r' (S r)) as [->|NE]; [|apply EX; lia]. rewrite hp_rs_S. fold s. rewrite RND. reflexivity.
      + rewrite hp_rs_S. fold s. rewrite RND. exact DN.
      + rewrite hp_rs_S. fold s. rewrite RND. cbn [hs_heap]. exact HEAP3.
      + rewrite hp_rs_S. fold s. rewrite RND. cbn [hs_weight]. exact WGT5.
      + rewrite hp_rs_S. fold s. rewrite RND. cbn [hs_parent]. exact PAR4.
      + rewrite hp_rs_S. fold s. rewrite RND. cbn [hs_len]. exact LEN4.
      + intros m' hF wF pF. rewrite hp_rs_S. fold s. rewrite RND. exact (K m' hF wF pF).
  Qed.

End S0HM.

Lemma rw_cells_join2 : forall segs m A B cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells segs m A (cs1 ++ cs2).
Proof. intros segs m A B cs1 cs2 H1 H2 ->. apply rw_cells_app_iff_c. split; [exact H1| exact H2]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem S0_hbMakeCodeLengths : hbMakeCodeLengths_spec hm_facts S0C.
Proof.
  unfold hbMakeCodeLengths_spec. cbn [ci_segs ci_hbMakeCodeLengths ci_hi S0C]. intros until sv.
  intros Ha0 Ha1 Ha2 Ha3 LEN FREQ CM MI ST STK LO AL Hlb HlbN Hfb HfbN HA HEl HElC HEf HEfC HEf4 AP IAl IAf FRQ FACTS. subst a0 a1 a2 a3.
  bz_ceil; bz_params; unfold HM_FRAME, CEIL, apart in *.
  destruct (mod16_linq _ AL) as [qsp ALQ]. destruct (mod4_linq _ HEf4) as [qf EFQ].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  set (X := HE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Elen Efreq lb fb alphaSize NL NF lo qsp qf len freq Jl Jf sv m).
  assert (XOK : hmenv_ok X).
  { unfold hmenv_ok, CEILh. cbn [he_sp he_El he_Ef he_lb he_fb he_A he_NL he_NF he_lo he_qsp he_qf he_freq X].
    repeat (split; [first [lia| assumption]|]). exact FRQ. }
  destruct FACTS as [DN RFACTS].
  pose proof (ovb_length len Jl NL ltac:(lia)) as LL. pose proof (ovw_length freq Jf NF ltac:(lia)) as LF.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
  pose proof (munch_refl [(Elen + lb, Elen + lb + alphaSize); (bv_unsigned sp - 5328, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl s0segs m) as WM.
  (* [comment removed for export] *)
  carve_frame (2664 + 2664)%nat ST.
  pose proof (u8arr_of_rw_cells s0segs _ _ _ _ FR) as FRu.
  assert (LJ : Z.of_nat (length junk) = 5328%Z) by (pose proof (proj1 (proj1 (proj1 FR))) as W; cbn in W; lia).
  clear FR.
  u8take FRu P0 8%Z (bv_unsigned sp + -5320)%Z.
  u8take FRu SC1u 16%Z (bv_unsigned sp + -5304)%Z. u8take FRu SC2u 16%Z (bv_unsigned sp + -5288)%Z. u8take FRu SC3u 16%Z (bv_unsigned sp + -5272)%Z.
  u8take FRu PARu 2064%Z (bv_unsigned sp + -3208)%Z. u8take FRu WGTu 2064%Z (bv_unsigned sp + -1144)%Z.
  u8take FRu HEAPu 1040%Z (bv_unsigned sp + -104)%Z. rename FRu into SAVu.
  name_bytes P0 j0 8%Z. name_bytes SC1u jsc1 16%Z. name_bytes SC2u jsc2 16%Z. name_bytes SC3u jsc3 16%Z.
  name_bytes PARu Jp 2064%Z. name_bytes WGTu Jw 2064%Z. name_bytes HEAPu Jh 1040%Z. name_bytes SAVu jsav 104%Z.
  clear LJ junk.
  pose proof (rw_cells_of_u8arr s0segs _ _ _ SAVu) as SAV. clear SAVu. replace (length jsav) with 104%nat in SAV by lia.
  wstep.
  do 13 wstep.
  wstep. wstep.
  (* [comment removed for export] *)
  pose proof (rw_cells_of_u8arr s0segs _ _ _ SC1u) as SCJ1. clear SC1u. replace (length jsc1) with 16%nat in SCJ1 by lia.
  pose proof (rw_cells_of_u8arr s0segs _ _ _ SC2u) as SCJ2. clear SC2u. replace (length jsc2) with 16%nat in SCJ2 by lia.
  pose proof (rw_cells_of_u8arr s0segs _ _ _ SC3u) as SCJ3. clear SC3u. replace (length jsc3) with 16%nat in SCJ3 by lia.
  cps_destruct (rw_cells_junk16_C8 s0segs _ _ _ SCJ1) as (nd1 & rr1 & SC1). clear SCJ1.
  cps_destruct (rw_cells_junk16_C8 s0segs _ _ _ SCJ2) as (nd2 & rr2 & SC2). clear SCJ2.
  cps_destruct (rw_cells_junk16_C8 s0segs _ _ _ SCJ3) as (nd3 & rr3 & SC3). clear SCJ3.
  pose proof (rw_cells_join2 s0segs _ _ _ _ _ SC2 SC3 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SC23. clear SC2 SC3.
  pose proof (rw_cells_join2 s0segs _ _ _ _ _ SC1 SC23 ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as SC. clear SC1 SC23.
  cbn [app] in SC.
  pose proof (rw_cells_of_u8arr s0segs _ _ _ PARu) as PJ. clear PARu. replace (length Jp) with (Z.to_nat (4 * 516)) in PJ by lia.
  pose proof (ovw_init s0segs _ _ 516 _ PJ ltac:(lia)) as PAR. clear PJ. replace (bv_unsigned sp + -5272)%Z with (bv_unsigned sp - 5296 + 24)%Z in PAR by lia.
  pose proof (rw_cells_of_u8arr s0segs _ _ _ WGTu) as WJ. clear WGTu. replace (length Jw) with (Z.to_nat (4 * 516)) in WJ by lia.
  pose proof (ovw_init s0segs _ _ 516 _ WJ ltac:(lia)) as WGT. clear WJ. replace (bv_unsigned sp + -3208)%Z with (bv_unsigned sp - 5296 + 2088)%Z in WGT by lia.
  pose proof (rw_cells_of_u8arr s0segs _ _ _ HEAPu) as HJ. clear HEAPu. replace (length Jh) with (Z.to_nat (4 * 260)) in HJ by lia.
  pose proof (ovw_init s0segs _ _ 260 _ HJ ltac:(lia)) as HEAP. clear HJ. replace (bv_unsigned sp + -1144)%Z with (bv_unsigned sp - 5296 + 4152)%Z in HEAP by lia.
  pose proof (ovw_length znew Jp 516 ltac:(lia)) as LP. pose proof (ovw_length znew Jw 516 ltac:(lia)) as LW. pose proof (ovw_length znew Jh 260 ltac:(lia)) as LH.
  (* [comment removed for export] *)
  wstep. wstep. wstep.
  (* [comment removed for export] *)
  wstep; if_false_z.
  (* [comment removed for export] *)
  do 11 wstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (AL4 : Z.land (Efreq + 4 * fb) 3 = 0%Z) by (rewrite EFQ; replace (4 * qf + 4 * fb)%Z with (4 * (qf + fb))%Z by lia; apply land3_mul4; lia).
  enter_with (S0_hm_winit X _ Jw XOK (Z.to_nat alphaSize) 0 znew m1 m1);
    cbn [he_sp he_El he_Ef he_lb he_fb he_A he_NL he_NF he_gp he_tp he_F he_fc he_s0 he_s1 he_s2 he_s3 he_s4 he_s5 he_s6 he_s7 he_s8 he_s9 he_s10 he_s11 he_Jf he_freq X];
    [st_eq; rewrite ?AL4; repeat (match goal with |- context [?a <? ?b] => first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end); reflexivity| lia| lia| lia| exact WGT| exact FREQ| assumption| apply munch_refl| apply wmono_refl|].
  intros m2 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 WGT2 FREQ2 MI2 MU2 WM2.
  clear WGT FREQ. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
  (* [comment removed for export] *)
  replace (bv_unsigned sp + -104)%Z with (bv_unsigned sp - 5296 - 32 + 5224)%Z in SAV by lia.
  replace (bv_unsigned sp + -5328)%Z with (bv_unsigned sp - 5296 - 32)%Z in P0 by lia.
  replace (bv_unsigned sp + -5320)%Z with (bv_unsigned sp - 5296 - 32 + 8)%Z in SC by lia.
  change (hm_winit (Z.to_nat alphaSize) znew freq fb 0) with (hp_W0 freq fb alphaSize) in WGT2.
  pose proof (ovw_length (hp_W0 freq fb alphaSize) Jw 516 ltac:(lia)) as LW2.
  (* [comment removed for export] *)
  do 22 wstep.
  wstep. lit_store.
  do 5 wstep.
  wstep. lit_store.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
  assert (E1 : ((alphaSize + 1) * 4294967296 / 4294967296 + -1 = alphaSize)%Z) by (rewrite slli32_srli32; lia).
  assert (E4 : Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? alphaSize + 9223372036854775808)) 18446744073709551615) alphaSize = alphaSize).
  { replace (9223372036854775808 <? alphaSize + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia).
    change (0 - Z.b2z true)%Z with (-1)%Z. rewrite Z.land_m1_l. change 18446744073709551615%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite E1, E4 in SC. replace (Elen + lb + -1)%Z with (Elen + lb - 1)%Z in SC by lia.
  rewrite slli32_srli32.
  lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ ?xt0 ?xt1 ?xt2 _ _ ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7 _ _ _ _ _ _ _ _ _ _ ?xt3 ?xt4 ?xt5 ?xt6) _ _ _ _ _ _) =>
    enter_with (S0_hm_rounds X _ Jh Jw Jp XOK 40%nat 0%nat m5 m5 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6)
  end;
    cbn [he_sp he_El he_Ef he_lb he_fb he_A he_NL he_NF he_gp he_tp he_F he_fc he_len he_freq he_Jl X];
    [st_eq| | exact DN| exact RFACTS| exact HEAP| exact WGT2| exact PAR| exact LEN| exact SC| assumption| apply munch_refl| apply wmono_refl|].
  { intros r' Hr'. replace r' with 0%nat by lia. reflexivity. }
  intros m6 hF wF pF u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 HEAP6 WGT6 PAR6 LEN6 SC6 MI6 MU6 WM6.
  clear HEAP WGT2 PAR LEN SC. transport_after_call s0segs m5 m6 MU6 WM6. clear MU6 WM6.
  (* [comment removed for export] *)
  wstep. wstep. do 13 wstep. wstep. wstep.
  replace (Z_to_bv 64 (bv_unsigned sp - 5296 - 32 + 5328)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
  (* [comment removed for export] *)
  pose proof (stk_of_u8arr s0segs _ _ _ P0) as K0. stk_add ST K0.
  pose proof (stk_of_rw_cells s0segs _ _ _ SC6) as K1. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K1. stk_add ST K1.
  pose proof (stk_of_u32arr s0segs _ _ _ PAR6) as K2. rewrite ovw_length_nat in K2. stk_add ST K2.
  pose proof (stk_of_u32arr s0segs _ _ _ WGT6) as K3. rewrite ovw_length_nat in K3. stk_add ST K3.
  pose proof (stk_of_u32arr s0segs _ _ _ HEAP6) as K4. rewrite ovw_length_nat in K4. stk_add ST K4.
  pose proof (stk_of_rw_cells s0segs _ _ _ SAV) as K5. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K5. stk_add ST K5.
  lazymatch type of ST with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in ST by lia end.
  (* [comment removed for export] *)
  apply evt_done. unfold hbMakeCodeLengths_post. rewrite (hbMakeCodeLengths_pt len freq lb fb alphaSize znew znew eq_refl eq_refl).
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI6|]. split; [exact ST|]. exact LEN6.
Qed.

End ACeilS1.
