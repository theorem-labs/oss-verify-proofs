(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Frame MState PropExec Cells Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import SpecFrame SpecLeib WalkL Init SegL FxOut PrintfFmt2.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module AC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module EF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Module MSt := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module APx := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Module PrintfSeg2.
Import PrintfFmt2.

Lemma ro_one8 : forall m A v, AM.bytes_at asegs m A (AM.le8 v) -> AS.ro_cells asegs m A [AC.C8 v].
Proof. intros m A v H. split; [cbn; auto|]. cbn [AC.cells_bytes AC.cbytes]. rewrite app_nil_r. exact H. Qed.
Lemma ro_cons8 : forall m A v cs, AM.bytes_at asegs m A (AM.le8 v) -> AS.ro_cells asegs m (A + 8) cs -> AS.ro_cells asegs m A (AC.C8 v :: cs).
Proof.
  intros m A v cs H [WF B]. split; [cbn; auto|]. cbn [AC.cells_bytes AC.cbytes]. apply AM.bytes_at_app. split; [exact H|].
  replace (Z.of_nat (length (AM.le8 v))) with 8 by reflexivity. exact B.
Qed.

Lemma ro_cons8' : forall m A B v cs, AM.bytes_at asegs m A (AM.le8 v) -> B = A + 8 -> AS.ro_cells asegs m B cs -> AS.ro_cells asegs m A (AC.C8 v :: cs).
Proof. intros m A B v cs H -> K. apply ro_cons8; assumption. Qed.

Lemma stk_winv : forall m m' lo hi wl wh, AF.stk asegs m lo hi -> WalkL.winv asegs wl wh m m' -> AF.stk asegs m' lo hi.
Proof.
  intros m m' lo hi wl wh (S0 & S1 & SV) (_ & WM & RM). split; [exact S0|]. split; [exact S1|].
  intros a Ha. destruct (SV a Ha) as [W (b & RD)]. split; [apply WM; exact W|].
  destruct (AM.mrd asegs m' (AM.wa a)) as [b'|] eqn:Q; [exists b'; reflexivity|]. exfalso. apply (RM (AM.wa a)); [rewrite RD; discriminate| exact Q].
Qed.

Definition nz (b : byte) : Prop := bv_unsigned b <> 0.
Definition fmt_post (RA FMT : Z) (LEN : nat) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' va m' str,
    ms' = MSt.MS (AF.mkR ra' (Z_to_bv 64 (bv_unsigned sp + -640)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (bv_unsigned sp + -512)) s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x73ae8) fc None m' (APx.seg_rom asegs)
    /\ AF.munch [(bv_unsigned sp - 1280, bv_unsigned sp)] m m' /\ AF.wmono asegs m m' /\ AM.mem_inv asegs m'
    /\ AF.stk asegs m' lo (bv_unsigned sp)
    /\ AS.ro_cells asegs m' (bv_unsigned sp + -640) [AC.C8 (Z_to_bv 64 0); AC.C8 (Z_to_bv 64 0)]
    /\ AS.ro_cells asegs m' (bv_unsigned sp + -600)
         [AC.C8 s9; AC.C8 s8; AC.C8 s7; AC.C8 s6; AC.C8 s5; AC.C8 s4; AC.C8 s3; AC.C8 (Z_to_bv 64 0); AC.C8 (Z_to_bv 64 FMT); AC.C8 va;
          AC.C8 (Z_to_bv 64 0x73470)]
    /\ AS.ro_cells asegs m' (bv_unsigned sp + -112) [AC.C8 s2; AC.C8 s1; AC.C8 s0; AC.C8 (Z_to_bv 64 0x73420)]
    /\ AS.ro_cells asegs m' (bv_unsigned sp + -72) [AC.C8 (Z_to_bv 64 RA)]
    /\ length str = LEN /\ Forall nz str /\ AM.bytes_at asegs m' (bv_unsigned sp + -512) (str ++ [Z_to_bv 8 0]).

Lemma den_lit : forall E (c : int), den E (VL (wlit c)) = Z_to_bv 64 (to_Z c).
Proof. intros E c. cbn [den]. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Section S.
Variable RNG : EF.footprint.

Theorem printf_fmt_seg : forall (RA FMT : int) (LEN : nat) (xf : rf sv),
  checkP RA FMT LEN xf = true -> rf_get xf X0 = VL wzero -> (LEN <= 400)%nat ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  let R := AF.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
  let ms := MSt.MS R F (Z_to_bv 64 0x733e0) fc None m (APx.seg_rom asegs) in
  (forall r, rget (core_of ms) (reg_of_r5 r) = den (SegL.envW R F fc) (rf_get xf r)) ->
  bv_unsigned fc < 32 -> bv_unsigned sp < 2 ^ 63 ->
  AF.stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 1280 -> 0x62f000 <= lo ->
  AM.mem_inv asegs m ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (AM.wa i) = None) ->
  EF.rng RNG (bv_unsigned sp - 1280) 1280 -> rng_aimg RNG ->
  EF.evtF asegs RNG (fmt_post (to_Z RA) (to_Z FMT) LEN sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms.
Proof.
  intros RA FMT LEN xf CHK HX0 LENB ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R ms
         HR FC SPHI STK LO IMG MI RELRO RW RI.
  set (E := SegL.envW R F fc).
  assert (E1 : ev E 1%uint63 = sp) by reflexivity. idtac "E1 ok".
  eapply EF.evtF_mono.
  - apply (SegL.fx_segment_L ITABW ITABW_ok RNG R F ENTRYP fc m xf FACTSP 400%uint63 ROOMP lo [STOPP] FUELP (finP RA FMT LEN) 6%nat).
    + exact CHK.
    + idtac "chk ok". apply SpecLeib.shape_mkR.
    + intros st H. unfold finP in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
      destruct (s_resv st); [reflexivity| discriminate| discriminate].
    + unfold ROOMP. split; reflexivity.
    + exact HX0.
    + exact HR.
    + exact FC.
    + constructor; [| constructor]. cbn [fact_holds]. fold E. rewrite E1. rewrite !wlit_ok.
      change (to_Z 6483968%uint63) with 6483968. change (to_Z 9223372036854775807%uint63) with 9223372036854775807. lia.
    + exact STK.
    + exact LO.
    + exact IMG.
    + exact MI.
    + exact RELRO.
    + exact RW.
    + exact RI.
  - idtac "part1 ok". cbv beta. intros ms' (st' & mo' & R' & m' & EQ & HS' & FIN & INV & MI'). fold E in HS'.
    change (bv_unsigned (rget (core_of ms) (reg_of_r5 X2))) with (bv_unsigned sp) in INV. unfold ROOMP in INV.
    unfold finP in FIN. apply andb_prop in FIN as [FIN TXT]. apply andb_prop in FIN as [FIN SLT]. apply andb_prop in FIN as [FIN RGS].
    apply andb_prop in FIN as [PC _]. apply Uint63.eqb_correct in PC.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. rewrite bv_modulus_64 in SPR. unfold two64 in SPR.
    assert (SPLO : 0x62f000 + 1280 <= bv_unsigned sp) by lia.
    idtac "fin split ok".

    pose proof (so_regs _ _ _ _ _ _ HS') as SR. rewrite EQ in SR. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MSt.MS] in SR.
    cbn [forallb REGS fst snd] in RGS. repeat (apply andb_prop in RGS as [? RGS]).
    repeat match goal with H : sv_eqb _ _ = true |- _ => apply ValP.sv_eqb_eq in H end.
    assert (DV : forall z, - 1280 <= z < 0 -> den E (VP 1%uint63 (Z2w z)) = Z_to_bv 64 (bv_unsigned sp + z)).
    { intros z Hz. apply bv_eq. rewrite (FxOut.den_VP_Z2w E 1%uint63 z) by (rewrite ?E1; unfold two63, two64; lia).
      rewrite E1, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold two64; lia). reflexivity. }
    assert (Q2 : SpecLeib.rg R' 2 = Z_to_bv 64 (bv_unsigned sp + -640)).
    { pose proof (SR X2) as Q. rewrite H in Q. rewrite (DV (-640)) in Q by lia. exact Q. }
    assert (Q18 : SpecLeib.rg R' 18 = Z_to_bv 64 (bv_unsigned sp + -512)).
    { pose proof (SR X18) as Q. rewrite H0 in Q. rewrite (DV (-512)) in Q by lia. exact Q. }
    assert (Q3 : SpecLeib.rg R' 3 = gp) by (pose proof (SR X3) as Q; rewrite H1, SegL.den_VPz in Q; exact Q).
    assert (Q4 : SpecLeib.rg R' 4 = tp) by (pose proof (SR X4) as Q; rewrite H2, SegL.den_VPz in Q; exact Q).
    assert (Q26 : SpecLeib.rg R' 26 = s10) by (pose proof (SR X26) as Q; rewrite H3, SegL.den_VPz in Q; exact Q).
    assert (Q27 : SpecLeib.rg R' 27 = s11) by (pose proof (SR X27) as Q; rewrite H4, SegL.den_VPz in Q; exact Q).
    idtac "regs ok".

    assert (SL : forall off v, In (off, v) (SLOTS RA FMT) -> AM.bytes_at asegs m' (bv_unsigned sp + off) (AM.le8 (den E v))).
    { intros off v HIn. rewrite forallb_forall in SLT. specialize (SLT _ HIn). cbn [fst snd] in SLT.
      assert (OR : - 1280 <= off < 0 /\ off <= -8).
      { unfold SLOTS in HIn. cbn [In] in HIn. repeat (destruct HIn as [HIn|HIn]; [injection HIn as <- <-; lia|]). contradiction. }
      assert (EM : ms_mem ms' = m') by (rewrite EQ; reflexivity).
      rewrite <- EM. apply (FxOut.slot_ok_sound asegs WInit.OPSW E st' ms' mo' _ v _ HS' SLT).
      - rewrite (DV off) by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold two64; lia). reflexivity.
      - lia. }
    assert (DX : forall k x, ev E k = x -> den E (VP k wzero) = x) by (intros k x <-; apply SegL.den_VPz).
    idtac "slots ok".

    assert (EM : ms_mem ms' = m') by (rewrite EQ; reflexivity).
    destruct (FxOut.text_ok_sound asegs WInit.OPSW E st' ms' mo' 1%uint63 (-512) LEN HS' TXT) as (str & SLEN & SNZ & SB).
    { unfold two63; lia. }
    { unfold two63; lia. }
    { rewrite E1. lia. }
    { rewrite E1. unfold two64. lia. }
    rewrite E1, EM in SB.
    idtac "text ok".
    destruct INV as (MU & WM & RM).
    assert (IN : forall off v, (fun p => In p (SLOTS RA FMT)) (off, v) -> In (off, v) (SLOTS RA FMT)) by (intros; assumption).
    Ltac inslot := unfold SLOTS; cbn [In]; repeat (first [left; reflexivity | right]).
    pose proof (SL (-640) _ ltac:(inslot)) as S640. pose proof (SL (-632) _ ltac:(inslot)) as S632.
    pose proof (SL (-600) _ ltac:(inslot)) as S600. pose proof (SL (-592) _ ltac:(inslot)) as S592. pose proof (SL (-584) _ ltac:(inslot)) as S584.
    pose proof (SL (-576) _ ltac:(inslot)) as S576. pose proof (SL (-568) _ ltac:(inslot)) as S568. pose proof (SL (-560) _ ltac:(inslot)) as S560.
    pose proof (SL (-552) _ ltac:(inslot)) as S552. pose proof (SL (-544) _ ltac:(inslot)) as S544. pose proof (SL (-536) _ ltac:(inslot)) as S536.
    pose proof (SL (-528) _ ltac:(inslot)) as S528. pose proof (SL (-520) _ ltac:(inslot)) as S520.
    pose proof (SL (-112) _ ltac:(inslot)) as S112. pose proof (SL (-104) _ ltac:(inslot)) as S104. pose proof (SL (-96) _ ltac:(inslot)) as S96.
    pose proof (SL (-88) _ ltac:(inslot)) as S88. pose proof (SL (-72) _ ltac:(inslot)) as S72.
    idtac "slot facts ok".
    rewrite (DX 125%uint63 s9 eq_refl) in S600. rewrite (DX 124%uint63 s8 eq_refl) in S592. rewrite (DX 123%uint63 s7 eq_refl) in S584.
    rewrite (DX 122%uint63 s6 eq_refl) in S576. rewrite (DX 121%uint63 s5 eq_refl) in S568. rewrite (DX 120%uint63 s4 eq_refl) in S560.
    rewrite (DX 119%uint63 s3 eq_refl) in S552. rewrite (DX 118%uint63 s2 eq_refl) in S112. rewrite (DX 109%uint63 s1 eq_refl) in S104.
    rewrite (DX 108%uint63 s0 eq_refl) in S96.
    rewrite den_lit in S536, S520, S88, S72.
    change (den E (VL wzero)) with (Z_to_bv 64 0) in S640, S632, S544.
    change (to_Z 472176%uint63) with 0x73470 in S520. change (to_Z 472096%uint63) with 0x73420 in S88.
    idtac "slot values ok".
    unfold SpecLeib.mkR_of in EQ. rewrite Q2, Q18, Q3, Q4, Q26, Q27, PC in EQ. change (to_Z STOPP) with 0x73ae8 in EQ.
    do 25 eexists. exists (den E (VP 1%uint63 (Z2w (-56)))), m', str.
    split; [exact EQ|]. idtac "EQ ok".
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split; [eapply stk_winv; [exact STK| split; [exact MU| split; [exact WM| exact RM]]]|].
    split. { apply (ro_cons8' _ _ (bv_unsigned sp + -632) _ _ S640 ltac:(lia)). apply ro_one8. exact S632. }
    split. { apply (ro_cons8' _ _ (bv_unsigned sp + -592) _ _ S600 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -584) _ _ S592 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -576) _ _ S584 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -568) _ _ S576 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -560) _ _ S568 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -552) _ _ S560 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -544) _ _ S552 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -536) _ _ S544 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -528) _ _ S536 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -520) _ _ S528 ltac:(lia)).
             apply ro_one8. exact S520. }
    split. { apply (ro_cons8' _ _ (bv_unsigned sp + -104) _ _ S112 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -96) _ _ S104 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -88) _ _ S96 ltac:(lia)). apply ro_one8. exact S88. }
    split. { apply ro_one8. exact S72. }
    split; [exact SLEN|]. split; [exact SNZ| exact SB].
Time Qed.
End S.
End PrintfSeg2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import ABase.TwinB.
Import SpecFrame.TwinB SpecLeib.TwinB WalkL.TwinB Init.TwinB SegL.TwinB FxOut.TwinB PrintfFmt2.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module AC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module EF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Module MSt := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module APx := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Module PrintfSeg2.
Import PrintfFmt2.TwinB.PrintfFmt2.

Lemma ro_one8 : forall m A v, AM.bytes_at bsegs m A (AM.le8 v) -> AS.ro_cells bsegs m A [AC.C8 v].
Proof. intros m A v H. split; [cbn; auto|]. cbn [AC.cells_bytes AC.cbytes]. rewrite app_nil_r. exact H. Qed.
Lemma ro_cons8 : forall m A v cs, AM.bytes_at bsegs m A (AM.le8 v) -> AS.ro_cells bsegs m (A + 8) cs -> AS.ro_cells bsegs m A (AC.C8 v :: cs).
Proof.
  intros m A v cs H [WF B]. split; [cbn; auto|]. cbn [AC.cells_bytes AC.cbytes]. apply AM.bytes_at_app. split; [exact H|].
  replace (Z.of_nat (length (AM.le8 v))) with 8 by reflexivity. exact B.
Qed.

Lemma ro_cons8' : forall m A B v cs, AM.bytes_at bsegs m A (AM.le8 v) -> B = A + 8 -> AS.ro_cells bsegs m B cs -> AS.ro_cells bsegs m A (AC.C8 v :: cs).
Proof. intros m A B v cs H -> K. apply ro_cons8; assumption. Qed.

Lemma stk_winv : forall m m' lo hi wl wh, AF.stk bsegs m lo hi -> WalkL.TwinB.WalkL.winv bsegs wl wh m m' -> AF.stk bsegs m' lo hi.
Proof.
  intros m m' lo hi wl wh (S0 & S1 & SV) (_ & WM & RM). split; [exact S0|]. split; [exact S1|].
  intros a Ha. destruct (SV a Ha) as [W (b & RD)]. split; [apply WM; exact W|].
  destruct (AM.mrd bsegs m' (AM.wa a)) as [b'|] eqn:Q; [exists b'; reflexivity|]. exfalso. apply (RM (AM.wa a)); [rewrite RD; discriminate| exact Q].
Qed.

Definition nz (b : byte) : Prop := bv_unsigned b <> 0.
Definition fmt_post (RA FMT : Z) (LEN : nat) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' va m' str,
    ms' = MSt.MS (AF.mkR ra' (Z_to_bv 64 (bv_unsigned sp + -640)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (bv_unsigned sp + -512)) s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x74478) fc None m' (APx.seg_rom bsegs)
    /\ AF.munch [(bv_unsigned sp - 1280, bv_unsigned sp)] m m' /\ AF.wmono bsegs m m' /\ AM.mem_inv bsegs m'
    /\ AF.stk bsegs m' lo (bv_unsigned sp)
    /\ AS.ro_cells bsegs m' (bv_unsigned sp + -640) [AC.C8 (Z_to_bv 64 0); AC.C8 (Z_to_bv 64 0)]
    /\ AS.ro_cells bsegs m' (bv_unsigned sp + -600)
         [AC.C8 s9; AC.C8 s8; AC.C8 s7; AC.C8 s6; AC.C8 s5; AC.C8 s4; AC.C8 s3; AC.C8 (Z_to_bv 64 0); AC.C8 (Z_to_bv 64 FMT); AC.C8 va;
          AC.C8 (Z_to_bv 64 0x73e00)]
    /\ AS.ro_cells bsegs m' (bv_unsigned sp + -112) [AC.C8 s2; AC.C8 s1; AC.C8 s0; AC.C8 (Z_to_bv 64 0x73db0)]
    /\ AS.ro_cells bsegs m' (bv_unsigned sp + -72) [AC.C8 (Z_to_bv 64 RA)]
    /\ length str = LEN /\ Forall nz str /\ AM.bytes_at bsegs m' (bv_unsigned sp + -512) (str ++ [Z_to_bv 8 0]).

Lemma den_lit : forall E (c : int), den E (VL (wlit c)) = Z_to_bv 64 (to_Z c).
Proof. intros E c. cbn [den]. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Section S.
Variable RNG : EF.footprint.

Theorem printf_fmt_seg : forall (RA FMT : int) (LEN : nat) (xf : rf sv),
  checkP RA FMT LEN xf = true -> rf_get xf X0 = VL wzero -> (LEN <= 400)%nat ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  let R := AF.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
  let ms := MSt.MS R F (Z_to_bv 64 0x73d70) fc None m (APx.seg_rom bsegs) in
  (forall r, rget (core_of ms) (reg_of_r5 r) = den (SegL.TwinB.SegL.envW R F fc) (rf_get xf r)) ->
  bv_unsigned fc < 32 -> bv_unsigned sp < 2 ^ 63 ->
  AF.stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 1280 -> 0x631000 <= lo ->
  AM.mem_inv bsegs m ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (AM.wa i) = None) ->
  EF.rng RNG (bv_unsigned sp - 1280) 1280 -> rng_aimg RNG ->
  EF.evtF bsegs RNG (fmt_post (to_Z RA) (to_Z FMT) LEN sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms.
Proof.
  intros RA FMT LEN xf CHK HX0 LENB ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R ms
         HR FC SPHI STK LO IMG MI RELRO RW RI.
  set (E := SegL.TwinB.SegL.envW R F fc).
  assert (E1 : ev E 1%uint63 = sp) by reflexivity. idtac "E1 ok".
  eapply EF.evtF_mono.
  - apply (SegL.TwinB.SegL.fx_segment_L ITABW ITABW_ok RNG R F ENTRYP fc m xf FACTSP 400%uint63 ROOMP lo [STOPP] FUELP (finP RA FMT LEN) 6%nat).
    + exact CHK.
    + idtac "chk ok". apply SpecLeib.TwinB.SpecLeib.shape_mkR.
    + intros st H. unfold finP in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
      destruct (s_resv st); [reflexivity| discriminate| discriminate].
    + unfold ROOMP. split; reflexivity.
    + exact HX0.
    + exact HR.
    + exact FC.
    + constructor; [| constructor]. cbn [fact_holds]. fold E. rewrite E1. rewrite !wlit_ok.
      change (to_Z 6492160%uint63) with 6492160. change (to_Z 9223372036854775807%uint63) with 9223372036854775807. lia.
    + exact STK.
    + exact LO.
    + exact IMG.
    + exact MI.
    + exact RELRO.
    + exact RW.
    + exact RI.
  - idtac "part1 ok". cbv beta. intros ms' (st' & mo' & R' & m' & EQ & HS' & FIN & INV & MI'). fold E in HS'.
    change (bv_unsigned (rget (core_of ms) (reg_of_r5 X2))) with (bv_unsigned sp) in INV. unfold ROOMP in INV.
    unfold finP in FIN. apply andb_prop in FIN as [FIN TXT]. apply andb_prop in FIN as [FIN SLT]. apply andb_prop in FIN as [FIN RGS].
    apply andb_prop in FIN as [PC _]. apply Uint63.eqb_correct in PC.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. rewrite bv_modulus_64 in SPR. unfold two64 in SPR.
    assert (SPLO : 0x631000 + 1280 <= bv_unsigned sp) by lia.
    idtac "fin split ok".

    pose proof (so_regs _ _ _ _ _ _ HS') as SR. rewrite EQ in SR. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MSt.MS] in SR.
    cbn [forallb REGS fst snd] in RGS. repeat (apply andb_prop in RGS as [? RGS]).
    repeat match goal with H : sv_eqb _ _ = true |- _ => apply ValP.sv_eqb_eq in H end.
    assert (DV : forall z, - 1280 <= z < 0 -> den E (VP 1%uint63 (Z2w z)) = Z_to_bv 64 (bv_unsigned sp + z)).
    { intros z Hz. apply bv_eq. rewrite (FxOut.TwinB.FxOut.den_VP_Z2w E 1%uint63 z) by (rewrite ?E1; unfold two63, two64; lia).
      rewrite E1, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold two64; lia). reflexivity. }
    assert (Q2 : SpecLeib.TwinB.SpecLeib.rg R' 2 = Z_to_bv 64 (bv_unsigned sp + -640)).
    { pose proof (SR X2) as Q. rewrite H in Q. rewrite (DV (-640)) in Q by lia. exact Q. }
    assert (Q18 : SpecLeib.TwinB.SpecLeib.rg R' 18 = Z_to_bv 64 (bv_unsigned sp + -512)).
    { pose proof (SR X18) as Q. rewrite H0 in Q. rewrite (DV (-512)) in Q by lia. exact Q. }
    assert (Q3 : SpecLeib.TwinB.SpecLeib.rg R' 3 = gp) by (pose proof (SR X3) as Q; rewrite H1, SegL.TwinB.SegL.den_VPz in Q; exact Q).
    assert (Q4 : SpecLeib.TwinB.SpecLeib.rg R' 4 = tp) by (pose proof (SR X4) as Q; rewrite H2, SegL.TwinB.SegL.den_VPz in Q; exact Q).
    assert (Q26 : SpecLeib.TwinB.SpecLeib.rg R' 26 = s10) by (pose proof (SR X26) as Q; rewrite H3, SegL.TwinB.SegL.den_VPz in Q; exact Q).
    assert (Q27 : SpecLeib.TwinB.SpecLeib.rg R' 27 = s11) by (pose proof (SR X27) as Q; rewrite H4, SegL.TwinB.SegL.den_VPz in Q; exact Q).
    idtac "regs ok".

    assert (SL : forall off v, In (off, v) (SLOTS RA FMT) -> AM.bytes_at bsegs m' (bv_unsigned sp + off) (AM.le8 (den E v))).
    { intros off v HIn. rewrite forallb_forall in SLT. specialize (SLT _ HIn). cbn [fst snd] in SLT.
      assert (OR : - 1280 <= off < 0 /\ off <= -8).
      { unfold SLOTS in HIn. cbn [In] in HIn. repeat (destruct HIn as [HIn|HIn]; [injection HIn as <- <-; lia|]). contradiction. }
      assert (EM : ms_mem ms' = m') by (rewrite EQ; reflexivity).
      rewrite <- EM. apply (FxOut.TwinB.FxOut.slot_ok_sound bsegs WInit.OPSW E st' ms' mo' _ v _ HS' SLT).
      - rewrite (DV off) by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold two64; lia). reflexivity.
      - lia. }
    assert (DX : forall k x, ev E k = x -> den E (VP k wzero) = x) by (intros k x <-; apply SegL.TwinB.SegL.den_VPz).
    idtac "slots ok".

    assert (EM : ms_mem ms' = m') by (rewrite EQ; reflexivity).
    destruct (FxOut.TwinB.FxOut.text_ok_sound bsegs WInit.OPSW E st' ms' mo' 1%uint63 (-512) LEN HS' TXT) as (str & SLEN & SNZ & SB).
    { unfold two63; lia. }
    { unfold two63; lia. }
    { rewrite E1. lia. }
    { rewrite E1. unfold two64. lia. }
    rewrite E1, EM in SB.
    idtac "text ok".
    destruct INV as (MU & WM & RM).
    assert (IN : forall off v, (fun p => In p (SLOTS RA FMT)) (off, v) -> In (off, v) (SLOTS RA FMT)) by (intros; assumption).
    Ltac inslot := unfold SLOTS; cbn [In]; repeat (first [left; reflexivity | right]).
    pose proof (SL (-640) _ ltac:(inslot)) as S640. pose proof (SL (-632) _ ltac:(inslot)) as S632.
    pose proof (SL (-600) _ ltac:(inslot)) as S600. pose proof (SL (-592) _ ltac:(inslot)) as S592. pose proof (SL (-584) _ ltac:(inslot)) as S584.
    pose proof (SL (-576) _ ltac:(inslot)) as S576. pose proof (SL (-568) _ ltac:(inslot)) as S568. pose proof (SL (-560) _ ltac:(inslot)) as S560.
    pose proof (SL (-552) _ ltac:(inslot)) as S552. pose proof (SL (-544) _ ltac:(inslot)) as S544. pose proof (SL (-536) _ ltac:(inslot)) as S536.
    pose proof (SL (-528) _ ltac:(inslot)) as S528. pose proof (SL (-520) _ ltac:(inslot)) as S520.
    pose proof (SL (-112) _ ltac:(inslot)) as S112. pose proof (SL (-104) _ ltac:(inslot)) as S104. pose proof (SL (-96) _ ltac:(inslot)) as S96.
    pose proof (SL (-88) _ ltac:(inslot)) as S88. pose proof (SL (-72) _ ltac:(inslot)) as S72.
    idtac "slot facts ok".
    rewrite (DX 125%uint63 s9 eq_refl) in S600. rewrite (DX 124%uint63 s8 eq_refl) in S592. rewrite (DX 123%uint63 s7 eq_refl) in S584.
    rewrite (DX 122%uint63 s6 eq_refl) in S576. rewrite (DX 121%uint63 s5 eq_refl) in S568. rewrite (DX 120%uint63 s4 eq_refl) in S560.
    rewrite (DX 119%uint63 s3 eq_refl) in S552. rewrite (DX 118%uint63 s2 eq_refl) in S112. rewrite (DX 109%uint63 s1 eq_refl) in S104.
    rewrite (DX 108%uint63 s0 eq_refl) in S96.
    rewrite den_lit in S536, S520, S88, S72.
    change (den E (VL wzero)) with (Z_to_bv 64 0) in S640, S632, S544.
    change (to_Z 474624%uint63) with 0x73e00 in S520. change (to_Z 474544%uint63) with 0x73db0 in S88.
    idtac "slot values ok".
    unfold SpecLeib.TwinB.SpecLeib.mkR_of in EQ. rewrite Q2, Q18, Q3, Q4, Q26, Q27, PC in EQ. change (to_Z STOPP) with 0x74478 in EQ.
    do 25 eexists. exists (den E (VP 1%uint63 (Z2w (-56)))), m', str.
    split; [exact EQ|]. idtac "EQ ok".
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split; [eapply stk_winv; [exact STK| split; [exact MU| split; [exact WM| exact RM]]]|].
    split. { apply (ro_cons8' _ _ (bv_unsigned sp + -632) _ _ S640 ltac:(lia)). apply ro_one8. exact S632. }
    split. { apply (ro_cons8' _ _ (bv_unsigned sp + -592) _ _ S600 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -584) _ _ S592 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -576) _ _ S584 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -568) _ _ S576 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -560) _ _ S568 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -552) _ _ S560 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -544) _ _ S552 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -536) _ _ S544 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -528) _ _ S536 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -520) _ _ S528 ltac:(lia)).
             apply ro_one8. exact S520. }
    split. { apply (ro_cons8' _ _ (bv_unsigned sp + -104) _ _ S112 ltac:(lia)). apply (ro_cons8' _ _ (bv_unsigned sp + -96) _ _ S104 ltac:(lia)).
             apply (ro_cons8' _ _ (bv_unsigned sp + -88) _ _ S96 ltac:(lia)). apply ro_one8. exact S88. }
    split. { apply ro_one8. exact S72. }
    split; [exact SLEN|]. split; [exact SNZ| exact SB].
Time Qed.
End S.
End PrintfSeg2.
End TwinB.
