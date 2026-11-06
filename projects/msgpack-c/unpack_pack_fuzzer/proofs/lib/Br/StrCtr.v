(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Omono.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv RMallocG StrG CtrFX MemFX CopyFX HeapCtr MemcpyCtr.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section OPS.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis PBstr1 : forall E, PB (eb E) -> exists str, eb E 1%uint63 = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str
                                          /\ bv_unsigned (den E (SZ 9%uint63)) = Z.of_nat (length str) + 1.
Hypothesis PBstr3 : forall E, PB (eb E) -> exists str, eb E 3%uint63 = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str
                                          /\ bv_unsigned (den E (SZ 10%uint63)) = Z.of_nat (length str) + 1.
Hypothesis PB12 : forall E, PB (eb E) -> bv_unsigned (den E (SZ 15%uint63)) = Z.of_nat (length (eb E 12%uint63))
                                        /\ Z.of_nat (length (eb E 12%uint63)) mod 8 = 0.

Lemma str_blob_ok_sound : forall E j H, PB (eb E) -> str_blob_ok j H = true ->
  exists str, eb E j = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str /\ bv_unsigned (den E H) = Z.of_nat (length str) + 1.
Proof.
  intros E j H HPB SB. unfold str_blob_ok in SB. apply orb_prop in SB. destruct SB as [SB|SB]; apply andb_prop in SB as [J HH];
    apply Uint63.eqb_correct in J; apply sv_eqb_eq in HH; subst j H; [apply PBstr1| apply PBstr3]; exact HPB.
Qed.

Lemma pad_room : forall x y, x <= y -> y mod 8 = 0 -> (- x) mod 8 <= y - x.
Proof.
  intros x y Hxy Hy. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1. pose proof (Z.div_mod y 8 ltac:(lia)) as D2. rewrite Hy in D2.
  set (q1 := - x / 8) in *. set (q2 := y / 8) in *. set (r := (- x) mod 8) in *. clearbody q1 q2 r. nia || lia.
Qed.

Lemma s_resv_addfact : forall st f, s_resv (addfact st f) = s_resv st. Proof. reflexivity. Qed.
Lemma s_next_addfact : forall st f, s_next (addfact st f) = s_next st. Proof. reflexivity. Qed.
Lemma s_resv_setr : forall st r v, s_resv (setr st r v) = s_resv st. Proof. intros st r v. unfold setr. destruct r; reflexivity. Qed.

Lemma addfact_setr_comm : forall st r v f, setr (addfact st f) r v = addfact (setr st r v) f.
Proof. intros st r v f. unfold setr, addfact. destruct r; reflexivity. Qed.

Theorem strnlen_sound : forall pc, to_Z pc = RSTRNLEN_SYM ->
  contract_sound rsegs OPS MP PB (CtrA.strnlen_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrA.strnlen_c] in Happ. unfold CtrA.strnlen_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X10) as [w10|ks os| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (getr st X11) as [m| | | | | | | | | |] eqn:HX11; try discriminate.
  destruct (stack_ok st STRNLEN_STACK) as [[ksp klo1]|] eqn:SOK; [|discriminate].
  destruct (negb (weqb os wzero) || PrimInt63.eqb ks 0 || PrimInt63.eqb ks STACK_ID || PrimInt63.eqb ks STRS_ID) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C Ks12]. apply orb_false_iff in C as [C Ks1]. apply orb_false_iff in C as [OO Ks0].
  apply negb_false_iff in OO. apply weqb_eq in OO. subst os.
  destruct (IMap.find ks (s_regs st)) as [rs|] eqn:Hks; [|discriminate].
  destruct (IMap.find STRS_ID (s_regs st)) as [r12|] eqn:H12; [|discriminate].
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
  destruct (Mem.rg_cells rs) eqn:CSc; [|discriminate].
  destruct (Mem.rg_bg rs) as [| | | |j sh] eqn:BS; try discriminate.
  destruct (Mem.rg_cells r12) eqn:C12c; [|discriminate].
  destruct (Mem.rg_bg r12) as [| | | |j12 sh12] eqn:B12; try discriminate.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  set (L := sv_alu ALU_SUB (Mem.rg_hi rs) (VL wone)) in Happ.
  set (st1 := setregs st (IMap.add STACK_ID (forget_r1 r1 ksp) (s_regs st))) in Happ.
  destruct (havoc_errno rsegs ERRNO _) as [st3|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 AL]. apply andb_prop in C2 as [C2 CONT]. apply andb_prop in C2 as [C2 LOW]. apply andb_prop in C2 as [C2 POSA].
  apply andb_prop in C2 as [C2 LEm]. apply andb_prop in C2 as [C2 POSH]. apply andb_prop in C2 as [C2 LO12]. apply andb_prop in C2 as [C2 LOs].
  apply andb_prop in C2 as [C2 SH12]. apply andb_prop in C2 as [C2 SH]. apply andb_prop in C2 as [C2 J12]. apply andb_prop in C2 as [SB HI12].
  apply Uint63.eqb_correct in SH. apply Uint63.eqb_correct in SH12. apply Uint63.eqb_correct in J12. subst sh sh12 j12.
  apply Uint63.eqb_correct in LO12. apply Uint63.eqb_correct in LOs. apply sv_eqb_eq in HI12.

  destruct (call_sound OPS E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (so_zero _ _ _ _ _ _ HS) as EZ0.
  destruct (stack_sound OPS E st ms mo STRNLEN_STACK ksp klo1 HS ltac:(vm_compute; reflexivity) SOK)
    as (off & r1' & HX2 & Hr1' & W1 & BG1 & Hksp & -> & K16 & KNEG & SPE & LO0 & ROOM & HI & STK).
  rewrite Hr1 in Hr1'. injection Hr1' as <-. change (to_Z STRNLEN_STACK) with 32 in ROOM.
  pose proof (so_reg _ _ _ _ _ _ HS ks rs Hks) as ROs. pose proof (so_reg _ _ _ _ _ _ HS STRS_ID r12 H12) as RO12.
  pose proof (so_reg _ _ _ _ _ _ HS STACK_ID r1 Hr1) as RO1.
  set (A := bv_unsigned (ev E ks)) in *. set (Bs := bv_unsigned (ev E STRS_ID)) in *. set (base := bv_unsigned (ev E STACK_ID)) in *.
  set (sp := base + keyZ ksp) in *.
  set (Hz := bv_unsigned (den E (Mem.rg_hi rs))). set (mZ := w2Z m). set (S12 := bv_unsigned (den E (SZ 15%uint63))).
  assert (HI12z : hiZ E r12 = S12) by (unfold hiZ; rewrite HI12; reflexivity).
  pose proof (w2Z_range m) as Rm. fold mZ in Rm.
  apply (known_ltu_sound E _ _ _ Hfs) in POSH. rewrite unsigned_VL in POSH. change (w2Z wzero) with 0 in POSH. fold Hz in POSH.
  apply (known_leu_sound E _ _ _ Hfs) in LEm. rewrite unsigned_VL in LEm. fold Hz mZ in LEm.
  apply (known_ltu_sound E _ _ _ Hfs) in POSA. rewrite unsigned_VL, den_VPz in POSA. change (w2Z wzero) with 0 in POSA. fold A in POSA.
  apply (known_leu_sound E _ _ _ Hfs) in LOW. rewrite !den_VPz in LOW. fold A Bs in LOW.
  apply (known_leu_sound E _ _ _ Hfs) in CONT. rewrite !den_sv_alu in CONT. cbn [alu64 alu] in CONT. rewrite !bv_add_unsigned, !den_VPz in CONT.
  fold A Bs Hz S12 in CONT.
  pose proof (ValP.aligned_sound E _ Hfs _ _ AL ltac:(change (to_Z 3%uint63) with 3; lia)) as AL8. rewrite den_VPz in AL8. change (2 ^ to_Z 3%uint63) with 8 in AL8. fold Bs in AL8.
  assert (LZs : loZ rs = 0) by (unfold loZ; rewrite LOs; reflexivity). assert (LZ12 : loZ r12 = 0) by (unfold loZ; rewrite LO12; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROs Ks0) as [RLs RHs]. pose proof (ro_range _ _ _ _ _ _ RO12 eq_refl) as [RL12 RH12].
  fold A in RLs, RHs. fold Bs in RL12, RH12. rewrite LZs in RLs. rewrite LZ12 in RL12. unfold hiZ in RHs. fold Hz in RHs. rewrite HI12z in RH12. unfold W64.two64 in RHs, RH12.
  destruct (PB12 E HPB) as [ES12 M8]. fold S12 in ES12.
  assert (CONT' : A + Hz <= Bs + S12).
  { unfold bv_wrap in CONT. rewrite bv_modulus_64 in CONT. rewrite !Z.mod_small in CONT; unfold W64.two64; lia. }
  destruct (str_blob_ok_sound E j (Mem.rg_hi rs) HPB SB) as (str & EBJ & NONUL & ELEN). fold Hz in ELEN.

  set (o := A - Bs). set (len := Bs + S12 - A).
  pose proof (MemFX.blob_region_bytes rsegs (s_priv st) E (ms_mem ms) STRS_ID r12 12%uint63 o (Z.to_nat len) RO12 eq_refl C12c B12 ltac:(lia) ltac:(lia) ltac:(rewrite HI12z; lia)) as BUF.
  fold Bs in BUF. replace (Bs + o) with A in BUF by lia.
  set (buf := map (fun i => nth (Z.to_nat o + i)%nat (eb E 12%uint63) (Z_to_bv 8 0)) (seq 0 (Z.to_nat len))) in BUF.
  assert (LBUF : length buf = Z.to_nat len) by (subst buf; apply MemFX.blob_slice_length).

  assert (EQJ : forall i, (i < Z.to_nat Hz)%nat -> nth i buf (Z_to_bv 8 0) = nth i (eb E j) (Z_to_bv 8 0)).
  { intros i Hi.
    pose proof (ro_bg _ _ _ _ _ _ ROs (Z.of_nat i) ltac:(intros _; rewrite LZs; unfold hiZ; fold Hz; lia) ltac:(intros X; rewrite Ks0 in X; discriminate X)
                  ltac:(intros g gr _ F; rewrite CSc in F; cbn in F; discriminate F)) as G1.
    unfold bg_byte in G1. rewrite BS in G1. change (to_Z 0%uint63) with 0 in G1. rewrite Z.sub_0_r, Nat2Z.id in G1. fold A in G1.
    destruct BUF as (_ & _ & BY). rewrite LBUF in BY. pose proof (BY i ltac:(lia)) as G2. rewrite <- MemFX.rb_mrd in G2. rewrite G1 in G2.
    rewrite (nth_error_nth' _ (Z_to_bv 8 0)) in G2 by (rewrite LBUF; lia). injection G2 as G2. symmetry. exact G2. }
  assert (SPLIT : buf = str ++ Z_to_bv 8 0 :: skipn (Z.to_nat Hz) buf).
  { rewrite <- (firstn_skipn (Z.to_nat Hz) buf) at 1. change (str ++ Z_to_bv 8 0 :: skipn (Z.to_nat Hz) buf) with (str ++ ([Z_to_bv 8 0] ++ skipn (Z.to_nat Hz) buf)).
    rewrite app_assoc. f_equal. rewrite <- EBJ. apply list_eq_nth_error.
    - rewrite length_firstn, EBJ, length_app. cbn [length]. lia.
    - intros i Hi. rewrite length_firstn in Hi. rewrite nth_error_firstn. replace (Nat.ltb i (Z.to_nat Hz)) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by lia. rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite EBJ, length_app; cbn [length]; lia).
      f_equal. apply EQJ. lia. }
  assert (M8' : (Bs + S12) mod 8 = 0) by (rewrite ES12, Z.add_mod, AL8, M8 by lia; reflexivity).
  pose proof (pad_room (A + Hz) (Bs + S12) CONT' M8') as PADR.
  assert (OK : memchr_ok A 0 mZ buf).
  { rewrite SPLIT. apply memchr_ok_cstr; [exact NONUL|]. rewrite length_skipn, LBUF.
    replace (A + Z.of_nat (length str) + 1) with (A + Hz) by lia. lia. }
  assert (RES : strnlen_res mZ buf = Hz - 1).
  { rewrite SPLIT. rewrite (strnlen_res_cstr A mZ str _ NONUL). lia. }

  destruct (stk_split rsegs (ms_mem ms) _ sp _ STK ltac:(unfold sp; lia)) as [STK1 _].
  assert (SEP : A + Z.of_nat (length buf) <= sp - 32 \/ sp <= A).
  { rewrite LBUF, Z2Nat.id by lia.
    destruct (Z_lt_le_dec (sp - 32) (A + len)) as [L1|G1]; [| left; lia].
    destruct (Z_lt_le_dec A sp) as [L2|G2]; [| right; lia]. exfalso.

    set (a := Z.max A (sp - 32)).
    apply (so_disj _ _ _ _ _ _ HS STRS_ID r12 STACK_ID r1 H12 Hr1 ltac:(discriminate) eq_refl eq_refl (or_intror W1) a).
    fold Bs base. rewrite LZ12, HI12z. unfold a, sp, len in *. split; lia. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 A).
  { rewrite <- reg_of_X10, GR, HX10, den_VPz. subst A. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 mZ).
  { rewrite <- reg_of_X11, GR, HX11, den_VL. reflexivity. }
  assert (SP2 : bv_unsigned (PropExec.getr (ms_regs ms) 2%bv) = sp) by (rewrite <- reg_of_X2, GR; exact SPE).
  pose proof (ms_shape OPS E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrA.strnlen_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE. pose proof two64_eq as T64.
  apply (strnlen_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo A mZ (base + loZ r1) buf K A0 A1
           ltac:(lia) ltac:(unfold W64.two64 in Rm; lia) RA1 ltac:(rewrite SP2; exact STK1) ltac:(rewrite SP2; unfold RSTRNLEN_STACK, sp; lia)
           BUF OK ltac:(rewrite SP2; unfold RSTRNLEN_STACK; exact SEP) MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' STK' BA OM. rewrite SP2 in MU, STK'. unfold RSTRNLEN_STACK in MU.

  set (Fv := MemFX.cfv R' (MemFX.word4_at rsegs M' (to_Z ERRNO))). set (Gv := fun (_ : Z) (_ : Z) => Z_to_bv 8 0).
  set (E' := env_above E (s_next st) Fv Gv).
  pose proof (env_above_ext E (s_next st) Fv Gv) as EXT. fold E' in EXT.
  assert (HS' : St.st_ok rsegs OPS E' st (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs)) mo).
  { rewrite <- MSE. exact (st_ok_reval rsegs OPS (s_next st) E E' EXT st ms mo POS SVB HS). }
  destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & _ & _ & P4 & _).
  destruct (regs_reval_find (s_next st) E E' EXT _ _ _ (so_bst _ _ _ _ _ _ HS) P4 Hr1) as (EV1 & EH1 & _).
  destruct (regs_reval_find (s_next st) E E' EXT _ _ _ (so_bst _ _ _ _ _ _ HS) P4 Hks) as (EVs & EHs & _ & RVBs).

  pose proof (so_reg _ _ _ _ _ _ HS' STACK_ID r1 Hr1) as RO1'.
  assert (RO' : St.region_ok rsegs (s_priv st) E' M' STACK_ID (forget_r1 r1 ksp)).
  { unfold forget_r1. unfold STACK_ID, CtrLib.STACK_ID in *.
    apply (MemFX.forget_r1_ok rsegs (s_priv st) E' (ms_mem ms) M' r1 ksp (so_zero _ _ _ _ _ _ HS') RO1' BG1 W1 K16 KNEG);
      rewrite ?EV1, ?EH1; fold base; fold sp; try lia.
    - intros a Ha. assert (EQM : M' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
      { apply (MU (Z_to_bv 64 a)). cbn. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64, sp in *; lia). unfold sp in *. split; [lia| exact I]. }
      split; [unfold rb; rewrite EQM; reflexivity|]. unfold wb, wview. rewrite EQM. exact (fun X => X).
    - intros a Ha. destruct STK' as (_ & _ & ST'). destruct (ST' a ltac:(unfold sp in *; lia)) as [Wv [b Hb]].
      split; [rewrite MemFX.rb_mrd, Hb; discriminate| apply (proj2 (MemFX.wb_wview rsegs _ _)); exact Wv]. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E' st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo
                STACK_ID r1 (forget_r1 r1 ksp) HS' Hr1 eq_refl W1) as BW.
  assert (HS1 : St.st_ok rsegs OPS E' st1 (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None M' (seg_rom rsegs)) mo).
  { unfold st1, setregs. apply BW.
    - intros a Ha NI. apply (MU (Z_to_bv 64 a)). cbn. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; exact Ha).
      rewrite EV1, EH1 in NI. fold base in NI. unfold sp in *. split; [lia| exact I].
    - exact OM.
    - exact (minv_of_mem_inv M' MI').
    - exact RO'.
    - unfold forget_r1. destruct (region_forget_sound rsegs (s_priv st) E' (ms_mem ms) STACK_ID r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp) RO1') as (_ & Elo & _).
      unfold loZ. rewrite Elo. lia.
    - unfold forget_r1. destruct (region_forget_sound rsegs (s_priv st) E' (ms_mem ms) STACK_ID r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp) RO1') as (_ & _ & Ehi & _).
      unfold hiZ. rewrite Ehi. lia. }

  assert (NX1 : s_next st1 = s_next st) by reflexivity.
  assert (EL : den E' L = Z_to_bv 64 (Hz - 1)).
  { unfold L. rewrite den_sv_alu. cbn [alu64 alu]. apply bv_eq. rewrite bv_sub_unsigned, den_VL, Z_to_bv_unsigned.
    unfold hiZ in EHs. rewrite EHs. fold Hz. rewrite wbv_unsigned. change (w2Z wone) with 1.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite !Z.mod_small; unfold W64.two64 in *; lia. }
  assert (HKR : forall x, x <> X0 -> x <> X10 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 N10 CPx. apply KEPT. apply kept_or_clobbered; assumption. }
  pose proof (MemFX.clobber_setr10_sound_above rsegs OPS E st1 (ms_regs ms) R' (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None M' (seg_rom rsegs) mo Fv Gv L
                HS1 POS B62 (fun x i H => MemFX.cfv_clob R' _ x i H) HKR ltac:(change (s_next st1) with (s_next st); fold E'; rewrite EL, A0', RES; reflexivity)) as HS2.
  change (s_next st1) with (s_next st) in HS2. fold E' in HS2.

  assert (F1 : fact_holds E' (FULt L (Mem.rg_hi rs))).
  { cbn [fact_holds]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia). unfold hiZ in EHs. rewrite EHs. fold Hz. lia. }
  assert (F2 : fact_holds E' (FULt L (VL m))).
  { cbn [fact_holds]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia). rewrite unsigned_VL. fold mZ. lia. }
  assert (F3 : fact_holds E' (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j L 1%uint63)) (VL wzero))).
  { cbn [fact_holds]. rewrite den_sv_ext by (unfold width_ok; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; lia).
    cbn [den]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia).
    unfold E'. rewrite eb_above. rewrite EBJ. unfold blob_bytes. change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0.
    replace (Z.to_nat (Hz - 1)) with (length str) by lia. rewrite skipn_app, skipn_all, Nat.sub_diag. cbn. reflexivity. }
  pose proof (MemFX.addfact_sound rsegs OPS E' _ _ mo _ (MemFX.addfact_sound rsegs OPS E' _ _ mo _ (MemFX.addfact_sound rsegs OPS E' _ _ mo _ HS2 F1) F2) F3) as HS3.

  rewrite !addfact_setr_comm in HE.
  set (f1 := FULt L (Mem.rg_hi rs)) in HE, HS3 |- *. set (f2 := FULt L (VL m)) in HE, HS3 |- *.
  set (f3 := FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j L 1%uint63)) (VL wzero)) in HE, HS3 |- *.
  pose proof (clobber_fields st1) as (_ & _ & Frv & _ & _ & _ & _ & Fnx). pose proof (int_range (s_next st)) as NR. rewrite two63_eq in NR.
  assert (RVn : s_resv (addfact (addfact (addfact (setr (clobber st1) X10 L) f1) f2) f3) = RNone).
  { rewrite !s_resv_addfact, s_resv_setr, Frv. exact RV. }
  assert (EV : ev E' (s_next (addfact (addfact (addfact (setr (clobber st1) X10 L) f1) f2) f3)) = MemFX.word4_at rsegs M' (to_Z ERRNO)).
  { rewrite !s_next_addfact, s_next_setr, Fnx, NX1. unfold E'.
    rewrite ev_above by (rewrite add_Z; [| change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; lia]; change (to_Z 15%uint63) with 15; lia).
    rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; lia). change (to_Z 15%uint63) with 15.
    replace (to_Z (s_next st) + 15 - to_Z (s_next st)) with 15 by lia. apply MemFX.cfv_15. }
  destruct (MemFX.havoc_errno_sound rsegs OPS E' _ ERRNO st3 R' (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo HS3 RVn EV HE) as (HS4 & _).
  pose proof (MemFX.setpc_sound rsegs OPS E' st3 R' (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None M' (seg_rom rsegs) mo r HS4) as ST.
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ EXT HMP ST).
Qed.
End OPS.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Omono.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.StrFun.
Import F_syscalls.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CopyFX.
Import RMallocG.TwinB StrG.TwinB HeapCtr.TwinB MemcpyCtr.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section OPS.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis PBstr1 : forall E, PB (eb E) -> exists str, eb E 1%uint63 = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str
                                          /\ bv_unsigned (den E (SZ 9%uint63)) = Z.of_nat (length str) + 1.
Hypothesis PBstr3 : forall E, PB (eb E) -> exists str, eb E 3%uint63 = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str
                                          /\ bv_unsigned (den E (SZ 10%uint63)) = Z.of_nat (length str) + 1.
Hypothesis PB12 : forall E, PB (eb E) -> bv_unsigned (den E (SZ 15%uint63)) = Z.of_nat (length (eb E 12%uint63))
                                        /\ Z.of_nat (length (eb E 12%uint63)) mod 8 = 0.

Lemma str_blob_ok_sound : forall E j H, PB (eb E) -> str_blob_ok j H = true ->
  exists str, eb E j = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str /\ bv_unsigned (den E H) = Z.of_nat (length str) + 1.
Proof.
  intros E j H HPB SB. unfold str_blob_ok in SB. apply orb_prop in SB. destruct SB as [SB|SB]; apply andb_prop in SB as [J HH];
    apply Uint63.eqb_correct in J; apply sv_eqb_eq in HH; subst j H; [apply PBstr1| apply PBstr3]; exact HPB.
Qed.

Lemma pad_room : forall x y, x <= y -> y mod 8 = 0 -> (- x) mod 8 <= y - x.
Proof.
  intros x y Hxy Hy. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1. pose proof (Z.div_mod y 8 ltac:(lia)) as D2. rewrite Hy in D2.
  set (q1 := - x / 8) in *. set (q2 := y / 8) in *. set (r := (- x) mod 8) in *. clearbody q1 q2 r. nia || lia.
Qed.

Lemma s_resv_addfact : forall st f, s_resv (addfact st f) = s_resv st. Proof. reflexivity. Qed.
Lemma s_next_addfact : forall st f, s_next (addfact st f) = s_next st. Proof. reflexivity. Qed.
Lemma s_resv_setr : forall st r v, s_resv (setr st r v) = s_resv st. Proof. intros st r v. unfold setr. destruct r; reflexivity. Qed.

Lemma addfact_setr_comm : forall st r v f, setr (addfact st f) r v = addfact (setr st r v) f.
Proof. intros st r v f. unfold setr, addfact. destruct r; reflexivity. Qed.

Theorem strnlen_sound : forall pc, to_Z pc = RSTRNLEN_SYM ->
  contract_sound rsegs OPS MP PB (CtrA.strnlen_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply CtrA.strnlen_c] in Happ. unfold CtrA.strnlen_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X10) as [w10|ks os| | | | | | | | |] eqn:HX10; try discriminate.
  destruct (getr st X11) as [m| | | | | | | | | |] eqn:HX11; try discriminate.
  destruct (stack_ok st STRNLEN_STACK) as [[ksp klo1]|] eqn:SOK; [|discriminate].
  destruct (negb (weqb os wzero) || PrimInt63.eqb ks 0 || PrimInt63.eqb ks STACK_ID || PrimInt63.eqb ks STRS_ID) eqn:C; [discriminate|].
  apply orb_false_iff in C as [C Ks12]. apply orb_false_iff in C as [C Ks1]. apply orb_false_iff in C as [OO Ks0].
  apply negb_false_iff in OO. apply weqb_eq in OO. subst os.
  destruct (IMap.find ks (s_regs st)) as [rs|] eqn:Hks; [|discriminate].
  destruct (IMap.find STRS_ID (s_regs st)) as [r12|] eqn:H12; [|discriminate].
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
  destruct (Mem.rg_cells rs) eqn:CSc; [|discriminate].
  destruct (Mem.rg_bg rs) as [| | | |j sh] eqn:BS; try discriminate.
  destruct (Mem.rg_cells r12) eqn:C12c; [|discriminate].
  destruct (Mem.rg_bg r12) as [| | | |j12 sh12] eqn:B12; try discriminate.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  set (L := sv_alu ALU_SUB (Mem.rg_hi rs) (VL wone)) in Happ.
  set (st1 := setregs st (IMap.add STACK_ID (forget_r1 r1 ksp) (s_regs st))) in Happ.
  destruct (havoc_errno rsegs ERRNO _) as [st3|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 AL]. apply andb_prop in C2 as [C2 CONT]. apply andb_prop in C2 as [C2 LOW]. apply andb_prop in C2 as [C2 POSA].
  apply andb_prop in C2 as [C2 LEm]. apply andb_prop in C2 as [C2 POSH]. apply andb_prop in C2 as [C2 LO12]. apply andb_prop in C2 as [C2 LOs].
  apply andb_prop in C2 as [C2 SH12]. apply andb_prop in C2 as [C2 SH]. apply andb_prop in C2 as [C2 J12]. apply andb_prop in C2 as [SB HI12].
  apply Uint63.eqb_correct in SH. apply Uint63.eqb_correct in SH12. apply Uint63.eqb_correct in J12. subst sh sh12 j12.
  apply Uint63.eqb_correct in LO12. apply Uint63.eqb_correct in LOs. apply sv_eqb_eq in HI12.

  destruct (call_sound OPS E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (so_zero _ _ _ _ _ _ HS) as EZ0.
  destruct (stack_sound OPS E st ms mo STRNLEN_STACK ksp klo1 HS ltac:(vm_compute; reflexivity) SOK)
    as (off & r1' & HX2 & Hr1' & W1 & BG1 & Hksp & -> & K16 & KNEG & SPE & LO0 & ROOM & HI & STK).
  rewrite Hr1 in Hr1'. injection Hr1' as <-. change (to_Z STRNLEN_STACK) with 32 in ROOM.
  pose proof (so_reg _ _ _ _ _ _ HS ks rs Hks) as ROs. pose proof (so_reg _ _ _ _ _ _ HS STRS_ID r12 H12) as RO12.
  pose proof (so_reg _ _ _ _ _ _ HS STACK_ID r1 Hr1) as RO1.
  set (A := bv_unsigned (ev E ks)) in *. set (Bs := bv_unsigned (ev E STRS_ID)) in *. set (base := bv_unsigned (ev E STACK_ID)) in *.
  set (sp := base + keyZ ksp) in *.
  set (Hz := bv_unsigned (den E (Mem.rg_hi rs))). set (mZ := w2Z m). set (S12 := bv_unsigned (den E (SZ 15%uint63))).
  assert (HI12z : hiZ E r12 = S12) by (unfold hiZ; rewrite HI12; reflexivity).
  pose proof (w2Z_range m) as Rm. fold mZ in Rm.
  apply (known_ltu_sound E _ _ _ Hfs) in POSH. rewrite unsigned_VL in POSH. change (w2Z wzero) with 0 in POSH. fold Hz in POSH.
  apply (known_leu_sound E _ _ _ Hfs) in LEm. rewrite unsigned_VL in LEm. fold Hz mZ in LEm.
  apply (known_ltu_sound E _ _ _ Hfs) in POSA. rewrite unsigned_VL, den_VPz in POSA. change (w2Z wzero) with 0 in POSA. fold A in POSA.
  apply (known_leu_sound E _ _ _ Hfs) in LOW. rewrite !den_VPz in LOW. fold A Bs in LOW.
  apply (known_leu_sound E _ _ _ Hfs) in CONT. rewrite !den_sv_alu in CONT. cbn [alu64 alu] in CONT. rewrite !bv_add_unsigned, !den_VPz in CONT.
  fold A Bs Hz S12 in CONT.
  pose proof (ValP.aligned_sound E _ Hfs _ _ AL ltac:(change (to_Z 3%uint63) with 3; lia)) as AL8. rewrite den_VPz in AL8. change (2 ^ to_Z 3%uint63) with 8 in AL8. fold Bs in AL8.
  assert (LZs : loZ rs = 0) by (unfold loZ; rewrite LOs; reflexivity). assert (LZ12 : loZ r12 = 0) by (unfold loZ; rewrite LO12; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROs Ks0) as [RLs RHs]. pose proof (ro_range _ _ _ _ _ _ RO12 eq_refl) as [RL12 RH12].
  fold A in RLs, RHs. fold Bs in RL12, RH12. rewrite LZs in RLs. rewrite LZ12 in RL12. unfold hiZ in RHs. fold Hz in RHs. rewrite HI12z in RH12. unfold W64.two64 in RHs, RH12.
  destruct (PB12 E HPB) as [ES12 M8]. fold S12 in ES12.
  assert (CONT' : A + Hz <= Bs + S12).
  { unfold bv_wrap in CONT. rewrite bv_modulus_64 in CONT. rewrite !Z.mod_small in CONT; unfold W64.two64; lia. }
  destruct (str_blob_ok_sound E j (Mem.rg_hi rs) HPB SB) as (str & EBJ & NONUL & ELEN). fold Hz in ELEN.

  set (o := A - Bs). set (len := Bs + S12 - A).
  pose proof (MemFX.blob_region_bytes rsegs (s_priv st) E (ms_mem ms) STRS_ID r12 12%uint63 o (Z.to_nat len) RO12 eq_refl C12c B12 ltac:(lia) ltac:(lia) ltac:(rewrite HI12z; lia)) as BUF.
  fold Bs in BUF. replace (Bs + o) with A in BUF by lia.
  set (buf := map (fun i => nth (Z.to_nat o + i)%nat (eb E 12%uint63) (Z_to_bv 8 0)) (seq 0 (Z.to_nat len))) in BUF.
  assert (LBUF : length buf = Z.to_nat len) by (subst buf; apply MemFX.blob_slice_length).

  assert (EQJ : forall i, (i < Z.to_nat Hz)%nat -> nth i buf (Z_to_bv 8 0) = nth i (eb E j) (Z_to_bv 8 0)).
  { intros i Hi.
    pose proof (ro_bg _ _ _ _ _ _ ROs (Z.of_nat i) ltac:(intros _; rewrite LZs; unfold hiZ; fold Hz; lia) ltac:(intros X; rewrite Ks0 in X; discriminate X)
                  ltac:(intros g gr _ F; rewrite CSc in F; cbn in F; discriminate F)) as G1.
    unfold bg_byte in G1. rewrite BS in G1. change (to_Z 0%uint63) with 0 in G1. rewrite Z.sub_0_r, Nat2Z.id in G1. fold A in G1.
    destruct BUF as (_ & _ & BY). rewrite LBUF in BY. pose proof (BY i ltac:(lia)) as G2. rewrite <- MemFX.rb_mrd in G2. rewrite G1 in G2.
    rewrite (nth_error_nth' _ (Z_to_bv 8 0)) in G2 by (rewrite LBUF; lia). injection G2 as G2. symmetry. exact G2. }
  assert (SPLIT : buf = str ++ Z_to_bv 8 0 :: skipn (Z.to_nat Hz) buf).
  { rewrite <- (firstn_skipn (Z.to_nat Hz) buf) at 1. change (str ++ Z_to_bv 8 0 :: skipn (Z.to_nat Hz) buf) with (str ++ ([Z_to_bv 8 0] ++ skipn (Z.to_nat Hz) buf)).
    rewrite app_assoc. f_equal. rewrite <- EBJ. apply list_eq_nth_error.
    - rewrite length_firstn, EBJ, length_app. cbn [length]. lia.
    - intros i Hi. rewrite length_firstn in Hi. rewrite nth_error_firstn. replace (Nat.ltb i (Z.to_nat Hz)) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by lia. rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite EBJ, length_app; cbn [length]; lia).
      f_equal. apply EQJ. lia. }
  assert (M8' : (Bs + S12) mod 8 = 0) by (rewrite ES12, Z.add_mod, AL8, M8 by lia; reflexivity).
  pose proof (pad_room (A + Hz) (Bs + S12) CONT' M8') as PADR.
  assert (OK : memchr_ok A 0 mZ buf).
  { rewrite SPLIT. apply memchr_ok_cstr; [exact NONUL|]. rewrite length_skipn, LBUF.
    replace (A + Z.of_nat (length str) + 1) with (A + Hz) by lia. lia. }
  assert (RES : strnlen_res mZ buf = Hz - 1).
  { rewrite SPLIT. rewrite (strnlen_res_cstr A mZ str _ NONUL). lia. }

  destruct (stk_split rsegs (ms_mem ms) _ sp _ STK ltac:(unfold sp; lia)) as [STK1 _].
  assert (SEP : A + Z.of_nat (length buf) <= sp - 32 \/ sp <= A).
  { rewrite LBUF, Z2Nat.id by lia.
    destruct (Z_lt_le_dec (sp - 32) (A + len)) as [L1|G1]; [| left; lia].
    destruct (Z_lt_le_dec A sp) as [L2|G2]; [| right; lia]. exfalso.

    set (a := Z.max A (sp - 32)).
    apply (so_disj _ _ _ _ _ _ HS STRS_ID r12 STACK_ID r1 H12 Hr1 ltac:(discriminate) eq_refl eq_refl (or_intror W1) a).
    fold Bs base. rewrite LZ12, HI12z. unfold a, sp, len in *. split; lia. }

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 A).
  { rewrite <- reg_of_X10, GR, HX10, den_VPz. subst A. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 mZ).
  { rewrite <- reg_of_X11, GR, HX11, den_VL. reflexivity. }
  assert (SP2 : bv_unsigned (PropExec.getr (ms_regs ms) 2%bv) = sp) by (rewrite <- reg_of_X2, GR; exact SPE).
  pose proof (ms_shape OPS E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc CtrA.strnlen_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE. pose proof two64_eq as T64.
  apply (strnlen_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo A mZ (base + loZ r1) buf K A0 A1
           ltac:(lia) ltac:(unfold W64.two64 in Rm; lia) RA1 ltac:(rewrite SP2; exact STK1) ltac:(rewrite SP2; unfold RSTRNLEN_STACK, sp; lia)
           BUF OK ltac:(rewrite SP2; unfold RSTRNLEN_STACK; exact SEP) MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' STK' BA OM. rewrite SP2 in MU, STK'. unfold RSTRNLEN_STACK in MU.

  set (Fv := MemFX.cfv R' (MemFX.word4_at rsegs M' (to_Z ERRNO))). set (Gv := fun (_ : Z) (_ : Z) => Z_to_bv 8 0).
  set (E' := env_above E (s_next st) Fv Gv).
  pose proof (env_above_ext E (s_next st) Fv Gv) as EXT. fold E' in EXT.
  assert (HS' : St.st_ok rsegs OPS E' st (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom rsegs)) mo).
  { rewrite <- MSE. exact (st_ok_reval rsegs OPS (s_next st) E E' EXT st ms mo POS SVB HS). }
  destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & _ & _ & P4 & _).
  destruct (regs_reval_find (s_next st) E E' EXT _ _ _ (so_bst _ _ _ _ _ _ HS) P4 Hr1) as (EV1 & EH1 & _).
  destruct (regs_reval_find (s_next st) E E' EXT _ _ _ (so_bst _ _ _ _ _ _ HS) P4 Hks) as (EVs & EHs & _ & RVBs).

  pose proof (so_reg _ _ _ _ _ _ HS' STACK_ID r1 Hr1) as RO1'.
  assert (RO' : St.region_ok rsegs (s_priv st) E' M' STACK_ID (forget_r1 r1 ksp)).
  { unfold forget_r1. unfold STACK_ID, CtrLib.STACK_ID in *.
    apply (MemFX.forget_r1_ok rsegs (s_priv st) E' (ms_mem ms) M' r1 ksp (so_zero _ _ _ _ _ _ HS') RO1' BG1 W1 K16 KNEG);
      rewrite ?EV1, ?EH1; fold base; fold sp; try lia.
    - intros a Ha. assert (EQM : M' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
      { apply (MU (Z_to_bv 64 a)). cbn. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64, sp in *; lia). unfold sp in *. split; [lia| exact I]. }
      split; [unfold rb; rewrite EQM; reflexivity|]. unfold wb, wview. rewrite EQM. exact (fun X => X).
    - intros a Ha. destruct STK' as (_ & _ & ST'). destruct (ST' a ltac:(unfold sp in *; lia)) as [Wv [b Hb]].
      split; [rewrite MemFX.rb_mrd, Hb; discriminate| apply (proj2 (MemFX.wb_wview rsegs _ _)); exact Wv]. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E' st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo
                STACK_ID r1 (forget_r1 r1 ksp) HS' Hr1 eq_refl W1) as BW.
  assert (HS1 : St.st_ok rsegs OPS E' st1 (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None M' (seg_rom rsegs)) mo).
  { unfold st1, setregs. apply BW.
    - intros a Ha NI. apply (MU (Z_to_bv 64 a)). cbn. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; exact Ha).
      rewrite EV1, EH1 in NI. fold base in NI. unfold sp in *. split; [lia| exact I].
    - exact OM.
    - exact (minv_of_mem_inv M' MI').
    - exact RO'.
    - unfold forget_r1. destruct (region_forget_sound rsegs (s_priv st) E' (ms_mem ms) STACK_ID r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp) RO1') as (_ & Elo & _).
      unfold loZ. rewrite Elo. lia.
    - unfold forget_r1. destruct (region_forget_sound rsegs (s_priv st) E' (ms_mem ms) STACK_ID r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp) RO1') as (_ & _ & Ehi & _).
      unfold hiZ. rewrite Ehi. lia. }

  assert (NX1 : s_next st1 = s_next st) by reflexivity.
  assert (EL : den E' L = Z_to_bv 64 (Hz - 1)).
  { unfold L. rewrite den_sv_alu. cbn [alu64 alu]. apply bv_eq. rewrite bv_sub_unsigned, den_VL, Z_to_bv_unsigned.
    unfold hiZ in EHs. rewrite EHs. fold Hz. rewrite wbv_unsigned. change (w2Z wone) with 1.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite !Z.mod_small; unfold W64.two64 in *; lia. }
  assert (HKR : forall x, x <> X0 -> x <> X10 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0 N10 CPx. apply KEPT. apply kept_or_clobbered; assumption. }
  pose proof (MemFX.clobber_setr10_sound_above rsegs OPS E st1 (ms_regs ms) R' (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None M' (seg_rom rsegs) mo Fv Gv L
                HS1 POS B62 (fun x i H => MemFX.cfv_clob R' _ x i H) HKR ltac:(change (s_next st1) with (s_next st); fold E'; rewrite EL, A0', RES; reflexivity)) as HS2.
  change (s_next st1) with (s_next st) in HS2. fold E' in HS2.

  assert (F1 : fact_holds E' (FULt L (Mem.rg_hi rs))).
  { cbn [fact_holds]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia). unfold hiZ in EHs. rewrite EHs. fold Hz. lia. }
  assert (F2 : fact_holds E' (FULt L (VL m))).
  { cbn [fact_holds]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia). rewrite unsigned_VL. fold mZ. lia. }
  assert (F3 : fact_holds E' (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j L 1%uint63)) (VL wzero))).
  { cbn [fact_holds]. rewrite den_sv_ext by (unfold width_ok; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; lia).
    cbn [den]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64 in *; lia).
    unfold E'. rewrite eb_above. rewrite EBJ. unfold blob_bytes. change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0.
    replace (Z.to_nat (Hz - 1)) with (length str) by lia. rewrite skipn_app, skipn_all, Nat.sub_diag. cbn. reflexivity. }
  pose proof (MemFX.addfact_sound rsegs OPS E' _ _ mo _ (MemFX.addfact_sound rsegs OPS E' _ _ mo _ (MemFX.addfact_sound rsegs OPS E' _ _ mo _ HS2 F1) F2) F3) as HS3.

  rewrite !addfact_setr_comm in HE.
  set (f1 := FULt L (Mem.rg_hi rs)) in HE, HS3 |- *. set (f2 := FULt L (VL m)) in HE, HS3 |- *.
  set (f3 := FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j L 1%uint63)) (VL wzero)) in HE, HS3 |- *.
  pose proof (clobber_fields st1) as (_ & _ & Frv & _ & _ & _ & _ & Fnx). pose proof (int_range (s_next st)) as NR. rewrite two63_eq in NR.
  assert (RVn : s_resv (addfact (addfact (addfact (setr (clobber st1) X10 L) f1) f2) f3) = RNone).
  { rewrite !s_resv_addfact, s_resv_setr, Frv. exact RV. }
  assert (EV : ev E' (s_next (addfact (addfact (addfact (setr (clobber st1) X10 L) f1) f2) f3)) = MemFX.word4_at rsegs M' (to_Z ERRNO)).
  { rewrite !s_next_addfact, s_next_setr, Fnx, NX1. unfold E'.
    rewrite ev_above by (rewrite add_Z; [| change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; lia]; change (to_Z 15%uint63) with 15; lia).
    rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; lia). change (to_Z 15%uint63) with 15.
    replace (to_Z (s_next st) + 15 - to_Z (s_next st)) with 15 by lia. apply MemFX.cfv_15. }
  destruct (MemFX.havoc_errno_sound rsegs OPS E' _ ERRNO st3 R' (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo HS3 RVn EV HE) as (HS4 & _).
  pose proof (MemFX.setpc_sound rsegs OPS E' st3 R' (ms_fregs ms) (Z_to_bv 64 RSTRNLEN_SYM) (ms_fcsr ms) None M' (seg_rom rsegs) mo r HS4) as ST.
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ EXT HMP ST).
Qed.
End OPS.
End TwinB.
