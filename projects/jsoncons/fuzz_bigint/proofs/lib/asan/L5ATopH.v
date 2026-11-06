(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5AStrctor L5ATopP2 As0Sums As0_code_8d9e8_8e368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ATH.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ATP2. Import L5ADH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

(* [comment removed for export] *)
Lemma kept_reg regs regs' (k : nat) : APSX.kept_ok regs regs' -> (0 < k < 32)%nat -> ~ In k APC.caller_saved -> getr regs' (reg k) = getr regs (reg k).
Proof.
  intros H Hk NI. apply H.
  - intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
    rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
  - unfold AX2.ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. rewrite Nat2Z.id. exact NI.
Qed.

(* [comment removed for export] *)
Definition tfrk (S : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U R 1) /\ L5.u64_at RSEGS M (S - 16) (U R 8) /\ L5.u64_at RSEGS M (S - 24) (U R 9) /\ L5.u64_at RSEGS M (S - 32) (U R 18) /\
  L5.u64_at RSEGS M (S - 40) (U R 19) /\ L5.u64_at RSEGS M (S - 48) (U R 20) /\ L5.u64_at RSEGS M (S - 56) (U R 21) /\ L5.u64_at RSEGS M (S - 64) (U R 22) /\
  L5.u64_at RSEGS M (S - 72) (U R 23) /\ L5.u64_at RSEGS M (S - 80) (U R 24) /\ L5.u64_at RSEGS M (S - 88) (U R 25) /\ L5.u64_at RSEGS M (S - 96) (U R 26) /\
  L5.u64_at RSEGS M (S - 104) (U R 27).
Definition town (V2 cls F : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop := tfrk (V2 + cls) R M /\ L5.u64_at RSEGS M (V2 - 176) F.
Definition tocell (V2 cls : Z) (a : Z) : Prop := V2 + cls - 104 <= a < V2 + cls \/ V2 - 176 <= a < V2 - 168.
Lemma town_agree V2 cls F R M1 M1' : 4096 <= V2 - 192 -> V2 + cls <= 2 ^ 47 -> 0 <= cls <= 16 ->
  town V2 cls F R M1 -> (forall a, tocell V2 cls a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> town V2 cls F R M1'.
Proof.
  intros H0 H1 HC ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) & C14) AG. unfold town, tfrk, tocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Local Abbreviation apure := (L5ADH.apure L ar C HI LY HIok).

Section TOP.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (V2 cls r SCRT : Z) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation S := (V2 + cls).
Local Notation SPA := (V2 - 192).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2A : aligned V2 32.
Hypothesis V2R : 140735332487424 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 208 + 4096 <= SCRT.
Local Abbreviation binv := (L5AFK.binv L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3).
Local Abbreviation Wret := (L5AFK.Wret F fl 3).
Local Notation FF' := ((F, 3, V2 - 192 + 32) :: FF).

(* [comment removed for export] *)
Definition TIDX : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 27]%nat.
Definition rinvT (Rc : bvmap 5 word) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 SPA /\ getr Rc (reg 8) = Z_to_bv 64 S /\ getr Rc (reg 9) = Z_to_bv 64 SPA /\
  getr Rc (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 19) = Z_to_bv 64 F /\ getr Rc (reg 20) = Z_to_bv 64 (F + 32) /\
  getr Rc (reg 27) = Z_to_bv 64 F /\ getr Rc (reg 3) = getr R (reg 3) /\ getr Rc (reg 4) = getr R (reg 4).
Lemma rinvT_keep Ra Rb : rinvT Ra -> (forall k, In k TIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvT Rb.
Proof.
  intros (X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) KS. unfold rinvT.
  rewrite !KS by (apply L5K.in_b; vm_compute; reflexivity). repeat split; assumption.
Qed.
Lemma rinvT_ks Ra Rb (KS : list nat) : rinvT Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) TIDX = true -> rinvT Rb.
Proof. intros RI HKS HB. apply (rinvT_keep Ra Rb RI). intros k Hk. apply HKS. exact (L5K.incl_b TIDX KS HB k Hk). Qed.
Lemma rinvT_pres Ra Rb : rinvT Ra -> regs_preserved Ra Rb -> rinvT Rb.
Proof.
  intros RI RP. apply (rinvT_keep Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP).
  revert Hk. apply (L5K.incl_b TIDX cs_all). vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tail_run (fx : FPState) Rc MV : rinvT Rc ->
  L5.writable RSEGS MV SPA (S - SPA) -> L5.img_clear MV 860160 880640 -> L5.u64_at RSEGS MV 908088 2147450880 -> L5.u32_at RSEGS MV 908096 1 ->
  L5.u64_at RSEGS MV 882712 834348 -> town V2 cls F R MV ->
  L5.defined MV F 512 -> L5.writable RSEGS MV F 512 -> L5.writable RSEGS MV (F / 8 + SB) 64 -> L5.u64_at RSEGS MV (F + 504) fl -> L5.writable RSEGS MV fl 1 ->
  exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx Rc 0x8e1b4 MV) (st fx9 R9 r M9v) /\ mem_grows MV M9v
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wret a -> M9v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ L5.u8_at RSEGS M9v fl 0 /\ getr R9 (reg 10) = Z_to_bv 64 0 /\ regs_preserved R R9.
Proof.
  intros RI WSv IMGC CSB CUAR RMS OWNv FDEFv FWv FSHWv FLCv FLWv.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4).
  assert (ALF : aligned F 32) by exact F32.
  assert (FRG : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= V2 < 2 ^ 64) by (clear - FR FLR V2R; lia). destruct FRG as (FRG & FLRG & V2RG).
  assert (SFB : F + 512 <= V2 - 192 /\ fl + 1 <= V2 - 192) by (clear - FCEIL FLR SPC SLO; lia).
  assert (SFA : V2 - 192 + 192 <= F \/ F + 512 <= V2 - 192) by (clear - SFB; lia).
  assert (SFLA : V2 - 192 + 192 <= fl \/ fl + 1 <= V2 - 192) by (clear - FLR SPC SLO; lia).
  assert (W192 : L5.writable RSEGS MV (V2 - 192) 192). { eapply L5.writable_sub. exact WSv. clear; lia. clear - CLS; lia. }
  (* [comment removed for export] *)
  pose proof (tpQ1_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & qFR & qFZ & (qMS & qKS & qR1 & qR10 & qR11 & _)).
  assert (RI1 : rinvT R1). { apply (rinvT_ks Rc R1 KS_tpQ1 RI qKS). vm_compute; reflexivity. }
  (* [comment removed for export] *)
  assert (RMS1 : L5.u64_at RSEGS M1v 882712 834348).
  { eapply L5C.u64_at_agree. 4: exact RMS. 2: clear; lia. 2: clear; lia. intros i Hi. apply qFZ. clear - Hi; lia. all: clear - Hi FR F8; unfold SB; lia. }
  assert (AG1 : forall i, 65536 <= i < 6500352 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi. apply qFZ. clear - Hi; lia. all: clear - Hi FR F8; unfold SB; lia. }
  assert (IMGC1 : L5.img_clear M1v 860160 880640). { intros i Hi. rewrite AG1 by (clear - Hi; lia). apply IMGC. exact Hi. }
  assert (CSB1 : L5.u64_at RSEGS M1v 908088 2147450880). { eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros i Hi. apply AG1. clear - Hi; lia. }
  assert (CUAR1 : L5.u32_at RSEGS M1v 908096 1).
  { unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS MV M1v 4 908096 ltac:(clear; lia) ltac:(cbn; clear; lia)). exact CUAR. intros i Hi. apply AG1. cbn in Hi. clear - Hi; lia. }
  pose proof (tpQt_conc fx1 R1 M1v (fun j => match j with 2%nat => U R1 2 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & _ & tFR & _ & (tMS & tKS & tR6 & tR11 & tR12)).
  assert (E2 : M2v = M1v) by (apply mem_eq_of_agree; intros a Ha; apply tFR). subst M2v.
  (* [comment removed for export] *)
  set (sh := F / 8 + 2147450880) in *.
  assert (SHR : 2147450880 <= sh /\ sh + 64 <= 17594333495296).
  { subst sh. clear - FR. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47 - 512) 8 ltac:(lia) ltac:(lia)). change ((2 ^ 47 - 512) / 8) with 17592186044352 in H0. lia. }
  assert (FSHW1 : L5.writable RSEGS M1v sh 64). { eapply L5.writable_grows. exact MG1. exact FSHWv. }
  destruct (as0_fill_spec_memset fx2 M1v (Z_to_bv 64 sh) (Z_to_bv 64 245) 64 R2 (Z_to_bv 64 582112)) as (R3 & MS3 & KO3 & _).
  { clear; lia. }
  { rewrite L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia. }
  { pose proof (FSHW1 0 64%nat ltac:(clear; lia) ltac:(clear; lia)) as X. rewrite Z.add_0_r in X. exact X. }
  { rewrite L5.unsigned_lit by (clear; lia). unfold AX2.two64. clear; lia. }
  { apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
  { rewrite r1, (tKS 1%nat) by inl. exact qR1. }
  { rewrite r10, (tKS 10%nat) by inl. exact qR10. }
  { rewrite r11. exact tR11. }
  { rewrite r12, tR12. exact qR11. }
  set (M3v := wbytes M1v (Z_to_bv 64 sh) (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 245))) (Z.to_nat 64))) in *.
  assert (MG3 : mem_grows M1v M3v) by (apply wbytes_grows).
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + 64) -> M3v (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
  { intros a Ha Hn. subst M3v. apply AX2S.wbytes_out. rewrite repeat_length, L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia.
    rewrite repeat_length, !L5.unsigned_lit by (clear - SHR Ha; lia). clear - Hn. lia. }
  assert (RI3 : rinvT R3).
  { apply (rinvT_keep R1 R3 RI1). intros j Hj. rewrite (kept_reg R2 R3 j KO3). apply tKS. revert Hj. apply (L5K.incl_b TIDX KS_tpQt). vm_compute; reflexivity.
    unfold TIDX in Hj; cbn [In] in Hj; clear - Hj; lia. unfold TIDX in Hj. cbn [In] in Hj. unfold APC.caller_saved. cbn [In]. clear - Hj. lia. }
  (* [comment removed for export] *)
  assert (AGS : forall a, V2 - 192 <= a < S -> M3v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
  { intros a Ha. rewrite AG3. apply qFZ. clear - Ha V2R CLS; lia. clear - Ha SFB; lia. clear - Ha SHR V2R; subst sh; unfold SB; lia.
    clear - Ha V2R CLS; lia. clear - Ha SHR V2R; lia. }
  assert (OWN3 : town V2 cls F R M3v).
  { apply (town_agree V2 cls F R MV M3v ltac:(clear - V2R; lia) ltac:(clear - V2S; lia) ltac:(clear - CLS; lia) OWNv). intros a Ha. apply AGS. unfold tocell in Ha. clear - Ha CLS; lia. }
  destruct OWN3 as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) & C14).
  assert (FDEF3 : L5.defined M3v F 512). { eapply L5.defined_grows. exact MG3. eapply L5.defined_grows. exact MG1. exact FDEFv. }
  assert (FW3 : L5.writable RSEGS M3v F 512). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact FWv. }
  assert (FSHW3 : L5.writable RSEGS M3v (F / 8 + 2147450880) 64). { eapply L5.writable_grows. exact MG3. exact FSHW1. }
  assert (FLW3 : L5.writable RSEGS M3v fl 1). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact FLWv. }
  assert (FLC3 : L5.u64_at RSEGS M3v (F + 504) fl).
  { eapply L5C.u64_at_agree. 4: exact FLCv. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. rewrite AG3. apply qFZ. clear - Hi FR; lia. clear - Hi; lia.
    clear - Hi FR FBIG SHR; subst sh; unfold SB; lia. clear - Hi FR; lia. clear - Hi FR FBIG SHR; lia. }
  assert (AGI3 : forall i, 65536 <= i < 6500352 -> M3v (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)) by (intros i Hi; apply AG3; [clear - Hi; lia | clear - Hi SHR; lia]).
  assert (IMGC3 : L5.img_clear M3v 860160 880640). { intros i Hi. rewrite AGI3 by (clear - Hi; lia). apply IMGC1. exact Hi. }
  assert (CSB3 : L5.u64_at RSEGS M3v 908088 2147450880). { eapply L5C.u64_at_agree. 4: exact CSB1. 2: clear; lia. 2: clear; lia. intros i Hi. apply AGI3. clear - Hi; lia. }
  assert (CUAR3 : L5.u32_at RSEGS M3v 908096 1).
  { unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M1v M3v 4 908096 ltac:(clear; lia) ltac:(cbn; clear; lia)). exact CUAR1. intros i Hi. apply AGI3. cbn in Hi. clear - Hi; lia. }
  pose proof RI3 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4).
  assert (V0R : forall k, 0 <= U R k < 2 ^ 64) by (intros k; apply UR).
  assert (FIN : forall (fx9 : FPState) R9 M9v (KS : list nat),
            msteps RSEGS (st fx2 R3 0x8e1e0 M3v) (st fx9 R9 0x8e2bc M9v) -> mem_grows M3v M9v ->
            (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (fl + 0 <= i < fl + 0 + 1) -> M9v (Z_to_bv 64 i) = M3v (Z_to_bv 64 i)) ->
            (forall x, In x KS -> getr R9 (reg x) = getr R3 (reg x)) -> In 3%nat KS -> In 4%nat KS ->
            getr R9 (reg 1) = Z_to_bv 64 (U R 1) -> getr R9 (reg 2) = Z_to_bv 64 S -> getr R9 (reg 10) = Z_to_bv 64 0 ->
            (forall k, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (U R k)) ->
            L5.u8_at RSEGS M9v fl 0 ->
            exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx Rc 0x8e1b4 MV) (st fx9 R9 r M9v) /\ mem_grows MV M9v
              /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wret a -> M9v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
              /\ L5.u8_at RSEGS M9v fl 0 /\ getr R9 (reg 10) = Z_to_bv 64 0 /\ regs_preserved R R9).
  { intros fx9 R9 M9v KS eMS MG9 eFZ eKS K3 K4 eR1 eR2 eR10 eRS eFL0.
    pose proof (ret_to fx9 R9 M9v 0x8e2bc W_8e2bc r F_8e2bc eq_refl D_8e2bc ltac:(rewrite eR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
    exists fx9, R9, M9v. split. { eapply msteps_trans. exact qMS. eapply msteps_trans. exact tMS. eapply msteps_trans. exact MS3. eapply msteps_trans. exact eMS. exact RET. }
    split. { eapply mem_grows_trans. exact MG1. eapply mem_grows_trans. exact MG3. exact MG9. }
    split. { intros a Ha Hw. unfold L5AFK.Wret in Hw. change (ff_bytes 3 / 8) with 64 in Hw. rewrite eFZ. rewrite AG3. apply qFZ. exact Ha.
             - clear - Hw; lia.
             - clear - Hw; unfold SB in Hw; lia.
             - exact Ha.
             - clear - Hw; subst sh; unfold SB in Hw; lia.
             - exact Ha.
             - clear - Hw; lia. }
    split. exact eFL0. split. exact eR10.
    apply preserved_by_index. intros j Hj. unfold cs_all in Hj. cbn [In] in Hj.
    destruct Hj as [<-|Hj]. { rewrite eR2. symmetry. exact G2. }
    destruct Hj as [<-|Hj]. { rewrite (eKS 3%nat K3). exact Y3. }
    destruct Hj as [<-|Hj]. { rewrite (eKS 4%nat K4). exact Y4. }
    rewrite (eRS j) by (cbn [In]; clear - Hj; tauto). symmetry. apply U_to. }
  assert (WS3 : L5.writable RSEGS M3v SPA (S - SPA)). { eapply L5.writable_grows. exact MG3. eapply L5.writable_grows. exact MG1. exact WSv. }
  destruct CLS as [E|E]; rewrite E in Y8, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, WS3.
  - (* [comment removed for export] *)
    assert (WSc : L5.writable RSEGS M3v (V2 - 192) 192). { eapply L5.writable_sub. exact WS3. clear; lia. clear; lia. }
    pose proof (tpQ20_conc fx2 R3 M3v (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl
                  | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                  | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 54%nat => U R 27 | 58%nat => U R3 1 | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26 & eR27 & eFL0)).
    apply (FIN fx9 R9 M9v KS_tpQ20 eMS MG9 eFZ eKS ltac:(inl) ltac:(inl) eR1).
    + rewrite eR2, E. first [reflexivity | (f_equal; clear; lia)].
    + exact eR10.
    + intros j Hj. cbn [In] in Hj.
      repeat (destruct Hj as [<-|Hj]; [first [exact eR8 | exact eR9 | exact eR18 | exact eR19 | exact eR20 | exact eR21 | exact eR22 | exact eR23 | exact eR24 | exact eR25 | exact eR26 | exact eR27] |]). destruct Hj.
    + exact eFL0.
  - (* [comment removed for export] *)
    assert (WSc : L5.writable RSEGS M3v (V2 - 192) 208). { eapply L5.writable_sub. exact WS3. clear; lia. clear; lia. }
    pose proof (tpQ216_conc fx2 R3 M3v (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl
                  | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                  | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 54%nat => U R 27 | 58%nat => U R3 1 | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26 & eR27 & eFL0)).
    apply (FIN fx9 R9 M9v KS_tpQ216 eMS MG9 eFZ eKS ltac:(inl) ltac:(inl) eR1).
    + rewrite eR2, E. first [reflexivity | (f_equal; clear; lia)].
    + exact eR10.
    + intros j Hj. cbn [In] in Hj.
      repeat (destruct Hj as [<-|Hj]; [first [exact eR8 | exact eR9 | exact eR18 | exact eR19 | exact eR20 | exact eR21 | exact eR22 | exact eR23 | exact eR24 | exact eR25 | exact eR26 | exact eR27] |]). destruct Hj.
    + exact eFL0.
Qed.

(* [comment removed for export] *)
Lemma top_tail (fx : FPState) Rc Mc modelc BX BXf LKc crc Ac :
  binv [] BX Mc modelc LKc crc Ac -> rinvT Rc ->
  ( (exists b0, L5.u8_at RSEGS Mc (F + 32) b0 /\ 0 <= b0 < 256 /\ Z.testbit b0 0 = false /\ BXf = BX)
    \/ (exists w0 pd nb, L5.u64_at RSEGS Mc (F + 32) w0 /\ 0 <= w0 < 2 ^ 64 /\ Z.testbit w0 0 = true /\ L5.u64_at RSEGS Mc (F + 48) pd /\ 4096 <= pd <= 2 ^ 47
                         /\ In (pd, nb) (BX ++ LB) /\ lb_remove pd (BX ++ LB) = BXf ++ LB) ) ->
  (forall (fxf : FPState) Rf Mf modelf LKf Af,
      regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXf ++ LB) FF' SPA OPDEL_SCR a -> ~ Wret a -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      ahpres L ar LB FF S SCRT [] M Mf ->
      model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> incl LKf LK ->
      ri_inv HI (BXf ++ LB) FF LKf crc Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e198 Mc modelc) K.
Proof.
  intros BI RI STR KF.
  (* [comment removed for export] *)
  assert (RET : forall (fx' : FPState) R' M' model' BX' LK' A' (Mo : word -> option byte),
            binv [] BX' M' model' LK' crc A' -> rinvT R' -> BX' = BXf -> incl A' A' ->
            (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXf ++ LB) FF' SPA OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mo (Z_to_bv 64 a)) ->
            (forall (fxf : FPState) Rf Mf modelf,
                regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 ->
                (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXf ++ LB) FF' SPA OPDEL_SCR a -> ~ Wret a -> Mf (Z_to_bv 64 a) = Mo (Z_to_bv 64 a)) ->
                ahpres L ar LB FF S SCRT [] M Mf -> model_rt model modelf -> amodel_ok A' modelf ->
                ri_inv HI (BXf ++ LB) FF LK' crc A' Mf (vml_of modelf) ->
                srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
            srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x8e1b4 M' model') K).
  { intros fx' R' M' model' BX' LK' A' Mo BI' RI' EBX _ AGo KF'. subst BX'.
    destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G [] BXf M' model' LK' crc A' BI')
      as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & _).
    change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (F + 512 - 8) with (F + 504) in FLCv by (clear; lia).
    destruct (tail_run fx' R' _ RI' WSv IMGC CSB CUAR RMS OWNv FDEFv FWv FSHWv FLCv FLWv) as (fx9 & R9 & M9v & MS9 & MG9 & FZ9 & FL9 & R910 & RP9).
    apply (L5AFK.retire_core L ar C HI LY HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G [] BXf M' model' LK' crc A' fx' fx9 R' 0x8e1b4 R9 r M9v K BI' MS9 MG9 FZ9 FL9).
    intros Mf modelf FRMf AHf RTf AMf HHf. apply (KF' fx9 R9 Mf modelf RP9 R910).
    - intros a Ha Hc Hw. rewrite (FRMf a Ha Hw). apply AGo. exact Ha. exact Hc.
    - exact AHf.
    - exact RTf.
    - exact AMf.
    - exact HHf. }
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G [] BX Mc modelc LKc crc Ac BI)
    as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & (_ & _ & FV & _)).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4).
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (F + 512 - 8) with (F + 504) in FLCv by (clear; lia).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ALF : aligned F 32) by exact F32.
  assert (FRG : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= V2 < 2 ^ 64) by (clear - FR FLR V2R; lia). destruct FRG as (FRG & FLRG & V2RG).
  assert (SFB : F + 512 <= V2 - 192 /\ fl + 1 <= V2 - 192) by (clear - FCEIL FLR SPC SLO; lia).
  assert (SFA : V2 - 192 + 192 <= F \/ F + 512 <= V2 - 192) by (clear - SFB; lia).
  assert (SFLA : V2 - 192 + 192 <= fl \/ fl + 1 <= V2 - 192) by (clear - SFB; lia).
  assert (W192 : L5.writable RSEGS MV (V2 - 192) 192). { eapply L5.writable_sub. exact WSv. clear; lia. clear - CLS; lia. }
  assert (CELLV : forall a v, F <= a -> a + 8 <= F + 512 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact FV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 FR; lia) ltac:(clear - H2 FR; lia))). exact Hc. }
  assert (CELL1 : forall v, L5.u8_at RSEGS Mc (F + 32) v -> L5.u8_at RSEGS MV (F + 32) v).
  { intros v Hc. apply (proj2 (u8_at_vis (ahid Ac modelc) Mc (F + 32) v ltac:(eapply avis_sub; [exact FV | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). exact Hc. }
  destruct STR as [(b0 & SB0 & B0R & B0T & EBX)|(w0 & pd & nb & SW0 & W0R & W0T & SPD & PDR & INP & ELB)].
  - (* [comment removed for export] *)
    pose proof (CELL1 _ SB0) as SB0v. assert (B0R' : 0 <= b0 <= 255 /\ 0 <= b0 < 2 ^ 64) by (clear - B0R; lia). destruct B0R' as [B0R' B0R''].
    pose proof (tpPs_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => b0 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _)).
    assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8e198 R1 0x8e1b4 K B1 B2 pMS).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3 [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (RET fx1 R1 Mc model1 BX LKc Ac Mc BI1).
    + apply (rinvT_ks Rc R1 KS_tpPs RI pKS). vm_compute; reflexivity.
    + symmetry; exact EBX.
    + apply incl_refl.
    + intros a _ _. reflexivity.
    + intros fxf Rf Mf modelf RPf R10f AGf AHf RTf AMf HHf. apply (KF fxf Rf Mf modelf LKc Ac RPf R10f AGf AHf RTf B4 AMf B5 HHf).
  - (* [comment removed for export] *)
    pose proof (CELL1 _ (L5ASC.u8_of_u64_lo Mc (F + 32) w0 SW0)) as SB0v.
    assert (B0R : 0 <= w0 mod 256 <= 255 /\ 0 <= w0 mod 256 < 2 ^ 64) by (pose proof (Z.mod_pos_bound w0 256 ltac:(clear; lia)) as X; clear - X; lia). destruct B0R as [B0R B0R'].
    assert (B0T : Z.testbit (w0 mod 256) 0 = true). { change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by (clear; lia). exact W0T. }
    pose proof (CELLV (F + 32) w0 ltac:(clear; lia) ltac:(clear; lia) SW0) as SW0v. pose proof (CELLV (F + 48) pd ltac:(clear; lia) ltac:(clear; lia) SPD) as SPDv.
    assert (PDR' : 4096 <= pd <= 140737488355328 /\ 0 <= pd < 2 ^ 64) by (clear - PDR; lia). destruct PDR' as [PDR' PDR''].
    pose proof (tpPl_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => w0 mod 256 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _)).
    assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
    assert (RI1 : rinvT R1). { apply (rinvT_ks Rc R1 KS_tpPl RI pKS). vm_compute; reflexivity. }
    pose proof RI1 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4).
    pose proof (tpPl2_conc fx1 R1 MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R1 1 | 61%nat => pd | 62%nat => w0 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx2 & R2 & M2v & _ & dFR & _ & (dMS & dKS & dR1 & dR10 & dR11)).
    assert (E2 : M2v = MV) by (apply mem_eq_of_agree; intros a Ha; apply dFR). subst M2v.
    assert (RI2 : rinvT R2). { apply (rinvT_ks R1 R2 KS_tpPl2 RI1 dKS). vm_compute; reflexivity. }
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx2 Rc 0x8e198 R2 OPDEL_SIZED K B1 B2 (msteps_trans _ _ _ _ pMS dMS)).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3 [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    pose proof RI2 as (Z2 & _ & _ & _ & _ & _ & _ & _ & Z4).
    assert (SPA16 : (V2 - 192) mod 16 = 0). { clear - V2A. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (Hdel fx2 R2 Mc model1 K (BX ++ LB) FF' LKc crc Ac pd nb SPA 582068 HH1 AM1 HK INP).
    + rewrite r10. exact dR10.
    + rewrite r1. exact dR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. exact Z2.
    + rewrite r4, Z4. exact G4.
    + replace SPA with (S - (192 + cls)) by (clear; lia). apply (astk_sub ar Mc Mc S SCRT (192 + cls) OPDEL_SCR B6 (mem_grows_refl Mc)).
      clear - CLS; lia. rewrite DEL_EQ; clear; lia. rewrite DEL_EQ; clear - HSCR CLS; lia. replace (S - (192 + cls)) with (V2 - 192) by (clear; lia). exact SPA16.
    + intros fx3 R3 M3 model3 A3 RP3 AH3 RT3 IA3 AM3 HH3. rewrite ELB in AH3, HH3.
      assert (BI3 : binv [] BXf M3 model3 LKc crc A3).
      { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2
                 (L5AFK.GCTX L ar HI LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS)
                 [] [] BX BXf BXf Mc model1 LKc crc Ac M3 model3 LKc crc A3 OPDEL_SCR [] BI1 AH3 HH3 AM3 RT3 IA3 (incl_refl _)).
        - rewrite DEL_EQ; clear; lia.
        - rewrite DEL_EQ; clear - HSCR CLS; lia.
        - intros rr a [].
        - intros a _ _ rr [].
        - intros a X. exact X. }
      apply (RET fx3 R3 M3 model3 BXf LKc A3 Mc BI3).
      * apply (rinvT_pres R2 R3 RI2 RP3).
      * reflexivity.
      * apply incl_refl.
      * intros a Ha Hc. apply (proj1 AH3). split. exact Ha. split. exact Hc. intros rr [].
      * intros fxf Rf Mf modelf RPf R10f AGf AHf RTf AMf HHf. apply (KF fxf Rf Mf modelf LKc A3 RPf R10f AGf AHf RTf).
        -- intros x Hx. apply IA3. apply B4. exact Hx.
        -- exact AMf.
        -- exact B5.
        -- exact HHf.
Qed.
End TOP.
End WithIface.
End SCFG_1.
End L5ATH.
