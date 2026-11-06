(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablVia.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablPush OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_PushP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6d0f4_6d2b0.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
End U1_code_6d0f4_6d2b0.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3 MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablVia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablStmts TablLib TablPush Tabl_PushP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_PushU1.U1_code_6d0f4_6d2b0.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation tc := Img.tc.

Definition PT_ENTRY : Z := 0x6d134.
Definition PT_BODY  : Z := 0x6d198.
Definition PT_LOOP2 : Z := 0x6d188.
Definition PT_JOIN  : Z := 0x6d218.
Definition PT_EXIT  : Z := 0x6d28c.
Definition PT_TRAP  : Z := 0x6d22c.
Definition PBS_ENTRY : Z := 0x6d838.
Definition PT_STOPS : list Z := [PT_BODY; PT_LOOP2; PT_EXIT; PBS_ENTRY; PT_TRAP; 0x6d230].

Lemma LYU1 {AC : AllocCeiling} : lay_ok SEGS L.
Proof.
  constructor.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_errno_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
  - intros x Hx. apply ly_noseg. pose proof ac_bounds_lit. lia.
Qed.

Lemma roc_roU : forall M, img_ro_clear L M -> ro_clear L M.
Proof. intros M H w (Hi & Hn & _). exact (H w Hi Hn). Qed.

Lemma rdn_noseg_mdefU : forall Mx a (k : nat) bs,
  rdn SEGS Mx (Z_to_bv 64 a) k = Some bs -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat k -> find_segment SEGS x 1 = None) -> mdef Mx a (Z.of_nat k).
Proof.
  intros Mx a k. revert a. induction k as [|k IH]; intros a bs HR Ha Hk Hseg i Hi; [lia|].
  cbn [rdn] in HR.
  destruct (Mx (Z_to_bv 64 a)) as [b0|] eqn:Hm.
  - destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r, Hm; discriminate|].
    destruct (rdn SEGS Mx (Z_to_bv 64 a + 1) k) as [rest|] eqn:HR'; [|discriminate].
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) in HR'
      by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod; change (bv_unsigned (1%bv : bv 64)) with 1;
          rewrite (Z.mod_small (a + 1)), (Z.mod_small a), Z.mod_small by lia; reflexivity).
    replace (a + i) with (a + 1 + (i - 1)) by lia. apply (IH (a + 1) rest HR'); try lia. intros x Hx. apply Hseg. lia.
  - exfalso. unfold seg_rom, memory_read in HR. rewrite u64_of_Z in HR by lia.
    change (Z.of_N 1) with 1 in HR. rewrite (Hseg a) in HR by lia. discriminate.
Qed.

Lemma fld_hi_mdefU {AC : AllocCeiling} : forall Mx a (k : nat) v, fld SEGS Mx a k v -> alloc_ceiling <= a -> a + Z.of_nat k < 2 ^ 64 -> mdef Mx a (Z.of_nat k).
Proof.
  intros Mx a k v HF Ha Hk. pose proof ac_bounds_lit.
  eapply rdn_noseg_mdefU; [exact HF | lia | lia |]. intros x Hx. apply ly_noseg. lia.
Qed.

Section PT.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variable cpbs : vec_consts.
  Hypothesis MSpos : 0 <= MALLOC_STACK MI.
  Hypothesis Hcpbs : vc_entry cpbs = PBS_ENTRY /\ 0 <= vc_stack cpbs.
  Hypothesis PBS : vec32_pbslow_stmt SEGS L MI ST (2 ^ 31) cpbs.

  Section Body.
    Variables (fx : FPState) (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret pspan pat b cap p : Z) (xs l : list Z) (K : TSet).
    Definition STK : Z := 96 + (vc_stack cpbs + NEW_STACK SEGS L MI).
    Hypothesis CB : callB MI ST A s R M model sp ret STK.
    Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 pspan.
    Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 pat.
    Hypothesis Fp : fld SEGS M pspan 8 p.
    Hypothesis Fl : fld SEGS M (pspan + 8) 8 (Zlen l).
    Hypothesis RSP : ro_span SEGS L p l.
    Hypothesis Hp4 : p mod 4 = 0.
    Hypothesis Hll : Zlen l <= 33.
    Hypothesis Hl31 : Forall (fun t => 0 <= t < 2 ^ 31) l.
    Hypothesis Hpsc : alloc_ceiling <= pspan.
    Hypothesis Hps47 : pspan + 16 <= 2 ^ 47.
    Hypothesis Hpsw : forall a, zwin pspan (pspan + 16) a -> ~ zwin (sp - STK) sp a.
    Hypothesis VEC : vec32 MI A M pat b xs cap.
    Hypothesis OBJ : obj_ok MI A sp STK pat 24.
    Hypothesis PAT8 : pat mod 8 = 0.
    Hypothesis DJ : forall a, zwin pspan (pspan + 16) a -> ~ zwin pat (pat + 24) a.
    Hypothesis NMX : caps_bound (Zlen xs) cap (Zlen l) <= NMAX MI.
    Hypothesis RP : room_pushes SEGS L MI A (live MI A) (Zlen xs) cap (length l).
    Hypothesis CONT : forall A' R' M' model' (b' cap' : Z),
        retB MI ST A' s R R' M' model model' ->
        vec32 MI A' M' pat b' (push_types l xs) cap' ->
        pushes_post SEGS L MI A A' (Zlen xs) (Zlen l) b cap b' cap' ->
        eff MI A A' M M' (sp - STK, sp) (pushes_fp SEGS L MI A pat b cap b' cap') ->
        srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) model') K.

    Lemma PC : pctx SEGS L MI ST A s R M model sp ret STK 64 pat b cap xs (Zlen xs) (length l).
    Proof using AC MI ST cpbs MSpos Hcpbs A s R M model sp ret pat b cap p xs l CB VEC OBJ NMX RP.
      pose proof Hcpbs as [_ Hst]. constructor.
      - exact LYU1. - exact MSpos. - exact CB. - exact VEC. - exact OBJ.
      - unfold STK, NEW_STACK. split; [lia | reflexivity].
      - exact RP.
      - exact NMX.
      - destruct VEC as (_ & _ & _ & Hlen & _). lia.
    Qed.

    #[local] Notation PINV := (TablPush.PINV SEGS L MI ST A s M model sp STK pat b cap (Zlen xs) (length l)).
    #[local] Notation PCargs X := (X SEGS L MI ST A s R M model sp ret STK 64 pat b cap xs (Zlen xs) (length l) PC).

    Definition FRAME (M1 : mem) : Prop :=
      cellw SEGS M1 (sp - 8) 8 (bv_unsigned (getr R 1%bv)) /\ cellw SEGS M1 (sp - 16) 8 (bv_unsigned (getr R 8%bv)) /\
      cellw SEGS M1 (sp - 24) 8 (bv_unsigned (getr R 9%bv)) /\ cellw SEGS M1 (sp - 32) 8 (bv_unsigned (getr R 18%bv)) /\
      cellw SEGS M1 (sp - 40) 8 (bv_unsigned (getr R 19%bv)) /\ cellw SEGS M1 (sp - 48) 8 (bv_unsigned (getr R 20%bv)) /\
      cellw SEGS M1 (sp - 56) 8 (bv_unsigned (getr R 21%bv)).

    Definition REGS (R1 : bvmap 5 word) : Prop :=
      getr R1 2%bv = Z_to_bv 64 (sp - 64) /\ getr R1 3%bv = getr R 3%bv /\ getr R1 4%bv = getr R 4%bv /\
      forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr R1 r = getr R r.

    #[local] Ltac dCB := destruct CB as [AI0 MS0 ROC0 SX0 SXH0 CR0 Hceil0 HROOM0 Hwin0 Hown_sx0 Herr_sx0].

    Lemma spf : alloc_ceiling + STK <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\ 2 ^ 24 <= sp - STK /\
                getr R 2%bv = Z_to_bv 64 sp /\ getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\ STK = 96 + (vc_stack cpbs + (16 + MALLOC_STACK MI)) /\ 112 <= STK.
    Proof using AC MI ST cpbs MSpos Hcpbs A s R M model sp ret pat p CB. dCB. destruct CR0. pose proof ac_bounds_lit. pose proof MSpos. pose proof Hcpbs as [_ ?]. unfold STK, NEW_STACK in *. repeat split; try assumption; lia. Qed.

    Lemma FRAME_agree : forall M1 M2, FRAME M1 -> agree_on (zwin (sp - 56) sp) M1 M2 -> FRAME M2.
    Proof using AC MI ST cpbs MSpos Hcpbs A s R M model sp ret pat p CB.
      intros M1 M2 (C1 & C2 & C3 & C4 & C5 & C6 & C7) AG. pose proof spf as (Hc & Hs47 & _ & Hcv & _ & _ & _ & _ & _ & HSTK).
      assert (G : forall a v, cellw SEGS M1 a 8 v -> sp - 56 <= a -> a + 8 <= sp -> cellw SEGS M2 a 8 v).
      { intros a v [Hv Hr] H1 H2. split; [exact Hv|]. eapply (fld_agree SEGS M1 M2 a 8 v); [lia | cbn; lia | exact Hr |].
        eapply agree_on_weaken; [exact AG|]. intros x Hx. unfold zwin in *. cbn in Hx. lia. }
      repeat split; (eapply G; [eassumption | lia | lia]).
    Qed.

    Lemma EXIT : forall R1 M1 A1 model1 b1 cap1,
      PINV A1 M1 model1 b1 cap1 (push_types l xs) -> REGS R1 -> FRAME M1 ->
      srealizes SEGS (mkCfg (@mkst fx R1 (Z_to_bv 64 PT_EXIT) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST cpbs MSpos Hcpbs fx A s R M model sp ret pat b cap p xs l K CB CONT.
      intros R1 M1 A1 model1 b1 cap1 PI (G2 & G3 & G4 & Ghi) (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK').
      pose proof PI as [AI MS FS SX ROC VEC' PP EF WIN].
      pose (E := Eseed R1 [Z_to_bv 64 (sp - 64); getr R 1%bv; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R1).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M1 [KWord (SA (EVar 32) 56) (N.to_nat 8) (EVar 33); KWord (SA (EVar 32) 48) (N.to_nat 8) (EVar 34); KWord (SA (EVar 32) 40) (N.to_nat 8) (EVar 35);
                                     KWord (SA (EVar 32) 32) (N.to_nat 8) (EVar 36); KWord (SA (EVar 32) 24) (N.to_nat 8) (EVar 37); KWord (SA (EVar 32) 16) (N.to_nat 8) (EVar 38);
                                     KWord (SA (EVar 32) 8) (N.to_nat 8) (EVar 39)]).
      { assert (G32 : ev E 32 = Z_to_bv 64 (sp - 64)) by (evs; reflexivity).
        repeat apply Forall_cons; [kwv C1 G32 | kwv C2 G32 | kwv C3 G32 | kwv C4 G32 | kwv C5 G32 | kwv C6 G32 | kwv C7 G32 | apply Forall_nil]. }
      xruns HR HK 20%nat PT_STOPS (SCR [] [] []) 40%N; [split_scs; sc_fl|].
      rreg HR' 1%bv A1'. rreg HR' 2%bv A2.
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | eapply ret_run; [vm_compute; reflexivity | rewrite A1'; exact GR1 | exact Hret] |].
      apply (CONT A1 R' M1 model1 b1 cap1).
      - constructor; [exact AI | exact MS | exact (proj1 FS) | exact (proj2 FS) | exact SX |].
        intros r Hr. cbn in Hr.
        repeat (destruct Hr as [<-|Hr];
          [ first [ rewrite A1'; reflexivity
                  | rewrite A2, zbv_add, GR2; f_equal; lia
                  | lazymatch goal with |- getr _ ?rr = _ => let X := fresh in rreg_ HR' rr X; rewrite X end;
                    lazymatch goal with |- getr _ ?q = getr _ ?rr => try (replace q with rr by (apply bv_eq; reflexivity)) end;
                    first [reflexivity | assumption | apply Ghi; inl] ] |]).
        destruct Hr.
      - exact VEC'.
      - exact PP.
      - exact EF.
    Qed.

    Lemma Dps : mdef M pspan 16.
    Proof using AC M pspan pat p l Fp Fl Hpsc Hps47.
      intros k Hk. destruct (Z.lt_ge_cases k 8).
      - exact (fld_hi_mdefU (AC:=AC) M pspan 8 p Fp Hpsc ltac:(cbn; lia) k ltac:(cbn; lia)).
      - replace (pspan + k) with (pspan + 8 + (k - 8)) by lia. exact (fld_hi_mdefU (AC:=AC) M (pspan + 8) 8 (Zlen l) Fl ltac:(lia) ltac:(cbn; lia) (k - 8) ltac:(cbn; lia)).
    Qed.

    Lemma pspan_cells : forall A1 M1 model1 b1 cap1 ys, PINV A1 M1 model1 b1 cap1 ys ->
      fld SEGS M1 pspan 8 p /\ fld SEGS M1 (pspan + 8) 8 (Zlen l).
    Proof using AC MI ST cpbs MSpos Hcpbs A s R M model sp ret pspan pat b cap p xs l CB Fp Fl Hpsc Hps47 Hpsw VEC OBJ DJ NMX RP.
      intros A1 M1 model1 b1 cap1 ys PI. pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK').
      assert (AG : agree_on (zwin pspan (pspan + 16)) M M1).
      { apply (PCargs pinv_agree_hi A1 M1 model1 b1 cap1 ys PI). intros a Ha. unfold zwin in Ha.
        split; [lia|]. split; [replace a with (pspan + (a - pspan)) by lia; apply Dps; lia|].
        split; [apply DJ; unfold zwin; lia | intros Hw; exact (Hpsw a ltac:(unfold zwin; lia) ltac:(unfold zwin; lia))]. }
      split.
      - apply (fld_agree SEGS M M1 pspan 8 p ltac:(lia) ltac:(cbn; lia) Fp). eapply agree_on_weaken; [exact AG|]; intros a Ha; unfold zwin in *; cbn in Ha; lia.
      - apply (fld_agree SEGS M M1 (pspan + 8) 8 (Zlen l) ltac:(lia) ltac:(cbn; lia) Fl). eapply agree_on_weaken; [exact AG|]; intros a Ha; unfold zwin in *; cbn in Ha; lia.
    Qed.

    #[local] Ltac regeq G := etransitivity; [|exact G]; f_equal; apply bv_eq; reflexivity.

    Definition AT (R1 : bvmap 5 word) (j : Z) : Prop :=
      getr R1 10%bv = Z_to_bv 64 j /\ getr R1 20%bv = Z_to_bv 64 (j + 1) /\
      getr R1 8%bv = Z_to_bv 64 pspan /\ getr R1 9%bv = Z_to_bv 64 pat /\ getr R1 18%bv = Z_to_bv 64 (Zlen l) /\
      getr R1 19%bv = Z_to_bv 64 (2 ^ 61) /\ getr R1 21%bv = Z_to_bv 64 5 /\
      REGS R1.

    #[local] Ltac hi_regs HR' Ghi :=
      intros r Hr; rewrite <- (Ghi r Hr); cbn in Hr;
      repeat (destruct Hr as [<-|Hr]; [lazymatch goal with |- getr _ ?rr = _ => let X := fresh in rreg_ HR' rr X; rewrite X end; f_equal; apply bv_eq; reflexivity|]); destruct Hr.

    Lemma LOOP2 : forall j R2 M2 model2,
      0 <= j < Zlen l -> mstd model2 ->
      getr R2 20%bv = Z_to_bv 64 (j + 1) ->
      getr R2 8%bv = Z_to_bv 64 pspan -> getr R2 9%bv = Z_to_bv 64 pat -> getr R2 18%bv = Z_to_bv 64 (Zlen l) ->
      getr R2 19%bv = Z_to_bv 64 (2 ^ 61) -> getr R2 21%bv = Z_to_bv 64 5 ->
      REGS R2 ->
      (forall R3, j + 1 < Zlen l -> AT R3 (j + 1) -> srealizes SEGS (mkCfg (@mkst fx R3 (Z_to_bv 64 PT_BODY) M2 (seg_rom SEGS)) model2) K) ->
      (forall R3, j + 1 = Zlen l -> REGS R3 -> srealizes SEGS (mkCfg (@mkst fx R3 (Z_to_bv 64 PT_EXIT) M2 (seg_rom SEGS)) model2) K) ->
      srealizes SEGS (mkCfg (@mkst fx R2 (Z_to_bv 64 PT_LOOP2) M2 (seg_rom SEGS)) model2) K.
    Proof using AC MI ST cpbs MSpos Hcpbs fx A s R M model sp ret pspan pat p l K CB Hll.
      intros j R2 M2 model2 Hj MS G20 G8 G9 G18 G19 G21 (G2 & G3 & G4 & Ghi) HKc HKx.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK').
      pose (E := Eseed R2 [Z_to_bv 64 (sp - 64); Z_to_bv 64 (j + 1); Z_to_bv 64 (Zlen l)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (20%bv, EVar 33); (18%bv, EVar 34)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M2 []) by constructor.
      destruct (Z.eq_dec (j + 1) (Zlen l)) as [Hlast|Hmore].
      - xruns HR HK 20%nat PT_STOPS (SCR [true] [] []) 40%N; [split_scs; cbn [sc_denot]; evs; rewrite zext32_val, br_geu by lia; bool_lia|].
        apply HKx; [exact Hlast|]. split; [|split; [|split]];
           [ rreg HR' 2%bv X; exact X | rreg HR' 3%bv X; rewrite X; regeq G3 | rreg HR' 4%bv X; rewrite X; regeq G4 | hi_regs HR' Ghi ].
      - xruns HR HK 20%nat PT_STOPS (SCR [false] [] []) 40%N; [split_scs; cbn [sc_denot]; evs; rewrite zext32_val, br_geu by lia; bool_lia|].
        apply HKc; [lia|]. unfold AT, REGS.
        repeat match goal with |- _ /\ _ => split end;
           [ rreg HR' 10%bv X; rewrite X; apply zext32_val; lia
           | rreg HR' 20%bv X; rewrite X, zbv_add; f_equal; lia
           | rreg HR' 8%bv X; rewrite X; regeq G8 | rreg HR' 9%bv X; rewrite X; regeq G9 | rreg HR' 18%bv X; exact X
           | rreg HR' 19%bv X; rewrite X; regeq G19 | rreg HR' 21%bv X; rewrite X; regeq G21
           | rreg HR' 2%bv X; exact X | rreg HR' 3%bv X; rewrite X; regeq G3 | rreg HR' 4%bv X; rewrite X; regeq G4
           | hi_regs HR' Ghi ].
    Qed.

    Lemma mod4_of_16 : forall b0 k, b0 mod 16 = 0 -> (b0 + 4 * k) mod 4 = 0.
    Proof using pat p.
      intros b0 k H. pose proof (Z_div_mod_eq_full b0 16) as E. rewrite H in E.
      replace (b0 + 4 * k) with ((4 * (b0 / 16) + k) * 4) by lia. apply Z_mod_mult.
    Qed.

    Lemma STEP : forall j R1 M1 A1 model1 b1 cap1,
      0 <= j < Zlen l -> AT R1 j -> FRAME M1 -> PINV A1 M1 model1 b1 cap1 (xs ++ doneL l j) ->
      (forall R3 M3 A3 model3 b3 cap3, j + 1 < Zlen l -> AT R3 (j + 1) -> FRAME M3 -> PINV A3 M3 model3 b3 cap3 (xs ++ doneL l (j + 1)) ->
         srealizes SEGS (mkCfg (@mkst fx R3 (Z_to_bv 64 PT_BODY) M3 (seg_rom SEGS)) model3) K) ->
      (forall R3 M3 A3 model3 b3 cap3, j + 1 = Zlen l -> REGS R3 -> FRAME M3 -> PINV A3 M3 model3 b3 cap3 (xs ++ doneL l (j + 1)) ->
         srealizes SEGS (mkCfg (@mkst fx R3 (Z_to_bv 64 PT_EXIT) M3 (seg_rom SEGS)) model3) K) ->
      srealizes SEGS (mkCfg (@mkst fx R1 (Z_to_bv 64 PT_BODY) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST cpbs MSpos Hcpbs PBS fx A s R M model sp ret pspan pat b cap p xs l K CB Fp Fl RSP Hp4 Hll Hl31 Hpsc Hps47 Hpsw VEC OBJ PAT8 DJ NMX RP.
      intros j R1 M1 A1 model1 b1 cap1 Hj (G10 & G20 & G8 & G9 & G18 & G19 & G21 & GRS) FR PI HKc HKx. pose proof GRS as (G2 & G3 & G4 & Ghi).
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK'). pose proof Hcpbs as [Hent Hst].
      pose proof PI as [AI MS FS SX ROC VEC' PP EF WIN]. pose proof RSP as (Hp0 & Hp1 & RS).
      pose proof VEC' as (Hv0 & Hv1 & HD & Hlen & Hbb & F0 & F1 & F2 & FEL). pose proof (PCargs pat_win) as PW.
      set (ys := xs ++ doneL l j) in *.
      set (i := Zlen l - 1 - j). set (t := Znth i l).
      assert (Ht : 0 <= t < 2 ^ 31) by (subst t i; unfold Znth, Zlen in *; apply (proj1 (Forall_nth _ _) Hl31); lia).
      assert (Ft : fld SEGS M1 (p + 4 * i) 4 t) by (subst t i; apply (RS M1 (roc_roU M1 ROC)); lia).
      destruct (pspan_cells A1 M1 model1 b1 cap1 _ PI) as [Fp1 Fl1].
      pose proof (doneL_step l j Hj) as DS. fold i in DS. fold t in DS.
      assert (Hys : 0 <= Zlen ys /\ Zlen ys = Zlen xs + Zlen (doneL l j)) by (subst ys; rewrite Zlen_app; unfold Zlen; lia).
      pose proof (doneL_len l j ltac:(lia)) as DL.
      pose (E := Eseed R1 [Z_to_bv 64 (sp - 64); Z_to_bv 64 pspan; Z_to_bv 64 pat; Z_to_bv 64 (Zlen l); Z_to_bv 64 j; Z_to_bv 64 (j + 1); Z_to_bv 64 p; Z_to_bv 64 t;
                           Z_to_bv 64 (b1 + 4 * Zlen ys); Z_to_bv 64 (b1 + 4 * cap1); Z_to_bv 64 t]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EVar 34); (18%bv, EVar 35); (10%bv, EVar 36); (20%bv, EVar 37); (19%bv, ELit (2 ^ 61)); (21%bv, ELit 5)]) R1).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (G32 : ev E 32 = Z_to_bv 64 (sp - 64)) by (evs; reflexivity). assert (G33 : ev E 33 = Z_to_bv 64 pspan) by (evs; reflexivity).
      assert (G34 : ev E 34 = Z_to_bv 64 pat) by (evs; reflexivity). assert (G38 : ev E 38 = Z_to_bv 64 p) by (evs; reflexivity).
      assert (G40 : ev E 40 = Z_to_bv 64 (b1 + 4 * Zlen ys)) by (evs; reflexivity). assert (G41 : ev E 41 = Z_to_bv 64 (b1 + 4 * cap1)) by (evs; reflexivity).

      set (KN := [KWord (SA (EVar 33) 0) (N.to_nat 8) (EVar 38); KWr (SA (EVar 32) 0) (ELit 64);
           KRange (EVar 38) 0x10000 (2 ^ 47); KAlign (EVar 38) 4; KRange (EVar 35) 1 33; KRange (EVar 36) 0 32;
           KWord (SA (EVar 34) 8) (N.to_nat 8) (EVar 40); KWord (SA (EVar 34) 16) (N.to_nat 8) (EVar 41);
           KWr (SA (EVar 34) 0) (ELit 24); KDisj (SA (EVar 34) 0) (ELit 24) (SA (EVar 32) 0) (ELit 64)]).
      assert (HK : know_ok SEGS E M1 KN).
      { subst KN. repeat apply Forall_cons; [kwv Fp1 G33 | | | | | | kwv F1 G34 | kwv F2 G34 | | | apply Forall_nil].
        - eapply (kwr_of_mdef SEGS E M1 32 (sp - 64) 0 64); [exact G32 | lia | lia | lia | lia |]. rewrite Z.add_0_r. intros k Hk. replace (sp - 64 + k) with (sp - STK + (STK - 64 + k)) by lia. apply WIN. lia.
        - eapply krange_var; [exact G38 | lia | lia].
        - eapply kalign_var; [exact G38 | lia | lia | exact Hp4].
        - eapply krange_var; [evs; reflexivity | lia | lia].
        - eapply krange_var; [evs; reflexivity | lia | lia].
        - eapply (kwr_of_mdef SEGS E M1 34 pat 0 24); [exact G34 | lia | lia | lia | lia |]. rewrite Z.add_0_r. exact HD.
        - eapply (kdisj_vars SEGS E M1 34 32 pat (sp - 64)); [exact G34 | exact G32 | lia | lia | lia | lia | lia]. }
      assert (CELL : cellw SEGS M1 (p + 4 * i) 4 t) by (split; [cbn; lia | exact Ft]).
      assert (ADDR : alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 4) (Z_to_bv 64 (Zlen l))) (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-4)) (Z_to_bv 64 j)) (Z_to_bv 64 p))
                     = Z_to_bv 64 (p + 4 * i + 4)).
      { rewrite !zbv_mul, !zbv_add. f_equal. subst i. lia. }
      assert (RD : sc_denot SEGS M1 E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 35)) (EAlu ALU_ADD (EMd M_MUL (ELit (-4)) (EVar 36)) (EVar 38))) (-4)) 4 true (EVar 42))).
      { eapply (sc_read_cell4_sx _ _ _ _ _ _ _ CELL); [unfold adenot; cbn [a_base a_off]; evs; rewrite ADDR, v_addi_Z by lia; f_equal; lia | evs; rewrite sxw_small by lia; reflexivity]. }
      assert (WRAP : sc_denot SEGS M1 E (SCBr false BC_LTU
                (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 35)) (EAlu ALU_ADD (EMd M_MUL (ELit (-4)) (EVar 36)) (EVar 38))) (ELit (-4))) (EVar 38))).
      { cbn [sc_denot]. evs. rewrite ADDR, zbv_add. rewrite br_ltu by lia. bool_lia. }
      assert (LT0 : sc_denot SEGS M1 E (SCBr false BC_LT (EVar 42) (ELit 0))).
      { cbn [sc_denot]. evs. rewrite br_lt by lia. bool_lia. }
      assert (EQ0 : forall bb : bool, (if bb then t = 0 else t <> 0) -> sc_denot SEGS M1 E (SCBr bb BC_EQ (EVar 42) (ELit 0))).
      { intros bb Hb. cbn [sc_denot]. evs. rewrite br_eq by lia. destruct bb; bool_lia. }
      assert (STI : stores_in (zwin (sp - 64) sp) M1 (wbytes M1 (Z_to_bv 64 (sp - 60)) (word_to_le_bytes 4 (Z_to_bv 64 t)))).
      { apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; [lia | cbn; lia |]. intros a Ha. cbn in Ha. unfold zwin. lia. }
      pose proof (PCargs pinv_stores A1 M1 model1 b1 cap1 ys PI _ STI) as PI2.
      assert (FRx : forall M2, agree_on (zwin (sp - 56) sp) (wbytes M1 (Z_to_bv 64 (sp - 60)) (word_to_le_bytes 4 (Z_to_bv 64 t))) M2 -> FRAME M2).
      { intros M2 AG. eapply FRAME_agree; [exact FR|]. intros a Ha. rewrite (AG a Ha).
        pose proof (frame_wbytes4 (zwin (sp - 60) (sp - 56)) M1 (sp - 60) (Z_to_bv 64 t) ltac:(lia) ltac:(lia) ltac:(intros x Hx; unfold zwin; lia)) as FRw.
        apply FRw. rewrite u64_of_Z by (unfold zwin in Ha; lia). unfold zwin in *. lia. }
      destruct (Z.eq_dec t 0) as [Tz|Tnz].
      -
        xruns HR HK 60%nat PT_STOPS (SCR [false; false; true] [EVar 42] []) 41%N.
        { split_scs; first [exact RD | exact WRAP | exact LT0 | apply EQ0; exact Tz | sc_fl]. }
        match goal with |- srealizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
          replace Mx with (wbytes M1 (Z_to_bv 64 (sp - 60)) (word_to_le_bytes 4 (Z_to_bv 64 t)))
            by (unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; f_equal; f_equal; lia) end.
        rewrite Tz in DS. cbn in DS. rewrite app_nil_r in DS.
        eapply (LOOP2 j R' _ model1 Hj MS);
          [ rreg HR' 20%bv X; exact X | rreg HR' 8%bv X; exact X | rreg HR' 9%bv X; exact X | rreg HR' 18%bv X; exact X
          | rreg HR' 19%bv X; exact X | rreg HR' 21%bv X; exact X | | |].
        + split; [|split; [|split]]; [rreg HR' 2%bv X; exact X | rreg HR' 3%bv X; rewrite X; regeq G3 | rreg HR' 4%bv X; rewrite X; regeq G4 | hi_regs HR' Ghi].
        + intros R3 Hlt AT3. eapply (HKc R3 _ A1 model1 b1 cap1 Hlt AT3). { apply FRx. intros a _; reflexivity. } rewrite DS. exact PI2.
        + intros R3 Heq RG3. eapply (HKx R3 _ A1 model1 b1 cap1 Heq RG3). { apply FRx. intros a _; reflexivity. } rewrite DS. exact PI2.
      - assert (DS' : doneL l (j + 1) = doneL l j ++ [t]) by (rewrite DS; destruct (Z.eqb_spec t OT_NONE); [exfalso; unfold OT_NONE in *; lia | reflexivity]).
        destruct (Z_lt_le_dec (Zlen ys) cap1) as [Hroom|Hfull].
        +
          destruct Hbb as [[Hb0 Hc0]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [lia|].
          destruct (ai_live_block MI A1 M1 model1 b1 (4 * cap1) AI HIn) as (_ & Hal16 & _ & Hce & Hblk).
          assert (Hb16 : 16 <= b1) by (destruct (Z_le_gt_dec 16 b1); [lia|]; rewrite Z.mod_small in Hal16 by lia; lia).
          pose proof (mod4_of_16 b1 (Zlen ys) Hal16) as Hb4.
          assert (HK2 : know_ok SEGS E M1 (KN ++ [KRange (EVar 40) 16 (2 ^ 47); KAlign (EVar 40) 4])).
          { apply Forall_app. split; [exact HK|]. repeat apply Forall_cons; [ | | apply Forall_nil].
            - eapply krange_var; [exact G40 | lia | lia].
            - eapply kalign_var; [exact G40 | lia | lia | exact Hb4]. }
          assert (HK3 : know_ok SEGS E M1 ((KN ++ [KRange (EVar 40) 16 (2 ^ 47); KAlign (EVar 40) 4]) ++ [KWr (SA (EVar 40) 0) (ELit 4)])).
          { apply Forall_app. split; [exact HK2|]. apply Forall_cons; [|apply Forall_nil].
            eapply (kwr_of_mdef SEGS E M1 40 (b1 + 4 * Zlen ys) 0 4); [exact G40 | lia | lia | lia | lia |].
            rewrite Z.add_0_r. intros k Hk. exact (proj2 (proj2 (Hblk (b1 + 4 * Zlen ys + k) ltac:(lia)))). }
          clear HK HK2. cbn [app] in HK3.
          xruns HR HK3 60%nat PT_STOPS (SCR [false; false; false; false] [EVar 42] []) 41%N.
          { split_scs; first [exact RD | exact WRAP | exact LT0 | apply EQ0; exact Tnz | sc_fl | cbn [sc_denot]; evs; rewrite br_geu by lia; bool_lia]. }
          unfold adenot; cbn [a_base a_off]; evs; rewrite ?v_addi_Z by lia; rewrite ?zbv_add.
          replace (sp - 64 + 4) with (sp - 60) by lia. rewrite (Z.add_0_r (b1 + 4 * Zlen ys)).
          match goal with |- srealizes _ (mkCfg (mkst _ _ ?Mx _) _) _ => set (M3 := Mx) end.
          assert (PI3 : PINV A1 M3 model1 b1 cap1 (ys ++ [t])) by (eapply (PCargs pinv_push_fast); [exact PI2 | exact Hroom | lia | reflexivity]).
          assert (FR3 : FRAME M3).
          { apply FRx. subst M3. intros a Ha. unfold zwin in Ha.
            rewrite (frame_wbytes8 (zwin pat (pat + 24)) _ (pat + 8) _ ltac:(lia) ltac:(lia) ltac:(intros x Hx; unfold zwin; lia)) by (rewrite u64_of_Z by lia; unfold zwin; lia).
            rewrite (frame_wbytes4 (zwin b1 (b1 + 4 * cap1)) _ (b1 + 4 * Zlen ys) _ ltac:(lia) ltac:(lia) ltac:(intros x Hx; unfold zwin; lia)) by (rewrite u64_of_Z by lia; unfold zwin; lia).
            reflexivity. }
          subst ys. rewrite <- app_assoc, <- DS' in PI3.
          eapply (LOOP2 j R' _ model1 Hj MS);
            [ rreg HR' 20%bv X; exact X | rreg HR' 8%bv X; exact X | rreg HR' 9%bv X; exact X | rreg HR' 18%bv X; exact X
            | rreg HR' 19%bv X; exact X | rreg HR' 21%bv X; exact X | | |].
          * split; [|split; [|split]]; [rreg HR' 2%bv X; exact X | rreg HR' 3%bv X; rewrite X; regeq G3 | rreg HR' 4%bv X; rewrite X; regeq G4 | hi_regs HR' Ghi].
          * intros R3 Hlt AT3. exact (HKc R3 _ A1 model1 b1 cap1 Hlt AT3 FR3 PI3).
          * intros R3 Heq RG3. exact (HKx R3 _ A1 model1 b1 cap1 Heq RG3 FR3 PI3).
        +
          subst KN.
          xruns HR HK 60%nat PT_STOPS (SCR [false; false; false; true] [EVar 42] []) 41%N.
          { split_scs; first [exact RD | exact WRAP | exact LT0 | apply EQ0; exact Tnz | sc_fl | cbn [sc_denot]; evs; rewrite br_geu by lia; bool_lia]. }
          unfold adenot; cbn [a_base a_off]; evs; rewrite ?v_addi_Z by lia; rewrite ?zbv_add.
          replace (sp - 64 + 4) with (sp - 60) by lia.
          rreg HR' 10%bv A10. rreg HR' 11%bv A11. rreg HR' 2%bv A2. rreg HR' 1%bv A1'. rreg HR' 3%bv A3. rreg HR' 4%bv A4.
          replace (Z_to_bv 64 448568) with (Z_to_bv 64 (vc_entry cpbs) : word) by (rewrite Hent; reflexivity).
          eapply ((PCargs pinv_pbslow) (2 ^ 31) _ cpbs A1 _ model1 b1 cap1 ys R' PT_JOIN (sp - 60) t K PBS);
            [ lia | exact PAT8 | lia | unfold STK; lia | exact PI2 | lia | change (Z.of_nat (length l)) with (Zlen l); lia | lia
            | exact A10 | rewrite A11, ?zbv_add; f_equal; lia | exact A2 | exact A1' | apply bv_eq; vm_compute; reflexivity | unfold PT_JOIN; lia
            | rewrite A3; regeq G3 | rewrite A4; regeq G4 | lia | lia
            | replace (sp - 60) with ((sp / 16 * 4 - 15) * 4) by (pose proof (Z_div_mod_eq_full sp 16); lia); apply Z_mod_mult
            | apply (fld_wbytes4 SEGS); lia | lia | ].

          intros A' R'' M' model' b' cap' PI' KEPT AG A10'.
          pose proof PI' as [AI' MS' _ _ _ VEC'' _ _ _]. pose proof VEC'' as (_ & _ & HD' & Hlen' & Hbb' & _).
          rewrite Zlen_app1 in Hlen'.
          destruct Hbb' as [[-> Hc0']|(Hbp' & Hal' & Hcp' & _ & HIn' & Hdj')]; [lia|].
          assert (Hb16' : 16 <= b') by (destruct (Z_le_gt_dec 16 b'); [lia|]; rewrite Z.mod_small in Hal' by lia; lia).
          pose proof (mod4_of_16 b' (Zlen ys + 1) Hal') as Hb4'.
          destruct (ai_live_block MI A' M' model' b' (4 * cap') AI' HIn') as (_ & _ & _ & Hce' & _).
          assert (FR' : FRAME M') by (apply FRx; eapply agree_on_weaken; [exact AG|]; intros a Ha; unfold zwin in *; lia).
          assert (KR : forall r, In r callee_saved -> getr R'' r = getr R' r) by (intros r Hr; exact (KEPT r Hr)).

          assert (S2 : getr R'' 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KR 2%bv) by inl; exact A2).
          assert (S3 : getr R'' 3%bv = getr R 3%bv) by (rewrite (KR 3%bv) by inl; rewrite A3; regeq G3).
          assert (S4 : getr R'' 4%bv = getr R 4%bv) by (rewrite (KR 4%bv) by inl; rewrite A4; regeq G4).
          assert (S8 : getr R'' 8%bv = Z_to_bv 64 pspan) by (rewrite (KR 8%bv) by inl; rreg HR' 8%bv X; exact X).
          assert (S9 : getr R'' 9%bv = Z_to_bv 64 pat) by (rewrite (KR 9%bv) by inl; rreg HR' 9%bv X; exact X).
          assert (S18 : getr R'' 18%bv = Z_to_bv 64 (Zlen l)) by (rewrite (KR 18%bv) by inl; rreg HR' 18%bv X; exact X).
          assert (S19 : getr R'' 19%bv = Z_to_bv 64 (2 ^ 61)) by (rewrite (KR 19%bv) by inl; rreg HR' 19%bv X; exact X).
          assert (S20 : getr R'' 20%bv = Z_to_bv 64 (j + 1)) by (rewrite (KR 20%bv) by inl; rreg HR' 20%bv X; exact X).
          assert (S21 : getr R'' 21%bv = Z_to_bv 64 5) by (rewrite (KR 21%bv) by inl; rreg HR' 21%bv X; exact X).
          assert (Shi : forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr R'' r = getr R r).
          { intros r Hr. rewrite (KR r) by (cbn in Hr |- *; clear -Hr; intuition). revert r Hr. hi_regs HR' Ghi. }
          clear HR' Hlf KR KEPT.
          pose (E2 := Eseed R'' [Z_to_bv 64 (sp - 64); Z_to_bv 64 pat; Z_to_bv 64 (b' + 4 * (Zlen ys + 1))]).
          assert (HR2 : regs_ok E2 (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 33); (10%bv, EVar 34); (21%bv, ELit 5)]) R'').
          { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
          assert (HK4 : know_ok SEGS E2 M' [KWr (SA (EVar 33) 0) (ELit 24); KRange (EVar 34) 16 (2 ^ 47); KAlign (EVar 34) 4]).
          { repeat apply Forall_cons; [ | | | apply Forall_nil].
            - eapply (kwr_of_mdef SEGS E2 M' 33 pat 0 24); [evs; reflexivity | lia | lia | lia | lia |]. rewrite Z.add_0_r. exact HD'.
            - eapply krange_var; [evs; reflexivity | lia | lia].
            - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hb4']. }
          xruns HR2 HK4 30%nat PT_STOPS (SCR [] [] []) 40%N; [split_scs; sc_fl|].
          unfold adenot; cbn [a_base a_off]; evs; rewrite ?v_addi_Z by lia.
          match goal with |- srealizes _ (mkCfg (mkst _ _ ?Mx _) _) _ => set (M4 := Mx) end.
          assert (PI4 : PINV A' M4 model' b' cap' (ys ++ [t])).
          { rewrite <- (firstn_all (ys ++ [t])). replace (length (ys ++ [t])) with (Z.to_nat (Zlen ys + 1)) by (unfold Zlen; rewrite length_app; cbn; lia).
            eapply (PCargs pinv_set_len); [exact PI' | rewrite Zlen_app1; lia | subst M4; do 3 f_equal; lia]. }
          assert (FR4 : FRAME M4).
          { eapply FRAME_agree; [exact FR'|]. subst M4. intros a Ha. unfold zwin in Ha.
            rewrite (frame_wbytes8 (zwin pat (pat + 24)) _ (pat + 8) _ ltac:(lia) ltac:(lia) ltac:(intros x Hx; unfold zwin; lia)) by (rewrite u64_of_Z by lia; unfold zwin; lia).
            reflexivity. }
          subst ys. rewrite <- app_assoc, <- DS' in PI4.
          lazymatch goal with |- srealizes _ (mkCfg (mkst ?Rn _ _ _) _) _ => eapply (LOOP2 j Rn _ model' Hj MS') end;
            [ rreg HR' 20%bv X; rewrite X; regeq S20 | rreg HR' 8%bv X; rewrite X; regeq S8 | rreg HR' 9%bv X; exact X
            | rreg HR' 18%bv X; rewrite X; regeq S18 | rreg HR' 19%bv X; rewrite X; regeq S19 | rreg HR' 21%bv X; exact X | | |].
          * split; [|split; [|split]]; [rreg HR' 2%bv X; exact X | rreg HR' 3%bv X; rewrite X; regeq S3 | rreg HR' 4%bv X; rewrite X; regeq S4 | hi_regs HR' Shi].
          * intros R3 Hlt AT3. exact (HKc R3 _ A' model' b' cap' Hlt AT3 FR4 PI4).
          * intros R3 Heq RG3. exact (HKx R3 _ A' model' b' cap' Heq RG3 FR4 PI4).
    Qed.

    Lemma LOOP : forall (n : nat) j R1 M1 A1 model1 b1 cap1,
      Zlen l - j <= Z.of_nat n -> 0 <= j < Zlen l -> AT R1 j -> FRAME M1 -> PINV A1 M1 model1 b1 cap1 (xs ++ doneL l j) ->
      srealizes SEGS (mkCfg (@mkst fx R1 (Z_to_bv 64 PT_BODY) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST cpbs MSpos Hcpbs PBS fx A s R M model sp ret pspan pat b cap p xs l K CB Fp Fl RSP Hp4 Hll Hl31 Hpsc Hps47 Hpsw VEC OBJ PAT8 DJ NMX RP CONT.
      induction n as [|n IH]; intros j R1 M1 A1 model1 b1 cap1 Hn Hj AT1 FR PI; [lia|].
      eapply STEP; [exact Hj | exact AT1 | exact FR | exact PI | |].
      - intros R3 M3 A3 model3 b3 cap3 Hlt AT3 FR3 PI3. eapply (IH (j + 1)); [lia | lia | exact AT3 | exact FR3 | exact PI3].
      - intros R3 M3 A3 model3 b3 cap3 Heq RG3 FR3 PI3. rewrite Heq, doneL_all in PI3. exact (EXIT R3 M3 A3 model3 b3 cap3 PI3 RG3 FR3).
    Qed.

    Lemma ENTRY : srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 PT_ENTRY) M (seg_rom SEGS)) model) K.
    Proof using AC MI ST cpbs MSpos Hcpbs PBS fx A s R M model sp ret pspan pat b cap p xs l K CB Ha0 Ha1 Fp Fl RSP Hp4 Hll Hl31 Hpsc Hps47 Hpsw VEC OBJ PAT8 DJ NMX RP CONT.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK').
      pose proof (PCargs pinv_init) as PI0. pose proof PI0 as [AI MS FS SX ROC VEC' PP EF WIN]. pose proof CB as CB'.
      destruct CB' as [_ _ _ _ _ [_ _ _ _ _ _ Hgp Htp] _ _ _ _ _].
      pose proof RSP as (Hp0 & Hp1 & RS). pose proof VEC as (Hv0 & Hv1 & HD & _). pose proof (PCargs pat_win) as PW.
      assert (HL0 : 0 <= Zlen l) by (unfold Zlen; lia).
      assert (Hpat1 : 1 <= pat).
      { destruct OBJ as [[Hhi|(q & k & Hin & H1 & H2)] _]; [lia|]. destruct (ai_live_block MI A M model q k AI Hin) as (_ & _ & Hq & _). lia. }
      pose (E := Eseed R [Z_to_bv 64 sp; Z_to_bv 64 pspan; Z_to_bv 64 pat; Z_to_bv 64 (Zlen l)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (PSD : pspan + 16 <= sp - 64 \/ sp <= pspan).
      { destruct (Z.lt_ge_cases pspan sp); [left|right; lia].
        destruct (Z.lt_ge_cases pspan (sp - STK)); [lia|]. exfalso. apply (Hpsw pspan); unfold zwin; lia. }
      assert (HK : know_ok SEGS E M [KWord (SA (EVar 33) 8) (N.to_nat 8) (EVar 35); KWr (SA (EVar 32) (-64)) (ELit 64);
                                    KDisj (SA (EVar 33) 0) (ELit 16) (SA (EVar 32) (-64)) (ELit 64);
                                    KRange (EVar 34) 1 (2 ^ 63); KAlign (EVar 34) 8]).
      { assert (G33 : ev E 33 = Z_to_bv 64 pspan) by (evs; reflexivity). assert (G32 : ev E 32 = Z_to_bv 64 sp) by (evs; reflexivity).
        assert (G34 : ev E 34 = Z_to_bv 64 pat) by (evs; reflexivity).
        repeat apply Forall_cons; [kwv Fl G33 | | | | | apply Forall_nil].
        - eapply (kwr_of_mdef SEGS E M 32 sp (-64) 64); [exact G32 | lia | lia | lia | lia |].
          intros k Hk. replace (sp + -64 + k) with (sp - STK + (STK - 64 + k)) by lia. apply WIN. lia.
        - eapply (kdisj_vars SEGS E M 33 32 pspan sp); [exact G33 | exact G32 | lia | lia | lia | lia | lia].
        - eapply krange_var; [exact G34 | lia | lia].
        - eapply kalign_var; [exact G34 | lia | lia | exact PAT8]. }

      set (M1 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
                   (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (getr R 1%bv)))
                   (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 (getr R 8%bv)))
                   (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 (getr R 9%bv)))
                   (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 (getr R 18%bv)))
                   (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 (getr R 19%bv)))
                   (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 (getr R 20%bv)))
                   (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 (getr R 21%bv))).
      assert (STI : stores_in (zwin (sp - 64) sp) M M1).
      { subst M1. repeat (apply stores_in_wbytes_more || apply stores_in_wbytes); rewrite ?length_N_to_le_bytes;
          first [apply stores_in_refl | lia | cbn; lia | intros x Hx; cbn in Hx; unfold zwin; lia]. }
      assert (FR1 : FRAME M1).
      { subst M1. unfold FRAME, cellw.
        repeat match goal with |- _ /\ _ => split end; try apply u64_range; rewrite Z_to_bv_bv_unsigned;
        repeat (rewrite CatExec.rdn_wbytes_out; [| rewrite ?length_N_to_le_bytes, !u64_of_Z by lia; cbn; lia | rewrite !u64_of_Z by lia; cbn; lia | rewrite ?length_N_to_le_bytes, !u64_of_Z by lia; cbn; lia]);
        (apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia). }
      pose proof (PCargs pinv_stores A M model b cap xs PI0 M1 STI) as PI1.
      assert (RG : forall Rx sr, regs_ok E sr Rx ->
                   sr_get sr 2%bv = EAlu ALU_ADD (EVar 32) (ELit (-64)) -> syms_id sr [3; 4; 22; 23; 24; 25; 26; 27]%bv = true -> REGS Rx).
      { intros Rx sr HRx Hspx Hs. pose proof (syms_id_sound _ _ _ _ _ HRx Hs) as SY.
        split; [|split; [|split]].
        - rewrite (HRx 2%bv), Hspx. cbn [edenot]. evs. rewrite zbv_add. f_equal; lia.
        - apply SY. inl. - apply SY. inl.
        - intros r Hr. apply SY. cbn in Hr |- *. clear -Hr. intuition. }
      destruct (Z.eq_dec (Zlen l) 0) as [Hz|Hnz].
      -
        xruns HR HK 40%nat PT_STOPS (SCR [true] [] []) 40%N. { split_scs; first [sc_fl | sc_br]. }
        match goal with |- srealizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
          replace Mx with M1 by (subst M1; unfold adenot; cbn [a_base a_off]; evs; rewrite !v_addi_Z by lia;
                                 repeat first [reflexivity | f_equal; try (f_equal; lia)]) end.
        apply (EXIT R' M1 A model b cap); [| apply (RG _ _ HR'); reflexivity | exact FR1].
        replace (push_types l xs) with xs; [exact PI1|].
        unfold push_types. destruct l; [rewrite app_nil_r; reflexivity | unfold Zlen in Hz; cbn in Hz; lia].
      - xruns HR HK 40%nat PT_STOPS (SCR [false] [] []) 40%N. { split_scs; first [sc_fl | sc_br]. }
        match goal with |- srealizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
          replace Mx with M1 by (subst M1; unfold adenot; cbn [a_base a_off]; evs; rewrite !v_addi_Z by lia;
                                 repeat first [reflexivity | f_equal; try (f_equal; lia)]) end.
        apply (LOOP (length l) 0 R' M1 A model b cap); [unfold Zlen; lia | lia | | exact FR1 | rewrite doneL_0, app_nil_r; exact PI1].
        unfold AT. repeat match goal with |- _ /\ _ => split end; try (apply (RG _ _ HR'); reflexivity).
        + rreg HR' 10%bv X; exact X. + rreg HR' 20%bv X; exact X. + rreg HR' 8%bv X; exact X. + rreg HR' 9%bv X; exact X.
        + rreg HR' 18%bv X; exact X. + rreg HR' 19%bv X; rewrite X; apply bv_eq; vm_compute; reflexivity. + rreg HR' 21%bv X; exact X.
    Qed.
  End Body.

  Theorem push_types_spec : push_types_stmt SEGS L MI ST TG tc cpbs.
  Proof using AC MI ST cpbs MSpos Hcpbs PBS.
    intros fx A s R M model sp ret pspan pat b cap p xs l K.
    cbn [tc_pattern_stack tc_push_types Img.tc g_maxlen TG TablData.MAXLEN].
    intros CB _ Ha0 Ha1 Fp Fl RSP Hp4 Hll Hl31 Hpsc Hps47 Hpsw VEC OBJ PAT8 DJ NMX RP CONT.
    eapply (ENTRY fx A s R M model sp ret pspan pat b cap p xs l K); eassumption.
  Qed.
End PT.
