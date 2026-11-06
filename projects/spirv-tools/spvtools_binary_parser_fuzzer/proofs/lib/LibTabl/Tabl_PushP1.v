(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablVia.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablPush.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_6ba90_6bb2c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
End S1_code_6ba90_6bb2c.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3 MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablVia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablStmts TablLib TablPush.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_PushP1.S1_code_6ba90_6bb2c.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgP1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgP1.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation tc := Img.tc.

Definition PT_ENTRY : Z := 0x6bad0.
Definition PT_BODY  : Z := 0x6bb1c.
Definition PT_LOOP2 : Z := 0x6bb0c.
Definition PT_RET1  : Z := 0x6bb48.
Definition PT_EXIT  : Z := 0x6bb4c.
Definition PB_ENTRY : Z := 0x6b99c.
Definition PT_STOPS : list Z := [PT_BODY; PT_EXIT; PB_ENTRY].

Definition cpbP1 : vec_consts := {| vc_entry := 0x6b99c; vc_stack := 64 |}.

Lemma LYP1 {AC : AllocCeiling} : lay_ok SEGS L.
Proof.
  constructor.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_errno_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
  - intros x Hx. apply ly_noseg. pose proof ac_bounds_lit. lia.
Qed.

Lemma roc_ro : forall M, img_ro_clear L M -> ro_clear L M.
Proof. intros M H w (Hi & Hn & _). exact (H w Hi Hn). Qed.

Definition doneL (l : list Z) (j : Z) : list Z :=
  filter (fun t => negb (t =? OT_NONE)) (rev (skipn (Z.to_nat (Zlen l - j)) l)).

Lemma doneL_0 : forall l, doneL l 0 = [].
Proof. intros l. unfold doneL. rewrite Z.sub_0_r. unfold Zlen. rewrite Nat2Z.id, skipn_all. reflexivity. Qed.

Lemma doneL_all : forall l xs, xs ++ doneL l (Zlen l) = push_types l xs.
Proof. intros l xs. unfold doneL, push_types. rewrite Z.sub_diag. reflexivity. Qed.

Lemma skipn_last : forall (l : list Z) k, (k < length l)%nat ->
  skipn k l = nth k l 0 :: skipn (S k) l.
Proof.
  induction l as [|y l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma doneL_step : forall l j, 0 <= j < Zlen l ->
  doneL l (j + 1) = doneL l j ++ (if Znth (Zlen l - 1 - j) l =? OT_NONE then [] else [Znth (Zlen l - 1 - j) l]).
Proof.
  intros l j Hj. unfold doneL, Znth, Zlen in *.
  replace (Z.to_nat (Z.of_nat (length l) - j)) with (S (Z.to_nat (Z.of_nat (length l) - (j + 1)))) by lia.
  rewrite (skipn_last l (Z.to_nat (Z.of_nat (length l) - (j + 1)))) by lia.
  match goal with |- context [rev (?x :: ?r)] => change (rev (x :: r)) with (rev r ++ [x]) end.
  rewrite list_basics.list.filter_app. cbn [filter list_basics.list.list_filter decide Is_true_dec].
  replace (Z.to_nat (Z.of_nat (length l) - 1 - j)) with (Z.to_nat (Z.of_nat (length l) - (j + 1))) by lia.
  destruct (_ =? OT_NONE); cbn; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma Zlen_app : forall (a c : list Z), Zlen (a ++ c) = Zlen a + Zlen c.
Proof. intros a c. unfold Zlen. rewrite length_app. lia. Qed.

Lemma doneL_len : forall l j, 0 <= j <= Zlen l -> 0 <= Zlen (doneL l j) <= j.
Proof.
  intros l j Hj. unfold doneL, Zlen in *.
  pose proof (list_basics.list.length_filter (λ t0 : Z, negb (t0 =? OT_NONE)) (rev (skipn (Z.to_nat (Z.of_nat (length l) - j)) l))) as H1.
  rewrite length_rev, length_skipn in H1. lia.
Qed.

Lemma rdn_noseg_mdef : forall Mx a (k : nat) bs,
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

Lemma fld_hi_mdef {AC : AllocCeiling} : forall Mx a (k : nat) v, fld SEGS Mx a k v -> alloc_ceiling <= a -> a + Z.of_nat k < 2 ^ 64 -> mdef Mx a (Z.of_nat k).
Proof.
  intros Mx a k v HF Ha Hk. pose proof ac_bounds_lit.
  eapply rdn_noseg_mdef; [exact HF | lia | lia |]. intros x Hx. apply ly_noseg. lia.
Qed.

Lemma zext32_val : forall a, 0 <= a < 2 ^ 32 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) (Z_to_bv 64 a)) (Z_to_bv 64 32) = Z_to_bv 64 a.
Proof.
  intros a Ha. rewrite zbv_mul, w_srl by lia. f_equal. change (2 ^ 32) with 4294967296. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Section PT.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Hypothesis MSpos : 0 <= MALLOC_STACK MI.
  Hypothesis PB : vec32_push_back_stmt SEGS L MI ST cpbP1.

  Section Body.
    Variables (fx : FPState) (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret pspan pat b cap p : Z) (xs l : list Z) (K : TSet).
    Definition STK : Z := 96 + (64 + NEW_STACK SEGS L MI).
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
    Proof using AC MI ST MSpos A s R M model sp ret pat b cap p xs l CB VEC OBJ NMX RP.
      constructor.
      - exact LYP1. - exact MSpos. - exact CB. - exact VEC. - exact OBJ.
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
      cellw SEGS M1 (sp - 40) 8 (bv_unsigned (getr R 19%bv)) /\ cellw SEGS M1 (sp - 48) 8 (bv_unsigned (getr R 20%bv)).

    Definition REGS (R1 : bvmap 5 word) : Prop :=
      getr R1 2%bv = Z_to_bv 64 (sp - 64) /\ getr R1 3%bv = getr R 3%bv /\ getr R1 4%bv = getr R 4%bv /\
      forall r, In r [21; 22; 23; 24; 25; 26; 27]%bv -> getr R1 r = getr R r.

    #[local] Ltac dCB := destruct CB as [AI0 MS0 ROC0 SX0 SXH0 CR0 Hceil0 HROOM0 Hwin0 Hown_sx0 Herr_sx0].

    Lemma spf : alloc_ceiling + STK <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\ 2 ^ 24 <= sp - STK /\
                getr R 2%bv = Z_to_bv 64 sp /\ getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\ STK = 96 + (64 + (16 + MALLOC_STACK MI)) /\ 176 <= STK.
    Proof using AC MI ST MSpos A s R M model sp ret p CB. dCB. destruct CR0. pose proof ac_bounds_lit. pose proof MSpos. unfold STK, NEW_STACK in *. repeat split; try assumption; lia. Qed.

    Lemma FRAME_agree : forall M1 M2, FRAME M1 -> agree_on (zwin (sp - 48) sp) M1 M2 -> FRAME M2.
    Proof using AC MI ST MSpos A s R M model sp ret p CB.
      intros M1 M2 (C1 & C2 & C3 & C4 & C5 & C6) AG. pose proof spf as (Hc & Hs47 & _ & Hcv & _ & _ & _ & _ & _ & HSTK).
      assert (G : forall a v, cellw SEGS M1 a 8 v -> sp - 48 <= a -> a + 8 <= sp -> cellw SEGS M2 a 8 v).
      { intros a v [Hv Hr] H1 H2. split; [exact Hv|]. eapply (fld_agree SEGS M1 M2 a 8 v); [lia | cbn; lia | exact Hr |].
        eapply agree_on_weaken; [exact AG|]. intros x Hx. unfold zwin in *. cbn in Hx. lia. }
      repeat split; (eapply G; [eassumption | lia | lia]).
    Qed.

    Lemma EXIT : forall R1 M1 A1 model1 b1 cap1,
      PINV A1 M1 model1 b1 cap1 (push_types l xs) -> REGS R1 -> FRAME M1 ->
      srealizes SEGS (mkCfg (@mkst fx R1 (Z_to_bv 64 PT_EXIT) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST MSpos fx A s R M model sp ret pat b cap p xs l K CB CONT.
      intros R1 M1 A1 model1 b1 cap1 PI (G2 & G3 & G4 & Ghi) (C1 & C2 & C3 & C4 & C5 & C6).
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK').
      pose proof PI as [AI MS FS SX ROC VEC' PP EF WIN].
      pose (E := Eseed R1 [Z_to_bv 64 (sp - 64); getr R 1%bv; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R1).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M1 [KWord (SA (EVar 32) 56) (N.to_nat 8) (EVar 33); KWord (SA (EVar 32) 48) (N.to_nat 8) (EVar 34); KWord (SA (EVar 32) 40) (N.to_nat 8) (EVar 35);
                                     KWord (SA (EVar 32) 32) (N.to_nat 8) (EVar 36); KWord (SA (EVar 32) 24) (N.to_nat 8) (EVar 37); KWord (SA (EVar 32) 16) (N.to_nat 8) (EVar 38)]).
      { assert (G32 : ev E 32 = Z_to_bv 64 (sp - 64)) by (evs; reflexivity).
        repeat apply Forall_cons; [kwv C1 G32 | kwv C2 G32 | kwv C3 G32 | kwv C4 G32 | kwv C5 G32 | kwv C6 G32 | apply Forall_nil]. }
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
    Proof using AC M pspan p l Fp Fl Hpsc Hps47.
      intros k Hk. destruct (Z.lt_ge_cases k 8).
      - exact (fld_hi_mdef (AC:=AC) M pspan 8 p Fp Hpsc ltac:(cbn; lia) k ltac:(cbn; lia)).
      - replace (pspan + k) with (pspan + 8 + (k - 8)) by lia. exact (fld_hi_mdef (AC:=AC) M (pspan + 8) 8 (Zlen l) Fl ltac:(lia) ltac:(cbn; lia) (k - 8) ltac:(cbn; lia)).
    Qed.

    Lemma pspan_cells : forall A1 M1 model1 b1 cap1 ys, PINV A1 M1 model1 b1 cap1 ys ->
      fld SEGS M1 pspan 8 p /\ fld SEGS M1 (pspan + 8) 8 (Zlen l).
    Proof using AC MI ST MSpos A s R M model sp ret pspan pat b cap p xs l CB Fp Fl Hpsc Hps47 Hpsw VEC OBJ DJ NMX RP.
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
      getr R1 10%bv = Z_to_bv 64 j /\ getr R1 19%bv = Z_to_bv 64 (j + 1) /\
      getr R1 8%bv = Z_to_bv 64 pspan /\ getr R1 9%bv = Z_to_bv 64 pat /\ getr R1 18%bv = Z_to_bv 64 (Zlen l) /\ getr R1 20%bv = Z_to_bv 64 (4 * Zlen l) /\
      REGS R1.

    Lemma LOOP2 : forall j R2 M2 model2,
      0 <= j < Zlen l -> mstd model2 ->
      getr R2 19%bv = Z_to_bv 64 (j + 1) ->
      getr R2 8%bv = Z_to_bv 64 pspan -> getr R2 9%bv = Z_to_bv 64 pat -> getr R2 18%bv = Z_to_bv 64 (Zlen l) -> getr R2 20%bv = Z_to_bv 64 (4 * Zlen l) ->
      REGS R2 ->
      forall pc0, (pc0 = PT_LOOP2 \/ pc0 = PT_RET1) ->
      (forall R3, j + 1 < Zlen l -> AT R3 (j + 1) -> srealizes SEGS (mkCfg (@mkst fx R3 (Z_to_bv 64 PT_BODY) M2 (seg_rom SEGS)) model2) K) ->
      (forall R3, j + 1 = Zlen l -> REGS R3 -> srealizes SEGS (mkCfg (@mkst fx R3 (Z_to_bv 64 PT_EXIT) M2 (seg_rom SEGS)) model2) K) ->
      srealizes SEGS (mkCfg (@mkst fx R2 (Z_to_bv 64 pc0) M2 (seg_rom SEGS)) model2) K.
    Proof using AC MI ST MSpos fx A s R M model sp ret pspan pat p l K CB Hll.
      intros j R2 M2 model2 Hj MS G19 G8 G9 G18 G20 (G2 & G3 & G4 & Ghi) pc0 Hpc HKc HKx.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK').
      pose (E := Eseed R2 [Z_to_bv 64 (sp - 64); Z_to_bv 64 (j + 1); Z_to_bv 64 (Zlen l)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (19%bv, EVar 33); (18%bv, EVar 34)]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M2 []) by constructor.
      destruct (Z.eq_dec (j + 1) (Zlen l)) as [Hlast|Hmore].
      - destruct Hpc as [-> | ->];
          (xruns HR HK 20%nat PT_STOPS (SCR [true] [] []) 40%N; [split_scs; cbn [sc_denot]; evs; rewrite zext32_val, br_geu by lia; bool_lia|]);
          (apply HKx; [exact Hlast|]; split; [|split; [|split]];
           [ rreg HR' 2%bv X; exact X | rreg HR' 3%bv X; rewrite X; regeq G3 | rreg HR' 4%bv X; rewrite X; regeq G4
           | intros r Hr; rewrite <- (Ghi r Hr); cbn in Hr;
             repeat (destruct Hr as [<-|Hr]; [lazymatch goal with |- getr _ ?rr = _ => let X := fresh in rreg_ HR' rr X; rewrite X end; f_equal; apply bv_eq; reflexivity|]); destruct Hr ]).
      - destruct Hpc as [-> | ->];
          (xruns HR HK 20%nat PT_STOPS (SCR [false] [] []) 40%N; [split_scs; cbn [sc_denot]; evs; rewrite zext32_val, br_geu by lia; bool_lia|]);
          (apply HKc; [lia|]; unfold AT, REGS;
           repeat match goal with |- _ /\ _ => split end;
           [ rreg HR' 10%bv X; rewrite X; apply zext32_val; lia
           | rreg HR' 19%bv X; rewrite X, zbv_add; f_equal; lia
           | rreg HR' 8%bv X; rewrite X; regeq G8 | rreg HR' 9%bv X; rewrite X; regeq G9 | rreg HR' 18%bv X; exact X
           | rreg HR' 20%bv X; rewrite X; regeq G20
           | rreg HR' 2%bv X; exact X | rreg HR' 3%bv X; rewrite X; regeq G3 | rreg HR' 4%bv X; rewrite X; regeq G4
           | intros r Hr; rewrite <- (Ghi r Hr); cbn in Hr;
             repeat (destruct Hr as [<-|Hr]; [lazymatch goal with |- getr _ ?rr = _ => let X := fresh in rreg_ HR' rr X; rewrite X end; f_equal; apply bv_eq; reflexivity|]); destruct Hr ]).
    Qed.

    Lemma FRAME_store52 : forall M1 (v : word), FRAME M1 -> FRAME (wbytes M1 (Z_to_bv 64 (sp - 52)) (word_to_le_bytes 4 v)).
    Proof using AC MI ST MSpos A s R M model sp ret p CB.
      intros M1 v FR. pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK'). eapply FRAME_agree; [exact FR|].
      eapply agree_on_of_frame_eq; [apply (frame_wbytes4 (zwin (sp - 52) (sp - 48))); [lia | lia | intros x Hx; unfold zwin; lia] |].
      intros a Ha. unfold zwin in *. lia.
    Qed.

    Lemma STEP : forall j R1 M1 A1 model1 b1 cap1,
      0 <= j < Zlen l -> AT R1 j -> FRAME M1 -> PINV A1 M1 model1 b1 cap1 (xs ++ doneL l j) ->
      (forall R3 M3 A3 model3 b3 cap3, j + 1 < Zlen l -> AT R3 (j + 1) -> FRAME M3 -> PINV A3 M3 model3 b3 cap3 (xs ++ doneL l (j + 1)) ->
         srealizes SEGS (mkCfg (@mkst fx R3 (Z_to_bv 64 PT_BODY) M3 (seg_rom SEGS)) model3) K) ->
      (forall R3 M3 A3 model3 b3 cap3, j + 1 = Zlen l -> REGS R3 -> FRAME M3 -> PINV A3 M3 model3 b3 cap3 (xs ++ doneL l (j + 1)) ->
         srealizes SEGS (mkCfg (@mkst fx R3 (Z_to_bv 64 PT_EXIT) M3 (seg_rom SEGS)) model3) K) ->
      srealizes SEGS (mkCfg (@mkst fx R1 (Z_to_bv 64 PT_BODY) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST MSpos PB fx A s R M model sp ret pspan pat b cap p xs l K CB Fp Fl RSP Hll Hl31 Hpsc Hps47 Hpsw VEC OBJ DJ NMX RP.
      intros j R1 M1 A1 model1 b1 cap1 Hj (G10 & G19 & G8 & G9 & G18 & G20 & GRS) FR PI HKc HKx. pose proof GRS as (G2 & G3 & G4 & Ghi).
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK').
      pose proof PI as [AI MS FS SX ROC VEC' PP EF WIN]. pose proof RSP as (Hp0 & Hp1 & RS).
      set (i := Zlen l - 1 - j). set (t := Znth i l).
      assert (Ht : 0 <= t < 2 ^ 31).
      { subst t i. unfold Znth, Zlen in *. apply (proj1 (Forall_nth _ _) Hl31). lia. }
      assert (Ft : fld SEGS M1 (p + 4 * i) 4 t).
      { subst t i. apply (RS M1 (roc_ro M1 ROC)). lia. }
      destruct (pspan_cells A1 M1 model1 b1 cap1 _ PI) as [Fp1 Fl1].
      pose proof (doneL_step l j Hj) as DS. fold i in DS. fold t in DS.
      pose (E := Eseed R1 [Z_to_bv 64 (sp - 64); Z_to_bv 64 pspan; Z_to_bv 64 pat; Z_to_bv 64 (Zlen l); Z_to_bv 64 j; Z_to_bv 64 (j + 1); Z_to_bv 64 (4 * Zlen l); Z_to_bv 64 p; Z_to_bv 64 t]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EVar 34); (18%bv, EVar 35); (10%bv, EVar 36); (19%bv, EVar 37); (20%bv, EVar 38)]) R1).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M1 [KWord (SA (EVar 33) 0) (N.to_nat 8) (EVar 39); KWr (SA (EVar 32) 0) (ELit 64)]).
      { assert (G33 : ev E 33 = Z_to_bv 64 pspan) by (evs; reflexivity).
        repeat apply Forall_cons; [kwv Fp1 G33 | | apply Forall_nil].
        eapply (kwr_of_mdef SEGS E M1 32 (sp - 64) 0 64); [evs; reflexivity | lia | lia | lia | lia |].
        rewrite Z.add_0_r. intros k Hk. replace (sp - 64 + k) with (sp - STK + (STK - 64 + k)) by lia. apply WIN. lia. }
      assert (CELL : cellw SEGS M1 (p + 4 * i) 4 t) by (split; [cbn; lia | exact Ft]).
      assert (ADDR : alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-4)) (Z_to_bv 64 j)) (alu64 ALU_ADD (Z_to_bv 64 (4 * Zlen l)) (Z_to_bv 64 p)) = Z_to_bv 64 (p + 4 * i + 4)).
      { rewrite zbv_mul, !zbv_add. f_equal. subst i. lia. }
      assert (RD : sc_denot SEGS M1 E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit (-4)) (EVar 36)) (EAlu ALU_ADD (EVar 38) (EVar 39))) (-4)) 4 true (EVar 40))).
      { eapply (sc_read_cell4_sx _ _ _ _ _ _ _ CELL); [unfold adenot; cbn [a_base a_off]; evs; rewrite ADDR, v_addi_Z by lia; f_equal; lia | evs; rewrite sxw_small by lia; reflexivity]. }
      assert (FL : sc_denot SEGS M1 E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit (-4)) (EVar 36)) (EAlu ALU_ADD (EVar 38) (EVar 39))) (-4)) (ELit 4))).
      { eapply (sc_flat _ _ _ _ (p + 4 * i + 4)); [cbn [a_base]; evs; exact ADDR | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]. }
      assert (STI : stores_in (zwin (sp - 64) sp) M1 (wbytes M1 (Z_to_bv 64 (sp - 52)) (word_to_le_bytes 4 (Z_to_bv 64 t)))).
      { apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; [lia | cbn; lia |]. intros a Ha. cbn in Ha. unfold zwin. lia. }
      pose proof (PCargs pinv_stores A1 M1 model1 b1 cap1 (xs ++ doneL l j) PI _ STI) as PI2.
      pose proof (FRAME_store52 M1 (Z_to_bv 64 t) FR) as FR2.
      destruct (Z.eq_dec t 0) as [Tz|Tnz].
      -
        xruns HR HK 40%nat (PT_LOOP2 :: PT_STOPS) (SCR [true] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | sc_fl | sc_br]. }
        match goal with |- srealizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
          replace Mx with (wbytes M1 (Z_to_bv 64 (sp - 52)) (word_to_le_bytes 4 (Z_to_bv 64 t)))
            by (unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; f_equal; f_equal; lia) end.
        rewrite Tz in DS. cbn in DS. rewrite app_nil_r in DS.
        eapply (LOOP2 j R' _ model1 Hj MS); [ | | | | | | left; reflexivity | |].
        + rreg HR' 19%bv X; exact X. + rreg HR' 8%bv X; exact X. + rreg HR' 9%bv X; exact X. + rreg HR' 18%bv X; exact X. + rreg HR' 20%bv X; exact X.
        + split; [|split; [|split]]; [rreg HR' 2%bv X; exact X | rreg HR' 3%bv X; rewrite X; regeq G3 | rreg HR' 4%bv X; rewrite X; regeq G4 |].
          intros r Hr; rewrite <- (Ghi r Hr); cbn in Hr.
          repeat (destruct Hr as [<-|Hr]; [lazymatch goal with |- getr _ ?rr = _ => let X := fresh in rreg_ HR' rr X; rewrite X end; f_equal; apply bv_eq; reflexivity|]); destruct Hr.
        + intros R3 Hlt AT3. eapply (HKc R3 _ A1 model1 b1 cap1 Hlt AT3 FR2). rewrite DS. exact PI2.
        + intros R3 Heq RG3. eapply (HKx R3 _ A1 model1 b1 cap1 Heq RG3 FR2). rewrite DS. exact PI2.
      -
        xruns HR HK 40%nat PT_STOPS (SCR [false] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | sc_fl | sc_br]. }
        match goal with |- srealizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
          replace Mx with (wbytes M1 (Z_to_bv 64 (sp - 52)) (word_to_le_bytes 4 (Z_to_bv 64 t)))
            by (unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; f_equal; f_equal; lia) end.
        assert (DS' : doneL l (j + 1) = doneL l j ++ [t]) by (rewrite DS; destruct (Z.eqb_spec t OT_NONE); [exfalso; unfold OT_NONE in *; lia | reflexivity]).
        rreg HR' 10%bv A10. rreg HR' 11%bv A11. rreg HR' 2%bv A2. rreg HR' 1%bv A1'. rreg HR' 3%bv A3. rreg HR' 4%bv A4.
        pose proof (doneL_len l j ltac:(lia)) as DL.
        eapply ((PCargs pinv_push) cpbP1 A1 _ model1 b1 cap1 (xs ++ doneL l j) R' PT_RET1 (sp - 52) t K PB).
        + cbn. lia. + unfold STK. cbn [vc_stack cpbP1]. lia.
        + exact PI2.
        + rewrite Zlen_app. lia. + rewrite Zlen_app. change (Z.of_nat (length l)) with (Zlen l). lia.
        + exact A10. + rewrite A11, zbv_add. f_equal. lia. + exact A2. + exact A1'.
        + apply bv_eq. vm_compute. reflexivity. + unfold PT_RET1. lia.
        + rewrite A3. regeq G3. + rewrite A4. regeq G4.
        + lia. + lia.
        + apply fld_wbytes4; lia. + lia.
        +
          intros A' R'' M' model' b' cap' PI' KEPT AG.
          pose proof PI' as [AI' MS' _ _ _ _ _ _ _].
          assert (FR' : FRAME M') by (eapply FRAME_agree; [exact FR2 | eapply agree_on_weaken; [exact AG|]; intros a Ha; unfold zwin in *; lia]).
          rewrite <- app_assoc, <- DS' in PI'.
          assert (KR : forall r, In r callee_saved -> getr R'' r = getr R' r) by (intros r Hr; exact (KEPT r Hr)).
          eapply (LOOP2 j R'' M' model' Hj MS'); [ | | | | | | right; reflexivity | |].
          * rewrite (KR 19%bv) by inl. rreg HR' 19%bv X. exact X.
          * rewrite (KR 8%bv) by inl. rreg HR' 8%bv X. exact X.
          * rewrite (KR 9%bv) by inl. rreg HR' 9%bv X. exact X.
          * rewrite (KR 18%bv) by inl. rreg HR' 18%bv X. exact X.
          * rewrite (KR 20%bv) by inl. rreg HR' 20%bv X. exact X.
          * split; [|split; [|split]]; [rewrite (KR 2%bv) by inl; exact A2 | rewrite (KR 3%bv) by inl; rewrite A3; regeq G3 | rewrite (KR 4%bv) by inl; rewrite A4; regeq G4 |].
            intros r Hr; rewrite <- (Ghi r Hr). rewrite (KR r) by (cbn in Hr |- *; clear -Hr; intuition). cbn in Hr.
            repeat (destruct Hr as [<-|Hr]; [lazymatch goal with |- getr _ ?rr = _ => let X := fresh in rreg_ HR' rr X; rewrite X end; f_equal; apply bv_eq; reflexivity|]); destruct Hr.
          * intros R3 Hlt AT3. exact (HKc R3 M' A' model' b' cap' Hlt AT3 FR' PI').
          * intros R3 Heq RG3. exact (HKx R3 M' A' model' b' cap' Heq RG3 FR' PI').
    Qed.

    Lemma LOOP : forall (n : nat) j R1 M1 A1 model1 b1 cap1,
      Zlen l - j <= Z.of_nat n -> 0 <= j < Zlen l -> AT R1 j -> FRAME M1 -> PINV A1 M1 model1 b1 cap1 (xs ++ doneL l j) ->
      srealizes SEGS (mkCfg (@mkst fx R1 (Z_to_bv 64 PT_BODY) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST MSpos PB fx A s R M model sp ret pspan pat b cap p xs l K CB Fp Fl RSP Hll Hl31 Hpsc Hps47 Hpsw VEC OBJ DJ NMX RP CONT.
      induction n as [|n IH]; intros j R1 M1 A1 model1 b1 cap1 Hn Hj AT1 FR PI; [lia|].
      eapply STEP; [exact Hj | exact AT1 | exact FR | exact PI | |].
      - intros R3 M3 A3 model3 b3 cap3 Hlt AT3 FR3 PI3. eapply (IH (j + 1)); [lia | lia | exact AT3 | exact FR3 | exact PI3].
      - intros R3 M3 A3 model3 b3 cap3 Heq RG3 FR3 PI3. rewrite Heq, doneL_all in PI3. exact (EXIT R3 M3 A3 model3 b3 cap3 PI3 RG3 FR3).
    Qed.

    Lemma ENTRY : srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 PT_ENTRY) M (seg_rom SEGS)) model) K.
    Proof using AC MI ST MSpos PB fx A s R M model sp ret pspan pat b cap p xs l K CB Ha0 Ha1 Fp Fl RSP Hll Hl31 Hpsc Hps47 Hpsw VEC OBJ DJ NMX RP CONT.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & Hret & HSTK & HSTK').
      pose proof (PCargs pinv_init) as PI0. pose proof PI0 as [AI MS FS SX ROC VEC' PP EF WIN]. pose proof CB as CB'.
      destruct CB' as [_ _ _ _ _ [_ _ _ _ _ _ Hgp Htp] _ _ _ _ _].
      pose proof RSP as (Hp0 & Hp1 & RS).
      assert (HL0 : 0 <= Zlen l) by (unfold Zlen; lia).
      pose (E := Eseed R [Z_to_bv 64 sp; Z_to_bv 64 pspan; Z_to_bv 64 pat; Z_to_bv 64 (Zlen l)]).
      assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 34)]) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (PSD : pspan + 16 <= sp - 64 \/ sp <= pspan).
      { destruct (Z.lt_ge_cases pspan sp); [left|right; lia].
        destruct (Z.lt_ge_cases pspan (sp - STK)); [lia|]. exfalso. apply (Hpsw pspan); unfold zwin; lia. }
      assert (HK : know_ok SEGS E M [KWord (SA (EVar 33) 8) (N.to_nat 8) (EVar 35); KWr (SA (EVar 32) (-64)) (ELit 64);
                                    KDisj (SA (EVar 33) 0) (ELit 16) (SA (EVar 32) (-64)) (ELit 64)]).
      { assert (G33 : ev E 33 = Z_to_bv 64 pspan) by (evs; reflexivity). assert (G32 : ev E 32 = Z_to_bv 64 sp) by (evs; reflexivity).
        repeat apply Forall_cons; [kwv Fl G33 | | | apply Forall_nil].
        - eapply (kwr_of_mdef SEGS E M 32 sp (-64) 64); [exact G32 | lia | lia | lia | lia |].
          intros k Hk. replace (sp + -64 + k) with (sp - STK + (STK - 64 + k)) by lia. apply WIN. lia.
        - eapply (kdisj_vars SEGS E M 33 32 pspan sp); [exact G33 | exact G32 | lia | lia | lia | lia | lia]. }

      set (M1 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
                   (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (getr R 1%bv)))
                   (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 (getr R 8%bv)))
                   (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 (getr R 9%bv)))
                   (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 (getr R 18%bv)))
                   (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 (getr R 19%bv)))
                   (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 (getr R 20%bv))).
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
                   sr_get sr 2%bv = EAlu ALU_ADD (EVar 32) (ELit (-64)) -> syms_id sr [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv = true -> REGS Rx).
      { intros Rx sr HRx Hsp Hs. pose proof (syms_id_sound _ _ _ _ _ HRx Hs) as SY.
        split; [|split; [|split]].
        - rewrite (HRx 2%bv), Hsp. cbn [edenot]. evs. rewrite zbv_add. f_equal; lia.
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
        + rreg HR' 10%bv X; exact X. + rreg HR' 19%bv X; exact X. + rreg HR' 8%bv X; exact X. + rreg HR' 9%bv X; exact X.
        + rreg HR' 18%bv X; exact X. + rreg HR' 20%bv X; rewrite X, zbv_mul; f_equal; lia.
    Qed.
  End Body.

  Theorem push_types_spec : push_types_stmt SEGS L MI ST TG tc cpbP1.
  Proof using AC MI ST MSpos PB.
    intros fx A s R M model sp ret pspan pat b cap p xs l K.
    cbn [tc_pattern_stack tc_push_types Img.tc vc_stack cpbP1 g_maxlen TG TablData.MAXLEN].
    intros CB _ Ha0 Ha1 Fp Fl RSP Hp4 Hll Hl31 Hpsc Hps47 Hpsw VEC OBJ PAT8 DJ NMX RP CONT.
    eapply (ENTRY fx A s R M model sp ret pspan pat b cap p xs l K); eassumption.
  Qed.
End PT.
