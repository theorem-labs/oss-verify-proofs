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
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablPush OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_PushP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_6bb2c_6bca4.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
End S1_code_6bb2c_6bca4.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeelFast.

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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablStmts TablLib TablPush Tabl_PushP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_TakeP1.S1_code_6bb2c_6bca4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgP1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require PeelFast.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgP1.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation tc := Img.tc.

Definition TF_ENTRY : Z := 0x6bc98.
Definition TF_BACK  : Z := 0x6bcc8.
Definition PB2_ENTRY : Z := 0x69844.
Definition TF_STOPS : list Z := [PB_ENTRY; PB2_ENTRY].
Definition cpb2P1 : vec_consts := {| vc_entry := 0x69844; vc_stack := 64 |}.

Lemma last_app1 : forall (ys : list Z) y d, last (ys ++ [y]) d = y.
Proof. intros. rewrite last_last. reflexivity. Qed.
Lemma removelast_app1 : forall (ys : list Z) y, removelast (ys ++ [y]) = ys.
Proof. intros. rewrite removelast_app by discriminate. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma Zlen_app1 : forall (ys : list Z) y, Zlen (ys ++ [y]) = Zlen ys + 1.
Proof. intros. rewrite Zlen_app. reflexivity. Qed.

Lemma Znth_last : forall xs, xs <> [] -> Znth (Zlen xs - 1) xs = last xs 0.
Proof.
  intros xs Hne. destruct (exists_last Hne) as (ys & y & ->).
  rewrite last_app1. unfold Znth, Zlen. rewrite length_app. cbn [length].
  replace (Z.to_nat (Z.of_nat (length ys + 1) - 1)) with (length ys) by lia.
  rewrite nth_middle. reflexivity.
Qed.

Section PT.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Hypothesis MSpos : 0 <= MALLOC_STACK MI.
  Hypothesis PB : vec32_push_back_stmt SEGS L MI ST cpbP1.
  Hypothesis PB2 : vec32_push_back_stmt SEGS L MI ST cpb2P1.

  Section Body.
    Variables (fx : FPState) (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret pat b cap : Z) (xs : list Z) (K : TSet).
    Definition STK : Z := 96 + (64 + NEW_STACK SEGS L MI).
    Hypothesis CB : callB MI ST A s R M model sp ret STK.
    Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 pat.
    Hypothesis VEC : vec32 MI A M pat b xs cap.
    Hypothesis Hne : xs <> [].
    Hypothesis OBJ : obj_ok MI A sp STK pat 24.
    Hypothesis Hx31 : Forall (fun t => 0 <= t < 2 ^ 31) xs.
    Hypothesis NMX : caps_bound (Zlen xs - 1) cap 3 <= NMAX MI.
    Hypothesis RP : room_pushes SEGS L MI A (live MI A) (Zlen xs - 1) cap 3.
    Hypothesis CONT : forall A' R' M' model' (b' cap' : Z),
        retB MI ST A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (fst (take_first xs)) ->
        vec32 MI A' M' pat b' (snd (take_first xs)) cap' ->
        pushes_post SEGS L MI A A' (Zlen xs - 1) 3 b cap b' cap' ->
        eff MI A A' M M' (sp - STK, sp) (pushes_fp SEGS L MI A pat b cap b' cap') ->
        srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) model') K.

    Lemma HL1 : 1 <= Zlen xs.
    Proof using AC MI ST fx A s R M model sp ret pat b cap xs K VEC Hne Hx31 NMX RP CONT. destruct xs; [congruence|]. unfold Zlen. cbn [length]. lia. Qed.

    Lemma PC : pctx SEGS L MI ST A s R M model sp ret STK 64 pat b cap xs (Zlen xs - 1) 3%nat.
    Proof using AC MI ST MSpos fx A s R M model sp ret pat b cap xs K CB VEC Hne OBJ Hx31 NMX RP CONT.
      pose proof HL1. constructor.
      - exact LYP1. - exact MSpos. - exact CB. - exact VEC. - exact OBJ.
      - unfold STK, NEW_STACK. split; [lia | reflexivity].
      - exact RP. - exact NMX. - lia.
    Qed.

    #[local] Notation PINV := (TablPush.PINV SEGS L MI ST A s M model sp STK pat b cap (Zlen xs - 1) 3%nat).
    #[local] Notation PCargs X := (X SEGS L MI ST A s R M model sp ret STK 64 pat b cap xs (Zlen xs - 1) 3%nat PC).
    #[local] Ltac dCB := destruct CB as [AI0 MS0 ROC0 SX0 SXH0 CR0 Hceil0 HROOM0 Hwin0 Hown_sx0 Herr_sx0].

    Lemma spf : alloc_ceiling + STK <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\ 2 ^ 24 <= sp - STK /\
                getr R 2%bv = Z_to_bv 64 sp /\ getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\ STK = 96 + (64 + (16 + MALLOC_STACK MI)) /\ 176 <= STK.
    Proof using AC MI ST MSpos A s R M model sp ret CB. dCB. destruct CR0. pose proof ac_bounds_lit. pose proof MSpos. unfold STK, NEW_STACK in *. repeat split; try assumption; lia. Qed.

    Definition TFR (M1 : mem) : Prop :=
      cellw SEGS M1 (sp - 8) 8 (bv_unsigned (getr R 1%bv)) /\ cellw SEGS M1 (sp - 16) 8 (bv_unsigned (getr R 8%bv)) /\
      cellw SEGS M1 (sp - 24) 8 (bv_unsigned (getr R 9%bv)) /\ cellw SEGS M1 (sp - 40) 8 TF_BACK /\ cellw SEGS M1 (sp - 48) 8 pat.

    Definition HI : list reg := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
    Definition SAME (R1 : bvmap 5 word) : Prop := forall r, In r HI -> getr R1 r = getr R r.

    Lemma TFR_agree : forall M1 M2, TFR M1 -> agree_on (fun a => zwin (sp - 48) (sp - 32) a \/ zwin (sp - 24) sp a) M1 M2 -> TFR M2.
    Proof using AC MI ST MSpos A s R M model sp ret pat CB.
      intros M1 M2 (C1 & C2 & C3 & C4 & C5) AG. pose proof spf as (Hc & Hs47 & _ & Hcv & _ & _ & _ & _ & _ & HSTK).
      assert (G : forall a v, cellw SEGS M1 a 8 v -> (sp - 48 <= a /\ a + 8 <= sp - 32) \/ (sp - 24 <= a /\ a + 8 <= sp) -> cellw SEGS M2 a 8 v).
      { intros a v [Hv Hr] Ha. split; [exact Hv|]. eapply (fld_agree SEGS M1 M2 a 8 v); [lia | cbn; lia | exact Hr |].
        eapply agree_on_weaken; [exact AG|]. intros x Hx. unfold zwin in *. cbn in Hx. lia. }
      repeat split; (eapply G; [eassumption | lia]).
    Qed.

    Lemma SAME_via : forall R1 R2, SAME R1 -> (forall r, In r HI -> getr R2 r = getr R1 r) -> SAME R2.
    Proof using R. intros R1 R2 S1 S2 r Hr. rewrite (S2 r Hr). apply S1, Hr. Qed.

    Lemma SAME_kept : forall R1 R2, SAME R1 -> kept R1 R2 -> SAME R2.
    Proof using R. intros R1 R2 S1 KE. eapply SAME_via; [exact S1|]. intros r Hr. apply KE. cbn in Hr |- *. clear -Hr. intuition. Qed.

    #[local] Ltac regeq G := etransitivity; [|exact G]; f_equal; apply bv_eq; reflexivity.

    Ltac same_of HR' S1 :=
      eapply (SAME_via _ _ S1); intros r Hr; cbn in Hr;
      repeat (destruct Hr as [<-|Hr]; [lazymatch goal with |- getr _ ?rr = _ => let X := fresh in rreg_ HR' rr X; rewrite X end; f_equal; apply bv_eq; reflexivity|]);
      destruct Hr.

    Lemma rdn_wbytes_out_Zc : forall segs bs m (zb za : Z) n,
      (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
       zb + Z.of_nat (length bs) <= 2^64 /\
       (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
      rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
    Proof using.
      intros segs bs m zb za n (Ha & Han & Hb & Hbn & Hd).
      apply CatExec.rdn_wbytes_out; rewrite ?u64_of_Z by lia; lia.
    Qed.
    Ltac peel_side_t := rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    Ltac peel := repeat first [ PeelFast.peel_fast_by peel_side_t
      | rewrite rdn_wbytes_out_Zc by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
      | rewrite CatExec.rdn_wbytes_out;
      [| rewrite ?length_N_to_le_bytes, !u64_of_Z by lia; cbn; lia | rewrite !u64_of_Z by lia; cbn; lia
       | rewrite ?length_N_to_le_bytes, !u64_of_Z by lia; cbn; lia] ].
    Ltac cell_hit := rewrite ?Z_to_bv_bv_unsigned; first [apply rdn_wbytes_hit8 | apply rdn_wbytes_hit4]; rewrite u64_of_Z by lia; lia.

    Ltac tfr_tower C1 C2 C3 C4 C5 :=
      unfold TFR, cellw; repeat match goal with |- _ /\ _ => split end;
      first [ apply u64_range | unfold TF_BACK; lia | lia
            | peel;
              first [ cell_hit | exact (proj2 C1) | exact (proj2 C2) | exact (proj2 C3) | exact (proj2 C4) | exact (proj2 C5) ] ].

    Ltac store1 := apply stores_in_wbytes_more;
      [ | lia | rewrite ?length_N_to_le_bytes; cbn; lia | rewrite ?length_N_to_le_bytes; intros x Hx; cbn in Hx; unfold zwin; lia ].
    Ltac frame_stores := repeat store1; apply stores_in_refl.

    Ltac norm_mem := unfold adenot; cbn [a_base a_off]; evs; rewrite ?v_addi_Z by lia; rewrite ?zbv_add.

    Lemma CALL : forall (first : bool) A1 M1 model1 b1 cap1 ys R1 (ra src x t0 : Z),
      PINV A1 M1 model1 b1 cap1 ys -> TFR M1 -> SAME R1 ->
      Zlen xs - 1 <= Zlen ys -> Zlen ys < Zlen xs - 1 + 3 ->
      getr R1 10%bv = Z_to_bv 64 pat -> getr R1 11%bv = Z_to_bv 64 src -> getr R1 2%bv = Z_to_bv 64 (sp - 64) ->
      getr R1 1%bv = Z_to_bv 64 ra -> ret_ok (Z_to_bv 64 ra) -> 0 <= ra < 2 ^ 64 ->
      getr R1 8%bv = Z_to_bv 64 pat -> getr R1 9%bv = Z_to_bv 64 t0 ->
      (src = sp - 52 \/ src = sp - 56) -> fld SEGS M1 src 4 x -> 0 <= x < 2 ^ 32 ->
      (forall A' R' M' model' (b' cap' : Z),
         PINV A' M' model' b' cap' (ys ++ [x]) -> TFR M' -> SAME R' ->
         getr R' 2%bv = Z_to_bv 64 (sp - 64) -> getr R' 8%bv = Z_to_bv 64 pat -> getr R' 9%bv = Z_to_bv 64 t0 ->
         srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ra) M' (seg_rom SEGS)) model') K) ->
      srealizes SEGS (mkCfg (@mkst fx R1 (Z_to_bv 64 (if first then PB_ENTRY else PB2_ENTRY)) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST MSpos PB PB2 fx A s R M model sp ret pat b cap xs K CB VEC Hne OBJ Hx31 NMX RP CONT.
      intros first A1 M1 model1 b1 cap1 ys R1 ra src x t0 PI TF SM HL1' HL2 G10 G11 G2 G1 Hret Hra G8 G9 Hsrc Fx Hx CONTc.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & HretR & HSTK & HSTK').
      assert (G3 : getr R1 3%bv = getr R 3%bv) by (apply SM; inl). assert (G4 : getr R1 4%bv = getr R 4%bv) by (apply SM; inl).
      assert (CONT2 : forall A' R' M' model' (b' cap' : Z),
         PINV A' M' model' b' cap' (ys ++ [x]) -> kept R1 R' -> agree_on (zwin (sp - 64) sp) M1 M' ->
         srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ra) M' (seg_rom SEGS)) model') K).
      { intros A' R' M' model' b' cap' PI' KE AG. apply (CONTc A' R' M' model' b' cap' PI').
        - eapply TFR_agree; [exact TF|]. eapply agree_on_weaken; [exact AG|]. intros a Ha. unfold zwin in *. lia.
        - exact (SAME_kept _ _ SM KE).
        - rewrite (KE 2%bv) by inl. exact G2. - rewrite (KE 8%bv) by inl. exact G8. - rewrite (KE 9%bv) by inl. exact G9. }
      destruct first.
      - eapply ((PCargs pinv_push) cpbP1 A1 M1 model1 b1 cap1 ys R1 ra src x K PB); try eassumption; cbn [vc_stack cpbP1]; unfold STK; try lia.
      - eapply ((PCargs pinv_push) cpb2P1 A1 M1 model1 b1 cap1 ys R1 ra src x K PB2); try eassumption; cbn [vc_stack cpb2P1]; unfold STK; try lia.
    Qed.

    Lemma seg_know : forall A1 M1 model1 b1 cap1 ys Rk (spv t0 : Z),
      PINV A1 M1 model1 b1 cap1 ys -> TFR M1 -> getr Rk 2%bv = Z_to_bv 64 spv ->
      let E := Eseed Rk [Z_to_bv 64 sp; Z_to_bv 64 pat; getr R 1%bv; getr R 8%bv; getr R 9%bv; Z_to_bv 64 t0] in
      know_ok SEGS E M1 [KWr (SA (EVar 32) (-64)) (ELit 64);
                         KWord (SA (EVar 32) (-8)) (N.to_nat 8) (EVar 34); KWord (SA (EVar 32) (-16)) (N.to_nat 8) (EVar 35);
                         KWord (SA (EVar 32) (-24)) (N.to_nat 8) (EVar 36);
                         KWord (SA (EVar 32) (-40)) (N.to_nat 8) (ELit TF_BACK); KWord (SA (EVar 32) (-48)) (N.to_nat 8) (EVar 33)].
    Proof using AC MI ST MSpos A s R M model sp ret pat b cap xs CB VEC.
      intros A1 M1 model1 b1 cap1 ys Rk spv t0 PI (C1 & C2 & C3 & C4 & C5) G2 E.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & HretR & HSTK & HSTK').
      pose proof PI as [AI MS FS SX ROC VEC' PP EF WIN]. pose proof VEC as (Hv0 & Hv1 & _).
      assert (G32 : ev E 32 = Z_to_bv 64 sp) by (evs; reflexivity).
      repeat apply Forall_cons; [ | kwv C1 G32 | kwv C2 G32 | kwv C3 G32 | kwv C4 G32 | kwv C5 G32 | apply Forall_nil].
      eapply (kwr_of_mdef SEGS E M1 32 sp (-64) 64); [exact G32 | lia | lia | lia | lia |].
      intros k Hk. replace (sp + -64 + k) with (sp - STK + (STK - 64 + k)) by lia. apply WIN. lia.
    Qed.

    Lemma seg_regs : forall Rk (spv t0 off : Z),
      getr Rk 2%bv = Z_to_bv 64 spv -> getr Rk 8%bv = Z_to_bv 64 pat -> getr Rk 9%bv = Z_to_bv 64 t0 -> spv = sp + off ->
      regs_ok (Eseed Rk [Z_to_bv 64 sp; Z_to_bv 64 pat; getr R 1%bv; getr R 8%bv; getr R 9%bv; Z_to_bv 64 t0])
              (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 32) (ELit off)); (8%bv, EVar 33); (9%bv, EVar 37)]) Rk.
    Proof using R sp pat.
      intros Rk spv t0 off G2 G8 G9 ->.
      apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs.
      - rewrite G2, zbv_add. reflexivity. - exact G8. - exact G9.
    Qed.

    Lemma pinv_mstd : forall A1 M1 model1 b1 cap1 ys, PINV A1 M1 model1 b1 cap1 ys -> mstd model1.
    Proof using AC MI ST A s M model sp pat b cap xs. intros A1 M1 model1 b1 cap1 ys [_ MS _ _ _ _ _ _ _]. exact MS. Qed.

    Ltac seg PI TF G2 G8 G9 ds :=
      lazymatch goal with |- srealizes _ (mkCfg (@mkst _ ?Rk _ ?Mk _) _) _ =>
      lazymatch type of G2 with getr _ _ = Z_to_bv 64 ?spv =>
      lazymatch type of G9 with getr _ _ = Z_to_bv 64 ?t0 =>
        let off := lazymatch spv with sp - ?k => constr:(Z.opp k) | sp + ?k => constr:(k) end in
        let off := eval vm_compute in off in
        let HR := fresh "HR" in let HK := fresh "HK" in
        pose proof (seg_know _ _ _ _ _ _ Rk spv t0 PI TF G2) as HK; cbv zeta in HK;
        pose proof (seg_regs Rk spv t0 off G2 G8 G9 ltac:(lia)) as HR;
        let MSx := fresh "MS" in pose proof (pinv_mstd _ _ _ _ _ _ PI) as MSx;
        xruns HR HK 60%nat TF_STOPS (SCR ds [] []) 40%N; [split_scs; first [sc_fl | sc_br] |]
      end end end.

    Lemma pop_know : forall A1 M1 model1 b1 cap1 ys t2 Rk (spv t0 : Z),
      PINV A1 M1 model1 b1 cap1 (ys ++ [t2]) -> TFR M1 -> getr Rk 2%bv = Z_to_bv 64 spv -> 0 <= t2 < 2 ^ 32 ->
      let E := Eseed Rk [Z_to_bv 64 sp; Z_to_bv 64 pat; getr R 1%bv; getr R 8%bv; getr R 9%bv; Z_to_bv 64 t0; Z_to_bv 64 (b1 + 4 * (Zlen ys + 1))] in
      know_ok SEGS E M1 [KWr (SA (EVar 32) (-64)) (ELit 64);
                         KWord (SA (EVar 32) (-8)) (N.to_nat 8) (EVar 34); KWord (SA (EVar 32) (-16)) (N.to_nat 8) (EVar 35);
                         KWord (SA (EVar 32) (-24)) (N.to_nat 8) (EVar 36);
                         KWord (SA (EVar 32) (-40)) (N.to_nat 8) (ELit TF_BACK); KWord (SA (EVar 32) (-48)) (N.to_nat 8) (EVar 33);
                         KWord (SA (EVar 33) 8) (N.to_nat 8) (EVar 38); KWord (SA (EVar 38) (-4)) (N.to_nat 4) (ELit t2);
                         KWr (SA (EVar 33) 0) (ELit 24);
                         KDisj (SA (EVar 33) 0) (ELit 24) (SA (EVar 32) (-64)) (ELit 64);
                         KDisj (SA (EVar 38) (-4)) (ELit 4) (SA (EVar 32) (-64)) (ELit 64);
                         KDisj (SA (EVar 38) (-4)) (ELit 4) (SA (EVar 33) 0) (ELit 24)].
    Proof using AC MI ST MSpos fx A s R M model sp ret pat b cap xs K CB VEC Hne OBJ Hx31 NMX RP CONT.
      intros A1 M1 model1 b1 cap1 ys t2 Rk spv t0 PI TF G2 Ht2 E. pose proof TF as (C1 & C2 & C3 & C4 & C5).
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & HretR & HSTK & HSTK').
      pose proof PI as [AI MS FS SX ROC VEC' PP EF WIN]. pose proof (PCargs pat_win) as PW.
      pose proof VEC' as (Hv0 & Hv1 & HD & Hlen & Hbb & F0 & F1 & F2 & FEL). rewrite Zlen_app in Hlen, F1. change (Zlen [t2]) with 1 in Hlen, F1.
      assert (Hys : 0 <= Zlen ys) by (unfold Zlen; lia).
      destruct Hbb as [[-> Hc0]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [lia|].
      destruct (ai_live_block MI A1 M1 model1 b1 (4 * cap1) AI HIn) as (_ & _ & _ & Hce & _).
      assert (Hiy : 0 <= Zlen ys < Zlen (ys ++ [t2])) by (rewrite Zlen_app; change (Zlen [t2]) with 1; lia).
      destruct (FEL (Zlen ys) Hiy) as [_ FT].
      replace (Znth (Zlen ys) (ys ++ [t2])) with t2 in FT by (unfold Znth, Zlen; rewrite Nat2Z.id, nth_middle; reflexivity).
      assert (G32 : ev E 32 = Z_to_bv 64 sp) by (evs; reflexivity). assert (G33 : ev E 33 = Z_to_bv 64 pat) by (evs; reflexivity).
      assert (G38 : ev E 38 = Z_to_bv 64 (b1 + 4 * (Zlen ys + 1))) by (evs; reflexivity).
      repeat apply Forall_cons; [ | kwv C1 G32 | kwv C2 G32 | kwv C3 G32 | kwv C4 G32 | kwv C5 G32 | kwv F1 G33 | kwv FT G38 | | | | | apply Forall_nil].
      - eapply (kwr_of_mdef SEGS E M1 32 sp (-64) 64); [exact G32 | lia | lia | lia | lia |].
        intros k Hk. replace (sp + -64 + k) with (sp - STK + (STK - 64 + k)) by lia. apply WIN. lia.
      - eapply (kwr_of_mdef SEGS E M1 33 pat 0 24); [exact G33 | lia | lia | lia | lia |]. rewrite Z.add_0_r. exact HD.
      - eapply (kdisj_vars SEGS E M1 33 32 pat sp); [exact G33 | exact G32 | lia | lia | lia | lia | lia].
      - eapply (kdisj_vars SEGS E M1 38 32 (b1 + 4 * (Zlen ys + 1)) sp); [exact G38 | exact G32 | lia | lia | lia | lia | lia].
      - eapply (kdisj_vars SEGS E M1 38 33 (b1 + 4 * (Zlen ys + 1)) pat); [exact G38 | exact G33 | lia | lia | lia | lia | lia].
    Qed.

    Lemma RETK : forall A1 M1 model1 b1 cap1 R2,
      PINV A1 M1 model1 b1 cap1 (snd (take_first xs)) ->
      getr R2 1%bv = getr R 1%bv -> getr R2 2%bv = Z_to_bv 64 sp -> getr R2 8%bv = getr R 8%bv -> getr R2 9%bv = getr R 9%bv -> SAME R2 ->
      getr R2 10%bv = Z_to_bv 64 (fst (take_first xs)) ->
      srealizes SEGS (mkCfg (@mkst fx R2 (Z_to_bv 64 0x6bce0) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST MSpos fx A s R M model sp ret pat b cap xs K CB CONT.
      intros A1 M1 model1 b1 cap1 R2 PI G1 G2 G8 G9 SM G10.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & HretR & HSTK & HSTK').
      pose proof PI as [AI MS FS SX ROC VEC' PP EF WIN].
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | eapply ret_run; [vm_compute; reflexivity | rewrite G1; exact GR1 | exact HretR] |].
      apply (CONT A1 R2 M1 model1 b1 cap1).
      - constructor; [exact AI | exact MS | exact (proj1 FS) | exact (proj2 FS) | exact SX |].
        intros r Hr. cbn in Hr.
        repeat (destruct Hr as [<-|Hr]; [ first [ exact G1 | rewrite G2, GR2; reflexivity | exact G8 | exact G9 | apply SM; inl ] |]).
        destruct Hr.
      - exact G10. - exact VEC'. - exact PP. - exact EF.
    Qed.

    Lemma pop_pinv : forall A1 M1 model1 b1 cap1 ys t2 M2 (v1 : word) (v2 v3 : word),
      PINV A1 M1 model1 b1 cap1 (ys ++ [t2]) ->
      M2 = wbytes (wbytes (wbytes (wbytes M1 (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b1 + 4 * (Zlen ys + 1) + -4))))
             (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 v1)) (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 v2)) (Z_to_bv 64 (sp - 52)) (word_to_le_bytes 4 v3) ->
      PINV A1 M2 model1 b1 cap1 ys.
    Proof using AC MI ST MSpos fx A s R M model sp ret pat b cap xs K CB VEC Hne OBJ Hx31 NMX RP CONT.
      intros A1 M1 model1 b1 cap1 ys t2 M2 v1 v2 v3 PI ->.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & HretR & HSTK & HSTK').
      pose proof (PCargs pinv_pop A1 M1 model1 b1 cap1 (ys ++ [t2]) (wbytes M1 (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b1 + 4 * (Zlen ys + 1) + -4)))) PI
                    ltac:(intros E0; destruct (app_eq_nil _ _ E0); discriminate)
                    ltac:(rewrite Zlen_app; change (Zlen [t2]) with 1; do 3 f_equal; lia)) as PI1.
      rewrite removelast_app1 in PI1.
      eapply (PCargs pinv_stores); [exact PI1 | frame_stores].
    Qed.

    Lemma LASTSEG : forall A1 M1 model1 b1 cap1 R1 ys (t2 t0 : Z),
      PINV A1 M1 model1 b1 cap1 (ys ++ [t2]) -> TFR M1 -> SAME R1 ->
      getr R1 2%bv = Z_to_bv 64 (sp - 64) -> getr R1 8%bv = Z_to_bv 64 pat -> getr R1 9%bv = Z_to_bv 64 t0 ->
      In t2 [42; 45; 47; 105] -> ys = snd (take_first xs) -> t2 = fst (take_first xs) ->
      srealizes SEGS (mkCfg (@mkst fx R1 (Z_to_bv 64 0x6bc84) M1 (seg_rom SEGS)) model1) K.
    Proof using AC MI ST MSpos fx A s R M model sp ret pat b cap xs K CB VEC Hne OBJ Hx31 NMX RP CONT.
      intros A1 M1 model1 b1 cap1 R1 ys t2 t0 PI TF SM G2 G8 G9 Ht2 Hys Hfst.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & HretR & HSTK & HSTK').
      pose proof PI as [AI MS FS SX ROC VEC' PP EF WIN]. pose proof VEC' as (Hv0 & Hv1 & HD & Hlen & Hbb & F0 & F1 & F2 & FEL).
      pose proof (PCargs pat_win) as PW. pose proof TF as (C1 & C2 & C3 & C4 & C5).
      rewrite Zlen_app in Hlen, F1. change (Zlen [t2]) with 1 in Hlen, F1. assert (Hys0 : 0 <= Zlen ys) by (unfold Zlen; lia).
      destruct Hbb as [[-> Hc0]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [lia|].
      destruct (ai_live_block MI A1 M1 model1 b1 (4 * cap1) AI HIn) as (_ & _ & _ & Hce & _).
      assert (Ht2r : 0 <= t2 < 2 ^ 32) by (cbn in Ht2; lia).
      pose proof (pop_know A1 M1 model1 b1 cap1 ys t2 R1 (sp - 64) t0 PI TF G2 Ht2r) as HK. cbv zeta in HK.
      set (E := Eseed R1 _) in HK.
      assert (HR : regs_ok E (srs sr_id [(2%bv, EAlu ALU_ADD (EVar 32) (ELit (-64))); (8%bv, EVar 33); (9%bv, EVar 37)]) R1)
        by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
            first [rewrite G2, zbv_add; f_equal; lia | exact G8 | exact G9]).
      cbn in Ht2. destruct Ht2 as [<-|[<-|[<-|[<-|[]]]]].
      all: xruns HR HK 80%nat TF_STOPS (SCR [] [] []) 40%N; [split_scs; first [sc_fl | sc_br] |].
      all: rreg HR' 1%bv A1'; rreg HR' 2%bv A2; rreg HR' 8%bv A8; rreg HR' 9%bv A9; rreg HR' 10%bv A10.
      all: eapply RETK; [ | exact A1' | rewrite A2, ?zbv_add; first [reflexivity | f_equal; lia] | exact A8 | exact A9 | same_of HR' SM | rewrite A10, <- Hfst; reflexivity ].
      all: rewrite <- Hys; eapply pop_pinv; [exact PI | norm_mem; reflexivity].
    Qed.

    Ltac regfrom HR' :=
      lazymatch goal with |- getr ?Rx ?r = _ =>
        let X := fresh in rreg_ HR' r X; rewrite X; rewrite ?zbv_add; first [reflexivity | f_equal; lia | apply sxw_small; lia]
      end.

    Ltac do_call first PIk TFk SMk HR' x src :=
      lazymatch goal with |- srealizes _ (mkCfg (@mkst _ ?Rk _ (wbytes ?Mk _ _) _) _) _ =>
      lazymatch type of PIk with TablPush.PINV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?A1 Mk ?model1 ?b1 ?cap1 ?ys =>
        let C1 := fresh "C" in let C2 := fresh "C" in let C3 := fresh "C" in let C4 := fresh "C" in let C5 := fresh "C" in
        pose proof TFk as (C1 & C2 & C3 & C4 & C5);
        eapply (CALL first A1 _ model1 b1 cap1 ys Rk _ src x);
        [ eapply (PCargs pinv_stores); [exact PIk | frame_stores]
        | tfr_tower C1 C2 C3 C4 C5
        | same_of HR' SMk
        | rewrite ?Zlen_app1; lia | rewrite ?Zlen_app1; lia
        | regfrom HR' | regfrom HR' | regfrom HR' | regfrom HR' | apply bv_eq; vm_compute; reflexivity | lia
        | regfrom HR' | regfrom HR' | lia | apply fld_wbytes4; lia | lia | clear C1 C2 C3 C4 C5 ]
      end end.

    Ltac seg_call first x src PIk TFk SMk G2 G8 G9 :=
      seg PIk TFk G2 G8 G9 (@nil bool);
      norm_mem;
      lazymatch goal with HR' : regs_ok _ _ ?Rn |- srealizes _ (mkCfg (@mkst _ ?Rn _ _ _) _) _ =>
        do_call first PIk TFk SMk HR' x src end.

    Lemma SAME0 : SAME R.  Proof using R. intros r _. reflexivity. Qed.

    Lemma take_first_cases : forall t,
      (t = 52 /\ take_first xs = (42, removelast xs ++ [52])) \/ (t = 53 /\ take_first xs = (45, removelast xs ++ [53])) \/
      (t = 54 /\ take_first xs = (47, removelast xs ++ [54; 1])) \/ (t = 55 /\ take_first xs = (42, removelast xs ++ [55; 6])) \/
      (t = 106 /\ take_first xs = (105, removelast xs ++ [106])) \/
      (t <> 52 /\ t <> 53 /\ t <> 54 /\ t <> 55 /\ t <> 106 /\ take_first xs = (t, removelast xs)) \/ t <> last xs 0.
    Proof using xs.
      intros t. destruct (Z.eq_dec t (last xs 0)) as [E|NE]; [|right; right; right; right; right; right; exact NE].
      unfold take_first. rewrite <- E. unfold expand, OT_VARIABLE_ID, OT_VARIABLE_LITERAL_INTEGER, OT_VARIABLE_LITERAL_INTEGER_ID,
        OT_VARIABLE_ID_LITERAL_INTEGER, OT_VARIABLE_CAPABILITY, OT_OPTIONAL_ID, OT_OPTIONAL_LITERAL_INTEGER, OT_ID,
        OT_OPTIONAL_TYPED_LITERAL_INTEGER, OT_LITERAL_INTEGER, OT_OPTIONAL_CAPABILITY.
      destruct (Z.eqb_spec t 52) as [->|N1]; [left; split; reflexivity|].
      destruct (Z.eqb_spec t 53) as [->|N2]; [right; left; split; reflexivity|].
      destruct (Z.eqb_spec t 54) as [->|N3]; [right; right; left; split; reflexivity|].
      destruct (Z.eqb_spec t 55) as [->|N4]; [right; right; right; left; split; reflexivity|].
      destruct (Z.eqb_spec t 106) as [->|N5]; [right; right; right; right; left; split; reflexivity|].
      right; right; right; right; right; left. repeat split; assumption.
    Qed.

    Lemma MAIN : srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 TF_ENTRY) M (seg_rom SEGS)) model) K.
    Proof using AC MI ST MSpos PB PB2 fx A s R M model sp ret pat b cap xs K CB Ha0 VEC Hne OBJ Hx31 NMX RP CONT.
      pose proof spf as (Hc & Hs47 & Hs16 & Hcv & Hs24 & GR2 & GR1 & HretR & HSTK & HSTK').
      pose proof (PCargs pinv_init) as PI0. pose proof PI0 as [AI MS FS SX ROC VEC' PP EF WIN]. pose proof HL1 as HL1'.
      pose proof VEC as (Hv0 & Hv1 & HD & Hlen & Hbb & F0 & F1 & F2 & FEL). pose proof (PCargs pat_win) as PW. pose proof SAME0 as SM0.
      destruct Hbb as [[-> Hc0]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [lia|].
      destruct (ai_live_block MI A M model b (4 * cap) AI HIn) as (_ & _ & _ & Hce & _).
      set (t := Znth (Zlen xs - 1) xs).
      assert (Ht : 0 <= t < 2 ^ 31) by (subst t; unfold Znth, Zlen in *; apply (proj1 (Forall_nth _ _) Hx31); lia).
      destruct (FEL (Zlen xs - 1) ltac:(lia)) as [_ FT]. fold t in FT. replace (b + 4 * (Zlen xs - 1)) with (b + 4 * Zlen xs + -4) in FT by lia.
      pose proof (Znth_last xs Hne) as TL. fold t in TL.
      destruct (exists_last Hne) as (ys & tl & Exs).
      assert (Etl : tl = t) by (rewrite TL, Exs, last_app1; reflexivity). subst tl.
      assert (RL : removelast xs = ys) by (rewrite Exs, removelast_app1; reflexivity).
      assert (Hys : Zlen ys = Zlen xs - 1) by (rewrite Exs, Zlen_app; change (Zlen [t]) with 1; lia).

      assert (SEGA : forall te : expr, edenot (Eseed R [Z_to_bv 64 sp; Z_to_bv 64 pat; Z_to_bv 64 (b + 4 * Zlen xs); Z_to_bv 64 t]) te = Z_to_bv 64 t -> forall ds : list bool,
        let E := Eseed R [Z_to_bv 64 sp; Z_to_bv 64 pat; Z_to_bv 64 (b + 4 * Zlen xs); Z_to_bv 64 t] in
        regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R /\
        know_ok SEGS E M [KWord (SA (EVar 33) 8) (N.to_nat 8) (EVar 34); KWord (SA (EVar 34) (-4)) (N.to_nat 4) te;
                          KWr (SA (EVar 32) (-64)) (ELit 64); KWr (SA (EVar 33) 0) (ELit 24);
                          KDisj (SA (EVar 33) 0) (ELit 24) (SA (EVar 32) (-64)) (ELit 64);
                          KDisj (SA (EVar 34) (-4)) (ELit 4) (SA (EVar 32) (-64)) (ELit 64);
                          KDisj (SA (EVar 34) (-4)) (ELit 4) (SA (EVar 33) 0) (ELit 24)]).
      { intros te Hte ds E. split.
        - apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption.
        - assert (G32 : ev E 32 = Z_to_bv 64 sp) by (evs; reflexivity). assert (G33 : ev E 33 = Z_to_bv 64 pat) by (evs; reflexivity).
          assert (G34 : ev E 34 = Z_to_bv 64 (b + 4 * Zlen xs)) by (evs; reflexivity).
          repeat apply Forall_cons; [kwv F1 G33 | | | | | | | apply Forall_nil].
          + eapply (kword_var _ _ _ _ (b + 4 * Zlen xs)); [cw_fix FT | cbn; lia | exact G34 | lia | lia | cbn; lia | exact Hte].
          + eapply (kwr_of_mdef SEGS E M 32 sp (-64) 64); [exact G32 | lia | lia | lia | lia |]. intros k Hk. replace (sp + -64 + k) with (sp - STK + (STK - 64 + k)) by lia. apply WIN. lia.
          + eapply (kwr_of_mdef SEGS E M 33 pat 0 24); [exact G33 | lia | lia | lia | lia |]. rewrite Z.add_0_r. exact HD.
          + eapply (kdisj_vars SEGS E M 33 32 pat sp); [exact G33 | exact G32 | lia | lia | lia | lia | lia].
          + eapply (kdisj_vars SEGS E M 34 32 (b + 4 * Zlen xs) sp); [exact G34 | exact G32 | lia | lia | lia | lia | lia].
          + eapply (kdisj_vars SEGS E M 34 33 (b + 4 * Zlen xs) pat); [exact G34 | exact G33 | lia | lia | lia | lia | lia]. }

      assert (TOWER : forall (v1 v2 v3 v5 v6 : word) (w7 : list byte),
        let M3 := wbytes (wbytes (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 v1)) (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 v2)) (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 v3) in
        let M4 := wbytes M3 (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs + -4))) in
        let M7 := wbytes (wbytes (wbytes M4 (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 v5)) (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 v6)) (Z_to_bv 64 (sp - 52)) w7 in
        length w7 = 4%nat -> PINV A M7 model b cap ys).
      { intros v1 v2 v3 v5 v6 w7 M3 M4 M7 Hw7.
        assert (PI3 : PINV A M3 model b cap xs) by (eapply (PCargs pinv_stores); [exact PI0 | subst M3; frame_stores]).
        assert (PI4 : PINV A M4 model b cap ys).
        { rewrite <- RL. eapply (PCargs pinv_pop); [exact PI3 | exact Hne | subst M4; do 3 f_equal; lia]. }
        eapply (PCargs pinv_stores); [exact PI4 | subst M7 M4 M3].
        do 3 (apply stores_in_wbytes_more; [ | lia | rewrite ?length_N_to_le_bytes, ?Hw7; cbn; lia | rewrite ?length_N_to_le_bytes, ?Hw7; intros x Hx; cbn in Hx; unfold zwin; lia ]).
        apply stores_in_refl. }
      destruct (take_first_cases t) as [[Et TFv]|[[Et TFv]|[[Et TFv]|[[Et TFv]|[[Et TFv]|[(N1 & N2 & N3 & N4 & N5 & TFv)|NE]]]]]];
        [ idtac .. | exfalso; exact (NE TL) ].
      all: rewrite RL in TFv.
      all: clear TL; clearbody t.
      1-5: subst t; destruct (SEGA (ELit _) eq_refl []) as [HR HK].

      1-5: xruns HR HK 60%nat TF_STOPS (SCR [] [] []) 40%N; [split_scs; first [sc_fl | sc_br] |]; norm_mem.
      1-5: lazymatch goal with |- srealizes _ (mkCfg (@mkst _ ?Rn _ (wbytes _ _ (word_to_le_bytes 4 (Z_to_bv 64 ?tv))) _) _) _ =>
             eapply (CALL true A _ model b cap ys Rn _ (sp - 52) tv tv);
             [ apply TOWER; reflexivity
             | tfr_tower HR HR HR HR HR
             | same_of HR' SM0
             | lia | lia
             | regfrom HR' | regfrom HR' | regfrom HR' | regfrom HR' | apply bv_eq; vm_compute; reflexivity | lia
             | regfrom HR' | regfrom HR' | left; reflexivity | apply fld_wbytes4; lia | lia
             | clear HR HK HR' Hlf; intros A1 R1 M1 model1 b1 cap1 PI1 TF1 SM1 G2a G8a G9a ] end.

      1: seg_call false 42 (sp - 56) PI1 TF1 SM1 G2a G8a G9a.
      1: intros A2 R2 M2 model2 b2 cap2 PI2 TF2 SM2 G2b G8b G9b.
      1: eapply (LASTSEG A2 M2 model2 b2 cap2 R2 (ys ++ [52]) 42 52 PI2 TF2 SM2 G2b G8b G9b ltac:(inl));
           rewrite TFv; [reflexivity | reflexivity].

      1: seg_call false 45 (sp - 56) PI1 TF1 SM1 G2a G8a G9a.
      1: intros A2 R2 M2 model2 b2 cap2 PI2 TF2 SM2 G2b G8b G9b.
      1: eapply (LASTSEG A2 M2 model2 b2 cap2 R2 (ys ++ [53]) 45 53 PI2 TF2 SM2 G2b G8b G9b ltac:(inl));
           rewrite TFv; [reflexivity | reflexivity].

      1: seg_call false 1 (sp - 56) PI1 TF1 SM1 G2a G8a G9a.
      1: intros A2 R2 M2 model2 b2 cap2 PI2 TF2 SM2 G2b G8b G9b.
      1: seg_call false 47 (sp - 56) PI2 TF2 SM2 G2b G8b G9b.
      1: intros A3 R3 M3 model3 b3 cap3 PI3 TF3 SM3 G2c G8c G9c.
      1: eapply (LASTSEG A3 M3 model3 b3 cap3 R3 ((ys ++ [54]) ++ [1]) 47 54 PI3 TF3 SM3 G2c G8c G9c ltac:(inl));
           rewrite TFv; [rewrite <- app_assoc; reflexivity | reflexivity].

      1: seg_call false 6 (sp - 56) PI1 TF1 SM1 G2a G8a G9a.
      1: intros A2 R2 M2 model2 b2 cap2 PI2 TF2 SM2 G2b G8b G9b.
      1: seg_call false 42 (sp - 56) PI2 TF2 SM2 G2b G8b G9b.
      1: intros A3 R3 M3 model3 b3 cap3 PI3 TF3 SM3 G2c G8c G9c.
      1: eapply (LASTSEG A3 M3 model3 b3 cap3 R3 ((ys ++ [55]) ++ [6]) 42 55 PI3 TF3 SM3 G2c G8c G9c ltac:(inl));
           rewrite TFv; [rewrite <- app_assoc; reflexivity | reflexivity].

      1: seg_call false 105 (sp - 56) PI1 TF1 SM1 G2a G8a G9a.
      1: intros A2 R2 M2 model2 b2 cap2 PI2 TF2 SM2 G2b G8b G9b.
      1: eapply (LASTSEG A2 M2 model2 b2 cap2 R2 (ys ++ [106]) 105 106 PI2 TF2 SM2 G2b G8b G9b ltac:(inl));
           rewrite TFv; [reflexivity | reflexivity].

      destruct (SEGA (EVar 35) ltac:(evs; reflexivity) []) as [HR HK].
      assert (MS' : mstd model) by exact MS.
      destruct (Z.le_gt_cases t 53) as [Hle|Hgt];
        [ xruns HR HK 80%nat TF_STOPS (SCR [true; false; true] [] []) 40%N
        | xruns HR HK 80%nat TF_STOPS (SCR [false; false; false; true] [] []) 40%N ].
      1,3: split_scs; first [sc_fl | cbn [sc_denot]; evs; rewrite ?(ext_val_sx_id 4) by (first [lia | rewrite u64_of_Z by lia; cbn; lia]);
                                      rewrite ?br_ge, ?br_lt, ?br_eq, ?br_ne by lia; bool_lia].
      all: norm_mem; rreg HR' 1%bv A1'; rreg HR' 2%bv A2; rreg HR' 8%bv A8; rreg HR' 9%bv A9; rreg HR' 10%bv A10.
      all: eapply RETK; [ | exact A1' | rewrite A2, ?zbv_add; first [reflexivity | f_equal; lia] | exact A8 | exact A9 | same_of HR' SM0
                        | rewrite A10, TFv; cbn [fst]; rewrite ?(ext_val_sx_id 4) by (first [lia | rewrite u64_of_Z by lia; cbn; lia]); reflexivity ].
      all: rewrite TFv; cbn [snd]; apply TOWER; reflexivity.
    Qed.
  End Body.

  Theorem take_first_spec : take_first_stmt SEGS L MI ST tc cpbP1.
  Proof using AC MI ST MSpos PB PB2.
    intros fx A s R M model sp ret pat b cap xs K.
    cbn [tc_pattern_stack tc_take_first Img.tc vc_stack cpbP1].
    intros CB Ha0 VEC Hne OBJ PAT8 Hx31 NMX RP CONT.
    eapply (MAIN fx A s R M model sp ret pat b cap xs K); eassumption.
  Qed.
End PT.
