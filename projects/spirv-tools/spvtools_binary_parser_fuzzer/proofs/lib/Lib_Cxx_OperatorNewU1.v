(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  DivergeSim SRealizes ShapeUpto RefMemcpyLib SymExec3 SymExec3Sound LibIface
  U1_code_e7b00_e7b74 .
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma u64_of_Z : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply u_Z2bv; lia. Qed.

Lemma rdn8_agree : forall (M1 M2 : word -> option byte) (a : word),
  (bv_unsigned a + 8 <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + 8)%Z -> M2 x = M1 x) ->
  rdn SEGS M2 a 8 = rdn SEGS M1 a 8.
Proof.
  intros M1 M2 a Hnw Hag. apply rdn_ext; [cbn; lia|]. intros x Hx. apply Hag. cbn in Hx. lia.
Qed.

Lemma rdn_wbytes_hit : forall (m : word -> option byte) (a : word) (v : word),
  (bv_unsigned a + 8 <= 2 ^ 64)%Z ->
  rdn SEGS (wbytes m a (word_to_le_bytes 8 v)) a 8 = Some (word_to_le_bytes 8 v).
Proof. intros m a v Hnw. apply rdn_wbytes_hit8; lia. Qed.

Section OpNew.

  Context {AC : AllocCeiling}.
  Definition L : Layout := U1Layout.L.

  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Hypothesis MALLOC_STACK_pos : 0 <= MALLOC_STACK MI.

  Definition NEW_STACK : Z := 16 + MALLOC_STACK MI.

  Theorem operator_new_spec : new_rule_stmt SEGS L MI ST NEW_STACK.
  Proof.
    intros fx A s R M model n sp ret K AI MS ROC SXI SXH CR Ha0 Hn Hsp Hroom Hwin Hown_sx Herr_sx ROOM CONT.
    destruct CR as [Hra Hret Hretr Hsp2 Hsp16 Hsphi Hgp Htp].
    cbn [ly_new ly_malloc ly_gp ly_tp ly_errno_off ly_img ly_relro ly_new_handler ly_oom_spin L U1Layout.L] in *.
    unfold NEW_STACK in *.
    pose proof ac_bounds_lit as Hceil.
    pose proof Hroom as HOK; unfold stack_room in HOK.
    assert (Hn64 : (0 <= n < 2 ^ 62)%Z).
    { pose proof (ai_big_pos MI). pose proof (ai_nmax_bound MI). lia. }
    assert (Hns : (0 < new_size n < 2 ^ 62)%Z) by (unfold new_size; lia).

    set (M1 := wbytes (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 ret)))
                      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 (getr R 8))).
    assert (M1_out : forall a : word, ~ (sp - 16 <= bv_unsigned a < sp)%Z -> M1 a = M a).
    { intros a Ha. unfold M1.
      rewrite (wbytes_outside _ _ (Z_to_bv 64 (sp - 16)) a)
        by (rewrite ?length_word_to_le_bytes, u64_of_Z by lia; cbn; lia).
      rewrite (wbytes_outside _ _ (Z_to_bv 64 (sp - 8)) a)
        by (rewrite ?length_word_to_le_bytes, u64_of_Z by lia; cbn; lia).
      reflexivity. }
    assert (M1_grows : forall a : word, M a <> None -> M1 a <> None).
    { intros a Ha. unfold M1. apply wbytes_grows, wbytes_grows. exact Ha. }
    assert (M1_ra : rdn SEGS M1 (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))).
    { unfold M1. rewrite rdn_wbytes_out
        by (rewrite ?length_word_to_le_bytes, ?u64_of_Z by lia; cbn; lia).
      apply rdn_wbytes_hit. rewrite u64_of_Z by lia. lia. }
    assert (M1_s0 : rdn SEGS M1 (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8))).
    { unfold M1. apply rdn_wbytes_hit. rewrite u64_of_Z by lia. lia. }

    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
    - norm_pc. sv F_e7b00 D_e7b00 (Z_to_bv 64 (sp - 16)).
      stw F_e7b04 D_e7b04 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
      stw F_e7b08 D_e7b08 (Z_to_bv 64 (sp - 16)) (getr R 8) ltac:(ok_sub HOK).
      stepiv F_e7b0c D_e7b0c (Z_to_bv 64 (if n =? 0 then 1 else 0)) ltac:(idtac).
      { gres. rewrite Ha0. unfold v_sltiu. rewrite (u_Z2bv n) by lia.
        change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z.
        destruct (Z.eqb_spec n 0) as [->|Hne]; [reflexivity|].
        destruct (Z.ltb_spec n 1); [exfalso; lia | reflexivity]. }
      stepiv F_e7b10 D_e7b10 (Z_to_bv 64 (new_size n)) ltac:(idtac).
      { gres. rewrite Ha0. unfold v_add. rewrite !u_Z2bv by (try destruct (n =? 0); lia).
        unfold new_size. f_equal. destruct (Z.eqb_spec n 0) as [->|Hne]; lia. }
      sv F_e7b14 D_e7b14 (Z_to_bv 64 (new_size n)).
      stepj F_e7b18 D_e7b18.
      apply mst_refl.
    -
      fold M1.
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?R1 ?pc1 _ _) _) _ =>
        replace pc1 with (Z_to_bv 64 (ly_malloc L)) by (apply bv_eq; reflexivity);
        set (R1v := R1) end.
      eapply (mi_malloc MI fx A R1v M1 model (new_size n) (sp - 16) 0xe7b50 K).
      +
        eapply (ai_frame MI); [exact AI | | | reflexivity | reflexivity].
        * intros a Ho. apply M1_out. intros Hin. exact (proj1 (Hwin (bv_unsigned a) ltac:(unfold zwin; lia)) Ho).
        * exact M1_grows.
      + exact MS.
      +
        intros w Hiw Hnrw. rewrite M1_out; [exact (ROC w Hiw Hnrw)|].
        intros Hst. destruct Hiw as (lo & hi & Hin & Hr). cbn [ly_img L U1Layout.L] in Hin.
        destruct Hin as [E|[]]. injection E as <- <-. lia.
      +
        subst R1v. constructor; gres.
        * apply bv_eq; vm_compute; reflexivity.
        * unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
        * lia.
        * reflexivity.
        * replace (sp - 16)%Z with (sp + (-1) * 16)%Z by lia. rewrite Z.mod_add by lia. exact Hsp16.
        * lia.
        * exact Hgp.
        * exact Htp.
      + subst R1v. gres. reflexivity.
      + pose proof (ai_big_pos MI). unfold new_size. lia.
      + lia.
      +
        unfold stack_room, M1. ok_sub HOK.
      + intros a Ha. apply (proj1 (Hwin a ltac:(unfold zwin in *; lia))).
      + exact ROOM.
      +
        intros A' R' M' model' p AI' MS' Hfs Hfds KEPT Ha0' Hp LADD CAPS BIGC NEWT FR DEF.

        assert (HinP : In (p, new_size n) (live MI A')) by (rewrite (proj1 LADD); left; reflexivity).
        destruct (ai_live_block MI A' M' model' p (new_size n) AI' HinP) as (_ & _ & _ & Hpce & Hpown).

        assert (R'2 : getr R' 2 = Z_to_bv 64 (sp - 16)).
        { rewrite (KEPT 2%bv) by (cbn; tauto). subst R1v. gres. reflexivity. }
        assert (R'1 : getr R' 1 = Z_to_bv 64 0xe7b50).
        { rewrite (KEPT 1%bv) by (cbn; tauto). subst R1v. gres. apply bv_eq; vm_compute; reflexivity. }

        assert (SLOT : forall x : word, (sp - 16 <= bv_unsigned x < sp)%Z -> M' x = M1 x).
        { intros x Hx. apply FR. intros [Ho | [Hpx | [Hw | He]]].
          - destruct (NEWT _ Ho) as [HoA | [Hni Hnone]].
            + exact (proj1 (Hwin (bv_unsigned x) ltac:(unfold zwin; lia)) HoA).
            + rewrite Z_to_bv_bv_unsigned in Hnone. revert Hnone. unfold M1.
              destruct (Z.lt_ge_cases (bv_unsigned x) (sp - 8)).
              * rewrite wbytes_inside by (rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn; lia). discriminate.
              * rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn; lia).
                rewrite wbytes_inside by (rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn; lia). discriminate.
          - lia.
          - unfold zwin in Hw. lia.
          - unfold errno_win, zwin in He. cbn [ly_tp ly_errno_off L U1Layout.L] in He. lia. }
        assert (RA' : rdn SEGS M' (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))).
        { rewrite (rdn8_agree M1 M'); [exact M1_ra | rewrite u64_of_Z by lia; lia |].
          intros x Hx. rewrite u64_of_Z in Hx by lia. apply SLOT. lia. }
        assert (S0' : rdn SEGS M' (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8))).
        { rewrite (rdn8_agree M1 M'); [exact M1_s0 | rewrite u64_of_Z by lia; lia |].
          intros x Hx. rewrite u64_of_Z in Hx by lia. apply SLOT. lia. }

        eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        * norm_pc.
          stepb_tk F_e7b1c D_e7b1c ltac:(try rewrite Ha0'; try rewrite getr_zero; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
          ld_step F_e7b38 D_e7b38 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret)
                  ltac:(first [ exact RA' | replace (sp - 16 + 8)%Z with (sp - 8)%Z by lia; exact RA' ])
                  ltac:(apply bytes_le_to_Z_8).
          ld_step F_e7b3c D_e7b3c (word_to_le_bytes 8 (getr R 8)) (getr R 8)
                  ltac:(first [ exact S0' | replace (sp - 16 + 0)%Z with (sp - 16)%Z by lia; exact S0' ])
                  ltac:(apply bytes_le_to_Z_8).
          sv F_e7b40 D_e7b40 (Z_to_bv 64 sp).
          stepjr F_e7b44 D_e7b44 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
          apply mst_refl.
        *
          replace (v_jalr (Z_to_bv 64 ret) (bv_signed 0)) with (v_jalr (Z_to_bv 64 ret) 0) by reflexivity.
          unfold ret_ok in Hret. rewrite Hret.

          assert (IMGsx : forall a, sx_region ST a -> (0xef000 <= a < 0x124000)%Z).
          { intros a Ha. destruct (sx_region_rw ST a Ha) as (lo & hi & Hin & Hr). cbn [ly_rw L U1Layout.L] in Hin.
            destruct Hin as [E|[]]. injection E as <- <-. exact Hr. }
          assert (OWNimg : forall a, owned MI A a -> (0xef000 <= a < 0x124000)%Z \/ ~ (0x10000 <= a < 0x124000)%Z).
          { intros a Ho. destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw|Hni].
            - left. destruct Hrw as (lo & hi & Hin & Hr). cbn [ly_rw L U1Layout.L] in Hin. destruct Hin as [E|[]]. injection E as <- <-. exact Hr.
            - right. intros Hc. apply Hni. exists 0x10000%Z, 0x124000%Z. split; [left; reflexivity | exact Hc]. }
          assert (NEWimg : forall a, owned MI A' a -> owned MI A a \/ (~ (0x10000 <= a < 0x124000)%Z /\ M1 (Z_to_bv 64 a) = None)).
          { intros a Ho. destruct (NEWT a Ho) as [HoA|[Hni Hm]]; [left; exact HoA | right]. split; [|exact Hm].
            intros Hc. apply Hni. exists 0x10000%Z, 0x124000%Z. split; [left; reflexivity | exact Hc]. }

          assert (FRM : frame_eq (fun a => owned MI A' a \/ (p <= a < p + new_size n)%Z
                                        \/ zwin (sp - (16 + MALLOC_STACK MI)) sp a \/ errno_win L a) M M').
          { intros a Hna. rewrite (FR a).
            - apply M1_out. intros Hst. apply Hna. right; right; left. unfold zwin. lia.
            - intros [Ho|[Hq|[Hw|He]]]; apply Hna.
              + left; exact Ho. + right; left; exact Hq.
              + right; right; left. unfold zwin in *. lia. + right; right; right; exact He. }
          eapply (CONT A' _ M' model' p AI' MS' Hfs Hfds).
          --
             apply (sx_frame ST s M M' SXI). intros a Ha.
             assert (Himg : (0x10000 <= bv_unsigned a < 0x124000)%Z).
             { destruct Ha as [Hs|Hr]; [pose proof (IMGsx _ Hs); lia|].
               destruct Hr as (lo & hi & Hin & Hr). cbn [ly_relro L U1Layout.L] in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia. }
             apply FRM. intros [Ho|[Hq|[Hw|He]]].
             ++ destruct (NEWimg _ Ho) as [HoA|[HnA _]].
                ** destruct Ha as [Hs|Hr]; [exact (Hown_sx _ HoA Hs)|].
                   destruct Hr as (lo & hi & Hin & Hr). cbn [ly_relro L U1Layout.L] in Hin. destruct Hin as [E|[]]. injection E as <- <-.
                   destruct (OWNimg _ HoA); lia.
                ** exact (HnA Himg).
             ++ destruct (Hpown (bv_unsigned a) Hq) as (_ & Hni & _). apply Hni.
                exists 0x10000%Z, 0x124000%Z. split; [left; reflexivity | exact Himg].
             ++ unfold zwin in Hw. lia.
             ++ destruct Ha as [Hs|Hr]; [exact (Herr_sx _ He Hs)|].
                unfold errno_win, zwin in He. cbn [ly_tp ly_errno_off L U1Layout.L] in He.
                destruct Hr as (lo & hi & Hin & Hr). cbn [ly_relro L U1Layout.L] in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia.
          --
             intros r Hr.
             destruct (decide (r = 2%bv)) as [->|Hn2]; [rewrite getr_same by (intros E; discriminate E); symmetry; exact Hsp2|].
             rewrite (getr_other _ 2%bv) by exact Hn2.
             destruct (decide (r = 8%bv)) as [->|Hn8]; [rewrite getr_same by (intros E; discriminate E); reflexivity|].
             rewrite (getr_other _ 8%bv) by exact Hn8.
             destruct (decide (r = 1%bv)) as [->|Hn1]; [rewrite getr_same by (intros E; discriminate E); symmetry; exact Hra|].
             rewrite (getr_other _ 1%bv) by exact Hn1.
             rewrite (KEPT r Hr). subst R1v.
             assert (Hn10 : r <> 10%bv).
             { intros ->. cbn in Hr. intuition discriminate. }
             rewrite (getr_other _ 1%bv) by exact Hn1. rewrite (getr_other _ 10%bv) by exact Hn10.
             rewrite (getr_other _ 8%bv) by exact Hn8. rewrite (getr_other _ 8%bv) by exact Hn8.
             rewrite (getr_other _ 2%bv) by exact Hn2. reflexivity.
          -- rewrite (getr_other _ 2%bv), (getr_other _ 8%bv), (getr_other _ 1%bv) by (intros E; discriminate E). exact Ha0'.
          -- exact Hp. -- exact LADD. -- exact CAPS. -- exact BIGC.
          -- intros a Ho. destruct (NEWT a Ho) as [HoA|[Hni Hm]]; [left; exact HoA | right]. split; [exact Hni|].
             rewrite <- (M1_out (Z_to_bv 64 a)); [exact Hm|].

             pose proof (ai_owned_below_ceiling MI A' M' model' a AI' Ho Hni) as Hac.
             rewrite u64_of_Z by lia. lia.
          -- exact FRM.
          --
             intros a Hd. destruct (DEF a (M1_grows a Hd)) as [Hd'|Ho];
               [left; exact Hd'| right; exact Ho].
  Qed.
End OpNew.
