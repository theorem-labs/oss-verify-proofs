(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 SumMemsetLib SumMemset S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac DiagS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition APP_STK : Z := 80.
Definition APP_RET1 : Z := 0x8b748.
Definition APP_RETPC : Z := 0x8b79c.

Section Append.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.

  Definition FUEL : nat := 200%nat.
  Definition STOPS : list Z := [A_MEMSET].

  Definition app_W (sp p d len n : Z) (a : Z) : Prop :=
    zwin (p + 8) (p + 16) a \/ zwin (d + len) (d + len + n + 1) a \/ zwin (sp - APP_STK) sp a.

  Theorem str_append_long : forall A (M : mem) (R : bvmap 5 word) (sp ret p n ch d asz : Z) (cs : list Z),
    str_rep MI A M p (SLong d asz) cs -> 0 < n -> Zlen cs + n <= asz - 1 ->
    mdef M d asz ->
    (forall a, zwin p (p + 24) a \/ zwin d (d + asz) a -> ~ zwin (sp - APP_STK) sp a) ->
    stack_room SEGS M sp APP_STK -> 2 ^ 16 <= sp - APP_STK -> sp < 2 ^ 47 ->
    ret_ok (Z_to_bv 64 ret) -> getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> getr R 12%bv = Z_to_bv 64 ch ->
    0 <= ch < 2 ^ 64 -> 0 <= ret < 2 ^ 64 ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 A_STR_APPEND) M (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 p
      /\ str_rep MI A M' p (SLong d asz) (cs ++ repeat (ch mod 256) (Z.to_nat n))
      /\ stores_in (app_W sp p d (Zlen cs) n) M M'.
  Proof using fx AC MI.
    intros A M R sp ret p n ch d asz cs STR Hn Hroom HDd DISJ HROOM Hsplo Hsphi Hret Hra Hsp Ha0 Ha1 Ha2 Hch Hretr.
    unfold APP_STK in *. pose proof STR as STR0. destruct STR as (Hp0 & Hp1 & HDp & Hlen & HM & FC & FN). cbn [str_cap str_data] in *.
    destruct HM as (Hd0 & Hd16 & Hdsz & Hal & Hmin & HIn & Hdj & F0 & F1 & F2). unfold SSO_CAP in Hmin.
    set (len := Zlen cs) in *.
    assert (DJp : p + 24 <= sp - 80 \/ sp <= p).
    { destruct (Z.lt_ge_cases (p + 24) (sp - 80 + 1)); [lia|]. destruct (Z.lt_ge_cases p sp); [|lia]. exfalso.
      destruct (Z.lt_ge_cases p (sp - 80)); [apply (DISJ (sp - 80)); [left|]; unfold zwin; lia | apply (DISJ p); [left|]; unfold zwin; lia]. }
    assert (DJd : d + asz <= sp - 80 \/ sp <= d).
    { destruct (Z.lt_ge_cases (d + asz) (sp - 80 + 1)); [lia|]. destruct (Z.lt_ge_cases d sp); [|lia]. exfalso.
      destruct (Z.lt_ge_cases d (sp - 80)); [apply (DISJ (sp - 80)); [right|]; unfold zwin; lia | apply (DISJ d); [right|]; unfold zwin; lia]. }
    clear DISJ.

    set (E := Eseed R [Z_to_bv 64 (asz + 1); Z_to_bv 64 len; Z_to_bv 64 d; Z_to_bv 64 asz]).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M
      [KWr (SA (EVar 2) (-80)) (ELit 80);
       KWord (SA (EVar 10) 0) (N.to_nat 8) (EAlu ALU_ADD (EVar 35) (ELit 1)); KAlign (EVar 35) 8;
       KWord (SA (EVar 10) 8) (N.to_nat 8) (EVar 33); KWord (SA (EVar 10) 16) (N.to_nat 8) (EVar 34);
       KRange (EVar 11) 1 (2 ^ 63); KRange (EVar 32) 47 (2 ^ 63); KRange (EVar 33) 0 (2 ^ 63);
       KRange (EVar 2) (2 ^ 16 + 80) (2 ^ 47); KRange (EVar 10) 0 (2 ^ 63 - 24); KRange (EVar 34) 1 (2 ^ 63);
       KDisj (SA (EVar 10) 0) (ELit 24) (SA (EVar 2) (-80)) (ELit 80);
       KDisj (SA (EVar 34) 0) (EVar 35) (SA (EVar 2) (-80)) (ELit 80)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply kwr_stack; [evs; exact Hsp | reflexivity | lia | lia | exact HROOM].
      - eapply (kword_var _ _ _ _ p); [eapply fld_cellw; [fld_fix F0 | cbn; lia] | cbn; lia | evs; exact Ha0 | lia | lia | cbn; lia | evs ].
        rewrite alu_Z by lia. cbn [zar]. f_equal. rewrite Z.mod_small by lia. reflexivity.
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hal].
      - kwv F1 Ha0.
      - kwv F2 Ha0.
      - krv Ha1.
      - krv Ha1.
      - krv Ha1.
      - krv Hsp.
      - krv Ha0.
      - krv Ha0.
      - kdj p 24 sp 80. lia.
      - kdj d asz sp 80. lia. }
    xrun HR HK FUEL STOPS (SCR [true; true] [] []) 40%N.
    { repeat apply Forall_cons; try apply Forall_nil; cbn [sc_denot]; zbr_auto. }
    clear HK. rename R' into R1. rename HR' into HR1.
    regval HR1 (10%bv : reg) (d + len) X10. regval HR1 (11%bv : reg) ch X11. regval HR1 (12%bv : reg) n X12.
    regval HR1 (1%bv : reg) APP_RET1 X1. regval HR1 (2%bv : reg) (sp - 80) X2. regval HR1 (8%bv : reg) p X8.
    regval HR1 (20%bv : reg) d X20. regval HR1 (22%bv : reg) (len + n) X22.
    wnorm_in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms end.
    assert (ST1 : stores_in (zwin (sp - 80) sp) M M1) by (subst M1; stores_tower).
    assert (HD1 : mdef M1 d asz) by (eapply stores_in_mdef; [exact ST1 | exact HDd]).

    destruct (s1_memset M1 (Z_to_bv 64 (d + len)) (Z_to_bv 64 ch) (Z_to_bv 64 APP_RET1) n (seg_rom SEGS) R1
                ltac:(lia) ltac:(rewrite u64_of_Z by lia; lia)
                ltac:(replace (d + len) with (d + (len)) by lia; eapply mdef_store_ok_off; [exact HD1 | lia | lia | lia | lia])
                ltac:(apply bv_eq; vm_compute; reflexivity) X10 X11 X12 X1)
      as (R2 & Hms2 & Y10 & AG).
    replace s1_memset_entry with (Z_to_bv 64 A_MEMSET) in Hms2 by (apply bv_eq; vm_compute; reflexivity).
    set (M2 := wbytes M1 (Z_to_bv 64 (d + len)) (repeat (cbyte (Z_to_bv 64 ch)) (Z.to_nat n))) in Hms2.
    assert (Y : forall r, ~ In r ms_clob -> getr R2 r = getr R1 r) by (intros r Hr; exact (AG r Hr)).
    assert (Y2 : getr R2 2%bv = Z_to_bv 64 (sp - 80)) by (rewrite Y by ninl; exact X2).
    assert (Y8 : getr R2 8%bv = Z_to_bv 64 p) by (rewrite Y by ninl; exact X8).
    assert (Y20 : getr R2 20%bv = Z_to_bv 64 d) by (rewrite Y by ninl; exact X20).
    assert (Y22 : getr R2 22%bv = Z_to_bv 64 (len + n)) by (rewrite Y by ninl; exact X22).
    assert (ST2 : stores_in (fun a => zwin (d + len) (d + len + n) a \/ zwin (sp - 80) sp a) M M2).
    { subst M2. eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST1 | intros a Ha; right; exact Ha] | lia | rewrite repeat_length; lia | ].
      intros x Hx. rewrite repeat_length in Hx. left. unfold zwin. lia. }

    set (E2 := Eseed R2 [Z_to_bv 64 asz; Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv;
                          getr R 20%bv; getr R 21%bv; getr R 22%bv; getr R 23%bv; getr R 24%bv]).
    assert (HR2 : regs_ok E2 sr_id R2) by (apply regs_ok_seed).
    assert (SLOT : forall k (v : word), In (k, v) [(1, Z_to_bv 64 ret); (2, getr R 8%bv); (3, getr R 9%bv); (4, getr R 18%bv); (5, getr R 19%bv);
                                                (6, getr R 20%bv); (7, getr R 21%bv); (8, getr R 22%bv); (9, getr R 23%bv); (10, getr R 24%bv)] ->
                   cellw SEGS M2 (sp - 8 * k) 8 (bv_unsigned v)).
    { intros k v Hin. split; [pose proof (u64_range v); cbn; lia|]. rewrite Z_to_bv_bv_unsigned. subst M2 M1.
      cbn in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; peel; reflexivity|]). destruct Hin. }
    assert (HW0 : cellw SEGS M2 p 8 (asz + 1)).
    { split; [cbn; lia|]. subst M2 M1. peel. exact F0. }
    assert (HK2 : know_ok SEGS E2 M2
      [KWord (SA (EVar 8) 0) (N.to_nat 8) (EAlu ALU_ADD (EVar 32) (ELit 1)); KAlign (EVar 32) 8;
       KWr (SA (EVar 8) 8) (ELit 8); KWr (SA (EAlu ALU_ADD (EVar 20) (EVar 22)) 0) (ELit 1);
       KDisj (SA (EAlu ALU_ADD (EVar 20) (EVar 22)) 0) (ELit 1) (SA (EVar 2) 0) (ELit 80);
       KDisj (SA (EVar 8) 0) (ELit 24) (SA (EVar 2) 0) (ELit 80);
       KRange (EVar 2) (2 ^ 16) (2 ^ 47); KRange (EVar 8) 0 (2 ^ 63 - 24); KRange (EVar 20) 1 (2 ^ 63); KRange (EVar 22) 1 (2 ^ 63);
       KWord (SA (EVar 2) 72) (N.to_nat 8) (EVar 33); KWord (SA (EVar 2) 64) (N.to_nat 8) (EVar 34);
       KWord (SA (EVar 2) 56) (N.to_nat 8) (EVar 35); KWord (SA (EVar 2) 48) (N.to_nat 8) (EVar 36);
       KWord (SA (EVar 2) 40) (N.to_nat 8) (EVar 37); KWord (SA (EVar 2) 32) (N.to_nat 8) (EVar 38);
       KWord (SA (EVar 2) 24) (N.to_nat 8) (EVar 39); KWord (SA (EVar 2) 16) (N.to_nat 8) (EVar 40);
       KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 41); KWord (SA (EVar 2) 0) (N.to_nat 8) (EVar 42)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kword_var _ _ _ _ p); [rewrite Z.add_0_r; exact HW0 | cbn; lia | evs; exact Y8 | lia | lia | cbn; lia | evs ].
        rewrite alu_Z by lia. cbn [zar]. f_equal. rewrite Z.mod_small by lia. reflexivity.
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hal].
      - eapply kwr_of_mdef; [evs; exact Y8 | lia | lia | lia | lia |]. eapply stores_in_mdef; [exact ST2|]. eapply mdef_sub; [exact HDp | lia | lia].
      - cbn [kentry_ok]. unfold flat, estart, elenZ, adenot. cbn [a_base a_off edenot]. evs. regsub.
        rewrite alu_Z by lia. cbn [zar].
        rewrite Z.mod_small, !u64_of_Z by lia.
        split; [lia|]. intros dd m Hdd Hdm. destruct m as [|m']; [reflexivity|].
        rewrite <- (Nat2Z.id (S m')). apply store_ok_of_defined; [lia | lia |].
        eapply (stores_in_mdef _ _ _ _ _ ST2). eapply mdef_sub; [exact HDd | lia | lia].
      - cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. evs. regsub.
        rewrite alu_Z by lia. cbn [zar]. rewrite Z.mod_small, !u64_of_Z by lia. lia.
      - kdj p 24 (sp - 80) 80. lia.
      - krv Y2.
      - krv Y8.
      - krv Y20.
      - krv Y22.
      - kwv (SLOT 1 _ ltac:(inl)) Y2.
      - kwv (SLOT 2 _ ltac:(inl)) Y2.
      - kwv (SLOT 3 _ ltac:(inl)) Y2.
      - kwv (SLOT 4 _ ltac:(inl)) Y2.
      - kwv (SLOT 5 _ ltac:(inl)) Y2.
      - kwv (SLOT 6 _ ltac:(inl)) Y2.
      - kwv (SLOT 7 _ ltac:(inl)) Y2.
      - kwv (SLOT 8 _ ltac:(inl)) Y2.
      - kwv (SLOT 9 _ ltac:(inl)) Y2.
      - kwv (SLOT 10 _ ltac:(inl)) Y2. }
    xrun_at HR2 HK2 fx APP_RET1 (seg_rom SEGS) FUEL [APP_RETPC] (SCR [true] [] []) 50%N.
    { scs_auto. }
    clear HK2. rename R' into R3. rename HR' into HR3. rename Hms0 into Hms3.
    regval HR3 (1%bv : reg) ret Z1. regval HR3 (10%bv : reg) p Z10.
    wnorm_in Hms3.
    lazymatch type of Hms3 with msteps _ _ (mkst _ _ ?m _) => set (M3 := m) in Hms3 end.

    pose proof (ret_at SEGS APP_RETPC R3 M3 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) Z1 Hret) as Hms4.
    exists R3, M3. split; [|split; [|split; [exact Z10 | split]]].
    - eapply msteps_trans; [exact Hms|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|]. exact Hms4.
    -
      intros r Hr. unfold callee_saved in Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [kept_via HR3 Y HR1|]). destruct Hr.
    -
      assert (SI : stores_in (fun a => zwin (sp - 80) sp a \/ zwin (p + 8) (p + 16) a \/ zwin (d + len) (d + len + n + 1) a) M M3).
      { subst M3. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST2|] | | |] | | |];
          rewrite ?repeat_length, ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia. }
      assert (AGR : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= sp - 80 \/ sp <= lo) -> (hi <= p + 8 \/ p + 16 <= lo) ->
                     (hi <= d + len \/ d + len + n + 1 <= lo) -> agree_on (zwin lo hi) M M3).
      { intros lo hi H1 H2 H3 H4 H5. eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin in *. lia. }
      assert (Hchr : 0 <= ch mod 256 < 256) by (apply Z.mod_pos_bound; lia).
      unfold CRep.str_rep. rewrite Zlen_app, Zlen_repeat by lia. fold len. cbn [str_cap str_data].
      split; [exact Hp0|]. split; [exact Hp1|]. split; [eapply stores_in_mdef; [exact SI|exact HDp]|].
      split; [lia|].
      split. { split; [lia|]. split; [exact Hd16|]. split; [lia|]. split; [exact Hal|]. split; [unfold SSO_CAP; lia|].
               split; [exact HIn|]. split; [exact Hdj|].
               split. { unfold fld. rewrite <- F0. apply rdn_agree_win; [lia|cbn; lia|]. apply AGR; cbn; lia. }
               split. { unfold fld. subst M3. peel. }
               unfold fld. rewrite <- F2. apply rdn_agree_win; [lia|cbn; lia|]. apply AGR; cbn; lia. }
      split.
      + intros i Hi. destruct (Z.lt_ge_cases i len) as [Hlt|Hge].
        * rewrite Znth_app_l by lia. destruct (FC i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
          eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AGR; cbn; lia.
        * rewrite Znth_app_r, Znth_repeat by lia. split; [exact Hchr|].
          unfold fld. subst M3 M2. peel.
          replace (d + i) with (d + len + (i - len)) by lia.
          replace (word_to_le_bytes 1 (Z_to_bv 64 (ch mod 256))) with (repeat (cbyte (Z_to_bv 64 ch)) 1).
          2:{ cbn [repeat]. unfold cbyte. apply sb_byte_w1. }
          apply rdn_repeat_sub; lia.
      + unfold fld. subst M3. replace (d + (len + n)) with (d + len + n) by lia.
        change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
        change 1%nat with (length [Z_to_bv 8 0]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
    - eapply stores_in_weaken; [|]. 2: intros a Ha; exact Ha.
      subst M3. unfold app_W, APP_STK.
      eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST2|] | | |] | | |];
        rewrite ?repeat_length, ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia.
  Qed.
End Append.
