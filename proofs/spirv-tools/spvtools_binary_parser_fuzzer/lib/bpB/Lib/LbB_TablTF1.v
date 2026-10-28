(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BacX BellsX HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0 BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablLO LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablXP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TF_HEAD : Z := 0xffed4.
Definition TF_ANN_RET : Z := 0xfff44.
Definition TF_XP_RET : Z := 0xfff50.
Definition TF_RET : Z := 0xfff9c.

Definition KTB1 : list reg := [3; 4; 19; 25; 26; 27]%bv.
Definition KTPOP : list reg := [2; 3; 4; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition KTCALL : list reg := [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition KTBACK : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition KTEXIT : list reg := [3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma ext4_small : forall x, 0 <= x < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. f_equal.
  change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31). change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Section TF1.
  Context {HCEIL : HeapCeil}.

  Lemma tf_b1 : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) (SP v lo : Z),
    getr R 1 = ra -> getr R 2 = Z_to_bv 64 SP -> getr R 8 = s0 -> getr R 9 = s1 -> getr R 18 = s2 -> getr R 19 = s3 ->
    getr R 20 = s4 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 10 = Z_to_bv 64 v -> rfull R ->
    SP mod 16 = 0 -> 2 ^ 45 <= SP <= 2 ^ 47 -> 0 <= v -> v + 24 <= 2 ^ 47 -> v <> 0 -> v mod 8 = 0 ->
    stk asegs m lo SP -> lo <= SP - 80 -> mem_inv asegs m -> ACONST m ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 AT_TAKE_FIRST) fc None m ro) (MS R' F (Z_to_bv 64 TF_HEAD) fc None M' ro)
      /\ rfull R' /\ kept_in KTB1 R R'
      /\ getr R' 2 = Z_to_bv 64 (SP - 80) /\ getr R' 8 = Z_to_bv 64 v /\ getr R' 9 = Z_to_bv 64 (v + 8) /\ getr R' 18 = Z_to_bv 64 (v + 16)
      /\ getr R' 20 = Z_to_bv 64 5 /\ getr R' 21 = Z_to_bv 64 0x7fff8000 /\ getr R' 22 = Z_to_bv 64 (sh (v + 8))
      /\ getr R' 23 = Z_to_bv 64 (sh v) /\ getr R' 24 = Z_to_bv 64 (sh (v + 16))
      /\ munch [(SP - 80, SP)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo' hi', stk asegs m lo' hi' -> stk asegs M' lo' hi')
      /\ rw_cells asegs M' (SP - 80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Proof.
    intros R F fc m ro ra s0 s1 s2 s3 s4 s5 s6 s7 s8 SP v lo P1 P2 P8 P9 P18 P19 P20 P21 P22 P23 P24 P10 HF SP16 SPR V0 V47 VNZ VM8 ST LO MI AC.
    subst ra s0 s1 s2 s3 s4 s5 s6 s7 s8.
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (Hq : SP = 16 * (SP / 16)) by (clear - SP16; Z.div_mod_to_equations; lia).
    set (q := SP / 16) in *. clearbody q.
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 q]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EMd M_MUL (ELit 16) (EVar 33))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs.
      - exact P10.
      - rewrite P2, w_mul by lia. f_equal. lia. }
    assert (HB : bv_unsigned (edenot E (EMd M_MUL (ELit 16) (EVar 33))) = 16 * q) by (subst E; evs; rewrite w_mul, u64_of_Z by lia; reflexivity).
    assert (EV : forall o, estart E (SA (EVar 32) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK : know_ok asegs E m
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWr (SA (EMd M_MUL (ELit 16) (EVar 33)) (-80)) (ELit 80);
         KRange (EVar 33) (2 ^ 41) (2 ^ 43 + 1); KRange (EVar 32) 0 (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite HB; lia
                           | unfold estart, elenZ; cbn [a_base a_off]; rewrite HB; subst E; evs; rewrite u64_of_Z by lia; lia
                           | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    assert (WS : forall a, SP - 80 <= a -> a + 8 <= SP -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    xrun_at (PropExec.mkFP F fc) asegs R AT_TAKE_FIRST m ro HR HK 60%nat [TF_HEAD] (SCR [false; false] [] []) 40%N.
    { split_scs; cbn [sc_denot]; subst E; evs;
        first [rewrite land7_val by lia; rewrite VM8, br_ne by lia; reflexivity | rewrite br_eq by lia; apply Z.eqb_neq; exact VNZ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    split; [exact HF1|].
    assert (KK : kept_in KTB1 R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KTB1 HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    split; [exact KK|].
    rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 18%bv L18. rreg HR' 20%bv L20. rreg HR' 21%bv L21.
    rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24.
    split; [rewrite L2; rewrite ?w_mul, ?w_add, ?w_addm by lia; first [reflexivity | rewrite TablLib.zbv_add; f_equal; lia | f_equal; lia]|].
    split; [exact L8|]. split; [rewrite L9, TablLib.zbv_add; reflexivity|]. split; [rewrite L18, TablLib.zbv_add; reflexivity|].
    split; [rewrite L20; reflexivity|].
    split; [rewrite L21; reflexivity|].
    split; [rewrite L22, TablLib.zbv_add, sh_word by lia; reflexivity|].
    split; [rewrite L23, sh_word by lia; reflexivity|].
    split; [rewrite L24, TablLib.zbv_add, sh_word by lia; reflexivity|].
    split.
    { subst M1. clear - Hlf HB Hq SPR.
      pose proof (munch_mem_denot_sb [(-80, 0)] (EMd M_MUL (ELit 16) (EVar 33)) _ m _ Hlf ltac:(vm_compute; reflexivity)) as MU.
      rewrite HB in MU. cbn [map fst snd] in MU. eapply munch_eqW; [exact MU | repeat f_equal; lia]. }
    split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [intros lo' hi' S; subst M1; apply stk_mem_denot; exact S|].
    subst M1. clear - Hlf HB Hq SPR WS.
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 0%nat|].
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 1%nat|].
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 2%nat|].
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 3%nat|].
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 4%nat|].
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 5%nat|].
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 6%nat|].
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 7%nat|].
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 8%nat|].
    lgcell2 Hlf HB WS 9%nat.
  Qed.

  Lemma tf_pop : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (v b d c t j : Z),
    getr R 8 = Z_to_bv 64 v -> getr R 9 = Z_to_bv 64 (v + 8) -> getr R 18 = Z_to_bv 64 (v + 16) -> getr R 20 = Z_to_bv 64 5 ->
    getr R 21 = Z_to_bv 64 0x7fff8000 -> getr R 22 = Z_to_bv 64 (sh (v + 8)) -> getr R 23 = Z_to_bv 64 (sh v) -> getr R 24 = Z_to_bv 64 (sh (v + 16)) -> rfull R ->
    v mod 8 = 0 -> 0x6e8000 <= v -> (v + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= v) -> v + 24 <= 2 ^ 47 ->
    16 <= b -> b mod 8 = 0 -> b <= d -> d + 4 <= c -> c <= 2 ^ 47 -> d mod 4 = 0 -> (c <= 0x7fff7000 \/ 0x10007fff8000 <= b) ->
    (v + 24 <= b \/ c <= v) ->
    fldA m v 8 b -> fldA m (v + 8) 8 (d + 4) -> fldA m (v + 16) 8 c -> gz m v 24 ->
    fldA m d 4 t -> 0 <= t < 2 ^ 31 ->
    LbB_Kit.shk m d j -> (j = 0 \/ (d mod 8 = 0 /\ 4 <= j < 8)) ->
    wr_at asegs m (v + 8) 8 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 TF_HEAD) fc None m ro) (MS R' F (Z_to_bv 64 AANNOTATE_CC) fc None M' ro)
      /\ rfull R' /\ kept_in KTPOP R R'
      /\ getr R' 1 = Z_to_bv 64 TF_ANN_RET /\ getr R' 10 = Z_to_bv 64 b /\ getr R' 11 = Z_to_bv 64 c
      /\ getr R' 12 = Z_to_bv 64 (d + 4) /\ getr R' 13 = Z_to_bv 64 d /\ getr R' 19 = Z_to_bv 64 t
      /\ getr R' 8 = Z_to_bv 64 v /\ getr R' 9 = Z_to_bv 64 (v + 8) /\ getr R' 18 = Z_to_bv 64 (v + 16) /\ getr R' 20 = Z_to_bv 64 5
      /\ getr R' 21 = Z_to_bv 64 0x7fff8000 /\ getr R' 22 = Z_to_bv 64 (sh (v + 8)) /\ getr R' 23 = Z_to_bv 64 (sh v) /\ getr R' 24 = Z_to_bv 64 (sh (v + 16))
      /\ munch [(v + 8, v + 16)] m M' /\ wmono asegs m M' /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ (mem_inv asegs m -> mem_inv asegs M')
      /\ rw_cells asegs M' (v + 8) [C8 (Z_to_bv 64 d)].
  Proof.
    intros R F fc m ro v b d c t j P8 P9 P18 P20 P21 P22 P23 P24 HF V8 VLO VB VHI B16 B8 BD DC C47 D4 BB DJV F0 F8 F16 GZ FT TR SJ JC WV.
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 d; Z_to_bv 64 j; Z_to_bv 64 t; Z_to_bv 64 b; Z_to_bv 64 c]).
    set (SR0 := srs sr_id [(8%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 16));
                           (20%bv, ELit 5); (21%bv, ELit 2147450880);
                           (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880));
                           (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880));
                           (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) (ELit 2147450880))]).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs;
        [exact P8 | rewrite P9, TablLib.zbv_add; reflexivity | rewrite P18, TablLib.zbv_add; reflexivity | exact P20 | exact P21
        | rewrite P22, TablLib.zbv_add, sh_word by lia; reflexivity | rewrite P23, sh_word by lia; reflexivity
        | rewrite P24, TablLib.zbv_add, sh_word by lia; reflexivity]. }
    assert (EV : forall o, estart E (SA (EVar 32) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ED : forall o, estart E (SA (EVar 33) o) = d + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 0) 8 (EVar 36); KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 33) (ELit 4)); KWord (SA (EVar 32) 16) 8 (EVar 37);
         KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0);
         KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) 2147450880) 1 (ELit 0);
         KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) 1 (ELit 0);
         KWord (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) 2147450880) 1 (EVar 34);
         KWord (SA (EVar 33) 0) 4 (EVar 35);
         KWr (SA (EVar 32) 8) (ELit 8);
         KRange (EVar 32) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 33) 16 (2 ^ 47 - 4); KAlign (EVar 33) 4;
         KRange (EVar 34) 0 7; KRange (EVar 35) 0 (2 ^ 31); KRange (EVar 36) 16 (2 ^ 47); KRange (EVar 37) 0 (2 ^ 47);
         KDisj (SA (EVar 33) 0) (ELit 4) (SA (EVar 32) 8) (ELit 8) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (pt_kword_of_fld E m (SA (EVar 32) 0) (EVar 36) 8%nat v b F0); [lia | rewrite EV; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (pt_kword_of_fld E m (SA (EVar 32) 8) _ 8%nat (v + 8) (d + 4) F8); [lia | rewrite EV; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      apply Forall_cons. { eapply (pt_kword_of_fld E m (SA (EVar 32) 16) (EVar 37) 8%nat (v + 16) c F16); [lia | rewrite EV; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 8)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact (gz_at m v 24 8 GZ ltac:(lia))]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 16)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact (gz_at m v 24 16 GZ ltac:(lia))]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ v); [subst E; evs; reflexivity | lia | pose proof (gz_at m v 24 0 GZ ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X]. }
      apply Forall_cons. { eapply (kshadow _ _ _ d j); [subst E; evs; reflexivity | lia | destruct JC; lia | subst E; evs; reflexivity | exact SJ]. }
      apply Forall_cons. { eapply (pt_kword_of_fld E m (SA (EVar 33) 0) (EVar 35) 4%nat d t FT); [lia | rewrite ED; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WV | rewrite EV; lia | unfold elenZ; rewrite EV; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      do 2 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; split; [lia | exact D4]|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by (destruct JC; lia); destruct JC; lia|].
      do 3 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. unfold elenZ. rewrite ED, EV. subst E; evs. rewrite !u64_of_Z by lia. clear - DJV BD DC; lia. }
    assert (SHV : forall o, 0 <= o <= 16 -> estart E (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit o)) (ELit 3)) 2147450880) = sh (v + o)).
    { intros o Ho. unfold estart. cbn [a_base a_off]. subst E; evs. rewrite TablLib.zbv_add, HWord.w_srl by lia.
      rewrite u64_of_Z by (clear - VLO VHI Ho; Z.div_mod_to_equations; lia). unfold sh. rewrite ASHADOW_BASE_val. change (2 ^ 3) with 8. lia. }
    assert (SHB : 0x7fff8000 <= sh (v + 16) /\ sh (v + 16) + 1 <= 0x10007fff8000) by (clear - VLO VHI; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SD : sc_denot asegs m E (SCDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) 2147450880) (ELit 1) (SA (EVar 32) 8) (ELit 8))).
    { cbn [sc_denot]. unfold flat, elenZ. rewrite (SHV 16 ltac:(lia)), EV. cbn [edenot]. rewrite !u64_of_Z by lia. clear - SHB VB VLO VHI. lia. }
    destruct JC as [J0|(JA & J1)].
    - subst j. xrun_at (PropExec.mkFP F fc) asegs R TF_HEAD m ro HR HK 40%nat [AANNOTATE_CC] (SCR [false; false; false; false; false] [] []) 40%N.
      { split_scs; first [exact SD | cbn [sc_denot]; subst E; evs; rewrite ?TablLib.zbv_add, ?ext4_small by lia;
          first [rewrite br_ne by lia | rewrite br_ltu by lia | rewrite br_lts_small by lia]; bool_lia]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      split; [exact (msteps_full asegs _ _ Hms HF)|].
      assert (KK : kept_in KTPOP R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KTPOP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      split; [exact KK|].
      rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 19%bv L19.
      rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 18%bv L18. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
      rreg HR' 24%bv L24.
      split; [exact L1|]. split; [exact L10|]. split; [exact L11|]. split; [rewrite L12, TablLib.zbv_add; reflexivity|]. split; [exact L13|].
      split; [rewrite L19, ext4_small by lia; reflexivity|].
      split; [exact L8|]. split; [rewrite L9, TablLib.zbv_add; reflexivity|]. split; [rewrite L18, TablLib.zbv_add; reflexivity|]. split; [exact L20|].
      split; [exact L21|]. split; [rewrite L22, TablLib.zbv_add, sh_word by lia; reflexivity|]. split; [rewrite L23, sh_word by lia; reflexivity|].
      split; [rewrite L24, TablLib.zbv_add, sh_word by lia; reflexivity|].
      split.
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        apply Forall_cons; [cbn [e_addr e_width]; rewrite EV; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply Forall_nil]. }
      split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
          | rewrite EV; lia | exact WV | reflexivity | exact I | try subst E; HLib.evs; reflexivity].
    - assert (SL : sc_denot asegs m E (SCBr true BC_LT (EAlu ALU_ADD (EAlu ALU_AND (EVar 33) (ELit 7)) (ELit 3)) (EVar 34))).
      { cbn [sc_denot]. subst E; evs. rewrite land7_val by lia. rewrite JA, TablLib.zbv_add. rewrite br_lts_small by lia. apply Z.ltb_lt. lia. }
      assert (SN : sc_denot asegs m E (SCBr true BC_NE (EVar 34) (ELit 0))).
      { cbn [sc_denot]. subst E; evs. rewrite br_ne by lia. apply negb_true_iff, Z.eqb_neq. lia. }
      xrun_at (PropExec.mkFP F fc) asegs R TF_HEAD m ro HR HK 40%nat [AANNOTATE_CC] (SCR [true; true; false; false; false; false] [] []) 40%N.
      { split_scs; first [exact SD | exact SL | exact SN | cbn [sc_denot]; subst E; evs; rewrite ?TablLib.zbv_add, ?ext4_small by lia;
          first [rewrite br_ltu by lia | rewrite br_lts_small by lia]; bool_lia]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      split; [exact (msteps_full asegs _ _ Hms HF)|].
      assert (KK : kept_in KTPOP R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KTPOP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      split; [exact KK|].
      rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 19%bv L19.
      rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 18%bv L18. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
      rreg HR' 24%bv L24.
      split; [exact L1|]. split; [exact L10|]. split; [exact L11|]. split; [rewrite L12, TablLib.zbv_add; reflexivity|]. split; [exact L13|].
      split; [rewrite L19, ext4_small by lia; reflexivity|].
      split; [exact L8|]. split; [rewrite L9, TablLib.zbv_add; reflexivity|]. split; [rewrite L18, TablLib.zbv_add; reflexivity|]. split; [exact L20|].
      split; [exact L21|]. split; [rewrite L22, TablLib.zbv_add, sh_word by lia; reflexivity|]. split; [rewrite L23, sh_word by lia; reflexivity|].
      split; [rewrite L24, TablLib.zbv_add, sh_word by lia; reflexivity|].
      split.
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        apply Forall_cons; [cbn [e_addr e_width]; rewrite EV; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply Forall_nil]. }
      split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
          | rewrite EV; lia | exact WV | reflexivity | exact I | try subst E; HLib.evs; reflexivity].
  Qed.

  Lemma tf_call : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte),
    rfull R ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 TF_ANN_RET) fc None m ro) (MS R' F (Z_to_bv 64 AT_EXPAND) fc None m ro)
      /\ rfull R' /\ kept_in KTCALL R R'
      /\ getr R' 1 = Z_to_bv 64 TF_XP_RET /\ getr R' 10 = getr R 19 /\ getr R' 11 = getr R 8.
  Proof.
    intros R F fc m ro HF.
    pose (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by apply regs_ok_seed.
    assert (HK : know_ok asegs E m []) by constructor.
    xrun_at (PropExec.mkFP F fc) asegs R TF_ANN_RET m ro HR HK 10%nat [AT_EXPAND] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    lazymatch goal with Hms : CatSim.msteps _ _ (@PropExec.mkst _ ?R1 _ ?mm _) |- _ =>
      change mm with m in Hms; exists R1; split; [exact Hms|]; split; [exact (msteps_full asegs _ _ Hms HF)|] end.
    split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KTCALL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    split; [exact L1|]. split; [rewrite L10; try subst E; evs; reflexivity | rewrite L11; try subst E; evs; reflexivity].
  Qed.

  Lemma tf_back : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte),
    getr R 10 = Z_to_bv 64 1 -> rfull R ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 TF_XP_RET) fc None m ro) (MS R' F (Z_to_bv 64 TF_HEAD) fc None m ro)
      /\ rfull R' /\ kept_in KTBACK R R'.
  Proof.
    intros R F fc m ro P10 HF.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 1)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); try subst E; evs; exact P10).
    assert (HK : know_ok asegs E m []) by constructor.
    xrun_at (PropExec.mkFP F fc) asegs R TF_XP_RET m ro HR HK 4%nat [TF_HEAD; 0xfff6c] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    lazymatch goal with Hms : CatSim.msteps _ _ (@PropExec.mkst _ ?R1 _ ?mm _) |- _ =>
      change mm with m in Hms; exists R1; split; [exact Hms|]; split; [exact (msteps_full asegs _ _ Hms HF)|] end.
    intros rr Hrr; eapply (syms_id_sound R _ _ R' KTBACK HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
  Qed.

  Lemma tf_exit : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) (SP : Z),
    getr R 10 = Z_to_bv 64 0 -> getr R 2 = Z_to_bv 64 (SP - 80) -> rfull R ->
    2 ^ 45 <= SP <= 2 ^ 47 ->
    rw_cells asegs m (SP - 80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv asegs m ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 TF_XP_RET) fc None m ro) (MS R' F (Z_to_bv 64 TF_RET) fc None m ro)
      /\ rfull R' /\ kept_in KTEXIT R R'
      /\ getr R' 1 = ra /\ getr R' 2 = Z_to_bv 64 SP /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\ getr R' 18 = s2 /\ getr R' 19 = s3
      /\ getr R' 20 = s4 /\ getr R' 21 = s5 /\ getr R' 22 = s6 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 10 = getr R 19.
  Proof.
    intros R F fc m ro ra s0 s1 s2 s3 s4 s5 s6 s7 s8 SP P10 P2 HF SPR CS MI.
    pose (E := Eseed R [Z_to_bv 64 (SP - 80); ra; s0; s1; s2; s3; s4; s5; s6; s7; s8]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); try subst E; evs; [exact P10 | exact P2]).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 80) by (try subst E; evs; rewrite u64_of_Z by lia; reflexivity).
    Ltac ktail CSF EP k c :=
      eapply (kword_of_rw_cells asegs _ _ _ _ k c); [exact CSF | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | lia | lia | HLib.evs; reflexivity].
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 0) 8 (EVar 42); KWord (SA (EVar 32) 8) 8 (EVar 41); KWord (SA (EVar 32) 16) 8 (EVar 40);
         KWord (SA (EVar 32) 24) 8 (EVar 39); KWord (SA (EVar 32) 32) 8 (EVar 38); KWord (SA (EVar 32) 40) 8 (EVar 37);
         KWord (SA (EVar 32) 48) 8 (EVar 36); KWord (SA (EVar 32) 56) 8 (EVar 35); KWord (SA (EVar 32) 64) 8 (EVar 34);
         KWord (SA (EVar 32) 72) 8 (EVar 33); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { ktail CS EP 0%nat (C8 s8). }
      apply Forall_cons. { ktail CS EP 8%nat (C8 s7). }
      apply Forall_cons. { ktail CS EP 16%nat (C8 s6). }
      apply Forall_cons. { ktail CS EP 24%nat (C8 s5). }
      apply Forall_cons. { ktail CS EP 32%nat (C8 s4). }
      apply Forall_cons. { ktail CS EP 40%nat (C8 s3). }
      apply Forall_cons. { ktail CS EP 48%nat (C8 s2). }
      apply Forall_cons. { ktail CS EP 56%nat (C8 s1). }
      apply Forall_cons. { ktail CS EP 64%nat (C8 s0). }
      apply Forall_cons. { ktail CS EP 72%nat (C8 ra). }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R TF_XP_RET m ro HR HK 30%nat [TF_RET; TF_HEAD] (SCR [] [] []) 43%N.
    { first [apply Forall_nil | split_scs]. }
    lazymatch goal with Hms : CatSim.msteps _ _ (@PropExec.mkst _ ?R1 _ ?mm _) |- _ =>
      change mm with m in Hms; exists R1; split; [exact Hms|]; split; [exact (msteps_full asegs _ _ Hms HF)|] end.
    split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KTEXIT HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 18%bv L18. rreg HR' 19%bv L19.
    rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24.
    split; [rewrite L1; try subst E; evs; reflexivity|]. split; [rewrite L2; try subst E; evs; rewrite TablLib.zbv_add; f_equal; lia|].
    split; [rewrite L8; try subst E; evs; reflexivity|]. split; [rewrite L9; try subst E; evs; reflexivity|].
    split; [rewrite L18; try subst E; evs; reflexivity|]. split; [rewrite L19; try subst E; evs; reflexivity|].
    split; [rewrite L20; try subst E; evs; reflexivity|]. split; [rewrite L21; try subst E; evs; reflexivity|].
    split; [rewrite L22; try subst E; evs; reflexivity|]. split; [rewrite L23; try subst E; evs; reflexivity|].
    split; [rewrite L24; try subst E; evs; reflexivity|].
    rewrite L10; try subst E; evs; reflexivity.
  Qed.
End TF1.
