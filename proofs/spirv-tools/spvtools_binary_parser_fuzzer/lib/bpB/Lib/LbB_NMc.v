(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMState BMem BCells BArr BExec BLFrame BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BakeStackRep BllocRepX RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_Conv LbB_Call LbB_DStat LbB_Own LbB_NBr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DPdK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatSim StoreOk MemSplit Hoare LibIface SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumLeaf.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wr_at_of_mdef_hi : forall M a n, mdef M a n -> AIMG_TOP <= a -> a + n <= 2 ^ 64 -> wr_at asegs M a n.
Proof.
  intros M a n HD Ha Hn. split; [unfold AIMG_TOP in Ha; lia|]. split; [lia|]. intros i Hi.
  pose proof (proj1 (mdef_defined M a n) HD i Hi) as Di.
  unfold wa. rewrite wview_high by (rewrite unsigned_lit by (unfold AIMG_TOP in Ha; lia); lia).
  destruct (M (Z_to_bv 64 (a + i))) as [b|] eqn:E; [discriminate | contradiction].
Qed.

Lemma stores_in_of_munch2 : forall (l1 h1 l2 h2 : Z) M M',
  munch [(l1, h1); (l2, h2)] M M' -> wmono asegs M M' -> AIMG_TOP <= l1 -> AIMG_TOP <= l2 ->
  stores_in (fun a => zwin l1 h1 a \/ zwin l2 h2 a) M M'.
Proof.
  intros l1 h1 l2 h2 M M' MU WM H1 H2. split.
  - intros a Hn. apply MU. cbn [outside fst snd]. unfold zwin in Hn. lia.
  - intros a Hd. pose proof (bv_unsigned_in_range 64 a) as Ra.
    destruct (Classical_Prop.classic (zwin l1 h1 (bv_unsigned a) \/ zwin l2 h2 (bv_unsigned a))) as [IN | OUT].
    + assert (HI : AIMG_TOP <= bv_unsigned a) by (unfold zwin in IN; lia).
      pose proof (WM a) as W. rewrite !wview_high in W by exact HI. exact (W Hd).
    + rewrite (MU a); [exact Hd|]. cbn [outside fst snd]. unfold zwin in OUT. lia.
Qed.

Section AMc.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma a_memcpy_g : forall (F : bvmap 5 word) (fc : bv 32) (R : bvmap 5 word) (M : mem) (dst src l ret sp lo shi : Z) (bs : list byte),
    rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 48 -> ret mod 2 = 0 ->
    PropExec.getr R 2%bv = Z_to_bv 64 sp ->
    PropExec.getr R 10%bv = Z_to_bv 64 dst -> PropExec.getr R 11%bv = Z_to_bv 64 src -> PropExec.getr R 12%bv = Z_to_bv 64 l ->
    0 <= l <= 2 ^ 40 ->
    PropExec.rdn asegs M (Z_to_bv 64 src) (Z.to_nat l) = Some bs -> mdef M dst l ->
    (dst + l <= src \/ src + l <= dst) ->
    stack0 M lo shi -> lo + 64 <= dst -> dst + l + 64 <= shi ->
    ((lo + 64 <= src /\ src + l + 64 <= shi /\ sp <= src) \/ (l = 0 /\ AIMG_LO + 64 <= src /\ src + 64 <= AIMG_TOP)) ->
    stk asegs M lo sp -> aceil <= lo -> lo <= sp - AINTRIN_STACK -> sp <= dst -> sp mod 16 = 0 ->
    mem_inv asegs M -> ACONST M ->
    exists R' M',
      BExec.msteps asegs (MS R F (Z_to_bv 64 AMEMCPY_STUB) fc None M (seg_rom asegs)) (MS R' F (Z_to_bv 64 ret) fc None M' (seg_rom asegs))
      /\ rfull R' /\ PropExec.getr R' 10%bv = Z_to_bv 64 dst
      /\ (forall r, In r (1%bv :: leaf_kept) -> PropExec.getr R' r = PropExec.getr R r)
      /\ stores_in (fun a => zwin dst (dst + l) a \/ zwin (sp - AINTRIN_STACK) sp a) M M'
      /\ PropExec.rdn asegs M' (Z_to_bv 64 dst) (Z.to_nat l) = Some bs
      /\ mem_inv asegs M' /\ ACONST M' /\ stack0 M' lo shi /\ stk asegs M' lo sp.
  Proof.
    intros F fc R M dst src l ret sp lo shi bs RF Hra Hret Hre Hsp Ha0 Ha1 Ha2 Hl RD HD DJ S0 D1 D2 SRC ST CEIL LOS SPD SP16 MI AC.
    pose proof (stack0_bounds M lo shi S0) as (B1 & B2 & B3). pose proof aceil_facts as ((A1 & A2) & _).
    pose proof (PropExec.rdn_length asegs M _ _ bs RD) as Hlen.
    assert (SB : 2 ^ 16 <= src /\ src + l + 64 <= AAPP_HI /\ (src + l <= lo \/ sp <= src)).
    { destruct SRC as [(S1' & S2' & SPS)|(L0 & I1 & I2)]; [clear - S1' S2' SPS B1 B3 A1; lia | clear - L0 I1 I2 A1 CEIL; unfold AIMG_LO, AIMG_TOP, AAPP_HI in *; lia]. }
    destruct SB as (SB1 & SB2 & SB3).
    assert (BS : bytes_at asegs M src bs).
    { apply (bytes_at_of_rdn asegs M src bs); [clear - SB1; lia | rewrite Hlen; clear - SB2 Hl; unfold AAPP_HI in *; lia | rewrite Hlen; exact RD]. }
    assert (DW : wr_at asegs M dst l).
    { apply wr_at_of_mdef_hi; [exact HD | clear - D1 B1 A1; unfold AIMG_TOP; lia | clear - D2 B3 Hl; unfold AAPP_HI in *; lia]. }
    destruct (rw_cells_of_wr_hi M dst l DW ltac:(clear - D1 B1 A1; unfold AIMG_TOP; lia) ltac:(clear - Hl; lia)) as [junk JK].
    rewrite (MS_full_eq R F _ fc M _ RF).
    pose proof (ah_memcpy_icpt H HH (PropExec.getr R 1) (PropExec.getr R 2) (PropExec.getr R 3) (PropExec.getr R 4) (PropExec.getr R 5)
                  (PropExec.getr R 6) (PropExec.getr R 7) (PropExec.getr R 8) (PropExec.getr R 9) (PropExec.getr R 10)
                  (PropExec.getr R 11) (PropExec.getr R 12) (PropExec.getr R 13) (PropExec.getr R 14) (PropExec.getr R 15)
                  (PropExec.getr R 16) (PropExec.getr R 17) (PropExec.getr R 18) (PropExec.getr R 19) (PropExec.getr R 20)
                  (PropExec.getr R 21) (PropExec.getr R 22) (PropExec.getr R 23) (PropExec.getr R 24) (PropExec.getr R 25)
                  (PropExec.getr R 26) (PropExec.getr R 27) (PropExec.getr R 28) (PropExec.getr R 29) (PropExec.getr R 30)
                  (PropExec.getr R 31) F fc M bs junk lo) as K.
    rewrite Ha0, Ha1, Ha2, Hsp in K.
    assert (SPLO : 0 <= sp) by (clear - LOS A1 CEIL; unfold AINTRIN_STACK in *; lia).
    assert (U1 : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; clear - D1 D2 B1 B3 A1 Hl; unfold AAPP_HI in *; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; clear - SB1 SB2 Hl; unfold AAPP_HI in *; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 l) = l) by (apply unsigned_lit; clear - Hl; lia).
    assert (U4 : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; clear - SPLO SPD D2 B3 Hl; unfold AAPP_HI in *; lia).
    rewrite !U1, !U2, !U3, !U4 in K.
    destruct K as (ms' & RUN & POST).
    - exact BS.
    - exact Hlen.
    - exact JK.
    - clear - DJ. lia.
    - destruct SRC as [(S1' & S2' & SPS)|(L0 & I1 & I2)]; [eapply stack0_accessible; [exact S0 | clear - S1'; lia | clear - Hl; lia | clear - S2'; lia]
        | rewrite L0; apply accessible_nil; clear - I1 I2; unfold AIMG_LO, AIMG_TOP, AAPP_HI in *; lia].
    - eapply stack0_accessible; [exact S0 | clear - D1; lia | clear - Hl; lia | clear - D2; lia].
    - destruct SRC as [(S1' & S2' & SPS)|(L0 & I1 & I2)]; [eapply stack0_shvis; [exact S0 | exact S1' | clear - Hl; lia | exact S2']
        | eapply ACONST_shvis; [exact AC | exact I1 | clear - L0; lia | clear - L0 I2; lia]].
    - eapply stack0_shvis; [exact S0 | exact D1 | clear - Hl; lia | exact D2].
    - exact ST.
    - exact CEIL.
    - exact LOS.
    - exact MI.
    - exact AC.
    - clear - Hl. lia.
    - destruct SRC as [(S1' & S2' & SPS)|(L0 & I1 & I2)]; [eapply stack0_in_app_mem; [exact S0 | clear - S1'; lia | clear - S2'; lia]
        | left; clear - L0 I1 I2; unfold AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia].
    - eapply stack0_in_app_mem; [exact S0 | clear - D1; lia | clear - D2; lia].
    - apply LbB_DPdK.aconst_ok_hi. clear - D1 B1 A1. lia.
    - right. exact SPD.
    - clear - SB3. destruct SB3; [left | right]; assumption.
    - destruct POST as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E' & MU & WM & MI' & ST' & RW' & BS' & AC').
      rewrite Hra, (ret_pc_even ret ltac:(clear - Hret; lia) Hre) in E'. subst ms'.
      rewrite ?U1, ?U2, ?U3, ?U4 in MU. rewrite ?U1, ?U2, ?U3, ?U4 in ST'. rewrite ?U1, ?U2, ?U3, ?U4 in RW'. rewrite ?U1, ?U2, ?U3, ?U4 in BS'.
      rewrite Hsp, Ha0, Ha1, Ha2.
      eexists _, m'. split; [exact RUN|].
      split; [apply rfull_mkR|]. split; [cbn [PropExec.getr mkR]; reflexivity|].
      split.
      { intros r Hr. cbn [In leaf_kept] in Hr.
        repeat (destruct Hr as [<-|Hr]; [cbn [PropExec.getr LbB_Call.getr mkR]; first [reflexivity | symmetry; assumption] |]). destruct Hr. }
      split.
      { apply (stores_in_of_munch2 dst (dst + l) (sp - AINTRIN_STACK) sp M m' MU WM); clear - D1 B1 A1 CEIL LOS; unfold AIMG_TOP, AINTRIN_STACK in *; lia. }
      split.
      { assert (BA : bytes_at asegs m' dst bs) by (pose proof (proj2 (proj1 RW')) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X).
        pose proof (BMem.bytes_at_rdn asegs m' dst bs 0 (Z.to_nat l) BA ltac:(rewrite Hlen; lia)) as RR.
        rewrite Z.add_0_r, skipn_O, <- Hlen, firstn_all in RR. rewrite Hlen in RR.
        rewrite rdn_HL. unfold wa in RR. exact RR. }
      split; [exact MI'|]. split; [exact AC'|]. split; [| exact ST'].
      eapply stack0_transport; [exact S0 | exact MU | exact WM |].
      apply Forall_cons; [apply stack0_ok_app; clear - D1 B1 A1; unfold AHI_LO; lia|].
      apply Forall_cons; [apply stack0_ok_app; clear - CEIL LOS A1; unfold AHI_LO, AINTRIN_STACK in *; lia | apply Forall_nil].
  Qed.

  Lemma a_memcpy : forall (F : bvmap 5 word) (fc : bv 32) (R : bvmap 5 word) (M : mem) (dst src l ret sp lo shi : Z) (bs : list byte),
    rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 48 -> ret mod 2 = 0 ->
    PropExec.getr R 2%bv = Z_to_bv 64 sp ->
    PropExec.getr R 10%bv = Z_to_bv 64 dst -> PropExec.getr R 11%bv = Z_to_bv 64 src -> PropExec.getr R 12%bv = Z_to_bv 64 l ->
    0 <= l <= 2 ^ 40 ->
    PropExec.rdn asegs M (Z_to_bv 64 src) (Z.to_nat l) = Some bs -> mdef M dst l ->
    (dst + l <= src \/ src + l <= dst) ->
    stack0 M lo shi -> lo + 64 <= dst -> dst + l + 64 <= shi -> lo + 64 <= src -> src + l + 64 <= shi ->
    stk asegs M lo sp -> aceil <= lo -> lo <= sp - AINTRIN_STACK -> sp <= dst -> sp <= src -> sp mod 16 = 0 ->
    mem_inv asegs M -> ACONST M ->
    exists R' M',
      BExec.msteps asegs (MS R F (Z_to_bv 64 AMEMCPY_STUB) fc None M (seg_rom asegs)) (MS R' F (Z_to_bv 64 ret) fc None M' (seg_rom asegs))
      /\ rfull R' /\ PropExec.getr R' 10%bv = Z_to_bv 64 dst
      /\ (forall r, In r (1%bv :: leaf_kept) -> PropExec.getr R' r = PropExec.getr R r)
      /\ stores_in (fun a => zwin dst (dst + l) a \/ zwin (sp - AINTRIN_STACK) sp a) M M'
      /\ PropExec.rdn asegs M' (Z_to_bv 64 dst) (Z.to_nat l) = Some bs
      /\ mem_inv asegs M' /\ ACONST M' /\ stack0 M' lo shi /\ stk asegs M' lo sp.
  Proof.
    intros F fc R M dst src l ret sp lo shi bs RF Hra Hret Hre Hsp Ha0 Ha1 Ha2 Hl RD HD DJ S0 D1 D2 S1' S2' ST CEIL LOS SPD SPS SP16 MI AC.
    eapply a_memcpy_g; try eassumption. left. split; [exact S1' | split; [exact S2' | exact SPS]].
  Qed.
End AMc.

Section AMs.
  Context {HCEIL : HeapCeil}.

  Lemma a_memset : forall (F : bvmap 5 word) (fc : bv 32) (R : bvmap 5 word) (M : mem) (dst c n ret sp lo shi : Z),
    rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 48 -> ret mod 2 = 0 ->
    PropExec.getr R 2%bv = Z_to_bv 64 sp ->
    PropExec.getr R 10%bv = Z_to_bv 64 dst -> PropExec.getr R 11%bv = Z_to_bv 64 c -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    0 <= c < 256 -> 0 <= n <= 2 ^ 40 -> mdef M dst n ->
    stack0 M lo shi -> lo + 64 <= dst -> dst + n + 64 <= shi ->
    stk asegs M lo sp -> aceil <= lo -> lo <= sp - AINTRIN_STACK -> sp <= dst ->
    mem_inv asegs M -> ACONST M ->
    exists R' M',
      BExec.msteps asegs (MS R F (Z_to_bv 64 AMEMSET_STUB) fc None M (seg_rom asegs)) (MS R' F (Z_to_bv 64 ret) fc None M' (seg_rom asegs))
      /\ rfull R' /\ PropExec.getr R' 10%bv = Z_to_bv 64 dst
      /\ (forall r, In r (1%bv :: leaf_kept) -> PropExec.getr R' r = PropExec.getr R r)
      /\ stores_in (fun a => zwin dst (dst + n) a \/ zwin (sp - AINTRIN_STACK) sp a) M M'
      /\ PropExec.rdn asegs M' (Z_to_bv 64 dst) (Z.to_nat n) = Some (repeat (b8 c) (Z.to_nat n))
      /\ mem_inv asegs M' /\ ACONST M' /\ stack0 M' lo shi /\ stk asegs M' lo sp.
  Proof.
    intros F fc R M dst c n ret sp lo shi RF Hra Hret Hre Hsp Ha0 Ha1 Ha2 Hc Hn HD S0 D1 D2 ST CEIL LOS SPD MI AC.
    pose proof (stack0_bounds M lo shi S0) as (B1 & B2 & B3). pose proof aceil_facts as ((A1 & A2) & _).
    assert (DW : wr_at asegs M dst n).
    { apply wr_at_of_mdef_hi; [exact HD | clear - D1 B1 A1; unfold AIMG_TOP; lia | clear - D2 B3 Hn; unfold AAPP_HI in *; lia]. }
    destruct (rw_cells_of_wr_hi M dst n DW ltac:(clear - D1 B1 A1; unfold AIMG_TOP; lia) ltac:(clear - Hn; lia)) as [junk JK].
    rewrite (MS_full_eq R F _ fc M _ RF).
    pose proof (memset_icpt_ok (PropExec.getr R 1) (PropExec.getr R 2) (PropExec.getr R 3) (PropExec.getr R 4) (PropExec.getr R 5)
                  (PropExec.getr R 6) (PropExec.getr R 7) (PropExec.getr R 8) (PropExec.getr R 9) (PropExec.getr R 10)
                  (PropExec.getr R 11) (PropExec.getr R 12) (PropExec.getr R 13) (PropExec.getr R 14) (PropExec.getr R 15)
                  (PropExec.getr R 16) (PropExec.getr R 17) (PropExec.getr R 18) (PropExec.getr R 19) (PropExec.getr R 20)
                  (PropExec.getr R 21) (PropExec.getr R 22) (PropExec.getr R 23) (PropExec.getr R 24) (PropExec.getr R 25)
                  (PropExec.getr R 26) (PropExec.getr R 27) (PropExec.getr R 28) (PropExec.getr R 29) (PropExec.getr R 30)
                  (PropExec.getr R 31) F fc M c junk lo) as K.
    rewrite Ha0, Ha1, Ha2, Hsp in K.
    assert (SPLO : 0 <= sp) by (clear - LOS A1 CEIL; unfold AINTRIN_STACK in *; lia).
    assert (U1 : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; clear - D1 D2 B1 B3 A1 Hn; unfold AAPP_HI in *; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; clear - Hn; lia).
    assert (U4 : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; clear - SPLO SPD D2 B3 Hn; unfold AAPP_HI in *; lia).
    rewrite !U1, !U3, !U4 in K.
    destruct K as (ms' & RUN & POST).
    - reflexivity.
    - exact Hc.
    - exact JK.
    - eapply stack0_accessible; [exact S0 | clear - D1; lia | clear - Hn; lia | clear - D2; lia].
    - eapply stack0_shvis; [exact S0 | exact D1 | clear - Hn; lia | exact D2].
    - exact ST.
    - exact CEIL.
    - exact LOS.
    - exact MI.
    - exact AC.
    - clear - Hn. lia.
    - eapply stack0_in_app_mem; [exact S0 | clear - D1; lia | clear - D2; lia].
    - apply LbB_DPdK.aconst_ok_hi. clear - D1 B1 A1. lia.
    - right. exact SPD.
    - destruct POST as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E' & MU & WM & MI' & ST' & RW' & AC').
      rewrite Hra, (ret_pc_even ret ltac:(clear - Hret; lia) Hre) in E'. subst ms'.
      rewrite ?U1, ?U3, ?U4 in MU. rewrite ?U1, ?U3, ?U4 in ST'. rewrite ?U1, ?U3, ?U4 in RW'.
      rewrite Hsp, Ha0, Ha1, Ha2.
      eexists _, m'. split; [exact RUN|].
      split; [apply rfull_mkR|]. split; [cbn [PropExec.getr mkR]; reflexivity|].
      split.
      { intros r Hr. cbn [In leaf_kept] in Hr.
        repeat (destruct Hr as [<-|Hr]; [cbn [PropExec.getr LbB_Call.getr mkR]; first [reflexivity | symmetry; assumption] |]). destruct Hr. }
      split.
      { apply (stores_in_of_munch2 dst (dst + n) (sp - AINTRIN_STACK) sp M m' MU WM); clear - D1 B1 A1 CEIL LOS; unfold AIMG_TOP, AINTRIN_STACK in *; lia. }
      split.
      { set (pb := poison_bytes (Z.to_nat n) c).
        assert (BA : bytes_at asegs m' dst pb) by (pose proof (proj2 (proj1 RW')) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X).
        assert (Hlen : length pb = Z.to_nat n) by (subst pb; unfold poison_bytes; apply repeat_length).
        pose proof (BMem.bytes_at_rdn asegs m' dst _ 0 (Z.to_nat n) BA ltac:(rewrite Hlen; lia)) as RR.
        rewrite Z.add_0_r, skipn_O, <- Hlen, firstn_all in RR. rewrite Hlen in RR.
        rewrite rdn_HL. unfold wa in RR. subst pb. unfold poison_bytes in RR. exact RR. }
      split; [exact MI'|]. split; [exact AC'|]. split; [| exact ST'].
      eapply stack0_transport; [exact S0 | exact MU | exact WM |].
      apply Forall_cons; [apply stack0_ok_app; clear - D1 B1 A1; unfold AHI_LO; lia|].
      apply Forall_cons; [apply stack0_ok_app; clear - CEIL LOS A1; unfold AHI_LO, AINTRIN_STACK in *; lia | apply Forall_nil].
  Qed.
End AMs.
