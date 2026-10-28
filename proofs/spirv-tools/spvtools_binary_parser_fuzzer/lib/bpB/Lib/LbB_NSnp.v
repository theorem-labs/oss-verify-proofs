(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMState BMem BCells BArr BExec BLFrame BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BakeStackRep BllocRepX RtB_IMemset RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_Conv LbB_Call LbB_DStat LbB_NBr LbB_NMc LbB_NLeaf LbB_NPc1 LbB_NLoops LbB_NPc2 LbB_NPc3 LbB_NSn LbB_NVf LbB_NPfc LbB_NIvf LbB_NVsn LbB_NIvsn.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DPdK LbB_PqK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail SumWalkTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac NumLeaf.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation SEGS := asegs (only parsing).
Local Ltac xms H := first [exact H | apply msteps_bridge; exact H].

Definition A_SNPRINTF_L : Z := 0x15c96c.
Definition SNP_RET_VSN : Z := 0x15c9c8.
Definition SNP_RETPC : Z := 0x15c9f4.
Definition AGLOBAL_LOCALE : Z := 0x6e5b20.
Definition AC_LOCALE_OBJ : Z := 0x6a768.

Definition TDL_BYTES : list Z := [0x20; 0x5b; 0x6e; 0; 0; 0; 0; 0].
Definition tdl_pinned (m : mem) : Prop :=
  forall i, 0 <= i < 8 -> m (Z_to_bv 64 (ATDLOC + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) TDL_BYTES 0)).
Lemma tdl_pinned_pteq : forall m m', tdl_pinned m -> (forall x, ATDLOC <= x < ATDLOC + 8 -> m' (wa x) = m (wa x)) -> tdl_pinned m'.
Proof. intros m m' HT HE i Hi. unfold wa in HE. rewrite (HE (ATDLOC + i)) by lia. exact (HT i Hi). Qed.

Lemma tdl_wr_any : forall M, wr_at asegs M ATDLOC 8.
Proof.
  intros M. unfold ATDLOC. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wview. destruct (M (wa (0x6c5828 + i))) as [b|]; [discriminate|].
  assert (H8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct H8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma ACONST_frame_td : forall W m m',
  ACONST m -> munch ((ATDLOC, ATDLOC + 8) :: W) m m' -> wmono asegs m m' -> Forall aconst_ok W -> ACONST m'.
Proof.
  intros W m m' AC MU WM FW.
  assert (OUT : forall a, aconst_addr a -> ~ (ATDLOC <= a < ATDLOC + 8) -> outside ((ATDLOC, ATDLOC + 8) :: W) a).
  { intros a Ha Hn. cbn. split; [exact Hn|]. clear MU WM AC. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split.
    - intros K. exact (Forall_inv FW a K Ha).
    - apply IH. exact (Forall_inv_tail FW). }
  eapply ACONST_ext_td; [exact AC | | intros a _ HW; apply WM; exact HW |].
  - intros a Ha HC Hn. unfold wa. apply MU. rewrite unsigned_lit by lia. apply OUT; [exact HC | exact Hn].
  - intros a Ha. destruct AC as (_ & _ & (S0 & S1 & SS)). destruct (SS a Ha) as [W0 (b & Hb)].
    unfold mrd in *. unfold wa in *. rewrite MU.
    + rewrite Hb. eauto.
    + rewrite unsigned_lit by (unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia). apply OUT; [unfold aconst_addr; do 16 right; left; exact Ha |].
      unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE, ATDLOC in *. lia.
Qed.

Section Snp.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variable gd : Z.
  Hypothesis Hgd : 0 <= gd < 2 ^ 64.
  Variables (R : bvmap 5 word) (M : mem) (ssp ret v conv lo shi : Z).

  Hypothesis Hra : getr R 1%bv = Z_to_bv 64 ret.
  Hypothesis Hret : ret_ok (Z_to_bv 64 ret).
  Hypothesis Hretr : 0 <= ret < 2 ^ 64.
  Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 ssp.
  Hypothesis Htp : getr R 4%bv = Z_to_bv 64 ATP.
  Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 (ssp + 72).
  Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 24.
  Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 AC_LOCALE_OBJ.
  Hypothesis Ha3 : getr R 13%bv = Z_to_bv 64 (ssp + 96).
  Hypothesis Ha4 : getr R 14%bv = Z_to_bv 64 v.
  Hypothesis Hslo : 2 ^ 33 <= ssp - 4864.
  Hypothesis Hshi : ssp + 100 < 2 ^ 47.
  Hypothesis Hal : ssp mod 16 = 0.
  Hypothesis HD : mdef M (ssp - 4864) 4964.
  Hypothesis Hv : 0 <= v < 2 ^ 64.
  Hypothesis F0 : fld SEGS M (ssp + 96) 1 37.
  Hypothesis F1 : fld SEGS M (ssp + 97) 1 108.
  Hypothesis F2 : fld SEGS M (ssp + 98) 1 conv.
  Hypothesis F3 : fld SEGS M (ssp + 99) 1 0.
  Hypothesis Hconv : conv = 117 \/ conv = 100 \/ conv = 120.
  Hypothesis Hvpos : conv = 100 -> v < 2 ^ 63.
  Hypothesis FCAN : fld SEGS M A_CANARY 8 gd.
  Hypothesis FTD : fld SEGS M ATDLOC 8 AGLOBAL_LOCALE.

  Hypothesis RF : rfull R.
  Hypothesis NI : ninv lo shi M.
  Hypothesis STK : stk asegs M lo ssp.
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LOS : lo + AINTRIN_STACK + 3632 <= ssp.
  Hypothesis SHI : ssp + 164 <= shi.

  Definition snp_post (nc : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
    getr R' 10%bv = Z_to_bv 64 nc /\ 1 <= nc <= 21
    /\ (forall r, In r leaf_kept -> getr R' r = getr R r)
    /\ stores_in (fun a => zwin (ssp - 3568 - AINTRIN_STACK) ssp a \/ zwin ATDLOC (ATDLOC + 8) a \/ zwin (ssp + 72) (ssp + 72 + nc + 1) a) M M'
    /\ tdl_pinned M' /\ rfull R' /\ ninv lo shi M' /\ stk asegs M' lo ssp.

  Lemma stack0_ok_td : stack0_ok (ATDLOC, ATDLOC + 8).
  Proof.
    pose proof aceil_facts as ((AF1 & AF2) & _).
    assert (A0 : 0 <= aceil) by (clear - AF1; lia).
    pose proof (sh_above_image aceil A0) as SA.
    unfold stack0_ok. right. cbn [fst snd]. unfold ATDLOC, AIMG_TOP in *. clear - SA. lia.
  Qed.

  Lemma ninv_td : forall Mx My (l h : Z), ninv lo shi Mx -> stores_in (fun a => zwin l h a \/ zwin ATDLOC (ATDLOC + 8) a) Mx My ->
    aceil <= l -> h <= 2 ^ 63 -> ninv lo shi My.
  Proof.
    intros Mx My l h (MI & AC & S0 & RR) ST Hl Hh. pose proof aceil_facts as ((AF1 & AF2) & _).
    assert (MU : munch [(ATDLOC, ATDLOC + 8); (l, h)] Mx My).
    { eapply (munch_of_stores_in _ [(ATDLOC, ATDLOC + 8); (l, h)]); [exact ST|]. intros x Hx. cbv beta in Hx. cbn [outside fst snd]. unfold zwin in Hx. clear - Hx. lia. }
    pose proof (wmono_of_stores_in _ _ _ ST) as WM.
    split; [| split; [| split]].
    - eapply mem_inv_hi; [exact MI | exact ST | intros a Ha; cbv beta in Ha; unfold zwin, ATDLOC in Ha; clear - Ha Hl AF1; lia].
    - eapply ACONST_frame_td; [exact AC | exact MU | exact WM |]. apply Forall_cons; [apply LbB_DPdK.aconst_ok_hi; clear - Hl AF1; lia | apply Forall_nil].
    - eapply stack0_transport; [exact S0 | exact MU | exact WM |].
      apply Forall_cons; [exact stack0_ok_td |].
      apply Forall_cons; [apply stack0_ok_app; clear - Hl AF1; unfold AHI_LO; lia | apply Forall_nil].
    - eapply relro_clear_hi; [exact RR | exact ST | intros a Ha; cbv beta in Ha; unfold zwin, ATDLOC in Ha; clear - Ha Hl AF1; lia].
  Qed.

  Lemma snprintf_l_A : exists nc R' M',
    BExec.msteps SEGS (@mkst (PropExec.mkFP F fc) R (Z_to_bv 64 A_SNPRINTF_L) M (seg_rom SEGS)) (@mkst (PropExec.mkFP F fc) R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
    /\ snp_post nc R' M'.
  Proof.
    pose proof NI as (ROC & AC & S0 & RRC). pose proof aceil_facts as ((AF1 & AF2) & _).
    pose proof (tdl_wr_any M) as WTD.
    set (E := Eseed R (@nil word)).
    assert (HR : regs_ok E (srs sr_id [(10%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 72)); (13%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 96))]) R) by srs_ok.
    assert (HK : know_ok SEGS E M
      [KWr (SA (EVar 2) (-4864)) (ELit 4964); KRange (EVar 2) (2 ^ 33 + 4864) (2 ^ 47 - 100); KAlign (EVar 2) 16;
       KRange (EVar 4) ATP ATP; KRange (EVar 11) 24 24; KRange (EVar 12) AC_LOCALE_OBJ AC_LOCALE_OBJ;
       KWord (SA (ELit 0) ATDLOC) (N.to_nat 8) (ELit AGLOBAL_LOCALE); KWr (SA (ELit 0) ATDLOC) (ELit 8);
       KImg 0x10000 0x17e000; KImg 0x17e000 0x186000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ ssp (-4864) 4964); [evs; exact Hsp | lia | lia | lia | lia | exact HD].
      - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hal].
      - unfold ATP in *; krv Htp. - krv Ha1. - unfold AC_LOCALE_OBJ in *; krv Ha2.
      - unfold ATDLOC, AGLOBAL_LOCALE in *. kwa FTD.
      - eapply (kwr_of_wr_at asegs _ M ATDLOC 8); [exact WTD | | |]; unfold estart, elenZ; cbn [a_base a_off edenot]; unfold ATDLOC; rewrite ?u64_of_Z by lia; lia.
      - apply kimg_ro. exact ROC. - apply kimg_relro. exact RRC. }
    xrun_at HR HK (PropExec.mkFP F fc) A_SNPRINTF_L (seg_rom SEGS) 100%nat [AVSNPRINTF_STUB; SNP_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK. rename R' into R1. rename HR' into HR1. rename Hms into Hms1. wnorm_in Hms1.
    lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
    assert (ST1 : stores_in (fun a => zwin (ssp - 80) ssp a \/ zwin ATDLOC (ATDLOC + 8) a) M M1) by (subst M1; unfold ATDLOC; stores_tower).
    assert (SV1 : slots SEGS M1 (ssp - 32) [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]) by (subst M1; slots_tower).
    assert (Gv1 : fld SEGS M1 (ssp - 32) 8 v) by (unfold fld; subst M1; gnorm (14%bv : reg); rewrite Ha4; peel).
    assert (Gtd1 : fld SEGS M1 ATDLOC 8 AC_LOCALE_OBJ) by (unfold fld, ATDLOC; subst M1; peel).
    assert (HD1 : mdef M1 (ssp - 4864) 4964) by (eapply stores_in_mdef; [exact ST1 | exact HD]).
    assert (T01 : forall a (n : nat) x, (a + Z.of_nat n <= ssp - 80 \/ ssp <= a) -> 2 ^ 32 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M1 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy; cbv beta; unfold zwin, ATDLOC; lia | lia | lia | exact HF]. }
    regval HR1 (1%bv : reg) SNP_RET_VSN X1. regval HR1 (2%bv : reg) (ssp - 80) X2.
    regval HR1 (10%bv : reg) (ssp - 80 + 152) X10. regval HR1 (11%bv : reg) 24 X11. regval HR1 (12%bv : reg) (ssp - 80 + 176) X12. regval HR1 (13%bv : reg) (ssp - 80 + 48) X13.
    pose proof (T01 (ssp + 96) 1%nat 37 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F0) as F0'. replace (ssp + 96) with (ssp - 80 + 176) in F0' by lia.
    pose proof (T01 (ssp + 97) 1%nat 108 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F1) as F1'. replace (ssp + 97) with (ssp - 80 + 177) in F1' by lia.
    pose proof (T01 (ssp + 98) 1%nat conv ltac:(lia) ltac:(lia) ltac:(cbn; lia) F2) as F2'. replace (ssp + 98) with (ssp - 80 + 178) in F2' by lia.
    pose proof (T01 (ssp + 99) 1%nat 0 ltac:(lia) ltac:(lia) ltac:(cbn; lia) F3) as F3'. replace (ssp + 99) with (ssp - 80 + 179) in F3' by lia.
    replace (ssp - 32) with (ssp - 80 + 48) in Gv1 by lia.
    assert (FCAN1 : fld SEGS M1 A_CANARY 8 gd) by (eapply (fld_via_stores SEGS); [exact ST1 | intros y Hy; cbv beta; unfold zwin, A_CANARY, ASSPGUARD, ATDLOC in *; lia | unfold A_CANARY, ASSPGUARD; lia | unfold A_CANARY, ASSPGUARD; cbn; lia | exact FCAN]).
    assert (HD1' : mdef M1 (ssp - 80 - 4784) 4964) by (replace (ssp - 80 - 4784) with (ssp - 4864) by lia; exact HD1).

    assert (RF1 : rfull R1) by exact (msteps_full asegs _ _ Hms1 RF).
    assert (NI1 : ninv lo shi M1) by (eapply (ninv_td M M1 (ssp - 80) ssp NI ST1); [clear - LOS CEIL; unfold AINTRIN_STACK in *; lia | lia]).
    assert (STK1 : stk asegs M1 lo (ssp - 80)).
    { eapply LbB_PqK.stk_keep; [exact (proj1 (stk_split asegs M lo (ssp - 80) ssp STK ltac:(clear - LOS; unfold AINTRIN_STACK in *; lia)))
        | eapply (munch_of_stores_in _ [(ssp - 80, ssp); (ATDLOC, ATDLOC + 8)]); [exact ST1 | intros x Hx; cbv beta in Hx; cbn [outside fst snd]; unfold zwin in Hx; clear - Hx; lia]
        | exact (wmono_of_stores_in _ _ _ ST1) | clear - CEIL AF1; unfold AIMG_TOP; lia]. }

    pose proof (vsnprintf_icpt H HH F fc gd Hgd R1 M1 (ssp - 80) SNP_RET_VSN v conv lo shi) as LV.
    repeat lazymatch type of LV with (exists _, _) => fail | forall _ : ?T, _ =>
      specialize (LV ltac:(first [eassumption | reflexivity | apply bv_eq; vm_compute; reflexivity | unfold SNP_RET_VSN; lia | mlia
                                  | clear - LOS; unfold AINTRIN_STACK in *; lia | clear - SHI; lia])) end.
    destruct LV as (nc & R2 & M2 & Hms2 & P10 & Pnc & PK & PST & RF2 & NI2 & STK2).

    assert (ST02 : stores_in (fun a => zwin (ssp - 3568 - AINTRIN_STACK) ssp a \/ zwin ATDLOC (ATDLOC + 8) a \/ zwin (ssp + 72) (ssp + 72 + nc + 1) a) M M2).
    { eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact PST | ..]; intros a Ha; cbv beta in *; unfold zwin, AINTRIN_STACK in *; lia. }
    assert (Gtd2 : fld SEGS M2 ATDLOC 8 AC_LOCALE_OBJ) by (eapply (fld_via_stores SEGS); [exact PST | intros y Hy; cbv beta; unfold zwin, ATDLOC, AINTRIN_STACK in *; lia | unfold ATDLOC; lia | unfold ATDLOC; cbn; lia | exact Gtd1]).
    assert (SV2 : slots SEGS M2 (ssp - 32) [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]).
    { eapply slots_agree; [exact SV1 | cbn; lia | lia |]. eapply stores_in_agree; [exact PST|]. intros b Hb. unfold zwin, AINTRIN_STACK in *. cbn in Hb. cbv beta. unfold zwin. lia. }
    assert (Y2' : getr R2 2%bv = Z_to_bv 64 (ssp - 80)) by (rewrite (PK 2%bv) by inl; exact X2).
    assert (Y4 : getr R2 4%bv = Z_to_bv 64 ATP) by (rewrite (PK 4%bv) by inl; regval HR1 (4%bv : reg) ATP X; exact X).
    assert (Y19 : getr R2 19%bv = Z_to_bv 64 (2 ^ 64 - 1)) by (rewrite (PK 19%bv) by inl; regval HR1 (19%bv : reg) (2 ^ 64 - 1) X; exact X).
    set (E2 := Eseed R2 [Z_to_bv 64 nc; Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]).
    assert (HR2 : regs_ok E2 sr_id R2) by (apply regs_ok_seed).
    assert (HK2 : know_ok SEGS E2 M2
      [KWr (SA (EVar 2) (-4784)) (ELit 4964); KRange (EVar 2) (2 ^ 33 + 4784) (2 ^ 47 - 180); KAlign (EVar 2) 16;
       KRange (EVar 4) ATP ATP; KRange (EVar 19) (2 ^ 64 - 1) (2 ^ 64 - 1); KRange (EVar 10) 1 21;
       KWord (SA (ELit 0) ATDLOC) (N.to_nat 8) (ELit AC_LOCALE_OBJ); KWr (SA (ELit 0) ATDLOC) (ELit 8);
       KWord (SA (EVar 2) 40) (N.to_nat 8) (EVar 33); KWord (SA (EVar 2) 32) (N.to_nat 8) (EVar 34); KWord (SA (EVar 2) 24) (N.to_nat 8) (EVar 35);
       KWord (SA (EVar 2) 16) (N.to_nat 8) (EVar 36); KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 37);
       KImg 0x10000 0x17e000; KImg 0x17e000 0x186000]).
    { pose proof NI2 as (MI2 & _ & _ & RR2). repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ (ssp - 80) (-4784) 4964); [evs; exact Y2' | lia | lia | lia | lia | replace (ssp - 80 + -4784) with (ssp - 4864) by lia; eapply stores_in_mdef; [exact ST02 | exact HD]].
      - krv Y2'. - eapply kalign_var; [evs; exact Y2' | lia | lia | mlia].
      - unfold ATP in *; krv Y4. - krv Y19. - krv P10.
      - unfold ATDLOC, AC_LOCALE_OBJ in *. kwa Gtd2.
      - eapply (kwr_of_wr_at asegs _ M2 ATDLOC 8); [exact (tdl_wr_any M2) | | |]; unfold estart, elenZ; cbn [a_base a_off edenot]; unfold ATDLOC; rewrite ?u64_of_Z by lia; lia.
      - kwe (SV2 0%nat ltac:(cbn [length]; lia)) Y2'. - kwe (SV2 1%nat ltac:(cbn [length]; lia)) Y2'. - kwe (SV2 2%nat ltac:(cbn [length]; lia)) Y2'.
      - kwe (SV2 3%nat ltac:(cbn [length]; lia)) Y2'. - kwe (SV2 4%nat ltac:(cbn [length]; lia)) Y2'.
      - apply kimg_ro. exact MI2. - apply kimg_relro. exact RR2. }
    xrun_at HR2 HK2 (PropExec.mkFP F fc) SNP_RET_VSN (seg_rom SEGS) 100%nat [AVSNPRINTF_STUB; SNP_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK2. rename Hms into Hms3. wnorm_in Hms3.
    lazymatch type of Hms3 with msteps _ _ (mkst _ _ ?mm _) => set (M3 := mm) in Hms3 end.
    regval HR' (1%bv : reg) ret T1. regval HR' (10%bv : reg) nc T10.
    pose proof (@ret_at (PropExec.mkFP F fc) SEGS SNP_RETPC R' M3 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) T1 Hret) as Hms4.
    assert (PIN3 : tdl_pinned M3).
    { intros i Hi. subst M3. unfold ATDLOC. rewrite MemSplit.wbytes_inside; [| cbn; rewrite u64_of_Z by lia; lia | cbn; rewrite !u64_of_Z by lia; lia].
      rewrite !u64_of_Z by lia. replace (7100456 + i - 7100456) with i by lia.
      assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
      destruct Hi8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; (f_equal; apply bv_eq; vm_compute; reflexivity). }
    assert (ST3 : stores_in (zwin ATDLOC (ATDLOC + 8)) M2 M3) by (subst M3; unfold ATDLOC; stores_tower).
    exists nc, R', M3. split.
    { eapply BExec.msteps_trans; [xms Hms1|]. eapply BExec.msteps_trans; [xms Hms2|]. eapply BExec.msteps_trans; [xms Hms3 | xms Hms4]. }
    split; [exact T10|]. split; [exact Pnc|]. split.
    { intros r Hr. unfold leaf_kept in Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR' PK HR1|]). destruct Hr. }
    assert (ST03 : stores_in (fun a => zwin (ssp - 3568 - AINTRIN_STACK) ssp a \/ zwin ATDLOC (ATDLOC + 8) a \/ zwin (ssp + 72) (ssp + 72 + nc + 1) a) M M3).
    { eapply (stores_in_join _ _ _ M M2 M3); [exact ST02 | exact ST3 | ..]; intros a Ha; cbv beta in *; unfold zwin, ATDLOC, AINTRIN_STACK in *; lia. }
    split; [exact ST03|].
    split; [exact PIN3|]. split; [exact (msteps_full asegs _ _ Hms3 RF2)|]. split.
    { eapply (ninv_td M2 M3 (ssp - 80) ssp NI2); [eapply stores_in_weaken; [exact ST3 | intros a Ha; right; exact Ha] | clear - LOS CEIL; unfold AINTRIN_STACK in *; lia | lia]. }
    eapply LbB_PqK.stk_keep; [exact STK
      | eapply (munch_of_stores_in _ [(ssp - 3568 - AINTRIN_STACK, ssp); (ATDLOC, ATDLOC + 8); (ssp + 72, ssp + 72 + nc + 1)]); [exact ST03 | intros x Hx; cbv beta in Hx; cbn [outside fst snd]; unfold zwin in Hx; clear - Hx; lia]
      | exact (wmono_of_stores_in _ _ _ ST03) | clear - CEIL AF1; unfold AIMG_TOP; lia].
  Qed.
End Snp.
