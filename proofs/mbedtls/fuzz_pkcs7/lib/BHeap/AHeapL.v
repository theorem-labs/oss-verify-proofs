(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rip A_amem_lib A_amemset A_amemcpy A_imemcpy A_bcmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame AW_DepotB AW_DepotTop AW_MallocB
     AW_Poison AW_Refill AW_FakeDefs AW_FakeRep AW_SetShadow AHeapR AHeapB AHeapZ AHeapZW AHeapM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AHeapL () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapB.ext_lo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapB.ext_hi"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HL0"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.cshd"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HM_i"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.htop_i"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.call_postA"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hstkhi_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hflag_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.havol_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hfr_i"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HK_i"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.zcells"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_sfree5"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.csize"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.B.A_rip.rip_post"; "ARUN_1.L.rip0_T"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_rip"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rip"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amem_consts"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amemset_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcsA"; "RocqVerifyHarness.AgentSubmission.B.A_rip.app_range"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amem_apart"; "ARUN_1.L.jstep_T"; "ARUN_1.L.amemset0_T"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.B.A_amem_lib.amemcpy_post"; "ARUN_1.L.amemcpy0_T"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memcpy_i"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemmove"; "RocqVerifyHarness.AgentSubmission.B.A_bcmp.mic_consts"; "RocqVerifyHarness.AgentSubmission.B.A_bcmp.micpt_post"; "ARUN_1.L.bcmp0_T"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memcmp_i"].

Section ARUN_1. Context {hAR : arun}.
Section L.
  Variable STKLO : Z.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).
  Local Notation hst := (hst STKLO).
  Local Notation HM := (HM_i STKLO).
  Local Notation HK := (HK_i STKLO).
  Local Notation hcs := (hcs_i STKLO).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L22706556809.6 L23517510166.6 L23517520224.6 L24505647538.70L29784663004.67L33070409753.3 L37225257050.8 L56085136395.11L57495063529.71L61028776266.96L61028786748.74L61028894324.69L65155801659.3 L67548415054.10L8115031458.67 00000@00L00X00i01601>01Q02502F02S02`02m03503P03]S2sp1s1n2lo1x2HxS1A1s1n1a2INS1A1s1n1x2HxS3hAR1h1A1n3old1NS3hAR1h1A3oldS1s1n2SRS1h1A1n2A83SHI2A01HS3hAR5STKLO2sp1h1s1n2lo2LO2EL3SLO2SRS3hAR1h1A1n3old1NS3hAR1h1A3oldS3hAR1h1A3oldS3hAR1h1A3oldS1s1n2SRS3hAR1h1A1n3SLO2T12T22C12C2S3hAR1h1A3old". (* [comment removed for export] *)
  #[using="Type"] Theorem artA_set_shadow_i : forall (xx : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s' : hst) (LB LF : list blk) (A s n lo : Z) (old : list cell),
      HM s' LB LF m ->
      (xx = 0 \/ xx = 0xf5 \/ xx = 0xf8) ->
      A mod 8 = 0 -> 0 < n -> crange (hcs s') A (8 * n) -> s = shadow_of AL0 A ->
      (forall x, A <= x < A + 8 * n -> (arl_stklo R <= x < htop_i STKLO s') \/ in_block LF x) ->
      rw_cells asegs m (Z.shiftr A 3 + al_sb AL0) old -> Z.of_nat (cells_size old) = n ->
      stk asegs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_setsh R ->
      crange (hcs s') lo (bv_unsigned sp - lo) -> mem_inv asegs m ->
      a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
      evtA asegs AL0 (hcs s')
        (call_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun _ m' =>
            munch [(s, s + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
            /\ rw_cells asegs m' (Z.shiftr A 3 + al_sb AL0) [CB (Z.to_nat n) (repeat (Z_to_bv 8 xx) (Z.to_nat n))]
            /\ stk asegs m' lo (bv_unsigned sp) /\ HM s' LB LF m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if Z.eqb xx 0 then arl_set00 R else if Z.eqb xx 0xf5 then arl_setf5 R else arl_setf8 R))
            fc None m (seg_rom asegs)).
  Proof.
    intros xx ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF A s n lo old
      HM1 XX A8 N CRA ES WRI OLD SZ ST LO SPL CRS MI -> ->.
    pose proof HM1 as [HM0 [XR0 HA0]]. unfold hcs_i, htop_i in *. cbn [hh arl_stklo arl_set00 arl_setf5 arl_setf8 arl_need_setsh R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _ & T1 & T2).
    assert (ESH : Z.shiftr A 3 + al_sb AL0 = s).
    { subst s. unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
    rewrite ESH in OLD |- *.
    assert (A0 : 0x1000 <= A /\ A + 8 * n <= l_stk_hi (h_L h)).   (* [comment removed for export] *)
    { pose proof (hcsA_cases STKLO h A HOK (CRA A ltac:(lia))) as C1. pose proof (hcsA_cases STKLO h (A + 8 * n - 1) HOK (CRA (A + 8 * n - 1) ltac:(lia))) as C2.
      clear - C1 C2 N SLO T1 T2. lia. }
    assert (SR : 0x7fff8000 + 0x200 <= s /\ s + n <= 0x10007fff8000).
    { subst s. unfold shadow_of, AL0. cbn [al_sb]. pose proof (Z.div_mod A 8 ltac:(lia)). clear - A0 A8 N H SHI. lia. }
    dpose HM0 as (_ & _ & (GRO & _) & _). dpose GRO as (_ & _ & PS & _).
    eapply evtA_mono.
    { change (if xx =? 0 then A_SETSH_00 else if xx =? 245 then A_SETSH_F5 else A_SETSH_F8) with (setsh_entry xx).
      eapply (setsh_spec AL0 AL0_img AL0_wf (hcsA h) xx); try eassumption.
      - intros x Hx. right. left. exists (A + 8 * (x - s)). split.
        + apply CRA. clear - Hx N. lia.
        + subst s. unfold shadow_of. pose proof (Z.div_mod A 8 ltac:(lia)). clear - Hx H A8. nia.
      - clear - SR. lia.
      - clear - SR. lia. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU & WM & MI' & RW & PS')).
    unfold call_postA. deexists 16. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. clear - Hx. lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact RW|].
    split. { eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. clear - SR SLO LO EL. unfold kHighMemBeg in *. lia. }
    (* [comment removed for export] *)
    apply (hm_frame_i STKLO (HS STKLO h HOK) LB LF m m' HM1); [| exact WM].
    intros a Ha NW. apply MU. cbn. rewrite wa_unsigned by exact Ha. split; [| exact I]. intros IN. apply NW.
    right. exists (A + 8 * (a - s)). split.
    - unfold htop_i. cbn [hh]. apply WRI. clear - IN N. lia.
    - subst s. unfold shadow_of. cbn [arl_AL R R0]. pose proof (Z.div_mod A 8 ltac:(lia)). clear - IN H A8. nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section G.
    Variables (h : ahst) (LB LF : list blk) (m : mem).
    Hypothesis HOK : hok h.
    Hypothesis HM0 : HMc h LB LF m.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L12165155634.27L12413459064.6 L22047272162.27L3672670125.26 00000F00W00^00eS1h1k1a2XE2R12R25AUMU'S1k1a2XE2sh2Q12Q2S1k3C30S1k3C30". (* [comment removed for export] *)
    #[using="hAR STKLO HOK"] Lemma ext_not_fs : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Pk,$0.Pa,$1.P,(2.$0.R2.(3.Vh,))P,(4.(5.(6.R3.)R2.)(7.R2.(8.R3.)))(9.(4.(5.(:.(;.Vh,))R3.)(7.R3.(<.(:.(;.Vh,))$=.))))")
(* [comment removed for export] *).
    Proof.
      intros k a Hk XE FS. dpose HOK as (EL & AW & VW). dpose AW as (_ & _ & WR & _).
      ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & sh & Hsh & Q1 & Q2)]).
      - pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _).
        destruct (user_in_HB STKLO h HOK (ck_cls k) a ltac:(lia) ltac:(lia)) as [HB _].
        exact (proj1 (lit_apart_hulls STKLO h HOK _ a (fs_tr_in h) eq_refl ltac:(unfold t_hi; cbn; exact FS)) HB).
      - apply (fs_vs_sec STKLO h sh a HOK Hsh FS). clear - XE Q1 Q2. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L65491414238.600000AS1a1k2Ha2E12E22E3". (* [comment removed for export] *)
    #[using="hAR STKLO LF m HOK HM0"] Lemma block_not_fs : forall A n a, In (A, n) LB -> A <= a < A + n -> ~ (l_fs (h_L h) <= a < l_fs (h_L h) + kFakeBytes).
    Proof.
      intros A n a HIn Ha. dpose HOK as (EL & AW & VW). dpose HM0 as ((_ & HLB) & _). rewrite HLB in HIn.
      ddestruct (live_block h A n HIn) as (k & Hk & _ & -> & ->). ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & _).
      apply (ext_not_fs k a Hk). clear - Ha E1 E2 E3. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L58742387072.900000IS3hAR1k2N02E12E22E32E52E6". (* [comment removed for export] *)
    #[using="STKLO h LF m HOK HM0"] Lemma block_bounds : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "PA,$1.Pn,$1.P,(2.(>.$1.$1.)(?.$1.$1.R2.R1.)VLB,)(4.(5.(<.+65?000.+10.)R3.)(4.(5.=R2.)(4.(5.(<.R3.R2.)(10.VhAR,))(11.(5.(<.R3.R2.)+7???7000.)(5.$12.R3.)))))")
(* [comment removed for export] *).
    Proof.
      intros A n HIn. dpose HOK as (EL & AW & VW). dpose HM0 as ((_ & HLB) & _). rewrite HLB in HIn.
      ddestruct (live_block h A n HIn) as (k & Hk & _ & -> & ->). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _). clear - N0 E1 E2 E3 E4 E5 E6. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    #[using="hAR STKLO LB m HOK HM0"] Lemma frame_bounds : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Pfb,$13.P,(2.$13.R1.VLF,)(4.(5.(<.(:.(;.Vh,))+9000.)(14.$1.$1.R2.))(4.(5.(<.(14.$1.$1.R2.)(15.$1.$1.R2.))(<.(:.(;.Vh,))$=.))(5.+40.(15.$1.$1.R2.))))")
(* [comment removed for export] *).
    Proof.
      intros fb Hfb. dpose HOK as (EL & AW & VW). dpose HM0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GF & _).
      ddestruct (frame_ext h LF m fb AW GF Hfb) as (kk & i & _ & _ & _ & F1 & F2 & F3). auto.
    Qed.

    Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L10000056576.12L10000056576.6 L10000070706.13L10000169393.8 L10000251700.9 L10002219826.6 L20620986275.4 L24893144178.40L24897143244.41L26286799648.37L26940570727.5 L41250162518.7 L41370302854.30L45378414102.7 L51538944697.33L53526652478.8 L60601953241.33L61024713171.31L61028794182.35L61028828530.38L61028845559.32L61035084364.39L63368119852.33L9999878029.14 L9999891381.9  00000K00a01J01e02C02Y02f03503D03Q03^03n04@04U04h05@05M05\05k06:06I06X06g07V082S3hAR5STKLO1h1a1c2Rc3LF02HBS3hAR5STKLO1h1a3LF02HBS3hAR5STKLO1h1a1k2Rk3LF02E32E42E63U163E16S3hAR5STKLO1h1a1b2Rb3LF02B1S3hAR5STKLO1h1a1k2Rk3LF02E42E6S3hAR5STKLO1h1a2Z03LF0S1h1c4AUMU2MUS3hAR5STKLO1h1kS3hAR5STKLO1h1kS3hAR5STKLO1hS1h1a1c2Hc2RcS1h1a1c2Rc2D22M2S3hAR5STKLO1h1c2HcS1h1a1i2Rb2Hi4AUMU2AUS3hAR5STKLO1h1c3CSRS3hAR5STKLO1h1c1k3LF02HBS3hAR5STKLO1hS3hAR5STKLO1h1cS3hAR5STKLO1h1cS3hAR5STKLO1h1kS3hAR5STKLO1h1cS3hAR5STKLO1h1kS3hAR5STKLO1h1cS3hAR5STKLO1h1a2sh3Rsh3LF01k2MB2E63sh'2Q12Q22SMS3hAR5STKLO1h1a2Z03LF02S42S5". (* [comment removed for export] *)
    #[using="hAR HOK"] Lemma rzone_lt_stklo : forall a, rzone h a -> a < STKLO.
    Proof.
      intros a Z0. dpose HOK as (EL & AW & VW). pose proof (Lfacts STKLO h HOK) as LF0.
      dpose AW as ([WL _] & WC & WR & (WKF & NDAB & WKS) & WQ & WS & WD & WB & WBIG & WX & WG).
      unfold rzone in Z0. unfold kPrimHullLen, kPaHullLen, kHighMemBeg, kFakeBytes in LF0.
      destruct Z0 as [Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|Z0]]]]]]]]]]]]]]].
      - unfold IMGZ, RT in Z0. cbn in Z0. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 LF0. lia.
      - unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 LF0. lia.
      - unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 LF0. lia.
      - ddestruct Z0 as (b & Hb & Rb). dpose WD as (_ & _ & NBW & _). pose proof (proj1 (Forall_forall _ _) NBW b Hb) as (B0 & B1 & B2). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rb B1 LF0. lia.
      - ddestruct Z0 as (b & Hb & Rb). dpose WD as (_ & _ & _ & _ & _ & SBW & _). pose proof (proj1 (Forall_forall _ _) SBW b Hb) as (B0 & B1 & B2). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rb B1 LF0. lia.
      - ddestruct Z0 as (k & Hk & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rk E4 E6 LF0. lia.
      - ddestruct Z0 as (k & Hk & ST & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _). unfold shad in Rk.
        pose proof (Z.div_mod (ck_user k) 8 ltac:(lia)). pose proof (Z.div_mod (nfix (ck_n k) + 7) 8 ltac:(lia)). unfold nfix in *. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rk E3 E4 E6 LF0 H H0 N0. lia.
      - ddestruct Z0 as (k & Hk & ST & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _). destruct (ext_align STKLO h HOK k Hk) as [U16 E16].
        pose proof (Z.div_mod (ck_user k) 16 ltac:(lia)). pose proof (Z.div_mod (ext_hi k) 16 ltac:(lia)). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rk E4 E6 U16 E16 H H0 LF0. lia.
      - ddestruct Z0 as (c & Hc & Rc). destruct (ri_in_HB STKLO h HOK a ltac:(unfold ri_addr in Rc; unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rc Hc; lia)) as [HB _]. unfold kPrimHullLen in HB. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - HB LF0. lia.
      - ddestruct Z0 as (c & Hc & Rc). destruct (fa_in_HB STKLO h HOK c a Hc Rc) as (HB & _). unfold kPrimHullLen in HB. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - HB LF0. lia.
      - ddestruct Z0 as (c & Hc & Rc). cbn zeta in Rc. pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _).
        unfold shad in Rc. pose proof (Z.div_mod (region_beg (h_L h) c + r_alloc_user (h_reg h c)) 8 ltac:(lia)) as D1.
        pose proof (Z.div_mod (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as D2.
        pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as M2.
        assert (MU : r_alloc_user (h_reg h c) < r_mapped_user (h_reg h c)) by (unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rc D2 M2 AUMU; lia).
        destruct (user_in_HB STKLO h HOK c (region_beg (h_L h) c + r_mapped_user (h_reg h c) - 1) Hc ltac:(unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - MU AUMU; lia)) as [HB _].
        unfold kPrimHullLen in HB. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rc LF0 HB D1 D2 M2 AUMU. lia.
      - ddestruct Z0 as (c & k & Hc & Hk & ->). pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc.
        ddestruct WRc as (_ & AUMU & AUCS & _). pose proof (class_size_range c Hc) as CSR.
        assert (KC : k * class_size c + class_size c <= r_alloc_user (h_reg h c)).
        { rewrite AUCS in Hk |- *. rewrite Z.mul_comm, Z.div_mul in Hk by lia. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Hk CSR. nia. }
        destruct (user_in_HB STKLO h HOK c (chunk_at (h_L h) c k) Hc ltac:(unfold chunk_at; unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Hk KC AUMU CSR; nia)) as [HB _].
        unfold shad, kPrimHullLen in *. pose proof (Z.div_mod (chunk_at (h_L h) c k) 8 ltac:(lia)) as D1. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - LF0 HB D1. lia.
      - ddestruct Z0 as (b & Hb & Rb).
        assert (WBb : wf_batch h b).
        { dpose WQ as ((F1 & _) & (F2 & _) & _). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) F1 b Hb)| exact (proj1 (Forall_forall _ _) F2 b Hb)]. }
        ddestruct WBb as (_ & _ & _ & i & Hi & EB).
        pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & AUCS & _).
        assert (CS24 : class_size 24 = 8192) by reflexivity. unfold kBatchClass in Hi, EB. unfold carved in Hi. rewrite CS24 in Hi.
        pose proof AUCS as AU. unfold carved in AU. rewrite CS24 in AU.
        destruct (user_in_HB STKLO h HOK 24 a ltac:(lia)) as [HB _]; [rewrite EB in Rb; unfold chunk_at in Rb; rewrite CS24 in Rb; unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rb Hi AU AUMU; lia|].
        unfold kPrimHullLen in HB. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - HB LF0. lia.
      - dpose WS as (S1 & _ & S3 & S4 & S5 & _). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 S3 S4 S5 LF0. lia.
      - ddestruct Z0 as (sh & Hsh & Rsh). apply In_nth_error in Hsh. destruct Hsh as [j Hj]. ddestruct (WKS j sh Hj) as (k & Hk & P & MB & MS).
        ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & [(P' & _)|(_ & sh' & Hsh' & Q1 & Q2)]); [rewrite P in P'; discriminate|].
        unfold ext_lo in Q1. rewrite P in Q1. dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh' Hsh') as (_ & SM & _).
        unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rsh MB Q1 Q2 E6 SM LF0. lia.
      - unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 LF0. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00^0?L15045067274.46L16834529516.41L17319242221.2 L1736049313.6  L18933043916.38L22146861958.7 L23335138837.3 L24896883164.53L24897143244.45L24897143244.47L24897143244.54L25158612937.44L25158612937.46L26286799648.48L26940570727.5 L27203392549.6 L27879604548.1 L32712002677.46L3766336558.4  L41372465421.41L4162240340.11 L4263945044.7  L45378414102.7 L51538944697.44L57342294445.14L58811815237.1 L59308548577.5 L59308581345.8 L59308661201.43L59308661588.10L59308728801.9 L59308907477.8 L59309022036.12L59311121633.5 L59311121633.6 L59311121633.9 L59314873579.44L60601953241.44L61028779636.55L61028859718.38L61028860540.45L61035134403.37L63368119852.46L63368316589.56L66758271692.5 L66900479618.4 00000A00U00Z00n01301H01P01_01d01i02802=02B02O02\02o03203C03L03^04404I04^05105X05[05j06G06W07407N07g08M08\09109Q09a09n0:=0:J0:[0:`0;10;@0;L0;US3hAR5STKLO1h1c1kS3hAR5STKLO1h1a1b2RbS1a1kS3hAR5STKLO1h3LF02FBS1h1GS1h1a1c2Rc4AUMU2D22M2S1a1k2RkS3hAR5STKLO1h1kS1h1cS1h1cS3hAR5STKLO1h1kS1h1cS1h1cS3hAR5STKLO1hS1h1a1c2Hc2RcS1h1c4SB163C161H2H0S1kS3hAR5STKLO1h1c1kS1h1a1c1GS3hAR5STKLO1h1c2HcS1h1a2FS4FS4K1G1i2G81ES1h1c1k4SB163C161H2H0S1h1a1i2Rb2Hi4AUMU2AUS3hAR5STKLO1h1c3CSRS1a1k2Rk2E12E22E32E43U163E161H2H02H12H2S1kS1h1a2FS3SHB2NBS3hAR5STKLO1h1a2FS3LF03SHB2HBS3hAR5STKLO1h2E2S1h1a1k2Rk2FS3SHB2E12E22E42E5S1h1a1k2Rk2FS3SHB2E42E52ABS1h1a2sh3Rsh2FS3SHB2SM2T6S3hAR5STKLO1h1a2Z02FS3LF02PB3SHB2S42S5S1h1a2Z02FS3SHBS1h1a2Z02FS2TB3SHB2DBS3hAR5STKLO1h1a2Z02FS3LF02CB3SHBS3hAR5STKLO1h2E2S3hAR5STKLO1hS3hAR5STKLO1h1kS3hAR5STKLO1hS3hAR5STKLO1h1c1GS1h1GS3hAR5STKLO1h1c1GS3hAR5STKLO1h1kS1h1a1c1G2RcS1h1c1k1X". (* [comment removed for export] *)
    #[using="hAR STKLO LB LF m HOK HM0"] Lemma rzone_not_fs_shadow : forall a, rzone h a -> ~ (shad (l_fs (h_L h)) <= a < shad (l_fs (h_L h)) + kFakeBytes / 8).
    Proof.
      intros a Z0 FS. dpose HOK as (EL & AW & VW). pose proof (Lfacts STKLO h HOK) as LF0. dpose VW as (TWF & APT & _).
      dpose AW as ([WL _] & WC & WR & (WKF & NDAB & WKS) & WQ & WS & WD & WB & WBIG & WX & WG).
      assert (HBFS : forall x, l_b6 (h_L h) <= x < l_b6 (h_L h) + kPrimHullLen -> ~ (l_fs (h_L h) <= x < l_fs (h_L h) + kFakeBytes)).
      { intros x HB HF. exact (proj1 (lit_apart_hulls STKLO h HOK _ x (fs_tr_in h) eq_refl ltac:(unfold t_hi; cbn; exact HF)) HB). }
      (* [comment removed for export] *)
      assert (GR : forall G i, G mod 8 = 0 -> 0 <= i -> a = shad G + i -> l_fs (h_L h) <= G + 8 * i < l_fs (h_L h) + kFakeBytes).
      { intros G i G8 I0 E. unfold shad, kFakeBytes in *. ddestruct LF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS4K & _).
        pose proof (Z.div_mod G 8 ltac:(lia)). pose proof (Z.div_mod (l_fs (h_L h)) 4096 ltac:(lia)). change (11571200 / 8) with 1446400 in FS. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - FS E G8 I0 H H0 FS4K. lia. }
      unfold rzone in Z0. unfold kPrimHullLen, kPaHullLen in LF0.
      dpose (Lbands STKLO h HOK) as (TB & CB & FB & PB & DB).
      (* [comment removed for export] *)
      assert (SHB : (0x800c3e00 <= shad (l_fs (h_L h)) /\ shad (l_fs (h_L h)) + kFakeBytes / 8 + 1 <= 0x8fff7000)
                    \/ (0x2008fff7000 <= shad (l_fs (h_L h)) /\ shad (l_fs (h_L h)) + kFakeBytes / 8 <= kHighMemBeg)).
      { unfold shad, kHighMemBeg, kFakeBytes in *. pose proof (Z.div_mod (l_fs (h_L h)) 8 ltac:(lia)). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - LF0 FB H; lia. }
      unfold kHighMemBeg, kFakeBytes in *.
      destruct Z0 as [Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|Z0]]]]]]]]]]]]]]].
      - unfold IMGZ, RT in Z0. cbn in Z0. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 FS SHB. lia.
      - unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 FS SHB TB. lia.
      - unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 FS SHB CB LF0. lia.
      - ddestruct Z0 as (b & Hb & Rb).
        ddestruct (lit_zone STKLO h LB LF m HOK HM0 (node_tr b) a (tr_of_node h b Hb) eq_refl eq_refl ltac:(left; apply in_map; exact Hb)
                   ltac:(intros E; injection E as E1 E2; lia) ltac:(unfold t_hi; cbn; lia)) as (_ & _ & _ & NB). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - NB FS SHB. lia.
      - ddestruct Z0 as (b & Hb & Rb).
        ddestruct (lit_zone STKLO h LB LF m HOK HM0 (store_tr b) a (tr_of_store h b Hb) eq_refl eq_refl ltac:(right; left; apply in_map; exact Hb)
                   ltac:(intros E; injection E as E1 E2; lia) ltac:(unfold t_hi; cbn; lia)) as (_ & _ & _ & NB). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - NB FS SHB. lia.
      - ddestruct Z0 as (k & Hk & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _).
        assert (AB : ext_lo k <= ck_ab k) by (unfold ext_lo, ck_map_beg; destruct (ck_prim k); clear; lia). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rk AB E4 E5 FS SHB. lia.
      - ddestruct Z0 as (k & Hk & ST & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _). destruct (ext_align STKLO h HOK k Hk) as [U16 E16].
        ddestruct (chunk_geom h k AW Hk) as (_ & _ & U8).
        pose proof (GR (ck_user k) (a - shad (ck_user k)) U8 ltac:(unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rk; lia) ltac:(clear; lia)) as X.
        apply (ext_not_fs k (ck_user k + 8 * (a - shad (ck_user k))) Hk); [| exact X].
        pose proof (Z.div_mod (ck_user k) 16 ltac:(lia)). pose proof (Z.div_mod (ext_hi k) 16 ltac:(lia)). pose proof (Z.div_mod (nfix (ck_n k) + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nfix (ck_n k) + 7) 8 ltac:(lia)).
        unfold nfix in *. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rk E1 E2 E3 E4 U16 E16 H H0 H1 H2 N0. lia.
      - ddestruct Z0 as (k & Hk & ST & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rk E1 E2 E4 E5 FS SHB. lia.
      - ddestruct Z0 as (c & Hc & Rc). destruct (ri_in_HB STKLO h HOK a ltac:(unfold ri_addr in Rc; unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rc Hc; lia)) as [HB _]. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - HB FS SHB LF0. lia.
      - ddestruct Z0 as (c & Hc & Rc). destruct (fa_in_HB STKLO h HOK c a Hc Rc) as (HB & _). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - HB FS SHB LF0. lia.
      - ddestruct Z0 as (c & Hc & Rc). cbn zeta in Rc. pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & AUCS & _).
        set (G := region_beg (h_L h) c + r_alloc_user (h_reg h c)) in *.
        assert (G8 : G mod 8 = 0).
        { subst G. unfold region_beg, kRegionSize. rewrite AUCS. pose proof (class_size_mod16 c Hc) as C16. ddestruct LF0 as (_ & _ & _ & SB16 & _).
          pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)). pose proof (Z.div_mod (class_size c) 16 ltac:(lia)).
          replace (l_sb (h_L h) + c * 2 ^ 32 + class_size c * carved h c) with (8 * (l_sb (h_L h) / 2^16 * 2^13 + c * 2^29 + (class_size c / 16) * carved h c * 2)) by (unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - H H0 SB16 C16; lia).
          rewrite Z.mul_comm. apply Z_mod_mult. }
        pose proof (Z.div_mod (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as D2.
        pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as M2.
        pose proof (GR G (a - shad G) G8 ltac:(unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rc; lia) ltac:(clear; lia)) as X.
        destruct (user_in_HB STKLO h HOK c (G + 8 * (a - shad G)) Hc ltac:(subst G; unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rc D2 M2 AUMU; lia)) as [HB _]. exact (HBFS _ HB X).
      - ddestruct Z0 as (c & k & Hc & Hk & ->). pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc.
        ddestruct WRc as (_ & AUMU & AUCS & _). pose proof (class_size_range c Hc) as CSR.
        assert (KC : k * class_size c + class_size c <= r_alloc_user (h_reg h c)).
        { rewrite AUCS in Hk |- *. rewrite Z.mul_comm, Z.div_mul in Hk by lia. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Hk CSR. nia. }
        assert (G8 : chunk_at (h_L h) c k mod 8 = 0).
        { unfold chunk_at, region_beg, kRegionSize. pose proof (class_size_mod16 c Hc) as C16. ddestruct LF0 as (_ & _ & _ & SB16 & _).
          pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)). pose proof (Z.div_mod (class_size c) 16 ltac:(lia)).
          replace (l_sb (h_L h) + c * 2 ^ 32 + k * class_size c) with (8 * (l_sb (h_L h) / 2^16 * 2^13 + c * 2^29 + k * (class_size c / 16) * 2)) by (unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - H H0 SB16 C16; lia).
          rewrite Z.mul_comm. apply Z_mod_mult. }
        pose proof (GR (chunk_at (h_L h) c k) 0 G8 ltac:(lia) ltac:(lia)) as X.
        destruct (user_in_HB STKLO h HOK c (chunk_at (h_L h) c k) Hc ltac:(unfold chunk_at; unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Hk KC AUMU CSR; nia)) as [HB _].
        apply (HBFS _ HB). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - X. lia.
      - ddestruct Z0 as (b & Hb & Rb).
        assert (WBb : wf_batch h b).
        { dpose WQ as ((F1 & _) & (F2 & _) & _). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) F1 b Hb)| exact (proj1 (Forall_forall _ _) F2 b Hb)]. }
        ddestruct WBb as (_ & _ & _ & i & Hi & EB).
        pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & AUCS & _).
        assert (CS24 : class_size 24 = 8192) by reflexivity. unfold kBatchClass in Hi, EB. unfold carved in Hi. rewrite CS24 in Hi.
        pose proof AUCS as AU. unfold carved in AU. rewrite CS24 in AU.
        destruct (user_in_HB STKLO h HOK 24 a ltac:(lia)) as [HB _]; [rewrite EB in Rb; unfold chunk_at in Rb; rewrite CS24 in Rb; unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rb Hi AU AUMU; lia|].
        unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - HB FS SHB LF0. lia.
      - dpose WS as (S1 & _ & S3 & S4 & S5 & _). unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 S3 S4 S5 FS SHB PB LF0. lia.
      - ddestruct Z0 as (sh & Hsh & Rsh). dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh Hsh) as (_ & SM & _).
        pose proof (tr_wf' STKLO h _ HOK (tr_of_sec h sh Hsh)) as (T0 & T1 & T2 & T3 & T4 & T5 & T6).
        specialize (T6 eq_refl). unfold t_hi in T6. cbn [t_lo t_len sec_tr] in T6. unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Rsh SM T6 FS SHB. lia.
      - unfold kHighMemBeg, kFakeBytes, kPrimHullLen, kPaHullLen in *; clear - Z0 FS SHB DB. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    #[using="Type"] Lemma presA_intro : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Pm',P,(16.&40.)(17.(16.&8.))PSP,$1.P,(18.$19.Vm,R2.)P,Pa,$1.P,(4.(5.=R1.)(7.R1.(1:.+2.+40.)))P,(1;.(1<.VhAR,)(1=.$13.VLB,(1>.VLF,))R4.R2.)(1?.(17.(16.&8.))A1.R6.(20.R3.)A1.Vm,(20.R3.))P,Pc,$1.P,(21.VR,VLB,VLF,VSTKLO,(22.(;.Vh,))R1.)P,(4.(5.=(23.$24.R2.))(7.(23.$24.R2.)(1:.+2.+40.)))(1?.(17.(16.&8.))A1.R7.(20.(23.$24.R3.))A1.Vm,(20.(23.$24.R3.)))(25.$19.VR,VLB,VLF,R4.VSTKLO,(22.(;.Vh,))(26.$27.)Vm,R5.)")
(* [comment removed for export] *).
    Proof.
      intros m' SP WM H1 H2. split.
      - intros a Ha Hc _. split; [exact (H1 a Ha Hc)| apply WM].
      - intros c Hc Hr. split; [exact (H2 c Hc Hr)| apply WM].
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma cshd_cases : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Pc,$1.P,(21.VR,VLB,VLF,VSTKLO,(22.(;.Vh,))R1.)(11.(4.(5.VSTKLO,R2.)(7.R2.(22.(;.Vh,))))(11.(28.$1.LA,$1.(28.$1.Ln,$1.(4.(2.(>.$1.$1.)(?.$1.$1.R2.R1.)VLB,)(4.(5.R2.R4.)(7.R4.(<.R2.R1.))))))(11.(28.$13.Lfb,$13.(4.(2.$13.R1.VLF,)(4.(5.(14.$1.$1.R1.)R3.)(7.R3.(<.(14.$1.$1.R1.)(15.$1.$1.R1.))))))(4.(5.+?:360.R2.)(7.R2.+65=:;0.)))))")
(* [comment removed for export] *).
    Proof.
      intros c [S|[(b & Hb & Rb)|[(b & Hb & Rb)|[C _]]]].
      - left. exact S.
      - right; left. destruct b as [A n]. dexists A, n. auto.
      - right; right; left. exists b. auto.
      - right; right; right. cbn [arl_L R R0 hl_data_lo hl_data_hi HL0] in C. exact C.
    Qed.
  End G.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L32390681409.8L64976844748.800000800>S2FB1n1lS2FB1n". (* [comment removed for export] *)
  #[using="Type"] Lemma fdata_sub : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "PLF0,(29.$13.)PB,$1.Pj,$1.P,(2.(>.$1.$1.)(?.$1.$1.R2.R1.)(1>.R3.))(28.$13.Lfb,$13.(11.(4.(2.$13.R1.R5.)(4.(5.(14.$1.$1.R1.)R4.)(5.(<.R4.R3.)(<.(14.$1.$1.R1.)(15.$1.$1.R1.)))))(4.(2.$13.R1.R5.)(7.(15.$1.$1.R1.)+28.))))")
(* [comment removed for export] *).
  Proof.
    induction LF0 as [|[FB n] r IH]; cbn; intros B j HB; [destruct HB|].
    destruct HB as [E|[E|HB]].
    - injection E as <- <-. exists (FB, n). cbn. destruct (Z_lt_le_dec n 40); [right; auto| left]. split; [auto|]. lia.
    - injection E as <- <-. exists (FB, n). cbn. destruct (Z_lt_le_dec n 40); [right; auto| left]. split; [auto|]. lia.
    - ddestruct (IH B j HB) as (fb & [(H1 & H2 & H3)|(H1 & H2)]); exists fb; [left| right]; auto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma cells_bytes_zcells : forall n, cells_bytes (zcells n) = repeat (Z_to_bv 8 0) n /\ cells_wf (zcells n).
  Proof. induction n as [|n [IH1 IH2]]; cbn; [auto|]. rewrite IH1. auto. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0160@L10242787511.6  L14852739058.10 L15632256259.11 L15650887376.2  L1710473495.3   L17968754837.14 L18933043916.127L19933652353.0  L23057438132.5  L24474518484.10 L24564478866.2  L26048066876.1  L26271394959.7  L31059338132.11 L31914370620.5  L34990682663.14 L35478579995.4  L3668098591.11  L36904195316.6  L37147847652.6  L37490299427.2  L37490563635.10 L37494509971.7  L37496662420.9  L38645389814.11 L38749923093.2  L38749923093.5  L38950042235.12 L39522088248.11 L40102332687.0  L41013457360.12 L41015210570.7  L44228106536.8  L46500954936.7  L50804956811.12 L5367345375.6   L53724635892.128L53724635892.141L53724636023.142L53737382384.126L5425838070.13  L55588686165.0  L57614628895.0  L59308730611.8  L59309007462.11 L59309007462.13 L61021639585.9  L61021741316.7  L61024664913.98 L61028759382.139L61028940993.139L61030858065.138L63368119078.139L63374621462.140L64508735719.4  L66011003635.11 L66966394253.4  L67149866062.3  L7290892034.11  L8799750698.21  L8800010810.20  L8800126135.24  L8804186758.23  L8804221322.26  L8806201866.18  L8806251018.12  L8806271151.29  L8895812889.1   L8899412545.5   L9008531763.6   00000E00c01:01?01E01F01a01b01n02=02B02E02W03603G03H03U03l04=04R04W05305I05i05j05o06B06C06T06U06V07007E07]07^08408O09209U0:00:10:20:30:J0:i0;L0;d0<70<S0=30=T0>50>X0?;0?L0?]0?j0@50@F0A70Ah0Bg0Cn0E10Ee0FD0GS0GV0Gj0H@S3hAR5STKLO1h3FLO3LF0S5STKLO2sp1h2lo2LO3SPT2T21x2HxS3hAR5STKLO1h3LF02DB2DIS1c1CS1L2FSFS3hAR1k2sp2LF3LFL2SP1L2FS1rSS1r1B1j2BR1XS1k3FSZ1r3R641cS1k1KS1rS1k1h1r2R12R21c2RCS1k1h4FS4K3FSZ1r2R12R23R641H2H0S2sp1h3SPT3SHI2T2FS2kk2E12E22E4S3hAR5STKLO1h3LF02FB2CBS1k1h3FSZ1r2R12R2S3hAR5STKLO1h3LF03FHIS1c1CS3hAR5STKLO1h2EL3SLO3SHI1c1SS3hAR1c1A1n2RA3BB13BB3S3hAR5STKLO1h3LF01c2fb3Rfb2G12G2FS1h1XS3hAR5STKLO1h3LF01XFS3hAR5STKLO1h3LF0SFS3hAR5STKLO1h2lo2LO2EL3SLOS1k1h1r2R12R22kk1X2RBS3hAR5STKLO1k1h3LF01r2R2FS3hAR5STKLO1h3LF01r2R1S3hAR1k2sp2LF3LFL2SP1L2FS1rS3hAR5STKLO1k2sp2LF3LFL2SP1L2FS1r1cS3hAR5STKLO1k2sp2LF3LFL2SP1L2FS1r1cS3hAR1k2sp2LF3LFL2SP1L2FS1rFSSS1k1r1c2B'2j'3Rfb2RC2APS3hAR5STKLO1k1h3LF01r2R11c1C2RCS3hAR5STKLO1k1h3SLO3LF01r2R21c1S2RCS1k1r1B1j2B'2j'2F12F22APS1k1r1B1j2fb3F402G3S3hAR5STKLO1k2sp1h2LF3LFL2SPS3hAR5STKLO1k2sp1h2LF3LFL2SP1r1cS3hAR5STKLO1k2sp2LF3LFL2SP1L2FS1rS3hAR5STKLO1k2sp2LF3LFL2SP1L2FS1rS3hAR5STKLO1k2sp1h2LF3LFL2SP1L2FS1rS3hAR5STKLO1k2sp2LF3LFL2SP1L2FS1r1cS3hAR5STKLO1h3LF0S3hAR5STKLO1h3LF0S5STKLO1h1c1SS2sp2lo3SPLS3hAR5STKLO1h3LF0S3hAR5STKLO1k2sp1h2lo2SP2LO3SPL3LF01r2R24SHD11a1SS3hAR5STKLO1k2sp1h2lo2SP2LO3SLO3LF01r2R14SHD11a1CS3hAR5STKLO1k2sp1h2lo2SP2LO3SLO3LF02FB1r2R12R24SHD11c2C03IMP2NRS3hAR5STKLO1k2sp1h2lo2SP2LO3LF01r2R12R24SHD24SHD31x2Y12Y22Y33NFS2D83M8'S3hAR5STKLO1k2sp1h2lo2SP2LO3SLO3LF02FB1r2R12R24SHD11a1B1j2Rb2NF3BB3S5STKLO1k2sp1h2lo2SP2LO1r2R12R24SHD24SHD31a2Z12Z22Z3S1k2sp2lo2SP1L2FS1r1a2fb3F402G3S3hAR5STKLO1k2sp1h2lo2SP2LO3SLO3LF02FB1r2R12R24SHD11a1b2Rb2B'2j'2F12F22G12G22APS1hS3hAR5STKLO1h2FS3LF0S3hAR5STKLO1h3LF01r2R1". (* [comment removed for export] *)
  #[using="Type"] Theorem art_smalloc_i : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Pk,$1.Pra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))Ps',(2;.VhAR,VSTKLO,)PLB,(29.$13.)PLF,(29.$13.)Psz,$1.Plo,$1.P,(2<.VhAR,VSTKLO,R5.R4.R3.R6.)P,(2=.(2>.$13.R4.)#200.)P,(4.(5.=R2:.)(5.R2:.+5.))P,(4.(7.=R5.)(5.R5.(2?.+40.(1:.+2.R2;.))))P,(30.$19.R:.R5.(31.&40.R2:.))P,(5.(32.VR,)R6.)P,(5.R7.(33.(31.&40.R2<.)(34.VR,)))P,(5.(31.&40.R2=.)(35.VhAR,VSTKLO,R<.))P,(36.$19.R>.)P,(1?.(16.&40.)R2=.(37.&40.(38.VR,)))P,(1?.(16.&40.)R28.(37.&40.R<.))(39.$19.$24.(3:.VhAR,VSTKLO,R10.)(3;.$19.R32.R31.R30.R2?.R2;.R2:.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R13.R12.Lr,(16.&40.)Lm',P,(16.&40.)(17.(16.&8.))(4.(36.$19.R1.)(4.(30.$19.R1.R>.(31.&40.R33.))(4.(18.$19.R13.R1.)(4.(25.$19.VR,R11.R10.(31.&40.R33.)(32.VR,)(3<.VhAR,VSTKLO,R12.)(26.$27.)R13.R1.)(28.(2;.VhAR,VSTKLO,)Ls'',(2;.VhAR,VSTKLO,)(4.(1?.P,$1.Sp(3:.VhAR,VSTKLO,R1.)(3:.VhAR,VSTKLO,R13.))(4.(1?.$1.(35.VhAR,VSTKLO,R1.)(35.VhAR,VSTKLO,R13.))(4.(1?.$1.(3<.VhAR,VSTKLO,R1.)(3<.VhAR,VSTKLO,R13.))(4.(1?.$1.(3=.VhAR,VSTKLO,R1.)(3=.VhAR,VSTKLO,R13.))(4.(1?.$1.(3>.VhAR,VSTKLO,R1.)(3>.VhAR,VSTKLO,R13.))(4.(1?.$1.(3?.VhAR,VSTKLO,R1.)(3?.VhAR,VSTKLO,R13.))(4.Pmo,$40.(41.(42.VhAR,VSTKLO,R2.R1.)(42.VhAR,VSTKLO,R14.R1.))(28.$1.LFB,$1.(28.(29.(16.&8.))Ljunk,(29.(16.&8.))(4.(1?.(16.&40.)R5.(37.&40.R2.))(4.(1?.$1.(43.R2.+40.)=)(4.(44.VR,R14.R13.R2.(2?.+40.(1:.+2.R38.)))(4.(2<.VhAR,VSTKLO,R3.R14.(45.(>.$1.$1.)(?.$1.$1.R2.(2?.+40.(1:.+2.R38.)))R13.)R4.)(4.(46.$19.R4.R2.(45.$47.(48.(49.(2?.+40.(1:.+2.R38.)))R1.)(26.$47.)))(46.$19.R4.(<.(4:.R2.+3.)(4;.$24.))(4<.(49.(2?.+8.(1:.+2.R38.)))))))))))))))))))))))))(4=.(4>.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(37.&40.(4?.VR,R33.))R12.(50.(16.&40.))R11.(51.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros k ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF sz lo
      HM1 LFL K SZ ST LO SPL SPT MI -> ->.
    pose proof HM1 as [HM0 [XR0 HA0]]. unfold hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i in *. cbn [hh arl_stklo arl_smalloc arl_tp arl_need_smalloc R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _ & T1 & T2). pose proof (Lfacts STKLO h HOK) as LF0.
    dpose (Lbands STKLO h HOK) as (TB & CB & FB & PB & DB). pose proof (Limg STKLO h HOK) as [TI DI].
    dpose VW as (TWF & APT & _).
    dpose HM0 as (HP & GM & (GRO & GRW) & GT & GD & GC & GR & GQ & GS & GF & GI & GE).
    dpose GM as (SHLO & SHHI & STKW & TW & CTXW & FSW). unfold kHighMemBeg, kPrimHullLen, kPaHullLen, kFakeBytes in *.
    dpose GRO as (_ & _ & PS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SMS & _ & T48 & _).
    set (SP := bv_unsigned sp) in *. assert (ESP : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
    set (L := h_L h) in *. set (FS := l_fs L) in *.
    pose proof (fsk_sizes k ltac:(clear - K; lia)) as FSZ.
    (* [comment removed for export] *)
    assert (CTXFS : l_ctx L + 0x10000 <= FS \/ FS + kFakeBytes <= l_ctx L).
    { destruct (APT _ _ (tr_of_ctx h) (fs_tr_in h)) as [E|X]; [exfalso; injection E; unfold kFakeBytes; clear - LF0; subst L; lia|].
      unfold t_hi in X. cbn [t_lo t_len] in X. subst L FS. clear - X LF0. lia. }
    assert (DTFS : l_dtls L + 4096 <= FS \/ FS + kFakeBytes <= l_dtls L).
    { destruct (APT _ _ (tr_of_dtls h) (fs_tr_in h)) as [E|X]; [exfalso; injection E; unfold kFakeBytes; clear; lia|].
      unfold t_hi in X. cbn [t_lo t_len] in X. subst L FS. clear - X. lia. }
    eapply evtA_mono.
    { eapply (fake_smalloc AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl k
                ra gp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                SP FS (l_dtls L) (l_T L) (l_ctx L) lo LF F fc m K GF LFL); try eassumption.
      all: try (subst FS L; unfold kHighMemBeg, kFakeBytes; clear - LF0 TB CB FB PB DB TI DI; lia).
      - (* [comment removed for export] *) subst FS. eapply (wr_at_sub m (l_fs L) kFakeBytes 36864); [exact FSW| clear; lia| clear; lia| unfold kFakeBytes; clear; lia].
      - (* [comment removed for export] *)
        rewrite shd_eq by (subst FS L; clear - LF0; lia).
        destruct FB as [FLO|FHI].
        + replace (2147450880 + (FS + 36864) / 8) with (0x7fff7000 + (2147450880 + (FS + 36864) / 8 - 0x7fff7000)) by (clear; lia).
          eapply wr_at_sub; [exact SHLO| | clear; lia|]; subst FS L; unfold kHighMemBeg, kFakeBytes in LF0; pose proof (Z.div_mod (l_fs (h_L h) + 36864) 8 ltac:(lia)); clear - LF0 FLO H; lia.
        + replace (2147450880 + (FS + 36864) / 8) with (0x2008fff7000 + (2147450880 + (FS + 36864) / 8 - 0x2008fff7000)) by (clear; lia).
          eapply wr_at_sub; [exact SHHI| | clear; lia|]; subst FS L; unfold kHighMemBeg, kFakeBytes in LF0; pose proof (Z.div_mod (l_fs (h_L h) + 36864) 8 ltac:(lia)); clear - LF0 FHI H; lia.
      - intros x Hx. left. apply (crange_dtls AL0 h). exact Hx.
      - intros x Hx. left. apply (crange_ctx AL0 h). ddestruct LF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). subst L. rewrite CL. exact Hx.
      - intros x Hx. left. apply (crange_T AL0 h). exact Hx.
      - intros x Hx. left. apply (vcs_of_tr AL0 h _ x (fs_tr_in h)); [reflexivity|]. unfold t_hi. cbn. subst FS L. exact Hx.
      - subst SP L. clear - LO SLO EL. lia.
      - subst SP. clear - SPL. lia.
      - subst SP L. clear - SPT T2 SHI. lia.
      - intros x Hx. apply (hcsA_stack STKLO h HOK). subst SP L. clear - Hx LO SPT T2 EL. lia. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (x5 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & m' & r & -> & WM & MI' & ST' & SMS' & PS' & junk & R1 & R2 & R64 & RAP & MU & GF' & RWJ & RWS)).
    (* [comment removed for export] *)
    assert (FB8 : 8 * 2^k = fsk_bytes k / 8 /\ fsk_bytes k = 64 * 2^k) by (clear - FSZ; tauto). destruct FB8 as [FB8 FB64].
    assert (SHDR : shd r = shad r /\ shad FS <= shd r /\ shd r + fsk_bytes k / 8 <= shad FS + kFakeBytes / 8).
    { rewrite shd_eq by (subst FS L; clear - R1 LF0; lia). unfold shad. ddestruct LF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS4K & _).
      pose proof (Z.div_mod r 64 ltac:(lia)). pose proof (Z.div_mod (l_fs L) 4096 ltac:(lia)). pose proof (Z.div_mod (fsk_bytes k) 64 ltac:(lia)).
      subst FS L. unfold kFakeBytes in *. clear - R1 R2 R64 H H0 H1 FS4K FSZ. split; [reflexivity|]. lia. }
    ddestruct SHDR as (SHD1 & SHD2 & SHD3).
    assert (OUTZ : forall a, rzone h a -> outside [(lo, SP); (FS, FS + 36864); (r, r + fsk_bytes k); (shd r, shd r + fsk_bytes k / 8)] a).
    { intros a Za. cbn. pose proof (rzone_lt_stklo h HOK a Za) as Z1. pose proof (rzone_not_fs STKLO h HOK a Za) as Z2.
      pose proof (rzone_not_fs_shadow h LB LF m HOK HM0 a Za) as Z3. subst FS L. unfold kFakeBytes in *. clear - Z1 Z2 Z3 LO EL R1 R2 SHD1 SHD2 SHD3. lia. }
    assert (AG : zagree (rzone h) m m') by (intros x Zx; apply MU; apply OUTZ; exact Zx).
    assert (HM' : HMc h LB ((r, 64 * 2^k) :: LF) m').
    { eapply HMc_zframe; [exact HOK| exact WM| exact AG| exact HM0|]. unfold hm_fake. rewrite <- FB64. exact GF'. }
    (* [comment removed for export] *)
    assert (HA' : hm_absent h m').
    { apply (hm_absent_agree h m m' HA0). intros x Zx. apply MU. cbn.
      dpose (habs_zone_out STKLO h (bv_unsigned x) HOK Zx) as (Y1 & Y2 & Y3).
      assert (NFS : ~ (l_fs (h_L h) <= bv_unsigned x < l_fs (h_L h) + kFakeBytes)).
      { intros X. apply (habs_zone_tr h (bv_unsigned x) _ Zx (fs_tr_in h)). unfold t_hi. cbn [t_lo t_len]. exact X. }
      pose proof (Z.div_mod (l_fs (h_L h)) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (l_fs (h_L h)) 8 ltac:(lia)) as M8'.
      pose proof aceil_lt47 as A47.
      subst FS L. unfold kFakeBytes, kHighMemBeg, shad in *. change (11571200 / 8) with 1446400 in *.
      clear - Y1 Y2 Y3 NFS LO R1 R2 SHD1 SHD2 SHD3 LF0 A47 D8 M8'. lia. }
    unfold call_postA. dexists x5, t1, t2, (Z_to_bv 64 r), x11, x12, x13, x14, x15, x16, x17, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact WM|].
    split.
    { (* [comment removed for export] *)
      apply (presA_intro h LB LF m m' SP WM).
      - intros a Ha CA. apply MU. rewrite wa_unsigned by exact Ha. cbn.
        destruct CA as [S|[C|(b & Hb & Rb)]].
        + subst FS L. unfold kFakeBytes in *. clear - S Ha R1 R2 LF0 LO EL SPL SHD1 SHD2 SHD3 FB. unfold shad in *. lia.
        + cbn [hl_data_lo hl_data_hi hl_static HL0] in C. subst FS L. unfold kHighMemBeg, kFakeBytes in *. clear - C R1 R2 LF0 LO EL SLO SHD1 SHD2 SHD3 FB. unfold shad in *. lia.
        + apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
          * destruct b as [B j]. cbn [fst snd] in Rb. pose proof (block_not_fs h LB LF m HOK HM0 B j a Hb Rb) as NF. dpose (block_bounds h LB LF m HOK HM0 B j Hb) as (BB1 & BB2 & BB3).
            subst FS L. unfold kHighMemBeg, kFakeBytes in *. clear - NF BB1 BB2 BB3 Rb R1 R2 LO EL SLO SHD1 SHD2 SHD3 FB LF0. unfold shad in *. lia.
          * ddestruct (fdata_sub LF (fst b) (snd b) ltac:(destruct b; exact Hb)) as (fb & [(Hfb & F1 & F2)|(Hfb & F40)]);
              dpose (frame_bounds h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3); [| clear - F40 G3; lia].
            destruct fb as [B' j']. cbn [fst snd] in *. pose proof (RAP B' j' Hfb) as AP.
            subst FS L. unfold kHighMemBeg, kFakeBytes in *. clear - Rb F1 F2 G1 G2 G3 AP R1 R2 LO EL SLO SHD1 SHD2 SHD3 FB LF0. unfold shad in *. lia.
      - intros c Hc Hr. apply MU. rewrite wa_unsigned by exact Hr. cbn.
        assert (SHC : shadow_of AL0 c = shad c) by reflexivity. rewrite SHC in *. 
        assert (CC : 0 <= c < 2^47 /\ (STKLO <= c \/ c < 0x65dab0 \/ (exists A n, In (A, n) LB /\ A <= c < A + n) \/ (exists fb, In fb LF /\ fst fb <= c < fst fb + snd fb))).
        { destruct (cshd_cases h LB LF c Hc) as [S|[(A & n & HIn & RA)|[(fb & Hfb & Rfb)|C]]].
          - split; [subst L; clear - S LO SLO SHI EL; lia| left; clear - S; lia].
          - dpose (block_bounds h LB LF m HOK HM0 A n HIn) as (BB1 & BB2 & BB3). split; [unfold kHighMemBeg in BB1; clear - BB1 BB3 RA; lia|]. right; right; left. dexists A, n. auto.
          - dpose (frame_bounds h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & _). split; [subst FS L; unfold kHighMemBeg, kFakeBytes in *; clear - G1 G2 Rfb LF0; lia|]. do 3 right. exists fb. auto.
          - split; [clear - C; lia| right; left; clear - C; lia]. }
        destruct CC as [C0 CC].
        (* [comment removed for export] *)
        assert (IMP : shd r <= shad c < shd r + fsk_bytes k / 8 -> r <= c < r + fsk_bytes k).
        { rewrite SHD1. unfold shad. pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). pose proof (Z.div_mod r 64 ltac:(lia)). pose proof (Z.div_mod (fsk_bytes k) 64 ltac:(lia)).
          clear - H H0 H1 H2 R64 FSZ C0. lia. }
        assert (NR : ~ (r <= c < r + fsk_bytes k)).
        { intros RC. destruct CC as [S|[C|[(A & n & HIn & RA)|(fb & Hfb & Rfb)]]].
          - subst FS L. unfold kFakeBytes in *. clear - S RC R1 R2 LF0 SLO EL. lia.
          - subst FS L. unfold kFakeBytes, kHighMemBeg in *. clear - C RC R1 R2 LF0. lia.
          - apply (block_not_fs h LB LF m HOK HM0 A n c HIn RA). subst FS L. unfold kFakeBytes in *. clear - RC R1 R2. lia.
          - destruct fb as [B' j']. cbn [fst snd] in Rfb. pose proof (RAP B' j' Hfb) as AP. clear - AP RC Rfb. lia. }
        subst FS L. unfold shad, kHighMemBeg, kFakeBytes in *. pose proof (Z.div_mod c 8 ltac:(lia)).
        clear - IMP NR C0 H LO EL SLO SHI LF0 R1 R2 SHD1 SHD2 SHD3 FB. lia. }
    exists (HS STKLO h HOK). cbn [hh]. do 6 (split; [reflexivity|]). split; [intros mo; split; intros X; exact X|].
    dexists r, junk. split; [reflexivity|]. split; [exact R64|].
    split.
    { (* [comment removed for export] *)
      split; [subst FS L; unfold kHighMemBeg in LF0; clear - R1 LF0; lia|].
      split; [cbn [alloc_ceiling hl_ceil arl_L R R0 HL0]; rewrite <- FB64; subst FS L; unfold kFakeBytes in *; clear - R2 LF0; lia|].
      split; [cbn [hl_data_lo hl_data_hi arl_L R R0 HL0]; right; subst FS L; unfold kHighMemBeg in LF0; clear - R1 LF0; lia|].
      intros B j HBj. rewrite <- FB64. apply in_app_iff in HBj. destruct HBj as [HBj|HBj].
      - dpose (block_bounds h LB LF m HOK HM0 B j HBj) as (BB1 & BB2 & BB3).
        destruct (Z_lt_le_dec B r) as [BR|RB].
        + destruct (Z_lt_le_dec r (B + j)) as [X|X]; [| right; exact X]. exfalso.
          apply (block_not_fs h LB LF m HOK HM0 B j r HBj ltac:(clear - BR X; lia)). subst FS L. unfold kFakeBytes in *. clear - R1 R2 FSZ. lia.
        + destruct (Z_lt_le_dec B (r + fsk_bytes k)) as [X|X]; [| left; exact X]. exfalso.
          pose proof HP as [_ HLB]. rewrite HLB in HBj. ddestruct (live_block h B j HBj) as (kk & Hkk & _ & -> & ->).
          ddestruct (chunk_ext h kk AW Hkk) as (_ & E1 & E2 & E3 & E4 & _).
          apply (ext_not_fs h HOK kk (ck_user kk) Hkk ltac:(clear - E1 E2 E4; lia)). subst FS L. unfold kFakeBytes in *. clear - RB X R1 R2. lia.
      - ddestruct (fdata_sub LF B j HBj) as (fb & [(Hfb & F1 & F2)|(Hfb & F40)]); dpose (frame_bounds h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3); [| clear - F40 G3; lia].
        destruct fb as [B' j']. cbn [fst snd] in *. pose proof (RAP B' j' Hfb) as AP. clear - AP F1 F2. lia. }
    split; [split; [exact HM'| split; [exact (XR_zframe h m m' AG XR0)| exact HA']]|].
    split; [rewrite <- FB64; exact RWJ|].
    (* [comment removed for export] *)
    replace (Z.shiftr r 3 + al_sb AL0) with (shd r) by (unfold shd, AL0; cbn [al_sb]; clear; lia).
    destruct (cells_bytes_zcells (Z.to_nat (8 * 2^k))) as [ZB ZW].
    eapply rw_cells_reshape; [exact RWS| exact ZW|]. rewrite ZB. cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite FB8. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18939178185.19L39522399935.3 L53726731980.20L9932991387.7  00000600@00F00[S1h2kkS3hAR1h2WLS1h2kkS1h2kk1j2SZ4FS4K1H2H0". (* [comment removed for export] *)
  #[using="Type"] Lemma frame_align8 : forall h LF m fb, awf' h -> hm_fake h LF m -> In fb LF -> fst fb mod 8 = 0.
  Proof.
    intros h LF m fb AW GF Hfb. pose proof AW as ([WL [_ WD]] & _).
    ddestruct (frame_ext h LF m fb AW GF Hfb) as (kk & j & Hkk & Hj & Efb & _). rewrite Efb. cbn [fst]. rewrite fsk_frame_eq.
    pose proof (fsk_sizes kk Hkk) as SZ. unfold wf_L in WL.
    assert (FS4K : l_fs (h_L h) mod 4096 = 0) by (clear - WL; lia).
    pose proof (Z.div_mod (l_fs (h_L h)) 4096 ltac:(lia)). pose proof (Z.div_mod (fsk_bytes kk) 64 ltac:(lia)).
    replace (l_fs (h_L h) + 36864 + kk * 2 ^ 20 + j * fsk_bytes kk) with (8 * (l_fs (h_L h) / 4096 * 512 + 4608 + kk * 2^17 + j * (fsk_bytes kk / 64) * 8)) by (clear - H H0 FS4K SZ; lia).
    rewrite Z.mul_comm. apply Z_mod_mult.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L11890850722.3  L15650887376.2  L18933043916.116L26271394959.6  L26283807813.7  L28571623601.23 L28571638717.21 L28574030006.24 L28574030641.9  L28574112561.16 L28575802113.18 L28575982988.22 L28576066321.20 L3665967805.5   L37490299427.2  L37490563635.10 L37494509971.7  L37496924564.9  L38542592055.8  L38643260756.5  L39520022938.5  L41015210570.7  L41015522674.6  L44475053413.10 L48065676890.7  L48266967333.5  L5225863116.1   L5423397503.3   L5423706964.7   L5451249742.3   L59309007462.10 L59309007462.12 L59315036641.15 L61028759382.126L61028779636.117L61028779636.128L61028940993.126L61030858065.125L61031281901.115L63368119078.126L63368316589.118L63374621462.127L66966394253.4  L7293021088.5   L9631783855.6   00000;00@00]00n01@02D03F04M04h05W06H07H08908N08S08o09E09e09f09g0:80:R0:S0;30;40;C0;G0;R0;S0;^0<<0<^0=E0=g0>D0>i0?L0?o0@R0A70AT0B90BF0BW0BnS2sp2lo3SPLS1c1CS3hAR2sp2FB3old2SZ2SP1L2FS2G3S1h2FB2G12G21c2RCS2FB3FB81c1H2H02H1S3hAR5STKLO2sp1h2FB2lo2SP2LO3SLO3LF03FSB1p2P12P23SHW1a1B1j2Rb2NF3BB3S3hAR5STKLO2sp1h2FB2lo2SP2LO3LF01p2P12P23SHW1x2Y12Y22Y33NFS2D83M8'S3hAR5STKLO2sp1h2FB2lo2SP2LO3SLO3LF03FSB1p2P23SHW1a1b2Rb2fb2Q12Q22W12W2S2sp2FB2lo2SP1p1a2fb3F402W3S5STKLO2sp1h2FB2lo2SP2LO1p2P12P23SHW1a2Z12Z22Z3S3hAR5STKLO2sp1h2FB2lo2SP2LO3SLO3LF01p2P13SHW1a1CS3hAR5STKLO2sp1h2FB2lo2SP2LO3SLO3LF03FSB1p2P12P23SHW1c2C03IMP2NRS3hAR5STKLO2sp1h2FB2lo2SP2LO3SPL3LF01p2P23SHW1a1SS3hAR5STKLO1h3LF03FB'S1c1CS3hAR5STKLO1h2EL3SLO3SHI1c1SS3hAR1c1A1n2RA3BB13BB3S3hAR5STKLO1h3LF01c2fb3Rfb2W12W2FFS3hAR5STKLO1h3LF0S3hAR5STKLO1h2lo2LO2EL3SLOFS1h2FB4FS4K2G12G23FB81H2H02H12H2FS2sp1h2SP3SHI1HS2FBS2sp2SP3SPBFS2sp2lo3SPLS3hAR5STKLO1h2FB3LF02G11c1C2RCS3hAR5STKLO1h2FB3SLO3LF02G21c1S2RCS2FB1L2FS1c3kk'2i'3Rfb2RC2kk1i3EFB2EN1XS3hAR5STKLO2sp1h2FB3old2SZ2SP2G31cS3hAR2sp2FB3old2SZ2SP1L2FS2G3S3hAR5STKLO2sp2FB3old2SZ2SP1L2FS2G31cS3hAR5STKLO2sp2FB3old2SZ2SP1L2FS2G3S3hAR5STKLO2sp2FB3old2SZ2SP1L2FS2G3S3hAR5STKLO2sp2FB3old2SZ2SP1L2FS2G3S3hAR5STKLO2sp1h2FB3old2SZ2SP1L2FS2G3S3hAR2sp2FB3old2SZ2SP1L2FS2G3S3hAR5STKLO2sp2FB3old2SZ2SP1L2FS2G31cS5STKLO1h1c1SS3hAR5STKLO1h3LF0S3hAR5STKLO1h2FB3LF02G1". (* [comment removed for export] *)
  #[using="Type"] Theorem art_sfree5_i : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Pra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))Ps',(2;.VhAR,VSTKLO,)PLB,(29.$13.)PLF,(29.$13.)PFB,$1.Psz,$1.Plo,$1.Pold,(29.$47.)P,(2<.VhAR,VSTKLO,R7.R6.R5.R8.)P,(2.(>.$1.$1.)(?.$1.$1.R5.+800.)R6.)P,(46.$19.R:.(<.(4:.R6.+3.)(4;.$24.))R3.)P,(1?.$52.(53.R4.)#100.)P,(30.$19.R<.R6.(31.&40.R2<.))P,(5.(32.VR,)R7.)P,(5.R8.(33.(31.&40.R2>.)(34.VR,)))P,(54.(3:.VhAR,VSTKLO,R>.)R9.(33.(31.&40.R2?.)R9.))P,(36.$19.R10.)P,(1?.(16.&40.)R29.(37.&40.R=.))P,(1?.(16.&40.)R29.(37.&40.R=.))(39.$19.$24.(3:.VhAR,VSTKLO,R12.)(3;.$19.R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.L,(16.&40.)Lm',P,(16.&40.)(17.(16.&8.))(4.(36.$19.R1.)(4.(30.$19.R1.R?.(31.&40.R35.))(4.(18.$19.R15.R1.)(4.(25.$19.VR,R13.(55.R11.R12.)(31.&40.R35.)(32.VR,)(3<.VhAR,VSTKLO,R14.)(26.$27.)R15.R1.)(28.(2;.VhAR,VSTKLO,)Ls'',(2;.VhAR,VSTKLO,)(4.(1?.P,$1.Sp(3:.VhAR,VSTKLO,R1.)(3:.VhAR,VSTKLO,R15.))(4.(1?.$1.(35.VhAR,VSTKLO,R1.)(35.VhAR,VSTKLO,R15.))(4.(1?.$1.(3<.VhAR,VSTKLO,R1.)(3<.VhAR,VSTKLO,R15.))(4.(1?.$1.(3=.VhAR,VSTKLO,R1.)(3=.VhAR,VSTKLO,R15.))(4.(1?.$1.(3>.VhAR,VSTKLO,R1.)(3>.VhAR,VSTKLO,R15.))(4.(1?.$1.(3?.VhAR,VSTKLO,R1.)(3?.VhAR,VSTKLO,R15.))(4.Pmo,$40.(41.(42.VhAR,VSTKLO,R2.R1.)(42.VhAR,VSTKLO,R16.R1.))(2<.VhAR,VSTKLO,R1.R14.(55.R12.R13.)R2.))))))))))))))(4=.(4>.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(37.&40.(56.VR,))R14.(50.(16.&40.))R13.(51.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF FB sz lo old
      HM1 HIn OLD SZ ST LO SPL CRS MI -> ->.
    pose proof HM1 as [HM0 [XR0 HA0]]. unfold hcs_i, htop_i, hstkhi_i, hflag_i, havol_i, hfr_i in *. cbn [hh arl_stklo arl_sfree5 arl_need_smalloc R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _ & T1 & T2). pose proof (Lfacts STKLO h HOK) as LF0. dpose (Lbands STKLO h HOK) as (_ & _ & FSB & _).   (* [comment removed for export] *)
    dpose HM0 as (HP & GM & (GRO & GRW) & GT & GD & GC & GR & GQ & GS & GF & GI & GE).
    dpose GRO as (_ & _ & PS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F5W & _).
    unfold kHighMemBeg, kPrimHullLen, kPaHullLen, kFakeBytes in *.
    set (SP := bv_unsigned sp) in *. assert (ESP : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
    set (L := h_L h) in *. set (FS := l_fs L) in *.
    dpose (frame_bounds h LB LF m HOK HM0 (FB, 2048) HIn) as (G1 & G2 & G3). cbn [fst snd] in G1, G2, G3. fold L FS in G1, G2. unfold kFakeBytes in G1, G2.
    pose proof (frame_align8 h LF m (FB, 2048) AW GF HIn) as FB8. cbn [fst] in FB8.
    assert (SHDF : shd FB = Z.shiftr FB 3 + al_sb AL0) by (unfold shd, AL0; cbn [al_sb]; clear; lia).
    assert (SPB : SP <= 2^47).
    { pose proof (hcsA_below_top STKLO h (SP - 1) HOK (CRS (SP - 1) ltac:(subst SP; clear - SPL; lia))). subst L. clear - H SHI. lia. }
    eapply evtA_mono.
    { eapply (fake_sfree5 AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl
                ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                SP FS FB lo LF F fc m GF HIn); try eassumption.
      all: try (dpose (Lbands STKLO h HOK) as (_ & _ & FB' & _); subst FS L; unfold kHighMemBeg, kFakeBytes in *; clear - LF0 FB'; lia).
      - rewrite SHDF. destruct OLD as [_ W]. rewrite SZ in W. exact W.
      - intros x Hx. left. apply (vcs_of_tr AL0 h _ x (fs_tr_in h)); [reflexivity|]. unfold t_hi, kFakeBytes. cbn. subst FS L. exact Hx.
      - subst SP L. clear - LO SLO EL. lia.
      - subst SP. clear - SPL. lia.
      - clear - SPB. lia. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (x5 & x6 & x7 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & p & -> & P1 & P2 & MU & WM & MI' & ST' & GF' & RWS & PS')).
    assert (SHW : shad FS <= shd FB /\ shd FB + 256 <= shad FS + 1446400).
    { rewrite shd_eq by (subst FS L; clear - G1 LF0; lia). unfold shad. pose proof (Z.div_mod FB 8 ltac:(lia)). ddestruct LF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS4K & _).
      pose proof (Z.div_mod (l_fs L) 4096 ltac:(lia)). pose proof (Z.div_mod (l_fs L) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (l_fs L) 8 ltac:(lia)).
      subst FS L. clear - G1 G2 FB8 H H0 H1 H2 FS4K. lia. }
    assert (OUTZ : forall a, rzone h a -> outside [(lo, SP); (p, p + 1); (shd FB, shd FB + 256)] a).
    { intros a Za. cbn. pose proof (rzone_lt_stklo h HOK a Za) as Z1. pose proof (rzone_not_fs STKLO h HOK a Za) as Z2.
      pose proof (rzone_not_fs_shadow h LB LF m HOK HM0 a Za) as Z3. subst FS L. unfold kFakeBytes in *. change (11571200 / 8) with 1446400 in Z3. clear - Z1 Z2 Z3 LO EL P1 P2 SHW. lia. }
    assert (AG : zagree (rzone h) m m') by (intros x Zx; apply MU; apply OUTZ; exact Zx).
    assert (HM' : HMc h LB (lb_remove FB LF) m') by (eapply HMc_zframe; [exact HOK| exact WM| exact AG| exact HM0| exact GF']).
    (* [comment removed for export] *)
    assert (HA' : hm_absent h m').
    { apply (hm_absent_agree h m m' HA0). intros x Zx. apply MU. cbn.
      dpose (habs_zone_out STKLO h (bv_unsigned x) HOK Zx) as (Y1 & Y2 & Y3).
      assert (NFS : ~ (l_fs (h_L h) <= bv_unsigned x < l_fs (h_L h) + kFakeBytes)).
      { intros X. apply (habs_zone_tr h (bv_unsigned x) _ Zx (fs_tr_in h)). unfold t_hi. cbn [t_lo t_len]. exact X. }
      pose proof (Z.div_mod (l_fs (h_L h)) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (l_fs (h_L h)) 8 ltac:(lia)) as M8'.
      pose proof aceil_lt47 as A47.
      subst FS L. unfold kFakeBytes, kHighMemBeg, shad in *. change (11571200 / 8) with 1446400 in *.
      clear - Y1 Y2 Y3 NFS LO P1 P2 SHW LF0 A47 D8 M8'. lia. }
    unfold call_postA. dexists x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7, x28, x29, x30, x31, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact WM|].
    split.
    { apply (presA_intro h LB (lb_remove FB LF) m m' SP WM).
      - intros a Ha CA. apply MU. rewrite wa_unsigned by exact Ha. cbn.
        destruct CA as [S|[C|(b & Hb & Rb)]].
        + subst FS L. unfold shad in *. clear - S Ha P1 P2 LF0 LO EL SPL SHW FSB G1. lia.
        + cbn [hl_data_lo hl_data_hi hl_static HL0] in C. subst FS L. unfold shad in *. clear - C P1 P2 LF0 LO EL SLO SHW FSB. lia.
        + apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
          * destruct b as [B j]. cbn [fst snd] in Rb. pose proof (block_not_fs h LB LF m HOK HM0 B j a Hb Rb) as NF. dpose (block_bounds h LB LF m HOK HM0 B j Hb) as (BB1 & BB2 & BB3).
            subst FS L. unfold kHighMemBeg, kFakeBytes, shad in *. clear - NF BB1 BB3 Rb P1 P2 LO EL SLO SHW FSB LF0. lia.
          * ddestruct (fdata_sub (lb_remove FB LF) (fst b) (snd b) ltac:(destruct b; exact Hb)) as (fb & [(Hfb & Q1 & Q2)|(Hfb & F40)]);
              apply In_lb_remove in Hfb; dpose (frame_bounds h LB LF m HOK HM0 fb Hfb) as (W1 & W2 & W3); [| clear - F40 W3; lia].
            subst FS L. unfold kFakeBytes, shad in *. clear - Rb Q1 Q2 W1 W2 P1 P2 LO EL SLO SHW FSB LF0. lia.
      - intros c Hc Hr. apply MU. rewrite wa_unsigned by exact Hr. cbn.
        assert (SHC : shadow_of AL0 c = shad c) by reflexivity. rewrite SHC in *.
        assert (CC : 0 <= c < 2^47 /\ (STKLO <= c \/ c < 0x65dab0 \/ (exists A n, In (A, n) LB /\ A <= c < A + n) \/ (exists fb, In fb (lb_remove FB LF) /\ fst fb <= c < fst fb + snd fb))).
        { destruct (cshd_cases h LB (lb_remove FB LF) c Hc) as [S|[(A & n & HIn' & RA)|[(fb & Hfb & Rfb)|C]]].
          - split; [subst L; clear - S LO SLO SHI EL; lia| left; clear - S; lia].
          - dpose (block_bounds h LB LF m HOK HM0 A n HIn') as (BB1 & BB2 & BB3). split; [unfold kHighMemBeg in BB1; clear - BB1 BB3 RA; lia|]. right; right; left. dexists A, n. auto.
          - pose proof (frame_bounds h LB LF m HOK HM0 fb (In_lb_remove _ _ _ Hfb)) as (W1 & W2 & _). split; [subst FS L; unfold kHighMemBeg, kFakeBytes in *; clear - W1 W2 Rfb LF0; lia|]. do 3 right. exists fb. auto.
          - split; [clear - C; lia| right; left; clear - C; lia]. }
        destruct CC as [C0 CC].
        assert (IMP : shd FB <= shad c < shd FB + 256 -> FB <= c < FB + 2048).
        { rewrite shd_eq by (clear - G1 LF0; subst FS L; lia). unfold shad. pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). pose proof (Z.div_mod FB 8 ltac:(lia)).
          clear - H H0 H1 FB8 C0. lia. }
        assert (NR : ~ (FB <= c < FB + 2048)).
        { intros RC. destruct CC as [S|[C|[(A & n & HIn' & RA)|(fb & Hfb & Rfb)]]].
          - subst FS L. clear - S RC G1 G2 LF0 SLO EL. lia.
          - subst FS L. clear - C RC G1 G2 LF0. lia.
          - apply (block_not_fs h LB LF m HOK HM0 A n c HIn' RA). subst FS L. unfold kFakeBytes. clear - RC G1 G2. lia.
          - (* [comment removed for export] *)
            dpose GF as (_ & _ & _ & _ & NDF).
            assert (Hfb' : In fb LF) by (eapply In_lb_remove; exact Hfb).
            assert (NE : fst fb <> FB) by (intros E; apply (lb_remove_notin LF FB NDF (snd fb)); rewrite <- E at 1; rewrite <- surjective_pairing; exact Hfb).
            ddestruct (frame_ext h LF m fb AW GF Hfb') as (kk' & i' & Hkk' & Hi' & Efb' & _).
            ddestruct (frame_ext h LF m (FB, 2048) AW GF HIn) as (kk & i & Hkk & Hi & Efb & _). injection Efb as EFB EN.
            rewrite Efb' in Rfb, NE. cbn [fst snd] in Rfb, NE. fold L FS in Rfb, NE, EFB.
            destruct (fsk_frames_apart FS kk i kk' i' Hkk Hi Hkk' Hi') as [X|X].
            { destruct (Z.eq_dec kk kk') as [<-|NK]; [| left; exact NK]. right. intros <-. apply NE. symmetry. exact EFB. }
            all: pose proof (proj1 (fsk_sizes kk Hkk)) as B; rewrite <- EN in B; clear - X Rfb RC EFB EN B; lia. }
        subst FS L. unfold shad in *. pose proof (Z.div_mod c 8 ltac:(lia)).
        clear - IMP NR C0 H LO EL SLO SHI LF0 P1 P2 SHW FSB. lia. }
    exists (HS STKLO h HOK). cbn [hh]. do 6 (split; [reflexivity|]). split; [intros mo; split; intros X; exact X|].
    split; [exact HM'| split; [exact (XR_zframe h m m' AG XR0)| exact HA']].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rtcc RTC := lazymatch goal with
    | |- ro_cells _ ?m ?a [C8 (Z_to_bv 64 ?v)] => exact (asan_rtc_cell m a 8%nat v RTC ltac:(unfold rtc_cells; cbn [In]; tauto))
    | |- ro_cells _ ?m ?a [C4 (Z_to_bv 64 ?v)] => exact (asan_rtc_cell m a 4%nat v RTC ltac:(unfold rtc_cells; cbn [In]; tauto))
    | |- ro_cells _ ?m ?a [C1 (Z_to_bv 8 ?v)] => exact (asan_rtc_cell m a 1%nat v RTC ltac:(unfold rtc_cells; cbn [In]; tauto))
    end.

  #[using="Type"] Lemma rip_consts_of_rtc : forall m, asan_rtc m -> rip_consts m.
  Proof. intros m RTC. split; rtcc RTC. Qed.

  #[using="Type"] Lemma amem_consts_of_rtc : forall m, asan_rtc m -> amem_consts m.
  Proof. intros m RTC. split; [ .. | exact (rip_consts_of_rtc m RTC)]; rtcc RTC. Qed.

  #[using="Type"] Lemma ro_cells_app1 : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Pm,P,(16.&40.)(17.(16.&8.))PA,$1.Pc,$47.Pcs,(29.$47.)P,(57.$19.R4.R3.(45.$47.R2.R1.))(4.(57.$19.R5.R4.(45.$47.R3.(26.$47.)))(57.$19.R5.(<.R4.(58.(59.R3.)))R2.))")
(* [comment removed for export] *).
  Proof.
    intros m A c cs [WF BY]. cbn in WF. destruct WF as [W1 W2]. cbn [cells_bytes] in BY. apply bytes_at_app in BY. destruct BY as [B1 B2].
    rewrite cbytes_length in B2 by exact W1. split; split; cbn; [tauto| rewrite app_nil_r; exact B1| exact W2| exact B2].
  Qed.

  #[using="Type"] Lemma mic_consts_of_HM : forall h LB LF m, HMc h LB LF m -> asan_rtc m -> mic_consts m.
  Proof.
    intros h LB LF m HM0 RTC. dpose HM0 as (_ & _ & (GRO & _) & _).
    dpose GRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MICF & MICR & _).
    destruct (ro_cells_app1 m _ _ _ MICF) as [MF1 MF2]. destruct (ro_cells_app1 m _ _ _ MICR) as [MR1 MR2]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in MF2, MR2.
    split; [| exact MF1| exact MF2| | exact MR1| exact MR2| exact (rip_consts_of_rtc m RTC)]; rtcc RTC.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rip0_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "PCS,P,$1.SpPra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))PBEG,$1.Plo,$1.P,(5:.$24.R25.)P,(30.$19.R4.R2.(31.&40.R24.))P,(7.+10007???7???.R3.)P,(5.R4.(33.(31.&40.R26.)+50.))P,(54.R29.R5.(33.(31.&40.R27.)R5.))P,(36.$19.R8.)P,(1?.(16.&40.)R21.(37.&40.R8.))P,(1?.(16.&40.)R21.(37.&40.=))(39.$19.$24.R2=.(5;.R2<.R2;.R2:.R29.R25.R24.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R=.R<.R9.R;.)(4=.(4>.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(37.&40.+6:>>4.)R<.(50.(16.&40.))R;.(51.$19.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L14852739058.10L16702008875.3 L2424860234.3  L26277566518.7 L27759003520.8 L34782300383.4 00000N00W00_01901T01`S5STKLO2sp1h2lo2LO3SPT2T21x2HxS3BEG1n1XS1n1N2NZS3hAR5STKLO1h2lo2LO2EL3SLOS5STKLO2sp1h2lo2LO3SPT1a2INS3BEG1n2T81X". (* [comment removed for export] *)
  #[using="Type"] Theorem art_rip_i : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "P,$5<.Pra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))Ps',(2;.VhAR,VSTKLO,)PLB,(29.$13.)PLF,(29.$13.)PBEG,$1.Pn,$1.Plo,$1.P,(2<.VhAR,VSTKLO,R6.R5.R4.R7.)P,(5=.$19.$24.(3:.VhAR,VSTKLO,R7.)R8.R4.R3.)P,(4.(5.=R4.)(7.R4.(1:.+2.+28.)))P,(11.(1?.$1.R5.=)(5.(<.(<.R6.R5.)+8.)(1:.+2.+2?.)))P,(30.$19.R;.R5.(31.&40.R2;.))P,(5.(32.VR,)R6.)P,(5.R7.(33.(31.&40.R2=.)(5>.VR,)))P,(5.(31.&40.R2>.)(35.VhAR,VSTKLO,R=.))P,(36.$19.R?.)P,(1?.(16.&40.)R28.(37.&40.R<.))P,(1?.(16.&40.)R28.(37.&40.R<.))(39.$19.$24.(3:.VhAR,VSTKLO,R11.)(3;.$19.R33.R32.R31.R30.R2<.R2;.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R14.R13.Lr,(16.&40.)Lm',P,(16.&40.)(17.(16.&8.))(4.(1?.(16.&40.)R2.(37.&40.=))(4.(5?.(45.(>.$1.$1.)(?.$1.$1.R>.(31.&40.R34.))(26.(>.$1.$1.)))R14.R1.)(4.(18.$19.R14.R1.)(4.(36.$19.R1.)(4.(30.$19.R1.R>.(31.&40.R34.))(2<.VhAR,VSTKLO,R13.R12.R11.R1.)))))))(4=.(4>.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(37.&40.(60.VR,))R13.(50.(16.&40.))R12.(51.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros RIP0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF BEG n lo
      HM1 OBJ N TOP8 ST LO SPL SPT MI -> ->.
    pose proof HM1 as [HM0 [XR0 HA0]]. unfold hcs_i, htop_i in *. cbn [hh arl_stklo arl_rip arl_need_rip R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _ & T1 & T2).
    pose proof XR0 as [RTC _].
    assert (CRS : crange (hcsA h) lo (bv_unsigned sp - lo)).
    { intros x Hx. apply (hcsA_stack STKLO h HOK). clear - Hx LO SPT T2 EL. lia. }
    assert (POST : forall ms', rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms' ->
              call_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
                r = Z_to_bv 64 0 /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                /\ stk asegs m' lo (bv_unsigned sp) /\ HM (HS STKLO h HOK) LB LF m') ms').
    { (intros ms' dd_H; ddestruct dd_H as (x5 & x6 & x7 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST')).
      unfold call_postA. deexists 16. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
      apply (hm_frame_i STKLO (HS STKLO h HOK) LB LF m m' HM1); [| exact WM].
      intros a Ha NW. apply MU. cbn. rewrite wa_unsigned by exact Ha. split; [| exact I]. intros IN. apply NW.
      left. left. cbn [arl_stklo R0]. unfold htop_i. cbn [hh]. clear - IN LO SPT. lia. }
    destruct (Z.eq_dec n 0) as [->|NZ].
    - eapply evtA_mono; [| exact POST]. eapply (RIP0 (hcsA h)); try eassumption; try reflexivity.
      + exact (hcsA_ok STKLO h HOK).
      + clear - LO SLO EL. lia.
    - pose proof OBJ as [CRB _].
      assert (AR : app_range BEG (BEG + n + 7)).
      { destruct (hcsA_app STKLO h BEG n HOK CRB ltac:(clear - N NZ; lia)) as [X|X]; cbn [al_sb AL0] in X; [left; clear - X; lia| right].
        destruct TOP8 as [T0|T8]; [exfalso; exact (NZ T0)|]. clear - X T8. lia. }
      eapply evtA_mono; [| exact POST].
      eapply (rip_spec AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl); try eassumption; try reflexivity.
      + exact (rip_consts_of_rtc m RTC).
      + clear - LO SLO EL. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition jstep_T (src dst : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "PCS,P,$1.SpPra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))P,(5:.$24.R23.)(39.$19.$24.R24.Lms',$61.(1?.$61.R1.(4=.(4>.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(37.&40.O1.)R4.(50.(16.&40.))R3.(51.$19.)))(4=.(4>.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(37.&40.O2.)R3.(50.(16.&40.))R2.(51.$19.)))")
(* [comment removed for export] *).

  Definition amemset0_T (entry need : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "PCS,P,$1.SpPra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))PDST,$1.Pv,$1.Plo,$1.P,(5:.$24.R26.)P,(4.(5.=R4.)(5.R4.(1:.+2.+40.)))P,(4.(5.=R4.)(7.R4.+100.))P,(62.R7.)P,(30.$19.R8.R5.(31.&40.R28.))P,(7.+10007???7???.R6.)P,(5.R7.(33.(31.&40.R2:.)O1.))P,(54.R2=.R8.(33.(31.&40.R2;.)R8.))P,(36.$19.R<.)P,(1?.(16.&40.)R25.(37.&40.R<.))P,(1?.(16.&40.)R25.(37.&40.R<.))P,(1?.(16.&40.)R25.(37.&40.=))(39.$19.$24.R32.(63.R31.R30.R2?.R2>.R2:.R29.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R12.R11.R?.R>.=R=.R10.)(4=.(4>.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(37.&40.O2.)R11.(50.(16.&40.))R10.(51.$19.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L12861272847.4L21993281130.3L37256830570.3L59308906707.3L60201483707.300000:00A00H00P00WS1X1n2T81AS1X1n1NS1X1n1NS1n1N2T0S1X1n1A". (* [comment removed for export] *)
  #[using="Type"] Lemma leaf_obj_facts : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Ph,$64.PLB,(29.(>.$1.$1.))PLF,(29.(>.$1.$1.))Pm,P,(16.&40.)(17.(16.&8.))PX,$1.Pn,$1.P,(65.VhAR,VSTKLO,R6.)P,(66.VhAR,R7.R6.R5.R4.)P,(54.(67.R8.)R4.R3.)P,(7.=R4.)P,(11.(1?.$1.R5.=)(5.(<.(<.R6.R5.)+8.)(1:.+2.+2?.)))(4.(68.R7.(<.(<.R7.R6.)+7.))P,(5.+1.R6.)(4.(54.(67.R<.)(33.R8.(43.R8.+40.))+40.)(54.(67.R<.)(33.(33.(<.R8.R7.)+1.)(43.(33.(<.R8.R7.)+1.)+40.))+40.)))")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m X n HOK HM0 CR N T8. split.
    - destruct (hcsA_app STKLO h X n HOK CR N) as [A|A]; cbn [al_sb AL0] in A; [left; clear - A; lia| right].
      destruct T8 as [T0|T8]; [exfalso; clear - T0 N; lia|]. clear - A T8. lia.
    - intros _. split; intros x Hx.
      + apply (hcsA_hull64 STKLO h X x HOK (CR X ltac:(clear - N; lia)) Hx).
      + apply (hcsA_hull64 STKLO h (X + n - 1) x HOK (CR (X + n - 1) ltac:(clear - N; lia)) Hx).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma leaf_shrd : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Ph,$64.PLB,(29.(>.$1.$1.))PLF,(29.(>.$1.$1.))Pm,P,(16.&40.)(17.(16.&8.))Pc,$1.P,(65.VhAR,VSTKLO,R5.)P,(66.VhAR,R6.R5.R4.R3.)P,(67.R7.R3.)(28.(16.&8.)Lb,(16.&8.)(69.$19.R6.(23.$24.R5.)(45.(16.&8.)R1.(26.(16.&8.)))))")
(* [comment removed for export] *).
  Proof. intros h LB LF m c HOK HM0 Hc. ddestruct (shadow_mapped STKLO h LB LF m c HOK HM0 Hc) as (b & B & _). exists b. exact B. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L11632234026.8 L14271202706.7 L14273246642.4 L14273611154.3 L14275644980.5 L14275742775.10L1433380809.0  L15018181705.0 L16138495053.0 L22633142477.0 L31754916681.0 L31842947789.0 L57584510985.0 L59308972630.12L61613648525.0 00000=00U00b00j01801Y01Z01[01\01]01^01_01`02;02<S3DST1n1N1X1AS3hAR5STKLO1h2EL3SLO1a1SS1a2fb3F402W3S1a1C2NSS1a1A1j2Rb3BB1S3hAR5STKLO1h1a1b2Rb2fb2Q12W13LF0SSSSSSSS3DST1X1Y3HXY2LT1B2P12P22P3S". (* [comment removed for export] *)
  #[using="Type"] Lemma leaf_apart : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "Ph,$64.PLB,(29.(>.$1.$1.))PLF,(29.(>.$1.$1.))Pm,P,(16.&40.)(17.(16.&8.))PDST,$1.Pn,$1.P,(65.VhAR,VSTKLO,R6.)P,(66.VhAR,R7.R6.R5.R4.)P,(7.=R3.)P,(6:.(1<.VhAR,)(1=.(>.$1.$1.)R8.(1>.R7.))VSTKLO,(6;.(;.R9.))R5.R4.)(6<.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m DST n HOK HM0 N CW. dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & _).
    assert (PT : forall a, DST <= a < DST + n -> 0x0fa360 <= a /\ ~ (0x1099f8 <= a < 0x109a00) /\ ~ (0x10a6d8 <= a < 0x10a6fc)).
    { intros a Ha. destruct (CW a Ha) as [S|[[C NS]|(b & Hb & Rb)]].
      - clear - S SLO EL. lia.
      - cbn [hl_data_lo hl_data_hi hl_static HL0] in C, NS. unfold RT in NS. cbn [in_rangesZ] in NS. clear - C NS. lia.
      - apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
        + destruct b as [A j]. cbn [fst snd] in Rb. pose proof (block_bounds h LB LF m HOK HM0 A j Hb) as (BB1 & _). unfold kHighMemBeg in BB1. clear - BB1 Rb. lia.
        + ddestruct (fdata_sub LF (fst b) (snd b) ltac:(destruct b; exact Hb)) as (fb & [(Hfb & Q1 & Q2)|(Hfb & F40)]);
            dpose (frame_bounds h LB LF m HOK HM0 fb Hfb) as (W1 & W2 & W3); [| clear - F40 W3; lia].
          pose proof (Lfacts STKLO h HOK) as LF0. unfold kHighMemBeg in LF0. clear - Rb Q1 W1 LF0. lia. }
    unfold amem_apart.
    assert (IV : forall X Y, Y <= 0x0fa360 \/ (X = 0x1099f8 /\ Y = 0x109a00) \/ (X = 0x10a6d8 /\ Y = 0x10a6fc) -> X < Y -> DST + n <= X \/ Y <= DST).
    { intros X Y HXY LT. destruct (Z_lt_le_dec X (DST + n)) as [A|A]; [| left; exact A]. destruct (Z_lt_le_dec DST Y) as [B|B]; [| right; exact B].
      exfalso. ddestruct (PT (Z.max DST X) ltac:(clear - A B LT N; lia)) as (P1 & P2 & P3). clear - P1 P2 P3 HXY A B LT N. lia. }
    repeat split; apply IV; clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L2424860234.3 L2426986718.3 L26277566518.7L27008878158.3L27759003520.8L39045816654.3L61400588433.300000900C00]00h01C01N01YS1n2N02NZS1n2ds3LENS3hAR5STKLO1h2lo2LO2EL3SLOS2sp2lo3SPLS5STKLO2sp1h2lo2LO3SPT1a2INS2sp2lo3SPLS3DST2B02B1". (* [comment removed for export] *)
  #[using="Type"] Theorem artA_amemset_i : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "P,(6=.+67=;4.+68808.)P,(6>.+68258.+8:0.)P,(6>.+68808.+8;0.)Pentry,$1.Pra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))Ps',(2;.VhAR,VSTKLO,)PLB,(29.$13.)PLF,(29.$13.)PDST,$1.Pv,$1.Pn,$1.Plo,$1.Pds,(29.(16.&8.))P,(11.(1?.$1.R2;.(6?.VR,))(1?.$1.R2;.(70.VR,)))P,(2<.VhAR,VSTKLO,R9.R8.R7.R:.)P,(71.$19.R;.R7.R3.)P,(1?.$1.(58.(2>.(16.&8.)R4.))R6.)P,(5=.$19.$24.(3:.VhAR,VSTKLO,R<.)R=.R9.R7.)P,(4.(5.=R9.)(7.R9.+100.))P,(30.$19.R?.R8.(31.&40.R2?.))P,(5.(32.VR,)R9.)P,(5.R:.(33.(31.&40.R31.)(72.VR,)))P,(54.(3:.VhAR,VSTKLO,R11.)R;.(33.(31.&40.R32.)R;.))P,(36.$19.R13.)P,(11.(5.(<.R10.R>.)R=.)(5.(31.&40.R34.)R10.))P,(11.(1?.$1.R?.=)(5.(<.(<.R11.R?.)+8.)(1:.+2.+2?.)))P,(7.R10.(1:.+2.+28.))P,(6:.(73.VR,)(1=.$13.R15.(1>.R14.))(32.VR,)(35.VhAR,VSTKLO,R16.)R13.R11.)P,(5.(31.&40.R38.)(35.VhAR,VSTKLO,R17.))P,(1?.(16.&40.)R31.(37.&40.R15.))P,(1?.(16.&40.)R31.(37.&40.R15.))P,(1?.(16.&40.)R31.(37.&40.R15.))(39.$19.$24.(3:.VhAR,VSTKLO,R1;.)(3;.$19.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1>.R1=.Lr,(16.&40.)Lm',P,(16.&40.)(17.(16.&8.))(4.(5?.(45.(>.$1.$1.)(?.$1.$1.R1:.(<.R1:.R18.))(45.(>.$1.$1.)(?.$1.$1.R17.(31.&40.R3>.))(26.(>.$1.$1.))))R1>.R1.)(4.(18.$19.R1>.R1.)(4.(36.$19.R1.)(4.(1?.(16.&40.)R2.(37.&40.R1:.))(4.(71.$19.R1.R1:.(74.(16.&8.)(37.&8.R19.)(49.R18.)))(4.(30.$19.R1.R17.(31.&40.R3>.))(2<.VhAR,VSTKLO,R1=.R1<.R1;.R1.))))))))(4=.(4>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(37.&40.R3>.)R1=.(50.(16.&40.))R1<.(51.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros JW AM0 IM0 entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF DST v n lo ds
      ENT HM1 ARR LEN OBJ V ST LO SPL CRS MI DISJ TOP8 N40 CW SPT -> -> ->.
    pose proof HM1 as [HM0 [XR0 HA0]]. unfold hcs_i, htop_i in *. cbn [hh arl_stklo arl_amemset arl_memset_i arl_need_amem arl_L R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _ & T1 & T2).
    pose proof XR0 as [RTC _]. pose proof (amem_consts_of_rtc m RTC) as AC.
    assert (HSElo : HSE < lo) by (clear - LO SLO EL; lia).
    assert (N0 : 0 <= n) by (clear - LEN; lia).
    (* [comment removed for export] *)
    assert (POST : forall ms', amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST v n lo m ms' ->
              call_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
                munch [(DST, DST + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                /\ r = Z_to_bv 64 DST /\ u8arr asegs m' DST (repeat (Z_to_bv 8 v) (Z.to_nat n))
                /\ stk asegs m' lo (bv_unsigned sp) /\ HM (HS STKLO h HOK) LB LF m') ms').
    { (intros ms' dd_H; ddestruct dd_H as (x5 & x6 & x7 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ARR' & ST')).
      unfold call_postA. deexists 16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [reflexivity|].
      split; [exact ARR'|]. split; [exact ST'|].
      apply (hm_frame_i STKLO (HS STKLO h HOK) LB LF m m' HM1); [| exact WM].
      intros a Ha NW. apply MU. cbn. rewrite wa_unsigned by exact Ha. unfold htop_i in NW. cbn [hh] in NW.
      split; [| split; [| exact I]]; intros IN; apply NW; left.
      - exact (CW a IN).
      - left. cbn [arl_stklo R0]. clear - IN LO SPT. lia. }
    destruct (Z.eq_dec n 0) as [NZ0|NZ].
    - (* [comment removed for export] *)
      assert (D64 : 0 <= DST <= 2^64) by (destruct ARR as [(B0 & B1 & _) _]; rewrite LEN, NZ0 in B1; clear - B0 B1; lia).
      rewrite NZ0 in POST |- *. destruct ENT as [-> | ->].
      + eapply evtA_mono; [| exact POST]. eapply (AM0 (hcsA h)); try eassumption; try reflexivity; [exact (hcsA_ok STKLO h HOK)| clear - SPL; lia].
      + eapply evtA_cut; [eapply (JW (hcsA h)); exact (hcsA_ok STKLO h HOK)|].
        cbn beta. intros ms1 ->. eapply evtA_mono; [| exact POST].
        eapply (IM0 (hcsA h)); try eassumption; try reflexivity; [exact (hcsA_ok STKLO h HOK)| clear - SPL; lia].
    - (* [comment removed for export] *)
      assert (NP : 0 < n) by (clear - N0 NZ; lia).
      pose proof OBJ as [CRD _].
      destruct (leaf_obj_facts h LB LF m DST n HOK HM0 CRD NP TOP8) as [AR HULL].
      pose proof (leaf_apart h LB LF m DST n HOK HM0 NP CW) as AP.
      destruct ENT as [-> | ->].
      + eapply evtA_mono; [| exact POST].
        eapply (amemset_spec AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl); try eassumption; try reflexivity.
        * intros c Hc. exact (leaf_shrd h LB LF m c HOK HM0 Hc).
        * clear - SPL; lia.
      + eapply evtA_cut; [eapply (JW (hcsA h)); exact (hcsA_ok STKLO h HOK)|].
        cbn beta. intros ms1 ->. eapply evtA_mono; [| exact POST].
        eapply (imemset_spec AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl); try eassumption; try reflexivity.
        * intros c Hc. exact (leaf_shrd h LB LF m c HOK HM0 Hc).
        * clear - SPL; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition amemcpy0_T (entry need : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "PCS,P,$1.SpPra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))PDST,$1.PSRC,$1.Plo,$1.P,(5:.$24.R26.)P,(4.(5.=R4.)(5.R4.(1:.+2.+40.)))P,(4.(5.=R4.)(5.R4.(1:.+2.+40.)))P,(62.R7.)P,(30.$19.R8.R5.(31.&40.R28.))P,(7.+10007???7???.R6.)P,(5.R7.(33.(31.&40.R2:.)O1.))P,(54.R2=.R8.(33.(31.&40.R2;.)R8.))P,(36.$19.R<.)P,(1?.(16.&40.)R25.(37.&40.R<.))P,(1?.(16.&40.)R25.(37.&40.R<.))P,(1?.(16.&40.)R25.(37.&40.=))(39.$19.$24.R32.(75.R31.R30.R2?.R2>.R2:.R29.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R12.R11.R?.R>.=R=.(26.(16.&8.))R10.)(4=.(4>.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(37.&40.O2.)R11.(50.(16.&40.))R10.(51.$19.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L2424860234.3 L2426986718.3 L26277566518.7L27008878158.3L27759003520.8L35527397198.3L61400588433.3L64242860165.3L66076962694.500000900C00]00h01C01N01Y01d025S1n2N02NZS1n2ds3LENS3hAR5STKLO1h2lo2LO2EL3SLOS2sp2lo3SPLS5STKLO2sp1h2lo2LO3SPT1a2INS2sp2lo3SPLS3DST2B02B1S3SRC2B02B1S1n1b2ss4LENS3NZ0". (* [comment removed for export] *)
  #[using="Type"] Theorem artA_amemcpy_i : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "P,(6=.+67=;8.+68:?8.)P,(76.+67=;<.+8;0.)P,(76.+68:?8.+8<0.)Pentry,$1.Pra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))Ps',(2;.VhAR,VSTKLO,)PLB,(29.$13.)PLF,(29.$13.)PDST,$1.PSRC,$1.Pn,$1.Plo,$1.Pds,(29.(16.&8.))Pss,(29.(16.&8.))P,(11.(1?.$1.R2<.(77.VR,))(11.(1?.$1.R2<.(78.VR,))(1?.$1.R2<.(79.VR,))))P,(2<.VhAR,VSTKLO,R:.R9.R8.R;.)P,(71.$19.R<.R8.R4.)P,(69.$19.R=.R8.R4.)P,(1?.$1.(58.(2>.(16.&8.)R6.))R8.)P,(1?.$1.(58.(2>.(16.&8.)R6.))R9.)P,(5=.$19.$24.(3:.VhAR,VSTKLO,R?.)R10.R<.R:.)P,(5=.$19.$24.(3:.VhAR,VSTKLO,R10.)R11.R<.R;.)P,(11.(1?.$1.R<.=)(11.(5.(<.R>.R<.)R=.)(5.(<.R=.R<.)R>.)))P,(30.$19.R13.R<.(31.&40.R33.))P,(5.(32.VR,)R=.)P,(5.R>.(33.(31.&40.R35.)(72.VR,)))P,(54.(3:.VhAR,VSTKLO,R15.)R?.(33.(31.&40.R36.)R?.))P,(36.$19.R17.)P,(11.(5.(<.R14.R12.)R11.)(5.(31.&40.R38.)R14.))P,(11.(5.(<.R14.R13.)R12.)(5.(31.&40.R39.)R14.))P,(11.(1?.$1.R14.=)(5.(<.(<.R16.R14.)+8.)(1:.+2.+2?.)))P,(11.(1?.$1.R15.=)(5.(<.(<.R16.R15.)+8.)(1:.+2.+2?.)))P,(7.R16.(1:.+2.+28.))P,(6:.(73.VR,)(1=.$13.R1;.(1>.R1:.))(32.VR,)(35.VhAR,VSTKLO,R1<.)R19.R17.)P,(5.(31.&40.R3>.)(35.VhAR,VSTKLO,R1=.))P,(1?.(16.&40.)R37.(37.&40.R1;.))P,(1?.(16.&40.)R37.(37.&40.R1;.))P,(1?.(16.&40.)R37.(37.&40.R1;.))(39.$19.$24.(3:.VhAR,VSTKLO,R21.)(3;.$19.R43.R42.R41.R40.R3<.R3;.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R24.R23.Lr,(16.&40.)Lm',P,(16.&40.)(17.(16.&8.))(4.(5?.(45.(>.$1.$1.)(?.$1.$1.R20.(<.R20.R1>.))(45.(>.$1.$1.)(?.$1.$1.R1=.(31.&40.R44.))(26.(>.$1.$1.))))R24.R1.)(4.(18.$19.R24.R1.)(4.(36.$19.R1.)(4.(1?.(16.&40.)R2.(37.&40.R20.))(4.(71.$19.R1.R20.R1;.)(4.(30.$19.R1.R1=.(31.&40.R44.))(2<.VhAR,VSTKLO,R23.R22.R21.R1.))))))))(4=.(4>.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R24.(37.&40.R44.)R23.(50.(16.&40.))R22.(51.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros JW AM0 IM0 entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF DST SRC n lo ds ss
      ENT HM1 ARR BS LEN LENS OBJ OBJS OVL ST LO SPL CRS MI DISJ DISJS TOP8 TOP8S N40 CW SPT -> -> ->.
    pose proof HM1 as [HM0 [XR0 HA0]]. unfold hcs_i, htop_i in *. cbn [hh arl_stklo arl_amemcpy arl_memcpy_i arl_amemmove arl_need_amem arl_L R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _ & T1 & T2).
    pose proof XR0 as [RTC _]. pose proof (amem_consts_of_rtc m RTC) as AC.
    assert (HSElo : HSE < lo) by (clear - LO SLO EL; lia).
    assert (N0 : 0 <= n) by (clear - LEN; lia).
    assert (POST : forall ms', amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST SRC n lo ss m ms' ->
              call_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
                munch [(DST, DST + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                /\ r = Z_to_bv 64 DST /\ u8arr asegs m' DST ss /\ stk asegs m' lo (bv_unsigned sp) /\ HM (HS STKLO h HOK) LB LF m') ms').
    { (intros ms' dd_H; ddestruct dd_H as (x5 & x6 & x7 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ARR' & BS' & ST')).
      unfold call_postA. deexists 16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [reflexivity|].
      split; [exact ARR'|]. split; [exact ST'|].
      apply (hm_frame_i STKLO (HS STKLO h HOK) LB LF m m' HM1); [| exact WM].
      intros a Ha NW. apply MU. cbn. rewrite wa_unsigned by exact Ha. unfold htop_i in NW. cbn [hh] in NW.
      split; [| split; [| exact I]]; intros IN; apply NW; left.
      - exact (CW a IN).
      - left. cbn [arl_stklo R0]. clear - IN LO SPT. lia. }
    destruct (Z.eq_dec n 0) as [NZ0|NZ].
    - (* [comment removed for export] *)
      assert (D64 : 0 <= DST <= 2^64) by (destruct ARR as [(B0 & B1 & _) _]; rewrite LEN, NZ0 in B1; clear - B0 B1; lia).
      assert (S64 : 0 <= SRC <= 2^64) by (ddestruct BS as (B0 & B1 & _); rewrite LENS, NZ0 in B1; clear - B0 B1; lia).
      assert (ES : ss = []) by (destruct ss; [reflexivity| cbn in LENS; clear - LENS NZ0; lia]). subst ss.
      rewrite NZ0 in POST |- *.
      destruct ENT as [-> |[-> | ->]].
      + eapply evtA_mono; [| exact POST]. unfold amemcpy0_T in AM0. eapply (AM0 (hcsA h)) with (DST := DST) (SRC := SRC); try reflexivity; try eassumption; [exact (hcsA_ok STKLO h HOK)| clear - SPL; lia].
      + eapply evtA_cut; [eapply (JW (hcsA h)); exact (hcsA_ok STKLO h HOK)|].
        cbn beta. intros ms1 ->. eapply evtA_mono; [| exact POST]. unfold amemcpy0_T in IM0.
        eapply (IM0 (hcsA h)) with (DST := DST) (SRC := SRC); try reflexivity; try eassumption; [exact (hcsA_ok STKLO h HOK)| clear - SPL; lia].
      + eapply evtA_mono; [| exact POST]. unfold amemcpy0_T in AM0. eapply (AM0 (hcsA h)) with (DST := DST) (SRC := SRC); try reflexivity; try eassumption; [exact (hcsA_ok STKLO h HOK)| clear - SPL; lia].
    - (* [comment removed for export] *)
      assert (NP : 0 < n) by (clear - N0 NZ; lia).
      pose proof OBJ as [CRD _]. pose proof OBJS as [CRSR _].
      destruct (leaf_obj_facts h LB LF m DST n HOK HM0 CRD NP TOP8) as [AR HULL].
      destruct (leaf_obj_facts h LB LF m SRC n HOK HM0 CRSR NP TOP8S) as [ARS HULLS].
      pose proof (leaf_apart h LB LF m DST n HOK HM0 NP CW) as AP.
      destruct ENT as [-> |[-> | ->]].
      + eapply evtA_mono; [| exact POST].
        eapply (amemcpy_spec AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl); try eassumption; try reflexivity.
        * intros c Hc. exact (leaf_shrd h LB LF m c HOK HM0 Hc).
        * clear - SPL; lia.
      + eapply evtA_cut; [eapply (JW (hcsA h)); exact (hcsA_ok STKLO h HOK)|].
        cbn beta. intros ms1 ->. eapply evtA_mono; [| exact POST].
        eapply (imemcpy_spec AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl); try eassumption; try reflexivity.
        * intros c Hc. exact (leaf_shrd h LB LF m c HOK HM0 Hc).
        * clear - SPL; lia.
      + eapply evtA_mono; [| exact POST].
        eapply (amemcpy_spec AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl); try eassumption; try reflexivity.
        * intros c Hc. exact (leaf_shrd h LB LF m c HOK HM0 Hc).
        * clear - SPL; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bcmp0_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "PCS,P,$1.SpPra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))PP,$1.PQ,$1.Plo,$1.P,(5:.$24.R26.)P,(4.(5.=R4.)(5.R4.(1:.+2.+40.)))P,(4.(5.=R4.)(5.R4.(1:.+2.+40.)))P,(7:.R7.)P,(30.$19.R8.R5.(31.&40.R28.))P,(7.+10007???7???.R6.)P,(5.R7.(33.(31.&40.R2:.)+11=0.))P,(54.R2=.R8.(33.(31.&40.R2;.)R8.))P,(36.$19.R<.)P,(1?.(16.&40.)R25.(37.&40.R<.))P,(1?.(16.&40.)R25.(37.&40.R<.))P,(1?.(16.&40.)R25.(37.&40.=))(39.$19.$24.R32.(7;.R31.R30.R2?.R2>.R2:.R29.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R12.R11.R=.(26.(16.&8.))(26.(16.&8.))R10.)(4=.(4>.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(37.&40.+58704.)R11.(50.(16.&40.))R10.(51.$19.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0>L11527581574.5L11668847217.3L2420696128.3 L2424860234.3 L26277566518.7L27759003520.8L4442763142.5 L46813189085.3L61055709130.0L66151417303.4L9954808910.3 00000A00J00U00^01801S01d01m01n02902DS1n1b2qs4LENQ3NZ0S1P2B02B1S1n2ps4LENPS1n2N02NZS3hAR5STKLO1h2lo2LO2EL3SLOS5STKLO2sp1h2lo2LO3SPT1a2INS1n1b2ps4LENP3NZ0S1Q2B02B1SS1r2RB1k2HkS2sp2lo3SPL". (* [comment removed for export] *)
  #[using="Type"] Theorem artA_bcmp_i : ltac2:(CDefT.buildp (gd_tbl_AHeapL ()) "P,$7<.Pra,(16.&40.)Psp,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa0,(16.&40.)Pa1,(16.&40.)Pa2,(16.&40.)Pa3,(16.&40.)Pa4,(16.&40.)Pa5,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PF,(2:.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(17.(16.&8.))Ps',(2;.VhAR,VSTKLO,)PLB,(29.$13.)PLF,(29.$13.)PP,$1.PQ,$1.Pn,$1.Plo,$1.Pps,(29.(16.&8.))Pqs,(29.(16.&8.))P,(2<.VhAR,VSTKLO,R9.R8.R7.R:.)P,(69.$19.R;.R7.R3.)P,(69.$19.R<.R7.R3.)P,(1?.$1.(58.(2>.(16.&8.)R5.))R7.)P,(1?.$1.(58.(2>.(16.&8.)R5.))R8.)P,(5=.$19.$24.(3:.VhAR,VSTKLO,R>.)R?.R;.R9.)P,(5=.$19.$24.(3:.VhAR,VSTKLO,R?.)R10.R;.R:.)P,(30.$19.R11.R:.(31.&40.R31.))P,(5.(32.VR,)R;.)P,(5.R<.(33.(31.&40.R33.)(7=.VR,)))P,(54.(3:.VhAR,VSTKLO,R13.)R=.(33.(31.&40.R34.)R=.))P,(36.$19.R15.)P,(11.(5.(<.R12.R10.)R?.)(5.(31.&40.R36.)R12.))P,(11.(5.(<.R12.R11.)R10.)(5.(31.&40.R37.)R12.))P,(11.(1?.$1.R12.=)(5.(<.(<.R14.R12.)+8.)(1:.+2.+2?.)))P,(11.(1?.$1.R13.=)(5.(<.(<.R14.R13.)+8.)(1:.+2.+2?.)))P,(7.R14.(1:.+2.+28.))P,(5.(31.&40.R3;.)(35.VhAR,VSTKLO,R1:.))P,(1?.(16.&40.)R34.(37.&40.R18.))P,(1?.(16.&40.)R34.(37.&40.R18.))P,(1?.(16.&40.)R34.(37.&40.R18.))(39.$19.$24.(3:.VhAR,VSTKLO,R1>.)(3;.$19.R40.R3?.R3>.R3=.R39.R38.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R21.R20.Lr,(16.&40.)Lm',P,(16.&40.)(17.(16.&8.))(4.(5?.(45.(>.$1.$1.)(?.$1.$1.R1:.(31.&40.R41.))(26.(>.$1.$1.)))R21.R1.)(4.(18.$19.R21.R1.)(4.(36.$19.R1.)(4.(41.(1?.(16.&40.)R2.(37.&40.=))(1?.(29.(16.&8.))R19.R18.))(4.(30.$19.R1.R1:.(31.&40.R41.))(2<.VhAR,VSTKLO,R20.R1?.R1>.R1.)))))))(4=.(4>.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R21.(37.&40.(7>.VR,))R20.(50.(16.&40.))R1?.(51.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros BC0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF P Q n lo ps qs
      HM1 BP BQ LENP LENQ OBJP OBJQ ST LO SPL CRS MI DISJP DISJQ TOP8P TOP8Q N40 SPT -> -> ->.
    pose proof HM1 as [HM0 [XR0 HA0]]. unfold hcs_i, htop_i in *. cbn [hh arl_stklo arl_memcmp_i arl_need_bcmp arl_L R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _ & T1 & T2).
    pose proof XR0 as [RTC _]. pose proof (mic_consts_of_HM h LB LF m HM0 RTC) as MC.
    assert (HSElo : HSE < lo) by (clear - LO SLO EL; lia).
    assert (N0 : 0 <= n) by (clear - LENP; lia).
    assert (POST : forall ms', micpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo ps qs m ms' ->
              call_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
                munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                /\ (r = Z_to_bv 64 0 <-> ps = qs) /\ stk asegs m' lo (bv_unsigned sp) /\ HM (HS STKLO h HOK) LB LF m') ms').
    { (intros ms' dd_H; ddestruct dd_H as (r & x5 & x6 & x7 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & RIFF & RB & ST')).
      unfold call_postA. deexists 16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
      split. { rewrite <- RIFF. split; intros E; [| rewrite E; reflexivity].
               apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. unfold bv_modulus in E. cbn [Z.pow Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul] in E. rewrite Z.mod_0_l in E by (clear; lia).
               apply Z.mod_divide in E; [| clear; lia]. destruct E as [k Hk]. clear - Hk RB. lia. }
      split; [exact ST'|].
      apply (hm_frame_i STKLO (HS STKLO h HOK) LB LF m m' HM1); [| exact WM].
      intros a Ha NW. apply MU. cbn. rewrite wa_unsigned by exact Ha. unfold htop_i in NW. cbn [hh] in NW.
      split; [| exact I]. intros IN. apply NW. left. left. cbn [arl_stklo R0]. clear - IN LO SPT. lia. }
    destruct (Z.eq_dec n 0) as [NZ0|NZ].
    - assert (P64 : 0 <= P <= 2^64) by (ddestruct BP as (B0 & B1 & _); rewrite LENP, NZ0 in B1; clear - B0 B1; lia).
      assert (Q64 : 0 <= Q <= 2^64) by (ddestruct BQ as (B0 & B1 & _); rewrite LENQ, NZ0 in B1; clear - B0 B1; lia).
      assert (EP : ps = []) by (destruct ps; [reflexivity| cbn in LENP; clear - LENP NZ0; lia]).
      assert (EQ : qs = []) by (destruct qs; [reflexivity| cbn in LENQ; clear - LENQ NZ0; lia]). subst ps qs.
      rewrite NZ0 in *. eapply evtA_mono; [| exact POST]. unfold bcmp0_T in BC0.
      eapply (BC0 (hcsA h)) with (P := P) (Q := Q); try reflexivity; try eassumption; [exact (hcsA_ok STKLO h HOK)| clear - SPL; lia].
    - assert (NP : 0 < n) by (clear - N0 NZ; lia).
      pose proof OBJP as [CRP _]. pose proof OBJQ as [CRQ _].
      destruct (leaf_obj_facts h LB LF m P n HOK HM0 CRP NP TOP8P) as [ARP HULLP].
      destruct (leaf_obj_facts h LB LF m Q n HOK HM0 CRQ NP TOP8Q) as [ARQ HULLQ].
      eapply evtA_mono; [| exact POST].
      eapply (bcmp_icpt_spec AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl); try eassumption; try reflexivity.
      + intros c Hc. exact (leaf_shrd h LB LF m c HOK HM0 Hc).
      + clear - SPL; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End L.

End ARUN_1.
