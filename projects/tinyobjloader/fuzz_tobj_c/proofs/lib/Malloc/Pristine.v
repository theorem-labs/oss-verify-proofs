(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "option"; "andb"; "cons"; "false"; "Some"; "nat"; "nil"; "list"; "prod"; "length"; "None"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "pow"; "eqb"; "modulo"; "ltb"; "mul"; "sub"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.Req"; "untouched"; "reads"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "wz"; "C_P"; "C_U"; "mc_ctx"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_lock"; "mc_med_cnt_tab"; "mc_need_locks"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "ctz_tab_bytes"; "med_cnt_tab_bytes"; "size_classes_bytes"; "small_cnt_tab_bytes"; "holds"; "img_reserved"; "mc_auxv"; "mc_page_size"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "CTX_SIZE"; "byteview"; "le_byte"; "Layout"; "layout"; "zseq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine"; "all_range"; "img_table"; "image_ok"; "img_zero"; "img_zero_rw"; "pristine_req"; "untouched"; "auxv_keys"; "img_word"; "reads"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "image_byte"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.Img"; "img_table"; "img_zero"; "img_zero_rw"; "img_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsP"; "segsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR"; "rd_of"; "tp_ok"; "wseg_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA_init"; "ma_blocks"; "ma_s"; "ri_brk0"; "ri_sec"; "ri_top"; "run_init"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "st_init_done"; "PGSZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "alloc_top"; "m_vmmaps"; "vm_brk"; "vm_maps"; "vm_start_brk"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfInv MallocWfMain MallocLayout MallocFooter NestTier MallocIface MallocLaws Contract ReprGlue ZBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition auxv_keys : list Z := ltac2:(tb__ "0|0|
SaS5Z3SaS5Z4SaS5Z5SaS5Z10SaS5Z6SaS5ZbSaS5ZcSaS5Z17SaS5Z19SaS5Z0SeS5A1A3A3A3A3A3A3A3A3A3A3").

Section Req.
  Variable segs : list Segment.
  Variable C : mconsts.

  Definition untouched (m : word -> option byte) (lo n : Z) : Prop := ltac2:(tb__ "0|1|
S5S0S14Vlo;R1A2S15R1S13Vlo;Vn;A2A2A2S1S8S20Q8A1M0A1Vm;S23R2A1A1S12G0A1A3F_;Fa;").

  Definition reads (m : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop := ltac2:(tb__ "0|2|
SdS38R1Vw;A2S1S8S20Q8M0A1M1A1S54Vsegs;Vm;S23S13Va;S16R2A1A2A1A3ScG1S22G0S3bVv;Vw;R2A3A2A2A3F_;Fk;").

  Definition readable (m : word -> option byte) (lo n : Z) : Prop := ltac2:(tb__ "0|1|
S5S0S14Vlo;R1A2S15R1S13Vlo;Vn;A2A2A2S2S20Q8A1M0G0S1S8G0A1S54Vsegs;Vm;S23R3A1A3ScG0R1A2A3Lb;A2F_;Fa;").

  Definition pristine_req (ri : run_init) (rho : valuation) (md : Model) : Prop := ltac2:(tb__ "0|e|
S4cVrho;A1S20Q40M0A1M1S8S20Q8A1A1F_;S5aVri;A1S5S0S1eR2S26VC;A1S39A3S0S1eR2S2aVC;A1Z4M2A3S0S1eR2S2dVC;A1G2A3S0S1eR2S2cVC;A1Z1A3S0S1eR2S2eVC;A1Z60A3S0S1eR2S2fVC;A1Z1bA3S0S1eR2S2bVC;A1G2A3S0S1eR2S29VC;A1Z20A3S0S1eR2S28VC;A1Z8M3A3S0S1fR2S37VC;A1U8M4Z1000A4S0S2S5S5S1fR3S27VC;A1G4R1A4Lgd;A2S0S2S5S5S2S5S5S0S1fR4S36VC;A1G4R2A4S0S14S5cVri;A1M5R2A2S0S14S13R2Za0A2S17Z2Z40A2M6A2S0S14G5R1A2S0S14S13R1Z10M7A2G6A2S0SdS38R1UaA2M8S1fR6S13R4S1bG7S16R2A1A2A2G4S49S5R2S46Z0M9A4A4F_;Fj;S0SdG8S2S5S5S1fR7S13S13R5S1bG7S16R3A1A2A2G3A2G4R1A4Lv;A2F_;Fj;S0S1fR4S13R2Z88A2G4R1A4S1fR4S13R1G3A2G4S5bVri;A1MaA4A2A2A2A2A2A2A2A2Lq;A2Lav;A2S0S1SfS10G1G1A2MbA1S64S62Vmd;A1McA1SeGbA1A3S0S1S5S21G0S63GcA1A2R1A3S0S1S5S21G0S65GcA1A2R1A3S0S1S5S19R1S5fA2G9A3S0S0S1S5S61GcA1G5A3S0S0S14Z7fff7f800000MdG5A2S14G5Z7fffff800000A2A2S0S14G9GaA2S15GaG6A2A2A2A2S0S0S15G9R1A2S15R1GdA2A2S0S35VC;GcA2S55VC;Vrho;A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Tbrk0;Tm;").
End Req.

Definition all_range (f : Z -> bool) (lo n : Z) : bool := ltac2:(tb__ "0|0|
S66S5Vf;S3eVlo;Vn;A2A3").

Lemma all_range_sound f lo n : ltac2:(tb__ "0|0|
S1S6S3fVf;Vlo;Vn;A3S7A3S5S0S14Vlo;R1A2S15R1S13Vlo;Vn;A2A2A2S1S6Vf;R2A1S7A3F_;Fa;F_;").
Proof.
  intros H a Ha. unfold all_range in H. rewrite forallb_forall in H. apply H. apply In_zseq. lia.
Qed.

Section Img.
  Variable segs : list Segment.
  Variable C : mconsts.

  Definition img_zero_rw (lo n : Z) : bool := ltac2:(tb__ "0|3|
S3fS5S9S8S20Q8M0A1M1A1S6Lx;S4aVsegs;S23R1A1M2A2G1S18S21G0R1A2Z0A2Lb;SbX8x2S56Vsegs;G2A2A2La;Vlo;Vn;A3").
  Definition img_zero (lo n : Z) : bool := ltac2:(tb__ "0|2|
S3fS5S8S20Q8M0A1M1A1S6Lx;S4aVsegs;S23R1A1A2G1S18S21G0R1A2Z0A2Lb;SbX8x2La;Vlo;Vn;A3").
  Definition img_table (lo : Z) (tab : list Z) : bool := ltac2:(tb__ "0|2|
S3fS5S8S20Q8M0A1M1A1S6Lx;S4aVsegs;S23R1A1A2G1S18S21G0R1A2S49S5S1dS1cR2Vlo;A2A1Vtab;Z0A4A2Lb;SbX8x2La;Vlo;S16S11S5Vtab;A2A1A3").
  Definition img_word (lo : Z) (v : Z) : bool := ltac2:(tb__ "0|2|
S3fS5S8S20Q8M0A1M1A1S6Lx;S4aVsegs;S23R1A1A2G1S18S21G0R1A2S3bVv;U8S1dS1cR2Vlo;A2A1A3A2Lb;SbX8x2La;Vlo;Z8A3").

  Definition image_ok : bool := ltac2:(tb__ "0|3|
S9S9S9S9S9S9S9S9S9S9S9S4fS26VC;A1M0S39A2S4fS2aVC;A1Z4M1A2A2S4eS2dVC;A1G1A2A2S4eS2cVC;A1Z1A2A2S4dS2eVC;A1S32A2A2S4dS2fVC;A1S33A2A2S4dS2bVC;A1S31A2A2S4dS29VC;A1S30A2A2S50S28VC;A1S27VC;A1A2A2S18S19G0Z8A2Z0M2A2A2S1aG2G0A2A2S1aS13G0S39A2S17Z2Z3eA2A2A2").
End Img.

Lemma image_ok_P : ltac2:(tb__ "0|0|
S1S6S41S51S24A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma image_ok_U : ltac2:(tb__ "0|0|
S1S6S41S52S25A2S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma le_byte_0 w k : le_byte 0 w k = 0.
Proof. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.

Lemma auxv_keys_early j : ltac2:(tb__ "0|2|
S38Vj;U8A2S0S3S1S5S49S5Vj;S46Z0M0A4M1G0A3A1S3S1S5G1Z19A3A1A2F_;").
Proof.
  intros Hj.
  assert (X : forallb (fun j => negb (nth j auxv_keys 0 =? 0) && negb (nth j auxv_keys 0 =? 25)) (seq 0 8) = true) by reflexivity.
  rewrite forallb_forall in X. specialize (X j ltac:(apply in_seq; lia)).
  apply andb_prop in X as [X1 X2]. apply Bool.negb_true_iff in X1. apply Bool.negb_true_iff in X2.
  apply Z.eqb_neq in X1. apply Z.eqb_neq in X2. auto.
Qed.

Section Thm.
  Variable segs : list Segment.
  Variable C : mconsts.
  Variable ri : run_init.
  Variable rho : valuation.
  Variable md : Model.
  Hypothesis IMG : ltac2:(tb__ "0|0|
S1S6S41Vsegs;VC;A2S7A3").
  Hypothesis HS : statics_in_image C.
  Hypothesis REQ : ltac2:(tb__ "0|0|
S44Vsegs;VC;Vri;Vrho;Vmd;A5").

  Let m := rm rho.
  Let rd := rd_of segs m.
  Let wok := wok_of segs m.
  Let bv := byteview_of rd wok.
  Let rv := byteview_of rd (fun _ => true).
  Let L : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS26VC;A1SdZ0L_;S5aVri;A1S5bVri;A1S5cVri;A1A5").

  Lemma IMG_parts : ltac2:(tb__ "0|3|
S0S1S6S43Vsegs;S26VC;A1M0S39A3S7A3S0S1S6S43Vsegs;S2aVC;A1Z4M1A3S7A3S0S1S6S42Vsegs;S2dVC;A1G1A3S7A3S0S1S6S42Vsegs;S2cVC;A1Z1A3S7A3S0S1S6S40Vsegs;S2eVC;A1S32A3S7A3S0S1S6S40Vsegs;S2fVC;A1S33A3S7A3S0S1S6S40Vsegs;S2bVC;A1S31A3S7A3S0S1S6S40Vsegs;S29VC;A1S30A3S7A3S0S1S6S47Vsegs;S28VC;A1S27VC;A1A3S7A3S0S1S5S19G0Z8A2Z0M2A3S0S15G2G0A2S15S13G0S39A2S17Z2Z3eA2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using IMG.
    pose proof IMG as H. unfold image_ok in H. rewrite !Bool.andb_true_iff in H.
    destruct H as (((((((((((A1 & A2) & A3) & A4) & A5) & A6) & A7) & A8) & A9) & A10) & A11) & A12).
    apply Z.eqb_eq in A10. apply Z.ltb_lt in A11. apply Z.ltb_lt in A12.
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma zero_rw_byte lo n a : ltac2:(tb__ "0|3|
S1S6S43Vsegs;Vlo;Vn;A3S7A3S45Vm;Vlo;Vn;A3S0S14Vlo;Va;A2S15Va;S13Vlo;Vn;A2A2A2S0S14Z0M0Va;A2S15Va;S17Z2Z40A2A2A2S0S1S8S5A1M1Vbv;Va;A1ScS5G0A2M2A3S1G1Vrv;Va;A1G2A3A2F_;F_;F_;F_;").
  Proof using rd wok.
    intros Hi Hu Ha Hr. pose proof (all_range_sound _ _ _ Hi a Ha) as X. cbn beta in X.
    apply andb_prop in X as [X1 X2]. specialize (Hu a Ha).
    unfold bv, rv, rd, wok, m in *. unfold byteview_of, rd_of, wok_of. unfold wz in *. rewrite Hu, X2.
    replace ((0 <=? a) && (a <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    cbn [andb]. destruct (image_byte segs (Z_to_bv 64 a)) as [b|]; [|discriminate]. apply Z.eqb_eq in X1. rewrite X1. auto.
  Qed.

  Lemma zero_byte lo n a : ltac2:(tb__ "0|1|
S1S6S42Vsegs;Vlo;Vn;A3S7A3S45Vm;Vlo;Vn;A3S0S14Vlo;Va;A2S15Va;S13Vlo;Vn;A2A2A2S0S14Z0M0Va;A2S15Va;S17Z2Z40A2A2A2S1S8S5A1Vrv;Va;A1ScS5G0A2A3F_;F_;F_;F_;").
  Proof using rd.
    intros Hi Hu Ha Hr. pose proof (all_range_sound _ _ _ Hi a Ha) as X. cbn beta in X. specialize (Hu a Ha).
    unfold rv, rd, m in *. unfold byteview_of, rd_of. unfold wz in *. rewrite Hu.
    replace ((0 <=? a) && (a <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    cbn [andb]. destruct (image_byte segs (Z_to_bv 64 a)) as [b|]; [|discriminate]. apply Z.eqb_eq in X. rewrite X. reflexivity.
  Qed.

  Lemma table_byte lo tab k : ltac2:(tb__ "0|3|
S1S6S40Vsegs;Vlo;Vtab;A3S7A3S45Vm;Vlo;S16S11S5Vtab;A2M0A1M1A3S38Vk;G0A2S14Z0M2Vlo;A2S15S13Vlo;G1A2S17Z2Z40A2A2S1S8S5A1Vrv;S13Vlo;S16Vk;A1A2A1ScS5S49S5Vk;Vtab;G2A4A2A3F_;F_;F_;F_;F_;").
  Proof using rd.
    intros Hi Hu Hk Hlo Hhi. pose proof (all_range_sound _ _ _ Hi (lo + Z.of_nat k) ltac:(lia)) as X. cbn beta in X.
    specialize (Hu (lo + Z.of_nat k) ltac:(lia)).
    unfold rv, rd, m in *. unfold byteview_of, rd_of. unfold wz in *. rewrite Hu.
    replace ((0 <=? lo + Z.of_nat k) && (lo + Z.of_nat k <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    cbn [andb]. destruct (image_byte segs (Z_to_bv 64 (lo + Z.of_nat k))) as [b|]; [|discriminate]. apply Z.eqb_eq in X. rewrite X.
    replace (lo + Z.of_nat k - lo) with (Z.of_nat k) by lia. rewrite Nat2Z.id. reflexivity.
  Qed.

  Lemma reads_holds a w v (M : byteview) : ltac2:(tb__ "0|0|
S4S1S3aVM;Vrv;A3S0S1S3aVM;Vbv;A3SdS38R1Vw;A2S1S6Vwok;S23S13Va;S16R2A1A2A1A1S7A3F_;Fk;A2A2S48Vsegs;Vm;Va;Vw;Vv;A5S14Z0Va;A2S14S13Va;S16Vw;A1A2S17Z2Z40A2A2S34VM;Va;Vw;Vv;A4F_;F_;F_;F_;").
  Proof using rd.
    intros HM Hr Ha Hw k Hk. specialize (Hr k Hk). unfold rd in *.
    assert (R : 0 <= a + Z.of_nat k < 2 ^ 64) by lia.
    assert (E : forall f, byteview_of (rd_of segs m) f (a + Z.of_nat k) = if f (wz (a + Z.of_nat k)) then Some (le_byte v w k) else None).
    { intros f. unfold byteview_of. unfold wz in *.
      replace ((0 <=? a + Z.of_nat k) && (a + Z.of_nat k <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      cbn [andb]. destruct (f (Z_to_bv 64 (a + Z.of_nat k))); [|reflexivity]. rewrite Hr. f_equal. apply Z_to_bv_small.
      change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_pos_bound. lia. }
    destruct HM as [-> | [-> Hwk]]; unfold rv, bv; rewrite E; [reflexivity|]. rewrite (Hwk k Hk). reflexivity.
  Qed.

  Theorem minv_pristine : ltac2:(tb__ "0|2|
S0S53Vsegs;VC;S57VC;Vri;A2M0Vrho;Vmd;A5S0S1SfS10S5S5A2M1A1S58G0A1SeG1A1A3S1S6S5eS59G0A1A1SbA3A2A2").
  Proof using HS IMG REQ.
    split; [|split; reflexivity].
    pose proof IMG_parts as (Ictx & Ilock & Irep & Inl & Isc & Ismall & Imed & Ictz & Igot & Cmod & Cpos & Chi).
    pose proof REQ as RQ. unfold pristine_req in RQ. cbn zeta in RQ.
    destruct RQ as (Uctx & Ulock & Urep & Unl & Usc & Usmall & Umed & Uctz & Ugot & Rps & (gd & Rguard) &
                    (av & q & Rav & Hav0 & Hav1 & Hq0 & Hq1 & Rkeys & Rvals & Rq & Rsec) & Vmaps & Vbrk & Vsbrk & Vpg & (Vtop & Vtr & Vsec) & Vrange & Vimg & Htp).
    assert (TOP : topL L = ri_top ri) by (apply topL_of_range; exact Vtr).
    unfold MInvR, MInv. cbn [ma_s ma_L MA_init].
    change (rd_of segs (rm rho)) with rd. change (wok_of segs (rm rho)) with wok. fold bv. fold rv.
    split; [apply wf_init|].
    split.
    {   unfold bounded, usage_of. cbn [st_usage st_meta_alloc_shift st_areas st_avail_meta_area_count init_state length Z.of_nat].
      split; [|split; [lia|split; [lia|left; split; reflexivity]]]. intros sc.
      assert (K : forall (n : nat) (k : nat), nth k (repeat 0 n) 0 = 0).
      { intros n. induction n as [|n IH]; intros [|k]; cbn; auto. }
      unfold znth. rewrite K. lia. }
    split; [reflexivity|].
    assert (FP : footprint init_state = [(LCtx 0, CTX_SIZE)]) by reflexivity.
    assert (CTX : forall a, mc_ctx C <= a < mc_ctx C + CTX_SIZE -> bv a = Some 0 /\ rv a = Some 0).
    { intros a Ha. apply (zero_rw_byte _ _ a Ictx Uctx Ha). unfold CTX_SIZE in *. lia. }
    split.
    {   split; [split; [|split]|].
      -   split; [exact Cmod|]. split; [intros k rg Hk; cbn in Hk; destruct k; discriminate|].
        rewrite FP. split; [cbn; split; [intros ? [] | exact I]|]. intros rg [<-|[]]. unfold crange, loc_addr. cbn. unfold CTX_SIZE in *. lia.
      -
        assert (ALL : forallb (fun c => match mc_loc c, mc_val c with
                                        | LCtx off, VZ 0 => (0 <=? off) && (off + Z.of_nat (mc_w c) <=? CTX_SIZE)
                                        | _, _ => false end) (image init_state) = true) by (vm_compute; reflexivity).
        apply Forall_forall. intros c Hc. rewrite forallb_forall in ALL. specialize (ALL c Hc).
        destruct c as [[off|p] w [z| | |]]; try discriminate. destruct z; try discriminate.
        apply andb_prop in ALL as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2.
        unfold MallocInv.cell_holds. cbn [mc_loc mc_val mc_w loc_addr sval_num ly_ctx].
        intros k Hk. rewrite le_byte_0.
        cbn [mc_w] in A2. apply (proj1 (CTX (mc_ctx C + off + Z.of_nat k) ltac:(lia))).
      -
        intros x [(rg & Hrg & Hx) _]. rewrite FP in Hrg. destruct Hrg as [<-|[]]. unfold loc_addr in Hx. cbn in Hx.
        rewrite (proj1 (CTX x ltac:(lia))). discriminate.
      -   unfold footer_cells. cbn. constructor. }
    split.
    {   split; [intros r rg Hr; cbn in Hr; destruct r; discriminate|].
      split; [intros r rg Hr; cbn in Hr; destruct r; discriminate|].
      split; [cbn; rewrite Vbrk, Vsbrk; auto|].
      split; [intros p n Hin; rewrite FP in Hin; destruct Hin as [Hin|[]]; discriminate|].

      split; [intros r rg off Hr; cbn in Hr; destruct r; discriminate|].
      split; [intros r1 r2 rg1 rg2 _ H1; cbn in H1; destruct r1; discriminate|].
      split; [intros r rg Hr; cbn in Hr; destruct r; discriminate|].
      split; [intros r rg Hr; cbn in Hr; destruct r; discriminate|].
      split; [intros r rg q0 n0 Hr; cbn in Hr; destruct r; discriminate|].
      split; [intros r p0 k rgk _ Hk; cbn in Hk; destruct k; discriminate|].
        rewrite Vtop. apply topL_of_range. exact Vtr. }
    pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
    destruct HS0 as (Ilibc & Irep' & Isc' & Ismall' & Imed' & Ictz' & Igot' & Iguard' & Ilock' & Ictx' & Ierr' & Hpg & Hceil).
    assert (CEIL : topL L < 2 ^ 63) by (rewrite TOP; lia).
    unfold mc_need_locks, mc_page_size, mc_auxv, PGSZ, UNIT in *.
    split.
    {
      unfold statics_ok, mc_need_locks, mc_page_size.
      split. { intros k Hk. rewrite le_byte_0. apply (zero_byte _ _ _ Inl Unl); lia. }
      split. { apply (reads_holds _ _ _ rv (or_introl eq_refl) Rps); lia. }
      split. { intros k Hk. rewrite le_byte_0. apply (zero_byte _ _ _ Irep Urep); lia. }
      split. { intros k Hk. rewrite le_byte_0. apply (proj1 (zero_rw_byte _ _ (mc_lock C + Z.of_nat k) Ilock Ulock ltac:(lia) ltac:(lia))). }
      split. { intros k Hk. apply (table_byte _ _ k Isc Usc); [exact Hk | lia | change (Z.of_nat (length size_classes_bytes)) with 96; lia]. }
      split. { intros k Hk. apply (table_byte _ _ k Ismall Usmall); [exact Hk | lia | change (Z.of_nat (length small_cnt_tab_bytes)) with 27; lia]. }
      split. { intros k Hk. apply (table_byte _ _ k Imed Umed); [exact Hk | lia | change (Z.of_nat (length med_cnt_tab_bytes)) with 4; lia]. }
      split. { intros k Hk. apply (table_byte _ _ k Ictz Uctz); [exact Hk | lia | change (Z.of_nat (length ctz_tab_bytes)) with 32; lia]. }
      exists gd. split.
      - intros k Hk. pose proof (all_range_sound _ _ _ Igot (mc_chk_guard_got C + Z.of_nat k) ltac:(lia)) as X. cbn beta in X.
        specialize (Ugot (mc_chk_guard_got C + Z.of_nat k) ltac:(lia)).
        unfold rv, rd, m in *. unfold byteview_of, rd_of. unfold wz in *. rewrite Ugot.
        replace ((0 <=? mc_chk_guard_got C + Z.of_nat k) && (mc_chk_guard_got C + Z.of_nat k <? 2 ^ 64))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        cbn [andb]. destruct (image_byte segs (Z_to_bv 64 (mc_chk_guard_got C + Z.of_nat k))) as [b|]; [|discriminate].
        apply Z.eqb_eq in X. rewrite X. replace (mc_chk_guard_got C + Z.of_nat k - mc_chk_guard_got C) with (Z.of_nat k) by lia. rewrite Nat2Z.id. reflexivity.
      - apply (reads_holds _ _ _ rv (or_introl eq_refl) Rguard); lia. }
    split.
    {   intros _. unfold auxv_ok, mc_auxv. exists av, q, 8. cbn [ly_sec]. fold L. rewrite TOP.
      split; [apply (reads_holds _ _ _ rv (or_introl eq_refl) Rav); lia|].
      split; [apply (reads_holds _ _ _ rv (or_introl eq_refl) (Rkeys 8%nat ltac:(lia))); lia|].
      split; [replace (av + 16 * 8 + 8) with (av + 136) by lia; apply (reads_holds _ _ _ rv (or_introl eq_refl) Rq); lia|].
      split; [apply (reads_holds _ _ _ rv (or_introl eq_refl) Rsec); lia|].
      split.
      { intros j Hj. destruct (Rvals (Z.to_nat j) ltac:(lia)) as [v Rv]. rewrite Z2Nat.id in Rv by lia.
        exists (nth (Z.to_nat j) auxv_keys 0), v.
        split; [pose proof (reads_holds _ _ _ rv (or_introl eq_refl) (Rkeys (Z.to_nat j) ltac:(lia))) as K; rewrite Z2Nat.id in K by lia; apply K; lia|].
        destruct (auxv_keys_early (Z.to_nat j) ltac:(lia)) as [K0 K25].
        split; [exact K0|].
        split; [apply (reads_holds _ _ _ rv (or_introl eq_refl) Rv); lia|].
        intros E. exfalso. exact (K25 E). }
      split; [|lia]. exists 9. split; [lia|]. split; [apply (reads_holds _ _ _ rv (or_introl eq_refl) (Rkeys 9%nat ltac:(lia))); lia|].
      intros j Hj. lia. }
    split.
    {   intros e He. rewrite Vmaps in He. destruct He. }
    split; [   exact Vimg |].
    split.
    {   intros l1 e l2 E. rewrite Vmaps in E. destruct l1; discriminate E. }
      apply reach_ok_nometas. reflexivity.
  Qed.
End Thm.

Theorem minv_pristine_P : ltac2:(tb__ "0|2|
S5dS4bS60S44S51S24R3R2R1A5S0S53S51S24S57S24R4A2M0R3R2A5S0S1SfS10S5S5A2M1A1S58G0A1SeG1A1A3S1S6S5eS59G0A1A1SbA3A2A2F_;Fmd;Frho;Fri;").
Proof. intros ri rho md R. exact (minv_pristine segsP C_P ri rho md image_ok_P statics_in_image_P R). Qed.

Theorem minv_pristine_U : ltac2:(tb__ "0|2|
S5dS4bS60S44S52S25R3R2R1A5S0S53S52S25S57S25R4A2M0R3R2A5S0S1SfS10S5S5A2M1A1S58G0A1SeG1A1A3S1S6S5eS59G0A1A1SbA3A2A2F_;Fmd;Frho;Fri;").
Proof. intros ri rho md R. exact (minv_pristine segsU C_U ri rho md image_ok_U statics_in_image_U R). Qed.
