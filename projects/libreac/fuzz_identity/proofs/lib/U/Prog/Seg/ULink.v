From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_identity_init_c reac_identity_ingest_c reac_identity_fw_str_c
  reac_identity_reac_ver_str_c reac_box_catalogue_defect_c reac_box_family_of_c reac_box_family_stem_c check_str_c
  put_dec_c reac_box_name_c reac_box_catalogue_c bcmp_c memchr_c memcpy_c strlen_c strcmp_c buf_of_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import
  A01 A02 A03 A04 A05 A06 A07 A08 A09 B01 B02 B03 B04 B05 B06 B07 B08 B09 B10 B11 B12 B13 B14 B15 B16 B17 B18 B19 B20 B21 B22 B23 B24 B25 B26 B27 B28 B29 C01 C02 C03 C04 C05 D01 E01 E02 E03 E04 E05 E06 E07 E08 E09 E10 F01 F02 F03 F04 G01 G02 G03 G04 G05 G06 G07 H01 H02 H03 H04 H05 H06 H07 H08 H09 H10 H11 H12 H13 H14 H15 H16 H17 I01 I02 I03 I04 I05 I06 I07 I08 I09 I10 I11 J01 J02 J03 J04 J05 J06 J07 J08 UB00 UAsm USlot.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_identity_init reac_identity_ingest reac_identity_fw_str reac_identity_reac_ver_str
  write_uint reac_box_catalogue_defect reac_box_family_of reac_box_family_stem check_str put_dec reac_box_name sb_dec sb_ch
  reac_box_catalogue bcmp memchr memcpy memset strlen strcmp buf_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require FrameProof.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import URzInst.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import AllocRoom.
From OSSVerify.libreac.fuzz_identity Require Statements.
Import ListNotations.
Open Scope Z_scope.
Section Link.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : lib.Reusable.YM05.RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis INIT : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_init_c.reac_identity_init_contract.
Hypothesis ING : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_ingest_c.reac_identity_ingest_contract.
Hypothesis FWS : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_fw_str_c.reac_identity_fw_str_contract.
Hypothesis VS : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_reac_ver_str_c.reac_identity_reac_ver_str_contract.
Hypothesis CATD : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_catalogue_defect_c.reac_box_catalogue_defect_contract.
Hypothesis FAM : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_family_of_c.reac_box_family_of_contract.
Hypothesis STEM : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_family_stem_c.reac_box_family_stem_contract.
Hypothesis CHK : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.check_str_c.check_str_contract.
Hypothesis PD : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.put_dec_c.put_dec_contract.
Hypothesis BOXN : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_name_c.reac_box_name_contract.
Hypothesis CAT : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_catalogue_c.reac_box_catalogue_contract.
Hypothesis BC : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.bcmp_c.bcmp_contract.
Hypothesis MCH : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.memchr_c.memchr_contract.
Hypothesis MCP : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.memcpy_c.memcpy_contract.
Hypothesis SLEN : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.strlen_c.strlen_contract.
Hypothesis SCMP : OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.strcmp_c.strcmp_contract.

Ltac link_seg :=
  first
    [ eapply seg_A01
    | eapply seg_A02
    | eapply seg_A03
    | eapply seg_A04
    | eapply seg_A05
    | eapply seg_A06
    | eapply seg_A07
    | eapply seg_A08
    | eapply seg_A09
    | eapply seg_B01
    | eapply seg_B02
    | eapply seg_B03
    | eapply seg_B04
    | eapply seg_B05
    | eapply seg_B06
    | eapply seg_B07
    | eapply seg_B08
    | eapply seg_B09
    | eapply seg_B10
    | eapply seg_B11
    | eapply seg_B12
    | eapply seg_B13
    | eapply seg_B14
    | eapply seg_B15
    | eapply seg_B16
    | eapply seg_B17
    | eapply seg_B18
    | eapply seg_B19
    | eapply seg_B20
    | eapply seg_B21
    | eapply seg_B22
    | eapply seg_B23
    | eapply seg_B24
    | eapply seg_B25
    | eapply seg_B26
    | eapply seg_B27
    | eapply seg_B28
    | eapply seg_B29
    | eapply seg_C01
    | eapply seg_C02
    | eapply seg_C03
    | eapply seg_C04
    | eapply seg_C05
    | eapply seg_D01
    | eapply seg_E01
    | eapply seg_E02
    | eapply seg_E03
    | eapply seg_E04
    | eapply seg_E05
    | eapply seg_E06
    | eapply seg_E07
    | eapply seg_E08
    | eapply seg_E09
    | eapply seg_E10
    | eapply seg_F01
    | eapply seg_F02
    | eapply seg_F03
    | eapply seg_F04
    | eapply seg_G01
    | eapply seg_G02
    | eapply seg_G03
    | eapply seg_G04
    | eapply seg_G05
    | eapply seg_G06
    | eapply seg_G07
    | eapply seg_H01
    | eapply seg_H02
    | eapply seg_H03
    | eapply seg_H04
    | eapply seg_H05
    | eapply seg_H06
    | eapply seg_H07
    | eapply seg_H08
    | eapply seg_H09
    | eapply seg_H10
    | eapply seg_H11
    | eapply seg_H12
    | eapply seg_H13
    | eapply seg_H14
    | eapply seg_H15
    | eapply seg_H16
    | eapply seg_H17
    | eapply seg_I01
    | eapply seg_I02
    | eapply seg_I03
    | eapply seg_I04
    | eapply seg_I05
    | eapply seg_I06
    | eapply seg_I07
    | eapply seg_I08
    | eapply seg_I09
    | eapply seg_I10
    | eapply seg_I11
    | eapply seg_J01
    | eapply seg_J02
    | eapply seg_J03
    | eapply seg_J04
    | eapply seg_J05
    | eapply seg_J06
    | eapply seg_J07
    | eapply seg_J08 ];
  eassumption.

Theorem slot_entry_holds : Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  apply (slot_entry B APIf ra empty); try (eapply loop_records); link_seg.
Qed.

End Link.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_identity.Statements.ubsan_halts.
Proof.
  destruct FrameProof.frame_ubsan_holds as (B & API & LS & SH & SK & ra & empty & H1 & H2 & H3 & H4 & H5 & H6 & H7 &
    H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H19v & H19d & H20 & H21 & H22 & H23 &
    H24 & H25 & H26 & H27 & H28 & H29 & HROOM & HALLOC & HLAST).
  assert (FF : frame_facts_u B API LS SH SK ra empty)
    by (unfold frame_facts_u; repeat (split; [first [assumption | repeat split; assumption]|]); assumption).
  apply (HLAST [] (fun _ _ => True)).
  - intros a (lo & len & Hin & _). destruct Hin.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j _.
    destruct (HALLOC rc fx) as (HMAL & HFREE & _).
    pose (RC0 := rzC_SR). pose (RA0 := rzA_SR B (API rc) HMAL HFREE).
    apply (slot_lib B API ra empty FF rzC_SR_realizes).
    { intros b n h. destruct (HROOM b n h) as (h1 & h2 & h3). cbn. unfold slot_room. rewrite h3. unfold CAPMAX. lia. }
    eapply (slot_entry_holds B API ra empty FF);
      first
        [ exact HMAL | exact HFREE
        | exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_init.reac_identity_init_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.memset.memset_holds)
        | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_ingest.reac_identity_ingest_holds
        | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_fw_str.reac_identity_fw_str_holds
        | exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_reac_ver_str.reac_identity_reac_ver_str_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.write_uint.write_uint_holds)
        | exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_catalogue_defect.reac_box_catalogue_defect_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.strcmp.strcmp_holds)
        | exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_family_of.reac_box_family_of_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.bcmp.bcmp_holds)
        | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_family_stem.reac_box_family_stem_holds
        | exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.check_str.check_str_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.strlen.strlen_holds)
        | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.put_dec.put_dec_holds
        | exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_name.reac_box_name_holds (OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.sb_dec.sb_dec_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.sb_ch.sb_ch_holds) OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.sb_ch.sb_ch_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.memcpy.memcpy_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.strlen.strlen_holds)
        | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_box_catalogue.reac_box_catalogue_holds
        | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.bcmp.bcmp_holds | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.memchr.memchr_holds | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.memcpy.memcpy_holds
        | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.strlen.strlen_holds | exact OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.strcmp.strcmp_holds ].
Qed.
