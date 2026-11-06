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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import FrameProof ZTraceSpec ZAllocator SlotAgree AllocRoom AllocCf SlotTopG AgreeZlib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import ULink.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import URzInst.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import AllocRoom.
From OSSVerify.libreac.fuzz_identity Require Statements.
Import ListNotations.
Open Scope Z_scope.

Lemma frame_facts_u_ag : forall {rc : RunCeil},
  frame_facts_u src0_msyms (@zlib_API) OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Agree.checksum_shape_ag
    src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  intros rc. unfold frame_facts_u.
  split; [exact ms_segs_rsegs|]. split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact errno_below_ceiling|].
  do 11 (split; [reflexivity|]).
  split; [split; [reflexivity | split; reflexivity]|].
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact ctx_not_ro|]. split; [exact frame_G_facts|]. split; [exact frame_RELRO_facts|].
  split; [intros pl fs K; reflexivity|]. split; [intros n b; reflexivity|].
  exact zlib_frame_allocator.
Qed.

Lemma cap_ag_same : OSSVerify.Proofs.libreac.fuzz_identity.lib.SlotAgree.CAP_AG = CAP_AG.
Proof. vm_compute. reflexivity. Qed.

Lemma cap_ag_range_u : 128 <= CAP_AG <= CAPMAX.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Theorem ubsan_slot_cg : forall (rc : RunCeil) (fx : FPState) j, (j < 4)%nat ->
  @lib_contract_cg fx rc OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Agree.checksum_shape_ag
    src0_msyms (@zlib_API rc) src0_sink_head src0_sink [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros rc fx j _.
  assert (LIM : forall L A mem md, aa_MR (@zlib_API rc) L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md))
    by (intros L A mem md H; exact (zlib_limit rc L A mem md H)).
  pose proof (@frame_facts_u_ag rc) as FF.
  pose (RC0 := rzC_CF).
  pose (RA0 := rzA_CF src0_msyms (@zlib_API rc) zlib_malloc_contract_cf zlib_free_contract_cf LIM).
  apply (slot_lib_cg src0_msyms (@zlib_API) RA_LIB EMPTY FF rzC_CF_crealizes).
  { intros b n (h1 & h2 & h3). pose proof cap_ag_range_u as HC.
    pose proof cap_ag_same as HE. cbn. unfold sroom_ag, slot_room. rewrite HE in h3.
    split; [split; [exact h1 | split; [exact h2 | lia]] | lia]. }
  eapply (slot_entry_holds src0_msyms (@zlib_API) RA_LIB EMPTY FF);
    first
      [ exact (OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.reac_identity_init.reac_identity_init_holds OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.memset.memset_holds)
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
