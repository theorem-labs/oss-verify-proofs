From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv
  reac_identity_init_c reac_identity_ingest_c reac_identity_fw_str_c reac_identity_reac_ver_str_c
  reac_box_catalogue_defect_c reac_box_family_of_c reac_box_family_stem_c check_str_c put_dec_c
  reac_box_name_c reac_box_catalogue_c bcmp_c memchr_c memcpy_c strlen_c strcmp_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import
  A01 A02 A03 A04 A05 A06 A07 A08 A09 B01 B02 B03 B04 B05 B06 B07 B08 B09 B10 B11 B12 B13 B14 B15 B16 B17 B18 B19
  B20 B21 B22 B23 B24 B25 B26 B27 B28 B29 C01 C02 C03 C04 C05 D01 E01 E02 E03 E04 E05 E06 E07 E08 E09 E10 F01 F02
  F03 F04 G01 G02 G03 G04 G05 G06 G07 H01 H02 H03 H04 H05 H06 H07 H08 H09 H10 H11 H12 H13 H14 H15 H16 H17 H17x
  I01 I02 I03 I04 I05 I06 I07 I08 I09 I10 I11 J01 J02 J03 J04 J05 J06 J07 J08 B00 Asm Slot.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_init reac_identity_ingest
  reac_identity_fw_str reac_identity_reac_ver_str write_uint reac_box_catalogue_defect reac_box_family_of
  reac_box_family_stem check_str put_dec reac_box_name sb_dec reac_box_catalogue bcmp memchr memcpy memset strlen strcmp.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import FrameProof ZTraceSpec ZAllocator SlotAgree AllocRoom AgreeZlib SlotTopG.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Link.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP URzInstP.
From OSSVerify.libreac.fuzz_identity Require Statements.
Import ListNotations.
Open Scope Z_scope.


#[global] Instance checksum_shape_ag : lib_shape.
Proof.
  refine {| LIBK := fun pl fs K => K (LL 0 fs []);
    lib_delta := fun n b => b;
    lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG |}.
  intros pl fs K K' H. apply H.
Defined.

Lemma CAP_AG_range : 128 <= CAP_AG <= CAPMAX.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Lemma room_calls_ag : forall n k, @room_calls checksum_shape_ag n k SBD_AG.
Proof.
  intros n k. pose proof CAP_AG_range as HC. induction k as [|k IH]; cbn [room_calls]; [exact I|].
  split; [|exact IH]. cbn. unfold SBD_AG. cbn [sb_live sb_bytes sb_cap]. lia.
Qed.

Lemma frame_facts_ag : forall {rc : RunCeil}, frame_facts src0_msyms (@zlib_API) checksum_shape_ag src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  intros rc. unfold frame_facts.
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

Theorem plain_slot_ag : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_g fx rc checksum_shape_ag src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    [] frame_RELRO (fun _ _ => True) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros rc fx j _.
  pose proof (@frame_facts_ag rc) as FF.
  destruct (zlib_frame_allocator rc fx) as (HMAL & HFREE & _).
  pose (RC0 := rzC_SR). pose (RA0 := rzA_SR src0_msyms (@zlib_API rc) HMAL HFREE).
  apply (slot_lib src0_msyms (@zlib_API) RA_LIB EMPTY FF rzC_SR_realizes).
  { intros b n (h1 & h2 & h3). pose proof CAP_AG_range as HC. cbn. unfold slot_room. lia. }
  eapply (slot_entry_holds src0_msyms (@zlib_API) RA_LIB EMPTY FF);
    first
      [ exact (reac_identity_init.reac_identity_init_holds memset.memset_holds)
        | exact reac_identity_ingest.reac_identity_ingest_holds
        | exact reac_identity_fw_str.reac_identity_fw_str_holds
        | exact (reac_identity_reac_ver_str.reac_identity_reac_ver_str_holds write_uint.write_uint_holds)
        | exact (reac_box_catalogue_defect.reac_box_catalogue_defect_holds strcmp.strcmp_holds)
        | exact (reac_box_family_of.reac_box_family_of_holds bcmp.bcmp_holds)
        | exact reac_box_family_stem.reac_box_family_stem_holds
        | exact (check_str.check_str_holds strlen.strlen_holds)
        | exact (put_dec.put_dec_holds memset.memset_holds)
        | exact (reac_box_name.reac_box_name_holds sb_dec.sb_dec_holds memcpy.memcpy_holds strlen.strlen_holds)
        | exact reac_box_catalogue.reac_box_catalogue_holds
        | exact bcmp.bcmp_holds | exact memchr.memchr_holds | exact memcpy.memcpy_holds
        | exact strlen.strlen_holds | exact strcmp.strcmp_holds ].
Qed.
