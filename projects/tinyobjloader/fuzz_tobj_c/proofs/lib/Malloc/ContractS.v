(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "True"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "nil"; "cons"; "pair"; "option"; "app"; "None"; "bool"; "true"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "rw"; "rm"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "vm_limit"; "m_vm_materialized"; "sp_window_lo"; "vm_init_sp"; "vm_maps"; "vm_reserved"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_s"; "ma_blocks"; "MA_init"; "ma_L"; "run_init"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "st_avail_meta_count"; "st_free_meta_head"; "st_init_done"; "MMAP_THRESHOLD"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "ROOMC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "segsP"; "segsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"; "EC_P"; "EC_U"; "MInvR"; "L_malloc_ok"; "Pre_malloc"; "top_var"; "mem_kept"; "tp_ok"; "JL_free"; "J_free_pre"; "L_free"; "Pre_free"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "drvN"; "JLi_ok"; "init_cost"; "initedT"; "malloc_cost"; "DRV_OPS"; "payload_cost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "J_am_pre"; "Pre_am"; "JL_am_ok"; "L_am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.WithSegs.Contracts"; "JLdS_ok"; "JLdS_free"; "JLdS_big_ok"; "J_big_S"; "J_free_S"; "J_init_S"; "J_payload_S"; "Post_init_S"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.WithSegs.AM"; "alloc_meta_avail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS"; "alloc_meta_avail"; "free_drv_S"; "malloc_big_S"; "malloc_init_S"; "malloc_payload_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesS"; "TR_angS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmPam"; "Pam_cnt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_P"; "IEC_U"; "auxv_init"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine"; "pristine_req"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary SymCall SymComplete ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocCalloc MallocIface Contract ContractI Pristine FreeGap
  ContractDrv VmRoom RoomS TRRulesK TRRulesS ContractAM ContractAMT AmPam DrvReach.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Plain.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Ubsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable C : mconsts.

Section AM.
Variable IE : ientry_consts.

Definition alloc_meta_avail : Prop := ltac2:(tb__ "0|2|
S35OF_;S7S2cA1ScS8S2cS6A2A1S6S6F_;S24S7S17A1S16OF_;F_;S12S3bVsegs;R7R2A3S5S4S1ScS2cA1S2eS25R4A1M0A1SeS2cA1A3A1S21Z0S2dG0A1A2A2S1SfS2fS25R5A1A1S10A3S36Vsegs;RaS3aVsegs;S53Vsegs;VC;R9R8R7R6R5A7S54VIE;A1R4A4S2bVsegs;S37R4SaS8S13S2aA2M1SbS13S2aS56VIE;A1S55Vsegs;VC;R9R8R7R6R5A7A4S9G1A1A3A4A4F_;F_;F_;Frho;FKc;FA;FU;FR;FX;Fok;").

Theorem AM_angS_of_avail : ltac2:(tb__ "0|2|
S61S35OF_;S7S17A1S16OF_;F_;S3cVsegs;R2R1A3OS7S2cA1ScS8S2cS6A2A1S6S6F_;S24S12S5S4S1ScS2cA1S2eS25R2A1M0A1SeS2cA1A3A1S21Z0M1S2dG0A1A2A2S1SfS2fS25R3A1A1S10A3S67Vsegs;RbG1S3aVsegs;S53Vsegs;VC;R7R6R5R4RaA7S54VIE;A1R3A4S2bVsegs;S37R3S60Vsegs;VC;VIE;R8S3R7R6R5R4RaAaA4A5F_;F_;Frho1;FA;FU;FR;FX;FNG;F_;FKc;Fok;F_;").
Proof using .
  intros HX ok Kc HS NG X R U A rho1 Hav Hinit. split; [lia|]. intros r Hr.
  set (Kr := fun tr md => Kc tr md /\ vm_roomS md (r + 0)).
  assert (HF : ok_frame segs ok Kr).
  { intros tr ms md ms' [HK _]. exact (proj1 HS tr ms md ms' HK). }
  eapply triple_conseq; [| | exact (HX ok X R U A Kr rho1 HF Hav Hinit)].
  - intros w [[Hsm HJ] HR]. split; [exact Hsm|].
    destruct HJ as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [split; [exact H3 | exact HR]|].
    split; [exact H4 | exact H5].
  - intros w (L & JL & rho' & Hin & Hag & Hsm & HJ). destruct Hin as [EQ | []]. injection EQ as <- <-.
    destruct HJ as (A' & m & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & [HK HR]).
    split.
    + exists (L_am_ok IE), (JL_am_okG segs C True X R U A Kc), rho'. split; [right; left; reflexivity|].
      split; [exact Hag|]. split; [exact Hsm|]. split; [exact I|]. exists A', m. repeat (split; [eassumption|]). exact HK.
    + unfold roomwS. replace r with (r + 0) by lia. exact HR.
Qed.

Theorem AM_cntS : ltac2:(tb__ "0|0|
S61S35OF_;S7S17A1S16OF_;F_;S3cVsegs;R2R1A3OS11S7S2cA1ScS8S2cS6A2A1S6S6F_;S24S12S68R6S25R2A1A2S67Vsegs;RbZ0S3aVsegs;S53Vsegs;VC;R6R5R4R3RaA7S54VIE;A1R2A4S2bVsegs;S37R2S60Vsegs;VC;VIE;R8S3R6R5R4R3RaAaA4A5F_;Frho1;FA;FU;FR;FX;Fn;FNG;F_;FKc;Fok;F_;").
Proof using .
  intros HX ok Kc HS NG n X R U A rho1 [HI HC]. apply (AM_angS_of_avail HX ok Kc HS NG X R U A rho1); [right; lia | exact HI].
Qed.
End AM.

Section Contracts.
Variable E : entry_consts.

Definition JLdS_ok (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|3|
S12S12S7S17A1S16S2S24S24S2S7S8S6S6A2M0A1M1G1S2G1G1S0S3fVsegs;VC;R3R6R4A5S0S4dVA;R3A2S0S4aVC;Vk;R3A3S0S33R4VX;A2S0S1G1S26R3A1SdG0R2SaG0SbS6S6S31Q40M2S14R6S49A2A2S31G2S14R7PcA2A2A4R1A3A3A3S0S1G1S26VA;A1SdG0R2R1A3A3S0S43Vsegs;VC;VA;R3S15R7A1S15R6A1A6VKc;R5R4A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Lemma JLdS_ok_JLi : ltac2:(tb__ "0|1|
S24S6S6S7S17A1M0S16OF_;F_;S12S12G0S16S57R8R7R6R5R4R3R2R1A8S4bVsegs;VC;R9R6R5R4R3R2A8F_;Fmd;Ftr;Frho';Frho0;FKc;FX;Fk;FA;").
Proof using .
  intros A k X Kc rho0 rho' tr md (A' & l1 & l2 & HM & Hi & _ & _ & HB' & HB & HK & HKc).
  exists A', l1, l2. split; [exact HM|]. split; [exact Hi|]. split; [exact HB'|]. split; [exact HB|]. split; [exact HK|exact HKc].
Qed.

Definition J_init_S (brk0 : run_init) (X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S12S7S17A1S16S0S6cVsegs;VC;Vbrk0;R3R1A5S0S1S6S31Q40S14R3PcA2A2Z10000A3S0VKc;R2R1A2S0S0S33R1VX;A2S1fS4cVX;A2A2S0S6bVsegs;VC;S28S27VC;Vbrk0;A2M0A1R3A4S42G0R3A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition Post_init_S (brk0 : run_init) (X : Z) (Kc : list event -> Model -> Prop) : sstate * jpost := ltac2:(tb__ "0|0|
SbS13S2aS40VE;A1S57S27VC;Vbrk0;A2S4fS23VX;S4cA2VKc;A4A4").

Definition malloc_init_S : Prop := ltac2:(tb__ "0|1|
S35OF_;S29S6S7S17A1S16OF_;F_;S12S3cVsegs;R5R2A3S36Vsegs;R6S3aVsegs;S5cR5R4R3A3S41VE;A1R2A4S2bVsegs;S37R2SaS8S13S2aA2M0S5eR5R4R3A3S9G0A1A3A4A4F_;Frho;FKc;FX;Fbrk0;Fok;").

Definition J_big_S (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S12S7S17A1S16S0S3fVsegs;VC;VA;R3R1A5S0S4aVC;Vk;VA;A3S0S21Z0Vk;A2S0S0S1fS30S31Q40S14R3PcA2A2M0A2S1fG0S20Z2Z1aA2A2A2S0VKc;R2R1A2S0S0S33R1VX;A2S1fS4eG0A1VX;A2A2S0S44VC;R3A2S42VA;R3A2A2A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition JLdS_big_ok (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|0|
S12S12S7S17A1S16S57VA;S23Vk;Z1A2S23VX;S4eS31Q40S14R4PcA2A2A1A2VKc;R4R3R2R1A8Lmd;Ltr;Lrho';Lrho0;").

Definition malloc_big_S : Prop := ltac2:(tb__ "0|1|
S35OF_;S24S6S6S7S17A1S16OF_;F_;S12S3cVsegs;R6R2A3S36Vsegs;R7S3aVsegs;S5aR6R5R4R3A4S41VE;A1R2A4S2bVsegs;S37R2SaS8S13S2aA2M0SbS13S2aS40VE;A1S59R6R5R4R3A4A4S9G0A1A3A4A4F_;Frho;FKc;FX;Fk;FA;Fok;").

Definition J_free_S (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|0|
S12S7S17A1S16S0S46Vsegs;VC;VA;VKc;R3R2R1A7S0S4aVC;Vk;VA;A3S0S21Z0Vk;A2S33R1VX;A2A2A2A2Lmd;Ltr;Lrho;").

Definition JLdS_free (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|3|
S12S12S7S17A1S16S2S24S24S2S7S8S6S6A2M0A1M1G1S2G1G1S0S3fVsegs;VC;R3R6R4A5S0S4dVA;R3A2S0S4aVC;Vk;R3A3S0S33R4VX;A2S0S1G1S26VA;A1SdG0R2SaG0SbS6S6S31Q40M2S14R7PcA2A2S31G2S14R7PdA2A2A4R1A3A3A3S0S1G1S26R3A1SdG0R2R1A3A3S0S43Vsegs;VC;VA;R3S15R7A1S15R6A1A6VKc;R5R4A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition free_drv_S : Prop := ltac2:(tb__ "0|1|
S35OF_;S24S6S6S7S17A1S16OF_;F_;S12S3cVsegs;R6R2A3S36Vsegs;R7S3aVsegs;S5bR6R5R4R3A4S48VE;A1R2A4S2bVsegs;S37R2SaS8S13S2aA2M0SbS13S2aS47VE;A1S58R6S23R5Z1A2R4R3A4A4S9G0A1A3A4A4F_;Frho;FKc;FX;Fk;FA;Fok;").

Lemma JLdS_free_JL : ltac2:(tb__ "0|1|
S24S6S6S7S17A1M0S16OF_;F_;S12S12G0S16S58R8R7R6R5R4R3R2R1A8S45Vsegs;VC;R9R6R5R4R3R2A8F_;Fmd;Ftr;Frho';Frho0;FKc;FX;Fk;FA;").
Proof using .
  intros A k X Kc rho0 rho' tr md (A' & l1 & l2 & HM & Hi & _ & _ & HB & HB' & HK & HKc).
  exists A', l1, l2. split; [exact HM|]. split; [exact HB|]. split; [exact HB'|]. split; [exact HK|]. split; [exact (conj (fun _ => proj1 Hi) (proj2 Hi))|exact HKc].
Qed.

Definition J_payload_S (A : MA) (k X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S12S7S17A1S16S0S3fVsegs;VC;VA;R3R1A5S0S4aVC;Vk;VA;A3S0S0S21Z0S31Q40S14R3PcA2A2M0A2S1fG0S20Z2Z1aA2A2A2S0VKc;R2R1A2S0S0S33R1VX;A2S1fS50G0A1VX;A2A2S0S44VC;R3A2S42VA;R3A2A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition malloc_payload_S : Prop := ltac2:(tb__ "0|1|
S35OF_;S24S6S6S7S17A1S16OF_;F_;S12S3cVsegs;R6R2A3S36Vsegs;R7S3aVsegs;S5dR6R5R4R3A4S41VE;A1R2A4S2bVsegs;S37R2SaS8S13S2aA2M0SbS13S2aS40VE;A1S4bVsegs;VC;R6R3A4A4S9G0A1A3A4A4F_;Frho;FKc;FX;Fk;FA;Fok;").

End Contracts.
End WithSegs.

Definition alloc_meta_avail_P : Prop := ltac2:(tb__ "0|0|
S62S38S51S69A3").
Definition alloc_meta_avail_U : Prop := ltac2:(tb__ "0|0|
S62S39S52S6aA3").
Definition malloc_init_S_P : Prop := ltac2:(tb__ "0|0|
S65S38S51S3dA3").
Definition malloc_init_S_U : Prop := ltac2:(tb__ "0|0|
S65S39S52S3eA3").
Definition malloc_big_S_P : Prop := ltac2:(tb__ "0|0|
S64S38S51S3dA3").
Definition malloc_big_S_U : Prop := ltac2:(tb__ "0|0|
S64S39S52S3eA3").
Definition free_drv_S_P : Prop := ltac2:(tb__ "0|0|
S63S38S51S3dA3").
Definition free_drv_S_U : Prop := ltac2:(tb__ "0|0|
S63S39S52S3eA3").
Definition malloc_payload_S_P : Prop := ltac2:(tb__ "0|0|
S66S38S51S3dA3").
Definition malloc_payload_S_U : Prop := ltac2:(tb__ "0|0|
S66S39S52S3eA3").

Lemma reserved_len_P : (length (segments_reserved segsP) <= 8)%nat.
Proof. vm_compute. repeat constructor. Qed.
Lemma reserved_len_U : (length (segments_reserved segsU) <= 8)%nat.
Proof. vm_compute. repeat constructor. Qed.

Theorem vm_roomS_init_P : ltac2:(tb__ "0|5|
S16S6S1S7S8S32Q40M0A1M1G1A2M2A1M3S1eS18R2A1A1S5fS38A1A3S1G3S1dS18R3A1A1S9G2A1A3S1S7G1A1S1aR4A1S9G1A1A3S1fZ0R4A2S1fS22R5S20Z2M4Z14A2A2S19S18R6A1A1A2S1fS19S18R7A1A1S20G4Z28A2A2S1fS22R7S20G4Z10A2A2S34A2S1fS1bS31G0S1cS18R9A1A1A2A2S33RaR9A2F_;F_;F_;F_;F_;F_;F_;F_;FX;Fmd;").
Proof.
  intros md X Hres Hmaps Hmat HX Hlim Hlim' HXC Hsp. apply vm_roomS_init; auto.
  - rewrite Hres. exact reserved_len_P.
  - rewrite Hres. exact reserved_total_P.
  - unfold alloc_top, stack_max_size, sp_window_lo in *. lia.
Qed.

Theorem vm_roomS_init_U : ltac2:(tb__ "0|5|
S16S6S1S7S8S32Q40M0A1M1G1A2M2A1M3S1eS18R2A1A1S5fS39A1A3S1G3S1dS18R3A1A1S9G2A1A3S1S7G1A1S1aR4A1S9G1A1A3S1fZ0R4A2S1fS22R5S20Z2M4Z14A2A2S19S18R6A1A1A2S1fS19S18R7A1A1S20G4Z28A2A2S1fS22R7S20G4Z10A2A2S34A2S1fS1bS31G0S1cS18R9A1A1A2A2S33RaR9A2F_;F_;F_;F_;F_;F_;F_;F_;FX;Fmd;").
Proof.
  intros md X Hres Hmaps Hmat HX Hlim Hlim' HXC Hsp. apply vm_roomS_init; auto.
  - rewrite Hres. exact reserved_len_U.
  - rewrite Hres. exact reserved_total_U.
  - unfold alloc_top, stack_max_size, sp_window_lo in *. lia.
Qed.
