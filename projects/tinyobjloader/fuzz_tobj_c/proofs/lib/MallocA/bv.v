(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl CDepotCall bw.

(* [comment removed for export] *)
Module InvQ10b.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "mul"; "div"; "pow"; "modulo"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_geom"; "aa_sec"; "sc_map_beg"; "sc_map_size"; "ag_pab"; "ag_spacebeg"; "aa_live"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_thread"; "aa_cls"; "aa_depot"; "class_state"; "cs_empty"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "maskv"; "cell_ok"; "mkACell"; "acell"; "c_addr"; "c_w"; "restrictv"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b"; "RZ"; "newZc"; "lst_cell"; "@Corelib.Init.Datatypes"; "option"; "Some"; "nat"; "length"; "prod"; "bool"; "false"; "pair"; "None"; "list"; "snd"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "SEC_INST"; "secondary_repr"; "QG"; "bandtp_inv"; "fs_inv"; "primary_repr"; "thread_inv"; "depot_wf"; "geom_ok"; "ia_inv"; "inv3"; "live_block_repr"; "live_sep"; "misc_inv"; "nthZ"; "@Stdlib.Lists.List"; "nth_error"; "In"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "PG"; "is_primary"; "kQuarantineMin"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "sec_junk_zone"; "chunk_zone"; "sec_tbl_zone"; "unmap_sec"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "cls_foot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "set_q"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt SoundA SummaryA MmapFixedA MmapFixedA2 MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.RebuildS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.InvQ10a.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition RZ (A : AA) (i : nat) (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|0|
SdS52Vz;A1SdS54VA;Vi;Vz;A3SdS53Vch;Vz;A2S51Vch;Vz;A2A2A2A2").
Definition newZc (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|0|
SdS53Vch;Vz;A2S51Vch;Vz;A2A2").
Definition lst_cell (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|2|
SeSfSfSaSbS2dSfA1S49SfS11VA;A1M0S56S30SfG0A2U1A2A3S2eSfR1A2A3SaS0S1S12R1A1M1Z18A2Vz;A2S2Vz;S1G1Z20A2A2A2A2Llst;A2").

Section Geo.
Variables (A : AA) (m : bview).
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HLS : live_sep A.
Hypothesis HPR : primary_repr m A.
Hypothesis HSR : secondary_repr m A.
Hypothesis HI3 : inv3 A.
Local Abbreviation G := (aa_geom A).
Local Abbreviation T := (ag_thread (aa_geom A)).
Local Abbreviation SB := (ag_spacebeg (aa_geom A)).
Local Abbreviation PAB := (ag_pab (aa_geom A)).

Lemma ch_nums : ltac2:(tb__ "0|5|
S2fSfSbS2dSfA1S49SfS11VA;A1R2A3S2eSfR1A2A3SaS0Z646000S12R2A1M0A2SaS2Z11000S13R2A1M1A2SaS0S1G0G1A2M2Z7fffff800000A2SaSdS0G2Z7fff7000A2S0Z10007fff8000G0A2A2SaSbS9S7G0Z8M3A2Z0M4A3SaSbS9S7G1G3A2G4A3SbS9S4cG2A1S1S4cG0A1S5G1G3A2A2A3A2A2A2A2A2A2F_;Fc;Fj;").
Proof.
  intros j c Hj. destruct HSR as (S1 & _). destruct (S1 j c Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (topG_range G) as TG. unfold PG in *.
  pose proof (dyn_in_big _ _ _ D10 ltac:(lia)) as BI. unfold IMG_HI in BI. destruct D10 as (_ & _ & _ & _ & DB).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DB.
  assert (M8 : forall x, x mod 4096 = 0 -> x mod 8 = 0).
  { intros x Hx. pose proof (Z.div_mod x 4096 ltac:(lia)) as X. rewrite Hx, Z.add_0_r in X. rewrite X. replace (4096 * (x / 4096)) with ((512 * (x / 4096)) * 8) by lia. apply Z_mod_mult. }
  split; [exact BI|]. split; [lia|]. split; [lia|]. split; [exact DB|]. split; [exact (M8 _ D6)|]. split; [exact (M8 _ D7)|].
  unfold Sh. pose proof (Z.div_mod (sc_map_size c) 8 ltac:(lia)) as DL. rewrite (M8 _ D7), Z.add_0_r in DL. rewrite DL at 1.
  rewrite Z.mul_comm, Z.div_add by lia. lia.
Qed.

Lemma NZ_app : ltac2:(tb__ "0|2|
S2fSfS9S9S9SbS2dSfA1S49SfS11VA;A1R5A3S2eSfR4A2A3S0Z0R4A2M0G0S0S1R6R5A2Z7fffff800000A2SdS0S1R7R6A2S12R8A1M1A2S0S1G1S13R8A1A2R7A2A2SdS0S1R8R7A2Z7fff7000A2S0Z10007fff8000R8A2A2SaS0R9R7A2S2R7S1R9R8A2A2A2ScS2bRbR8A2A1F_;F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;Fc;Fj;").
Proof.
  intros j c lo len z Hj H1 H2 H3 H4 H5 Hz X. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  apply (app_new (sc_map_beg c) (sc_map_size c) N6 ltac:(lia) ltac:(unfold IMG_HI; lia) N3 ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact N4)
                 lo len z H1 H2 H3 H4 ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact H5) Hz).
  unfold newZ. unfold newZc, chunk_zone, chunk_sh_zone in X. rewrite N7 in X. exact X.
Qed.
Lemma NZ_sh2 : ltac2:(tb__ "0|1|
S2fSfS9S9S9SbS2dSfA1S49SfS11VA;A1R5A3S2eSfR4A2A3S0Z0R4A2SaS0R5R4A2S0R4Z7fffff800000A2A2SdS0R5S12R7A1M0A2S0S1G0S13R7A1A2R6A2A2SaS0S4cR7A1R5A2S2R5S4cR6A1A2A2ScS2bR9R6A2A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;Fc;Fj;").
Proof.
  intros j c lo hi z Hj H1 H2 H3 Hz X. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  apply (sh2_new (sc_map_beg c) (sc_map_size c) N5 N6 ltac:(lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact N4) lo hi z H1 H2 H3 Hz).
  unfold newZ. unfold newZc, chunk_zone, chunk_sh_zone in X. rewrite N7 in X. exact X.
Qed.
Lemma NZ_sh : ltac2:(tb__ "0|3|
S2fSfS9S9S9SbS2dSfA1S49SfS11VA;A1R5A3S2eSfR4A2A3S0Z0R4A2M0G0S0S1R6R5A2Z7fffff800000A2SdS0S1R7R6A2S12R8A1M1A2S0S1G1S13R8A1A2R7A2A2SaS0S4cR8A1M2R6A2S2R6S1G2S5S1R7Z7A2Z8A2A2A2A2ScS2bRaR7A2A1F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;Fc;Fj;").
Proof.
  intros j c lo len z Hj H1 H2 H3 H4 Hz X. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  apply (sh_new (sc_map_beg c) (sc_map_size c) N5 N6 ltac:(lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact N4) lo len z H1 H2 H3 H4 Hz).
  unfold newZ. unfold newZc, chunk_zone, chunk_sh_zone in X. rewrite N7 in X. exact X.
Qed.

Variables (i : nat) (ch : sec_chunk).
Hypothesis Hi : ltac2:(tb__ "0|0|
SbS2dSfA1S49SfS11VA;A1Vi;A3S2eSfVch;A2A3").

Lemma pab_nums : ltac2:(tb__ "0|3|
SaS0Z646000S14S10VA;A1A1M0A2SaS0S1G0Z800000M1A2M2Z7fffff800000A2SaSdS0G2Z7fff7000A2S0Z10007fff8000G0A2A2S0S4Z8S3S30SfS11VA;A1A2A1A2G1A2A2A2A2").
Proof.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & P4 & _). pose proof (topG_range G) as TG.
  unfold IMG_HI, kPtrArrayReserve, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. repeat split; lia.
Qed.

Lemma nRZ_low : ltac2:(tb__ "0|0|
S9S2R1Z646000A2ScSaS0S1S3aZ38A2R2A2S2R2Zee070A2A2A1ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;").
Proof.
  intros z Hz NW X. destruct pab_nums as (P1 & _). destruct (ch_nums i ch Hi) as (N1 & _).
  destruct X as [X|[X|[X|X]]].
  - unfold sec_junk_zone, SEC_INST in *. lia.
  - destruct X as [X|[X|[X|(lst & Hl & X)]]]; [unfold SEC_INST in *; lia | unfold SEC_INST in *; lia | lia |].
    destruct (ch_nums _ lst Hl) as (L1 & _). lia.
  - unfold chunk_zone in X. lia.
  - unfold chunk_sh_zone, Sh, SHADOW_OFF in X. pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma nRZ_high : ltac2:(tb__ "0|2|
S9S0Z646000R1A2ScSaS0S1S14S10VA;A1A1S4Z8M0S3Vi;A1A2A2M1R2A2S2R2S1G1G0A2A2A2A1ScS2cVA;R3A2A1ScS2bVch;R4A2A1ScS2aVA;Vi;Vch;R5A4A1F_;F_;F_;F_;Fz;").
Proof.
  intros z Hz NP NL NN X. destruct X as [X|[X|X]].
  - unfold sec_junk_zone, SEC_INST in X. lia.
  - destruct X as [X|[X|[X|X]]]; [unfold SEC_INST in X; lia | lia | exact (NP X) | exact (NL X)].
  - exact (NN X).
Qed.
Lemma cell_in_pab : ltac2:(tb__ "0|3|
S9SaS0S1S14S10VA;A1A1M0S4Z8M1S3Vi;A1A2A2M2R1A2S2R1S1G2G1A2A2A2SaS0G0R2A2S2R2S1G0Z800000A2A2A2F_;Fz;").
Proof.
  intros z Hz. destruct pab_nums as (_ & _ & _ & P4). pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite Hi; discriminate)) as LI. lia.
Qed.

Lemma nRZ_block : ltac2:(tb__ "0|3|
S9S9S9S0Z0M0R3A2S2G0R3A2S0S1R5R4A2Z7fffff800000A2SdS0S1R6R5A2Z10000A2S0Z646000R6A2A2SdS0S1R7R6A2Z7fff7000A2S0Z10007fff8000R7A2A2SdS0S1R8R7A2S14S10VA;A1A1M1A2S0S1G1Z800000A2R8A2A2S2fSfSbS2dSfA1S49SfS11VA;A1R2A3S2eSfR1A2A3SdS0S1RcRbA2S12R2A1M2A2S0S1G2S13R2A1A2RcA2A2F_;Fc;Fj;SaS0RaR8A2S2R8S1RaR9A2A2A2ScS2aVA;Vi;Vch;R9A4A1F_;F_;F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z H0 Hl HT HI HB HP HC Hz.
  destruct (Z_lt_dec z 6578176) as [LO|HI'].
  - apply nRZ_low; [exact LO|]. unfold SEC_INST. lia.
  - apply nRZ_high; [lia | | |].
    + intros X. pose proof (cell_in_pab z X). lia.
    + intros (lst & Hl2 & X). destruct (ch_nums _ lst Hl2) as (_ & L2 & _). pose proof (HC _ lst Hl2). lia.
    + apply (NZ_app i ch lo len z Hi); try lia. exact (HC i ch Hi).
Qed.

Lemma band_nRZ : ltac2:(tb__ "0|0|
S9SaS0Z7fff7000R1A2S2R1Z10007fff8000A2A2ScS2bVch;R2A2A1ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;").
Proof.
  intros z Hz NN. apply nRZ_high; [lia | | | exact NN].
  - intros X. pose proof (cell_in_pab z X). destruct pab_nums as (_ & _ & P3 & _). lia.
  - intros (lst & Hl & X). destruct (ch_nums _ lst Hl) as (_ & L2 & _ & L4 & _). lia.
Qed.
Lemma nRZ_sh2 : ltac2:(tb__ "0|1|
S9S9S9S0Z0R3A2SaS0R4R3A2S0R3Z7fffff800000A2A2SdS0R4S12Vch;A1M0A2S0S1G0S13Vch;A1A2R5A2A2SaS0S4cR6A1R4A2S2R4S4cR5A1A2A2ScS2aVA;Vi;Vch;R5A4A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H0 H1 H2 Hz. pose proof (sh_run_band2 lo hi z H0 H1 Hz) as B. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B.
  apply band_nRZ; [exact B|]. exact (NZ_sh2 i ch lo hi z Hi H0 H1 H2 Hz).
Qed.
Lemma nRZ_sh : ltac2:(tb__ "0|3|
S9S9S9S0Z0R3A2M0G0S0S1R5R4A2Z7fffff800000A2SdS0S1R6R5A2S12Vch;A1M1A2S0S1G1S13Vch;A1A2R6A2A2SaS0S4cR7A1M2R5A2S2R5S1G2S5S1R6Z7A2Z8A2A2A2A2ScS2aVA;Vi;Vch;R6A4A1F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z H0 H1 H2 H3 Hz. pose proof (sh_run_band lo len z H0 H1 H2 Hz) as B. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B.
  apply band_nRZ; [exact B|]. exact (NZ_sh i ch lo len z Hi H0 H1 H2 H3 Hz).
Qed.

Lemma sec3 : ltac2:(tb__ "0|a|
S2fSfSbS2dSfA1S49SfS11VA;A1R2A3S2eSfR1A2A3SaSdS0S1S12R2A1M0S13R2A1A2M1S15S10VA;A1M2A1M3A2S0S1S1G3S6Z2Z25A2A2Z1000M4A2G0A2A2SaSdS0G1S1aG2A1M5A2S0S1G5G4A2G0A2A2SaSdS0G1S14G2A1M6A2S0S1G6Z800000A2G0A2A2SaSdS0G1S19G2A1M7A2S0S1G7Zb09000A2G0A2A2SaSdS0G1S17G2A1M8A2S0S1G8G4A2G0A2A2SdS0G1S18G2A1M9A2S0S1G9G4A2G0A2A2A2A2A2A2A2F_;Fc;Fj;").
Proof.
  intros j c Hj. destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (X1 & X2 & X3 & X4 & _ & X6 & X7).
  rewrite kSpaceSize_val in X1. rewrite FS_total_val in X4. unfold kPtrArrayReserve in X3. repeat split; assumption.
Qed.
Lemma nRZ_T : ltac2:(tb__ "0|1|
S9SaS0S1aS10VA;A1A1M0R1A2S2R1S1G0Z1000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_numsS _ HG) as (_ & _ & _ & T1 & T2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _). destruct HI3 as ((_ & _ & _ & _ & PT & _) & _).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI, kPtrArrayReserve in *.
  apply (nRZ_block T 4096 z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (_ & X & _). lia.
Qed.
Lemma nRZ_ctx : ltac2:(tb__ "0|1|
S9SaS0S17S10VA;A1A1M0R1A2S2R1S1G0Z1000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_numsS _ HG) as (_ & _ & _ & _ & _ & C1 & C2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & _ & CB & _ & _ & CI & _). destruct HI3 as ((_ & _ & _ & _ & _ & _ & PC & _) & _).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI, kPtrArrayReserve in *.
  apply (nRZ_block (ag_ctx G) 4096 z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (_ & _ & _ & _ & X & _). lia.
Qed.
Lemma nRZ_dtls : ltac2:(tb__ "0|1|
S9SaS0S18S10VA;A1A1M0R1A2S2R1S1G0Z1000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_numsS _ HG) as (_ & _ & _ & _ & _ & _ & _ & D1 & D2 & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & _ & _ & DB & _ & _ & DI). destruct HI3 as ((_ & _ & _ & _ & _ & _ & _ & PD) & _).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI, kPtrArrayReserve in *.
  apply (nRZ_block (ag_dtls G) 4096 z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (_ & _ & _ & _ & _ & X). lia.
Qed.
Lemma nRZ_fsb : ltac2:(tb__ "0|1|
S9SaS0S19S10VA;A1A1M0R1A2S2R1S1G0Zb09000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_numsS _ HG) as (_ & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (FB & _). destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). rewrite FS_total_val in FB, PF.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI, kPtrArrayReserve in *.
  apply (nRZ_block (ag_fsb G) 11571200 z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (_ & _ & _ & X & _). lia.
Qed.
Lemma space_nums : ltac2:(tb__ "0|1|
SaS0Z10007fff8000S15S10VA;A1A1M0A2SaS0S1S1G0S6Z2Z25A2A2Z1000A2Z7fffff800000A2SbS9S7G0Z8A2Z0A3A2A2").
Proof.
  pose proof (geom_old _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16 & S1 & S2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1. split; [exact S1|]. split; [lia|].
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ 16)); [exists (2 ^ 13); reflexivity | apply Z.mod_divide; [lia | exact S16]].
Qed.
Lemma nRZ_space : ltac2:(tb__ "0|1|
S9SaS0S15S10VA;A1A1M0R1A2S2R1S1S1G0S6Z2Z25A2A2Z1000A2A2A2ScS2aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. destruct space_nums as (S1 & S2 & _). destruct HI3 as ((_ & _ & _ & PS & _) & _). rewrite kSpaceSize_val in PS. unfold kPtrArrayReserve in PS.
  apply (nRZ_block SB (2 ^ 37 + 4096) z); try lia. intros j c Hj. destruct (sec3 j c Hj) as (X & _). lia.
Qed.
Lemma nRZ_space_sh : ltac2:(tb__ "0|1|
S9S9S9S0S15S10VA;A1A1M0R3A2S0R4R3A2S0R4S1S1G0S6Z2Z25A2A2Z1000A2A2SaS0S4cR6A1R4A2S2R4S4cR5A1A2A2ScS2aVA;Vi;Vch;R5A4A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H1 H2 H3 Hz. destruct space_nums as (S1 & S2 & _). destruct (sec3 i ch Hi) as (X & _).
  apply (nRZ_sh2 lo hi z); first [lia | assumption].
Qed.
Lemma nRZ_pab : ltac2:(tb__ "0|3|
S9SaS0S14S10VA;A1A1M0R1A2S2R1S1G0Z800000A2A2A2ScSaS0S1G0S4Z8M1S3Vi;A1A2A2M2R2A2S2R2S1G2G1A2A2A2A1ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;").
Proof.
  intros z Hz NC. destruct pab_nums as (P1 & P2 & P3 & _). apply nRZ_high; [lia | exact NC | |].
  - intros (lst & Hl & X). destruct (sec3 _ lst Hl) as (_ & _ & X3 & _). destruct (ch_nums _ lst Hl) as (_ & L2 & _). lia.
  - destruct (sec3 i ch Hi) as (_ & _ & X3 & _). apply (NZ_app i ch PAB 8388608 z Hi); lia.
Qed.

Lemma nRZ_chunk : ltac2:(tb__ "0|3|
S2fSfS9SbS2dSfA1S49SfS11VA;A1M0R3A3S2eSfR2A2A3ScSbS2fR4Vi;A3A1SaS0S12R4A1M1R3A2S2R3S1G1S13R4A1A2A2A2SbS2fR6S56S30SfG0A2U1A2A3ScSaS0S1S12R6A1M2Z18A2R5A2S2R5S1G2Z20A2A2A2A1F_;ScS2aVA;Vi;Vch;R5A4A1F_;F_;F_;F_;Fz;Fc;Fj;").
Proof.
  intros j c z Hj Nji Hz NC. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & _). destruct (sec3 j c Hj) as (_ & _ & X3 & _).
  destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _).
  apply nRZ_high; [lia | | |].
  - intros X. pose proof (cell_in_pab z X). lia.
  - intros (lst & Hl & X). destruct (Nat.eq_dec j (length (aa_sec A) - 1)) as [E|NE].
    + pose proof Hl as Hl'. rewrite <- E, Hj in Hl'. injection Hl' as <-. exact (NC E X).
    + destruct (ch_nums _ lst Hl) as (_ & L2 & _). pose proof (X5 _ lst Hl NE). lia.
  - apply (NZ_app i ch (sc_map_beg c) (sc_map_size c) z Hi); try lia. pose proof (X5 i ch Hi Nji). lia.
Qed.
Lemma nRZ_chunk_sh : ltac2:(tb__ "0|1|
S2fSfS9SbS2dSfA1S49SfS11VA;A1R3A3S2eSfR2A2A3ScSbS2fR4Vi;A3A1SaS0S4cS12R4A1M0A1R3A2S2R3S4cS1G0S13R4A1A2A1A2A2ScS2aVA;Vi;Vch;R4A4A1F_;F_;F_;Fz;Fc;Fj;").
Proof.
  intros j c z Hj Nji Hz. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & N4 & _).
  destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _). pose proof (X5 i ch Hi Nji).
  apply (nRZ_sh2 (sc_map_beg c) (sc_map_beg c + sc_map_size c) z); first [lia | assumption].
Qed.

Lemma nRZ_dblock : ltac2:(tb__ "0|2|
S31S9S9A2M0S9S4aG0R2S5aS1cVA;A1A1A3S2Zf000S37S9S9R3A3A2SaS0S38S9S9R4A3M1R3A2S2R3S1G1S37S9S9R4A3A2A2A2ScS2aVA;Vi;Vch;R4A4A1F_;F_;F_;Fz;Fbn;").
Proof.
  intros bn z Hbn HL Hz. destruct HI3 as (_ & _ & _ & _ & DEP3 & _). destruct (DEP3 bn Hbn) as (DY & _ & _ & _ & _ & _ & SP & SC).
  pose proof (dyn_in_big _ _ _ DY HL) as BB. destruct DY as (D1 & D2 & D3 & _ & D5). pose proof (topG_range G) as TG.
  unfold sepZ in SP. cbn [fst snd] in SP. unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve in *.
  apply (nRZ_block (fst bn) (snd bn) z); try lia. intros j c Hj. pose proof (SC c (nth_error_In _ _ Hj)) as S. unfold sepZ in S. cbn [fst snd] in S. lia.
Qed.

Lemma RZ_fs : ltac2:(tb__ "0|0|
S9S2aVA;Vi;Vch;R1A4SbS32S39S10VA;A1R2A2S33A3F_;Fz;").
Proof.
  intros z HZ. destruct (fs_footb G z) eqn:E; [|reflexivity]. exfalso. revert HZ.
  pose proof (geom_numsS _ HG) as (_ & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  unfold fs_footb in E. cbv zeta in E. rewrite FS_total_val, FS_frames_off_val, FS_kFlagsOffset_val in E.
  apply orb_prop in E as [E|E]; [apply orb_prop in E as [E|E]|]; apply andb_prop in E as [X Y]; apply Z.leb_le in X; apply Z.ltb_lt in Y.
  - apply nRZ_fsb. lia.
  - apply nRZ_fsb. lia.
  - destruct (sec3 i ch Hi) as (_ & _ & _ & X4 & _). apply (nRZ_sh2 (ag_fsb G + 36864) (ag_fsb G + 11571200) z); try lia.
Qed.

Lemma nRZ_cls : ltac2:(tb__ "0|0|
S9S9SaS0Z1R2A2S0R2Z1eA2A2S59S10VA;A1R3S48S1dS1bVA;A1R3S1eA4R2A4ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;Fc;").
Proof.
  intros c z Hc Hz. destruct space_nums as (S1 & S2 & _).
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  unfold cls_foot in Hz. cbv zeta in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - apply nRZ_space. clear -Hz Hc. lia.
  - apply nRZ_space. clear -Hz Hc M5 M6. nia.
  - apply nRZ_space. clear -Hz Hc M1 M2 M3. nia.
  - apply (nRZ_space_sh (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); [clear -Hc; nia | clear -M1 M2; lia | clear -Hc M1 M2 M3; nia | exact Hz].
  - apply nRZ_T. clear -Hz Hc. lia.
Qed.

Hypothesis HNL : ltac2:(tb__ "0|0|
S9S9S4aS31S9S9A2S34S9S9R2R1A4S16VA;A1A3SbS32S4eR2A1S33A3ScSbS9R4S1S1S12Vch;A1S4dA2Z800A2A3A1F_;F_;Fn;Fb;").
Lemma nRZ_live : ltac2:(tb__ "0|1|
S9S9S9S4aS31S9S9A2S34S9S9R3R2A4S16VA;A1A3SdSaS0S8R4S50R3A1A2R2A2S2R2S1R4R3A2A2A2SaS0S4cR4A1M0R2A2S2R2S1G0S5S1R3Z7A2Z8A2A2A2A2A2ScS2aVA;Vi;Vch;R3A4A1F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z Hin Hz. destruct space_nums as (S1 & S2 & _). destruct (is_primary n) eqn:HP.
  - pose proof HI3 as (H3 & _). pose proof (live_prim_czone A HG H3 m HLS HPR b n Hin HP) as L. cbv zeta in L.
    destruct L as (C1 & O0 & OM & OE & _ & _ & CZ).
    destruct (czone_where A HG H3 _ _ z C1 O0 OM OE (CZ z Hz)) as [W|[W _]].
    + apply nRZ_space. clear -W. lia.
    + apply (nRZ_space_sh SB (SB + 2 ^ 37) z); [lia | lia | lia | exact W].
  - destruct (live_sec_map A m HLS HSR HI3 b n Hin HP) as (j & c & Hj & Eb & RZn & N1 & BN & _).
    assert (Nji : j <> i) by (intros ->; rewrite Hi in Hj; injection Hj as <-; exact (HNL b n Hin HP Eb)).
    destruct (ch_nums j c Hj) as (C1 & C2 & C3 & _). unfold PG in Eb.
    destruct Hz as [Hz|Hz].
    + apply (nRZ_chunk j c z Hj Nji); [rewrite RZn in Hz; lia | intros _; rewrite RZn in Hz; lia].
    + destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _). pose proof (X5 i ch Hi Nji) as AP.
      apply (nRZ_sh b n z); [lia | lia | lia | lia | exact Hz].
Qed.

Lemma chunk_sh_band : ltac2:(tb__ "0|0|
S2fSfS9SbS2dSfA1S49SfS11VA;A1R3A3S2eSfR2A2A3S51R3R2A2SaS0Z7fff7000R3A2S2R3Z10007fff8000A2A2F_;F_;Fz;Fc;Fj;").
Proof.
  intros j c z Hj Hz. destruct (ch_nums j c Hj) as (N1 & N2 & N3 & _). unfold chunk_sh_zone in Hz.
  pose proof (sh_run_band2 (sc_map_beg c) (sc_map_beg c + sc_map_size c) z ltac:(lia) ltac:(lia) Hz) as B.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B. exact B.
Qed.
Lemma RZ_band : ltac2:(tb__ "0|0|
S9S2aVA;Vi;Vch;R1A4SaS0Z7fff7000R2A2S2R2Z10007fff8000A2A2S51Vch;R3A2F_;F_;Fz;").
Proof.
  intros z HZ B. destruct (ch_nums i ch Hi) as (N1 & N2 & N3 & N4 & _).
  assert (D : newZc ch z \/ ~ newZc ch z) by (unfold newZc, chunk_zone, chunk_sh_zone; lia).
  destruct D as [[D|D]|D]; [unfold chunk_zone in D; lia | exact D | exfalso; exact (band_nRZ z B D HZ)].
Qed.
Lemma RZ_dec : ltac2:(tb__ "0|1|
S9SdS2aVA;Vi;Vch;R1A4M0ScG0A1A2Fz;").
Proof.
  intros z. unfold RZ, sec_junk_zone, sec_tbl_zone, chunk_zone, chunk_sh_zone.
  destruct (nth_error (aa_sec A) (length (aa_sec A) - 1)) as [lst|] eqn:EL.
  - assert (D : (sc_map_beg lst + 24 <= z < sc_map_beg lst + 32) \/ ~ (sc_map_beg lst + 24 <= z < sc_map_beg lst + 32)) by lia.
    destruct D as [D|D].
    + left. right. left. right. right. right. exists lst. split; [reflexivity | exact D].
    + assert (E : (SEC_INST + 64 <= z < 0xee040 \/ 0xee048 <= z < 0xee070) \/ (SEC_INST + 56 <= z < SEC_INST + 64 \/ 0xee040 <= z < 0xee044 \/ PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8)
                    \/ (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) \/ (Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch))
                    \/ ~ ((SEC_INST + 64 <= z < 0xee040 \/ 0xee048 <= z < 0xee070) \/ (SEC_INST + 56 <= z < SEC_INST + 64 \/ 0xee040 <= z < 0xee044 \/ PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8)
                    \/ (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) \/ (Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)))) by lia.
      destruct E as [E|[E|[E|[E|E]]]]; [left; left; exact E | left; right; left; tauto | left; right; right; left; exact E | left; right; right; right; exact E|].
      right. intros [X|[X|[X|X]]]; [apply E; left; exact X | | apply E; right; right; left; exact X | apply E; right; right; right; exact X].
      destruct X as [X|[X|[X|(l2 & Hl2 & X)]]]; [apply E; right; left; left; exact X | apply E; right; left; right; left; exact X | apply E; right; left; right; right; exact X|].
      injection Hl2 as <-. exact (D X).
  - assert (E : (SEC_INST + 64 <= z < 0xee040 \/ 0xee048 <= z < 0xee070) \/ (SEC_INST + 56 <= z < SEC_INST + 64 \/ 0xee040 <= z < 0xee044 \/ PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8)
                    \/ (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) \/ (Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch))
                    \/ ~ ((SEC_INST + 64 <= z < 0xee040 \/ 0xee048 <= z < 0xee070) \/ (SEC_INST + 56 <= z < SEC_INST + 64 \/ 0xee040 <= z < 0xee044 \/ PAB + 8 * Z.of_nat i <= z < PAB + 8 * Z.of_nat i + 8)
                    \/ (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) \/ (Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)))) by lia.
    destruct E as [E|[E|[E|[E|E]]]]; [left; left; exact E | left; right; left; tauto | left; right; right; left; exact E | left; right; right; right; exact E|].
    right. intros [X|[X|[X|X]]]; [apply E; left; exact X | | apply E; right; right; left; exact X | apply E; right; right; right; exact X].
    destruct X as [X|[X|[X|(l2 & Hl2 & X)]]]; [apply E; right; left; left; exact X | apply E; right; left; right; left; exact X | apply E; right; left; right; right; exact X|].
    discriminate Hl2.
Qed.
End Geo.

Section Xfer.
Variables (A : AA) (rho0 rho1 : valuation) (tp : list word) (md : Model) (i : nat) (ch : sec_chunk).
Variables (ZZ PZ : Z -> Prop).
Local Abbreviation v0 := (view segsA (rm rho0)).
Local Abbreviation v1 := (view segsA (rm rho1)).
Local Abbreviation mm := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho0))).
Local Abbreviation mm' := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho1))).
Hypothesis HA : ltac2:(tb__ "0|0|
S58VA;Vrho0;Vtp;Vmd;A4").
Hypothesis Hi : ltac2:(tb__ "0|0|
SbS2dSfA1S49SfS11VA;A1Vi;A3S2eSfVch;A2A3").
Hypothesis HNL : ltac2:(tb__ "0|0|
S9S9S4aS31S9S9A2S34S9S9R2R1A4S16VA;A1A3SbS32S4eR2A1S33A3ScSbS9R4S1S1S12Vch;A1S4dA2Z800A2A3A1F_;F_;Fn;Fb;").
Hypothesis HZZ : ltac2:(tb__ "0|0|
S9VZZ;R1A1S2aVA;Vi;Vch;R2A4F_;Fz;").
Hypothesis HDEC : ltac2:(tb__ "0|1|
S9SdVZZ;R1A1M0ScG0A1A2Fz;").
Hypothesis HOUT : ltac2:(tb__ "0|0|
S9ScVZZ;R1A1A1SbS2dS4bQ8A1A1S20S1fS29Vrho1;A1R2A3S20S1fS29Vrho0;A1R2A3A3F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S9VZZ;R1A1VPZ;R2A1ScSbS2dS4bQ8A1M0A1M1S20S1fS29Vrho0;A1R3A3S35G0A1M2A3A1ScSbG1S20S1fS29Vrho1;A1R4A3G2A3A1F_;F_;F_;Fz;").

Lemma X_parts : ltac2:(tb__ "0|2|
SaS42S10VA;A1M0A1SaS46VA;A1SaS3fS21S39G0A1S20S1fS29Vrho0;A1A2A2M1VA;A2SaS3bG1VA;A2S44VA;A1A2A2A2A2").
Proof.
  destruct HA as (HG & _ & _ & HRest & _ & HI3 & _). cbv zeta in HRest. destruct HRest as (R1 & _ & R3 & R4 & _).
  exact (conj HG (conj R1 (conj R3 (conj R4 HI3)))).
Qed.
Lemma X_out : ltac2:(tb__ "0|1|
S9ScS2aVA;Vi;Vch;R1A4A1SbS2dS4bQ8A1A1S21S39S10VA;A1A1M0S20S1fS29Vrho1;A1A2R2A3S21G0S20S1fS29Vrho0;A1A2R2A3A3F_;Fz;").
Proof. intros z Hz. unfold maskv. rewrite (HOUT z (fun H => Hz (HZZ z H))). reflexivity. Qed.
Lemma X_in : ltac2:(tb__ "0|4|
S9VZZ;R1A1SaSbS2dS4bQ8A1A1M0S21S39S10VA;A1A1M1S20S1fS29Vrho0;A1M2A2R2A3S20S1fG2R2A3A3SbG0S21G1S20S1fS29Vrho1;A1M3A2R2A3S20S1fG3R2A3A3A2F_;Fz;").
Proof.
  intros z Hz. destruct X_parts as (HG & HLS & HPR & HSR & HI3).
  pose proof (RZ_fs A mm HG HSR HI3 i ch Hi z (HZZ z Hz)) as F. unfold maskv. rewrite F. split; reflexivity.
Qed.

Lemma X_some : ltac2:(tb__ "0|4|
S9VZZ;R1A1VPZ;R2A1F_;SeS4bQ8A1M0G0SbS2dG0A1M1S21S39S10VA;A1A1M2S20S1fS29Vrho0;A1A2R3A3S2eG0R1A2M3A3Lb;A2SeG0G0SbG1S21G2S20S1fS29Vrho1;A1A2R4A3G3A3Lb;A2F_;F_;Fz;").
Proof.
  intros z HP [b Hb]. destruct (HDEC z) as [Hz|Hz].
  - destruct (X_in z Hz) as [E0 E1]. rewrite E1. rewrite E0 in Hb. destruct (v1 z) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (HIN z Hz (HP Hz)); [rewrite Hb; discriminate | exact E].
  - unfold maskv in *. rewrite (HOUT z Hz). exists b. exact Hb.
Qed.
Lemma X_cell : ltac2:(tb__ "0|1|
S24S2fS57R1S26R2A1A2ScS2aVA;Vi;Vch;S1S25R3A1S3R2A1A2A4A1F_;Fk;S22S21S39S10VA;A1A1M0S20S1fS29Vrho0;A1A2A2R2A2S22S21G0S20S1fS29Vrho1;A1A2A2R3A2F_;F_;Fc;").
Proof. intros c H. apply cell_ok_agree. intros k Hk. exact (X_out _ (H k Hk)). Qed.

Lemma X_rtc : ltac2:(tb__ "0|0|
S28S20S1fS29Vrho1;A1A2S10VA;A1A2").
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & HR & _).
  unfold rtc_inv in *. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply HOUT. intros HZ. apply HZZ in HZ. revert HZ.
  unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
  unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
  unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
  - unfold rtc_cells_img in Hc. apply (nRZ_low A mm HSR i ch Hi); unfold SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]); destruct Hc.
  - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
    assert (ZC : (ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 288) \/ (ag_ctx (aa_geom A) <= z < ag_ctx (aa_geom A) + 0x1000)
                 \/ (ag_dtls (aa_geom A) <= z < ag_dtls (aa_geom A) + 0x1000) \/ (ag_fsb (aa_geom A) <= z < ag_fsb (aa_geom A) + 97)).
    { repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]). destruct Hc. }
    destruct ZC as [Z1|[Z1|[Z1|Z1]]].
    + apply (nRZ_T A mm HG HSR HI3 i ch Hi). lia.
    + apply (nRZ_ctx A mm HG HSR HI3 i ch Hi). lia.
    + apply (nRZ_dtls A mm HG HSR HI3 i ch Hi). lia.
    + apply (nRZ_fsb A mm HG HSR HI3 i ch Hi). lia.
Qed.

Lemma X_fs : ltac2:(tb__ "0|0|
S3eS27S39S10VA;A1A1S20S1fS29Vrho1;A1A2A2VA;A2").
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & _ & HF & _).
  rewrite (restrictv_ext (fs_footb (aa_geom A)) v0 v1); [exact HF|].
  intros z Hz. apply HOUT. intros HZ. rewrite (RZ_fs A mm HG HSR HI3 i ch Hi z (HZZ z HZ)) in Hz. discriminate Hz.
Qed.
Lemma X_live : live_block_repr mm' A.
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & R2 & _).
  apply (live_block_repr_agree mm mm' A A eq_refl); [| | exact R2].
  - intros b n z Hin Hz. apply X_out. exact (nRZ_live A mm HG HLS HPR HSR HI3 i ch Hi HNL b n z Hin Hz).
  - intros b n Hin. exact (proj1 (HLS b n Hin)).
Qed.
Lemma X_prim : primary_repr mm' A.
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). pose proof HPR as (Q1 & Q2 & Q3 & P4). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
  intros c Hc. apply (class_repr_agree mm mm' (aa_geom A) A A c); [exact Hc | reflexivity | reflexivity | reflexivity | intros b n H _ _; exact H | intros z H; exact H | | exact (P4 c Hc)].
  intros z Hz. apply X_out. exact (nRZ_cls A mm HG HPR HSR HI3 i ch Hi c z Hc Hz).
Qed.
Lemma X_img : ltac2:(tb__ "0|1|
S9S2R1Z646000A2ScSaS0S1S3aZ38A2R2A2S2R2Zee070A2A2A1SbS2dS4bQ8A1A1S21S39S10VA;A1A1M0S20S1fS29Vrho1;A1A2R3A3S21G0S20S1fS29Vrho0;A1A2R3A3A3F_;F_;Fz;").
Proof. intros z H1 H2. destruct X_parts as (HG & HLS & HPR & HSR & HI3). apply X_out. exact (nRZ_low A mm HSR i ch Hi z H1 H2). Qed.
Lemma X_qmin : ltac2:(tb__ "0|0|
S22S21S39S10VA;A1A1S20S1fS29Vrho1;A1A2A2S23S1S3cZ48A2U8S4fA3A2").
Proof.
  destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & (_ & R5m) & _).
  eapply cell_ok_agree; [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply X_img; unfold QG, SEC_INST; lia.
Qed.
Lemma X_depot : depot_wf mm' A.
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & _ & R6 & _).
  unfold depot_wf in *. eapply depot_mem_frame; [|exact R6]. intros a0 Ha.
  destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
  - apply X_img; unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK, SEC_INST in *; lia.
  - apply X_out. apply (nRZ_dblock A mm HSR HI3 i ch Hi (bb, NBSZ) a0); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold NBSZ; cbn; lia | exact Hab].
  - apply X_out. apply (nRZ_dblock A mm HSR HI3 i ch Hi (bb, FBSZ) a0); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold FBSZ; cbn; lia | exact Hab].
Qed.
Lemma X_ia : ia_inv mm' A.
Proof.
  destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & _ & _ & R7 & _).
  apply (ia_inv_agreeN mm mm' A A eq_refl); [|exact R7]. intros z Hz. apply X_img; unfold IA_BEG, IA_END, SEC_INST in *; lia.
Qed.
Lemma X_thread : ltac2:(tb__ "0|1|
S40S21S39S10VA;A1M0A1S20S1fS29Vrho1;A1A2A2G0A2").
Proof.
  destruct X_parts as (HG & HLS & HPR & HSR & HI3). destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & _ & _ & _ & (TH1 & TH2) & _).
  assert (TO : forall z, ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 4096 -> mm' z = mm z).
  { intros z Hz. apply X_out. exact (nRZ_T A mm HG HSR HI3 i ch Hi z Hz). }
  split; [rewrite TO by lia; exact TH1|]. eapply present_agree; [|exact TH2]. intros z Hz. apply TO. lia.
Qed.
Lemma X_misc : misc_inv mm'.
Proof.
  destruct HA as (_ & _ & _ & HRest & _). cbv zeta in HRest. destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & R9).
  pose proof R9 as (_ & M2 & M3). apply (misc_inv_N mm mm'); [| | | exact R9].
  - intros z Hz. apply X_img; unfold SEC_INST; lia.
  - eapply present_agree; [|exact M2]. intros z Hz. apply X_img; unfold SEC_INST; lia.
  - eapply present_agree; [|exact M3]. intros z Hz. apply X_img; unfold SEC_INST, ERRNO_A in *; lia.
Qed.

Hypothesis HBAND : ltac2:(tb__ "0|0|
S9VZZ;R1A1SaS0Z7fff7000R2A2S2R2Z10007fff8000A2A2VPZ;R3A1F_;F_;Fz;").
Lemma X_bandtp : ltac2:(tb__ "0|1|
S36S4bQ40A1M0A1G0S4aG0R1R2A3S4aG0R2Vtp;A3F_;Fp;S3dS20S1fS29Vrho1;A1A2R2A2F_;Ftp';").
Proof.
  intros tp' SUB p Hp BP z Hz. destruct HA as (_ & _ & _ & _ & _ & _ & HB). destruct (HB p (SUB p Hp) BP z Hz) as [b Hb].
  pose proof (band_page_band _ BP) as BB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BB.
  destruct (HDEC z) as [Hzz|Hzz]; [|rewrite (HOUT z Hzz); exists b; exact Hb].
  destruct (v1 z) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
  apply (HIN z Hzz (HBAND z Hzz ltac:(lia))); [rewrite Hb; discriminate | exact E].
Qed.

Lemma X_all : ltac2:(tb__ "0|5|
SaS28S20S1fS29Vrho1;A1A2M0S10VA;A1M1A2SaS3eS27S39G1A1M2G0A2VA;A2SaS45S21G2G0A2M3VA;A2SaS3fG3VA;A2SaS22G3S23S1S3cZ48A2U8S4fA3A2SaS41G3VA;A2SaS43G3VA;A2SaS40G3G1A2SaS47G3A1S36S4bQ40A1M4A1G4S4aG4R1R2A3S4aG4R2Vtp;A3F_;Fp;S3dG0R2A2F_;Ftp';A2A2A2A2A2A2A2A2A2").
Proof.
  exact (conj X_rtc (conj X_fs (conj X_live (conj X_prim (conj X_qmin (conj X_depot (conj X_ia (conj X_thread (conj X_misc X_bandtp))))))))).
Qed.

Lemma X_sec_same : ltac2:(tb__ "0|1|
S9VZZ;R1A1M0S51Vch;R2A2F_;Fz;S9G0VPZ;R2A1F_;Fz;S3bS21S39S10VA;A1A1S20S1fS29Vrho1;A1A2A2VA;A2F_;F_;").
Proof.
  intros HZS HPZ. destruct X_parts as (HG & HLS & HPR & HSR & HI3).
  assert (OB : forall z, ~ (2147446784 <= z < 17594333495296) -> mm' z = mm z).
  { intros z NB. unfold maskv. rewrite (HOUT z); [reflexivity|]. intros HZ. exact (NB (chunk_sh_band A mm HSR i ch z Hi (HZS z HZ))). }
  assert (PR : forall lo hi, present mm lo hi -> present mm' lo hi) by (intros lo hi H z Hz; exact (X_some z (HPZ z) (H z Hz))).
  assert (CO : forall c, (forall k, (k < c_w c)%nat -> ~ (2147446784 <= c_addr c + Z.of_nat k < 17594333495296)) -> cell_ok mm c -> cell_ok mm' c).
  { intros c H. apply cell_ok_agree. intros k Hk. exact (OB _ (H k Hk)). }
  destruct (pab_nums A mm HSR) as (P1 & P2 & P3 & P4).
  pose proof HSR as (S1 & SPT & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. cbv zeta.
  split.
  { intros j c Hj. destruct (S1 j c Hj) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    destruct (ch_nums A mm HSR j c Hj) as (N1 & N2 & N3 & N4 & _). pose proof (proj1 (nth_error_Some (aa_sec A) j) ltac:(rewrite Hj; discriminate)) as LJ.
    split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C1]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C2]|].
    split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C3]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C4]|].
    split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact C5]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [intros z Hz Hn; exact (X_some z (HPZ z) (D13 z Hz Hn)) | exact (PR _ _ D14)]. }
  split; [exact (PR _ _ SPT)|]. split; [exact S2|]. split; [exact S3|]. split; [exact S45|].
  unfold SEC_INST in *.
  split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I1]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I2]|].
  split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I3]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I4]|].
  split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I5]|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I6]|].
  split; [exact (PR _ _ I7)|]. split; [apply CO; [cbn [c_addr c_w]; intros k Hk; lia | exact I8] | exact (PR _ _ I9)].
Qed.
End Xfer.

Section XferU.
Variables (A : AA) (rho0 rho1 : valuation) (tp : list word) (md : Model) (i : nat) (ch : sec_chunk) (t g : list qbatch).
Local Abbreviation v0 := (view segsA (rm rho0)).
Local Abbreviation v1 := (view segsA (rm rho1)).
Local Abbreviation mm := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho0))).
Local Abbreviation mm' := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho1))).
Local Abbreviation PABu := (ag_pab (aa_geom A)).
Local Abbreviation nn := (Z.of_nat (length (aa_sec A))).
Hypothesis HA : ltac2:(tb__ "0|0|
S58VA;Vrho0;Vtp;Vmd;A4").
Hypothesis Hi : ltac2:(tb__ "0|0|
SbS2dSfA1S49SfS11VA;A1Vi;A3S2eSfVch;A2A3").
Hypothesis HOUT : ltac2:(tb__ "0|0|
S9ScS2aVA;Vi;Vch;R1A4A1SbS2dS4bQ8A1A1S20S1fS29Vrho1;A1R2A3S20S1fS29Vrho0;A1R2A3A3F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S9SdS52R1A1S51Vch;R1A2A2ScSbS2dS4bQ8A1M0A1M1S20S1fS29Vrho0;A1R2A3S35G0A1M2A3A1ScSbG1S20S1fS29Vrho1;A1R3A3G2A3A1F_;F_;Fz;").
Hypothesis CN : ltac2:(tb__ "0|0|
S22S20S1fS29Vrho1;A1A2S23S1S3aZ38A2U8S8S3S30SfS11VA;A1A2A1Z1A2A3A2").
Hypothesis CM : cell_ok v1 (mkACell 0xee040 4 0).
Hypothesis CL : ltac2:(tb__ "0|a|
SfSbS2dSfA1S49SfS11VA;A1M0S56S30SfG0A2M1U1A2A3S2eSfR1A2A3SaS2S3Vi;A1M2S8S3G1A1Z1A2M3A2SaS22S20S1fS29Vrho1;A1M4A2M5S23S1S14S10VA;A1A1S4Z8M6G2A2A2M7U8M8S12R3A1M9A3A2S22G5S23S1G9Z18A2G8G2A3A2A2F_;SbS9G2G3A3S9SaS0G7R1A2S2R1S1G7G6A2A2A2SbS2dS4bQ8A1A1S20S1fG4R2A3S20S1fS29Vrho0;A1R2A3A3F_;Fz;F_;A2F_;Flst;").

Lemma U_out : ltac2:(tb__ "0|1|
S9ScS2aVA;Vi;Vch;R1A4A1SbS2dS4bQ8A1A1S21S39S10VA;A1A1M0S20S1fS29Vrho1;A1A2R2A3S21G0S20S1fS29Vrho0;A1A2R2A3A3F_;Fz;").
Proof. exact (X_out A rho0 rho1 i ch (RZ A i ch) (fun _ H => H) HOUT). Qed.
Lemma U_in : ltac2:(tb__ "0|4|
S9S2aVA;Vi;Vch;R1A4SaSbS2dS4bQ8A1A1M0S21S39S10VA;A1A1M1S20S1fS29Vrho0;A1M2A2R2A3S20S1fG2R2A3A3SbG0S21G1S20S1fS29Vrho1;A1M3A2R2A3S20S1fG3R2A3A3A2F_;Fz;").
Proof. exact (X_in A rho0 rho1 tp md i ch (RZ A i ch) HA Hi (fun _ H => H)). Qed.
Lemma U_some : ltac2:(tb__ "0|4|
S9S2aVA;Vi;Vch;R1A4SdS52R2A1S51Vch;R2A2A2F_;SeS4bQ8A1M0G0SbS2dG0A1M1S21S39S10VA;A1A1M2S20S1fS29Vrho0;A1A2R3A3S2eG0R1A2M3A3Lb;A2SeG0G0SbG1S21G2S20S1fS29Vrho1;A1A2R4A3G3A3Lb;A2F_;F_;Fz;").
Proof.
  exact (X_some A rho0 rho1 tp md i ch (RZ A i ch) (fun z => sec_junk_zone z \/ chunk_sh_zone ch z) HA Hi (fun _ H => H) (RZ_dec A i ch) HOUT (fun z _ HP => HIN z HP)).
Qed.
Lemma U_cell : ltac2:(tb__ "0|1|
S24S2fS57R1S26R2A1A2ScS2aVA;Vi;Vch;S1S25R3A1S3R2A1A2A4A1F_;Fk;S22S21S39S10VA;A1A1M0S20S1fS29Vrho0;A1A2A2R2A2S22S21G0S20S1fS29Vrho1;A1A2A2R3A2F_;F_;Fc;").
Proof. exact (X_cell A rho0 rho1 i ch (RZ A i ch) (fun _ H => H) HOUT). Qed.
Lemma U_cellv : ltac2:(tb__ "0|1|
S24S2fS57R1S26R2A1A2S2aVA;Vi;Vch;S1S25R3A1S3R2A1A2A4F_;Fk;S22S20S1fS29Vrho1;A1A2M0R2A2S22S21S39S10VA;A1A1G0A2R3A2F_;F_;Fc;").
Proof. intros c H Hc k Hk. rewrite (proj2 (U_in _ (H k Hk))). exact (Hc k Hk). Qed.

Theorem X_sec_unmap : ltac2:(tb__ "0|0|
S3bS21S39S10VA;A1A1S20S1fS29Vrho1;A1A2A2S55S5bVA;Vt;Vg;A3Vi;A2A2").
Proof.
  destruct (X_parts A rho0 tp md HA) as (HG & HLS & HPR & HSR & HI3).
  destruct (pab_nums A mm HSR) as (P1 & P2 & P3 & P4).
  pose proof HSR as (S1 & SPT & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite Hi; discriminate)) as LI.
  unfold secondary_repr. cbv zeta.
  change (aa_geom (unmap_sec (set_q A t g) i)) with (aa_geom A). change (aa_sec (unmap_sec (set_q A t g) i)) with (swap_remove (aa_sec A) i).
  change (aa_ptr_committed (unmap_sec (set_q A t g) i)) with (aa_ptr_committed A). change (aa_live (unmap_sec (set_q A t g) i)) with (aa_live A).
  rewrite (swap_remove_length _ i ch Hi).
  assert (ELEN : Z.of_nat (length (aa_sec A) - 1) = nn - 1) by lia.

  assert (OLDC : forall j c, nth_error (aa_sec A) j = Some c -> j <> i -> forall off w v, 0 <= off -> off + Z.of_nat w <= 32 ->
                   (j = (length (aa_sec A) - 1)%nat -> off + Z.of_nat w <= 24) ->
                   cell_ok mm (mkACell (sc_map_beg c + off) w v) -> cell_ok mm' (mkACell (sc_map_beg c + off) w v)).
  { intros j c Hj Nji off w v Ho Hw HL. apply U_cell. cbn [c_addr c_w]. intros k Hk. destruct (ch_nums A mm HSR j c Hj) as (_ & N2 & _).
    apply (nRZ_chunk A mm HSR HI3 i ch Hi j c _ Hj Nji); [lia | intros E; specialize (HL E); lia]. }
  assert (PABC : forall j v, j <> i -> (j < length (aa_sec A))%nat -> cell_ok mm (mkACell (PABu + 8 * Z.of_nat j) 8 v) -> cell_ok mm' (mkACell (PABu + 8 * Z.of_nat j) 8 v)).
  { intros j v Nji Lj. apply U_cell. cbn [c_addr c_w]. intros k Hk. apply (nRZ_pab A mm HSR HI3 i ch Hi); [lia|]. intros X. apply Nji. lia. }
  split.
  { intros j c Hj. destruct (swap_remove_nth _ i ch j c Hi Hj) as (LTj & [[Nji Hjo]|(Eji & LTi & Hl)]).
    -
      destruct (S1 j c Hjo) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
      split; [apply (OLDC j c Hjo Nji); [lia | cbn; lia | intros E; lia | exact C1]|].
      split; [apply (OLDC j c Hjo Nji); [lia | cbn; lia | intros E; lia | exact C2]|].
      split; [apply (OLDC j c Hjo Nji); [lia | cbn; lia | intros E; lia | exact C3]|].
      split; [apply (OLDC j c Hjo Nji); [lia | cbn; lia | intros E; lia | exact C4]|].
      split; [apply (PABC j _ Nji ltac:(lia)); exact C5|].
      split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
      split.
      + intros z Hz Hn. rewrite U_out; [exact (D13 z Hz Hn)|]. apply (nRZ_chunk A mm HSR HI3 i ch Hi j c z Hjo Nji Hz). intros E. lia.
      + intros z Hz. rewrite U_out; [exact (D14 z Hz)|]. exact (nRZ_chunk_sh A mm HSR HI3 i ch Hi j c z Hjo Nji Hz).
    -
      subst j. destruct (CL c Hl) as [CLa _]. destruct (CLa ltac:(lia)) as [CP CI].
      assert (Nl : (length (aa_sec A) - 1)%nat <> i) by lia.
      destruct (S1 _ c Hl) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
      destruct (ch_nums A mm HSR _ c Hl) as (_ & N2 & _).
      assert (INL : forall z, sc_map_beg c + 24 <= z < sc_map_beg c + 32 -> RZ A i ch z).
      { intros z Hz. right. left. right. right. right. exists c. split; [exact Hl | exact Hz]. }
      split; [apply (OLDC _ c Hl Nl); [lia | cbn; lia | intros _; cbn; lia | exact C1]|].
      split; [apply (OLDC _ c Hl Nl); [lia | cbn; lia | intros _; cbn; lia | exact C2]|].
      split; [apply (OLDC _ c Hl Nl); [lia | cbn; lia | intros _; cbn; lia | exact C3]|].
      split; [apply U_cellv; [cbn [c_addr c_w]; intros k Hk; apply INL; lia | exact CI]|].
      split; [apply U_cellv; [cbn [c_addr c_w]; intros k Hk; right; left; right; right; left; lia | exact CP]|].
      split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
      split.
      + intros z Hz Hn. destruct (Z_le_dec (sc_map_beg c + 24) z) as [GE|LT]; [destruct (Z_lt_dec z (sc_map_beg c + 32)) as [LT2|GE2]|].
        * assert (CI' : cell_ok mm' (mkACell (sc_map_beg c + 24) 8 (Z.of_nat i))) by (apply U_cellv; [cbn [c_addr c_w]; intros k Hk; apply INL; lia | exact CI]).
          pose proof (CI' (Z.to_nat (z - (sc_map_beg c + 24))) ltac:(cbn [c_w]; lia)) as X.
          cbn [c_addr c_w] in X. rewrite Z2Nat.id in X by lia. replace (sc_map_beg c + 24 + (z - (sc_map_beg c + 24))) with z in X by lia. eexists. exact X.
        * rewrite U_out; [exact (D13 z Hz Hn)|]. apply (nRZ_chunk A mm HSR HI3 i ch Hi _ c z Hl Nl Hz). intros _. lia.
        * rewrite U_out; [exact (D13 z Hz Hn)|]. apply (nRZ_chunk A mm HSR HI3 i ch Hi _ c z Hl Nl Hz). intros _. lia.
      + intros z Hz. rewrite U_out; [exact (D14 z Hz)|]. exact (nRZ_chunk_sh A mm HSR HI3 i ch Hi _ c z Hl Nl Hz). }
  split.
  {
    intros z Hz. rewrite ELEN in Hz.
    destruct (Z_lt_dec z (PABu + 8 * nn)) as [INC|TAIL].
    -
      assert (EL : exists lst, nth_error (aa_sec A) (length (aa_sec A) - 1) = Some lst).
      { clear CL. destruct (nth_error (aa_sec A) (length (aa_sec A) - 1)) eqn:E; [eexists; reflexivity | apply nth_error_None in E; lia]. }
      destruct EL as [lst El].
      destruct (S1 _ lst El) as (_ & _ & _ & _ & C5 & _).
      assert (OLD : exists b, mm z = Some b).
      { pose proof (C5 (Z.to_nat (z - (PABu + 8 * (nn - 1)))) ltac:(cbn [c_w]; lia)) as X. cbn [c_addr c_w] in X. rewrite Z2Nat.id in X by lia.
        rewrite ELEN in X. replace (PABu + 8 * (nn - 1) + (z - (PABu + 8 * (nn - 1)))) with z in X by lia. eexists. exact X. }
      destruct (Nat.eq_dec i (length (aa_sec A) - 1)) as [Ei|Ni].
      + destruct (CL lst El) as [_ CLb]. assert (INR : RZ A i ch z) by (right; left; right; right; left; lia).
        destruct (U_in z INR) as [E0 E1]. rewrite E1, (CLb ltac:(lia) z ltac:(lia)), <- E0. exact OLD.
      + rewrite U_out; [exact OLD|]. apply (nRZ_pab A mm HSR HI3 i ch Hi); lia.
    - pose proof S2 as S2'. unfold kPtrArrayReserve in S2'. rewrite U_out; [apply SPT; lia|]. apply (nRZ_pab A mm HSR HI3 i ch Hi); lia. }
  split; [lia|]. split; [exact S3|]. split; [exact S45|].
  assert (CIMG : forall c, c_addr c + Z.of_nat (c_w c) <= SEC_INST + 56 -> cell_ok mm c -> cell_ok mm' c).
  { intros c H. apply U_cell. intros k Hk. apply (nRZ_low A mm HSR i ch Hi); unfold SEC_INST in *; lia. }
  split; [apply CIMG; [cbn; lia | exact I1]|]. split; [apply CIMG; [cbn; lia | exact I2]|]. split; [apply CIMG; [cbn; lia | exact I3]|].
  split; [apply CIMG; [cbn; lia | exact I4]|]. split; [apply CIMG; [cbn; lia | exact I5]|].
  split; [rewrite ELEN; apply U_cellv; [cbn [c_addr c_w]; intros k Hk; right; left; left; lia | exact CN]|].
  split; [intros z Hz; apply U_some; [intros _; left; left; lia | exact (I7 z Hz)]|].
  split; [apply U_cellv; [cbn [c_addr c_w]; intros k Hk; right; left; right; left; lia | exact CM]|].
  intros z Hz. apply U_some; [intros _; left; right; lia | exact (I9 z Hz)].
Qed.
End XferU.
End InvQ10b.

(* [comment removed for export] *)
Module SpineMallocR13.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "sub"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "SAlu"; "SLit"; "sprop"; "SVar"; "ss_next"; "ss_objs"; "rw"; "ss_facts"; "ss_lenient"; "cell"; "swf"; "SPBranch"; "SPNot"; "eval"; "mkCell"; "rm"; "smatch"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "nil"; "true"; "false"; "option"; "Some"; "app"; "prod"; "pair"; "None"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR13.FILL"; "JRfill"; "phL"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "LV0"; "LV2"; "GR"; "LV3"; "keepn"; "LNX"; "HINT_au"; "HINT_k"; "O_cell"; "O_pcm"; "O_ri"; "vAU"; "vNEW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "FAb"; "zoneR"; "entryR"; "frozen"; "ghosts"; "mkPh"; "ph_f"; "ph_u"; "rlink"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "ALU_XOR"; "BC_LTU"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR13"; "O_fcell"; "faend_e"; "F_lt"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineMallocR12.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition faend_e : sv := SAlu ALU_ADD fa_e2 need_e.
Definition O_fcell : sobj := ltac2:(tb__ "0|1|
S48S43S23S18S1dS10Z0A1Z4M0SfS59S12S41A1S10G0A1A3A3S26S18A1A3A2").
Definition F_lt : sprop := ltac2:(tb__ "0|0|
S1aS5bS12S40A1S4cA3").

Section FILL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S69Vst;S68A3S0S24S67A1VW;S26S67A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S50VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let S : Z := Size c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let au : Z := cs_allocated_user cs.
Let new : Z := gh_new A rb.

Variable ph : phase.
Hypothesis PQ : ph_quiet ph.
Definition phL (i : Z) : phase := ltac2:(tb__ "0|0|
S53S55Vph;A1S54Vph;A1Vi;Z0S28S28A6").
Lemma phL0 : phL 0 = ph.
Proof.
  destruct PQ as (Q1 & Q2 & Q3 & Q4).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phL; rewrite Q1, Q2, Q3, Q4; reflexivity | symmetry; apply ph_eta].
Qed.

Hypothesis HDEF : ltac2:(tb__ "0|3|
S21S77S1S6Z0R2A2S6R2Vnew;A2A2S56VA;Vrb;S39R3A1S78S35S1eVrb;A1A2R2A5S21S1S6S5S4eVA;Vrb;A2M0S7Z4M1Vnf;A2A2R1A2S8R1S5G0S7G1S5Vnf;Vnew;A2A2A2A2A2S3S0S29S3aQ8A1M2A1R5R2A1S2eG2A1A3A1F_;Fz;F_;F_;Fm;Fi;").

Lemma fill_nums : ltac2:(tb__ "0|7|
S1S1S6Z20VS;A2S6VS;Z10000A2A2S1S6Z0M0Vau;A2S1S6S5Vau;S7Vnew;VS;A2A2Ze0000000M1A2S1S1S6Z4M2Vnew;A2S6Vnew;Z2001A2A2S1S6G0Vnf;A2S1S6S7G2S5Vnf;Vnew;A2A2S5Z20000000M3Z8004M4A2A2S1S6G0S4eVA;Vrb;A2M5A2S1S8S5S5S5G5G3A2G4A2Z8A2SbZ2Z3eA2A2S1S0S21G5S5S5S75S74VA;A1A1M6S7Vc;Z100000000A2A2G1A2A3S1S1S6Z1Vc;A2S6Vc;Z1eA2A2S1S6Z100080000000G6A2S6S5S5G6Z2000000000A2Z1000A2Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  destruct (new_nums A rb CF PF) as (N1 & N2 & N3 & N4 & _ & N6 & _ & N8 & N9 & N10 & _). cbn zeta in N1, N2, N3, N4, N6, N8, N9, N10. fold nv c cs in N1, N2, N3, N4, N6, N8, N9, N10. fold S nf au new in N1, N2, N3, N4, N6, N8, N9, N10.
  unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. clear; lia. }
  split; [exact N1|]. split; [clear -N2; lia|]. split; [clear -N3 N6; lia|]. split; [exact N4|]. split; [exact N8|]. split; [clear -N4 N9 N10; lia|].
  split; [rewrite FAr; clear -C1 G13; lia|]. split; [rewrite FAr; clear -C1 G13 G14 TG; lia|]. split; [exact FAr|]. split; [exact C1|]. split; [exact G13|]. clear -G14 TG; lia.
Qed.

Definition JRfill (i : Z) : jpredA := ltac2:(tb__ "0|3|
SeS24S3aQ40M0A1M1A1S24S5dA1S5cS1S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vi;A1R4R3R2R1AaS1S0G1S15R4S40A2S3bG0S5Vi;Z1M2A2A2A3S1S0G1S15R4S41A2S3bG0S5Vau;S7Vi;VS;A2A2A2A3S0G1S15R4S43A2S3bG0S5S4eVA;Vrb;A2S7Z4S9S9S5Vnf;Vnew;A2G2A2Vi;A2A2A2A2A3A2A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRfill_K : ltac2:(tb__ "0|0|
S21S76VKc;S38R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRfill_stable : ltac2:(tb__ "0|0|
S21S22S0S25S63S45R1A2S27A3S37S35R2S38R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H0 & H2 & H3). apply Pos.leb_le in Hn. unfold LNX in Hn.
  split; [|split; [|split]].
  - eapply (JR_stable A Kc rb tp0 md0 (phL i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw LV0) by (unfold LV0; lia). exact H0.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV2) by (unfold LV2; lia). exact H2.
  - destruct Hag as (Hw & _). rewrite <- (Hw LV3) by (unfold LV3; lia). exact H3.
Qed.

Lemma zone_fill : ltac2:(tb__ "0|3|
S21S21S6Z0R2A2S2S4fVA;Vrb;S39S5R3Z1M0A2A1R2A4S4S4fVA;Vrb;S39R3A1R2A4S1S6S5S4eVA;Vrb;A2S7Z4M1S9S9S5Vnf;Vnew;A2G0A2R3A2A2A2M2R2A2S8R2S5G2G1A2A2A2A2A2F_;Fz;Fi;").
Proof.
  intros i z Hi. unfold zoneR, phL. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. unfold gh_nf. fold nv c cs nf new.
  split.
  - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; try (left; tauto).
    + destruct (Z.eq_dec i 0) as [->|NZ]; [right; clear -H; lia|].
      destruct (Z_lt_dec z (FAb A rb + 4 * (nf + new - 1 - i) + 4)) as [L|G]; [right; clear -H L; lia | left; right; right; right; right; left; clear -H G NZ Hi; lia].
  - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H]; try tauto.
    + right; right; right; right; left. clear -H Hi. lia.
    + right; right; right; right; left. clear -H Hi. lia.
Qed.

Lemma fill_release : ltac2:(tb__ "0|3|
S20S24ScA1M0SeS24S3aQ40A1A1S24S5dA1M1S6dS5cS5cS21S1S6Z0R1A2S8R1Vnew;A2A2S0G0S14RaA1S2bScR9S23ScS60S26ScA1A3M2A3A3S1fS35R9RbS2dG1S6eR7S6fR6R5A2A4A4S38R4RaR9R8R5A5S4dVA;VKc;Vrb;Vtp0;Vmd0;S39S5R5Z1A2A1S3fRbG2R8A3RaR9R6AaF_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FSt;").
Proof.
  intros St K r2 tp tr ms md mdJ i Hi HO Hsm ((HFz & HGh & HKc' & HM & HR & HRM) & H0 & H2 & H3).
  destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  set (r3 := rho_absorb r2 [O_fcell] ms). set (Ci := FAb A rb + 4 * (nf + new - 1 - i)) in *.
  assert (CiR : FAb A rb + 4 * nf <= Ci /\ Ci + 4 <= FAb A rb + 4 * (nf + new)) by (unfold Ci; clear -Hi; lia).
  assert (RC : obj_range r2 O_fcell = (Ci, Ci + 4)).
  { unfold O_fcell, O_cell. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite H3, u64_lit by (clear -CiR N5 N6 N7 N8; lia). f_equal; clear; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).
  assert (AIS : 0 <= au + i * S /\ au + i * S <= 3758096384) by (clear -Hi N1 N2 N3; nia).
  assert (M3C : cell_ok m3 (mkACell Ci 4 ((au + i * S) / 16))).
  { intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (absorb_obj r2 St tr ms md K [O_fcell] O_fcell Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SAlu ALU_SRL (SVar LV2) (SLit 4))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_fcell O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H3, soff_lit_small, u64_lit in ASb by (clear -CiR N5 N6 N7 N8; lia).
    assert (EV : alu64 ALU_SRL (rw r2 LV2) (Z_to_bv 64 4) = Z_to_bv 64 ((au + i * S) / 16)).
    { apply bv_eq. rewrite srl_val, H2, !u64_lit.
      - change (4 mod 64) with 4. rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity.
      - pose proof (Z.div_pos (au + i * S) 16 ltac:(clear -AIS; lia) ltac:(clear; lia)). pose proof (Z.div_le_upper_bound (au + i * S) 16 (2 ^ 30) ltac:(clear; lia) ltac:(clear -AIS; lia)). clear -H H1. lia.
      - clear -AIS. lia. }
    rewrite EV in ASb. unfold m3. rewrite view_in by (clear -CiR N5 N6 N7 N8 Hj; lia). fold Ci in ASb. replace (Ci + 0 + Z.of_nat j) with (Ci + Z.of_nat j) in ASb by (clear; lia). exact ASb. }
  assert (AGR : forall z, ~ (Ci <= z < Ci + 4) -> m3 z = m2 z).
  { intros z Hz. unfold m3, r3. apply view_absorb_out. intros o [<-|[]]. rewrite RC. cbn [fst snd]. exact Hz. }
  pose proof (zone_fill i) as ZI. fold Ci in ZI.
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|].
  split; [unfold mlink, phL in HM |- *; cbn [ph_u ph_f] in HM |- *; exact HM|].
  split.
  - fold m3. unfold rlink in HR |- *. fold m2 in HR. destruct HR as (L1 & L2 & L3 & _).
    split; [intros z Hz; rewrite AGR by (intros X; apply Hz; apply (ZI z ltac:(clear -Hi; lia)); right; exact X); apply L1; intros X; apply Hz; apply (ZI z ltac:(clear -Hi; lia)); left; exact X|].
    split.
    { intros z Hz. apply (ZI z ltac:(clear -Hi; lia)) in Hz.
      assert (D : Ci <= z < Ci + 4 \/ ~ (Ci <= z < Ci + 4)) by (clear; lia).
      destruct D as [D|D].
      - pose proof (M3C (Z.to_nat (z - Ci)) ltac:(cbn [c_w]; clear -D; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X.
        replace (Ci + Z.of_nat (Z.to_nat (z - Ci))) with z in X by (clear -D; lia). rewrite X. discriminate.
      - rewrite (AGR z D). destruct Hz as [Hz|Hz]; [exact (L2 z Hz) | contradiction]. }
    split.
    { intros j Hj. cbn [ph_fill phL] in Hj |- *. unfold gh_nf. fold nv c cs nf new au S.
      destruct (Z.eq_dec j i) as [->|NE]; [exact M3C|].
      eapply cell_ok_agree_range; [|apply (L3 j); cbn [ph_fill phL]; clear -Hj NE; lia].
      cbn [c_addr c_w]. unfold gh_nf. fold nv c cs nf new. intros z Hz. apply AGR. change (Z.of_nat 4) with 4 in Hz. unfold Ci. clear -Hz Hj NE. lia. }
    cbn [ph_pop ph_cnt ph_ri phL]. split; [intros x Hx; exfalso; clear -Hx; lia|]. split; intros X; discriminate X.
  - apply (rmlink_absorb _ r2 [O_fcell] ms HRM). intros o [<-|[]]. rewrite RC. cbn [fst snd]. right. unfold IMG_HI. clear -CiR N5 FAr C1 G13. lia.
Qed.

Variable F : nat.
Variables (CL0 : axst) (LB LX : leafA) (nobF : nat) (s_bk : wsub).
Let CL1 : axst := cL1 CL0.
Hypothesis SK_l : ltac2:(tb__ "0|1|
S0S24S2cS2cSdSdA2SdA2M0A1S66ScG0S6aS14S30VCL0;A1A1A4S66ScG0S6aS2bScS7aVW;A1S23ScS71S23ScS72S23ScS49S23ScS4aS26ScA1A3A3A3A3A3A4A3").
Hypothesis XX_l : ax_X CL0 = [].
Hypothesis XF_l : ltac2:(tb__ "0|0|
S6cS11S79VW;Vst;A2S16S30VCL0;A1A1A3").
Hypothesis NX_l : ltac2:(tb__ "0|0|
S0S25S64S13S30VCL0;A1A1S45A2S27A3").
Hypothesis W_l1 : ltac2:(tb__ "0|0|
S0S25S19S30VCL1;A1A1S27A3").
Hypothesis R_l1 : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z41740S23S21Z4174cS26S21A1A3A3VCL1;S27A5S2aG0S23S32VLB;S23S32VLX;S26S32A1A3A3A2A3").
Hypothesis LN_l1 : ltac2:(tb__ "0|0|
S0S25S17S30VCL1;A1A1S28A3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLB;A1A1A1M0S2bScS65ScVnobF;G0A3S23ScS60S26ScA1A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S0S24ScA1S14S30S31VLX;A1A1A1M0S2bScS65ScVnobF;G0A3S23ScS60S26ScA1A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S0S25S34S44S31VLB;A1VnobF;A2VCL0;Vs_bk;A3S27A3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S0S25S3eVs_bk;S42A2S27A3").
Hypothesis S_bk0 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S40A2SfS57S12S40A1S10Z1A1A3A3").
Hypothesis S_bk2 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S41A2SfS57S12S41A1S12S73A1A3A3").
Hypothesis S_bk3 : ltac2:(tb__ "0|0|
S0SdS3dVs_bk;S43A2SfS57S61SfS58SfS5aS12S40A1S10ZffffffffffffffffA1A3S10Z2A1A3A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S6bS11S62S16S30S31VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S6bS11S1bS62A1S16S30S31VLX;A1A1A1A3").

Lemma faend_val : ltac2:(tb__ "0|0|
SeS51Vrb;R1A2S52VA;Vrb;R2A3S0S21S3cQ40S1cR3S61A2A2S5S4eVA;Vrb;A2S7Z4S5Vnf;Vnew;A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (need_val A rb r CF PF HGh) as NV. fold nv c cs nf new in NV.
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). fold nv c in E158.
  unfold faend_e. cbn [eval]. rewrite add_val. fold (eval r need_e). rewrite NV.
  unfold fa_e2, rb_e, vSB, V_CLS. cbn [eval]. rewrite !add_val, sll_val, E155, E158, !u64_lit by (clear -C1 G13 G14; lia).
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 32)) by (clear -C1; lia).
  rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by (clear -C1 G13 G14; lia). rewrite (Z.mod_small (_ + _ * 2 ^ 32 + 3758096384)) by (clear -C1 G13 G14; lia).
  rewrite Z.mod_small by (clear -C1 G13 G14 N4 N5 N6; lia). rewrite FAr. clear; lia.
Qed.

Lemma fill_carve : ltac2:(tb__ "0|0|
S21SeS24S3aQ40A1A1S5fS1S6Z0R4A2S8R4Vnew;A2A2S36S35S38R5A1VCL0;R4R3R2A6S36S35S38R6A1VCL1;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof H as [HsmA HJ]. pose proof HJ as ((HFz & HGh & _ & _ & HR & _) & H0 & H2 & H3).
  set (Ci := FAb A rb + 4 * (nf + new - 1 - i)) in *.
  assert (CiR : FAb A rb + 4 * nf <= Ci /\ Ci + 4 <= FAb A rb + 4 * (nf + new)) by (unfold Ci; clear -Hi; lia).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & _ & _ & _ & _ & _ & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CL0) [O_pcc0; O_st; O_pcm; O_ri] r _ HW HE HFz Hsm SK_l XF_l) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  assert (E3 : bv_unsigned (eval r (SVar LV3)) = Ci) by (cbn [eval]; rewrite H3; apply u64_lit; clear -CiR N5 N6 N7 N8; lia).
  apply (SPA_carve_unk segs (JRfill i) r CL0 tp w (SVar LV3) (SLit 0) (SLit 4) LNX H W_l1 ltac:(apply Pos.eqb_eq in NX_l; rewrite NX_l; apply Pos.le_refl));
    rewrite ?E3, ?soff_lit_small by (clear; lia).
  - clear; lia.
  - clear; lia.
  - clear -CiR N5 N7; lia.
  - clear -CiR N5 N6 N7 N8; lia.
  - replace (Ci + 0) with Ci by (clear; lia). rewrite EO. apply Forall_app. split.
    + apply BZ. right; left. rewrite kSpaceSize_val. rewrite FAr in CiR. clear -CiR N5 N6 C1. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
        unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; rewrite FAr in CiR; clear -CiR N5 N6 C1 T1 PS1; lia.
  - intros a Ha. assert (Ha64 : 0x646000 <= a < 2 ^ 64) by (rewrite FAr in CiR; clear -Ha CiR N5 N6 C1 G13 G14; lia).
    pose proof (HDEF i (view segs (rm r)) ltac:(clear -Hi; lia) HR a ltac:(clear -Ha CiR; lia)) as D. rewrite view_in in D by (clear -Ha64; lia).
    pose proof (wok_rd_off_image (rm r) a) as WK.
    destruct (rd_of segs (rm r) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
  - unfold xwords_clear. rewrite XX_l. intros rr y j [].
Qed.

Lemma fill_iter : ltac2:(tb__ "0|1|
S21SeS24S3aQ40A1A1S5eS1S6Z0R4A2S8R4Vnew;A2A2S8S5R5Z1M0A2Vnew;A2SeVTR;S36S35S38S5R7G0A2A1VCL0;R1R5A5R4A2Fr';F_;S0S21S5R6G0A2Vnew;A3SeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S44S31VLX;A1VnobF;A2R1R6A5R5A2Fr';F_;VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  apply (tr_pre Kc TR KIT (SPA segs (JRfill i) CL1 r tp)); [intros w Hw; exact (fill_carve i r tp w Hi Hw)|].
  apply (tr_run Kc TR KIT F [0x41740; 0x4174c] CL1 [LB; LX] (JRfill i) r tp Q (JRfill_K i) (JRfill_stable i (ss_next (ax_S CL1)) eq_refl) R_l1 LN_l1).
  intros L r2 HL Hag.
  set (JREL := (fun r' t tr md => JRp (phL (i + 1)) r' t tr md /\ rw r' LV0 = rw r2 LV0 /\ rw r' LV2 = rw r2 LV2) : jpredA).
  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nobF (ss_objs (ax_S (la_state LL))) ++ [O_fcell] ->
            forall w, SPA segs (JRfill i) (la_state LL) r2 tp w ->
              exists r3, SPA segs JREL (keepn (la_state LL) nobF) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_fcell] (vms md tp ms)).
    apply (SPA_unobj_J (JRfill i) JREL r2 (la_state LL) _ [O_fcell] tp tr ms md HO Hw).
    intros Hsm HJ. split; [|split; reflexivity].
    exact (fill_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm HJ). }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. unfold F_lt in BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < new /\ rw r2 LV0 = Z_to_bv 64 (i + 1) /\ rw r2 LV2 = Z_to_bv 64 (au + i * S))).
    { intros w [_ ((HFz & HGh & _) & H0 & H2 & _)]. split; [|split; [exact H0 | exact H2]].
      destruct HGh as (_ & _ & _ & _ & _ & _ & _ & _ & Q228 & _). fold new in Q228.
      unfold branch_taken, bv_ltu, vNEW in BF. cbn [eval] in BF. rewrite H0, Q228, !u64_lit in BF by (clear -Hi N4; lia). apply Z.ltb_lt in BF. exact BF. }
    intros (Hlt & H0 & H2).
    apply (tr_cut Kc TR KIT valuation _ _ Q (REL LB OB_b)). intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRfill (i + 1)) CL0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J JREL (JRfill (i + 1)) _ CL0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & E0 & E2). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs. pose proof HJ as (HFz & HGh & _).
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
    assert (AIS : 0 <= au + i * S /\ au + (i + 1) * S <= 3758096384) by (clear -Hi Hlt N1 N2 N3; nia).
    split; [|split; [|split]].
    + eapply (JR_stable A Kc rb tp0 md0 (phL (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk0. cbn [eval]. rewrite E0, H0. apply bv_eq. rewrite add_val, !u64_lit by (clear -Hi N4; lia). rewrite Z.mod_small by (clear -Hi N4; lia). clear; lia.
    + cbn [rho_sub rw]. rewrite S_bk2. unfold V_SIZE. cbn [eval]. rewrite E2, H2, E148. apply bv_eq. rewrite add_val, !u64_lit by (clear -AIS N1; lia).
      rewrite Z.mod_small by (clear -AIS N1; lia). clear; lia.
    + cbn [rho_sub rw]. rewrite S_bk3. cbn [eval]. fold (eval r3 faend_e). apply bv_eq.
      rewrite add_val, (faend_val r3 HFz HGh), sll_val, xor_val, E0, H0.
      replace (bv_unsigned (Z_to_bv 64 18446744073709551615)) with 18446744073709551615 by reflexivity.
      rewrite !u64_lit by (clear -Hi N4 N5 N6 N7 N8; lia). rewrite lxor_ones64 by (clear -Hi N4; lia).
      change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia).
      replace (((18446744073709551615 - (i + 1)) * 2 ^ 2) mod 2 ^ 64) with (2 ^ 64 - 4 * (i + 2)).
      2: { apply (Z.mod_unique_pos _ _ 3); [clear -Hi N4; lia | clear; lia]. }
      rewrite (u64_lit (FAb A rb + 4 * (nf + new - 1 - (i + 1)))) by (clear -Hi Hlt N4 N5 N6 N7 N8; lia).
      symmetry. apply (Z.mod_unique_pos _ _ 1); [clear -Hi Hlt N4 N5 N6 N7 N8; lia | clear; lia].
  -
    apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. unfold F_lt in BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = new)).
    { intros w [_ ((HFz & HGh & _) & H0 & _)].
      destruct HGh as (_ & _ & _ & _ & _ & _ & _ & _ & Q228 & _). fold new in Q228.
      unfold branch_taken, bv_ltu, vNEW in BF. cbn [eval] in BF. rewrite H0, Q228, !u64_lit in BF by (clear -Hi N4; lia).
      destruct (Z.ltb_spec (i + 1) new) as [X|X]; [exfalso; apply BF; reflexivity | clear -X Hi; lia]. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ _ Q (REL LX OB_x)). intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phL new)) (keepn (la_state LX) nobF) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J JREL (JRp (phL new)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma fill_loop : ltac2:(tb__ "0|0|
S2fS21SeS24S3aQ40A1A1S5eS0S21S9Vnew;R4A2SaR5A1A3S1S6Z0R5A2S8R5Vnew;A2A2SeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S44S31VLX;A1VnobF;A2R1R5A5R4A2Fr';VTR;S36S35S38R7A1VCL0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [clear -Hn Hi; lia|].
  apply (fill_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [clear -Hn; lia | clear -Hi Hlt; lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variables (E3 LH : axst) (LFL LJP : leafA) (s_in : wsub).
Let FR : list sprop := factsR E3.
Let XLF : axst := ltac2:(tb__ "0|0|
S44S31VLX;A1VnobF;A2").
Let CXL : axst := cXL FR XLF.
Hypothesis R_h : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z41740S26S21A1A3VLH;S27A5S2aG0S23S32VLFL;S26S32A1A3A2A3").
Hypothesis LN_h : ltac2:(tb__ "0|0|
S0S25S17S30VLH;A1A1S28A3").
Hypothesis NX_h : ltac2:(tb__ "0|0|
S0S25S63S42S13S30VLH;A1A1A2S27A3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S0S25S34S31VLFL;A1VCL0;Vs_in;A3S27A3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S0S25S3eVs_in;S42A2S27A3").
Hypothesis S_in0 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S40A2S10Z1A1A3").
Hypothesis S_in2 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S41A2S4bA3").
Hypothesis S_in3 : ltac2:(tb__ "0|0|
S0SdS3dVs_in;S43A2SfS57S61S10N4A1A3A3").
Hypothesis W_xl : ltac2:(tb__ "0|0|
S0S25S19S30VCXL;A1A1S27A3").
Hypothesis D_xl : ltac2:(tb__ "0|4|
S0S29S2cS24S2cSdSdA2M0A1M1S24S11A1M2A2M3A1S70S30VXLF;A1S30VCXL;A1A2S2aG3S2dG1G2S26G0A1S23S11S46S23S11S47S26S11A1A3A3A4A2A3").
Hypothesis NX_xl : ltac2:(tb__ "0|0|
S0S25S64S13S30VCXL;A1A1S13S30VXLF;A1A1A2S27A3").
Hypothesis R_j : ltac2:(tb__ "0|1|
S0S29S24S32A1M0A1S33S35VF;S23S21Z413ccS26S21A1A3VCXL;S27A5S2aG0S23S32VLJP;S26S32A1A3A2A3").
Hypothesis LN_xl : ltac2:(tb__ "0|0|
S0S25S17S30VCXL;A1A1S28A3").
Hypothesis NXr_xl : ltac2:(tb__ "0|0|
S0S25S63S42S13S30VCXL;A1A1A2S27A3").

Theorem fill_all : ltac2:(tb__ "0|0|
SeS24S3aQ40A1A1S5eSeVTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;S39Vnew;A1A6S31VLJP;A1R1R3A5R2A2Fr';VTR;S36S35S4dVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX. destruct fill_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & FAr & C1 & G13 & G14).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41740] LH [LFL] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _.
  apply (tr_pre Kc TR KIT (SPA segs (JRfill 0) CL0 (rho_sub r1 s_in) tp)).
  { intros w Hw. apply (SPA_entails_J (JRp ph) (JRfill 0) _ CL0 s_in r1 tp w ENT_in); [|exact Hw].
    intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
    split; [|split; [|split]].
    - rewrite phL0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    - cbn [rho_sub rw]. rewrite S_in0. reflexivity.
    - cbn [rho_sub rw]. rewrite S_in2. unfold vAU. cbn [eval]. destruct HGh as (_ & _ & _ & Q223 & _). fold nv c cs au in Q223. rewrite Q223. f_equal. clear; lia.
    - cbn [rho_sub rw]. rewrite S_in3. cbn [eval]. fold (eval r1 faend_e). apply bv_eq. rewrite add_val, (faend_val r1 HFz HGh).
      replace (bv_unsigned (Z_to_bv 64 (-4))) with 18446744073709551612 by reflexivity. rewrite u64_lit by (clear -N4 N5 N6 N7 N8; lia).
      symmetry. apply (Z.mod_unique_pos _ _ 1); [clear -N4 N5 N6 N7 N8; lia | clear; lia]. }
  apply (fill_loop (Z.to_nat new) 0 _ tp Q); [clear -N4; lia | clear -N4; lia|].
  intros r2. fold XLF.

  apply (jr_restate A Kc rb tp0 md0 TR KIT XLF (ax_S CXL) _ _ (phL new) r2 tp Q W_xl D_xl NX_xl).
  { intros tr md (HFz & HGh & _) _. split; [constructor|].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
    destruct (new_nums A rb CF PF) as (_ & M2 & M3 & _ & M5 & M6 & _). cbn zeta in M2, M3, M5, M6. fold nv c cs in M2, M3, M5, M6. fold S nf au new in M2, M3, M5, M6.
    destruct HGh as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227. fold nf au new in Q221, Q223, Q228.
    destruct (kchunks_facts c C1) as (K1 & _).
    assert (NS : 0 <= new * S <= 3758096384) by (clear -N1 N2 N3 N4; nia).
    repeat apply Forall_cons; try apply Forall_nil.
    - unfold HINT_au. cbn [holds]. unfold branch_taken, bv_ltu, vMU, vAU, vNEW, V_SIZE. cbn [eval]. rewrite !add_val, mul_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N4 M2 M3; lia).
      rewrite (Z.mod_small (new * S)) by (clear -NS; lia). rewrite !Z.mod_small by (clear -NS N2 M2 M3; lia).
      intros X. apply Z.ltb_lt in X. clear -X M6. lia.
    - unfold HINT_k. cbn [holds]. unfold branch_taken, bv_ltu, vNF, vNEW, vK. cbn [eval]. rewrite add_val, Q221, Q227, Q228, !u64_lit by (clear -N4 N5 N6 K1; lia).
      rewrite Z.mod_small by (clear -N4 N5 N6; lia). intros X. apply Z.ltb_lt in X. clear -X M5 N5. lia. }
  change (ax_setS XLF (ax_S CXL)) with CXL.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x413cc] CXL [LJP] (phL new) r2 tp Q R_j LN_xl NXr_xl).
  intros L r3 [<-|[]] _. exact (HX r3).
Qed.
End FILL.
End SpineMallocR13.

(* [comment removed for export] *)
Module CDepotCallW.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "mul"; "opp"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SLit"; "sobj"; "sprop"; "rw"; "sstate"; "SVar"; "ss_next"; "ss_facts"; "SPUle"; "sv_eqb"; "SAlu"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "sprop_below"; "ss_objs"; "eval"; "swf"; "SExt"; "holds"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "cons"; "nat"; "nil"; "pair"; "prod"; "false"; "option"; "andb"; "orb"; "Some"; "app"; "None"; "fst"; "length"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW.DCW"; "X4"; "isSome"; "site_facts"; "X4r"; "osplit"; "permW"; "F_call"; "T4b"; "T4d"; "X4a"; "X4b"; "X4c"; "X4f"; "zoneR"; "R4_families"; "T40"; "T4a"; "T4c"; "T4m1"; "T4m2"; "T4m3"; "in_famb"; "prim_fitb"; "rt_okD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_depot"; "ag_spacebeg"; "topG"; "ag_ctx"; "ag_thread"; "sec_chunk"; "ageom"; "DG"; "aa_live"; "aa_sec"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PostD"; "PreD"; "nocells"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E4d"; "C5"; "upd"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "PIECES"; "V_CNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "V_DEPTH"; "malloc_depth"; "unwind_objs"; "J_alloc_preT"; "pre_facts"; "unwind_factsS"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "KEEPD"; "coveredb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "in_ranges"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "jpostA"; "J_ofPA"; "import_okPA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK"; "KD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "rz"; "ClassID"; "IMG_HI"; "IMG_LO"; "Sh"; "is_primary"; "kSpaceSize"; "needed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@LinuxProcessSemantics.Riscv.Instr";
"ALU_ADD"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "DFP"; "JLD"; "MAP1"; "MAP1N"; "STORE"; "dfp_static"; "DFPw"; "JD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "chk_of"; "cnt_of"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "geom_ok"; "inv3"; "primary_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD"; "AInvX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "HD_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "diffs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4"; "pvals_ok"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl"; "sobjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE"; "HDE_stmt"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_laws2 SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ap.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ap.SegD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section DCW.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.

Hypothesis HUS : stopJ_stable W st.

Hypothesis HUSr : ltac2:(tb__ "0|1|
S15S15S9Se0R1Sc2A2ScS68Q40A1S1aR3R2A2S1aR4R2A2A3F_;Fi;S89VW;Vst;R3A3M0G0F_;F_;Fr';Fr;").
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Hypothesis HCSTD : ltac2:(tb__ "0|0|
S8Sd9VCST;R1A2SfSbaR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S86VAInv;VW;Vst;VA;VKc;S1cPcA1A6").
Hypothesis Htmax : 1 <= tmax <= SZMAX.

Local Notation KEEPD := (CDepotCall.KEEPD CST XGL).

Definition F_call : list sprop := ltac2:(tb__ "0|3|
S2fS19S1fS17Z7fff7f800000A1M0S1cPaA1M1A2S2fS19S1fG0S21SafG1S17Nf10A1A3A2S2fS19S1fG0S21SafG1S17N848A1A3M2A2S2fS19S1fG2S17S7S4Z2Z40A2Z848A2A1A2S31S19A1A3A3A3A3").
Definition X4f : axst := ltac2:(tb__ "0|0|
Sd5S45S6eVW;Vst;Vtmax;A3A2").
Definition X4r (sz : Z) : axst := ltac2:(tb__ "0|1|
S70VW;Vst;Vtmax;S4bZ7e850S2fS33S30S16A2M0S32S30S16UbS17Vsz;A1A4S31G0A1A3S31S18A1S34S31S19A1A9").
Definition osplit (A : axst) (i : nat) (mid : sv) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9cS10VA;A1Vi;Vmid;A3S1bS13VA;R1A2LS';VA;X35x2").
Definition isSome {T} (o : option T) : bool := match o with Some _ => true | None => false end.
Definition X4a (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S42Vsz;A1U0S17Nf10A1A3").
Definition X4b (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S48Vsz;A1U1S17N910A1A3").
Definition X4c (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S49Vsz;A1U2S17N848A1A3").
Definition X4 (sz : Z) : axst := ltac2:(tb__ "0|0|
S43S4aVsz;A1U3S17N50A1A3").
Hypothesis NXE : ltac2:(tb__ "0|0|
ScS2cSdfSc2S1dS10S6eVW;Vst;Vtmax;A3A1A1A2S2eA3").
Hypothesis FBE : ltac2:(tb__ "0|0|
ScS2cS8fS19S26S1dS10S6eVW;Vst;Vtmax;A3A1A1A1S45A3S2eA3").
Hypothesis XE4 : ltac2:(tb__ "0|1|
ScS2dS33S16S16A2M0A1S12S6eVW;Vst;Vtmax;A3A1S31G0A1A3").
Hypothesis F192 : ltac2:(tb__ "0|1|
S91S19S2fS19S1fS17Z1A1S1cPc0A1M0A2S2fS19S1fG0S17Vtmax;A1A2S31S19A1A3A3S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FDEP : ltac2:(tb__ "0|0|
S91S19S87S84A1S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FUNW : ltac2:(tb__ "0|0|
S91S19S88VW;Vst;A2S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis FGEN4 : ltac2:(tb__ "0|0|
S91S19S71S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis YP4 : ltac2:(tb__ "0|0|
S90S19S1fS17Z1A1S1cS77A1A2S1eS10S6eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis WX4r : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS29S10S42R2A1A1A1S2eA3F_;Fsz;").
Hypothesis DX4r : ltac2:(tb__ "0|4|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS35S33S2dS33S16S16A2M0A1M1S2dS19A1M2A2M3A1SccS10S4bA1S10S42R2A1A1A2S38G3S32G1G2S2fG0S32S16S16S2aS34Q20S1cPc0A1A3S17R2A1A4S31G0A1A3S31S19A1A4A2A3F_;Fsz;").
Hypothesis SPL1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S42R2A1A1U0S17Nf10A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S48R2A1A1U1S17N910A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL3 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S49R2A1A1U2S17N848A1A3A2S2eA3F_;Fsz;").
Hypothesis SPL4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9cS10S4aR2A1A1U3S17N50A1A3A2S2eA3F_;Fsz;").

Definition call_pack (X : axst) (sz : Z) : option (wsub * list sobj * axst) := ltac2:(tb__ "0|6|
S2fS33S9S16A2M0S32S9S16PfS17N600A1A4Sd1P1S10VX;A1S10S66Vsz;A1M1A1A3A3S2dG0A1M2S35S2dS18A1M3A1S35S33S33S99G3A2S11A2M4A1Lx;Sa2VX;G1R1A3G3S38S33S33G2G3A2M5S11A2S32G5S11S32G2G3R2R1A4S9eR2G1S65Vsz;A1VX;R1A5A4A2LR;S3aG4A1X35x2Ts;").

Variables (s4 : Z -> wsub) (R4 : Z -> list sobj) (T4 : Z -> axst).
Hypothesis HER : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS35S2dS18A1M0A1Sa2S3fR2A1S66R2A1Vs4;R2A1A3S38G0VR4;R2A1A2A3F_;Fsz;").
Hypothesis HT4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS11S9eVs4;R2A1S66R2A1S65R2A1S3fR2A1VR4;R2A1A5VT4;R2A1A3F_;Fsz;").
Hypothesis XX4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS33S16S16A2M0A1S12S3fR2A1A1S31G0A1A3F_;Fsz;").
Hypothesis FBX4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS19S26S1dS10S3fR2A1A1M0A1A1S1eG0A1A3S2eA3F_;Fsz;").
Hypothesis Hchk4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cSa3S3fR2A1S66R2A1Vs4;R2A1VR4;R2A1S2fS11S65R2A1S31S11A1A3A5S2eA3F_;Fsz;").
Hypothesis NX4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS9S1dS10S3fR2A1A1A1S1dS10S6eVW;Vst;Vtmax;A3A1A1A3F_;Fsz;").
Hypothesis WG10 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PaM0A2S21SafS1cG0A1S17N910A1A3A3F_;Fsz;").
Hypothesis WG15 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PfA2S17N600A1A3F_;Fsz;").
Hypothesis WG12 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS16S97Vs4;R2A1PcA2S21SafS1cPaA1S17N848A1A3A3F_;Fsz;").

Definition R4_families : list sobj := ltac2:(tb__ "0|0|
S39S18SceS39S18S2fS18S72S2fS18S74S2fS18S73S2fS18S75S31S18A1A3A3A3A3S76A3A3").
Definition in_famb (o : sobj) : bool := ltac2:(tb__ "0|3|
S37S92S18S18SdaS67Vo;A1S67R1A1A2Lo';S39S18S4dS85VW;A1A3A3S36S20S22Vo;A1S1cPaA1A2S16S2cLx;S24Vo;A1S8S36S3N910R1A2S3R1Z0A2A2Llo;S9S36SdeR1S83A2S20S23Vo;A1S17Nf10A1A2A2Li;Sb0S16S16S34Lb;La;M0Lop;M1G1Sb1G0Lop;M2G2S2cSaS16S34La;Lw;Lsgn;S9S16S8S34Lk;Li;Ll;X16x8A2A2").
Hypothesis FAM4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS18S54VR4;R2A1A3S2eA3F_;Fsz;").
Hypothesis NEWO : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS18A1Sb4S10S66R2A1A1S10S65R2A1A1A2S31S18A1A3F_;Fsz;").
Hypothesis XPost : ltac2:(tb__ "0|1|
S8ScS2dS33S16S16A2M0A1S12S65R1A1A1S31G0A1A3Fsz;").

Hypothesis FBT4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS8fS19S26S1dS10VT4;R2A1A1A1A1S1eS10S3fR2A1A1A1A3S2eA3F_;Fsz;").
Hypothesis XT4 : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2dS33S16S16A2M0A1S12VT4;R2A1A1S31G0A1A3F_;Fsz;").
Definition T40 (sz : Z) : axst := ltac2:(tb__ "0|0|
Sd6VT4;Vsz;A1S1eS10S3fVsz;A1A1A1A2").
Definition oreb (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9dS10VA;A1Vi;A2S1bS13VA;R1A2LS';VA;X35x2").
Definition omrg (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S35S1bA1S11Lx;S9bS10VA;A1Vi;A2S1bS13VA;R1A2LS';VA;X35x2").
Definition T4a (sz : Z) : axst := oreb (T40 sz) 0.
Definition T4b (sz : Z) : axst := oreb (T4a sz) 1.
Hypothesis RB1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9dS10S4eR2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis RB2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9dS10S4fR2A1A1U1A2A2S2eA3F_;Fsz;").
Definition permW (n : nat) : list nat := ltac2:(tb__ "0|1|
S39S30S2fS30U9S2fS30U0S2fS30UaS2fS30U1S2fS30UbS2fS30U2S2fS30U3S2fS30U4S2fS30U5S2fS30U6S2fS30U7S2fS30U8S31S30A1A3A3A3A3A3A3A3A3A3A3A3A3Sc1UcM0Sd0Vn;G0A2A2A3").
Variable nobj : nat.
Hypothesis PERM_nd : ltac2:(tb__ "0|0|
ScS2cSd2S44Vnobj;A1A1S2eA3").
Hypothesis PERM_lt : ltac2:(tb__ "0|0|
ScS2cS8fS30S30SddR1Vnobj;A2Li;S44Vnobj;A1A3S2eA3").
Hypothesis PERM_cov : ltac2:(tb__ "0|0|
ScS2cS8fS30S30S92S30SdcR1A1S44Vnobj;A1A3Li;Sc1U0Vnobj;A2A3S2eA3").
Hypothesis PERM_len : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS30S3cS18S27S10S46R2A1A1A1A2Vnobj;A3F_;Fsz;").
Definition T4c (sz : Z) : axst := ltac2:(tb__ "0|2|
S13S46Vsz;A1M0Sd4S10G0A1M1Sd3S27G1A1S44Vnobj;A1A2A2A2").
Definition T4m1 (sz : Z) : axst := omrg (T4c sz) 0.
Definition T4m2 (sz : Z) : axst := omrg (T4m1 sz) 0.
Definition T4m3 (sz : Z) : axst := omrg (T4m2 sz) 0.
Definition T4d (sz : Z) : axst := omrg (T4m3 sz) 0.
Hypothesis MRG1 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S50R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG2 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S51R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG3 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S52R2A1A1U0A2A2S2eA3F_;Fsz;").
Hypothesis MRG4 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS40S1bS9bS10S53R2A1A1U0A2A2S2eA3F_;Fsz;").
Variable sd : Z -> wsub.
Hypothesis ENT5 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS14S47R2A1S6fVW;Vst;Vtmax;A3Vsd;R2A1A3S2eA3F_;Fsz;").
Hypothesis SID5 : ltac2:(tb__ "0|0|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS9aVsd;R2A1Sc2A2S2eA3F_;Fsz;").

Hypothesis R4cov : ltac2:(tb__ "0|1|
S8SbS0Z1R1A2S0R1Vtmax;A2A2ScS2cS94S1eS10S47R2A1A1M0A1VR4;R2A1S27G0A1A3S2eA3F_;Fsz;").

Definition rt_okD (o : sobj) : bool := ltac2:(tb__ "0|b|
S16S2cLx;M0S24Vo;A1S8G0S23Vo;A1S8S37S37S36S20S22Vo;A1M1S17Z0M2A1A2S36S36S36S3Sa9R2A2S3R2R1A2M3A2S3R1Sa8A2A2S37S3R1Sb9A2S3S1Sb7S5Z8Sb8A2A2R2A2A2A2A2S36S20G1S1cP97A1A2S36S36S3G2R2A2G3A2S3R1Z1000A2A2M4A2A2S36S20G1S1cP98A1A2G4A2A2Lhi;S9S34Li;M5Sb0S16S16S34Lb;La;M6Lop;M7G7Sb1G6Lop;M8G8S2cSaS16S34La;Lw;Lsgn;M9S9S16S8S34Lk;Li;Ll;MaX16x8Llo;G5G7G7G8G8G9GaX16x8").
Lemma RT_m1_okD : ltac2:(tb__ "0|0|
ScS2cS8fS18S56SceA3S2eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma obj_range_nocells : ltac2:(tb__ "0|0|
S15S18ScS33S8S8A2S25R2S67R1A1A2S25R2R1A2A3Fo;Frho;").
Proof. intros rho [b lo hi cs d]. reflexivity. Qed.

Definition zoneR (T C SB ab szc top a : Z) : Prop := ltac2:(tb__ "0|2|
SdSbSbS0Sa9Va;A2S2Va;Sa8A2A2SdS2Va;Sb9A2S0S1Sb7S5Z8Sb8A2A2Va;A2A2A2SdSbS0VT;Va;A2S2Va;S1VT;Z1000M0A2A2A2SdSbS0VC;Va;A2S2Va;S1VC;G0A2A2A2SdSbS0Vab;Va;A2S2Va;S1Vab;Vszc;A2M1A2A2SdSbS0SaaVab;A1Va;A2S2Va;SaaG1A1A2A2S0Vtop;Va;A2A2A2A2A2A2").

Lemma R4_zone : ltac2:(tb__ "0|a|
S8S15S57S18S8SbS0Z1M0R5A2S0R5Vtmax;A2A2S69Q40M1S1aR5PcA2A2S8ScfR6S5aS58R5A1A1SbdR1A1M2SbeR5R1A2Sa6R1A1Sa5G2A1R1A7SbS0G0SbfR6R2A2M3A2S0G3Z10M4A2A2ScS68G1A1M5S1aR8P97A2S6aG1S5dS58R7A1A1A2A3ScG5S1aR9P98A2S6aG1S5cS58R8A1A1A2A3ScG5S1aRaP95A2S6aG1SbfR9R5A2A2A3Sc3S58RaA1A1S0S5bS58RbA1A1S1S69G1S1aRcPaA2A2S6bG1S1aRcS83A2A2A2A2S0S6bG1S1aRdS83A2A2S6S84A1A2Sc0S18S18SbSbS0S1S5bS58ReA1A1G4A2S69G1S28RfS22R1A1A2A2M6A2S0G6S4Z2M7Z2fA2A2A2SbScS16S24R1A1S17N10A1A3ScS16S23R1A1S17Z0A1A3A2A2Lo;S85VW;A1A3S90S18RdVR4;R10A1A3SbS0S3bS8S8S25R10ReA2M8A3RdA2S2RdS3eS8S8G8A3A2A2S1S1S5aS58R10A1A1S5SbdRcA1S4G7Z20A2A2A2S5G4SbeR10RcA2A2A2S8S4cS5dS58R11A1M9A1S5cG9A1S5aG9A1R1Sa5SbdRdA1A1S5bG9A1RfA7Tab;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tnv;F_;Fa;Fo;FA;FrhoX;Fsz;").
Proof.
  intros sz rhoX A o a Hsz nv PV Hcnt E151 E152 E149 HG TOP DEP LNK Ho Ha ab.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T1 & T2 & _ & C1 & C2 & _ & _ & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  pose proof (pv_ab rhoX _ _ _ _ _ _ PV) as Eab. pose proof (pv_ub rhoX _ _ _ _ _ _ PV) as Eub. pose proof (pv_ue rhoX _ _ _ _ _ _ PV) as Eue.
  pose proof (pv_bsh rhoX _ _ _ _ _ _ PV) as Ebsh. pose proof (pv_bu rhoX _ _ _ _ _ _ PV) as Ebu. pose proof (pv_lu rhoX _ _ _ _ _ _ PV) as Elu.
  pose proof (pv_lp rhoX _ _ _ _ _ _ PV) as Elp. pose proof (pv_lt rhoX _ _ _ _ _ _ PV) as Elt. pose proof (pv_bp rhoX _ _ _ _ _ _ PV) as Ebp.
  pose proof (pv_br rhoX _ _ _ _ _ _ PV) as Ebr. pose proof (pv_lr rhoX _ _ _ _ _ _ PV) as [Elr Blr]. pose proof (r8_facts rhoX _ _ _ _ _ _ PV) as R8F.
  cbn zeta in Eab, Eub, Eue, Ebsh, Ebu, Elu, Elp, Elt, Ebp, Ebr, Elr, Blr, R8F. fold ab in Eab, Eub, Eue, Ebsh, Ebu, Ebp, Ebr.
  set (T := ag_thread (aa_geom A)) in *. set (CTX := ag_ctx (aa_geom A)) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  set (szc := Size (cls_of nv)) in *. set (rzv := rz nv) in *. set (x := chk_of A nv) in *. set (c := cls_of nv) in *.
  set (r8 := nv + 7 - (nv + 7) mod 8) in *. set (lp := if Z.eq_dec (nv mod 8) 0 then 0 else 1) in *.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_le_mono nv (nv + 7) 8 ltac:(lia) ltac:(lia)) as Q1.
  assert (AB8 : ab mod 8 = 0).
  { apply Z.mod_divide; [lia|]. destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(lia)) ltac:(tauto)) as [q Hq].
    exists (q * 2 ^ 13 + c * 2 ^ 29 + 2 * x). unfold ab. fold SB c x. lia. }
  assert (SHR : forall k, 0 <= k <= szc -> Sh ab <= Sh (ab + k) <= Sh (ab + szc)).
  { intros k Hk. unfold Sh. split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
  assert (SHK : forall k, 0 <= k -> Sh (ab + k) = Sh ab + k / 8).
  { intros k Hk. unfold Sh. destruct (proj1 (Z.mod_divide ab 8 ltac:(lia)) AB8) as [q Hq]. rewrite Hq.
    replace (q * 8 + k) with (q * 8 + k) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_mul by lia. lia. }

  pose proof (proj1 (forallb_forall _ _) (FAM4 sz Hsz) o Ho) as Fo. unfold in_famb in Fo. apply orb_prop in Fo as [Fo|Fo].
  - apply existsb_exists in Fo as (o' & Ho' & Eo). apply sobjb_sound in Eo.
    rewrite <- (obj_range_nocells rhoX o), Eo, (obj_range_nocells rhoX o') in Ha. clear Eo Ho o. rename o' into o.
    apply in_app_or in Ho' as [Ho'|HLK].
    2: {
      pose proof (proj1 (Forall_forall _ _) LNK o HLK) as (B & Elo & Ehi). destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in B, Elo, Ehi. subst olo ohi.
      rewrite obj_range_mk in Ha by (clear -B TG; lia). cbn [fst snd] in Ha. do 5 right. clear -Ha B. lia. }
    unfold R4_families in Ho'. apply in_app_or in Ho' as [HRT|Ho']; [|apply in_app_or in Ho' as [HPC|HPI]].
    +
      pose proof (proj1 (forallb_forall _ _) RT_m1_okD o HRT) as OK. unfold rt_okD in OK.
      destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in OK.
      destruct lo as [lo|i1|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate OK.
      destruct hi as [hi|i2|o2 a2 b2|o2 a2 b2|o2 a2 b2|o2 a2 b2|sg2 wd2 a2|l2 i2 k2]; try discriminate OK.
      apply orb_prop in OK as [OK|OK]; [apply orb_prop in OK as [OK|OK]|];
        apply andb_prop in OK as [EB OK]; apply sv_eqb_sound in EB; subst b.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply andb_prop in OK as [OK X1].
        apply Z.leb_le in OK. apply Z.leb_le in X1. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). cbn [fst snd eval] in Ha. rewrite u64_lit in Ha by (unfold IMG_LO, IMG_HI in OK, X0; lia). left.
        unfold IMG_LO, IMG_HI, STORE, MAP1, MAP1N in *. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E151, u64_lit in Ha by lia. right. left. lia.
      *
        apply andb_prop in OK as [OK X]. apply andb_prop in OK as [OK X0]. apply Z.leb_le in OK. apply Z.leb_le in X. apply Z.leb_le in X0.
        rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha. rewrite E152, u64_lit in Ha by lia. right. right. left. lia.
    +
      assert (EB : bv_unsigned (eval rhoX pc_base) = T + 0xd0 + 80 * c).
      { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
        rewrite (Z.mod_small (c * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. lia. }
      assert (ECH : soff rhoX choff = 16 + 4 * (cnt_of A nv - 1)).
      { unfold choff, V_CNT. rewrite soff_snorm. unfold U. cbn [eval]. rewrite E149. rewrite add_val, sll_val, add_val, !u64_lit by (clear - Hcnt; lia).
        replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
        replace ((cnt_of A nv + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt_of A nv - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
        change (2 mod 64) with 2. rewrite ?u64_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia.
        unfold snorm. rewrite Z.mod_small by lia. destruct (Z.ltb_spec ((cnt_of A nv - 1) * 2 ^ 2 + 16) (2 ^ 63)); lia. }
      assert (ET : bv_unsigned (eval rhoX vT) = T). { unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia. }
      right. left. destruct HPC as [<-|[<-|[<-|[<-|[]]]]].
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pcc] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pcs] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_pck] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite EB, ECH in Ha. cbn [fst snd] in Ha. lia.
      * unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi O_st] in Ha. rewrite !soff_lit_small in Ha by lia. rewrite ET in Ha. cbn [fst snd] in Ha. lia.
    +
      assert (ELL : soff rhoX LLe = 2 * (rzv / 16 * 2) / 2).
      { destruct (proj1 (Z.mod_divide rzv 16 ltac:(lia)) ltac:(tauto)) as [qr Hqr].
        apply soff_of_val; [|first [clear - Brz Hqr; lia | lia]]. unfold LLe. cbn [eval]. unfold V_RZ. rewrite E150, srl_val, !u64_lit by lia. change (3 mod 64) with 3.
        rewrite Z.shiftr_div_pow2 by lia. rewrite Hqr. replace (qr * 16 / 2 ^ 3) with (2 * qr) by (apply Z.div_unique with 0; lia).
        replace (qr * 16 / 16) with qr by (apply Z.div_unique with 0; lia). first [clear - Hqr Brz; lia | lia]. }
      destruct (proj1 (Z.mod_divide rzv 16 ltac:(lia)) ltac:(tauto)) as [qr Hqr]. rewrite Hqr in ELL.
      replace (qr * 16 / 16) with qr in ELL by (apply Z.div_unique with 0; lia). replace (2 * (qr * 2) / 2) with (2 * qr) in ELL by (apply Z.div_unique with 0; lia).
      assert (SHab : Sh (ab + rzv) = Sh ab + 2 * qr). { rewrite (SHK rzv) by lia. rewrite Hqr. replace (qr * 16 / 8) with (2 * qr) by (apply Z.div_unique with 0; lia). lia. }
      destruct HPI as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; unfold obj_range, obj_lo_of, obj_hi_of in Ha;
        cbn [ob_base ob_lo ob_hi O_H O_UB O_T O_L O_U O_P O_R] in Ha; rewrite ?soff_lit_small in Ha by lia.
      * rewrite Eab in Ha. rewrite (soff_of_val rhoX (SVar V_RZ) rzv) in Ha by (cbn [eval]; unfold V_RZ; rewrite ?E150; first [apply u64_lit; lia | lia]).
        cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Eub in Ha. rewrite (soff_of_val rhoX (SVar 12) nv) in Ha by (cbn [eval]; rewrite ?E12; first [apply u64_lit; lia | lia]).
        cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Eue in Ha. rewrite (soff_of_val rhoX LTe _ Elt) in Ha by lia. cbn [fst snd] in Ha. do 3 right. left. lia.
      * rewrite Ebsh, ELL in Ha. cbn [fst snd] in Ha. do 4 right. left. rewrite (SHK szc) by lia.
        pose proof (Z.div_le_mono rzv szc 8 ltac:(lia) ltac:(lia)). assert (rzv / 8 = 2 * qr) by (rewrite Hqr; symmetry; apply Z.div_unique with 0; lia). lia.
      * rewrite Ebu in Ha. rewrite (soff_of_val rhoX LUe (nv / 8) Elu) in Ha by (first [clear - Bn Q0; lia | lia]). cbn [fst snd] in Ha. do 4 right. left.
        rewrite SHab in Ha. rewrite (SHK szc) by lia.
        pose proof (Z.div_le_mono (rzv + nv) szc 8 ltac:(lia) ltac:(lia)) as M. rewrite Hqr in M at 1. replace ((qr * 16 + nv) / 8) with (2 * qr + nv / 8) in M by (rewrite <- (Z.div_add_l (2 * qr)) by lia; f_equal; lia).
        lia.
      * rewrite Ebp in Ha. rewrite (soff_of_val rhoX LPe lp Elp) in Ha by (unfold lp; destruct (Z.eq_dec _ _); lia). cbn [fst snd] in Ha. do 4 right. left.
        rewrite SHab in Ha. rewrite (SHK szc) by lia. destruct R8F as (Q81 & Q82 & Q83 & Q84).
        pose proof (Z.div_le_mono (rzv + r8) szc 8 ltac:(lia) ltac:(lia)) as M. rewrite Hqr, Q84 in M. fold lp in M.
        replace ((qr * 16 + (8 * (nv / 8) + (if Z.eq_dec (nv mod 8) 0 then 0 else 8))) / 8) with (2 * qr + nv / 8 + lp) in M.
        2:{ unfold lp. destruct (Z.eq_dec _ _); apply Z.div_unique with 0; lia. }
        unfold lp in *. destruct (Z.eq_dec _ _); lia.
      * rewrite Ebr in Ha. rewrite (soff_of_val rhoX LRe _ Elr) in Ha by (destruct R8F as (Q81 & Q82 & Q83 & Q84); pose proof (Z.div_le_upper_bound (szc - rzv - r8) 8) as DUB8; first [clear - Blr Bsz Brz Bn Q82 Q83 DUB8; lia | lia]).
        cbn [fst snd] in Ha. do 4 right. left. rewrite SHab in Ha. rewrite (SHK szc) by lia. destruct R8F as (Q81 & Q82 & Q83 & Q84).
        assert (Y1 : r8 / 8 + (szc - rzv - r8) / 8 <= (szc - rzv) / 8).
        { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le r8 8 ltac:(lia)). pose proof (Z.mul_div_le (szc - rzv - r8) 8 ltac:(lia)). lia. }
        pose proof (Z.div_le_mono (szc - rzv) szc 8 ltac:(lia) ltac:(lia)) as Y2. pose proof (Z.div_pos r8 8 ltac:(lia) ltac:(lia)) as Y3.
        assert (Y4 : rzv / 8 = 2 * qr) by (rewrite Hqr; symmetry; apply Z.div_unique with 0; lia).
        assert (Y5 : (szc - rzv) / 8 + 2 * qr <= szc / 8).
        { rewrite <- Y4. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (szc - rzv) 8 ltac:(lia)). pose proof (Z.mul_div_le rzv 8 ltac:(lia)). lia. }
        lia.
  -
    apply andb_prop in Fo as [Fb Fl]. apply sv_eqb_sound in Fb.
    destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in Fb, Fl. subst b.
    pose proof (urange (rw rhoX 10%positive)) as R10. pose proof (srange (rw rhoX V_DEPTH)) as R15.
    do 5 right. unfold obj_range, obj_lo_of, obj_hi_of in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
    destruct lo as [lo|i|o1 a1 b1|o1 a1 b1|o1 a1 b1|o1 a1 b1|sg wd a1|l1 i1 k1]; try discriminate Fl.
    +
      apply andb_prop in Fl as [Fl Fl2]. apply Z.leb_le in Fl. apply Z.leb_le in Fl2. cbn [fst snd] in Ha.
      rewrite soff_lit_small in Ha by lia. unfold malloc_depth in DEP. lia.
    + apply andb_prop in Fl as [Fi Fl]. apply Pos.eqb_eq in Fi. subst i. apply sv_eqb_sound in Fl. subst hi. rewrite soff_lit_small in Ha by lia.
      unfold soff in Ha. cbn [eval] in Ha. change 15%positive with V_DEPTH in Ha. cbn [fst snd] in Ha. lia.
Qed.

Definition prim_fitb (n : Z) : bool := ltac2:(tb__ "0|0|
S37S3dSabVn;A1A1S3S1Vn;Sa6Vn;A1A2Sa5Sa7SadVn;A1A1A1A2A2").
Lemma prim_fitb_all : ltac2:(tb__ "0|1|
S8SbS0Z1M0R1A2S2R1S1G0Z10000A2A2A2ScS2cS55R2A1S2eA3F_;Fn;").
Proof. intros n Hn. apply (forall_rangeZ_ok prim_fitb 1 65536); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma prim_fit : ltac2:(tb__ "0|0|
S8S0Z1R1A2ScS2cSabR2A1S2eA3S0S1R3Sa6R3A1A2Sa5Sa7SadR3A1A1A1A2F_;F_;Fn;").
Proof.
  intros n Hn HP. destruct (Z_lt_le_dec n (1 + 65536)) as [L|L].
  - pose proof (prim_fitb_all n ltac:(lia)) as H. unfold prim_fitb in H. rewrite HP in H. cbn [negb orb] in H. apply Z.leb_le in H. exact H.
  - exfalso. unfold is_primary, needed, kMaxSize, kChunkHeader2Size in HP. apply Z.leb_le in HP.
    pose proof (round_up_ge8 (Z.max n 16)). unfold rz in HP. rewrite Z.shiftl_mul_pow2 in HP by (unfold rz_log; repeat destruct (_ <=? _); lia).
    assert (0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; [lia | unfold rz_log; repeat destruct (_ <=? _); lia]). lia.
Qed.

Lemma live_user_zone : ltac2:(tb__ "0|2|
Sd8S57S8S8S8Sc3S58R4A1A1Sc4R5A1Sc5R7R6A2Sc6R8R7A2S90S33S8S8A2S32S8S8R7R6A4S61R8A1A3S0Z1R7A2SbS0R9R7A2S2R7S1R9R8A2A2A2SdSbS0S5aS58RbA1A1M0R8A2S2R8S1S1G0SacA2Z1000A2A2A2SeS5eS5eSbS90S5eR1S62RcA1A3SbS0S63R1A1M1R9A2S2R9S1G1S64R1A1A2A2A2A2Lch;A2A2F_;F_;F_;F_;F_;F_;F_;Fz;Fn;Fb;FA;Fm;").
Proof.
  intros m A b n z HG HI3 HP HS Hin Hn Hz. destruct HI3 as (_ & LIV3 & _).
  destruct (LIV3 b n Hin) as [EP|(ch & Hch & Eb & Esz)].
  - left. pose proof (primary_cls n ltac:(lia) EP) as Hc. pose proof (prim_fit n ltac:(lia) EP) as FIT. pose proof (rz_bound n) as RZ.
    destruct HP as (_ & _ & _ & P4).
    destruct (P4 _ Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
    destruct (LV b n Hin EP eq_refl) as (R1 & R2 & R3).
    pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
    pose proof (Size_pos _ Hc) as SP.
    set (c := ClassID (needed n)) in *. clearbody c.
    unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in *. unfold region_beg, kRegionSize in R1, R3. rewrite kSpaceSize_val.
    nia.
  - right. exists ch. split; [exact Hch|]. destruct HS as (HS1 & _). destruct (In_nth_error _ _ Hch) as (i & Hi).
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & D11 & D12 & _).
    assert (RU : forall x, x <= round_up x PG) by (intros x; unfold round_up, PG; pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)); lia).
    pose proof (RU (sc_size ch)). pose proof (round_up_ge8 n). unfold PG in *. lia.
Qed.

Lemma DFP_split : ltac2:(tb__ "0|0|
S60S8Sb5R2R1A2SdSbaR2A1SbbR3R2A2A2F_;Fa;FG;").
Proof. intros G a [H|[H|H]]; [left; exact H | right; right; left; exact H | right; right; right; exact H]. Qed.

Lemma keep_not_DFP : ltac2:(tb__ "0|0|
S57S15S2dS68Q40A1A1S6cS8Sc7R5R4R3R2A4S93VCST;VXGL;R6R2A4SfSb5S59R7A1R3A2A1F_;F_;Fa;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md a HX HK HD.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot A) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HK as [HC|HSH].
  - destruct (client_addr_cases CST A a _ HF HC) as [ST|[(b & n & Hbn & Hab)|[FR|[HCa|FL]]]].
    + apply (GOAL (topG (aa_geom A) <= a)); [intros H; apply ZN; do 9 right; exact H | lia | apply (NS (topG (aa_geom A)) (2 ^ 47)); [lia | unfold MAP1, MAP1N; lia]].
    + destruct (Hsep b n Hbn) as (N1 & _).
      destruct (live_user_zone _ A b n a HG HI3 HP HS Hbn N1 Hab) as [SP|(ch & Hch & Hz)].
      * apply (GOAL _ (fun H => ZN (or_intror (or_introl H))) SP). eapply NS; [exact SP | unfold MAP1, MAP1N; lia].
      * apply (GOAL (exists ch, In ch (aa_sec A) /\ sc_map_beg ch <= a < sc_map_beg ch + sc_map_size ch)).
        -- intros H. apply ZN. do 7 right. left. exact H.
        -- exists ch. exact (conj Hch Hz).
        -- destruct (In_nth_error _ _ Hch) as (i & Hi). destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _).
           pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as CB. eapply NS; [exact Hz | unfold IMG_HI in CB; unfold MAP1, MAP1N; lia].
    + destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_kFlagsOffset_val in M.
      apply (GOAL (ag_fsb (aa_geom A) <= a < ag_fsb (aa_geom A) + FS_total)); [intros H; apply ZN; do 5 right; left; exact H | lia |].
      eapply NS; [exact Hx | unfold IMG_HI in M; unfold MAP1, MAP1N; lia].
    + destruct (HCST _ HCa) as [X _]. apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | | exact (HCSTD a HCa)].
      split; [exact X|]. intros [Hs _]. exact (HCSTD a HCa Hs).
    + destruct FL as (c & p & Hc & Hp & _ & Ex). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M. rewrite FS_frames_off_val, FS_kFlagsOffset_val in M. rewrite <- Ex in M.
      apply (GOAL (ag_fsb (aa_geom A) <= a < ag_fsb (aa_geom A) + FS_total)); [intros H; apply ZN; do 5 right; left; exact H | lia |].
      apply (NS a (a + 1)); [lia | unfold IMG_HI in M; unfold MAP1, MAP1N; lia].
  - pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep HSH) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | |];
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; [lia|].
    eapply NS; [split; [apply Z.le_refl | apply Z.lt_succ_diag_r] | unfold MAP1, MAP1N; lia].
Qed.

Lemma zoneR_not_DFP : ltac2:(tb__ "0|0|
S57S15S2dS68Q40A1A1S6cS8S8S8Sc7R7R6R5R4A4S58R8A1S5fS0S5aR1A1R5A2S0S1R6R5A2S1S5aR2A1SacA2A2S0Z0R6A2S2S1R8R7A2S4Z2Z2fA2A2S4cS5dR5A1S5cR5A1S5aR5A1R9R8S5bR5A1R7A7SfSb5S59ReA1R8A2A1F_;F_;F_;F_;F_;TG;F_;Fa;Fszc;Fab;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md ab szc a HX G Hab1 Hab2 Hsz Hab3 HZ HD. subst G.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2, Hab2.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot A) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_split _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HZ as [[Z1 Z2]|[ZT|[ZC|[ZA|[ZS|ZK]]]]].
  - apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | |].
    + split; [exact Z1|]. intros [Hs _]. pose proof (dstat_range a Hs). lia.
    + intros Hs. pose proof (dstat_range a Hs). lia.
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_introl H)))) ZT). eapply NS; [exact ZT | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_introl H))))) ZC). eapply NS; [exact ZC | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL (ag_spacebeg (aa_geom A) <= a < ag_spacebeg (aa_geom A) + kSpaceSize + 4096)); [intros H; apply ZN; right; left; exact H | rewrite kSpaceSize_val; lia |].
    apply (NS (ag_spacebeg (aa_geom A)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
  - pose proof (Sh_in_band ab ltac:(lia)) as B1. pose proof (Sh_in_band (ab + szc) ltac:(lia)) as B2.
    apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | lia |].
    apply (NS SHADOW_BAND_LO (a + 1)); [lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, MAP1, MAP1N; lia].
  - apply (GOAL (topG (aa_geom A) <= a)); [intros H; apply ZN; do 9 right; exact H | exact ZK |].
    apply (NS (topG (aa_geom A)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
Qed.

Lemma SPA_updR : ltac2:(tb__ "0|5|
S7bS15S11S8S2dS33S30S16A2A1S2dS68Q40A1A1S8aS2dS33S16S16A2A1M0S2dS19A1M1ScS2cS29S10S70VW;Vst;Vtmax;R7R6R5S31S18A1M2S34S31S19A1M3A9A1A1S2eA3ScS35S33G0G1A2M4A1SccS10R8A1S10S70VW;Vst;Vtmax;R8R7R6G2S34G3A9A1A2S38G4S32G0G1R3R2A4A2A3ScdRaR4A2Sc0S19S2bRbA1R4A3S78Vsegs;RdRbRcR8R7A6S78Vsegs;ReS70VW;Vst;Vtmax;RcRbRaG2S34G3A9RdR9R8A6F_;F_;F_;F_;F_;Fnf;Fd;Fw;FtpY;Fru;Fpc;FE;FrhoY;FJx;").
Proof. intros Jx rhoY E pc ru tpY w d nf Hw Hd Hok Hnf HE. unfold CertCallocSP.upd. eapply SPA_restate; [exact Hw | exact Hd | reflexivity | exact Hok | exact Hnf | exact HE]. Qed.

Definition site_facts (A : AA) (rho rhoE : valuation) (sz : Z) : Prop := ltac2:(tb__ "0|c|
SbSbS0Z1M0Vsz;A2S0Vsz;Vtmax;A2A2SbS0S6bQ40M1S1aVrhoE;S83A2A2M2S6S84A1A2SbSc3S58VA;A1M3A1SbScS68G1A1M4S1aVrhoE;PcM5A2M6S1aVrho;G5A2A3SbS69G1G6A2S8SbScfVrhoE;S5aG3A1SbdR1A1M7SbeVA;R1A2Sa6R1A1Sa5G7A1R1A7SbSbS0G0SbfVA;R1A2M8A2S0G8Z10M9A2A2ScG4S1aVrhoE;P95A2S6aG1G8A2A3A2A2Tnv;SbScG4S1aVrhoE;P97A2S6aG1S5dG3A1A2A3SbScG4S1aVrhoE;P98A2S6aG1S5cG3A1A2A3SbS0S5bG3A1MaS1S69G1S1aVrhoE;PaA2A2G2A2A2Sc0S18S18SbSbS0S1GaG9A2S69G1S28VrhoE;S22R1A1A2A2MbA2S0GbS4Z2Z2fA2A2A2SbScS16S24R1A1S17N10A1A3ScS16S23R1A1S17Z0A1A3A2A2Lo;S85VW;A1A3A2A2A2A2A2A2A2A2").

Lemma dc_facts : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40M0A1A1S8aS78Vsegs;S8eVW;Vst;R6R5R4A5S6eVW;Vst;Vtmax;A3R3R2R1A6S41R7R5R4S69G0S1aR4Pc0A2A2A4F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof Hag as (Hagw & Hagl & Hagm).
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB. unfold top_high in Htop.
  pose proof (JG_rigid nW st A Kc rho rhoE tp tr md (proj2 Hw)) as (E12 & E148 & E149 & E150 & E158 & E159).
  assert (FACT : forall p, In p (ss_facts (ax_S (E4d W st tmax))) -> holds rhoE p).
  { intros p Hp. exact (fact_of_state nW st A Kc rho rhoE tp _ _ p Hw Hp). }
  pose proof (FACT _ (F192 _ (or_introl eq_refl))) as Fs1. pose proof (FACT _ (F192 _ (or_intror (or_introl eq_refl)))) as Fs2.
  cbn [holds eval] in Fs1, Fs2. rewrite u64_lit in Fs1 by lia. rewrite u64_lit in Fs2 by (unfold SZMAX in Htmax; lia).
  pose proof (FACT _ (FDEP _ ltac:(unfold pre_facts, F_depth; cbn [app]; do 2 right; left; reflexivity))) as Fd1.
  cbn [holds eval branch_taken] in Fd1. unfold bv_lts in Fd1. apply negb_true_iff in Fd1. apply Z.ltb_ge in Fd1.
  change (bv_signed (Z_to_bv 64 (- malloc_depth))) with (- malloc_depth) in Fd1.
  pose proof (proj1 HA) as HG.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  pose proof (cnt_pos_of_fact nW st A Kc rho rhoE tp _ _ Hw YP4) as Hcnt.
  pose proof (JGb_pvals nW st A Kc rho rhoE tp _ _ (conj (proj1 Hw) (JG_JGb nW st A Kc rho rhoE tp tr md (proj2 Hw))) FGEN4 Hcnt) as PV.
  cbn zeta in PV. rewrite <- E12 in PV, Hcnt, E149.
  pose proof PV as (_ & _ & _ & _ & _ & _ & Bn & _).
  assert (Hcnt16 : 1 <= cnt_of A (bv_unsigned (rw rhoE 12%positive)) <= 16).
  { split; [exact Hcnt|]. pose proof (pc_entry_facts segs A rhoE tp md _ HA Bn Hcnt) as PF. cbn zeta in PF. destruct PF as (_ & _ & _ & _ & X & _). exact X. }
  split; [lia|]. split; [exact Fd1|]. split; [exact HG|]. split; [exact E12|]. split; [exact (conj PV (conj Hcnt16 E149))|].
  split; [exact E151|]. split; [exact E152|]. split; [exact Htop|].
  pose proof (topG_range (aa_geom A)) as TGr. pose proof (srange (rw rhoE V_DEPTH)) as R15. unfold malloc_depth in Fd1.
  apply (unwind_objs_above W rhoE (topG (aa_geom A))); [|clear -Htop Fd1; lia | clear -TGr; lia].
  apply Forall_forall. intros p Hp. apply FACT. apply FUNW.
  unfold unwind_factsS. destruct st; [apply chain_pre_in; exact Hp|]. destruct W as [|l0 W0']; [destruct Hp | exact Hp].
Qed.

Lemma dc_site : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40M0A1A1S8aS78Vsegs;S8eVW;Vst;R6R5R4A5S6eVW;Vst;Vtmax;A3R3R2R1A6S78Vsegs;S8eVW;Vst;R7R6R5A5S3fS69G0S1aR4Pc0A2A2A1R4R3R2A6F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w Hw. pose proof (dc_facts A Kc rho rhoE tp w Hw) as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *. destruct w as [tr [ms md]].
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG. unfold malloc_depth in Fd1.

  assert (Em3808 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-3856)))) = bv_unsigned (rw rhoE 10%positive) - 3856).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-3856))) with (2 ^ 64 - 3856) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (HwF : SPA segs (JG W st A Kc rho) X4f rhoE tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 Hw)]. unfold X4f. apply (smatchA_add_facts segs rhoE tp F_call _ _ (proj1 Hw)); [|exact FBE]. unfold F_call.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?Em3808, ?Em2112; cbn [eval]; rewrite ?u64_lit by lia; lia. }

  assert (HwR : SPA segs (JG W st A Kc rho) (X4r sz) rhoE tp (tr, mkCfg ms md)).
  { unfold X4r. eapply SPA_updR; [exact (WX4r sz Hsz) | exact (DX4r sz Hsz) | | constructor | exact HwF].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd eval].
    apply bv_eq. change 32%N with (8 * N.of_nat 4)%N. rewrite ext_low_false_unsigned by lia. rewrite u64_lit by (unfold SZMAX in Htmax; lia).
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by (unfold SZMAX in Htmax; lia). reflexivity. }

  assert (OS : forall (Jx : jpredA) X i mid, isSome (split_obj_at (ax_S X) i mid) = true ->
            SPA segs Jx X rhoE tp (tr, mkCfg ms md) -> SPA segs Jx (osplit X i mid) rhoE tp (tr, mkCfg ms md)).
  { intros Jx X i mid Hs HX. unfold osplit. destruct (split_obj_at (ax_S X) i mid) as [S'|] eqn:E; [|exact HX]. eapply (SPA_split segs); [exact E | exact HX]. }
  unfold X4. apply OS; [exact (SPL4 sz Hsz)|]. unfold X4c. apply OS; [exact (SPL3 sz Hsz)|]. unfold X4b. apply OS; [exact (SPL2 sz Hsz)|].
  unfold X4a. apply OS; [exact (SPL1 sz Hsz)| exact HwR].
Qed.

Lemma dc_R4 : ltac2:(tb__ "0|2|
S57S15S15S8S41R4R3R2R1A4S57S15S2dS68Q40M0A1M1A1S6cG1Sc7R5R4R3R2A4ScS5fS58R6A1S58RbA1A3S98RaVR4;R9A1R3A3SfSb5S59R8A1S69G0R4A2A2A1F_;F_;F_;Fa;Fmdx;Ftpx;Frx;FAx;F_;Fsz;FrhoE;Frho;FA;").
Proof.
  intros A rho rhoE sz (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK) Ax rx tpx mdx a HX EG (o & Ho & Hoa) HD.
  cbn zeta in PV. pose proof PV as (_ & _ & _ & _ & _ & _ & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).
  pose proof (R4_zone sz rhoE A o (bv_unsigned a) Hsz PV Hcnt16 E151 E152 E149 HG Htop Fd1 LNK Ho Hoa) as HZ. cbn zeta in HZ. rewrite <- EG in HZ.
  refine (zoneR_not_DFP Ax rx tpx mdx _ _ (bv_unsigned a) HX _ _ _ _ HZ HD); rewrite ?EG; rewrite ?kSpaceSize_val; lia.
Qed.

Lemma dc_entry : ltac2:(tb__ "0|1|
S57S81S15S15S2dS68Q40A1A1S8S2dS6dA1M0S7eS6cS41R9R7R6R4A4S82R9A1S79Vsegs;R8R7S3fR6A1S32G0S7fR5S80R4R3A2A4A5S8eVW;Vst;RcRbRaR9R8R6R4A9SbcSaeSa4RdRcRaA3S59RdA1S96S95RaVR4;R8A1S7dR5R9R6A3A3Vs4;R8A1A2R9R7R5A7F_;F_;F_;F_;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 [Hag0 HJ0].
  pose proof SF as (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK). unfold malloc_depth in Fd1.
  pose proof HJ0 as (HA0 & HK0 & _ & _ & HB0 & HN0 & _). cbn [eval] in HB0, HN0.
  pose proof (AInvA_budget A rhoE tp md0 HA0) as (_ & _ & _ & HKm0 & _).
  pose proof (urange (rw rhoE 10%positive)) as R10. pose proof (topG_range (aa_geom A)) as TG.
  assert (Em2272 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2320)))) = bv_unsigned (rw rhoE 10%positive) - 2320).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2320))) with (2 ^ 64 - 2320) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Em2112 : bv_unsigned (eval rhoE (SAlu ALU_ADD (SVar 10) (SLit (-2120)))) = bv_unsigned (rw rhoE 10%positive) - 2120).
  { cbn [eval]. rewrite add_val. replace (bv_unsigned (Z_to_bv 64 (-2120))) with (2 ^ 64 - 2120) by reflexivity.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
  split.
  - apply (KD_intro A Kc rhoE _ HB0 HKm0 tp tr0 md0 HA0 HK0). unfold TOPr, V_DEPTH. cbn [rw rho_sub rho_absorb].
    rewrite (WG10 sz Hsz), (WG15 sz Hsz), (WG12 sz Hsz), !eval_absorb, Em2272, Em2112.
    change (bv_signed (eval rhoE (SLit (-1536)))) with (-1536). lia.
  - destruct (AInvA_X A rhoE tp md0 HA0) as (HX0 & HD0 & _).
    apply (depot_inv_frame segsA (aa_depot A) rhoE _ md0 tp); [|exact HD0]. intros a Ha. apply view_agree. intros Hr.
    apply rm_absorb_out. intros Hin. apply (dc_R4 A rho rhoE sz SF A rhoE tp md0 _ HX0 eq_refl Hin). rewrite u64_lit by exact Hr. exact Ha.
Qed.

Lemma dc_exit_ok : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS41ReRcRbR9A4S82ReA1Sb6SaeSa4R10RfRdA3S59R10A1A3S9fS96S95ReVR4;RcA1S7dR9RdRaA3A3Vs4;RcA1A2S15S79Vsegs;RfReS3fRdA1S32G1S7fRcS80RbRaA2A4A5S8eVW;Vst;R13R12R11R10RfRdRbA9Sb2S1dS10S66RfA1A1A1R3RbA3S79Vsegs;RcRbS65R10A1S32G1S7fRaS80R9R8A2A4A5R6R5R12RdRcRbR9A6Sa1R14S7dRfR13R10A3VR4;R12A1Vs4;R12A1S66R12A1S65R12A1S3fR12A1ReA8F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 [Hag0 HJ0] HagL HsmL HJL.
  pose proof SF as (Hsz & _). subst JL.
  destruct HJL as (G' & HKD' & HDI' & Hdpost & HRM & HVW & HRL & (l0 & EtpL)).
  split; [split|split].
  - intros a Hin. apply HRM. pose proof HKD' as (HXK & _). exact (dc_R4 A rho rhoE sz SF _ rhoE tpL md' a HXK eq_refl Hin).
  - intros o' oR Ho' HoR. rewrite (NEWO sz Hsz) in Ho'. destruct Ho'.
  - intros r a j oR Hr. rewrite (XPost sz) in Hr. destruct Hr.
  - intros r a j Hr. rewrite (XX4 sz Hsz) in Hr. destruct Hr.
Qed.

Lemma dc_exit_core : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS41ReRcRbR9A4S82ReA1Sb6SaeSa4R10RfRdA3S59R10A1A3S9fS96S95ReVR4;RcA1S7dR9RdRaA3A3Vs4;RcA1A2S15S79Vsegs;RfReS3fRdA1S32G1S7fRcS80RbRaA2A4A5S8eVW;Vst;R13R12R11R10RfRdRbA9Sb2S1dS10S66RfA1A1A1R3RbA3S79Vsegs;RcRbS65R10A1S32G1S7fRaS80R9R8A2A4A5R6R5R12RdRcRbR9A6S15S8aSb3R16S7dR11R15R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R2R10A9S78Vsegs;Sa0RaR9R16R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R3R10R2A6SeS57S57SeS15S15SeS15S15SbSc9R1eR3A2SbScaS93VCST;VXGL;R1eA3R1cR2A3S78Vsegs;Sc8VW;Vst;R3R1dR2A5S6fVW;Vst;Vtmax;A3R1R14R6A6A2A2LrhoX;A2Lrho'';A2LA';A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc JL rhoC Hsm0 [Hag0 HJ0] HagL HsmL HJL rho' w' HLK [Hsm' HJ'].
  pose proof SF as (Hsz & Fd1 & HG & E12 & (PV & Hcnt16 & E149) & E151 & E152 & Htop & LNK).
  pose proof Hag0 as (Hagw & Hagl & Hagm).
  pose proof HJ0 as (HA0 & HK0 & Htp0 & HU0 & _ & HN0 & Htop0). cbn [eval] in HN0. unfold top_high in Htop0.
  pose proof (HER sz Hsz) as ER. pose proof (HT4 sz Hsz) as ET4.
  subst JL.
  destruct (entails_frA_sound segs (X4 sz) (PreD sz) (s4 sz) (R4 sz) rhoE tp tr0 ms0 md0 ER Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'.
  destruct HJ' as (G2 & HKD2 & HDI2 & Hdpost2 & HRM2 & HVW2 & HRL2 & (l2 & EtpL2)).
  pose proof HKD2 as (HX2 & HK2 & HL2 & HT2).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  rewrite ET4 in Hsm'.
  assert (NXlt : forall i, (i < GW)%positive -> (i < ss_next (ax_S (X4 sz)))%positive).
  { intros i Hi. eapply Pos.lt_le_trans; [exact Hi|]. rewrite (NX4 sz Hsz). apply Pos.leb_le. exact NXE. }

  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (X4 sz)))).
  { pose proof (proj1 Hsm0) as HsmX. pose proof HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfacts4).
    apply Forall_forall. intros p Hp.
    exact (proj1 (holds_agree_vals _ rhoE rho' p Hag' (proj1 (forallb_forall _ _) (FBX4 sz Hsz) p Hp)) (proj1 (Forall_forall _ _) Hfacts4 p Hp)). }
  assert (HT40 : SPA segs (J_ofPA (JLD segsA (KD A Kc rhoE) (aa_depot A)) (rho_sub (rho_absorb rhoE (R4 sz) (vms md0 tp ms0)) (s4 sz)) tp rhoL tpL) (T40 sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T40. apply (SPA_refacts segs); [exact (conj Hsm' HJc) | exact (FBT4 sz Hsz) | intros _; exact HF4]. }

  assert (AXr : forall X i, ax_X (oreb X i) = ax_X X) by (intros X i; unfold oreb; destruct (rebase_obj_at _ _); reflexivity).
  assert (AXm : forall X i, ax_X (omrg X i) = ax_X X) by (intros X i; unfold omrg; destruct (merge_objs_at _ _); reflexivity).
  assert (AX40 : ax_X (T40 sz) = []) by (unfold T40, ax_with_facts; cbn [ax_X ax_setS]; exact (XT4 sz Hsz)).
  assert (OR : forall (Jx : jpredA) X i, isSome (rebase_obj_at (ax_S X) i) = true -> ax_X X = [] ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (oreb X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX0 HX. unfold oreb. destruct (rebase_obj_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_rebase segs); [exact E | exact HX0 | exact HX]. }
  assert (OM : forall (Jx : jpredA) X i, isSome (merge_objs_at (ax_S X) i) = true ->
            SPA segs Jx X rho' tpL (tr2, mkCfg ms2 md2) -> SPA segs Jx (omrg X i) rho' tpL (tr2, mkCfg ms2 md2)).
  { intros Jx X i Hs HX. unfold omrg. destruct (merge_objs_at (ax_S X) i) as [S'|] eqn:E; [|exact HX]. eapply (SPA_merge segs); [exact E | exact HX]. }
  match type of HT40 with SPA _ ?Jx _ _ _ _ => set (JP := Jx) in HT40 end.
  assert (HT4b : SPA segs JP (T4b sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4b. apply OR; [exact (RB2 sz Hsz) | unfold T4a; rewrite AXr; exact AX40 |]. unfold T4a. apply OR; [exact (RB1 sz Hsz) | exact AX40 | exact HT40]. }

  assert (HT4c : SPA segs JP (T4c sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4c. apply (SPA_select segs); [exact HT4b | exact PERM_nd | |].
    - intros i Hi. rewrite (PERM_len sz Hsz). apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt i Hi).
    - intros i Hi. rewrite (PERM_len sz Hsz) in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }

  assert (HT4d : SPA segs JP (T4d sz) rho' tpL (tr2, mkCfg ms2 md2)).
  { unfold T4d. apply OM; [exact (MRG4 sz Hsz)|]. unfold T4m3. apply OM; [exact (MRG3 sz Hsz)|]. unfold T4m2. apply OM; [exact (MRG2 sz Hsz)|].
    unfold T4m1. apply OM; [exact (MRG1 sz Hsz)| exact HT4c]. }
  assert (AX4d : ax_X (T4d sz) = []).
  { unfold T4d, T4m3, T4m2, T4m1. rewrite !AXm. unfold T4c. cbn [ax_X ax_setS]. unfold T4b, T4a. rewrite !AXr. exact AX40. }
  clear HT40 HT4b HT4c OR OM.

  assert (RNG : forall o, In o (R4 sz) -> obj_range rho' o = obj_range rhoE o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (X4 sz)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (A' := bumpK (with_depot A G2)).
  set (rho5 := rho_absorb rho' (R4 sz) (ms_with_mem ms2 (rm rhoE))).
  set (rho'' := mkVal (rw rho) (rl rho) (rm rho5)).
  assert (RM5 : forall a, rm rho5 a = if in_ranges_dec rho' (R4 sz) a then rm rhoE a else rm rhoL a).
  { intros a. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall a, in_ranges rho' (R4 sz) a <-> in_ranges rhoE (R4 sz) a).
  { intros a. split; intros (o & Ho & Hoa); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hoa). }
  assert (R4DFP : forall a, in_ranges rhoE (R4 sz) a -> ~ DFP G2 (bv_unsigned a)).
  { intros a Hin. exact (dc_R4 A rho rhoE sz SF A' rhoE tpL md2 a HX2 eq_refl Hin). }
  assert (KEY : forall a, ~ DFP G2 (bv_unsigned a) -> rm rho5 a = rm rhoE a).
  { intros a Ha. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) a) as [Hi|Hn]; [reflexivity|].
    rewrite (HRM2 a Ha). apply rm_absorb_out. intros Hi. exact (Hn (proj2 (IRE a) Hi)). }
  assert (KEYin : forall a, in_ranges rhoE (R4 sz) a -> rm rho5 a = rm rhoE a).
  { intros a Hi. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) a) as [|Hn]; [reflexivity|]. exfalso. exact (Hn (proj2 (IRE a) Hi)). }
  assert (BAND : forall Ax rx tpx mdx a, AInvX Ax rx tpx mdx -> SHADOW_BAND_LO <= a < SHADOW_BAND_HI -> ~ DFP (aa_depot Ax) a).
  { intros Ax rx tpx mdx a HX HB' HD. pose proof HX as (HGx & _ & _ & HRest & _ & HI3x & _). destruct HRest as (_ & _ & _ & HSx & _).
    assert (HSEC : forall i ch, nth_error (aa_sec Ax) i = Some ch -> dyn_in (topG (aa_geom Ax)) (sc_map_beg ch) (sc_map_size ch)).
    { intros i ch Hi. destruct HSx as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
    assert (HPAB : dyn_ok (topG (aa_geom Ax)) (ag_pab (aa_geom Ax)) kPtrArrayReserve) by (destruct HSx as (_ & _ & _ & _ & X4' & _); exact X4').
    pose proof (zones_not_DFPw Ax a HGx HI3x HSEC HPAB) as ZN. cbn zeta in ZN.
    destruct (DFP_split _ _ HD) as [Hs|Hws]; [pose proof (dstat_range a Hs) as DR; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HB'; unfold MAP1, MAP1N, STORE in DR; clear -HB' DR; lia | ].
    apply ZN; [do 8 right; left; exact HB' | exact Hws]. }

  assert (HX5 : AInvX A' rho5 tpL md2).
  { apply (AInvX_frameV A' rhoE rho5 tpL md2 HX2). intros z Hz. change (aa_depot A') with G2 in Hz.
    destruct (in_ranges_dec rhoE (R4 sz) (Z_to_bv 64 z)) as [Hi|Hn].
    - apply view_agree. intros _. apply KEYin. exact Hi.
    - transitivity (view segs (rm rhoL) z).
      + apply view_agree. intros Hr. rewrite RM5. destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 z)) as [Hi'|]; [exfalso; exact (Hn (proj1 (IRE _) Hi')) | reflexivity].
      + exact (eq_trans (HVW2 z Hz) (view_agree _ _ z (fun _ => rm_absorb_out _ _ _ _ Hn))). }
  assert (HDI5 : depot_inv segsA G2 rho5 md2 tpL).
  { apply (depot_inv_frame segsA G2 rhoL rho5 md2 tpL); [|exact HDI2]. intros a Ha. apply view_agree. intros Hr. rewrite RM5.
    destruct (in_ranges_dec rho' (R4 sz) (Z_to_bv 64 a)) as [Hi|]; [|reflexivity]. exfalso.
    apply (R4DFP (Z_to_bv 64 a) (proj1 (IRE _) Hi)). rewrite u64_lit by exact Hr. exact Ha. }
  assert (HA5 : AInvA segs A' rho5 tpL md2).
  { apply (X_AInvA A' rho5 tpL md2 HX5 HDI5). destruct (AInvA_X A rhoE tp md0 HA0) as (_ & _ & L60).
    destruct Hdpost2 as (EdN & _). unfold A'. cbn [aa_depot aa_Km aa_Kf bumpK with_depot]. lia. }
  assert (RW5 : forall i, (i < GW)%positive -> rw rho5 i = rw rhoE i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. exact (proj1 Hag' i (NXlt i Hi)). }
  assert (HJGb5 : JGb W st A' Kc rho'' rho5 tpL tr2 md2).
  { split.
    - split; [|split].
      + intros i Hi. unfold A'. refine (eq_trans (rhoM_of_AK A G2 rho rho'' (fun j => eq_refl _) i) _). rewrite (Hagw i Hi). symmetry. exact (RW5 i Hi).
      + intros l. unfold rhoM_of. rewrite rl_rho_sets. unfold rho'', rho5. cbn [rl rho_absorb]. rewrite <- (proj2 Hag' l), <- (Hagl l).
        unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
      + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
    - split; [exact HA5|]. split; [exact HK2|].
      split; [unfold tp_ok in Htp0 |- *; rewrite (RW5 24%positive) by (unfold GW; lia); exact Htp0|].
      split; [exact (HUSr rhoE rho5 RW5 HU0)|]. split; [exact I|].
      split; [cbn [eval]; rewrite (RW5 12%positive) by (unfold GW; lia); exact HN0|].
      unfold top_high. rewrite (RW5 10%positive), (RW5 V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop0. }

  assert (HT5 : SPA segs (JGb W st A' Kc rho'') (T4d sz) rho5 tpL (tr2, mkCfg ms2 md2)).
  { pose proof (proj1 (proj1 HT4d)) as HsmT. pose proof HsmT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HfT).
    unfold rho5. apply (SPA_absorb_any segs JP); [exact AX4d | | exact HT4d | exact HJGb5].
    intros o a Ho Ha. exact (coveredb_sound _ _ _ rho' o a HfT (R4cov sz Hsz) Ho Ha). }
  pose proof (SPA_entails segs (JGb W st A' Kc rho'') GW (T4d sz) (C5 W st tmax) _ rho5 tpL _ (ENT5 sz Hsz) (SID5 sz Hsz)
                (JGb_stable nW st A' Kc rho'' HUS HKc) HT5) as HC5.
  exists A', rho'', (rho_sub rho5 (sd sz)). split; [|split; [|exact HC5]].
  - unfold depot_onlyK, A'. cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_ptr_committed aa_live aa_q_thread aa_q_global aa_internal_inited aa_fs_busy aa_fs_hint aa_V aa_Km aa_Kf bumpK with_depot].
    repeat split; reflexivity.
  - split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros a Hk. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); unfold rhoM_of; rewrite rm_rho_sets; reflexivity|].
      exact (keep_not_DFP A' rhoE tpL md2 (bv_unsigned a) HX2 Hk).
    + intros a HBa Hdef. unfold rho''. cbn [rm]. rewrite KEY; [rewrite <- (Hagm a); unfold rhoM_of; rewrite rm_rho_sets; exact Hdef|].
      exact (BAND A' rhoE tpL md2 (bv_unsigned a) HX2 HBa).
Qed.

Lemma dc_exit : ltac2:(tb__ "0|2|
S8aOF_;S57S81S15S15S2dS68Q40A1A1M0S8bS8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS57S15S15G0Sc9R13R4A2ScaS93VCST;VXGL;R14A3R12R4A3S8dVsegs;R16S78Vsegs;Sc8VW;Vst;R6R14R5A5S6fVW;Vst;Vtmax;A3R4R3A5R10A4F_;F_;Ftp';FrhoX;Frho';FA';S41R10ReRdRaA4S82R10A1Sb6SaeSa4R12R11RfA3S59R12A1A3S9fS96S95R10VR4;RdA1S7dRaRfRbA3A3Vs4;RdA1A2S15S79Vsegs;R11R10S3fReA1S32G1S7fRdS80RcRbA2A4A5S8eVW;Vst;R15R14R13R12R11ReRcA9Sb2S1dS10S66R10A1A1A1R3RcA3S79Vsegs;RdRcS65R11A1S32G1S7fRbS80RaR9A2A4A5R6R5R14ReRdRcRaA6SbSa1R16S7dR10R15R11A3VR4;R13A1Vs4;R13A1S66R13A1S65R13A1S3fR13A1RfA8S15Sb3R17S7dR11R16R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R1R10A9S8dVsegs;R1cS78Vsegs;Sa0R9R8R17R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R2R10A5R16A4F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dc_exit_ok A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK n' Hg' w' Hw'.
  destruct (dc_exit_core A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
  exact (Hcont A' rho'' rhoX tpL Hdo Hl n' Hg' w' HC5).
Qed.

Lemma dc_exitE : ltac2:(tb__ "0|2|
S57S81S15S15S2dS68Q40A1A1M0S8aOF_;S8S2dS6dA1M1S7eS6cS15G0G1S7eS6cS57S15S15G0Sc9R13R4A2ScaS93VCST;VXGL;R14A3R12R4A3S8cVsegs;S78Vsegs;Sc8VW;Vst;R6R14R5A5S6fVW;Vst;Vtmax;A3R4R3A5R10A3F_;F_;Ftp';FrhoX;Frho';FA';S41R10ReRdRaA4S82R10A1Sb6SaeSa4R12R11RfA3S59R12A1A3S9fS96S95R10VR4;RdA1S7dRaRfRbA3A3Vs4;RdA1A2S15S79Vsegs;R11R10S3fReA1S32G1S7fRdS80RcRbA2A4A5S8eVW;Vst;R15R14R13R12R11ReRcA9Sb2S1dS10S66R10A1A1A1R3RcA3S79Vsegs;RdRcS65R11A1S32G1S7fRbS80RaR9A2A4A5R6R5R14ReRdRcRaA6SbSa1R16S7dR10R15R11A3VR4;R13A1Vs4;R13A1S66R13A1S65R13A1S3fR13A1RfA8S15Sb3R17S7dR11R16R12A3VR4;R14A1Vs4;R14A1S10S66R14A1A1S10S3fR14A1A1S10S65R14A1A1R1R10A9S8cVsegs;S78Vsegs;Sa0R9R8R17R11R10A5S9eVs4;R15A1S66R15A1S65R15A1S3fR15A1VR4;R15A1A5R2R10A5R16A3F_;Frho';A2F_;F_;F_;F_;F_;TrhoC;TJL;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd0;Fms0;Ftr0;Fsz;FQ;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc JL rhoC Hsm0 HJ0 HagL HsmL HJL.
  split; [exact (dc_exit_ok A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL)|].
  intros rho' HLK w' Hw'.
  destruct (dc_exit_core A Kc rho rhoE tp sz tr0 ms0 md0 rhoL tpL tr' ms' md' SF HKc Hsm0 HJ0 HagL HsmL HJL rho' w' HLK Hw') as (A' & rho'' & rhoX & Hdo & Hl & HC5).
  exact (Hcont A' rho'' rhoX tpL Hdo Hl w' HC5).
Qed.

Theorem depot_call_HD : ltac2:(tb__ "0|0|
S8aOF_;S57S81S15S8bS82R3A1S7cVsegs;R6S7aR4A1A3Sd7Vsegs;R7S7aR5A1A3ScbVnW;Vst;Vtmax;S93VCST;VXGL;R7A3R8R7R6R5R4A9F_;F_;F_;FQ;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho Q HKc Hokl Hokpl rhoE tp Hcont n HgQ w Hw. destruct w as [tr [ms md]].
  pose proof (dc_facts A Kc rho rhoE tp _ Hw) as SF. pose proof (dc_site A Kc rho rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & _). cbn [eval] in HN, HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & _).
  assert (Hn0 : 0 <= bv_unsigned (rw rhoE 12%positive)) by apply urange.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t tr0 md0, KD A Kc rhoE G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t tr0 md0 HKG). }
  apply (call_soundPA segs ok (JG W st A Kc rho) (JD segsA (KD A Kc rhoE) (aa_depot A)) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  -
    intros rho1 tp1 n1 Hg1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    refine (seg_D_sound2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE _ HKc HB Hn0 HKm0 NPRE ltac:(cbv; discriminate)) ok _ _ (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot A) (dN_entry A rhoE _ HB Hn0 tp md HA) (hcD_entry A rhoE _ HB Hn0 tp md HA) HT1 n1 Hg1 w1 Hw1).
    + intros G r t tr0 ms0 md0 msv' HKG HMI Hh Hp Hs. exact (Hokl r t tr0 ms0 md0 msv' (KD_Kc A Kc rhoE G r t tr0 md0 HKG) HMI Hh Hp Hs).
    + intros G r t tr0 ms0 md0 x8 HKG Hp Hok. exact (Hokpl r t tr0 ms0 md0 x8 (KD_Kc A Kc rhoE G r t tr0 md0 HKG) Hp Hok).
  -
    intros tr0 ms0 md0 Hsm0 HJ0. exact (dc_entry A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  -
    intros L JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    exact (dc_exit ok A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact HgQ.
  - exact Hw4.
Qed.

Theorem depot_call_HDE : ltac2:(tb__ "0|0|
S57S81S15S8aOF_;S82R3A1SdbVnW;Vst;Vtmax;S93VCST;VXGL;R5A3R5R4R3R2A8F_;FQ;Frho;FKc;FA;").
Proof.
  intros A Kc rho Q HKc rhoE tp Hcont w Hw. destruct w as [tr [ms md]].
  pose proof (dc_facts A Kc rho rhoE tp _ Hw) as SF. pose proof (dc_site A Kc rho rhoE tp _ Hw) as Hw4.
  pose proof SF as (Hsz & Fd1 & HG & E12 & _ & _ & _ & Htop & _).
  set (sz := bv_unsigned (rw rhoE 192%positive)) in *.
  pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  pose proof HJ as (HA & HK & Htp & HU & HB & HN & _). cbn [eval] in HN, HB.
  pose proof (AInvA_budget A rhoE tp md HA) as (_ & _ & _ & HKm0 & _).
  assert (Hn0 : 0 <= bv_unsigned (rw rhoE 12%positive)) by apply urange.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (HKT : forall G r t tr0 md0, KD A Kc rhoE G r t tr0 md0 -> alloc_top (m_vmmaps md0) = topG (aa_geom A)).
  { intros G r t tr0 md0 HKG. rewrite (geom_top _ HG). exact (KD_top A Kc rhoE G r t tr0 md0 HKG). }
  apply (call_completePA segs (JG W st A Kc rho) (JD segsA (KD A Kc rhoE) (aa_depot A)) (X4 sz) (PreD sz) (s4 sz) (R4 sz)
           [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))] Q rhoE tp (HER sz Hsz)).
  - change (map fst [(PostD sz, JLD segsA (KD A Kc rhoE) (aa_depot A))]) with [PostD sz]. exact (Hchk4 sz Hsz).
  - intros rho1 tp1 w1 Hw1. pose proof (proj1 (proj2 Hw1)) as (_ & _ & _ & HT1).
    exact (seg_D_complete2 (KD A Kc rhoE) (hcD A) (KD_laws A Kc rhoE _ HKc HB Hn0 HKm0 NPRE ltac:(cbv; discriminate)) (topG (aa_geom A)) TG HKT
              sz ltac:(lia) rho1 tp1 (aa_depot A) (dN_entry A rhoE _ HB Hn0 tp md HA) (hcD_entry A rhoE _ HB Hn0 tp md HA) HT1 w1 Hw1).
  - intros tr0 ms0 md0 Hsm0 HJ0. exact (dc_entry A Kc rho rhoE tp sz tr0 ms0 md0 SF HKc Hsm0 HJ0).
  - intros L JL tr0 ms0 md0 rhoL tpL tr' ms' md' HinL Hsm0 HJ0 HagL HsmL HJL.
    destruct HinL as [EL|[]].
    pose proof (f_equal fst EL) as EL1. pose proof (f_equal snd EL) as EL2. cbn [fst snd] in EL1, EL2. subst L JL. clear EL.
    exact (dc_exitE A Kc rho rhoE tp Q sz tr0 ms0 md0 rhoL tpL tr' ms' md' Hcont SF HKc Hsm0 HJ0 HagL HsmL HJL).
  - exact Hw4.
Qed.
End DCW.
End CDepotCallW.

(* [comment removed for export] *)
Module SegQS_k.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "modulo"; "mul"; "pow"; "sub"; "@Corelib.Init.Datatypes"; "list"; "fst"; "prod"; "snd"; "app"; "nat"; "option"; "cons"; "None"; "length"; "Some"; "bool"; "false"; "S"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "sec_chunk"; "aa_geom"; "ag_thread"; "qb_items"; "aa_sec"; "ag_pab"; "ag_spacebeg"; "qb_addr"; "aa_q_global"; "sc_map_beg"; "sc_map_size"; "topG"; "ageom"; "mkQB"; "sc_size"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "CURB"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qitems"; "it_ab"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "IMG_HI"; "PG"; "is_primary"; "kPtrArrayReserve"; "kQuarantineBatchCount"; "kSpaceSize"; "HIGH_SHADOW_END"; "IMG_LO"; "round_up"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "RMEM2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "QG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_zone"; "sec_junk_zone"; "sec_tbl_zone"; "chunk_sh_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k.QSK"; "ZQ"; "band"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "batch_mem"; "item_mem"; "qstat_zone"; "QW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "qsenv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma item_mem_frameZ : ltac2:(tb__ "0|4|
S33S33S10S0S0A2S5Z10S47S11S0S0R1A3A1A2S0S1S5S39R3A1R1A2S7R1SfS0S0R3A3A2A2S2S14S1cQ8A1M0A1M1R5R2A1R6R2A1A3F_;Fz;S0S1S5S3dSfS0S0R4A3A1M2R1A2S7R1S6G2S8S6S11S0S0R4A3Z7A2Z8A2A2A2A2S3S2G1R7R2A1S16G0A1M3A3A1S3S2G1R7R3A1G3A3A1F_;F_;Fz;S51R6R4A2S51R6R5A2F_;F_;F_;F_;Fit;Fm';Fm;").
Proof.
  intros m m' it Hrz HL HP (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold it_ab in HL.
  split; [rewrite HL by lia; exact H1|]. split; [eapply present_frame; [|exact H2]; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H3]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H4]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply present_frame; [|exact H5]; intros z Hz; apply HL; lia|].
  split.
  - unfold alloc_magic_ok in *. destruct H6 as [H6|[H6a H6b]]; [left; exact H6 | right].
    split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply HL; lia.
  - intros z Hz. destruct (H7 z Hz) as [b Hb]. pose proof (HP z Hz ltac:(rewrite Hb; discriminate)) as X.
    destruct (m' z) as [b'|]; [exists b'; reflexivity | exfalso; exact (X eq_refl)].
Qed.
Lemma batch_mem_frameZ : ltac2:(tb__ "0|8|
S33S33S1eS5S9S17S10S0S0A2M0S22R1A1A2A1S42A2S0S1S5S6S26R3A1M1Z8M2A2R1A2S7R1S6G1Z2000A2A2A2S2S14S1cQ8A1M3A1M4R5R2A1R6R2A1A3F_;Fz;G0S0S36G0R2S22R5A1A3S1S5S39R3A1R2A2S7R2SfS0S0R3A3M5A2A2S2G4R8R3A1R9R3A1A3F_;F_;Fz;Fit;G0S0S36G0R2S22R6A1A3S1S5S3dG5A1M6R2A2S7R2S6G6S8S6S11S0S0R3A3Z7A2G2A2A2A2A2S3S2G4RaR3A1S16G3A1M7A3A1S3S2G4RaR4A1G7A3A1F_;F_;F_;Fz;Fit;S50R7R5A2S50R7R6A2F_;F_;F_;F_;F_;Fb;Fm';Fm;").
Proof.
  intros m m' b HLn HB HI HP (H1 & H2 & H3 & H4 & H5). unfold kQuarantineBatchCount in HLn.
  split; [eapply cell_ok_frame1; [|exact H1]; cbn; intros z Hz; apply HB; lia|].
  split; [eapply cell_ok_frame1; [|exact H2]; cbn; intros z Hz; apply HB; lia|].
  split; [exact H3|]. split; [eapply present_frame; [|exact H4]; intros z Hz; apply HB; unfold kQuarantineBatchSize in Hz; lia|].
  intros i it Hi. destruct (H5 i it Hi) as [C I]. pose proof (nth_error_In _ _ Hi) as Hin.
  assert (Hi' : (i < length (qb_items b))%nat) by (apply (proj1 (nth_error_Some (qb_items b) i)); rewrite Hi; discriminate).
  split.
  - eapply cell_ok_frame1; [|exact C]. cbn. intros z Hz. apply HB. lia.
  - eapply item_mem_frameZ; [apply (proj1 (rz_facts (snd it))) | intros z Hz; exact (HI it z Hin Hz) | intros z Hz; exact (HP it z Hin Hz) | exact I].
Qed.

Lemma CR_frame : ltac2:(tb__ "0|e|
S33S33S2bS0S0S13SeS10S0S0A2M0A1SeS1eA1M1G1S0S1S5R7R1A2S7R1S6R7Z2000M2A2A2A2S2S14S1cQ8A1M3A1M4RaR2A1RbR2A1A3F_;Fz;S1eS36S1eR1S12S1eR4R3A3A3S1S5S9S17G0S22R2A1A2A1S42A2S0S1S5S26R3A1M5R1A2S7R1S6G5G2A2A2A2S2G4RdR2A1ReR2A1M6A3M7F_;Fz;A2F_;Fb;G0S36G0R1S12G0R6S38S12S1eR5R4A3A1A3A3S1S0S1S5S39R3A1R1A2S7R1SfS0S0R3A3M8A2A2S2G4G6RfR2A1M9A3MaF_;Fz;S0S1S5S3dG8A1MbR1A2S7R1S6GbS8S6S11S0S0R3A3Z7A2Z8A2A2A2A2S3S2G4G9S16G3A1McA3A1S3S2G4RfR3A1GcA3A1F_;F_;Fz;A2F_;Fit';S0S1S5S6S21RbA1MdZ50A2R1A2S7R1S6GdZ70A2A2A2G7F_;Fz;S0S1S5S6S49Za0A2R1A2S7R1S6S49Zc0A2A2A2GaF_;Fz;S35ReRbRaR9R8A5S48RfRdR8R7A4S1S35RfRdRcRbRaA5S48RfReR9R8A4A2F_;F_;F_;F_;F_;F_;F_;Frest;Ftmp';Fits0;Fnd;Fn0;Fa;FG;Fv';Fv;").
Proof.
  intros v v' G a n0 nd its0 tmp' rest EQa EQB EQI TOUT GOUT HCB HRM. split.
  - destruct HCB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold kQuarantineBatchCount in Q3.
    split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply EQa; lia|]. split; [exact Q2|]. split; [exact Q3|].
    split; [eapply present_frame; [|exact Q4]; intros z Hz; apply EQa; unfold kQuarantineBatchSize in Hz; lia|].
    intros j it' Hj. destruct (Q5 j it' Hj) as [Cj Ij]. pose proof (nth_error_In _ _ Hj) as Hin'.
    assert (Hj' : (j < length its0)%nat) by (apply (proj1 (nth_error_Some its0 j)); rewrite Hj; discriminate).
    split.
    + eapply cell_ok_frame1; [|exact Cj]. cbn. intros z Hz. apply EQa. lia.
    + destruct (EQI it' (in_or_app _ _ _ (or_introl Hin'))) as [E1 E2].
      eapply item_mem_frameZ; [apply (proj1 (rz_facts (snd it'))) | exact E1 | exact E2 | exact Ij].
  - destruct HRM as (HBM & HLT & HLR & HTHD & HGH). change Inv.QG with QG in *.
    split; [|split; [|split; [|split]]].
    + apply Forall_forall. intros b Hb. destruct (EQB b Hb) as [LB EB].
      apply (batch_mem_frameZ v v' b LB); [intros z Hz; apply EB; lia | | | exact (proj1 (Forall_forall _ _) HBM b Hb)].
      * intros it' z Hit' Hz. apply (proj1 (EQI it' ltac:(apply in_or_app; right; unfold qitems; apply in_flat_map; exists b; split; [exact Hb | exact Hit']))). exact Hz.
      * intros it' z Hit' Hz. apply (proj2 (EQI it' ltac:(apply in_or_app; right; unfold qitems; apply in_flat_map; exists b; split; [exact Hb | exact Hit']))). exact Hz.
    + apply qlinks_to_0. apply (qlinks_to_frame v v' tmp' 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply (proj2 (EQB b (in_or_app _ _ _ (or_introl Hb)))). lia.
    + apply qlinks_to_0. apply (qlinks_to_frame v v' rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply (proj2 (EQB b (in_or_app _ _ _ (or_intror Hb)))). lia.
    + destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    + destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia].
Qed.

Section QSK.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HKS : KQ_sec segsA K.
Hypothesis HSBD : KQ_secband K.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk).
Variables (a s : Z) (its : list (Z * Z)) (tmp' rest : list qbatch).
Hypothesis HTH : aa_q_thread A = [].
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis HGL : ltac2:(tb__ "0|0|
S2SeS1eA1S27VA;A1S15S1eS2cVa;S15S10S0S0A2Vit;Vits;A3Vs;A3S12S1eVtmp';Vrest;A3A3A3").
Hypothesis HPR : ltac2:(tb__ "0|0|
S2S19S40S11S0S0Vit;A3A1S1aA3").
Hypothesis HI : ltac2:(tb__ "0|0|
S2S14S1fA1S37S1fS23VA;A1Vi;A3S18S1fVch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S2S0SfS0S0Vit;A3S6S6S28Vch;A1S3fA2Z800A2A3").

Definition band (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S5S3cVz;A2S7Vz;S3bA2A2").

Definition ZQ (z : Z) : Prop := ltac2:(tb__ "0|0|
S4S4fVz;A1S4S4aVch;Vz;A2S4S4bVz;A1S4S4cVA;Vi;Vz;A3S52S20VA;A1Vz;A2A2A2A2A2").

Lemma chk_facts : ltac2:(tb__ "0|a|
S30SeS1cQ40A1A1SeS2fA1S2eS13S1fVK;VA;R6R5R4R3A5S2S14S1fA1M0S37S1fS23VA;A1M1R3A3S18S1fR2A2A3S28R3A1M2S0S29R4A1S0S1S2S0SaR2S3fA2Z0M3A3S1S2S0SaR1S3fA2G3A3S1S7Z11000R1A2S1S5S3eR2A2S1S5S6R2R1A2M4S2aS20VA;A1M5A1A2S1S4S5G4S3cA2S5S3bR2A2A2S1S4S5G4S25G5A1M6A2S5S6S6G6S43A2Z1000M7A2R2A2A2S1S4S5G4S21G5A1M8A2S5S6G8G7A2R2A2A2S1S4S5G4S24G5A1M9A2S5S6G9S41A2R2A2A2S13S1fS2G0S37S1fG1R2A3S18S1fR1A2A3S3S2S13R9R3A3A1S4S5S6R6R5A2G2A2S5S6G2S29R3A1A2R6A2A2F_;F_;Fch';Fj';A2A2A2A2A2A2A2A2A2Tmj;Thj;F_;F_;Fchj;Fj;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md j chj HK Hj hj mj.
  pose proof (ks_repr segsA K HKS A r tp tr md HK) as (SC1 & _).
  destruct (SC1 j chj Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _ & D12 & _).
  pose proof (ks_sep segsA K HKS A r tp tr md HK j chj Hj) as KS. cbv zeta in KS. destruct KS as (S1 & S2 & S3 & _ & S5).
  fold hj mj in D6, D7, D8, D10, D12, S1, S2, S3, S5.
  assert (M1 : 69632 < mj) by (unfold PG in D8; lia).
  split; [exact D6|]. split; [exact D7|]. split; [exact M1|].
  split; [apply (dyn_in_big _ _ _ D10); lia|]. split; [exact D12|].
  split; [destruct D10 as (_ & _ & _ & _ & X); exact X|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. exact S5.
Qed.

Lemma tbl_facts : ltac2:(tb__ "0|6|
S30SeS1cQ40A1A1SeS2fA1S2eVK;VA;R4R3R2R1A5S1S5SbZ8S9S17S1fS23VA;A1A2A1A2S41A2S1S5S3eS24S20VA;A1M0A1M1A2S1S4S5S6G1S41A2M2S3cA2S5S3bG1A2A2S1S4S5G2S25G0A1M3A2S5S6S6G3S43A2Z1000M4A2G1A2A2S4S5G2S21G0A1M5A2S5S6G5G4A2G1A2A2A2A2A2A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK. pose proof (ks_repr segsA K HKS A r tp tr md HK) as (_ & _ & (C1 & C2) & _ & DY & _).
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [_ _ _ _ _ _ _ _ _ _ HSEP3 _ _]. destruct HSEP3 as (_ & _ & _ & P4 & P5 & _).
  split; [lia|]. split; [apply (dyn_ok_big _ _ _ DY); unfold kPtrArrayReserve; lia|].
  split; [destruct DY as (_ & _ & _ & _ & _ & X); exact X|]. split; [exact P4 | exact P5].
Qed.

Lemma thr_facts : ltac2:(tb__ "0|4|
S30SeS1cQ40A1A1SeS2fA1S2eVK;VA;R4R3R2R1A5S21S20VA;A1M0A1S0S1S5Z1000M1R1A2S1S4S5S6R1G1A2M2S45A2S5S3eR1A2A2S1S4S5G2S3cA2S5S3bR1A2A2S1S5S44S25G0A1M3A2S5S6S6G3S43A2G1A2S2aG0A1A2A2A2A2A2TT;F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK T. destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ _ _ _].
  destruct HG as (_ & _ & (_ & D1 & _ & _ & D4 & D5) & _ & _ & _ & S2 & S3 & _). fold T in D1, D4, D5.
  split; [exact D1|]. split; [exact D4|]. split; [exact D5|]. split; [exact S2 | exact S3].
Qed.

Lemma batch_where : ltac2:(tb__ "0|1|
S30SeS1cQ40A1A1SeS2fA1S2eS1eVK;VA;R5R4R3R2A5S36S1eR2S27VA;A1A3S1S5S9S17S10S0S0A2S22R3A1A2A1S42A2S0S1S5S26R4A1M0R1A2S7R1S6G0Z2000A2A2A2S3S4eR2A1A1F_;Fz;A2F_;F_;Fb;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md b HK Hb.
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ HQPU _ HSEP _ _ _].
  pose proof (benv_of_K K HL A HCI r tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  assert (Hb' : In b (qall A)) by (unfold qall; rewrite HTH; exact Hb).
  destruct (batch_slot A HQPU HAU HG b Hb') as (y & E & Y0 & _ & Y1 & B5 & B6 & _ & BL & _).
  split; [exact BL|]. intros z Hz HZ.
  pose proof (tbl_facts r tp tr md HK) as (P1 & P2 & P3 & P4 & P5).
  pose proof (thr_facts r tp tr md HK) as (T1 & T2 & T3 & SB1 & SB2). cbv zeta in T1, T2, T3.
  assert (INSP : ag_spacebeg (aa_geom A) <= z < ag_spacebeg (aa_geom A) + kSpaceSize) by (unfold kSpaceSize; lia).
  destruct HZ as [HZ|[HZ|[HZ|[HZ|HZ]]]].
  - unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG in HZ. clear - HZ Hz B5. lia.
  - unfold chunk_zone in HZ. destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & _ & _ & _ & _ & C7 & _). cbv zeta in C7. clear - HZ INSP C7. lia.
  - unfold sec_junk_zone, SEC_INST in HZ. unfold HIGH_SHADOW_END in B5. clear - HZ Hz B5. lia.
  - unfold sec_tbl_zone, SEC_INST in HZ. destruct HZ as [HZ|[HZ|[HZ|(lst & Hl & HZ)]]].
    + unfold HIGH_SHADOW_END in B5. clear - HZ Hz B5. lia.
    + unfold HIGH_SHADOW_END in B5. clear - HZ Hz B5. lia.
    + pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi. unfold kPtrArrayReserve in *. clear - HZ INSP P1 P4 LTi. lia.
    + destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & M1 & _ & _ & _ & C7 & _). cbv zeta in M1, C7. clear - HZ INSP C7 M1. lia.
  - apply (HSEP z); [|unfold qstat_zone in HZ; clear - HZ; lia].
    unfold q_foot. rewrite HTH. cbn [app]. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. exact Hz.
Qed.

Lemma item_where : ltac2:(tb__ "0|4|
S30SeS1cQ40A1A1SeS2fA1S2eS10S0S0A2M0VK;VA;R5R4R3R2A5S36G0R2S38S3aVA;A1A1A3S1S0S1S5S39R4A1R1A2S7R1SfS0S0R4A3M1A2A2S1S3S4fR2A1M2A1S1S3S4bR2A1A1S1S3S4cVA;Vi;R2A3A1S1S3S52S20VA;A1R2A2A1S4aVch;R2A2S1S2S19S40S11S0S0R6A3A1S1aA3S2S0SfS0S0R6A3SfS0S0Vit;A3A3A2F_;A2A2A2A2F_;Fz;S0S1S5S3dG1A1M3R1A2S7R1S6G3S8S6S11S0S0R4A3Z7A2Z8A2A2A2A2G2F_;Fz;A2F_;F_;Fit';Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md it' HK Hin.
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ HQPU _ HSEP _ _ HKSECQ].
  pose proof (benv_of_K K HL A HCI r tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  pose proof (tbl_facts r tp tr md HK) as (P1 & P2 & P3 & P4 & P5).
  pose proof (thr_facts r tp tr md HK) as (T1 & T2 & T3 & SB1 & SB2). cbv zeta in T1, T2, T3.
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
  pose proof (rz_facts (snd it')) as (RZ1 & _).
  destruct (qitems_In A it' Hin) as (b & Hb & Hib).
  assert (NST : forall z, it_ab it' <= z < fst it' -> ~ qstat_zone (aa_geom A) z).
  { intros z Hz HZ. apply (HSEP z); [|unfold qstat_zone in HZ; clear - HZ; lia].
    unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. right. apply Exists_exists. exists it'. split; [exact Hib|]. left. unfold it_ab in Hz. exact Hz. }
  destruct (is_primary (snd it')) eqn:EP.
  -
    pose proof (item_slot A HQPU HAU HG it' Hin EP) as IS'. cbv zeta in IS'.
    destruct IS' as (C1 & I2 & _ & I4 & _ & I6 & _ & _ & _ & I10 & I11 & I12 & I13 & I14).
    pose proof kUserSpaceSize_val as KU.
    assert (INSP : forall z, it_ab it' <= z < fst it' -> ag_spacebeg (aa_geom A) <= z < ag_spacebeg (aa_geom A) + kSpaceSize) by (intros z Hz; unfold kSpaceSize in *; clear - Hz I2 I14 I10 I11 I12 C1; lia).
    split.
    + intros z Hz. specialize (INSP z Hz). split; [|split; [|split; [|split; [exact (NST z Hz)|]]]].
      * unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG. clear - Hz I13. lia.
      * unfold sec_junk_zone, SEC_INST. unfold HIGH_SHADOW_END in I13. clear - Hz I13. lia.
      * unfold sec_tbl_zone, SEC_INST. unfold HIGH_SHADOW_END in I13. intros [HZ|[HZ|[HZ|(lst & Hl & HZ)]]]; [clear - HZ Hz I13; lia | clear - HZ Hz I13; lia | |].
        -- unfold kPtrArrayReserve in *. clear - HZ INSP P1 P4 LTi. lia.
        -- destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & M1 & _ & _ & _ & C7 & _). cbv zeta in M1, C7. clear - HZ INSP C7 M1. lia.
      * intros HZ. exfalso. unfold chunk_zone in HZ. destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & _ & _ & _ & _ & C7 & _). cbv zeta in C7. clear - HZ INSP C7. lia.
    + intros z Hz. unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
      pose proof (topG_range (aa_geom A)) as TG. unfold kSpaceSize, HIGH_SHADOW_END in *.
      assert (U1 : 0 <= fst it' / 8) by (apply Z.div_pos; clear - I10 I2 SB1 RZ1 C1; lia).
      assert (U2 : (snd it' + 7) / 8 <= snd it') by (apply Z.div_le_upper_bound; clear - I12; lia).
      assert (U3 : fst it' / 8 + snd it' <= 2 ^ 44) by (pose proof (Z.div_le_upper_bound (fst it') 8 (2 ^ 44 - 65536) ltac:(lia)) as X; clear - X I11 I6 I14 SB2 TG I12 I10; lia).
      clear - Hz U1 U2 U3. lia.
  -
    destruct (ks_item segsA K HKS A r tp tr md HK it' Hin EP) as (j & chj & Hj & EU' & _).
    destruct (chk_facts r tp tr md j chj HK Hj) as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10). cbv zeta in J1, J2, J3, J4, J5, J6, J7, J8, J9, J10.
    pose proof (rz_facts (snd it')) as (_ & RZ2). pose proof (rz_facts (snd it')) as ((_ & RZ3) & _).
    assert (INCH : forall z, it_ab it' <= z < fst it' -> sc_map_beg chj + PG <= z < sc_map_beg chj + PG + 2048) by (intros z Hz; unfold it_ab in Hz; clear - Hz EU' RZ3 RZ1; lia).
    split.
    + intros z Hz. specialize (INCH z Hz). unfold PG in INCH. split; [|split; [|split; [|split; [exact (NST z Hz)|]]]].
      * unfold band. clear - INCH J3 J6. lia.
      * unfold sec_junk_zone, SEC_INST. unfold IMG_HI in J4. clear - INCH J4. lia.
      * unfold sec_tbl_zone, SEC_INST. unfold IMG_HI in J4. intros [HZ|[HZ|[HZ|(lst & Hl & HZ)]]]; [clear - HZ INCH J4; lia | clear - HZ INCH J4; lia | |].
        -- unfold kPtrArrayReserve in *. clear - HZ INCH P1 J9 J3 LTi. lia.
        -- destruct (Nat.eq_dec j (length (aa_sec A) - 1)) as [EJ|NJ].
           ++ subst j. rewrite Hl in Hj. injection Hj as <-. clear - HZ INCH. lia.
           ++ pose proof (J10 _ lst Hl NJ) as X. destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & M1 & _). cbv zeta in M1. clear - HZ INCH X J3 M1. lia.
      * intros HZ. unfold chunk_zone in HZ. split; [reflexivity|]. destruct (Nat.eq_dec j i) as [EJ|NJ].
        -- subst j. rewrite HI in Hj. injection Hj as <-. rewrite HU. exact EU'.
        -- exfalso. pose proof (J10 _ ch HI NJ) as X. clear - HZ INCH X J3. lia.
    + intros z Hz. destruct (HKSECQ it' Hin EP) as [_ X]. unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *. unfold PG, IMG_HI in *.
      assert (U1 : 0 <= fst it' / 8) by (apply Z.div_pos; clear - EU' J4; lia).
      destruct (batch_slot A HQPU HAU HG b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it' Hib) as (_ & N1 & _).
      pose proof (Z.div_mod (fst it') 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (fst it') 8 ltac:(lia)) as D2.
      pose proof (Z.div_mod (snd it' + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (snd it' + 7) 8 ltac:(lia)) as D4.
      clear - Hz D1 D2 D3 D4 X N1 EU' J4. lia.
Qed.

Lemma hdr_where : ltac2:(tb__ "0|2|
S30SeS1cQ40A1A1SeS2fA1S2eVK;VA;R4R3R2R1A5S1S0S1S5S6S21S20VA;A1A1M0Z50A2R1A2S7R1S6G0Z70A2A2A2S3S4eR2A1A1M1F_;Fz;S0S1S5S6S49Za0A2R1A2S7R1S6S49Zc0A2A2A2G1F_;Fz;A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK.
  pose proof (tbl_facts r tp tr md HK) as (P1 & P2 & P3 & P4 & P5).
  pose proof (thr_facts r tp tr md HK) as (T1 & T2 & T3 & SB1 & SB2). cbv zeta in T1, T2, T3.
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
  destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & C3 & C4 & _ & _ & _ & C8 & _). cbv zeta in C3, C4, C8.
  split; intros z Hz HZ; destruct HZ as [HZ|[HZ|[HZ|[HZ|HZ]]]].
  - unfold band in HZ. clear - HZ Hz T3. lia.
  - unfold chunk_zone in HZ. clear - HZ Hz C8 C3. lia.
  - unfold sec_junk_zone, SEC_INST in HZ. unfold IMG_LO, IMG_HI in T2. clear - HZ Hz T2. lia.
  - unfold sec_tbl_zone, SEC_INST in HZ. unfold IMG_LO, IMG_HI in T2. destruct HZ as [HZ|[HZ|[HZ|(lst & Hl & HZ)]]]; [clear - HZ Hz T2; lia | clear - HZ Hz T2; lia | |].
    + unfold kPtrArrayReserve in *. clear - HZ Hz P1 P5 LTi. lia.
    + destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & M1 & _ & _ & _ & _ & M8 & _). cbv zeta in M1, M8. clear - HZ Hz M1 M8. lia.
  - unfold qstat_zone in HZ. clear - HZ Hz. lia.
  - unfold band, SHADOW_BAND_LO, LOW_SHADOW_BEG, QG in *. clear - HZ Hz. lia.
  - unfold chunk_zone, IMG_HI, QG in *. clear - HZ Hz C4. lia.
  - unfold sec_junk_zone, SEC_INST, QG in *. clear - HZ Hz. lia.
  - unfold sec_tbl_zone, SEC_INST, QG in *. unfold IMG_HI in P2. destruct HZ as [HZ|[HZ|[HZ|(lst & Hl & HZ)]]]; [clear - HZ Hz; lia | clear - HZ Hz; lia | clear - HZ Hz P2; lia |].
    destruct (chk_facts r tp tr md _ lst HK Hl) as (_ & _ & _ & M4 & _). cbv zeta in M4. unfold IMG_HI in M4. clear - HZ Hz M4. lia.
  - unfold qstat_zone, QG, IMG_LO, IMG_HI in *. clear - HZ Hz T2. lia.
Qed.

Lemma qitems_split : ltac2:(tb__ "0|1|
S2SeS10S0S0A2M0A1S38S3aVA;A1A1S12G0S15G0Vit;Vits;A3S38S12S1eVtmp';Vrest;A3A1A3A3").
Proof. unfold qall. rewrite HTH, HGL. unfold qitems. cbn [app flat_map qb_items]. reflexivity. Qed.

Lemma other_item_off_chunk : ltac2:(tb__ "0|1|
S30SeS1cQ40A1A1SeS2fA1S2eS10S0S0A2M0VK;VA;R5R4R3R2A5S36G0R2S12G0Vits;S38S12S1eVtmp';Vrest;A3A1A3A3S2S19S40S11S0S0R3A3A1S1aA3S3S2S0SfS0S0R4A3SfS0S0Vit;A3A3A1F_;F_;F_;Fit';Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md it' HK Hin EP E.
  pose proof (ks_nodup segsA K HKS A r tp tr md HK) as ND. rewrite qitems_split in ND. cbn [app List.filter] in ND. rewrite HPR in ND. cbn [negb map] in ND.
  inversion ND as [|x l NI _]; subst. apply NI. apply list_elem_of_In. rewrite <- E. apply in_map. apply filter_In. split; [exact Hin | rewrite EP; reflexivity].
Qed.

Lemma CR_band : ltac2:(tb__ "0|6|
S30SeS1cQ40A1A1SeS2fA1S2eS33S33S0S13VK;VA;R8R7R6R5A5S0S3S4fR1A1A1S2S14S1cQ8A1M0A1M1R6R2A1R7R2A1M2A3F_;Fz;S0S3S2G1R7R1A1S16G0A1M3A3A1S3S2G1G2G3A3A1F_;Fz;S35R7Va;R5R4S15S10S0S0A2Vit;Vits;A3M4A5S48R8S20VA;A1Vtmp';Vrest;A4M5S1S35R8Va;R7R6G4A5G5A2F_;F_;F_;F_;F_;Fnd;Fn0;Fv';Fv;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md v v' n0 nd HK HEQ HPRS HCB HRM.
  destruct (hdr_where r tp tr md HK) as [HT HQ].
  assert (INB : forall b, In b (tmp' ++ rest) -> In b (aa_q_global A)) by (intros b Hb; rewrite HGL; right; exact Hb).
  apply (CR_frame v v' (aa_geom A) a n0 nd (it :: its) tmp' rest); try assumption.
  - intros z Hz. apply HEQ. intros HB. apply (proj2 (batch_where r tp tr md (mkQB a (it :: its) s) HK ltac:(rewrite HGL; left; reflexivity)) z Hz). left. exact HB.
  - intros b Hb. destruct (batch_where r tp tr md b HK (INB b Hb)) as [LB EB]. split; [exact LB|]. intros z Hz. apply HEQ. intros HB. apply (EB z Hz). left. exact HB.
  - intros it' Hin'. assert (Hq : In it' (qitems (qall A))) by (rewrite qitems_split; exact Hin').
    destruct (item_where r tp tr md it' HK Hq) as [W1 _]. split; [|intros z _ Hd; exact (HPRS z Hd)].
    intros z Hz. apply HEQ. exact (proj1 (W1 z Hz)).
  - intros z Hz. apply HEQ. intros HB. apply (HT z Hz). left. exact HB.
  - intros z Hz. apply HEQ. intros HB. apply (HQ z Hz). left. exact HB.
Qed.

Lemma CR_unmap : ltac2:(tb__ "0|4|
S30SeS1cQ40A1A1SeS2fA1S2eS33S33S0S13VK;VA;R8R7R6R5A5S0S3S4eR1A1A1S2S14S1cQ8A1M0A1M1R6R2A1R7R2A1A3F_;Fz;S0S3S4aVch;R1A2A1S3S2G1R8R2A1S16G0A1M2A3A1S3S2G1R8R3A1G2A3A1F_;F_;Fz;S35R7Va;R5R4S15S10S0S0A2Vit;Vits;A3A5S48R8S20VA;A1Vtmp';Vrest;A4M3S1S35R8Va;R7S1bR6A1Vits;A5G3A2F_;F_;F_;F_;F_;Fnd;Fn0;Fv';Fv;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md v v' n0 nd HK HEQ HPRS HCB HRM.
  destruct (hdr_where r tp tr md HK) as [HT HQ].
  assert (INB : forall b, In b (tmp' ++ rest) -> In b (aa_q_global A)) by (intros b Hb; rewrite HGL; right; exact Hb).
  destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & C3 & _ & _ & C6 & _). cbv zeta in C3, C6.
  apply (CR_frame v v' (aa_geom A) a n0 (S nd) its tmp' rest); try assumption.
  - intros z Hz. apply HEQ. exact (proj2 (batch_where r tp tr md (mkQB a (it :: its) s) HK ltac:(rewrite HGL; left; reflexivity)) z Hz).
  - intros b Hb. destruct (batch_where r tp tr md b HK (INB b Hb)) as [LB EB]. split; [exact LB|]. intros z Hz. apply HEQ. exact (EB z Hz).
  - intros it' Hin'. assert (Hq : In it' (qitems (qall A))) by (rewrite qitems_split; right; exact Hin').
    destruct (item_where r tp tr md it' HK Hq) as [W1 W2]. split.
    + intros z Hz. apply HEQ. destruct (W1 z Hz) as (N1 & N2 & N3 & N4 & N5). intros [HZ|[HZ|[HZ|[HZ|HZ]]]]; [exact (N1 HZ) | | exact (N2 HZ) | exact (N3 HZ) | exact (N4 HZ)].
      destruct (N5 HZ) as [EP E]. exact (other_item_off_chunk r tp tr md it' HK Hin' EP E).
    + intros z Hz. apply HPRS. pose proof (W2 z Hz) as HB. unfold band in HB. unfold chunk_zone. clear - HB C6 C3. lia.
  - intros z Hz. apply HEQ. exact (HT z Hz).
  - intros z Hz. apply HEQ. exact (HQ z Hz).
  - exact (CURB_next _ _ _ _ _ _ HCB).
Qed.

Lemma qw_off_chunk : ltac2:(tb__ "0|0|
S30SeS1cQ40A1A1SeS2fA1S2eVK;VA;R4R3R2R1A5S0S4S53VA;R1A2S4S4bR1A1S4dVch;R1A2A2A2S3S4aVch;R2A2A1F_;Fz;F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK z HZ HC.
  destruct (chk_facts r tp tr md i ch HK HI) as (_ & _ & C3 & C4 & C5 & C6 & _ & C8 & _). cbv zeta in C3, C4, C5, C6, C8.
  destruct (hdr_where r tp tr md HK) as [HT HQ]. pose proof (topG_range (aa_geom A)) as TG.
  assert (NB : ~ band z) by (unfold band; unfold chunk_zone in HC; lia).
  destruct HZ as [HZ|[HZ|HZ]].
  - destruct HZ as [HZ|[HZ|HZ]].
    + unfold qzone in HZ. apply Exists_exists in HZ as (b & Hb & HZ). destruct HZ as [HZ|HZ].
      * assert (Hb' : In b (aa_q_global A)) by (unfold qall in Hb; rewrite HTH in Hb; exact Hb).
        apply (proj2 (batch_where r tp tr md b HK Hb') z); [unfold kQuarantineBatchSize in HZ; exact HZ | right; left; exact HC].
      * apply Exists_exists in HZ as (it' & Hit' & EP & HZ).
        assert (Hq : In it' (qitems (qall A))) by (unfold qitems; apply in_flat_map; exists b; split; [exact Hb | exact Hit']).
        destruct (item_where r tp tr md it' HK Hq) as [W1 W2]. destruct HZ as [HZ|HZ].
        -- destruct (W1 z HZ) as (_ & _ & _ & _ & W5). destruct (W5 HC) as [EP' _]. rewrite EP in EP'. discriminate.
        -- exact (NB (W2 z HZ)).
    + unfold qhdr_zone in HZ. destruct HZ as [HZ|[HZ|HZ]].
      * apply (HT z HZ). right. left. exact HC.
      * unfold chunk_zone, IMG_HI, Inv.QG in *. lia.
      * apply (HQ z HZ). right. left. exact HC.
    + unfold qstat_zone, chunk_zone in *. lia.
  - unfold sec_junk_zone, SEC_INST, chunk_zone, IMG_HI in *. lia.
  - apply NB. unfold chunk_sh_zone in HZ. unfold IMG_HI in C4.
    pose proof (Sh_in_band (sc_map_beg ch) ltac:(lia)) as B1. pose proof (Z.div_le_upper_bound (sc_map_beg ch + sc_map_size ch) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as B2.
    unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *. lia.
Qed.

Hypothesis HSZ : ltac2:(tb__ "0|0|
S2S0S2dVch;A1S6S46S11S0S0Vit;A3Z8A2Z1000A2A3").
Lemma qsenv_intro : ltac2:(tb__ "0|4|
S30SeS1cQ40M0A1M1A1SeS2fA1S2eS0S13VK;VA;R6R5R4R3A5S35S34S54S32R7A1A2Va;R3R2S15S10S0S0A2Vit;Vits;A3A5S1S2G1S31R8Pa5A2S1dG0SdSfS0S0Vit;A3Z10A2A2A3S1S2G1S31R8Pc8A2S1dG0S24S20VA;A1A1A2A3S1S2G1S31R8Pc9A2S1dG0S9S17S1fS23VA;A1A2A1A2A3S1S2G1S31R8PcfA2S1dG0S8S11S0S0Vit;A3M2ScZ2Z20A2M3A2A2A3S2G1S31R8Pd1A2S1dG0SaG2G3A2A2A3A2A2A2A2S55VA;Vit;Vi;Vch;R9A5F_;F_;F_;Fnd;Fn0;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md n0 nd HK HCB HV.
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG HRIG HRTC _ HST _ _ HQPU _ _ HSEP3 _ _].
  pose proof (benv_of_K K HL A HCI r tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  assert (Hb : In (mkQB a (it :: its) s) (qall A)) by (unfold qall; rewrite HTH, HGL; left; reflexivity).
  destruct (batch_slot A HQPU HAU HG _ Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HIP). cbn [qb_items] in HIP.
  pose proof (Forall_inv HIP) as (_ & N1 & _).
  destruct HCB as (_ & _ & _ & _ & Q5). destruct (Q5 0%nat it eq_refl) as [_ HIM].
  constructor; try assumption.
  - exact (ks_repr segsA K HKS A r tp tr md HK).
  - pose proof (ks_sep segsA K HKS A r tp tr md HK i ch HI) as KS. cbv zeta in KS. exact KS.
Qed.
End QSK.
End SegQS_k.

(* [comment removed for export] *)
Module SpineMallocR6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "eval"; "rw"; "rm"; "SAlu"; "SLit"; "SPBranch"; "SPNot"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "lt"; "add"; "mul"; "to_nat"; "pow"; "sub"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "false"; "true"; "nil"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "w_cfg"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "entryR"; "ph0"; "FAb"; "frozen"; "ghosts"; "ph_fill"; "gh_nf"; "phase"; "gh_new"; "ph_cnt"; "ph_pop"; "ph_ri"; "rlink"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cs_cache"; "class_state"; "cs_free_array"; "aa_cache_inited"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refill_cs"; "kchunks"; "refillA"; "take_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "ulink"; "mem_keptA"; "ustop"; "UStopLeOrPc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "cnt_of"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Corelib.Lists.ListDef"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "cR0"; "vAU"; "vK"; "vMFA"; "vMU"; "vNF"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR4"; "ph_setcnt"; "ph_setri"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SUB"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1"; "r0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR6.ARMN"; "e16N"; "e_srcN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR6.ASMN"; "exitT"; "phFN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR6"; "e16N"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Lemma entry_fa : ltac2:(tb__ "0|3|
S34S1S16S32Q40M0A1A1S2fS16S42A1S44S1S22R7R6R5R4R3R2R1A7S33G0S3R7PcA2A2S0S46R1A1S0S47RaR2A2S36S55SdS4RaA1A2S52ScS0ScSeZ0M1R1A2S10R1SfS17S0S37R3A1M2A2A1A2A2S53R3S54S11S24ReRdA2S12Z4R2A2A2U4S50S0S13R2A1S37R4A1G1A4A3A2F_;Fidx;S0S49S0R1G2A3ScSeG1R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;A2Tm0;Tcs;Tc;Tnv;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE nv c cs m0.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & S1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _).
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MS : forall z, ag_spacebeg (aa_geom A) <= z < ag_spacebeg (aa_geom A) + kSpaceSize + 4096 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C9 & _ & N7 & _).
  split.
  - intros idx Hidx j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    assert (NE : nth_error (cs_free_array cs) (Z.to_nat idx) = Some (nth (Z.to_nat idx) (cs_free_array cs) 0)) by (apply nth_error_nth'; lia).
    pose proof (C9 _ _ NE j Hj) as Hc. cbn [c_addr c_w RtCells.c_val] in Hc. rewrite Z2Nat.id in Hc by lia.
    unfold FAb. fold nv c. rewrite MS in Hc; [exact Hc|]. rewrite kSpaceSize_val. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. clear -Hidx Hj MF0 C1. lia.
  - intros x Hx. destruct (N7 x ltac:(apply in_or_app; left; exact Hx)) as (X1 & _ & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by lia. lia.
Qed.

Section ARMN.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model) (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S22VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let k : Z := kchunks c.
Let fa : list Z := cs_free_array cs.

Hypothesis HNP : ltac2:(tb__ "0|0|
SeVk;SfS17S0Vfa;A2A1A2").

Lemma N_refill_cs : ltac2:(tb__ "0|0|
SbS36S3cVc;Vcs;A2S3fS13Vk;A1Vcs;A2A3").
Proof. unfold refill_cs, needs_populate. fold k fa. replace (Z.of_nat (length fa) <? k) with false by (symmetry; apply Z.ltb_ge; exact HNP). reflexivity. Qed.

Lemma N_HCACHE : ltac2:(tb__ "0|0|
SbS16S0A1S35S3cVc;Vcs;A2A1S51S0S13S15SfS17S0Vfa;A2A1Vk;A2A1Vfa;A3A3").
Proof.
  rewrite N_refill_cs. unfold take_cs. cbn [cs_cache]. fold fa. f_equal.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & (K1 & _) & _). fold k in K1. lia.
Qed.

Lemma N_HLEN : ltac2:(tb__ "0|0|
SbS0SfS17S0S35S3cVc;Vcs;A2A1A2A1Vk;A3").
Proof.
  rewrite N_HCACHE, length_skipn.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & (K1 & _) & _). fold k in K1. lia.
Qed.

Lemma N_HIDS : ltac2:(tb__ "0|0|
S0S49S0R1Vfa;A3ScSeZ0R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;").
Proof. exact (proj2 (entry_fa _ _ _ _ _ _ _ HE)). Qed.

Lemma N_HIDC : ltac2:(tb__ "0|0|
S0S49S0R1S35S3cVc;Vcs;A2A1A3ScSeZ0R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;").
Proof. intros x Hx. rewrite N_HCACHE in Hx. apply N_HIDS. rewrite <- (firstn_skipn (Z.to_nat (Z.of_nat (length fa) - k)) fa). apply in_or_app. right. exact Hx. Qed.

Definition e_srcN : sv := ltac2:(tb__ "0|0|
S5S61S5cS5S62S5S63S5bS58A3S6Z2A1A3A3").
Definition e16N : sv := SAlu ALU_SUB vNF vK.

Lemma N_HSRCP : ltac2:(tb__ "0|1|
S1S25Vrb;R1A2S26VA;Vrb;R2A3SbS32Q40M0A1S2R3S69A2S31G0S11S24VA;Vrb;A2S12Z4S15SfS17S0Vfa;A2A1Vk;A2A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. destruct HGh as (_ & Q221 & _ & _ & _ & _ & Q226 & Q227 & _). unfold gh_nf in Q221. fold nv c cs fa in Q221. fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _). fold k in K1. fold fa in MF0.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384) by (unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; fold nv c; lia).
  unfold e_srcN, vFA, vNF, vK. cbn [eval]. rewrite Q221, Q226, Q227. apply bv_eq.
  rewrite add_val, sll_val, sub_val. rewrite (u64_lit (Z.of_nat (length fa))), (u64_lit k), (u64_lit (FAb A rb)) by lia.
  change (2 mod 64) with 2. rewrite (Z.mod_small (Z.of_nat (length fa) - k)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma N_HRIv : ltac2:(tb__ "0|2|
S1S25Vrb;R1A2S26VA;Vrb;R2A3S3cVc;Vcs;A2S36ScSbS32Q40M0A1M1S2R4S68A2S31G0SfS17S0S37R1A1A2A1A2A3ScSbG1S2R4S59A2S31G0S3aR1A1A2A3ScSbG1S2R4S57A2S31G0S39R1A1A2A3SbG1S2R4S5aA2S31G0S3bR1A1A2A3A2A2A2TcsR;F_;F_;Fr;").
Proof.
  intros r HFz HGh csR. unfold csR. rewrite N_refill_cs. unfold take_cs. cbn [cs_free_array cs_mapped_free_array cs_allocated_user cs_mapped_user]. fold fa.
  destruct HGh as (_ & Q221 & Q222 & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs fa in Q221. fold nv c cs in Q222, Q223, Q224. fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _). fold k in K1. fold fa in MF0.
  split; [|split; [exact Q222 | split; [exact Q223 | exact Q224]]].
  unfold e16N, vNF, vK. cbn [eval]. rewrite Q221, Q227. apply bv_eq. rewrite sub_val. rewrite (u64_lit (Z.of_nat (length fa))), (u64_lit k) by lia.
  rewrite firstn_length_le by lia. rewrite Z.mod_small by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma N_HSRC : ltac2:(tb__ "0|1|
S0S52ScSeZ0M0R2A2SeR2Vk;A2A2S2eVA;Vrb;S4eS23R3A2S55SdS4Vrb;A1A2R2A5S0ScSeG0R1A2S10R1SfS17S0Vfa;A2A1A2A2S53R5S54S11S24VA;Vrb;A2S12Z4R2A2A2U4S50S0S13R2A1Vfa;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Proof.
  intros i m Hi (L1 & _) idx Hidx.
  eapply cell_ok_agree_range; [|exact (proj1 (entry_fa _ _ _ _ _ _ _ HE) idx Hidx)]. cbn [c_addr c_w]. intros z Hz. apply L1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & PS1) & _). fold k in K1. fold fa in MF0.
  change (Z.of_nat 4) with 4 in Hz. unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
  unfold zoneR, phK, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb]. unfold PCE. fold nv c.
  intros [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; lia.
Qed.
End ARMN.

Section ASMN.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S34S40S16S1cS66S4dA2A1F_;F_;").
Variables (W : list ulink) (st : ustop).
Variables (E3 E3P LP LJ XL LZ : axst).
Notation AInvS := (AInvA segs).
Hypothesis HWs : ltac2:(tb__ "0|0|
SbS44Vst;S45A3SbS16S42A1VW;S1bS42A1A3F_;").
Hypothesis FJ : ltac2:(tb__ "0|0|
S49S9S8S7S64S5bS58A3A1SaS65VLJ;A1A1A3").

Definition prefixT : Prop := ltac2:(tb__ "0|2|
S34S40S1S16S32Q40A1A1M0S2fS1dS1dOF_;F_;S4aR5R1A2S41R6A1S1S1G0S1dS22RcRaR9R8VW;Vst;R4A7S1R9S20SdS21ReRdRcRbRaS23A6VLP;R1R4A5R3A2Fr';S1RaS20SdS21RfReRdRcRbS23A6M1VLJ;R1R5A5R4A2Fr';RaS20SdG1S56VE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition popT (e_src : sv) : Prop := ltac2:(tb__ "0|9|
S34S40S1S16S32Q40M0A1M1A1M2S2fS1dS1dOF_;F_;S4aR5R1A2S41R6A1S1S22R9R7R6R5VW;Vst;R1A7S29ScSbS0S2cR1A1Z0M3A3ScSbS18S2bR1A1S19A3SbS18S2dR1A1S19A3A2A2S16S0A1M4S33G0S3RbPcA2A2S0S46R1A1S0S3dR1A1S0SfS17S0R4A2A1S0S0S52ScSeG3R2A2M5SeR2R4A2A2S2eR14R12S4eRaR3A2S55SdS4R12A1A2R2A5S0ScSeG3R1A2S10R1R6A2A2S53R5S54S11S24R17R15A2S12Z4M6R2A2A2U4S50S0S13R2A1RbG3A4A3A2F_;Fidx;F_;F_;Fm;Fi;SeR3R2A2SeS12G6R3A2Z20000000A2S10G3S27RaA1A2ScSeG3S28R15R13A2M7A2ScSbS0S11G7S2aR15R13A2M8A2R5A3SeS27RbA1G8A2A2A2F_;S0S49S0R1RaA3ScG5S10R2S14Z2Z1cA2A2A2F_;Fx;SbG4S35S3cR8S47R16R9A2A2A1S51S0S13S15R6R7A2A1RaA3A3S1S25R16R1A2S26R19R17R2A3SbG1S2R3Ve_src;A2S31G0S11S24R1aR18A2S12G6S15RaRbA2A2A2A2A3F_;F_;Fr;S1G2S1dS1R17S20SdS21R1cR1bR1aR19R18S4eR12RdA2A6VXL;R1R3A5R2A2Fr';R17S20SdS21R1cR1bR1aR19R18R12A6VLJ;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;F_;TnfP;Tk;Tc;Tnv;FfaP;FPH0;Fph;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition entryT : Prop := ltac2:(tb__ "0|2|
S34S40S1S1S16S32Q40M0A1A1S1fSbS18S38R6A1S1aA3SbS0S48R7S33G0S3R5PcA2A2A2Z0A3S20SdS4fVW;Vst;R8R7R6A5VE3;R5R4R3A6ScS22R9R6R5S60S1eR4A1A1M1VW;Vst;R7A7S20SdS21R9R8R6R5G1S23A6S56VE3;A1S67R9R6A2R5R4A6A2F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Definition exitT (e16 e24 e32 e48 : sv) : Prop := ltac2:(tb__ "0|7|
S34S40S1S16S32Q40M0A1M1A1M2S2fS1dS1dOF_;F_;S4aR5R1A2S41R6A1S1S22R9R7R6R5VW;Vst;R1A7S29S33G0S3R9PcA2A2S0S46R1A1S0S3dR1A1S0ScSbS0S2cR4A1R1A3ScSbS18S2bR4A1S19A3SbS18S2dR4A1S19A3A2A2S10Z0M3S27R5A1A2ScSeG3S28R10ReA2M4A2ScSeS12Z4S11G4S2aR10ReA2M5A2A2Z20000000A2SeS27R6A1G5A2A2A2F_;SbS18S38R10A1S1aA3S1S25R10R1A2S26R13R11R2A3S3cR8S47R14R9A2A2M6S36ScSbG1S2R4Ve16;A2S31G0SfS17S0S37R1A1A2A1A2A3ScSbG1S2R4Ve24;A2S31G0S3aR1A1A2A3ScSbG1S2R4Ve32;A2S31G0S39R1A1A2A3SbG1S2R4Ve48;A2S31G0S3bR1A1A2A3A2A2A2TcsR;F_;F_;Fr;SbS0SfS17S0S35S3cR6S47R12R7A2A2A1A2A1R5A3S0S49S0R1S35G6A1A3ScSeG3R2A2S10R2S14Z2Z1cA2A2A2F_;Fx;S1G2S1dS1R13S20SdS21R18R17R16R15R14S5fS5eReA1A1A6VLZ;R1R3A5R2A2Fr';R13S20SdS21R18R17R16R15R14ReA6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;Tk;Tc;Tnv;FphX;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition backT : Prop := ltac2:(tb__ "0|4|
S34S40S1S16S32Q40M0A1A1M1S2fS1dS1dOF_;F_;S4aR5R1A2S1S22R8R6R5R4VW;Vst;R1A7S29S33G0S3R8PcA2A2S0S46R1A1S0S1G1S16S30A1M2S2fS21R10RfReRdRcR7R4R3R2R1AaS5dSdS3eR11R6A2R5R4R2A5F_;Fmd;Ftr;Ftp;Fr;S1G1G2S2fS21R11R10RfReRdR8R4R3R2R1AaS43VCST;VXGL;R12S3eR12R7A2M3S4R10A1S4R5A1A6F_;Fmd;Ftr;Ftp;Fr;SbS0SfS17S0S35S3cR3S47ReR4A2A2A1A2A1S3dR3A1A3S1G1S1RdS20SdS4fVW;Vst;G3R11R3A5VE3P;R1R2A5S4cSdS4bR3R2VPFam;G3R11A2A5A2FrX;Ftp';Frho';S1G1RdS20SdS21R12R11R10RfReR9A6VLZ;R2R1A5S4cSdS4bRbRfVPFam;R12R11A2A5A2Ftp;Fr;F_;F_;F_;F_;Tc;Tnv;FphF;FHE;Frho;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").

Hypothesis H_entry : entryT.
Hypothesis H_prefix : prefixT.
Hypothesis H_pop : popT e_srcN.
Hypothesis H_exit : ltac2:(tb__ "0|0|
S6aS6cS59S57S5aA4").
Hypothesis H_back : backT.

Definition phFN (k : Z) : phase := ltac2:(tb__ "0|0|
S5fS5eS4eS23Vk;A2A1A1").

Theorem refill_N : ltac2:(tb__ "0|4|
S34S40S1S16S32Q40M0A1A1M1S1dS1dOF_;F_;S4aR4R1A2S41R5A1SbS18S38R7A1S1aA3SbS0S48R8S33G0S3R6PcM2A2A2A2Z0A3S4cSdS4bR7R6VPFam;R9R8A2A5S1dS1S2fS22RcR2R9R1VW;Vst;RaA7SeS3dS46S33G0S3R3G2A2A2A1A1S28RdR3A2A2S1G1S16S30A1S2fS21R12R11R8RfR7S6bS3dS46S33G0S3R8G2A2A2A1A1A1R4R3R2R1AaScS5dSdS3eR13S46S33G0S3R9G2A2A2A1A2M3R5R4R2A5S43VCST;VXGL;R13G3S4R9A1S4R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S34S1G1S1RbS20SdS4fVW;Vst;R4ReR3A5VE3P;R1R2A5S4cSdS4bR3R2VPFam;R4ReA2A5A2FrX;Ftp';Frho';FA';S1S2fS1S22RfR3RcR2VW;Vst;RdA7RcS20SdS21R10RfR4RdR3S23A6VLP;R2RdA5R7A2F_;Fr';Fmd0;Frb;S1RaS20SdS4fVW;Vst;ReRdRcA5VE3;R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp TR KIT HKc Hini Hcnt Q HREB HPOP HPOPUL rhoE.
  apply (tr_cutP Kc TR KIT Model _ (fun md0 => entryR A rhoE tp md0 W st rho) (fun md0 => SPA segs (JR A Kc rhoE tp md0 ph0) (cR0 E3) (r0_of A rhoE) tp) Q).
  { intros w Hw. exists (cfg_model (w_cfg w)). exact (H_entry A Kc rho rhoE tp w Hini Hcnt Hw). }
  intros md0 HE.
  apply (H_prefix A Kc rhoE tp md0 TR KIT HKc rho _ tp Q HE); [intros r'; exact (HPOPUL rhoE md0 r' HE)|].
  intros r1.

  apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FJ) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KIT (kchunks (cls_of (bv_unsigned (rw rhoE 12%positive))) <= gh_nf A rhoE)).
  { intros w [_ (HFz & HGh & _)]. destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. destruct (Z.ltb_spec (Z.of_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rhoE 12%positive)))))) (kchunks (cls_of (bv_unsigned (rw rhoE 12%positive))))) as [X|X]; [exfalso; apply BF; reflexivity | exact X]. }
  intros HNP. unfold gh_nf in HNP.
  set (nv := bv_unsigned (rw rhoE 12%positive)) in *. set (c := cls_of nv) in *. set (k := kchunks c) in *.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & _ & _ & (_ & MF0) & _).
  apply (H_pop A Kc rhoE tp md0 TR KIT HKc rho HE ph0 (conj eq_refl (conj eq_refl eq_refl)) (cs_free_array (cst_of A nv))
           (N_HSRC A rhoE tp md0 W st rho HE) HNP ltac:(lia) ltac:(cbn; intros X; exfalso; lia)
           (N_HIDS A rhoE tp md0 W st rho HE) (N_HCACHE A rhoE tp md0 W st rho HE HNP) (N_HSRCP A rhoE tp md0 W st rho HE HNP)).
  intros r2.
  apply (H_exit A Kc rhoE tp md0 TR KIT HKc rho HE (phK ph0 k) (conj eq_refl (conj eq_refl eq_refl)) ltac:(cbn; intros X; exfalso; lia) Hini
           (N_HRIv A rhoE tp md0 W st rho HE HNP) (N_HLEN A rhoE tp md0 W st rho HE HNP) (N_HIDC A rhoE tp md0 W st rho HE HNP)).
  intros r3.
  apply (H_back A Kc rhoE tp md0 TR KIT rho HE (phFN k)
           (fun r t tr md HJ => proj1 (HREB rhoE md0 HE HNP r t tr md HJ)) (fun r t tr md HJ => proj2 (HREB rhoE md0 HE HNP r t tr md HJ))
           (N_HLEN A rhoE tp md0 W st rho HE HNP) (HPOP (refillA A c))).
Qed.
End ASMN.
End SpineMallocR6.

(* [comment removed for export] *)
Module SpineCallocOvi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "L_calloc_null"; "JL_calloc_null"; "KcA"; "Kc_ok"; "Pre_callocI"; "unwind_stopJ"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "prod"; "pair"; "cons"; "option"; "Some"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "ss_next"; "sv"; "sobj"; "valuation"; "SLit"; "sprop_below"; "swf"; "SVar"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv"; "ov_cuts"; "stRo_S"; "EXo"; "s_o"; "stKo"; "N_ovn"; "R_o"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "Jc"; "rho_ce"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo"; "FACTSo"; "P0o"; "sb_o"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocSec2 SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocIo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS1i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineCallocOvA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wb_o : ltac2:(tb__ "0|0|
S15SaS2aS5cS1U0A1S0A2A1SbA3"). Proof. MemoFast.vmc. Qed.
Lemma Fb_o : ltac2:(tb__ "0|0|
S15SaS38S22S29S55A1S5aS1U0A1S0A2A3SbA3"). Proof. MemoFast.vmc. Qed.
Lemma RN_o : ltac2:(tb__ "0|0|
S15S9S26A1S33S1U0A1S0A2S12S26S56S42S59S26S58S32A4A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_o : ltac2:(tb__ "0|0|
S15SaS2aS2eS1U0A1S0A2A1SbA3"). Proof. MemoFast.vmc. Qed.
Lemma DKRn_o : ltac2:(tb__ "0|5|
S15S10SdS9SdS25S25A2M0A1M1S9S22A1M2A2M3A1S52S1cS31S1U0A1M4S0A2A1S2eG4S0A2A2S11G3SeG1G2SfG0SeS25S25S28S57A1S2bP18A1A4ScG0A1A3ScS22A1A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma NXRn_o : ltac2:(tb__ "0|1|
S15S1aS24S2eS1U0A1M0S0A2A1S24S1cS31G0S0A2A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_o : ltac2:(tb__ "0|1|
S15SaS1dS34S1U0A1M0S0A2S3S2G0S0A3S30G0S0A2A3SbA3"). Proof. MemoFast.vmc. Qed.
Lemma IDn_o : ltac2:(tb__ "0|0|
S15SaS53S30S1U0A1S0A2S3bA2SbA3"). Proof. MemoFast.vmc. Qed.
Definition CertO_o__runs : ltac2:(tb__ "0|0|
S9S10S9S1eA1A1A1") := ltac2:(tb__ "0|0|
S54S13Ufa0ScS19A1S2dU0S0A2A4").
Lemma CertO_o : ltac2:(tb__ "0|1|
S15SaS3fS13Ufa0ScS19A1S14S2dU0M0S0A2SfS1bS2fS1G0A1S0A2ScS1bA1A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GW (ov_cuts 0 UStopLe) [EXo (Wcan 0) UStopLe] CertO_o__runs); [unfold CertO_o__runs; reflexivity | MemoFast.vmc]. Qed.
Lemma ECertO_o : ltac2:(tb__ "0|3|
S15SaS40S13Ufa0ScS19A1S14S42S1bS3cS1bS3dR1Z1S28Z0M0A1M1A3Lc;S2dU0M2S0A2A4SfS3cS3dS2fS1G2A1S0A2G0G1A3ScS3cA1A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GW (map (fun c => mkVNA c 1 (SLit 0)) (ov_cuts 0 UStopLe)) [mkVNA (EXo (Wcan 0) UStopLe) 0 (SLit 0)] CertO_o__runs); [unfold CertO_o__runs; reflexivity | MemoFast.vmc]. Qed.
Lemma NXcuts_o : ltac2:(tb__ "0|0|
S1bS37S1bR1S2dU0S0A2A3S5dS14S24S1cR2A1A1A2F_;FC;").
Proof. intros C HC. apply Pos.leb_le. unfold ov_cuts in HC. destruct HC as [<-|[]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCUT_o : ltac2:(tb__ "0|4|
S41S27S8S1U0M0A1M1S0S4aR2R1A2A3S18S9S22A1M2G2S17S37S1bS3eR1S5bG1S0A2M3A2S2dG0S0A2A3S17S43S22S2cS4aR4R3A2A1R1A3S15SaS38S22S29S24S1cG3A1A1A1R1A3SbA3A2A2Lsx;A2F_;Frho;FA;").
Proof. intros A rho _. exists []. split; [left; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [constructor | reflexivity]]. Qed.

Theorem calloc_ov_0 : ltac2:(tb__ "0|4|
S9SdS19S19A2A1M0G0S20R2A1S21R2A1S19S1fR5R1A2S1fS48R2A2S16F_;F_;Fa;S19S1fR6R1A2S1fS4bR2A2S16F_;F_;Fa;S51OF_;S41S5S27S9S3aQ40M1A1A1S9SdS1bS35A2M2A1S6R4A1S46S13R7S45R5A1A3S37G2SeS1bS35S3S2S1U0A1M3S0A3S4S47S13A1ReRdR7R6A5A4R3A3S4cS4eZ2Z40A2S4dS39G1S23R6PcA2A2S39G1S23R6PdA2A2A2A2S50S13RaS44S13S49G3S0R9R8A4S7S2G3S0A3R7R6A5S36S13S3bR7R6R5A5A4F_;F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;Fok;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTM HCSTS.
  exact (calloc_ov 0 UStopLe CST XGL HCST HXGL HCSTM HCSTS HUS_c Wa_c Da_c Wb_o Fb_o RN_o WRn_o DKRn_o NXRn_o ENTn_o IDn_o (ov_cuts 0 UStopLe) HCUT_o CertO_o).
Qed.
Theorem ecalloc_ov_0 : ltac2:(tb__ "0|4|
S9SdS19S19A2A1M0G0S20R2A1S21R2A1S19S1fR5R1A2S1fS48R2A2S16F_;F_;Fa;S19S1fR6R1A2S1fS4bR2A2S16F_;F_;Fa;S41S5S27S9S3aQ40M1A1A1S9SdS1bS35A2M2A1S6R4A1S37G2SeS1bS35S3S2S1U0A1M3S0A3S4S47S13A1RcRbR6R5A5A4R2A3S4cS4eZ2Z40A2S4dS39G1S23R5PcA2A2S39G1S23R5PdA2A2A2A2S4fS13S44S13S49G3S0R8R7A4S7S2G3S0A3R6R5A5S36S13S3bR6R5R4A5A3F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;F_;F_;F_;F_;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL HCSTM HCSTS.
  exact (ecalloc_ov 0 UStopLe CST XGL HCST HXGL HCSTM HCSTS HUS_c Wa_c Da_c Wb_o Fb_o RN_o WRn_o DKRn_o NXRn_o ENTn_o IDn_o (ov_cuts 0 UStopLe) HCUT_o NXcuts_o ECertO_o).
Qed.
End SpineCallocOvi.

