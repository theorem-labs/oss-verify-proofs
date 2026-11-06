(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_base"; "seg_size"; "seg_writable"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "Some"; "andb"; "negb"; "option"; "orb"; "pair"; "prod"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "of_N"; "add"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "CTX_SIZE"; "LCtx"; "LMem"; "footprint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_img_hi"; "mc_img_lo"; "C_P"; "C_U"; "mconsts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "wseg_addr"; "client_addr_not_owned_stmt"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws"; "wsegs_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsP"; "segsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "find_segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws"; "statics_in_image"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocIface MallocLaws FpLaws Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma find_segment_In : ltac2:(tb__ "0|1|
SbS4A1S8S8S4S0SfS4A1S2dR4R3R2A3ScS4R1A2A3S1S2bS4R2R5A3S1S13S15S5R2A1A1M0R4A2S13S16R4R3A2S16G0S15S6R2A1A1A2A2A2A2F_;Fseg;Fn;Fx;Fsegs;").
Proof.
  induction segs as [|sg rest IH]; intros x n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base sg)) x && Z.leb (x + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n seg H) as (Hin & H1 & H2). split; [right; exact Hin | lia].
Qed.

Definition wsegs_inside (segs : list Segment) (lo hi : Z) : bool := ltac2:(tb__ "0|1|
S2cS4S4S10SeS7R1A1A1SdS17Vlo;S15S5R1A1A1M0A2S17S16G0S15S6R1A1A1A2Vhi;A2A2A2Lseg;Vsegs;A3").

Lemma wseg_in_range : ltac2:(tb__ "0|2|
SbS4A1S8S8S0S9S26R3R2R1A3SaA3S24Q40M0A1S0S9S22R5R1A2SaA3S1S13R5S25G0R2A2M1A2S14G1R4A2A2F_;Fa;F_;Fhi;Flo;Fsegs;").
Proof.
  intros segs lo hi H a Hw. unfold wseg_addr in Hw. unfold wsegs_inside in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  destruct (find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
  rewrite forallb_forall in H. specialize (H seg Hin). rewrite Hw in H. cbn [negb orb] in H.
  apply andb_prop in H as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4. lia.
Qed.

Lemma wsegs_inside_P : ltac2:(tb__ "0|0|
S0S9S26S27S1eS1fA1S1dS1fA1A3SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma wsegs_inside_U : ltac2:(tb__ "0|0|
S0S9S26S28S1eS20A1S1dS20A1A3SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem wseg_in_image_P : ltac2:(tb__ "0|2|
S24Q40M0A1S0S9S22S27R1A2SaA3S1S13S1eS1fA1S25G0R2A2M1A2S14G1S1dS1fA1A2A2F_;Fa;").
Proof. exact (wseg_in_range _ _ _ wsegs_inside_P). Qed.
Theorem wseg_in_image_U : ltac2:(tb__ "0|2|
S24Q40M0A1S0S9S22S28R1A2SaA3S1S13S1eS20A1S25G0R2A2M1A2S14G1S1dS20A1A2A2F_;Fa;").
Proof. exact (wseg_in_range _ _ _ wsegs_inside_U). Qed.

Lemma footprint_entry_cases : ltac2:(tb__ "0|0|
S2aS18S8S2bS12S18S8A2S11S18S8R2R1A4S1cR3A1A3S3S1S0S18R3S1aZ0A1A3S0S8R2S19A3A2S2S29S29S0S18R4S1bR1A1A3Lp;A2A2F_;Fn;Fl;Fs;").
Proof.
  intros s l n Hin. unfold footprint in Hin. destruct Hin as [E | Hin].
  - left. injection E as <- <-. auto.
  - right. apply in_app_iff in Hin as [Hin | Hin].
    + apply in_map_iff in Hin as (a & E & _). injection E as <- _. exists a. reflexivity.
    + apply in_flat_map in Hin as (k & _ & Hin).
      destruct (region_of s k) as [rg|]; [|destruct Hin].
      destruct (rg_kind rg); try (destruct Hin; fail).
      destruct (rg_live rg); [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- _. eexists. reflexivity.
Qed.

Theorem client_addr_not_owned : ltac2:(tb__ "0|2|
SbS4A1S21S2eR1A1S24Q40M0A1S0S9S22R4R1A2SaA3S1S13S1eR4A1S25G0R2A2M1A2S14G1S1dR4A1A2A2F_;Fa;S23R4R3A2F_;F_;FC;Fsegs;").
Proof.
  intros segs C HS HWS [s L] rho md a HM Hca.
  pose proof HM as (HW & HB & HC & ((HL & HI & HO) & HF) & HV & HST & HA & HLG & HIMG). cbn [ma_s ma_L] in *.
  pose proof HS as HS0. unfold statics_in_image in HS0. cbn beta zeta delta [CTX_SIZE PGSZ UNIT] in HS0.
  destruct HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & Ilock & Ictx & Ierr & Hpg & Hceil).

  assert (OWN : forall x, alloc_owned L s x ->
            (mc_ctx C <= x < mc_ctx C + CTX_SIZE)
            \/ (PGSZ <= x /\ x < topL L /\ ~ (mc_img_lo C <= x < mc_img_hi C))).
  { intros x [([l n] & Hrg & Hx) _]. cbn [fst snd] in Hx.
    destruct (footprint_entry_cases s l n Hrg) as [[-> ->] | [p ->]].
    - left. unfold loc_addr in Hx. rewrite HC in Hx. lia.
    - right. pose proof (fp_mem_range C L s (m_vmmaps md) p n HV HLG Hrg ltac:(lia)) as (G1 & G2 & G3).
      unfold addr_of in G1, G2, G3. lia. }
  pose proof (topL_range L) as TR.
  intros [Ho | Hl].
  -
    destruct Hca as [H | [(b & n & Hin & Hr) | (Hw & Hnctx & Hnlock & Hnerr)]].
    + cbn [ma_L] in H. destruct (OWN a Ho) as [X|X]; unfold CTX_SIZE, PGSZ, UNIT in *; lia.
    + destruct Ho as [_ Hnu]. apply Hnu.
      unfold ma_blocks, blocks in Hin. cbn [ma_s ma_L] in Hin.
      apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
      exists (p, n). split; [exact Hin|]. cbn [fst snd]. unfold addr_of in Hr. exact Hr.
    + pose proof (HWS _ Hw) as R.
      destruct (OWN a Ho) as [X|X].
      * exact (Hnctx X).
      * assert (Ha : 0 <= a < 2 ^ 64).
        { unfold PGSZ in X. lia. }
        rewrite Z_to_bv_unsigned, (bv_wrap_small 64 a) in R by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  -
    destruct Hca as [H | [(b & n & Hin & Hr) | (Hw & Hnctx & Hnlock & Hnerr)]].
    + cbn [ma_L] in H. unfold UNIT in *. lia.
    + pose proof (minv_block_geom C _ _ _ _ b n HM Hin) as (_ & _ & _ & _ & G). cbn [ma_s ma_L] in G. unfold UNIT, IB in G. lia.
    + exact (Hnlock Hl).
Qed.

Theorem client_addr_not_owned_P : client_addr_not_owned_stmt segsP C_P.
Proof. exact (client_addr_not_owned segsP C_P statics_in_image_P wseg_in_image_P). Qed.
Theorem client_addr_not_owned_U : client_addr_not_owned_stmt segsU C_U.
Proof. exact (client_addr_not_owned segsU C_U statics_in_image_U wseg_in_image_U). Qed.

Theorem malloc_laws_P : malloc_laws segsP C_P.
Proof.
  constructor.
  - exact (minv_frame C_P).
  - exact client_addr_not_owned_P.
  - exact statics_in_image_P.
  - exact wseg_in_image_P.
Qed.

Theorem malloc_laws_U : malloc_laws segsU C_U.
Proof.
  constructor.
  - exact (minv_frame C_U).
  - exact client_addr_not_owned_U.
  - exact statics_in_image_U.
  - exact wseg_in_image_U.
Qed.
