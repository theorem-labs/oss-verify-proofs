(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "ss_next"; "sv"; "sobj"; "agree_below"; "odefault"; "smatch"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_objs"; "sv_below"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@Corelib.Init.Datatypes"; "option"; "Some"; "bool"; "list"; "orb"; "andb"; "nat"; "pair"; "None"; "false"; "prod"; "true"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "to_N"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "stableJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "load_res"; "in_bounds"; "load_arr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ArrMat"; "arr_mat_at"; "k_okb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@Stdlib.Lists.List"; "nth_error"; "@Stdlib.NArith.BinNat.N"; "mul"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition k_okb (k : Z) : bool := ltac2:(tb__ "0|0|
S19S19S19S21Vk;Z1A2S21Vk;Z2A2A2S21Vk;Z4A2A2S21Vk;Z8A2A2").

Definition arr_mat_at (S : sstate) (n : nat) (off : sv) (k : Z) : option sstate := ltac2:(tb__ "0|3|
S15S4A1S15S0A1M0Lx;S31S4ScVS;A1Vn;A3S4S6G0Lx;S8R1A1S1dS0A1M1G1G1S10G1Ll;M2G2SfS3S18S1fSfSfA2A1S18SeA1S17G0L_;S1aS1aS2cVk;A1SdS2VS;A1Voff;A2A2S29SbVS;A1SaR5A1S9R5A1Voff;Vk;A5A2S28G0Lx;S2aVS;Vn;R5Voff;Vk;S1eS32Q8S22Vk;A1A2R4R3R2R1AbS3S0S16S0R1A2LS';Lv;G1X28x2G1X17x2Ltmpl;Lflds;Lcnt;Lesz;X6x6Lo;G1X15x2").

Section M.
Variable segs : list Segment.

Lemma k_okb_sound : ltac2:(tb__ "0|0|
SfS11S17S2cR1A1S20A3S13S11SfR2Z1A3S13S11SfR2Z2A3S13S11SfR2Z4A3S11SfR2Z8A3A2A2A2F_;Fk;").
Proof using .
  intros k H. unfold k_okb in H. rewrite !Bool.orb_true_iff, !Z.eqb_eq in H. tauto.
Qed.

Theorem smatch_arr_mat : ltac2:(tb__ "0|2|
S1S0S1bS3SfS0S18S2fA1M0S2dS2eS11S15S0A1S2bR8R7R6R5A4S16S0R4A2A3S7Vsegs;RaR9S1cG0S23R4S24R3R2A2A4A4S14S1S1S12S5S2RbA1M1RcR1A3S12S33G1S2R7A1A2S7Vsegs;R1R7S1cG0S23R6S24R5R4A2A4A4A2A2Lrho';A2F_;F_;Fmd;Fms;Ftr;FS';Fk;Foff;Fn;FS;Frho;").
Proof using .
  intros rho S n off k S' tr ms md H Hsm. unfold arr_mat_at in H.
  destruct (nth_error (ss_objs S) n) as [o|] eqn:Hn; [|discriminate].
  destruct (ob_dflt o) as [| | | | |esz cnt flds tmpl] eqn:Hd; try discriminate.
  destruct (k_okb k && sv_below (ss_next S) off && in_bounds (ss_facts S) (ob_lo o) (ob_hi o) off k) eqn:C; [|discriminate].
  apply andb_prop in C as [C Hib]. apply andb_prop in C as [Hk Hoff]. apply k_okb_sound in Hk.
  destruct (load_arr S n o off k false (8 * Z.to_N k)%N esz cnt flds tmpl) as [v S1|] eqn:HL; [|discriminate].
  injection H as ->.
  pose proof Hsm as (Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & Hfacts). cbn [fst snd cfg_ms cfg_model] in Hmem, Hfacts.
  destruct Hmem as (Hall & _ & _).
  pose proof (proj1 (Forall_forall _ _) Hall o (nth_error_In _ _ Hn)) as Hoh.
  assert (Howf : obj_wf (ss_next S) o = true).
  { unfold swf in Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [_ Hobjs].
    exact (proj1 (forallb_forall _ _) Hobjs o (nth_error_In _ _ Hn)). }
  destruct (in_bounds_sound rho (ss_facts S) (ob_lo o) (ob_hi o) off k Hfacts ltac:(lia) Hib) as [Hlo Hhi].
  destruct (load_arr_sound segs rho S tr ms md n o off k false v S' esz cnt flds tmpl Hsm Hk Hn Hoh Howf Hoff Hlo Hhi Hd HL)
    as (bs & rho' & _ & Hag & Hle & Hsm' & _).
  exists rho'. auto.
Qed.

Lemma SPJ_arr_mat : ltac2:(tb__ "0|0|
S26S1S0S1bS3SfS0S30S11S15S0A1S2bR6R5R4R3A4S16S0R2A2A3S27S2R7A1R9A2S25Vsegs;RaR8R9R3A5S14S1S1S12S5S2RaA1RbR1A3S25Vsegs;RcR6R1R5A5A2Lrho';A2F_;F_;F_;Fw;FS';Fk;Foff;Fn;FS;Frho;FJ;").
Proof using .
  intros J rho S n off k S' [tr [ms md]] H HJ [Hsm Hj].
  destruct (smatch_arr_mat rho S n off k S' tr ms md H Hsm) as (rho' & Hag & _ & Hsm').
  exists rho'. split; [exact Hag|]. split; [exact Hsm'|]. eapply HJ; [exact Hag | exact Hj].
Qed.
End M.
