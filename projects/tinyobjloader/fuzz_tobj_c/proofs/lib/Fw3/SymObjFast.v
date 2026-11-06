(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sstate"; "sv"; "ss_facts"; "sprop"; "cell"; "ob_hi"; "ob_lo"; "ss_objs"; "c_off"; "is_arr"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ss_next"; "sv_below"; "@Corelib.Init.Datatypes"; "option"; "bool"; "prod"; "andb"; "Some"; "list"; "nat"; "None"; "S"; "cons"; "app"; "false"; "negb"; "@Corelib.Numbers.BinNums"; "Z"; "N"; "positive"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "mk_pf"; "pf_dg"; "in_bounds_pf"; "mkPF"; "pfacts"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObjFast"; "shift_ok_p"; "sitv_p"; "rebase_obj_p"; "merge_objs_at_p"; "mk_pf_x"; "rebase_obj_at_p"; "split_obj_at_p"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "leb"; "ltb"; "pow"; "opp"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "itv_lin"; "set_objs"; "sitv_of"; "ctx0"; "sitv"; "snorm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "shift_off"; "split_obj_at"; "obj_merge"; "obj_split"; "rebase_obj"; "shift_cell"; "shift_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymDigFast"; "mk_dig_x"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymObj SymDigFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition mk_pf_x (f : list sprop) : pfacts := ltac2:(tb__ "0|0|
S25Vf;S3eVf;A1S4aVf;A1A3").
Lemma mk_pf_x_eq : ltac2:(tb__ "0|0|
S16S4A1S21S26S2dR1A1S22R1A1A3Ff;").
Proof. intros f. unfold mk_pf_x, mk_pf. rewrite mk_dig_x_eq. reflexivity. Qed.

Definition shift_ok_p (pf : pfacts) (x : sv) (c : Z) : bool := ltac2:(tb__ "0|2|
S11S13S1eS1eA2M0A1S12Lx;S3dS3bS23Vpf;A1Vx;A2A1G0G0S12Lp;R1S1eS1eS14S33S36S35Z2Z3fA2M1A1S32R2Vc;A2A2S34S32R1Vc;A2G1A2A2Lh;Ll;X13x1Lp;S1cX11x2").
Lemma shift_ok_p_eq : ltac2:(tb__ "0|0|
S16S4A1S2S1eS21S12S29S22R3A1R2R1A3S49R3R2R1A3A3Fc;Fx;Ffacts;").
Proof. reflexivity. Qed.

Definition rebase_obj_p (pf : pfacts) (o : sobj) : option sobj := ltac2:(tb__ "0|d|
S2S11S0A1M0Lx;ScVo;A1S1eS18S0A1M1Lz;S20G1Li;M2S27S2S2S27G0Lop;R3S2G0Lb;R1S1eS40R1A1S1eS13S1eS1eA2G0Lx;S3bS23Vpf;A1R4A2S1eS1eS12G0L_;S14S14S14S14S14S14S33R2R1A2S33Z0S32R2R3A2A2A2S34S32R1R3A2S35Z2Z40A2A2A2S29Vpf;S7Vo;A1M3R3A3A2S29Vpf;S6Vo;A1M4R3A3A2S31S5S5S29Vpf;S9R1A1R4A3Lcl;SdVo;A1M5A3A2S1dSaSeVo;A1M6A1A1A2S15S0SbR6S43G3R3A2S43G4R3A2S3aS5S5S48R3A1G5A4G6A5A2G1X12x2Lh;Ll;X13x1Tc;Lc0;G2S27S2S2G1Lb0;La0;M7Lop0;M8G8S28G7Lop0;M9G9S12S1fS2G1La0;Lw;Lsgn;S20S2S1eG1Lk;Li;Ll;MaX2x8G1G1G1G1G1G1G1G1G1X27xaLb;La;Lop;S27S2S2G1Lb;La;MbLop;S28GbLop;McGcS12S1fS2G1La;Lw;Lsgn;GaX2x8").
Lemma rebase_obj_p_eq : ltac2:(tb__ "0|0|
S16S4A1S0S21S11S0A1S2bS22R2A1R1A2S47R2R1A2A3Fo;Ffacts;").
Proof. reflexivity. Qed.

Definition rebase_obj_at_p (pf : pfacts) (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|3|
S11S0A1S11S1A1Lx;M0S30S0S8VS;A1M1Vi;A3S0G0S2bVpf;R1A2S0S15S1S3cVS;S1bS0S38S0Vi;G1A3S1aS0R1S39S0S19Vi;A1G1A3A3A3A2A2Lo';S18S1A1M2X11x2Lo;G2X11x2").
Lemma rebase_obj_at_p_eq : ltac2:(tb__ "0|0|
S1S17S21S11S1A1S2eS22S3R2A1A1R2R1A3S42R2R1A2A3Fi;FS;").
Proof. reflexivity. Qed.

Definition sitv_p (pf : pfacts) (e : sv) : option (Z * Z) := ltac2:(tb__ "0|0|
S3dS3bS23Vpf;A1Ve;A2A1").
Lemma sitv_p_eq : ltac2:(tb__ "0|0|
S16S4A1S2S21S11S13S1eS1eA2A1S2aS22R2A1R1A2S3fR2R1A2A3Fe;Ffacts;").
Proof. reflexivity. Qed.

Definition merge_objs_at_p (pf : pfacts) (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|7|
S11S0A1S11S1A1M0Lx;M1S30S0S8VS;A1M2Vi;A3S0G1S30S0G2S19Vi;A1M3A3S0S11S13S1eS1eA2M4A1G0Lx;M5S2aVpf;S7R2A1A2G4G4G0Lp;R1S1eS1eG5S2aVpf;S6R4A1A2G4G4G0Lp0;R1S1eS1eS12G0L_;S34S37R1R5A2S35Z2Z3fA2A2G1S45R8R7A2S0S15S1S3cVS;S1bS0S38S0Vi;G2A3S1aS0R1S39S0S19G3A1G2A3A3A3A2A2Lo;S18S1A1M6X11x2G6X12x2Lh2;Lz0;X13x1Lp0;G6X11x2Lz;Ll1;X13x1Lp;G6X11x2Lo2;G6X11x2Lo1;G6X11x2").
Lemma merge_objs_at_p_eq : ltac2:(tb__ "0|0|
S1S17S21S11S1A1S2cS22S3R2A1A1R2R1A3S41R2R1A2A3Fi;FS;").
Proof. reflexivity. Qed.

Definition split_obj_at_p (pf : pfacts) (S : sstate) (i : nat) (mid : sv) : option sstate := ltac2:(tb__ "0|4|
S11S0A1S11S1A1M0Lx;S30S0S8VS;A1M1Vi;A3S0S12G0L_;S14S10SfVS;A1Vmid;A2S24Vpf;S7R1A1S6R1A1Vmid;Z0A5A2S11S13S0S0A2M2A1G0Lx;S46R1Vmid;A2G2G2G0Lp;R1S0S0S15S1S3cVS;S1bS0S38S0Vi;G1A3S1aS0R2S1aS0R1S39S0S19Vi;A1G1A3A3A3A3A2A2Lo2;Lo1;X13x1Lp;S18S1A1M3X11x2G3X12x2Lo;G3X11x2").
Lemma split_obj_at_p_eq : ltac2:(tb__ "0|0|
S1S17S2S21S11S1A1S2fS22S3R3A1A1R3R2R1A4S44R3R2R1A3A3Fmid;Fi;FS;").
Proof. reflexivity. Qed.

Lemma rebase_obj_at_facts : ltac2:(tb__ "0|0|
S1S17S1S21S11S1A1S42R3R2A2S15S1R1A2A3S21S16S4A1S3R2A1S3R4A1A3F_;FS';Fi;FS;").
Proof.
  intros S i S' H. unfold rebase_obj_at in H. destruct (nth_error (ss_objs S) i); [|discriminate].
  destruct (rebase_obj (ss_facts S) s); [|discriminate]. injection H as <-. reflexivity.
Qed.
Lemma merge_objs_at_facts : ltac2:(tb__ "0|0|
S1S17S1S21S11S1A1S41R3R2A2S15S1R1A2A3S21S16S4A1S3R2A1S3R4A1A3F_;FS';Fi;FS;").
Proof.
  intros S i S' H. unfold merge_objs_at in H.
  destruct (nth_error (ss_objs S) i); [|discriminate]. destruct (nth_error (ss_objs S) (Datatypes.S i)); [|discriminate].
  destruct (sitv (ss_facts S) (ob_lo s)) as [[l1 h1]|]; [|discriminate].
  destruct (sitv (ss_facts S) (ob_hi s0)) as [[l2 h2]|]; [|discriminate].
  destruct (h2 - l1 <? 2 ^ 63); [|discriminate]. destruct (obj_merge s s0); [|discriminate]. injection H as <-. reflexivity.
Qed.
Lemma split_obj_at_facts : ltac2:(tb__ "0|0|
S1S17S2S1S21S11S1A1S44R4R3R2A3S15S1R1A2A3S21S16S4A1S3R2A1S3R5A1A3F_;FS';Fmid;Fi;FS;").
Proof.
  intros S i mid S' H. unfold split_obj_at in H. destruct (nth_error (ss_objs S) i); [|discriminate].
  destruct (sv_below (ss_next S) mid && in_bounds (ss_facts S) (ob_lo s) (ob_hi s) mid 0); [|discriminate].
  destruct (obj_split s mid) as [[o1 o2]|]; [|discriminate]. injection H as <-. reflexivity.
Qed.
