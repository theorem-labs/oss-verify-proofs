(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Init.Datatypes"; "bool"; "option"; "nat"; "list"; "true"; "None"; "false"; "prod"; "pair"; "Some"; "length"; "S"; "andb"; "app"; "cons"; "nil"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "MachineOk"; "machine_result"; "mkAccessReport"; "ms_svc_pending"; "access_report"; "ms_regs"; "ms_rom"; "ov_read_bytes"; "store_ok"; "wview"; "find_segment"; "memory_access"; "step"; "step_accesses"; "write_to_mem"; "Build_machine_state"; "code_read_ov"; "decode_exec_accesses"; "fetch_failure"; "fetch_half_any"; "fetch_half_ov"; "fetch_tail_any"; "fetch_word_ov"; "interp_eff_accesses"; "ms_fcsr"; "ms_fregs"; "ms_pc"; "ms_pc_val"; "ms_reg"; "ms_resv"; "seg_ov_read_bytes"; "access_value"; "accessed_ranges"; "memory_read"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Restrict"; "mrestrict"; "restrict"; "ranges_avoid"; "range_avoids"; "unrestrict"; "hclean"; "munrestrict"; "woff"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_base"; "seg_size"; "seg_executable"; "seg_writable"; "@Stdlib.ZArith.BinInt.Z"; "of_N"; "add"; "le"; "of_nat"; "pow"; "modulo"; "@Stdlib.Lists.List"; "In"; "@Corelib.Numbers.BinNums"; "Z"; "N"; "@LinuxProcessSemantics.Riscv.Sem"; "core"; "eff"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.Riscv.Prelude"; "bvmap"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

Definition woff (a : word) (k : nat) : word := ltac2:(tb__ "0|1|
S2Q40M0S49S1G0Va;A2S4bVk;A1A2A2").

Lemma woff_0 : ltac2:(tb__ "0|1|
S0Q40A1M0S3G0S42R1U0A2R1A3Fa;").
Proof.
  intros a. unfold woff. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma woff_unsigned : ltac2:(tb__ "0|1|
S0Q40M0A1S9S3S4fS1G0S42R2R1A2A2S4dS49S1G0R2A2S4bR1A1A2S4cZ2Z40A2A2A3Fk;Fa;").
Proof.
  intros a k. unfold woff. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Definition mrestrict (H : word -> bool) (m : word -> option byte)
    : word -> option byte := ltac2:(tb__ "0|1|
S0Q40A1S7S8S0Q8A1M0A1L_;VH;R1A1ScG0A1Vm;R1A1X7x2La;").

Definition munrestrict (H : word -> bool) (full m' : word -> option byte)
    : word -> option byte := ltac2:(tb__ "0|0|
S0Q40A1S7S8S0Q8A1A1L_;VH;R1A1Vfull;R1A1Vm';R1A1X7x2La;").

Definition restrict (H : word -> bool) (ms : machine_state) : machine_state := ltac2:(tb__ "0|0|
S28S1eVms;A1S32Vms;A1S34Vms;A1S1cVms;A1S36Vms;A1S31Vms;A1S3bVH;S18Vms;A1A2S1fVms;A1A8").

Definition unrestrict (H : word -> bool) (full : word -> option byte)
    (ms' : machine_state) : machine_state := ltac2:(tb__ "0|0|
S28S1eVms';A1S32Vms';A1S34Vms';A1S1cVms';A1S36Vms';A1S31Vms';A1S41VH;Vfull;S18Vms';A1A3S1fVms';A1A8").

Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop := ltac2:(tb__ "0|1|
S0Q40M0A1S3S7VH;R1A1SbA3S3S8S43A1S23Vsegs;S1G0R2A2Z1A3ScS43A1A3F_;Fa;").

Definition wx_segs_nowrap (segs : list Segment) : Prop := ltac2:(tb__ "0|0|
S43S4eS43R1Vsegs;A3S3S7S13S46R2A1S47R2A1A2SbA3S4aS49S48S44R3A1A1S48S45R3A1A1A2S4cZ2Z40A2A2F_;F_;Fseg;").

Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop := ltac2:(tb__ "0|0|
S9S53R1Vn;A2S3S7VH;S42Va;R2A2A1SdA3F_;Fk;").

Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop := ltac2:(tb__ "0|1|
S0Q40A1M0S9S4eSeG0S9A2SfG0S9R2R1A4Vl;A3S3eVH;R3R2A3F_;Fn;Fa;").

Lemma woff_succ : forall a k, woff (a + 1) k = woff a (S k).
Proof.
  intros a k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma range_avoids_hd : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;G0S9S3eR3R2S12R1A1A3S3S7R4R3A1SdA3F_;Fn;Fa;FH;").
Proof.
  intros H a n Hr. rewrite <- (woff_0 a). apply Hr. lia.
Qed.

Lemma range_avoids_tl : forall H a n,
  range_avoids H a (S n) -> range_avoids H (a + 1) n.
Proof.
  intros H a n Hr k Hk. rewrite woff_succ. apply Hr. lia.
Qed.

Lemma range_avoids_cons : forall H a n,
  H a = false -> range_avoids H (a + 1) n -> range_avoids H a (S n).
Proof.
  intros H a n H0 Hr k Hk. destruct k as [|k].
  - rewrite woff_0. exact H0.
  - rewrite <- woff_succ. apply Hr. lia.
Qed.

Lemma ranges_avoid_nil : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;S3dR1S16SeG0S9A2A1A2FH;").
Proof. intros H a n Hin. destruct Hin. Qed.

Lemma ranges_avoid_cons : ltac2:(tb__ "0|2|
S0Q40A1M0S7F_;G0S9SaSeG0S9A2M1A1S3eR4R3R2A3S3dR5R2A2S3dR6S15G1SfG0S9R5R4A4R3A3A2F_;F_;Fl;Fn;Fa;FH;").
Proof.
  intros H a n l Ha Hl a' n' [Heq | Hin].
  - injection Heq as <- <-. exact Ha.
  - exact (Hl a' n' Hin).
Qed.

Lemma ranges_avoid_app : ltac2:(tb__ "0|3|
S0Q40A1M0S7F_;SaSeG0S9A2M1A1M2G2S3dR3R2A2S3dR4R2A2S3dR5S14G1R4R3A3A2F_;F_;Fl2;Fl1;FH;").
Proof.
  intros H l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin | Hin];
    [exact (H1 a n Hin) | exact (H2 a n Hin)].
Qed.

Lemma restrict_svc_pending : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;S17S3S8G0A1S1cS3cR2R1A2A1S1cR1A1A3Fms;FH;").
Proof. reflexivity. Qed.
Lemma restrict_pc : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;S17S3G0S33S3cR2R1A2A1S33R1A1A3Fms;FH;").
Proof. reflexivity. Qed.
Lemma restrict_regs : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;S17S3S54Q5G0A2S1eS3cR2R1A2A1S1eR1A1A3Fms;FH;").
Proof. reflexivity. Qed.
Lemma restrict_reg : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;S17S0Q5A1S3G0S35S3cR3R2A2R1A2S35R2R1A2A3Fr;Fms;FH;").
Proof. reflexivity. Qed.
Lemma restrict_rom : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;S17S3G0S8S0Q8A1A1F_;S1fS3cR2R1A2A1S1fR1A1A3Fms;FH;").
Proof. reflexivity. Qed.
Lemma restrict_mem : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;S17S3G0S8S0Q8A1A1F_;S18S3cR2R1A2A1S3bR2S18R1A1A2A3Fms;FH;").
Proof. reflexivity. Qed.
Lemma unrestrict_svc_pending : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;G0S8S0Q8A1A1F_;S17S3S8G0A1S1cS3fR3R2R1A3A1S1cR1A1A3Fms;Ffull;FH;").
Proof. reflexivity. Qed.
Lemma unrestrict_mem : ltac2:(tb__ "0|2|
S0Q40A1M0S7F_;G0S8S0Q8A1A1F_;M1S17S3G1S18S3fR3R2R1A3A1S41R3R2S18R1A1A3A3Fms;Ffull;FH;").
Proof. reflexivity. Qed.

Lemma mrestrict_idem : ltac2:(tb__ "0|3|
S0Q40A1M0S7F_;G0S8S0Q8A1A1F_;M1S3G1S3bR2S3bR2R1A2M2A2G2A3Fm;FH;").
Proof.
  intros H m. apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a); reflexivity.
Qed.

Lemma munrestrict_mrestrict : ltac2:(tb__ "0|2|
S0Q40A1M0S7F_;G0S8S0Q8A1A1F_;M1S3G1S41R2R1S3bR2R1A2A3R1A3Fm;FH;").
Proof.
  intros H m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma mrestrict_munrestrict : ltac2:(tb__ "0|2|
S0Q40A1M0S7F_;G0S8S0Q8A1A1F_;M1G1S3G1S3bR3S41R3R2R1A3A2S3bR3R1A2A3Fm;Ffull;FH;").
Proof.
  intros H full m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma unrestrict_restrict : ltac2:(tb__ "0|0|
S0Q40A1S7F_;S17S3S17S3fR2S18R1A1S3cR2R1A2A3R1A3Fms;FH;").
Proof.
  intros H ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite munrestrict_mrestrict. reflexivity.
Qed.

Lemma restrict_unrestrict : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;G0S8S0Q8A1A1F_;S17S3S17S3cR3S3fR3R2R1A3A2S3cR3R1A2A3Fms;Ffull;FH;").
Proof.
  intros H full ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite mrestrict_munrestrict. reflexivity.
Qed.

Definition hclean (H : word -> bool) (ms : machine_state) : Prop := ltac2:(tb__ "0|1|
S0Q40A1S3S7VH;R1A1SbA3S3S8S0Q8A1M0A1S18Vms;R2A2ScG0A1A3F_;Fa;").

Lemma restrict_hclean : ltac2:(tb__ "0|0|
S0Q40A1S7F_;S17S40R2S3cR2R1A2A2Fms;FH;").
Proof.
  intros H ms a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
Qed.

Lemma hclean_restrict_id : ltac2:(tb__ "0|0|
S0Q40A1S7F_;S17S40R2R1A2S3S17S3cR3R2A2R2A3F_;Fms;FH;").
Proof.
  intros H ms Hc. destruct ms. unfold restrict. cbn. f_equal.
  apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma restrict_unrestrict_clean : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;G0S8S0Q8A1A1F_;S17S40R3R1A2S3S17S3cR4S3fR4R3R2A3A2R2A3F_;Fms;Ffull;FH;").
Proof.
  intros H full ms Hc. rewrite restrict_unrestrict. apply hclean_restrict_id. exact Hc.
Qed.

Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma memory_read1_hidden : ltac2:(tb__ "0|1|
S0Q40A1S3S7VH;R1A1SbA3S3S8SaS0Q8A1A1M0A1S3aVsegs;R2Q1A3ScG0A1A3F_;Fa;").
Proof.
  intros a Ha. unfold memory_read. cbn [Z.of_N]. rewrite (HH a Ha). reflexivity.
Qed.

Lemma ov_read_bytes_restrict : ltac2:(tb__ "0|4|
S9S0Q40A1M0S8S0Q8A1M1A1F_;G0SaG1A1M2S3S8G2A1M3S20Vsegs;S3bVH;R3A2R2R4A4S10G2R1A2A3S4S3G3S20Vsegs;R4R3R5A4S10G2R2A2A3S3eVH;R3R5A3A2F_;Fbs;Fa;Fm;Fn;").
Proof.
  induction n as [|n IH]; intros m a bs Hr.
  - cbn in Hr |- *. split; [exact Hr | intros k Hk; lia].
  - cbn [ov_read_bytes] in Hr |- *.
    unfold mrestrict in Hr at 1.
    destruct (H a) eqn:Ha.
    + rewrite (memory_read1_hidden a Ha) in Hr. discriminate.
    + destruct (match m a with
                | Some b => Some b
                | None => match memory_read segs a 1 with
                          | Some (b :: _) => Some b | _ => None end
                end) as [b|]; [|discriminate].
      destruct (ov_read_bytes segs (mrestrict H m) (a + 1) n) as [rest|] eqn:Hrest;
        [|discriminate].
      destruct (IH m (a + 1) rest Hrest) as [Hfull Hav].
      rewrite Hfull. split; [exact Hr|].
      apply range_avoids_cons; assumption.
Qed.

Lemma wview_restrict : ltac2:(tb__ "0|3|
S0Q40A1M0S8S0Q8A1M1A1M2F_;G0S3G2S22Vsegs;S3bVH;R2A2R1A3S7G2L_;VH;R1A1ScG1A1S22Vsegs;R2R1A3X7x2A3Fa;Fm;").
Proof.
  intros m a. unfold wview, mrestrict. destruct (H a) eqn:Ha; [|reflexivity].
  rewrite (HH a Ha). reflexivity.
Qed.

Lemma store_ok_restrict : ltac2:(tb__ "0|1|
S9S0Q40A1M0S8S0Q8A1A1F_;G0S3S7S21Vsegs;S3bVH;R2A2R1R3A4SbA3S4S3S7S21Vsegs;R3R2R4A4SbA3S3eVH;R2R4A3A2F_;Fa;Fm;Fn;").
Proof.
  induction n as [|n IH]; intros m a Hs.
  - split; [reflexivity | intros k Hk; lia].
  - cbn [store_ok] in Hs |- *. rewrite wview_restrict in Hs.
    destruct (H a) eqn:Ha; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) Hs) as [Hfull Hav].
    split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.

Lemma write_to_mem_restrict : ltac2:(tb__ "0|3|
SaS0Q8A1M0A1S0Q40A1M1S8G0A1F_;M2G1S3eVH;R1S11G0R3A2A3S3G2S27S3bVH;R3A2R2R4A3S3bVH;S27R3R2R4A3A2A3F_;Fa;Fm;Fbs;").
Proof.
  induction bs as [|b bs IH]; intros m a Hav; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite <- (IH _ (a + 1) Htl). f_equal.
  apply functional_extensionality. intro x. unfold mrestrict.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha. reflexivity.
Qed.

Lemma write_to_mem_hidden : ltac2:(tb__ "0|3|
SaS0Q8A1M0A1S0Q40A1M1S8G0A1M2F_;G1G1S3eVH;R2S11G0R4A2A3S3S7VH;R2A1SbA3S3G2S27R5R4R6R3A4R5R3A1A3F_;F_;Fx;Fa;Fm;Fbs;").
Proof.
  induction bs as [|b bs IH]; intros m a x Hav Hx; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite (IH _ (a + 1) x Htl Hx). cbv beta.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha in Hx. discriminate.
Qed.

Lemma mrestrict_visible : ltac2:(tb__ "0|2|
S0Q40A1M0S7F_;G0S8S0Q8A1A1M1F_;G0S3S7R3R1A1SdA3S3G1S3bR4R3R2A3R3R2A1A3F_;Fa;Fm;FH0;").
Proof. intros H0 m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.

Lemma ov_read_bytes_mrestrict_eq : ltac2:(tb__ "0|2|
S0Q40A1M0S7F_;S9G0S8S0Q8A1M1A1F_;G0S3eR4R1R3A3S3S8SaG1A1A1S20Vsegs;S3bR5R3A2R2R4A4S20Vsegs;R3R2R4A4A3F_;Fa;Fm;Fn;FH0;").
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [ov_read_bytes]. unfold mrestrict at 1. rewrite (range_avoids_hd H0 a n Hav).
  rewrite (IH m (a + 1) (range_avoids_tl H0 a n Hav)). reflexivity.
Qed.

Lemma wview_mrestrict_eq : ltac2:(tb__ "0|2|
S0Q40A1M0S7F_;G0S8S0Q8A1A1M1F_;G0S3S7R3R1A1SdA3S3G1S22Vsegs;S3bR4R3A2R2A3S22Vsegs;R3R2A3A3F_;Fa;Fm;FH0;").
Proof. intros H0 m a Ha. unfold wview, mrestrict. rewrite Ha. reflexivity. Qed.

Lemma store_ok_mrestrict_eq : ltac2:(tb__ "0|1|
S0Q40A1M0S7F_;S9G0S8S0Q8A1A1F_;G0S3eR4R1R3A3S3S7S21Vsegs;S3bR5R3A2R2R4A4S21Vsegs;R3R2R4A4A3F_;Fa;Fm;Fn;FH0;").
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [store_ok]. rewrite (wview_mrestrict_eq H0 m a (range_avoids_hd H0 a n Hav)).
  destruct (wview segs m a); [|reflexivity].
  exact (IH m (a + 1) (range_avoids_tl H0 a n Hav)).
Qed.

Lemma find_segment_some_spec : ltac2:(tb__ "0|1|
SaS43A1S4fS4fS43S3S8S43A1S23R4R3R2A3S10S43R1A2A3S4S4eS43R2R5A3S4S4aS48S44R2A1A1M0R4A2S4aS49R4R3A2S49G0S48S45R2A1A1A2A2A2A2F_;Fseg;Fn;Faddr;Fl;").
Proof.
  induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - injection Hf as ->. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | split; assumption].
  - destruct (IH addr n seg Hf) as (Hin & H1 & H2).
    split; [right; exact Hin | split; assumption].
Qed.

Lemma find_segment_none_spec : ltac2:(tb__ "0|1|
SaS43A1S4fS4fS3S8S43A1S23R3R2R1A3ScS43A1A3S43S4eS43R1R5A3S6S4S4aS48S44R2A1A1M0R5A2S4aS49R5R4A2S49G0S48S45R2A1A1A2A2A2A1F_;Fseg;F_;Fn;Faddr;Fl;").
Proof.
  induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
    [discriminate|].
  destruct Hin as [<- | Hin].
  - intros [H1 H2]. apply andb_false_iff in E as [E | E].
    + apply Z.leb_gt in E. lia.
    + apply Z.leb_gt in E. lia.
  - exact (IH addr n Hf seg Hin).
Qed.

Lemma in_segment_not_hidden : ltac2:(tb__ "0|1|
S0Q40M0A1S43S4eS43R1Vsegs;A3S4aS48S44R2A1A1S1G0R3A2A2S4aS49S1G0R4A2Z1A2S49S48S44R3A1A1S48S45R3A1A1A2A2S3S7VH;R5A1SdA3F_;F_;F_;Fseg;Fx;").
Proof.
  intros x seg Hin H1 H2. destruct (H x) eqn:Hx; [|reflexivity].
  exfalso. exact (find_segment_none_spec segs (bv_unsigned x) 1 (HH x Hx) seg Hin (conj H1 H2)).
Qed.

Lemma seg_ov_read_bytes_restrict : ltac2:(tb__ "0|3|
S9S0Q40M0A1M1S8S0Q8A1M2A1F_;S43G1S4eS43R2Vsegs;A3S4aS48S44R3A1A1S1G0R2A2A2S4aS49S1G0R3A2S4bR6A1A2S49S48S44R4A1A1S48S45R4A1A1A2A2S4aS49S48S44R5A1A1S48S45R5A1A1A2S4cZ2Z40A2A2S3S8SaG2A1A1S37S3bVH;R7A2R6R5R8A4S37R7R6R5R8A4A3F_;F_;F_;F_;Fa;Fseg;Fm;Fn;").
Proof.
  induction n as [|n IH]; intros m seg a Hin Hlo Hhi Htop; [reflexivity|].
  cbn [seg_ov_read_bytes].
  assert (Ha : H a = false) by (apply (in_segment_not_hidden a seg Hin); lia).
  unfold mrestrict at 1. rewrite Ha.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z).
    { rewrite bv_add_unsigned.
      assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (bv_unsigned_in_range 64 a). lia. }
    rewrite (IH m seg (a + 1) Hin) by lia. reflexivity.
Qed.

Lemma code_read_ov_restrict : ltac2:(tb__ "0|2|
S0Q40A1M0S8S0Q8A1M1A1F_;G0S50S3S8SaG1A1A1S29Vsegs;S3bVH;R3A2R2R1A4S29Vsegs;R3R2R1A4A3Fn;Fa;Fm;").
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg) eqn:Ewx; [|reflexivity].
  destruct (find_segment_some_spec segs _ _ seg Hf) as (Hin & H1 & H2).
  apply seg_ov_read_bytes_restrict; [exact Hin | exact H1 | | exact (Hwx seg Hin Ewx)].
  rewrite N_nat_Z. exact H2.
Qed.

Lemma fetch_word_ov_restrict : ltac2:(tb__ "0|1|
S0Q40A1M0S8S0Q8A1A1F_;G0S3S8S0Q20A1A1S2fVsegs;S3bVH;R2A2R1A3S2fVsegs;R2R1A3A3Fa;Fm;").
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_ov_restrict : ltac2:(tb__ "0|1|
S0Q40A1M0S8S0Q8A1A1F_;G0S3S8S0Q10A1A1S2dVsegs;S3bVH;R2A2R1A3S2dVsegs;R2R1A3A3Fa;Fm;").
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_any_restrict : ltac2:(tb__ "0|1|
S0Q40A1M0S8S0Q8A1A1F_;G0S3S8S0Q10A1A1S2cVsegs;S3bVH;R2A2R1A3S2cVsegs;R2R1A3A3Fa;Fm;").
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

Lemma fetch_tail_any_restrict : ltac2:(tb__ "0|1|
S0Q40A1M0S8S0Q8A1A1F_;G0S3S8S0Q20A1A1S2eVsegs;S3bVH;R2A2R1A3S2eVsegs;R2R1A3A3Fa;Fm;").
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

Lemma fetch_failure_restrict : ltac2:(tb__ "0|1|
S0Q40A1M0S8S0Q8A1A1F_;G0S3S1aS17A1S2bVsegs;S3bVH;R2A2R1A3S2bVsegs;R2R1A3A3Fa;Fm;").
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

Lemma interp_eff_accesses_restrict : ltac2:(tb__ "0|6|
S52S0Q40A1M0S8S0Q8A1A1M1F_;M2S51G2SaS24A1S3S1aS1dSeS51G2A2M3A1M4A1M5S30Vsegs;R5S3bVH;R4A2A3S19G4S1bG3SfS51G2R3R2A4R1A3A2A3S5G2G2S4S3G5S30Vsegs;R7R6A3S19G4S1bG3SfS51G2R5R1A4R3A3A2A3S4S3G2R4S3bVH;R1A2A3S4G0S3S7VH;R1A1SbA3S3G1R3R2A1R8R2A1A3F_;Fx;S3dVH;R3A2A2A2A2Lmf';A2F_;Frs;Fmr';Fc;Fm;Ft;").
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  -
    injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    apply ranges_avoid_nil.
  -
    destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
      [|discriminate].
    destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
    rewrite Hfull.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
    apply ranges_avoid_cons; assumption.
  -
    destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
    + intros x Hx. rewrite (Hhid x Hx).
      apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
    + apply ranges_avoid_cons; assumption.
Qed.

Lemma decode_exec_accesses_restrict : ltac2:(tb__ "0|2|
S17S0Q20A1S17SaS24A1S3S1aS1dS17A1M0A1M1S2aVsegs;S3cVH;R4A2R3A3S19G0S1bS17R2R1A3A2A3S4S3G1S2aVsegs;R5R4A3S19G0S1bS17S3fVH;S18R5A1R3A3R2A3A2A3S4S3dVH;R2A2S40VH;R3A2A2A2F_;Frs';Fmsr';Fw;Fms;").
Proof.
  intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-.
    split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
    unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
    rewrite munrestrict_mrestrict. destruct ms; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
    destruct (interp_eff_accesses segs
                (exec (Z_to_bv 64 isz) i
                   {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
                      c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
                      c_resv := ms_resv ms |})
                (mrestrict H (ms_mem ms)))
      as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
      as (mf' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn [access_value accessed_ranges].
    split; [|split; [exact Hrs|]].
    + unfold unrestrict. cbn.
      replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
      apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
      destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

Theorem step_accesses_restrict : ltac2:(tb__ "0|2|
S17S17SaS24A1S3S1aS1dS17A1M0A1M1S26Vsegs;S3cVH;R3A2A2S19G0S1bS17R2R1A3A2A3S4S3G1S26Vsegs;R4A2S19G0S1bS17S3fVH;S18R4A1R3A3R2A3A2A3S4S3dVH;R2A2S40VH;R3A2A2A2F_;Frs';Fmsr';Fms;").
Proof.
  intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

Theorem step_restrict_sound : ltac2:(tb__ "0|2|
S17S17S3S1aS17A1S25Vsegs;S3cVH;R2A2A2S19S17R1A2A3S5S1dS17A1M0G0S4S3S1aG0A1S26Vsegs;R4A2S19G0R1A2A3S4S3S17S38S17R1A2S3fVH;S18R4A1R3A3M1A3S4S3dVH;S39S17R1A2A2S4S40VH;R3A2S3S17S3cVH;G1A2R3A3A2A2A2A2Lrep;A2F_;Fmsr';Fms;").
Proof.
  intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as ->.
  destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
  exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
  split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
  apply restrict_unrestrict_clean. exact Hcl.
Qed.

Corollary step_restrict_step : ltac2:(tb__ "0|1|
S17S17S3S1aS17A1M0S25Vsegs;S3cVH;R2A2A2S19S17R1A2A3S3G0S25Vsegs;R3A2S19S17S3fVH;S18R3A1R2A3A2A3F_;Fmsr';Fms;").
Proof.
  intros ms msr' Hs.
  destruct (step_restrict_sound ms msr' Hs) as (rep & Hsa & Hv & _).
  unfold RiscvSemantics.step, drop_access_report. rewrite Hsa, Hv. reflexivity.
Qed.

Lemma step_accesses_ecall_shape : forall ms msr' rs',
  step_accesses segs ms = MachineOk (@mkAccessReport _ msr' rs') ->
  ms_svc_pending msr' <> None ->
  rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
  /\ ms_svc_pending msr' = Some (ms_reg ms 17).
Proof.
  intros ms msr' rs' Hs Hsvc.
  assert (Hdec : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ msr' rs') ->
            rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
            /\ ms_svc_pending msr' = Some (ms_reg ms 17)).
  { intros w Hd. unfold decode_exec_accesses in Hd.
    destruct (is_ecall w).
    - injection Hd as <- <-. cbn. repeat split; reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses segs _ _) as [[[c1 m1] rs1]| |]; try discriminate.
      cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn in Hsvc.
      exfalso. apply Hsvc. reflexivity. }
  unfold step_accesses in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Hf; try discriminate.
  unfold fetch_failure in Hf.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

End ISA.
