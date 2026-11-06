(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: lib/YP0iR.v, new, holds part of YP0i.v and YP09.v: sym_step_sh_soundP's
   shadow-arm proof steps (YP0i.v) and store_region's case split (YP09.v), reused in sym_step_sh_shadow_accs and
   store_region_in with the read-region bound accs_in_rrange (YP09R.v) added; new lemmas step_rep,
   step_accesses_on_fetch, sload_region_in, sstore_region_in, region_accs, accs_one, accs_two and
   sym_step_sh_soundR. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK0o YK15.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP00 YP0k YP06 YP03 YP0i YP09R YP0kR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(* sym_step_sh_soundP (YP0i.v) with a read-region bound: every memory range the machine step reports
   (RiscvSemantics.step_accesses, the list materialize_model_accesses reads) lies in a region extent of
   the symbolic memory (YP09R.accs_in_rrange). *)

Lemma step_rep : forall segs ms ms', RiscvSemantics.step segs ms = MachineOk ms' ->
  exists rep, step_accesses segs ms = MachineOk rep /\ access_value _ rep = ms'.
Proof.
  intros segs ms ms' H. unfold RiscvSemantics.step, drop_access_report in H.
  destruct (step_accesses segs ms) as [rep| |]; try discriminate.
  injection H as <-. exists rep. split; reflexivity.
Qed.

Lemma step_accesses_on_fetch : forall segs ms w,
  fetch_word segs (ms_pc_val ms) = Some w -> step_accesses segs ms = decode_exec_accesses segs ms w.
Proof. intros segs ms w H. unfold step_accesses, ms_pc. rewrite H. reflexivity. Qed.

Lemma store_region_in : forall rs b off n cv rs',
  store_region rs b off n cv = Some rs' ->
  exists r, In r rs /\ r_base r = b /\ r_lo r <= off /\ off + n <= r_hi r.
Proof.
  induction rs as [|r rs IH]; cbn [store_region]; intros b off n cv rs' H; [discriminate|].
  destruct (obase_eqb (r_base r) b && (r_lo r <=? off) && (off + n <=? r_hi r)) eqn:Hc.
  - apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply obase_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    exists r. split; [left; reflexivity|]. auto.
  - destruct (store_region rs b off n cv) as [rs''|] eqn:Hs; [|discriminate].
    destruct (IH _ _ _ _ _ Hs) as (r0 & Hin & Hb & Hlo & Hhi).
    exists r0. split; [right; exact Hin|]. auto.
Qed.

Lemma sload_region_in : forall segs G rs b off sz sg v,
  sload segs G rs b off sz sg = Some v ->
  exists r, In r rs /\ r_base r = b /\ r_lo r <= off /\ off + Z.of_nat (nbytes sz) <= r_hi r.
Proof.
  intros segs G rs b off sz sg v H. unfold sload in H.
  destruct (find_region rs b off (Z.of_nat (nbytes sz))) as [r|] eqn:Hf; [|discriminate].
  exists r. exact (find_region_sound _ _ _ _ _ Hf).
Qed.

Lemma sstore_region_in : forall rs b off sz v rs',
  sstore rs b off sz v = Some rs' ->
  exists r, In r rs /\ r_base r = b /\ r_lo r <= off /\ off + Z.of_nat (nbytes sz) <= r_hi r.
Proof. intros rs b off sz v rs' H. unfold sstore in H. exact (store_region_in _ _ _ _ _ _ H). Qed.

(* One reported range (base + off, n) inside a region extent of a well-formed symbolic memory. *)
Lemma region_accs : forall segs E m rs b off n,
  mem_ok segs E m rs ->
  (exists r, In r rs /\ r_base r = b /\ r_lo r <= off /\ off + Z.of_nat n <= r_hi r) ->
  forall k, (k < n)%nat -> in_rrange E rs (bv_unsigned (Z_to_bv 64 (base_val E b + off)) + Z.of_nat k).
Proof.
  intros segs E m rs b off n (_ & Hall & _) (r & Hin & Hb & Hlo & Hhi) k Hk.
  rewrite Forall_forall in Hall. destruct (Hall r Hin) as (H0 & H1 & _).
  subst b. exists r. split; [exact Hin|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma accs_one : forall E rs a n,
  (forall k, (k < n)%nat -> in_rrange E rs (bv_unsigned a + Z.of_nat k)) ->
  accs_in_rrange E rs [(a, n)].
Proof.
  intros E rs a n H a' n' k Hin Hk. destruct Hin as [Heq|[]]. injection Heq as <- <-. exact (H k Hk).
Qed.

Lemma accs_two : forall E rs a n,
  (forall k, (k < n)%nat -> in_rrange E rs (bv_unsigned a + Z.of_nat k)) ->
  accs_in_rrange E rs [(a, n); (a, n)].
Proof.
  intros E rs a n H a' n' k Hin Hk. destruct Hin as [Heq|[Heq|[]]]; injection Heq as <- <-; exact (H k Hk).
Qed.

Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Hypothesis Htbl : table_ok segs tbl.
Section e.
Variable P1 : env -> list sv -> bvmap 5 word -> Prop.
Variable P5 : list sv -> bv 32 -> Prop.
Local Notation st_okP := (st_okP segs P1 P5).

(* The shadow arms of sym_step_sh (YP0i.v:229-283): the machine step's reported ranges. *)
Lemma sym_step_sh_shadow_accs : forall E ss ss' ms why rep,
  st_okP E ss ms -> sym_step segs tbl ss = SStop why -> sym_step_sh segs tbl ss = SRun ss' ->
  step_accesses segs ms = MachineOk rep ->
  accs_in_rrange E (ss_mem ss) (accessed_ranges _ rep).
Proof.
  intros E ss ss' ms why rep HS Hs H Hrep. unfold sym_step_sh in H. rewrite Hs in H.
  destruct ms as [regs fregs pcv pend resv fcsr mem rom].
  destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
  subst pcv pend rom.
  destruct (clookup tbl (ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate].
  pose proof (Htbl (ss_pc ss) wz Hlk) as Hf. cbv zeta in H.
  rewrite (step_accesses_on_fetch segs _ (Z_to_bv 32 wz)) in Hrep by exact Hf.
  unfold decode_exec_accesses in Hrep.
  destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec; [discriminate|].
  destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hd; [|discriminate].
  assert (HR : forall r, rget (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) r
                 = sv_denot E (sr_get (ss_regs ss) r)).
  { intros r. rewrite rget_regs. apply Hregs. }
  destruct i; try discriminate; try match goal with op : amoop |- _ => destruct op; try discriminate end;
  destruct (isz =? 4) eqn:Hsz; cbn [negb] in H; try discriminate; apply Z.eqb_eq in Hsz; subst isz;
  cbv beta iota zeta delta
    [interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr] in Hrep;
  rewrite ?rset_core in Hrep; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv] in Hrep;
  rewrite ?HR in Hrep.
  - (* load *)
    remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
    destruct (shadow_norm (ss_facts ss) a) as [[b off]|] eqn:Hao; [|discriminate].
    destruct (sload segs (ss_facts ss) (ss_mem ss) b off sz signed) as [v|] eqn:Hsl; [|discriminate].
    pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem Hsl) as (bs & Hrd & Hv).
    assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
    { rewrite <- (shadow_norm_sound E (ss_facts ss) a b off HG Hao). subst a.
      rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
    rewrite Haddr in Hrep.
    pose proof (region_accs segs E mem (ss_mem ss) b off (nbytes sz) Hmem (sload_region_in _ _ _ _ _ _ _ _ Hsl)) as RA.
    destruct sz; cbn [nbytes nbits] in Hrd, Hv, RA;
    cbv beta iota zeta delta [RiscvSemantics.width_bytes] in Hrep;
    rewrite ov_rdn, Hrd in Hrep; cbn in Hrep; injection Hrep as <-; cbn [accessed_ranges];
    apply accs_one; exact RA.
  - (* store *)
    destruct (ss_resv ss) as [rv0|] eqn:Hrv; [discriminate|]. cbn in Hresv. subst resv.
    remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
    destruct (shadow_norm (ss_facts ss) a) as [[b off]|] eqn:Hao; [|discriminate].
    destruct (sstore (ss_mem ss) b off sz (sr_get (ss_regs ss) rs2)) as [m'|] eqn:Hst; [|discriminate].
    pose proof (sstore_sound segs E mem _ _ _ _ _ m' Hmem Hst) as [Hok Hmem'].
    assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
    { rewrite <- (shadow_norm_sound E (ss_facts ss) a b off HG Hao). subst a.
      rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
    rewrite Haddr in Hrep.
    pose proof (region_accs segs E mem (ss_mem ss) b off (nbytes sz) Hmem (sstore_region_in _ _ _ _ _ _ Hst)) as RA.
    destruct sz; cbn [nbytes nbits] in Hok, RA;
    cbv beta iota zeta delta [RiscvSemantics.width_bytes] in Hrep;
    rewrite Hok in Hrep; cbn in Hrep; injection Hrep as <-; cbn [accessed_ranges];
    apply accs_one; exact RA.
  - (* amoadd *)
    destruct (ss_resv ss) as [rv0|] eqn:Hrv; [discriminate|]. cbn in Hresv. subst resv.
    destruct (aligned_dec (ss_facts ss) (sr_get (ss_regs ss) rs1) (amo_bytes_of w)) eqn:Hal;
      cbn [negb] in H; [|discriminate].
    destruct (addr_of (sr_get (ss_regs ss) rs1)) as [[b off]|] eqn:Hao; [|discriminate].
    destruct (sload segs (ss_facts ss) (ss_mem ss) b off (amo_sz w) true) as [v|] eqn:Hsl; [|discriminate].
    destruct (sstore (ss_mem ss) b off (amo_sz w) (s_alu2 (ss_facts ss) ALU_ADD v (sr_get (ss_regs ss) rs2)))
      as [m'|] eqn:Hst; [|discriminate].
    pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem Hsl) as (bs & Hrd & Hv).
    pose proof (sstore_sound segs E mem _ _ _ _ _ m' Hmem Hst) as [Hok Hmem'].
    pose proof (addr_of_sound E (ss_facts ss) _ b off HG Hao) as Haddr.
    assert (Hamo : amo_aligned w (sv_denot E (sr_get (ss_regs ss) rs1)) = true).
    { unfold amo_aligned. apply Z.eqb_eq.
      apply (aligned_dec_sound P1 E (ss_facts ss)); [exact HG| destruct w; cbn; lia |].
      destruct w; exact Hal. }
    pose proof (region_accs segs E mem (ss_mem ss) b off (nbytes (amo_sz w)) Hmem
                  (sload_region_in _ _ _ _ _ _ _ _ Hsl)) as RA.
    rewrite Hamo in Hrep. cbn [negb] in Hrep. rewrite Haddr in *.
    destruct w; cbn [amo_sz nbytes nbits] in Hrd, Hv, Hok, RA;
    cbv beta iota zeta delta [RiscvSemantics.width_bytes] in Hrep;
    rewrite ov_rdn, Hrd, Hok in Hrep; cbn in Hrep; injection Hrep as <-; cbn [accessed_ranges];
    apply accs_two; exact RA.
Qed.

(* The fallback arm runs sym_step (YP0kR.sym_step_soundR); the three shadow arms are YP0i's
   sym_step_sh_soundP for the step and sym_step_sh_shadow_accs for the reported ranges. *)
Theorem sym_step_sh_soundR : forall E ss ss' ms,
  st_okP E ss ms -> sym_step_sh segs tbl ss = SRun ss' ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okP E ss' ms'
  /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms')
  /\ exists rep, step_accesses segs ms = MachineOk rep /\ access_value _ rep = ms'
     /\ accs_in_rrange E (ss_mem ss) (accessed_ranges _ rep).
Proof.
  intros E ss ss' ms HS H.
  destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hs.
  - assert (E1 : ss1 = ss') by (unfold sym_step_sh in H; rewrite Hs in H; congruence). subst ss1.
    exact (sym_step_soundR segs tbl Htbl P1 P5 E ss ss' ms HS Hs).
  - exfalso. unfold sym_step_sh in H. rewrite Hs in H. discriminate.
  - destruct (sym_step_sh_soundP segs tbl Htbl P1 P5 E ss ss' ms HS H) as (ms' & Hstep & HS' & Hfr).
    destruct (step_rep segs ms ms' Hstep) as (rep & Hrep & Hval).
    exists ms'. split; [exact Hstep|]. split; [exact HS'|]. split; [exact Hfr|].
    exists rep. split; [exact Hrep|]. split; [exact Hval|].
    exact (sym_step_sh_shadow_accs E ss ss' ms why rep HS Hs H Hrep).
Qed.
End e.
End d.
