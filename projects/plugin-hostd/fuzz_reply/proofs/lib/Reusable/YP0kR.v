(* CARRIED from commit d692856bfecbb98b2d89a0bba73b457c2098f96d,
   proofs/cgif/cgif_file_fuzzer/lib/YP0kR.v, sha256 fc6ebde5082ae1d3e82934de306900e12bd98b3db44b6a5bcf1d4f9a606bfde9 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP00 YP0k YP09R.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis Htbl : table_ok segs tbl.

Lemma accs_in_rrange_nil : forall E rs, accs_in_rrange E rs [].
Proof. intros E rs a n k []. Qed.

Lemma accs_in_rrange_hit : forall E m rs r off (n : nat),
  mem_ok segs E m rs -> In r rs -> r_lo r <= off -> off + Z.of_nat n <= r_hi r ->
  accs_in_rrange E rs [(Z_to_bv 64 (base_val E (r_base r) + off), n)].
Proof.
intros E m rs r off n (_ & Hok & _) Hin Hlo Hhi a n' k [Heq|[]] Hk.
injection Heq as <- <-.
rewrite Forall_forall in Hok. destruct (Hok r Hin) as (H0 & H1 & _).
exists r. split; [exact Hin|].
assert (Hw : bv_wrap 64 (base_val E (r_base r) + off) = base_val E (r_base r) + off).
{ apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
rewrite Z_to_bv_unsigned, Hw. lia.
Qed.

Lemma sload_region : forall G rs b off sz sg v,
  sload segs G rs b off sz sg = Some v ->
  exists r, In r rs /\ r_base r = b /\ r_lo r <= off /\ off + Z.of_nat (nbytes sz) <= r_hi r.
Proof.
intros G rs b off sz sg v H. unfold sload in H.
destruct (find_region rs b off (Z.of_nat (nbytes sz))) as [r|] eqn:Hf; [|discriminate].
exists r. exact (find_region_sound _ _ _ _ _ Hf).
Qed.

Lemma sstore_region : forall rs b off sz v rs',
  sstore rs b off sz v = Some rs' ->
  exists r, In r rs /\ r_base r = b /\ r_lo r <= off /\ off + Z.of_nat (nbytes sz) <= r_hi r.
Proof.
intros rs b off sz v rs' H. unfold sstore in H.
apply store_region_shape in H as (l1 & r & l2 & -> & _ & Hb & Hlo & Hhi & _).
exists r. split; [apply in_app_iff; right; left; reflexivity|]. auto.
Qed.

Section g.
Variable P1 : env -> list sv -> bvmap 5 word -> Prop.
Variable P5 : list sv -> bv 32 -> Prop.
Local Notation st_okP := (st_okP segs P1 P5).

Ltac nil_arm Hsa := injection Hsa as <-; cbn [accessed_ranges]; apply accs_in_rrange_nil.

Lemma sym_step_accs : forall E ss ss' ms rep,
  st_okP E ss ms -> sym_step segs tbl ss = SRun ss' ->
  step_accesses segs ms = MachineOk rep ->
  accs_in_rrange E (ss_mem ss) (accessed_ranges _ rep).
Proof.
intros E ss ss' ms rep HS H Hsa.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
subst pcv pend rom.
unfold sym_step in H.
destruct (clookup tbl (ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate].
pose proof (Htbl (ss_pc ss) wz Hlk) as Hf. cbv zeta in H.
unfold step_accesses, ms_pc in Hsa. cbn [ms_pc_val ms_mem] in Hsa. rewrite Hf in Hsa.
unfold decode_exec_accesses in Hsa.
destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec; [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hd; [|discriminate].
destruct (isz =? 4) eqn:Hsz; cbn [negb] in H; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom] in Hsa.
assert (HR : forall r, rget (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) r
= sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
destruct i; try discriminate;
cbv beta iota zeta delta
[interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv] in Hsa;
cbn [access_value accessed_ranges] in Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
  destruct (addr_of a) as [[b off]|] eqn:Hao; [|discriminate].
  destruct (sload segs (ss_facts ss) (ss_mem ss) b off sz signed) as [v|] eqn:Hsl; [|discriminate].
  destruct (sload_region _ _ _ _ _ _ _ Hsl) as (r & Hin & Hrb & Hlo & Hhi).
  assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
  { rewrite <- (addr_of_sound E (ss_facts ss) a b off HG Hao). subst a.
    rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
  rewrite ?HR, Haddr in Hsa. subst b.
  destruct sz; cbn [nbytes Z.of_nat] in Hhi;
  cbv beta iota zeta delta [interp_eff_accesses RiscvSemantics.width_bytes] in Hsa;
  (destruct (ov_read_bytes segs mem (Z_to_bv 64 (base_val E (r_base r) + off)) _) as [bs|]; [|discriminate]);
  cbn [access_value accessed_ranges] in Hsa; injection Hsa as <-; cbn [accessed_ranges];
  (eapply accs_in_rrange_hit; [exact Hmem | exact Hin | exact Hlo | cbn; lia]).
- destruct (ss_resv ss) as [rv0|] eqn:Hrv; [discriminate|]. cbn in Hresv. subst resv.
  remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
  destruct (addr_of a) as [[b off]|] eqn:Hao; [|discriminate].
  destruct (sstore (ss_mem ss) b off sz (sr_get (ss_regs ss) rs2)) as [m'|] eqn:Hst; [|discriminate].
  destruct (sstore_region _ _ _ _ _ _ Hst) as (r & Hin & Hrb & Hlo & Hhi).
  assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
  { rewrite <- (addr_of_sound E (ss_facts ss) a b off HG Hao). subst a.
    rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
  rewrite ?HR, Haddr in Hsa. subst b.
  destruct sz; cbn [nbytes Z.of_nat] in Hhi;
  cbv beta iota zeta delta [interp_eff_accesses RiscvSemantics.width_bytes] in Hsa;
  (destruct (store_ok segs mem (Z_to_bv 64 (base_val E (r_base r) + off)) _); [|discriminate]);
  cbn [access_value accessed_ranges] in Hsa; injection Hsa as <-; cbn [accessed_ranges];
  (eapply accs_in_rrange_hit; [exact Hmem | exact Hin | exact Hlo | cbn; lia]).
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- nil_arm Hsa.
- destruct (aligned_dec (ss_facts ss) (sr_get (ss_regs ss) rs1) (amo_bytes_of w)) eqn:Hal;
  cbn [negb] in H; [|discriminate].
  destruct (addr_of (sr_get (ss_regs ss) rs1)) as [[b off]|] eqn:Hao; [|discriminate].
  destruct (sload segs (ss_facts ss) (ss_mem ss) b off (amo_sz w) true) as [v|] eqn:Hsl; [|discriminate].
  destruct (sload_region _ _ _ _ _ _ _ Hsl) as (r & Hin & Hrb & Hlo & Hhi).
  pose proof (addr_of_sound E (ss_facts ss) _ b off HG Hao) as Haddr.
  assert (Hamo : amo_aligned w (sv_denot E (sr_get (ss_regs ss) rs1)) = true).
  { unfold amo_aligned. apply Z.eqb_eq.
    apply (aligned_dec_sound P1 E (ss_facts ss)); [exact HG| destruct w; cbn; lia |].
    destruct w; exact Hal. }
  rewrite ?HR in Hsa. rewrite Hamo in Hsa. cbn [negb] in Hsa. rewrite Haddr in Hsa. subst b.
  destruct w; cbn [amo_sz nbytes Z.of_nat] in Hhi;
  cbv beta iota zeta delta [interp_eff_accesses RiscvSemantics.width_bytes] in Hsa;
  (destruct (ov_read_bytes segs mem (Z_to_bv 64 (base_val E (r_base r) + off)) _) as [bs|]; [|discriminate]);
  cbn [access_value accessed_ranges] in Hsa; injection Hsa as <-; cbn [accessed_ranges];
  (eapply accs_in_rrange_hit; [exact Hmem | exact Hin | exact Hlo | cbn; lia]).
- destruct (aligned_dec (ss_facts ss) (sr_get (ss_regs ss) rs1) (amo_bytes_of w)) eqn:Hal;
  cbn [negb] in H; [|discriminate].
  assert (Hamo : amo_aligned w (sv_denot E (sr_get (ss_regs ss) rs1)) = true).
  { unfold amo_aligned. apply Z.eqb_eq.
    apply (aligned_dec_sound P1 E (ss_facts ss)); [exact HG| destruct w; cbn; lia |].
    destruct w; exact Hal. }
  rewrite ?HR in Hsa. rewrite Hamo in Hsa. cbn [negb] in Hsa.
  destruct (ss_resv ss) as [a'|] eqn:Hrv; cbn in Hresv; subst resv.
  + destruct (sv_eqb a' (sr_get (ss_regs ss) rs1)) eqn:Heq; cbn [negb] in H; [|discriminate].
    apply sv_eqb_eq in Heq. subst a'.
    destruct (addr_of (sr_get (ss_regs ss) rs1)) as [[b off]|] eqn:Hao; [|discriminate].
    destruct (sstore (ss_mem ss) b off (amo_sz w) (sr_get (ss_regs ss) rs2)) as [m'|] eqn:Hst; [|discriminate].
    destruct (sstore_region _ _ _ _ _ _ Hst) as (r & Hin & Hrb & Hlo & Hhi).
    pose proof (addr_of_sound E (ss_facts ss) _ b off HG Hao) as Haddr.
    rewrite Z.eqb_refl in Hsa. rewrite Haddr in Hsa. subst b.
    destruct w; cbn [amo_sz nbytes Z.of_nat] in Hhi;
    cbv beta iota zeta delta [interp_eff_accesses RiscvSemantics.width_bytes] in Hsa;
    (destruct (store_ok segs mem (Z_to_bv 64 (base_val E (r_base r) + off)) _); [|discriminate]);
    cbn [access_value accessed_ranges] in Hsa; injection Hsa as <-; cbn [accessed_ranges];
    (eapply accs_in_rrange_hit; [exact Hmem | exact Hin | exact Hlo | cbn; lia]).
  + nil_arm Hsa.
Qed.

Theorem sym_step_soundR : forall E ss ss' ms,
  st_okP E ss ms -> sym_step segs tbl ss = SRun ss' ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okP E ss' ms'
  /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms')
  /\ exists rep, step_accesses segs ms = MachineOk rep /\ access_value _ rep = ms'
     /\ accs_in_rrange E (ss_mem ss) (accessed_ranges _ rep).
Proof.
intros E ss ss' ms HS H.
destruct (sym_step_soundP segs tbl Htbl P1 P5 E ss ss' ms HS H) as (ms' & Hst & Hok & Hfr).
exists ms'. split; [exact Hst|]. split; [exact Hok|]. split; [exact Hfr|].
unfold RiscvSemantics.step, drop_access_report in Hst.
destruct (step_accesses segs ms) as [rep| |] eqn:Hsa; try discriminate.
injection Hst as Hv. exists rep. split; [reflexivity|]. split; [exact Hv|].
exact (sym_step_accs E ss ss' ms rep HS H Hsa).
Qed.

End g.
End d.
