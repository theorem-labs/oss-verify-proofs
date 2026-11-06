(* cgif's malloc contract at the trampoline of plugin-hostd/fuzz_command's ASan+UBSan image (fuzz_command.asan-ubsan;
   lib/Reusable/YG0d.v amalloc_realizes, pc_wrap_malloc = 0x589d0, window ASTACK) from the contract of the malloc
   interceptor's body (lib/B/Rt/RtDDefs.v amalloc_body_realizes at 0x58ba4, unwinder pc 0x58c6c, window MALLOC_IN_STK).
   __interceptor_trampoline_malloc 0x589d0 is one forward jump  j 0x58ba4  (lib/B/Rt/RtDMallocRun.v dm_run_j): no
   register and no byte changes. The trampoline's caller gives ASTACK = 16,384 bytes below sp; the body needs
   MALLOC_IN_STK = 14,208 of them and leaves the 2,176 bytes between present, because they are stack bytes
   outside its scratch window and the model's malloc_post puts the new block below the stack
   (lib/B/Rt/RtDMallocLeaf.v dm_leaf_widen). The caller's ly_bot < sp makes the body's trace the call trace.
   The proof is the one of lib/A/Rt/RtDMallocTramp.v (fuzz_command.asan) moved by the name-keyed A-to-B address map. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YN2j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG07 YG0k YFfk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDDefs RtDMallocRun RtDMallocLeaf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The jump leaves every register an atom. *)
Lemma dm_j_atoms : forallb (fun i : nat => sv_eqb (sr_get (ss_regs DM_J) (Z_to_bv 5 (Z.of_nat i))) (SOff i 0)) (seq 1 31) = true.
Proof. vm_compute. reflexivity. Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : CmdBSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem cmd_amalloc_of_body : amalloc_body_realizes tfibsegs B PC_malloc_body DM_PC0 -> amalloc_realizes tfibsegs B.
Proof.
intros BODY ly S W regs mem md n ch PRE Hn Hrange Hlive Htr.
rewrite (ts_code B TB) in Htr |- *. cbn [pc_malloc_ra0 pc_wrap_malloc Tfib_code] in Htr |- *.
pose proof PRE as (HAR & Hreg & Hret & Hal & Hslo & Hbot & Hshi & Hpres & Hgp & Htp & Hch & Hqm).
set (EE := YE2y.Env regs []).
assert (HS0 : st_ok tfibsegs EE DM_SJ (restrict (w_H W) (mkst regs (Z_to_bv 64 DM_TRAMP) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold DM_SJ, EE, YE2y.Env. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [exact I | split; exact I]. }
apply (amreal_SRr_pre tfibsegs _ W (cfg_at tfibsegs 0x589d0 regs mem md) _
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs EE DM_J (restrict (w_H W) ms1) /\
frame_of EE (ss_mem DM_SJ) (ms_mem (mkst regs (Z_to_bv 64 DM_TRAMP) mem (seg_rom tfibsegs))) (ms_mem ms1) /\
frame_of EE (ss_mem DM_SJ) (mrestrict (w_H W) (ms_mem (mkst regs (Z_to_bv 64 DM_TRAMP) mem (seg_rom tfibsegs))))
(mrestrict (w_H W) (ms_mem ms1)))).
{ exact (dm_phase W EE DM_SJ DM_J (mkst regs (Z_to_bv 64 DM_TRAMP) mem (seg_rom tfibsegs)) md DM_BODY HS0 dm_run_j). }
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF & _).
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (SBM : same_but_materialized md md1) by exact (with_vm_backing_same md mat1).
assert (Emem : ms_mem ms1 = mem).
{ apply functional_extensionality. intros x. exact (frame_of_nil EE mem (ms_mem ms1) x HF). }
assert (GA : forall x : bv 5, 1 <= bv_unsigned x -> getr (ms_regs ms1) x = getr regs x).
{ intros x Hx. rewrite (st_ok_reg_denot (w_H W) EE DM_J ms1 x HS1).
pose proof (bv_unsigned_in_range 5 x) as Rx. change (bv_modulus 5) with 32 in Rx.
assert (Hi : In (Z.to_nat (bv_unsigned x)) (seq 1 31)) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) dm_j_atoms _ Hi) as Hb. apply sv_eqb_eq in Hb.
rewrite Z2Nat.id in Hb by lia. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. cbn [sv_denot]. unfold EE.
rewrite (YE2y.Env_reg regs [] (Z.to_nat (bv_unsigned x)) x ltac:(rewrite Z2Nat.id by lia; reflexivity)).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
set (regs1 := ms_regs ms1) in *.
assert (G1 : getr regs1 1%bv = getr regs 1%bv) by (apply GA; vm_compute; discriminate).
assert (G2 : getr regs1 2%bv = getr regs 2%bv) by (apply GA; vm_compute; discriminate).
assert (G3 : getr regs1 3%bv = getr regs 3%bv) by (apply GA; vm_compute; discriminate).
assert (G4 : getr regs1 4%bv = getr regs 4%bv) by (apply GA; vm_compute; discriminate).
assert (G8 : getr regs1 8%bv = getr regs 8%bv) by (apply GA; vm_compute; discriminate).
assert (G10 : getr regs1 10%bv = getr regs 10%bv) by (apply GA; vm_compute; discriminate).
assert (SP : spZ regs1 = spZ regs) by (unfold spZ; rewrite G2; reflexivity).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EE DM_J ms1 HS1 eq_refl) as Hshape.
rewrite Hshape. change (ss_pc DM_J) with DM_BODY. fold regs1. rewrite Emem.
assert (ETR : inner_trace ly DM_PC0 regs1 ch = call_trace ly 0x58c6c regs ch).
{ unfold inner_trace. rewrite SP. destruct (Z.leb_spec (spZ regs) (ly_bot ly)) as [X|X]; [lia|].
unfold call_trace, frame0_ok, raZ, s0Z. rewrite SP, G1, G8. reflexivity. }
assert (HAR1 : AR tfibsegs B ly S W mem md1).
{ destruct (same_but_materialized_frame md md1 SBM) as (_ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3).
exact (al_frame _ _ LAWS ly S W mem md mem md1 HAR (fun _ _ _ => eq_refl) (fun _ H => H) V1 V2 V3 (fun _ _ _ => eq_refl)). }
assert (PRE1 : acall_pre_w tfibsegs B MALLOC_IN_STK ly S W regs1 mem md1 ch).
{ split; [exact HAR1|]. split; [exact Hreg|]. split; [rewrite G1; exact Hret|].
split; [rewrite SP; exact Hal|]. split; [rewrite SP; unfold MALLOC_IN_STK, ASTACK in *; lia|].
split; [rewrite SP; exact Hshi|]. split; [intros a Ha; rewrite SP in Ha; apply Hpres; unfold MALLOC_IN_STK, ASTACK in *; lia|].
split; [rewrite G3; exact Hgp|]. split; [rewrite G4; exact Htp|].
split; [|exact Hqm]. unfold chain_pre, frame0_ok, raZ, spZ, s0Z in Hch |- *. rewrite G1, G2, G8. exact Hch. }
assert (Htr1 : In (inner_trace ly DM_PC0 regs1 ch) (as_universe B) \/ st_nev S < EV_MAX) by (rewrite ETR; exact Htr).
pose proof (BODY ly S W regs1 mem md1 n ch PRE1 ltac:(rewrite G10; exact Hn) Hrange Hlive Htr1) as HB.
rewrite ETR in HB.
pose proof (dm_malloc_apost (as_universe B) S n (call_trace ly 0x58c6c regs ch)
(am_universe B ly S _ (proj1 HAR)) (am_wf B ly S _ (proj1 HAR)) Hreg Hrange Hlive (tr_admit_call _ _ _ _ _ _ Htr)) as HP.
pose proof (amreal_apost tfibsegs _ _ W _ _ HP HB) as HB2.
eapply amreal_mono; [|exact HB2].
intros r W' c' [HPr HQr].
exact (dm_leaf_widen B TB LAWS MALLOC_IN_STK ASTACK ly S W regs mem md n r W' c'
ltac:(unfold MALLOC_IN_STK, ASTACK; lia) HAR Hslo Hshi Hpres HPr
(dm_leaf_regs B MALLOC_IN_STK ly S W regs regs1 mem md md1 n r W' c' GA SBM HQr)).
Qed.

End t.
