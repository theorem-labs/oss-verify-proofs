(* libreac/fuzz_decode image B (fuzz_decode.asan-ubsan): proofs of three premise rows of the closing composition
   lib/B/DecodeBClose.v, the small runtime entries the calloc interceptor calls before the allocator.  Each lemma has
   the type of the DecodeBClose.v hypothesis it names:

     dec_b_rt_try   : H_CALLOC_RT_TRY    __asan::TryAsanInitFromRtl at 0x590f8 (13 instructions on the inited path)
     dec_b_rt_mcs   : H_CALLOC_RT_MCS    __asan::GetMallocContextSize at 0x59e80 (4 instructions)
     dec_b_rt_getpc : H_CALLOC_RT_GETPC  __sanitizer::StackTrace::GetCurrentPc at 0x72a54 (2 instructions)

   Released-proof lookup (rule 24): no released contract for any of the three (provenance/ALLOC-B-ROWS.md), so each
   is stepped here over coreB's own runtime table.  No Axiom, Parameter or Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCallocRt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v YB1q YF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
(* ===================================================================================================== *)
(* Rows H_CALLOC_RT_TRY / H_CALLOC_RT_MCS / H_CALLOC_RT_GETPC (DecodeBClose.v:250-252).  Each function is run from
   its entry to its `ret` by the symbolic run over coreB's runtime table lib/B/YB1q.v tfibtbl_rtA (which holds
   0x590f8 / 40, 0x59e80 and 0x72a54 / 90 instructions), then returned with SRr_ret_at, in the form of coreB's
   runtime leaves (lib/B/YFfg.v ialloc_inited).  The calloc wrapper walk is not changed. *)

(* StackTrace::GetCurrentPc, 0x72a54 `mv a0, ra`, 0x72a58 `ret`: no region, no fact. *)
Definition SS_GPC : sstate := mkSS DEC_B_GetCurrentPc sr_atoms [] None (mkFacts [] [] []).

Lemma dec_b_rt_getpc : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_getpc_spec_B.
Proof.
intros fx rc. unfold decode_getpc_spec_B, getpc_specP. change decodesegsB0 with tfibsegs.
intros W regs mem md Hra. pose proof Hwx_tfa as Hwx.
set (E0 := Ereg regs []).
assert (E1 : ew E0 1 = getr regs 1) by (exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (HS : st_ok tfibsegs E0 SS_GPC
  (restrict (w_H W) (mkst regs (Z_to_bv 64 DEC_B_GetCurrentPc) mem (seg_rom tfibsegs)))).
{ unfold SS_GPC. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [|split; exact I]. exact I. }
srr_run_to_sh tfibtbl_rtA_ok HS 0x72a58.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { apply (regs_preserved_of_st_ok tfibsegs E0 _ _ regs [] HS); [apply env_agree_refl | vm_compute; reflexivity]. }
split. { rreg HS (10%bv : bv 5) R10. rewrite R10, E1. reflexivity. }
intros x. apply (frame_of_outside E0 _ _ _ x HF). intros r Hr. cbn [ss_mem SS_GPC In] in Hr. destruct Hr.
Qed.

(* __asan::GetMallocContextSize, 0x59e80 `auipc a0`, 0x59e84 `lw a0` (the 4-byte cell 0xa203c), 0x59e88 `fence`,
   0x59e8c `ret`.  The cell holds the fresh atom 32 = v, with the fact 0 <= v < 2 ^ 31, from which the symbolic
   run takes the sign-extended load as the atom itself (a0 = SOff 32 0). *)
Definition aMCS : nat := 32.
Definition rMCS : YP09.region := YP09.mkRegion None DEC_B_malloc_context_size (DEC_B_malloc_context_size + 4) 0 0
  [YP09.mkChunk DEC_B_malloc_context_size (CVal 4 (SOff aMCS 0))].
Definition SS_MCS : sstate :=
  mkSS DEC_B_GetMallocContextSize sr_atoms [rMCS] None (mkFacts [(aMCS, mkAF 0 (2 ^ 31 - 1) 0)] [] []).

Lemma dec_b_rt_mcs : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_mcs_spec_B.
Proof.
intros fx rc. unfold decode_mcs_spec_B, mcs_specP. change decodesegsB0 with tfibsegs.
intros W regs mem md v. cbv zeta. intros Hra HV Hv. pose proof Hwx_tfa as Hwx.
set (E0 := Ereg regs [Z_to_bv 64 v]).
assert (E1 : ew E0 1 = getr regs 1) by (exact (ew_Ereg_nat regs [Z_to_bv 64 v] 1 1%bv eq_refl)).
assert (E32 : ew E0 aMCS = Z_to_bv 64 v) by reflexivity.
assert (HS : st_ok tfibsegs E0 SS_MCS
  (restrict (w_H W) (mkst regs (Z_to_bv 64 DEC_B_GetMallocContextSize) mem (seg_rom tfibsegs)))).
{ unfold SS_MCS. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - cbn [ms_mem mkst]. unfold rMCS. apply Forall_cons; [|apply Forall_nil].
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold DEC_B_malloc_context_size. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    eapply (chunk_ok_val tfibsegs E0 _ _ _ _ _ v);
      [cbn [sv_denot]; rewrite E32, (unsigned_lit_small v), Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia
      | rewrite Z.add_0_l; exact HV].
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    repeat match goal with |- context [ew ?E ?n] => change (ew E n) with (Z_to_bv 64 v) end.
    rewrite (unsigned_lit_small v) by lia. repeat split; first [lia | apply Z.mod_1_r]. }
srr_run_to_sh tfibtbl_rtA_ok HS 0x59e8c.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { apply (regs_preserved_of_st_ok tfibsegs E0 _ _ regs [Z_to_bv 64 v] HS);
  [apply env_agree_refl | vm_compute; reflexivity]. }
split.
{ pose proof (st_ok_restrict_reg tfibsegs (w_H W) E0 _ _ (10%bv : bv 5) HS) as R10.
  lazymatch type of R10 with _ = sv_denot _ (sr_get ?sr _) =>
    let t := eval vm_compute in (sr_get sr (10%bv : bv 5)) in change (sr_get sr (10%bv : bv 5)) with t in R10 end.
  cbn [ms_regs restrict mkst] in R10. rewrite R10. cbn [sv_denot]. change (ew E0 32) with (Z_to_bv 64 v).
  rewrite (unsigned_lit_small v), Z.add_0_r by lia. reflexivity. }
intros x. apply (frame_of_outside E0 _ _ _ x HF). intros r Hr. cbn [ss_mem SS_MCS In] in Hr.
destruct Hr as [<-|[]]. left. unfold rMCS. cbn. lia.
Qed.

(* __asan::TryAsanInitFromRtl with the runtime up: 0x590f8 `addi sp, sp, -16`, `sd ra, 8(sp)`, `sd s0, 0(sp)`,
   0x59104 / 0x59108 s0 = 0xa2018, `lb a1, 0(s0)` (= 1), `addi a0, zero, 1`, `fence`, 0x59118 `bne a1, a0` (not
   taken), `ld ra`, `ld s0`, `addi sp, sp, 16`, 0x59128 `ret`.  The stack window [sp - 16, sp) is above the image
   (the contract's IMG_TOP premise), so writable; the init byte is a read-only literal region. *)
Definition rTAI_STK : YP09.region := YP09.mkRegion (Some 2%nat) (- TAI_STK) 0 (- TAI_STK) 0 [].
Definition rTAI_INIT : YP09.region := YP09.mkRegion None DEC_B_asan_inited (DEC_B_asan_inited + 1) 0 0
  [YP09.mkChunk DEC_B_asan_inited (CVal 1 (SLit 1))].
Definition SS_TAI : sstate :=
  mkSS DEC_B_TryAsanInitFromRtl sr_atoms [rTAI_STK; rTAI_INIT] None
    (mkFacts [(2%nat, mkAF (TFIB_IMG_END + TAI_STK) (2 ^ 64 - 1) 4)] [] []).

Lemma dec_b_rt_try : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_try_init_spec_B.
Proof.
intros fx rc. unfold decode_try_init_spec_B, try_init_specP. change decodesegsB0 with tfibsegs.
intros W regs mem md. cbv zeta. intros Hra Hal Hsp HPRES HINIT. pose proof Hwx_tfa as Hwx.
rewrite YImgTop.IMG_TOP_val in Hsp.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
set (E0 := Ereg regs []).
assert (E2 : ew E0 2 = getr regs 2) by (exact (ew_Ereg_nat regs [] 2 2%bv eq_refl)).
assert (E1 : ew E0 1 = getr regs 1) by (exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (HS : st_ok tfibsegs E0 SS_TAI
  (restrict (w_H W) (mkst regs (Z_to_bv 64 DEC_B_TryAsanInitFromRtl) mem (seg_rom tfibsegs)))).
{ unfold SS_TAI. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - cbn [ms_mem mkst]. unfold rTAI_STK, rTAI_INIT. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (region_ok_stack tfibsegs E0 _ 2 sp (- TAI_STK)); [rewrite E2; reflexivity | unfold TAI_STK in *; lia | lia |].
      intros a Ha. apply apresent_writable; [unfold TAI_STK, TFIB_IMG_END in *; lia | apply HPRES; exact Ha].
    + unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold DEC_B_asan_inited. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact HINIT].
  - apply pairwise_disjoint_of_extents. unfold rTAI_STK, rTAI_INIT, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). fold sp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TAI_STK, TFIB_IMG_END, DEC_B_asan_inited in *. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl). fold sp.
    unfold TAI_STK, TFIB_IMG_END in *. repeat split; first [lia | change (2 ^ 4) with 16; exact Hal]. }
srr_run_to_sh tfibtbl_rtA_ok HS 0x59128.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
assert (FR : forall x : word, ~ (sp - TAI_STK <= bv_unsigned x < sp) -> ms_mem msR x = mem x).
{ intros x Hx. apply (frame_of_outside E0 _ _ _ x HF). intros r Hr. cbn [ss_mem SS_TAI In] in Hr.
  destruct Hr as [<-|[<-|[]]]; unfold rTAI_STK, rTAI_INIT; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
    [right; rewrite E2; fold sp; clear - Hx; lia | left; lia]. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { apply (regs_preserved_of_st_ok tfibsegs E0 _ _ regs [] HS); [apply env_agree_refl | vm_compute; reflexivity]. }
split. { rreg HS (10%bv : bv 5) R10. rewrite R10. reflexivity. }
split. { intros x Hx. apply FR. exact Hx. }
intros a HP. set (x := Z_to_bv 64 a) in *.
assert (D : (sp - TAI_STK <= bv_unsigned x < sp) \/ ~ (sp - TAI_STK <= bv_unsigned x < sp)) by lia.
destruct D as [D|D].
- pose proof (u64_range x) as Ux.
  assert (P : apresent (w_H W) (ms_mem msR) (bv_unsigned x)).
  { eapply (st_ok_window_apresent (w_H W) E0 _ _ 0 _ _ HS); [reflexivity
    | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite E2; fold sp; clear - D; unfold TAI_STK in *; lia
    | unfold TAI_STK, TFIB_IMG_END in *; lia]. }
  unfold apresent in P |- *. rewrite Z_to_bv_bv_unsigned in P. exact P.
- apply (apresent_same (w_H W) mem); [apply FR; exact D | exact HP].
Qed.
