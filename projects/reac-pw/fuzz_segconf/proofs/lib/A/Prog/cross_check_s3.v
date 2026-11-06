(* Segment 3 of the walk of cross_check on reac-pw/fuzz_segconf's ASan image A (fuzz_segconf.asan 0x89218): the
   epilogue, 0x89460 (CC_EPI = AF_cross_check + 0x248) to the return at 0x89498, in the form of
   plugin-hostd/fuzz_command's lib/A/Prog/check_reply_s8.v and numberR.v (origin/ossv/recipes 501c0d516c69): a
   symbolic state is seeded at the cut from INV_EPI, one plain run (PaLibF.v paj_run_sh) walks the 15
   instructions, and paj_ret_at gives the return configuration, whose post is apost_base lifted to apost_baseF by
   PaFx.v apost_baseF_of_base (the epilogue changes no FP state).

   The instructions walked (the unit's internal record, commit dfb49d6ad789,
   path records/segp/dis/cross_check.fuzz_segconf.asan.s lines 148-162), no branch, no call, no store and
   no inline check:
     0x89460 ld ra,0x78(sp)   0x89464 ld s0,0x70(sp)   0x89468 ld s1,0x68(sp)   0x8946c ld s2,0x60(sp)
     0x89470 ld s3,0x58(sp)   0x89474 ld s4,0x50(sp)   0x89478 ld s5,0x48(sp)   0x8947c ld s6,0x40(sp)
     0x89480 ld s7,0x38(sp)   0x89484 ld s8,0x30(sp)   0x89488 ld s9,0x28(sp)   0x8948c ld s10,0x20(sp)
     0x89490 ld s11,0x18(sp)  0x89494 addi sp,sp,0x80  0x89498 ret

   The seeded state: the registers are the cut's (atoms 0-31), atoms 32..44 are the entry's ra, s0, s1,
   s2..s11 (cc_saved, in slot order), and one READ-ONLY region on the sp atom, [0x18, 0x80), whose 13 chunks are
   the saved slots: slot j of cc_saved at sp + 0x78 - 8 j = sp0 - 8 - 8 j holds atom 32 + j (INV_EPI's
   fi_saved). The region has an empty write window, so the run writes nothing (awr_ok is vacuous and the
   memory at the return is the cut's). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaStep SegSyms
  SegList SegPa PaJournal SegPaLib PaLibG PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegObj SegPgBase SegABase PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c cross_check_c cross_check_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

(* the 13 saved slots as chunks on the sp atom (sp = sp0 - 128): slot j at offset 0x78 - 8 j holds atom 32 + j *)
Definition cc3_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (0x78 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13).
(* the frame's save area [sp + 0x18, sp + 0x80), read-only (empty write window) *)
Definition cc3_r : YP09.region := YP09.mkRegion (Some 2%nat) 0x18 0x80 0x18 0x18 cc3_chunks.
(* the state at 0x89460 *)
Definition ss_cc3 : sstate := mkSS CC_EPI sr_atoms [cc3_r] None (mkFacts [] [] []).
(* atoms 32..44: the entry's values of the registers the prologue saved, in slot order *)
Definition cc3_extra (regs0 : bvmap 5 word) : list word := map (fun r => getr regs0 (Z_to_bv 5 r)) cc_saved.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* atom 32 + j of the seeded environment is the entry's value of slot j's register *)
Lemma cc3_ew : forall (regs3 regs0 : bvmap 5 word) j r, nth_error cc_saved j = Some r ->
  ew (Eimg (Ereg regs3 (cc3_extra regs0))) (32 + j) = getr regs0 (Z_to_bv 5 r).
Proof.
intros regs3 regs0 j r Hr.
assert (Hj : (j < length cc_saved)%nat) by (apply nth_error_Some; rewrite Hr; discriminate).
cbn [length cc_saved] in Hj.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold cc3_extra.
apply nth_error_nth. rewrite nth_error_map, Hr. reflexivity.
Qed.

(* the seed: the machine state at 0x89460 satisfies ss_cc3, from INV_EPI's sp and saved slots *)
Lemma cc3_seed : forall (v : ccx) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte),
  getr regs3 2 = w64 (cc_sp0 v - 128) -> 128 <= cc_sp0 v <= 2 ^ 47 ->
  (forall j r, nth_error cc_saved j = Some r ->
    rdword (rdW W3 mem3) (cc_sp0 v - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs v) (Z_to_bv 5 r)))) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs3 (cc3_extra (x_regs v)))) ss_cc3
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_EPI)) mem3 (seg_rom SEGS))).
Proof.
intros v W3 regs3 mem3 HSP Hsp HSV.
assert (U2 : bv_unsigned (ew (Eimg (Ereg regs3 (cc3_extra (x_regs v)))) 2) = cc_sp0 v - 128).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), HSP.
  unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold ss_cc3. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, cc3_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. unfold cc3_chunks in Hc. apply in_map_iff in Hc.
  destruct Hc as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error cc_saved j) as [r|] eqn:Hr.
  2: { exfalso. apply nth_error_None in Hr. cbn [length cc_saved] in Hr. lia. }
  apply (chunk_ok_val SEGS _ _ _ _ 8%N _ (bv_unsigned (getr (x_regs v) (Z_to_bv 5 r)))).
  + cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. exact (cc3_ew regs3 (x_regs v) j r Hr).
  + change (8 * Z.of_N 8) with 64. apply u64_range.
  + lia.
  + replace (cc_sp0 v - 128 + (0x78 - 8 * Z.of_nat j)) with (cc_sp0 v - 8 - 8 * Z.of_nat j) by lia.
    exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ (HSV j r Hr)).
- exact (conj I I).
- exact (conj I (conj I I)).
Qed.

(* S3: the epilogue, the 13 reloads and the return. *)
Theorem cc_s3 : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z),
  PALib B -> PALibF B -> seg_val_objs -> seg_sig_prog ->
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md,
     AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  lit F_xmodel = VAL (A_OBJ 73) -> lit F_xbox = VAL (A_OBJ 74) -> 0 <= STK_REF ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  cc_S3P B lit gotw guard STK_REF.
Proof.
intros B lit gotw guard STK_REF TL TLF HVO HSG HRRO HSSP HLM HLB HSTK REF.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (paj_ret_at (PL := PL_seg) (PI := PI)) as RET.
intros v HP. unfold from_EPI, cc_from. intros ly3 S3 W3 regs3 mem3 md3 (HFI & HRC).
destruct HFI as [HJ HSP HGP HTP HSV HNA].
assert (HPRE : afn_pre SEGS B (cc_STK STK_REF) (x_ly v) (x_S v) (x_W v) (x_regs v) (x_mem v) (x_md v) (x_ch v))
  by (destruct HP; assumption).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold cc_STK in Hslo.
assert (Hsp : 128 <= cc_sp0 v <= 2 ^ 47) by (unfold cc_sp0; lia).
pose proof (cc3_seed v W3 regs3 mem3 HSP Hsp HSV) as HS.
remember (Eimg (Ereg regs3 (cc3_extra (x_regs v)))) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r).
{ intros n r Hn. pose proof (u5_range r). rewrite HE, Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j (r : bv 5), nth_error cc_saved j = Some (bv_unsigned r) -> ew E (32 + j) = getr (x_regs v) r).
{ intros j r Hr. rewrite HE, (cc3_ew regs3 (x_regs v) j _ Hr), Z_to_bv_bv_unsigned. reflexivity. }
assert (U2 : bv_unsigned (ew E 2) = cc_sp0 v - 128).
{ rewrite (EE 2%nat 2%bv eq_refl), HSP. unfold w64. apply unsigned_lit_small. lia. }
change (cfg_at SEGS (BASE + CC_EPI) regs3 mem3 md3)
  with (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + CC_EPI)) mem3 (seg_rom SEGS)) md3).
paj_run_sh RUNP HS HJ.
- (* the save area is read-only: the run writes no byte *)
  intros a (r & Hr & Ha). unfold ss_cc3 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
  unfold cc3_r in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia.
- (* the return *)
  assert (Hmem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
    intros (r & Hr & Ha). unfold ss_cc3 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
    unfold cc3_r in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
  prreg HS (1%bv : bv 5) Q1.
  assert (X0 : ew E 32 = getr (x_regs v) (1%bv : bv 5)) by exact (EX 0%nat (1%bv : bv 5) eq_refl).
  eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cc_post. apply (apost_baseF_of_base SEGS). unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
  split; [rewrite Q1, X0; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split.
  + apply aregs_preserved_eqs.
    all: lazymatch goal with |- getr _ ?rr = getr _ _ => let Rq := fresh "Rq" in prreg HS rr Rq; rewrite Rq; clear Rq end.
    1: { rewrite U2. replace (cc_sp0 v - 128 + 128) with (cc_sp0 v) by lia. unfold cc_sp0, spZ.
         apply Z_to_bv_bv_unsigned. }
    1: { rewrite (EE 3%nat 3%bv eq_refl), HGP, Hgp. reflexivity. }
    1: { rewrite (EE 4%nat 4%bv eq_refl), HTP, Htp. reflexivity. }
    all: lazymatch goal with |- ew _ ?n = getr _ ?rr =>
      let j := eval compute in (n - 32)%nat in exact (EX j rr eq_refl) end.
  + unfold cc_Q. cbv beta. rewrite Hmem. split; [exact HRC | exact HNA].
Qed.
End f.
End d.
