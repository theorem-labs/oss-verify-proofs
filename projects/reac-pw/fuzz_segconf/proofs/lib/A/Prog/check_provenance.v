(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of check_reply_answer (plugin-hostd/fuzz_command, 0x88450, 75 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close, a caller with calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer.v, with its module paths and module names changed; 954 of its 1064 lines of code are new or changed and 503 lines of the source are left out. *)
(* The ASan walk of check_provenance (fuzz_segconf image A, BASE + AF_check_provenance = 0x872e0, 58 instructions)
   against check_provenance_contract (lib/A/Prog/check_provenance_c.v), in the form of plugin-hostd/fuzz_command's
   lib/A/Prog/check_reply_answer.v at origin/ossv/recipes 501c0d516c69: one symbolic run per straight piece over
   the position-abstract listing (lib/A/Prog/SegList.v), the two instrumented checks removed by tok_load with the
   contract's sa_addr on want's mseg entry, the strcmp wrapper through its lib/A/Rt contract (a Section
   hypothesis), every branch to the no-return hook and abort refuted from the contract's two same_text conjuncts.
   The kit (call rule, entry state, byte bridges) is check_provenance_lem.v. Control flow: the plain walk
   lib/Prog/check_provenance.v at the plain / UBSan integration commit 440d61eaa8c8.

   Nine paths: the role_file test (want + 0x14 / want + 0x3c) leaves three (flag clear and the answer NULL; flag
   set and the answer the field's own address; flag set and strcmp(rf, want + 0x3c) = 0), and from each the
   ignore_file test (want + 0x1c / want + 0x9c) leaves the same three. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib SegObj SegGlob PaDenot PaSB PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase PaArt PaNoChain
  check_provenance_c check_provenance_lem SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* carry every atom fact ew Eo n = v (n below the bound of HAG) to the new valuation En (fuzz_command
   check_reply_answer.v cra_carry) *)
Ltac cpv_carry Eo En HAG :=
  repeat match goal with
  | H : ew Eo ?nn = ?v |- _ =>
      let H2 := fresh "Hc" in
      assert (H2 : ew En nn = v) by (rewrite HAG by lia; exact H);
      clear H; rename H2 into H
  end.
(* after a run (fresh atoms from 1024 on) or a call (CLOB values from atom k on), name the valuation of HS and
   carry the atom facts below bound and the agreement HAE with the entry registers (cra_reenv) *)
Ltac cpv_reenv HAE bound :=
  let Eo := lazymatch type of HAE with env_agree 32 _ ?Eo => Eo end in
  let En := lazymatch goal with
    | HS : st_ok_pi _ _ ?En _ _ |- _ => En
    | HS : st_ok _ ?En _ _ |- _ => En end in
  tryif constr_eq En Eo then idtac else (
    let HAG := fresh "HAG" in
    assert (HAG : forall nn, (nn < bound)%nat -> ew En nn = ew Eo nn)
      by (intros nn Hnn; cbn [extK]; first [apply ew_havoc_old; lia | rewrite ?ew_ewset_other by lia; reflexivity]);
    let HAE2 := fresh "HAE" in
    lazymatch type of HAE with env_agree 32 ?E0 Eo =>
      assert (HAE2 : env_agree 32 E0 En)
        by (split; [intros nn Hnn; rewrite HAG by lia; apply (proj1 HAE); exact Hnn | exact (proj2 HAE)]) end;
    clear HAE; rename HAE2 into HAE;
    let Ex := fresh "E" in
    set (Ex := En) in *;
    cpv_carry Eo Ex HAG;
    clear HAG; clearbody Ex).
(* what a run of this walk keeps: every byte outside its own frame [sp - 32, sp) (cra_kept) *)
Ltac cpv_kept sg spv E2 UN :=
  lazymatch goal with HFr : frame_of ?Ef _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  let Hu := fresh "Hu" in
  assert (Hu : bv_unsigned (ew Ef 2) = spv) by (rewrite E2; reflexivity);
  pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun a => spv - 32 <= a < spv) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Hu in Hrr; lia|]);
          destruct Hin)) as UN;
  clear Hu end.
(* the shadow base of the current valuation (atom 32) *)
Ltac cpv_ub E32 H :=
  lazymatch type of E32 with ew ?Ex 32 = _ =>
    assert (H : U Ex Bxp = SHADOW_OFF)
      by (unfold Bxp; rewrite (U_atom Ex 32 SB E32) by (unfold SB; lia); reflexivity) end.
(* the branch condition the last psrr_branch_tok left, under a fixed name *)
Ltac cpv_cond H := lazymatch goal with Hx : branch_taken _ _ _ = _ |- _ => rename Hx into H end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
(* the strcmp wrapper, as the contract's head comment names it (the interceptor layer's interface row 17), at every FP state;
   the walk takes it at fx, the state this call runs in *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Theorem check_provenance_walk :
  check_provenance_contract SEGS B (BASE + AF_check_provenance) STK_check_provenance RLO_A RHI_A.
Proof using LAWS TL ASTRCMP RUN BR RET.
pose proof (cpv_call_strcmp_of B RLO_A RHI_A LAWS TL (ASTRCMP fx)) as CSTRCMP.
unfold check_provenance_contract, check_provenance_pre.
intros ly S W regs mem md ch rf igf want orf oif g HPRE0 HRO H10 Hrf64 H11 Higf64 H12 Hw64
  (Hw4 & (bs & BS & ENC) & HWH & HWA & OS1 & OA1 & OS2 & OA2 & SAME1 & SAME2) HEV.
pose proof (afn_pre_na_of SEGS B _ _ _ _ _ _ _ _ HPRE0) as HPRE. clear HPRE0.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
assert (HSTK : STK_check_provenance = 8224) by reflexivity.
(* want's heap block: the entry lies below the allocator ceiling, so below the stack window of this call *)
destruct HWH as (wb & wm & Hwin & Hwb & Hwm).
destruct (al_blocks _ _ LAWS ly S W mem md wb wm HAR Hwin) as (_ & Hwb4096 & Hwbc & _).
pose proof (blk_off_imgP B ly S W mem md wb wm HAR Hwin) as Hwoff. unfold off_img in Hwoff.
assert (Hrqw : wm <= req_size wm) by (unfold req_size; destruct (Z.eqb_spec wm 0); lia).
unfold seg_spec.MSEG_SIZE in *.
assert (Hwlo : 4096 <= want) by lia.
assert (Hwceil : want + 256 <= alloc_ceiling) by lia.
(* the two flag words of the entry (mseg_enc's flag_enc at 0x14 and 0x1c) and its two text fields *)
pose proof ENC as (LEN & _ & _ & FR & _ & FI & _ & _ & CRF & CIF & _).
pose proof (cpv_flag_val (rdW W mem) want bs seg_spec.MS_ROLE_SET (ms_role_set g) BS
  ltac:(unfold seg_spec.MS_ROLE_SET; lia) ltac:(rewrite LEN; unfold seg_spec.MS_ROLE_SET; cbn; lia) FR) as VR.
pose proof (cpv_flag_val (rdW W mem) want bs seg_spec.MS_IGNORE_SET (ms_ignore_set g) BS
  ltac:(unfold seg_spec.MS_IGNORE_SET; lia) ltac:(rewrite LEN; unfold seg_spec.MS_IGNORE_SET; cbn; lia) FI) as VI.
unfold seg_spec.MS_ROLE_SET, seg_spec.MS_IGNORE_SET in VR, VI.
remember (if ms_role_set g then 1 else 0) as rs eqn:Ers.
remember (if ms_ignore_set g then 1 else 0) as is eqn:Eis.
assert (Rrs : 0 <= rs <= 1) by (rewrite Ers; destruct (ms_role_set g); lia).
assert (Ris : 0 <= is <= 1) by (rewrite Eis; destruct (ms_ignore_set g); lia).
destruct (cpv_entry B LAWS TL W ly S regs mem md want rs is HPRE H12 ltac:(lia) ltac:(lia) Hw4
  ltac:(destruct Hwoff as [Hoff|Hoff]; [left; lia | right; lia]) VR Rrs VI Ris) as [HS SHOK].
pose proof (ajournal_init_na SEGS B STK_check_provenance [] ly S W regs mem md HPRE) as HJ.
remember (Eimg (Ereg regs (cpv_extra rs is))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
by (intros k r Hk; subst E; rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia);
    apply ew_Ereg_nat; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (apply EE; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EE; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EE; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 rf) by (transitivity (getr regs 10); [apply EE; reflexivity | exact H10]).
assert (E11 : ew E 11 = Z_to_bv 64 igf) by (transitivity (getr regs 11); [apply EE; reflexivity | exact H11]).
assert (E12 : ew E 12 = Z_to_bv 64 want) by (transitivity (getr regs 12); [apply EE; reflexivity | exact H12]).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 rs) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 is) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (cpv_extra rs is)) E)
by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE EE.
set (sp0 := spZ regs) in *.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (HL : SHADOW_OFF + 2 ^ 44 + 8 <= sp0 - STK_check_provenance) by (unfold SHADOW_OFF; lia).
assert (HCL : alloc_ceiling <= sp0 - STK_check_provenance) by lia.
assert (HL8 : (sp0 - STK_check_provenance) mod 8 = 0).
{ rewrite HSTK. pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd. rewrite Hal16, Z.add_0_r in Hd.
  rewrite Hd. replace (16 * (sp0 / 16) - 8224) with ((2 * (sp0 / 16) - 1028) * 8) by lia.
  apply Z.mod_mul. lia. }
(* every read-only byte the strcmp row reads lies below the window of this call *)
assert (HROL : forall a, in_roP SEGS RLO_A RHI_A a -> 0 <= a < sp0 - STK_check_provenance).
{ intros a [(sg & Hsg & _ & Hr) | Hr].
  - pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as Ha. unfold kLowMemEnd in Ha. lia.
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
cpv_ub E32 UB.
unfold cfg_at. change (w64 (BASE + AF_check_provenance)) with (Z_to_bv 64 (BASE + AF_check_provenance)).
(* 0x872e0 .. 0x87330: the frame, the shadow base through the GOT word, check 1 (want + 0x14, removed by the
   contract's sa_addr on the entry), the flag word role_set, the mask want + 0x3c or 0, then beq a0,a3 *)
paj_run_tok RUN HS HJ SHOK CPspan.
{ cbn [ms_mem mkst]. rewrite (U_atom_off E 12 want 20 E12) by lia.
  apply (obl_of_block SEGS B LAWS ly S W mem md E Bxp _ 4 wb wm HAR Hwin UB); lia. }
{ awr_ok_tac. exact Usp. }
cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN0.
clear HF HFr HG UB.
cpv_reenv HAE 1024%nat.
assert (KEPT0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
  rdW W (ms_mem ms) a = rdW W mem a) by (intros a Ha Hn; apply UN0; lia).
assert (AG0 : cpv_agree (rdW W mem) (rdW W (ms_mem ms)) (sp0 - STK_check_provenance))
  by (intros a Ha; apply KEPT0; lia).
clear UN0.
destruct (ms_role_set g) eqn:ER; try rewrite ER in Ers; try rewrite ER in SAME1; cbn in Ers; subst rs.
{
  (* role_set = 1: the role_file answer is a text equal to the field at want + 0x3c *)
  destruct orf as [sr|]; cbn [same_text] in SAME1; [|discriminate SAME1].
  apply Z.eqb_eq in SAME1.
  destruct OS1 as (Hrfnz & OS1s). destruct OS1s as (OS1z & OS1t).
  destruct OA1 as (Hrs32 & Hrsheap & Hrsaddr).
  destruct (cpv_heap_bounds B LAWS ly S W mem md rf (Z.of_nat (length sr) + 1) HAR Hrsheap ltac:(lia))
    as [Hrf4096 Hrfceil].
  psrr_branch_tok RUN BR HS SHOK CPspan.
  { (* 0x87330 beq a0,a3 taken: rf is the field's own address, no wrapper call *)
    cpv_cond HBr1. clear HBr1.
    (* 0x87344 .. 0x8736c: check 2 (want + 0x1c, removed by the contract's sa_addr on the entry), the flag
       word ignore_set, the mask want + 0x9c or 0, then beq s0,a2 *)
    cpv_ub E32 UB2.
    paj_run_tok RUN HS HJ SHOK CPspan.
    { cbn [ms_mem mkst]. rewrite (U_atom_off _ 12 want 28 E12) by lia.
      apply (obl_of_block SEGS B LAWS ly S W _ _ _ Bxp _ 4 wb wm (proj1 HJ) Hwin UB2); lia. }
    { awr_ok_tac. rewrite E2. reflexivity. }
    cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UNs2.
    clear HF HFr HG UB2. cpv_reenv HAE 1024%nat.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (KEPTs2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
        rdW W (ms_mem msx) a = rdW W mem a)
        by (intros a Ha Hn; etransitivity; [apply UNs2; lia | apply KEPT0; lia]) end.
    clear UNs2.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (AGs2 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
        by (intros a Ha; apply KEPTs2; lia) end.
    destruct (ms_ignore_set g) eqn:EI; try rewrite EI in Eis; try rewrite EI in SAME2; cbn in Eis; subst is.
    {
      (* ignore_set = 1: the ignore_file answer is a text equal to the field at want + 0x9c *)
      destruct oif as [si|]; cbn [same_text] in SAME2; [|discriminate SAME2].
      apply Z.eqb_eq in SAME2.
      destruct OS2 as (Higfnz & OS2s). destruct OS2s as (OS2z & OS2t).
      destruct OA2 as (His32 & Hisheap & Hisaddr).
      destruct (cpv_heap_bounds B LAWS ly S W mem md igf (Z.of_nat (length si) + 1) HAR Hisheap ltac:(lia))
        as [Hig4096 Higceil].
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { (* 0x8736c beq s0,a2 taken: igf is the field's own address, no wrapper call *)
        cpv_cond HBi3. clear HBi3.
        (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
        paj_run_tok RUN HS HJ SHOK CPspan.
        { awr_ok_tac. rewrite E2. reflexivity. }
        cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN4.
        clear HF HFr HG. cpv_reenv HAE 1024%nat.
        lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
          assert (KEPT4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
            rdW W (ms_mem msx) a = rdW W mem a)
            by (intros a Ha Hn; etransitivity; [apply UN4; lia | apply KEPTs2; lia]) end.
        clear UN4.
        prreg HS (1%bv : bv 5) RR4.
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
        intros mat'. unfold apost_base.
        lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
        split; [cbn [ms_regs]; rewrite RR4, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
        split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
        split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
        split.
        { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT4; lia. }
        unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
        exists (st_fs S). destruct S; reflexivity.
      }
      (* not taken: 0x87370 beqz s0 and 0x87374 beqz a0 are abort arms, then the wrapper call *)
      cpv_cond HBi3. clear HBi3.
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN5.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN5; lia | apply KEPTs2; lia]) end.
      clear UN5.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (AG5 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
          by (intros a Ha; apply KEPT5; lia) end.
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { (* igf = 0: refuted, the answer is a text *)
        cpv_cond HBi6. exfalso. rewrite branch_eq_U in HBi6.
        rewrite (U_atom _ 11 igf E11) in HBi6 by lia.
        replace (U _ (SLit 0)) with 0 in HBi6 by reflexivity.
        apply Z.eqb_eq in HBi6. exact (Higfnz HBi6). }
      cpv_cond HBi6. clear HBi6.
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN7.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT7 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN7; lia | apply KEPT5; lia]) end.
      clear UN7.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (AG7 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
          by (intros a Ha; apply KEPT7; lia) end.
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { (* ignore_set = 0: refuted, the flag word is 1 *)
        cpv_cond HBi8. exfalso. rewrite branch_eq_U in HBi8.
        rewrite (U_atom _ 34 1 E34) in HBi8 by lia.
        replace (U _ (SLit 0)) with 0 in HBi8 by reflexivity.
        apply Z.eqb_eq in HBi8. discriminate HBi8. }
      cpv_cond HBi8. clear HBi8.
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN9.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT9 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN9; lia | apply KEPT7; lia]) end.
      clear UN9.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (AG9 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
          by (intros a Ha; apply KEPT9; lia) end.
      (* 0x8737c jal: strcmp(igf, want + 156) through the wrapper's trampoline *)
      pmkst HS.
      prreg HS (1%bv : bv 5) QR10. prreg HS (2%bv : bv 5) QS10. prreg HS (3%bv : bv 5) QG10.
      prreg HS (4%bv : bv 5) QT10. prreg HS (10%bv : bv 5) QA10. prreg HS (11%bv : bv 5) QB10.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
        set (rg10 := r) in *; set (mm10 := m) in *; set (mdq10 := d) in * end.
      assert (Qsp10 : spZ rg10 = sp0 + -32) by (unfold spZ; rewrite QS10, E2; apply unsigned_lit_small; lia).
      assert (QAv10 : getr rg10 10 = w64 igf) by (rewrite QA10, E11; reflexivity).
      assert (QBv10 : getr rg10 11 = w64 (want + 156))
        by (rewrite QB10, E12, unsigned_lit_small by lia; reflexivity).
      (* the two texts the wrapper reads, at the memory of the call *)
      assert (SX10 : sa_strz (rdW W mm10) igf si)
        by (apply (cpv_keep_strz (rdW W mem) (rdW W mm10) (sp0 - STK_check_provenance) igf si AG9
              ltac:(lia) ltac:(lia) OS2z)).
      assert (TX10 : sa_tail (rdW W mm10) (igf + Z.of_nat (length si)))
        by (apply (cpv_keep_tail (rdW W mem) (rdW W mm10) (sp0 - STK_check_provenance) (igf + Z.of_nat (length si)) AG9
              ltac:(lia) ltac:(lia) HL8 OS2t)).
      assert (AX10 : sa_addr (rdW W mm10) igf (Z.of_nat (length si) + 1))
        by (apply (cpv_keep_addr (rdW W mem) (rdW W mm10) (sp0 - STK_check_provenance) igf (Z.of_nat (length si) + 1) AG9
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hisaddr)).
      assert (BSm10 : sa_bytes (rdW W mm10) want bs)
        by (apply (cpv_keep_bytes (rdW W mem) (rdW W mm10) (sp0 - STK_check_provenance) want bs AG9
              ltac:(lia) ltac:(rewrite LEN; lia) BS)).
      destruct (cpv_field_strz (rdW W mm10) want bs 156 96%nat 96 (ms_ignore_file g) BSm10 ltac:(lia) ltac:(reflexivity)
        ltac:(rewrite LEN; cbn; lia) CIF) as [SY10 LY10].
      assert (TY10 : sa_tail (rdW W mm10) (want + 156 + Z.of_nat (length (ms_ignore_file g))))
        by (apply (cpv_tail_in (rdW W mm10) want bs _ BSm10 LEN Hw4); lia).
      assert (AY10 : sa_addr (rdW W mm10) (want + 156) (Z.of_nat (length (ms_ignore_file g)) + 1)).
      { apply (cpv_addr_sub (rdW W mm10) want 256 (want + 156) (Z.of_nat (length (ms_ignore_file g)) + 1)); [|lia|lia|lia].
        apply (cpv_keep_addr (rdW W mem) (rdW W mm10) (sp0 - STK_check_provenance) want 256 AG9);
          [lia | lia | lia | lia | exact HWA]. }
      eapply SRr_bind.
      { eapply (CSTRCMP igf (want + 156) (seg_spec.zb si) (seg_spec.zb (ms_ignore_file g)) W rg10 mm10
           STK_check_provenance sp0 [] ly S W mem md [] ly S mdq10 0 (-32) _ HJ).
        - apply (cpv_keep_aro B (rdW W mem) (rdW W mm10) (sp0 - STK_check_provenance) RLO_A RHI_A AG9 HROL HRO).
        - exact Qsp10.
        - reflexivity.
        - lia.
        - unfold STK_check_provenance, ESTACK; lia.
        - rewrite QG10, E3; exact Hgp.
        - rewrite QT10, E4; exact Htp.
        - exact QR10.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - apply (cpv_P_of W mm10 rg10 igf (want + 156) si (ms_ignore_file g));
            [exact QAv10 | exact QBv10 | lia | lia
            | exact SX10 | exact TX10 | exact AX10 | lia | rewrite Qsp10; unfold ESTACK; lia
            | exact SY10 | exact TY10 | exact AY10 | lia | rewrite Qsp10; unfold ESTACK; lia]. }
      cbv beta. intros Wc10 cc10 _ (-> & regs210 & mem210 & md210 & -> & HJ210 & HP210 & HQ210 & HK210).
      (* the wrapper answered 0: the two texts are the same bytes *)
      assert (NX10 : ~ In (Z_to_bv 8 0) (seg_spec.zb si))
        by (apply (proj2 (cpv_astr_of_strz SEGS W mm10 igf si SX10))).
      assert (NY10 : ~ In (Z_to_bv 8 0) (seg_spec.zb (ms_ignore_file g)))
        by (apply (proj2 (cpv_astr_of_strz SEGS W mm10 (want + 156) (ms_ignore_file g) SY10))).
      assert (ZX10 : seg_spec.zs (seg_spec.zb si) = si)
        by (exact (proj2 (proj2 (sa_strz_bytes SEGS (w_H W) mm10 igf si SX10)))).
      assert (ZY10 : seg_spec.zs (seg_spec.zb (ms_ignore_file g)) = (ms_ignore_file g))
        by (exact (proj2 (proj2 (sa_strz_bytes SEGS (w_H W) mm10 (want + 156) (ms_ignore_file g) SY10)))).
      assert (EQ10 : seg_spec.zb si = seg_spec.zb (ms_ignore_file g)).
      { apply (proj1 (cpv_bridge_strcmp _ _ NX10 NY10)). rewrite ZX10, ZY10. exact SAME2. }
      assert (A010 : getr regs210 10 = w64 0) by (apply (proj2 HQ210); exact EQ10).
      pose proof HJ210 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPs10 & _).
      jafter_call_keep_pi HS 40%nat regs210 (mrestrict (w_H W) mem210) HP210 [0; 3]%nat HSc10.
      cbn [ms_mem ms_regs restrict mkst] in HSc10.
      match type of HSc10 with ?tq -> _ => assert (HRK10 : tq); [|specialize (HSc10 HRK10); clear HRK10] end.
      { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        - apply (cpv_region_kept_win SEGS _ (w_H W) mm10 mem210 2 sp0).
          + rewrite E2. reflexivity.
          + intros a Ha. apply HK210; unfold ESTACK; lia.
          + intros a Ha. apply HPs10. rewrite HSTK. lia.
        - apply (cpv_region_kept_win SEGS _ (w_H W) mm10 mem210 12 want).
          + rewrite E12. apply unsigned_lit_small. lia.
          + intros a Ha. apply HK210; unfold ESTACK; lia.
          + intros a Ha. lia. }
      clear HS. rewrite <- restrict_mkst_fx in HSc10. rename HSc10 into HS.
      lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
        assert (A4410 : ew En 44 = Z_to_bv 64 0)
          by (change 44%nat with (40 + 4)%nat;
              rewrite (ew_havoc_new _ 40 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia);
              cbn [nth map]; exact A010) end.
      lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
        assert (HEIc10 : img_env VAL A_LIM (havoc Eo kk ws))
          by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
      cpv_reenv HAE 40%nat.
      clear SHOK. lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
        assert (SHOK : sh_ok SEGS Bxp [] En (mrestrict (w_H W) mem210)) by constructor end.
      assert (KEPT10 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
        rdW W mem210 a = rdW W mem a)
        by (intros a Ha Hn; etransitivity; [apply HK210; unfold ESTACK; lia | apply KEPT9; lia]).
      assert (AG10 : cpv_agree (rdW W mem) (rdW W mem210) (sp0 - STK_check_provenance))
        by (intros a Ha; apply KEPT10; lia).
      clear HJ. rename HJ210 into HJ.
      (* bnez a0 right after the call: the wrapper answered 0, so the abort arm is not taken *)
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { cpv_cond HBc10. exfalso. rewrite branch_ne_U in HBc10. apply negb_true_iff in HBc10.
        apply Z.eqb_neq in HBc10. apply HBc10. rewrite (U_atom _ 44 0 A4410) by lia. reflexivity. }
      cpv_cond HBc10. clear HBc10.
      (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN11.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT11 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN11; lia | apply KEPT10; lia]) end.
      clear UN11.
      prreg HS (1%bv : bv 5) RR11.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
      split; [cbn [ms_regs]; rewrite RR11, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
      split.
      { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT11; lia. }
      unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
      exists (st_fs S). destruct S; reflexivity.
    }
    {
      (* ignore_set = 0: the ignore_file answer is NULL and the mask is 0 *)
      destruct oif as [si|]; cbn [same_text] in SAME2; [discriminate SAME2|].
      cbn [sa_ostr] in OS2.
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { (* 0x8736c beq s0,a2 taken *)
        cpv_cond HBz12. clear HBz12.
        (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
        paj_run_tok RUN HS HJ SHOK CPspan.
        { awr_ok_tac. rewrite E2. reflexivity. }
        cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN13.
        clear HF HFr HG. cpv_reenv HAE 1024%nat.
        lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
          assert (KEPT13 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
            rdW W (ms_mem msx) a = rdW W mem a)
            by (intros a Ha Hn; etransitivity; [apply UN13; lia | apply KEPTs2; lia]) end.
        clear UN13.
        prreg HS (1%bv : bv 5) RR13.
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
        intros mat'. unfold apost_base.
        lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
        split; [cbn [ms_regs]; rewrite RR13, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
        split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
        split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
        split.
        { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT13; lia. }
        unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
        exists (st_fs S). destruct S; reflexivity.
      }
      (* not taken: refuted, igf = 0 and the mask is 0 *)
      cpv_cond HBz12. exfalso. rewrite branch_eq_U in HBz12.
      rewrite (U_atom _ 11 igf E11) in HBz12 by lia.
      rewrite (cpv_mask0 _ 34 0 12 want 156 E34 eq_refl E12 ltac:(lia) ltac:(lia) ltac:(lia)) in HBz12.
      apply Z.eqb_neq in HBz12. exact (HBz12 OS2).
    }
  }
  (* not taken: 0x87334 beqz a0 and 0x87338 beqz a2 are abort arms, then the wrapper call *)
  cpv_cond HBr1. clear HBr1.
  paj_run_tok RUN HS HJ SHOK CPspan.
  { awr_ok_tac. rewrite E2. reflexivity. }
  cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN14.
  clear HF HFr HG. cpv_reenv HAE 1024%nat.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KEPT14 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
      rdW W (ms_mem msx) a = rdW W mem a)
      by (intros a Ha Hn; etransitivity; [apply UN14; lia | apply KEPT0; lia]) end.
  clear UN14.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (AG14 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
      by (intros a Ha; apply KEPT14; lia) end.
  psrr_branch_tok RUN BR HS SHOK CPspan.
  { (* rf = 0: refuted, the answer is a text *)
    cpv_cond HBr15. exfalso. rewrite branch_eq_U in HBr15.
    rewrite (U_atom _ 10 rf E10) in HBr15 by lia.
    replace (U _ (SLit 0)) with 0 in HBr15 by reflexivity.
    apply Z.eqb_eq in HBr15. exact (Hrfnz HBr15). }
  cpv_cond HBr15. clear HBr15.
  paj_run_tok RUN HS HJ SHOK CPspan.
  { awr_ok_tac. rewrite E2. reflexivity. }
  cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN16.
  clear HF HFr HG. cpv_reenv HAE 1024%nat.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KEPT16 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
      rdW W (ms_mem msx) a = rdW W mem a)
      by (intros a Ha Hn; etransitivity; [apply UN16; lia | apply KEPT14; lia]) end.
  clear UN16.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (AG16 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
      by (intros a Ha; apply KEPT16; lia) end.
  psrr_branch_tok RUN BR HS SHOK CPspan.
  { (* role_set = 0: refuted, the flag word is 1 *)
    cpv_cond HBr17. exfalso. rewrite branch_eq_U in HBr17.
    rewrite (U_atom _ 33 1 E33) in HBr17 by lia.
    replace (U _ (SLit 0)) with 0 in HBr17 by reflexivity.
    apply Z.eqb_eq in HBr17. discriminate HBr17. }
  cpv_cond HBr17. clear HBr17.
  paj_run_tok RUN HS HJ SHOK CPspan.
  { awr_ok_tac. rewrite E2. reflexivity. }
  cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN18.
  clear HF HFr HG. cpv_reenv HAE 1024%nat.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KEPT18 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
      rdW W (ms_mem msx) a = rdW W mem a)
      by (intros a Ha Hn; etransitivity; [apply UN18; lia | apply KEPT16; lia]) end.
  clear UN18.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (AG18 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
      by (intros a Ha; apply KEPT18; lia) end.
  (* 0x8733c jal: strcmp(rf, want + 60) through the wrapper's trampoline *)
  pmkst HS.
  prreg HS (1%bv : bv 5) QR19. prreg HS (2%bv : bv 5) QS19. prreg HS (3%bv : bv 5) QG19.
  prreg HS (4%bv : bv 5) QT19. prreg HS (10%bv : bv 5) QA19. prreg HS (11%bv : bv 5) QB19.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
    set (rg19 := r) in *; set (mm19 := m) in *; set (mdq19 := d) in * end.
  assert (Qsp19 : spZ rg19 = sp0 + -32) by (unfold spZ; rewrite QS19, E2; apply unsigned_lit_small; lia).
  assert (QAv19 : getr rg19 10 = w64 rf) by (rewrite QA19, E10; reflexivity).
  assert (QBv19 : getr rg19 11 = w64 (want + 60))
    by (rewrite QB19, E12, unsigned_lit_small by lia; reflexivity).
  (* the two texts the wrapper reads, at the memory of the call *)
  assert (SX19 : sa_strz (rdW W mm19) rf sr)
    by (apply (cpv_keep_strz (rdW W mem) (rdW W mm19) (sp0 - STK_check_provenance) rf sr AG18
          ltac:(lia) ltac:(lia) OS1z)).
  assert (TX19 : sa_tail (rdW W mm19) (rf + Z.of_nat (length sr)))
    by (apply (cpv_keep_tail (rdW W mem) (rdW W mm19) (sp0 - STK_check_provenance) (rf + Z.of_nat (length sr)) AG18
          ltac:(lia) ltac:(lia) HL8 OS1t)).
  assert (AX19 : sa_addr (rdW W mm19) rf (Z.of_nat (length sr) + 1))
    by (apply (cpv_keep_addr (rdW W mem) (rdW W mm19) (sp0 - STK_check_provenance) rf (Z.of_nat (length sr) + 1) AG18
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrsaddr)).
  assert (BSm19 : sa_bytes (rdW W mm19) want bs)
    by (apply (cpv_keep_bytes (rdW W mem) (rdW W mm19) (sp0 - STK_check_provenance) want bs AG18
          ltac:(lia) ltac:(rewrite LEN; lia) BS)).
  destruct (cpv_field_strz (rdW W mm19) want bs 60 96%nat 96 (ms_role_file g) BSm19 ltac:(lia) ltac:(reflexivity)
    ltac:(rewrite LEN; cbn; lia) CRF) as [SY19 LY19].
  assert (TY19 : sa_tail (rdW W mm19) (want + 60 + Z.of_nat (length (ms_role_file g))))
    by (apply (cpv_tail_in (rdW W mm19) want bs _ BSm19 LEN Hw4); lia).
  assert (AY19 : sa_addr (rdW W mm19) (want + 60) (Z.of_nat (length (ms_role_file g)) + 1)).
  { apply (cpv_addr_sub (rdW W mm19) want 256 (want + 60) (Z.of_nat (length (ms_role_file g)) + 1)); [|lia|lia|lia].
    apply (cpv_keep_addr (rdW W mem) (rdW W mm19) (sp0 - STK_check_provenance) want 256 AG18);
      [lia | lia | lia | lia | exact HWA]. }
  eapply SRr_bind.
  { eapply (CSTRCMP rf (want + 60) (seg_spec.zb sr) (seg_spec.zb (ms_role_file g)) W rg19 mm19
       STK_check_provenance sp0 [] ly S W mem md [] ly S mdq19 0 (-32) _ HJ).
    - apply (cpv_keep_aro B (rdW W mem) (rdW W mm19) (sp0 - STK_check_provenance) RLO_A RHI_A AG18 HROL HRO).
    - exact Qsp19.
    - reflexivity.
    - lia.
    - unfold STK_check_provenance, ESTACK; lia.
    - rewrite QG19, E3; exact Hgp.
    - rewrite QT19, E4; exact Htp.
    - exact QR19.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - apply (cpv_P_of W mm19 rg19 rf (want + 60) sr (ms_role_file g));
        [exact QAv19 | exact QBv19 | lia | lia
        | exact SX19 | exact TX19 | exact AX19 | lia | rewrite Qsp19; unfold ESTACK; lia
        | exact SY19 | exact TY19 | exact AY19 | lia | rewrite Qsp19; unfold ESTACK; lia]. }
  cbv beta. intros Wc19 cc19 _ (-> & regs219 & mem219 & md219 & -> & HJ219 & HP219 & HQ219 & HK219).
  (* the wrapper answered 0: the two texts are the same bytes *)
  assert (NX19 : ~ In (Z_to_bv 8 0) (seg_spec.zb sr))
    by (apply (proj2 (cpv_astr_of_strz SEGS W mm19 rf sr SX19))).
  assert (NY19 : ~ In (Z_to_bv 8 0) (seg_spec.zb (ms_role_file g)))
    by (apply (proj2 (cpv_astr_of_strz SEGS W mm19 (want + 60) (ms_role_file g) SY19))).
  assert (ZX19 : seg_spec.zs (seg_spec.zb sr) = sr)
    by (exact (proj2 (proj2 (sa_strz_bytes SEGS (w_H W) mm19 rf sr SX19)))).
  assert (ZY19 : seg_spec.zs (seg_spec.zb (ms_role_file g)) = (ms_role_file g))
    by (exact (proj2 (proj2 (sa_strz_bytes SEGS (w_H W) mm19 (want + 60) (ms_role_file g) SY19)))).
  assert (EQ19 : seg_spec.zb sr = seg_spec.zb (ms_role_file g)).
  { apply (proj1 (cpv_bridge_strcmp _ _ NX19 NY19)). rewrite ZX19, ZY19. exact SAME1. }
  assert (A019 : getr regs219 10 = w64 0) by (apply (proj2 HQ219); exact EQ19).
  pose proof HJ219 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPs19 & _).
  jafter_call_keep_pi HS 40%nat regs219 (mrestrict (w_H W) mem219) HP219 [0; 3]%nat HSc19.
  cbn [ms_mem ms_regs restrict mkst] in HSc19.
  match type of HSc19 with ?tq -> _ => assert (HRK19 : tq); [|specialize (HSc19 HRK19); clear HRK19] end.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (cpv_region_kept_win SEGS _ (w_H W) mm19 mem219 2 sp0).
      + rewrite E2. reflexivity.
      + intros a Ha. apply HK219; unfold ESTACK; lia.
      + intros a Ha. apply HPs19. rewrite HSTK. lia.
    - apply (cpv_region_kept_win SEGS _ (w_H W) mm19 mem219 12 want).
      + rewrite E12. apply unsigned_lit_small. lia.
      + intros a Ha. apply HK219; unfold ESTACK; lia.
      + intros a Ha. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HSc19. rename HSc19 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (A4419 : ew En 44 = Z_to_bv 64 0)
      by (change 44%nat with (40 + 4)%nat;
          rewrite (ew_havoc_new _ 40 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia);
          cbn [nth map]; exact A019) end.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
    assert (HEIc19 : img_env VAL A_LIM (havoc Eo kk ws))
      by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
  cpv_reenv HAE 40%nat.
  clear SHOK. lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (SHOK : sh_ok SEGS Bxp [] En (mrestrict (w_H W) mem219)) by constructor end.
  assert (KEPT19 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
    rdW W mem219 a = rdW W mem a)
    by (intros a Ha Hn; etransitivity; [apply HK219; unfold ESTACK; lia | apply KEPT18; lia]).
  assert (AG19 : cpv_agree (rdW W mem) (rdW W mem219) (sp0 - STK_check_provenance))
    by (intros a Ha; apply KEPT19; lia).
  clear HJ. rename HJ219 into HJ.
  (* bnez a0 right after the call: the wrapper answered 0, so the abort arm is not taken *)
  psrr_branch_tok RUN BR HS SHOK CPspan.
  { cpv_cond HBc19. exfalso. rewrite branch_ne_U in HBc19. apply negb_true_iff in HBc19.
    apply Z.eqb_neq in HBc19. apply HBc19. rewrite (U_atom _ 44 0 A4419) by lia. reflexivity. }
  cpv_cond HBc19. clear HBc19.
  (* 0x87344 .. 0x8736c: check 2 (want + 0x1c, removed by the contract's sa_addr on the entry), the flag
     word ignore_set, the mask want + 0x9c or 0, then beq s0,a2 *)
  cpv_ub E32 UB20.
  paj_run_tok RUN HS HJ SHOK CPspan.
  { cbn [ms_mem mkst]. rewrite (U_atom_off _ 12 want 28 E12) by lia.
    apply (obl_of_block SEGS B LAWS ly S W _ _ _ Bxp _ 4 wb wm (proj1 HJ) Hwin UB20); lia. }
  { awr_ok_tac. rewrite E2. reflexivity. }
  cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UNs20.
  clear HF HFr HG UB20. cpv_reenv HAE 1024%nat.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KEPTs20 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
      rdW W (ms_mem msx) a = rdW W mem a)
      by (intros a Ha Hn; etransitivity; [apply UNs20; lia | apply KEPT19; lia]) end.
  clear UNs20.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (AGs20 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
      by (intros a Ha; apply KEPTs20; lia) end.
  destruct (ms_ignore_set g) eqn:EI; try rewrite EI in Eis; try rewrite EI in SAME2; cbn in Eis; subst is.
  {
    (* ignore_set = 1: the ignore_file answer is a text equal to the field at want + 0x9c *)
    destruct oif as [si|]; cbn [same_text] in SAME2; [|discriminate SAME2].
    apply Z.eqb_eq in SAME2.
    destruct OS2 as (Higfnz & OS2s). destruct OS2s as (OS2z & OS2t).
    destruct OA2 as (His32 & Hisheap & Hisaddr).
    destruct (cpv_heap_bounds B LAWS ly S W mem md igf (Z.of_nat (length si) + 1) HAR Hisheap ltac:(lia))
      as [Hig4096 Higceil].
    psrr_branch_tok RUN BR HS SHOK CPspan.
    { (* 0x8736c beq s0,a2 taken: igf is the field's own address, no wrapper call *)
      cpv_cond HBi21. clear HBi21.
      (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN22.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT22 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN22; lia | apply KEPTs20; lia]) end.
      clear UN22.
      prreg HS (1%bv : bv 5) RR22.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
      split; [cbn [ms_regs]; rewrite RR22, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
      split.
      { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT22; lia. }
      unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
      exists (st_fs S). destruct S; reflexivity.
    }
    (* not taken: 0x87370 beqz s0 and 0x87374 beqz a0 are abort arms, then the wrapper call *)
    cpv_cond HBi21. clear HBi21.
    paj_run_tok RUN HS HJ SHOK CPspan.
    { awr_ok_tac. rewrite E2. reflexivity. }
    cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN23.
    clear HF HFr HG. cpv_reenv HAE 1024%nat.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (KEPT23 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
        rdW W (ms_mem msx) a = rdW W mem a)
        by (intros a Ha Hn; etransitivity; [apply UN23; lia | apply KEPTs20; lia]) end.
    clear UN23.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (AG23 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
        by (intros a Ha; apply KEPT23; lia) end.
    psrr_branch_tok RUN BR HS SHOK CPspan.
    { (* igf = 0: refuted, the answer is a text *)
      cpv_cond HBi24. exfalso. rewrite branch_eq_U in HBi24.
      rewrite (U_atom _ 11 igf E11) in HBi24 by lia.
      replace (U _ (SLit 0)) with 0 in HBi24 by reflexivity.
      apply Z.eqb_eq in HBi24. exact (Higfnz HBi24). }
    cpv_cond HBi24. clear HBi24.
    paj_run_tok RUN HS HJ SHOK CPspan.
    { awr_ok_tac. rewrite E2. reflexivity. }
    cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN25.
    clear HF HFr HG. cpv_reenv HAE 1024%nat.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (KEPT25 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
        rdW W (ms_mem msx) a = rdW W mem a)
        by (intros a Ha Hn; etransitivity; [apply UN25; lia | apply KEPT23; lia]) end.
    clear UN25.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (AG25 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
        by (intros a Ha; apply KEPT25; lia) end.
    psrr_branch_tok RUN BR HS SHOK CPspan.
    { (* ignore_set = 0: refuted, the flag word is 1 *)
      cpv_cond HBi26. exfalso. rewrite branch_eq_U in HBi26.
      rewrite (U_atom _ 34 1 E34) in HBi26 by lia.
      replace (U _ (SLit 0)) with 0 in HBi26 by reflexivity.
      apply Z.eqb_eq in HBi26. discriminate HBi26. }
    cpv_cond HBi26. clear HBi26.
    paj_run_tok RUN HS HJ SHOK CPspan.
    { awr_ok_tac. rewrite E2. reflexivity. }
    cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN27.
    clear HF HFr HG. cpv_reenv HAE 1024%nat.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (KEPT27 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
        rdW W (ms_mem msx) a = rdW W mem a)
        by (intros a Ha Hn; etransitivity; [apply UN27; lia | apply KEPT25; lia]) end.
    clear UN27.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (AG27 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
        by (intros a Ha; apply KEPT27; lia) end.
    (* 0x8737c jal: strcmp(igf, want + 156) through the wrapper's trampoline *)
    pmkst HS.
    prreg HS (1%bv : bv 5) QR28. prreg HS (2%bv : bv 5) QS28. prreg HS (3%bv : bv 5) QG28.
    prreg HS (4%bv : bv 5) QT28. prreg HS (10%bv : bv 5) QA28. prreg HS (11%bv : bv 5) QB28.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
      set (rg28 := r) in *; set (mm28 := m) in *; set (mdq28 := d) in * end.
    assert (Qsp28 : spZ rg28 = sp0 + -32) by (unfold spZ; rewrite QS28, E2; apply unsigned_lit_small; lia).
    assert (QAv28 : getr rg28 10 = w64 igf) by (rewrite QA28, E11; reflexivity).
    assert (QBv28 : getr rg28 11 = w64 (want + 156))
      by (rewrite QB28, E12, unsigned_lit_small by lia; reflexivity).
    (* the two texts the wrapper reads, at the memory of the call *)
    assert (SX28 : sa_strz (rdW W mm28) igf si)
      by (apply (cpv_keep_strz (rdW W mem) (rdW W mm28) (sp0 - STK_check_provenance) igf si AG27
            ltac:(lia) ltac:(lia) OS2z)).
    assert (TX28 : sa_tail (rdW W mm28) (igf + Z.of_nat (length si)))
      by (apply (cpv_keep_tail (rdW W mem) (rdW W mm28) (sp0 - STK_check_provenance) (igf + Z.of_nat (length si)) AG27
            ltac:(lia) ltac:(lia) HL8 OS2t)).
    assert (AX28 : sa_addr (rdW W mm28) igf (Z.of_nat (length si) + 1))
      by (apply (cpv_keep_addr (rdW W mem) (rdW W mm28) (sp0 - STK_check_provenance) igf (Z.of_nat (length si) + 1) AG27
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hisaddr)).
    assert (BSm28 : sa_bytes (rdW W mm28) want bs)
      by (apply (cpv_keep_bytes (rdW W mem) (rdW W mm28) (sp0 - STK_check_provenance) want bs AG27
            ltac:(lia) ltac:(rewrite LEN; lia) BS)).
    destruct (cpv_field_strz (rdW W mm28) want bs 156 96%nat 96 (ms_ignore_file g) BSm28 ltac:(lia) ltac:(reflexivity)
      ltac:(rewrite LEN; cbn; lia) CIF) as [SY28 LY28].
    assert (TY28 : sa_tail (rdW W mm28) (want + 156 + Z.of_nat (length (ms_ignore_file g))))
      by (apply (cpv_tail_in (rdW W mm28) want bs _ BSm28 LEN Hw4); lia).
    assert (AY28 : sa_addr (rdW W mm28) (want + 156) (Z.of_nat (length (ms_ignore_file g)) + 1)).
    { apply (cpv_addr_sub (rdW W mm28) want 256 (want + 156) (Z.of_nat (length (ms_ignore_file g)) + 1)); [|lia|lia|lia].
      apply (cpv_keep_addr (rdW W mem) (rdW W mm28) (sp0 - STK_check_provenance) want 256 AG27);
        [lia | lia | lia | lia | exact HWA]. }
    eapply SRr_bind.
    { eapply (CSTRCMP igf (want + 156) (seg_spec.zb si) (seg_spec.zb (ms_ignore_file g)) W rg28 mm28
         STK_check_provenance sp0 [] ly S W mem md [] ly S mdq28 0 (-32) _ HJ).
      - apply (cpv_keep_aro B (rdW W mem) (rdW W mm28) (sp0 - STK_check_provenance) RLO_A RHI_A AG27 HROL HRO).
      - exact Qsp28.
      - reflexivity.
      - lia.
      - unfold STK_check_provenance, ESTACK; lia.
      - rewrite QG28, E3; exact Hgp.
      - rewrite QT28, E4; exact Htp.
      - exact QR28.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - apply (cpv_P_of W mm28 rg28 igf (want + 156) si (ms_ignore_file g));
          [exact QAv28 | exact QBv28 | lia | lia
          | exact SX28 | exact TX28 | exact AX28 | lia | rewrite Qsp28; unfold ESTACK; lia
          | exact SY28 | exact TY28 | exact AY28 | lia | rewrite Qsp28; unfold ESTACK; lia]. }
    cbv beta. intros Wc28 cc28 _ (-> & regs228 & mem228 & md228 & -> & HJ228 & HP228 & HQ228 & HK228).
    (* the wrapper answered 0: the two texts are the same bytes *)
    assert (NX28 : ~ In (Z_to_bv 8 0) (seg_spec.zb si))
      by (apply (proj2 (cpv_astr_of_strz SEGS W mm28 igf si SX28))).
    assert (NY28 : ~ In (Z_to_bv 8 0) (seg_spec.zb (ms_ignore_file g)))
      by (apply (proj2 (cpv_astr_of_strz SEGS W mm28 (want + 156) (ms_ignore_file g) SY28))).
    assert (ZX28 : seg_spec.zs (seg_spec.zb si) = si)
      by (exact (proj2 (proj2 (sa_strz_bytes SEGS (w_H W) mm28 igf si SX28)))).
    assert (ZY28 : seg_spec.zs (seg_spec.zb (ms_ignore_file g)) = (ms_ignore_file g))
      by (exact (proj2 (proj2 (sa_strz_bytes SEGS (w_H W) mm28 (want + 156) (ms_ignore_file g) SY28)))).
    assert (EQ28 : seg_spec.zb si = seg_spec.zb (ms_ignore_file g)).
    { apply (proj1 (cpv_bridge_strcmp _ _ NX28 NY28)). rewrite ZX28, ZY28. exact SAME2. }
    assert (A028 : getr regs228 10 = w64 0) by (apply (proj2 HQ228); exact EQ28).
    pose proof HJ228 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPs28 & _).
    jafter_call_keep_pi HS 56%nat regs228 (mrestrict (w_H W) mem228) HP228 [0; 1]%nat HSc28.
    cbn [ms_mem ms_regs restrict mkst] in HSc28.
    match type of HSc28 with ?tq -> _ => assert (HRK28 : tq); [|specialize (HSc28 HRK28); clear HRK28] end.
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - apply (cpv_region_kept_win SEGS _ (w_H W) mm28 mem228 2 sp0).
        + rewrite E2. reflexivity.
        + intros a Ha. apply HK228; unfold ESTACK; lia.
        + intros a Ha. apply HPs28. rewrite HSTK. lia.
      - apply (cpv_region_kept_win SEGS _ (w_H W) mm28 mem228 12 want).
        + rewrite E12. apply unsigned_lit_small. lia.
        + intros a Ha. apply HK228; unfold ESTACK; lia.
        + intros a Ha. lia. }
    clear HS. rewrite <- restrict_mkst_fx in HSc28. rename HSc28 into HS.
    lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
      assert (A4428 : ew En 60 = Z_to_bv 64 0)
        by (change 60%nat with (56 + 4)%nat;
            rewrite (ew_havoc_new _ 56 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia);
            cbn [nth map]; exact A028) end.
    lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
      assert (HEIc28 : img_env VAL A_LIM (havoc Eo kk ws))
        by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
    cpv_reenv HAE 56%nat.
    clear SHOK. lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
      assert (SHOK : sh_ok SEGS Bxp [] En (mrestrict (w_H W) mem228)) by constructor end.
    assert (KEPT28 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
      rdW W mem228 a = rdW W mem a)
      by (intros a Ha Hn; etransitivity; [apply HK228; unfold ESTACK; lia | apply KEPT27; lia]).
    assert (AG28 : cpv_agree (rdW W mem) (rdW W mem228) (sp0 - STK_check_provenance))
      by (intros a Ha; apply KEPT28; lia).
    clear HJ. rename HJ228 into HJ.
    (* bnez a0 right after the call: the wrapper answered 0, so the abort arm is not taken *)
    psrr_branch_tok RUN BR HS SHOK CPspan.
    { cpv_cond HBc28. exfalso. rewrite branch_ne_U in HBc28. apply negb_true_iff in HBc28.
      apply Z.eqb_neq in HBc28. apply HBc28. rewrite (U_atom _ 60 0 A4428) by lia. reflexivity. }
    cpv_cond HBc28. clear HBc28.
    (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
    paj_run_tok RUN HS HJ SHOK CPspan.
    { awr_ok_tac. rewrite E2. reflexivity. }
    cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN29.
    clear HF HFr HG. cpv_reenv HAE 1024%nat.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (KEPT29 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
        rdW W (ms_mem msx) a = rdW W mem a)
        by (intros a Ha Hn; etransitivity; [apply UN29; lia | apply KEPT28; lia]) end.
    clear UN29.
    prreg HS (1%bv : bv 5) RR29.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
    split; [cbn [ms_regs]; rewrite RR29, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
    split.
    { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT29; lia. }
    unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
    exists (st_fs S). destruct S; reflexivity.
  }
  {
    (* ignore_set = 0: the ignore_file answer is NULL and the mask is 0 *)
    destruct oif as [si|]; cbn [same_text] in SAME2; [discriminate SAME2|].
    cbn [sa_ostr] in OS2.
    psrr_branch_tok RUN BR HS SHOK CPspan.
    { (* 0x8736c beq s0,a2 taken *)
      cpv_cond HBz30. clear HBz30.
      (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN31.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT31 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN31; lia | apply KEPTs20; lia]) end.
      clear UN31.
      prreg HS (1%bv : bv 5) RR31.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
      split; [cbn [ms_regs]; rewrite RR31, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
      split.
      { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT31; lia. }
      unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
      exists (st_fs S). destruct S; reflexivity.
    }
    (* not taken: refuted, igf = 0 and the mask is 0 *)
    cpv_cond HBz30. exfalso. rewrite branch_eq_U in HBz30.
    rewrite (U_atom _ 11 igf E11) in HBz30 by lia.
    rewrite (cpv_mask0 _ 34 0 12 want 156 E34 eq_refl E12 ltac:(lia) ltac:(lia) ltac:(lia)) in HBz30.
    apply Z.eqb_neq in HBz30. exact (HBz30 OS2).
  }
}
{
  (* role_set = 0: the role_file answer is NULL and the mask is 0 *)
  destruct orf as [sr|]; cbn [same_text] in SAME1; [discriminate SAME1|].
  cbn [sa_ostr] in OS1.
  psrr_branch_tok RUN BR HS SHOK CPspan.
  { (* 0x87330 beq a0,a3 taken *)
    cpv_cond HBr32. clear HBr32.
    (* 0x87344 .. 0x8736c: check 2 (want + 0x1c, removed by the contract's sa_addr on the entry), the flag
       word ignore_set, the mask want + 0x9c or 0, then beq s0,a2 *)
    cpv_ub E32 UB33.
    paj_run_tok RUN HS HJ SHOK CPspan.
    { cbn [ms_mem mkst]. rewrite (U_atom_off _ 12 want 28 E12) by lia.
      apply (obl_of_block SEGS B LAWS ly S W _ _ _ Bxp _ 4 wb wm (proj1 HJ) Hwin UB33); lia. }
    { awr_ok_tac. rewrite E2. reflexivity. }
    cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UNs33.
    clear HF HFr HG UB33. cpv_reenv HAE 1024%nat.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (KEPTs33 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
        rdW W (ms_mem msx) a = rdW W mem a)
        by (intros a Ha Hn; etransitivity; [apply UNs33; lia | apply KEPT0; lia]) end.
    clear UNs33.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (AGs33 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
        by (intros a Ha; apply KEPTs33; lia) end.
    destruct (ms_ignore_set g) eqn:EI; try rewrite EI in Eis; try rewrite EI in SAME2; cbn in Eis; subst is.
    {
      (* ignore_set = 1: the ignore_file answer is a text equal to the field at want + 0x9c *)
      destruct oif as [si|]; cbn [same_text] in SAME2; [|discriminate SAME2].
      apply Z.eqb_eq in SAME2.
      destruct OS2 as (Higfnz & OS2s). destruct OS2s as (OS2z & OS2t).
      destruct OA2 as (His32 & Hisheap & Hisaddr).
      destruct (cpv_heap_bounds B LAWS ly S W mem md igf (Z.of_nat (length si) + 1) HAR Hisheap ltac:(lia))
        as [Hig4096 Higceil].
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { (* 0x8736c beq s0,a2 taken: igf is the field's own address, no wrapper call *)
        cpv_cond HBi34. clear HBi34.
        (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
        paj_run_tok RUN HS HJ SHOK CPspan.
        { awr_ok_tac. rewrite E2. reflexivity. }
        cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN35.
        clear HF HFr HG. cpv_reenv HAE 1024%nat.
        lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
          assert (KEPT35 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
            rdW W (ms_mem msx) a = rdW W mem a)
            by (intros a Ha Hn; etransitivity; [apply UN35; lia | apply KEPTs33; lia]) end.
        clear UN35.
        prreg HS (1%bv : bv 5) RR35.
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
        intros mat'. unfold apost_base.
        lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
        split; [cbn [ms_regs]; rewrite RR35, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
        split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
        split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
        split.
        { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT35; lia. }
        unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
        exists (st_fs S). destruct S; reflexivity.
      }
      (* not taken: 0x87370 beqz s0 and 0x87374 beqz a0 are abort arms, then the wrapper call *)
      cpv_cond HBi34. clear HBi34.
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN36.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT36 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN36; lia | apply KEPTs33; lia]) end.
      clear UN36.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (AG36 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
          by (intros a Ha; apply KEPT36; lia) end.
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { (* igf = 0: refuted, the answer is a text *)
        cpv_cond HBi37. exfalso. rewrite branch_eq_U in HBi37.
        rewrite (U_atom _ 11 igf E11) in HBi37 by lia.
        replace (U _ (SLit 0)) with 0 in HBi37 by reflexivity.
        apply Z.eqb_eq in HBi37. exact (Higfnz HBi37). }
      cpv_cond HBi37. clear HBi37.
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN38.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT38 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN38; lia | apply KEPT36; lia]) end.
      clear UN38.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (AG38 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
          by (intros a Ha; apply KEPT38; lia) end.
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { (* ignore_set = 0: refuted, the flag word is 1 *)
        cpv_cond HBi39. exfalso. rewrite branch_eq_U in HBi39.
        rewrite (U_atom _ 34 1 E34) in HBi39 by lia.
        replace (U _ (SLit 0)) with 0 in HBi39 by reflexivity.
        apply Z.eqb_eq in HBi39. discriminate HBi39. }
      cpv_cond HBi39. clear HBi39.
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN40.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT40 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN40; lia | apply KEPT38; lia]) end.
      clear UN40.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (AG40 : cpv_agree (rdW W mem) (rdW W (ms_mem msx)) (sp0 - STK_check_provenance))
          by (intros a Ha; apply KEPT40; lia) end.
      (* 0x8737c jal: strcmp(igf, want + 156) through the wrapper's trampoline *)
      pmkst HS.
      prreg HS (1%bv : bv 5) QR41. prreg HS (2%bv : bv 5) QS41. prreg HS (3%bv : bv 5) QG41.
      prreg HS (4%bv : bv 5) QT41. prreg HS (10%bv : bv 5) QA41. prreg HS (11%bv : bv 5) QB41.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
        set (rg41 := r) in *; set (mm41 := m) in *; set (mdq41 := d) in * end.
      assert (Qsp41 : spZ rg41 = sp0 + -32) by (unfold spZ; rewrite QS41, E2; apply unsigned_lit_small; lia).
      assert (QAv41 : getr rg41 10 = w64 igf) by (rewrite QA41, E11; reflexivity).
      assert (QBv41 : getr rg41 11 = w64 (want + 156))
        by (rewrite QB41, E12, unsigned_lit_small by lia; reflexivity).
      (* the two texts the wrapper reads, at the memory of the call *)
      assert (SX41 : sa_strz (rdW W mm41) igf si)
        by (apply (cpv_keep_strz (rdW W mem) (rdW W mm41) (sp0 - STK_check_provenance) igf si AG40
              ltac:(lia) ltac:(lia) OS2z)).
      assert (TX41 : sa_tail (rdW W mm41) (igf + Z.of_nat (length si)))
        by (apply (cpv_keep_tail (rdW W mem) (rdW W mm41) (sp0 - STK_check_provenance) (igf + Z.of_nat (length si)) AG40
              ltac:(lia) ltac:(lia) HL8 OS2t)).
      assert (AX41 : sa_addr (rdW W mm41) igf (Z.of_nat (length si) + 1))
        by (apply (cpv_keep_addr (rdW W mem) (rdW W mm41) (sp0 - STK_check_provenance) igf (Z.of_nat (length si) + 1) AG40
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hisaddr)).
      assert (BSm41 : sa_bytes (rdW W mm41) want bs)
        by (apply (cpv_keep_bytes (rdW W mem) (rdW W mm41) (sp0 - STK_check_provenance) want bs AG40
              ltac:(lia) ltac:(rewrite LEN; lia) BS)).
      destruct (cpv_field_strz (rdW W mm41) want bs 156 96%nat 96 (ms_ignore_file g) BSm41 ltac:(lia) ltac:(reflexivity)
        ltac:(rewrite LEN; cbn; lia) CIF) as [SY41 LY41].
      assert (TY41 : sa_tail (rdW W mm41) (want + 156 + Z.of_nat (length (ms_ignore_file g))))
        by (apply (cpv_tail_in (rdW W mm41) want bs _ BSm41 LEN Hw4); lia).
      assert (AY41 : sa_addr (rdW W mm41) (want + 156) (Z.of_nat (length (ms_ignore_file g)) + 1)).
      { apply (cpv_addr_sub (rdW W mm41) want 256 (want + 156) (Z.of_nat (length (ms_ignore_file g)) + 1)); [|lia|lia|lia].
        apply (cpv_keep_addr (rdW W mem) (rdW W mm41) (sp0 - STK_check_provenance) want 256 AG40);
          [lia | lia | lia | lia | exact HWA]. }
      eapply SRr_bind.
      { eapply (CSTRCMP igf (want + 156) (seg_spec.zb si) (seg_spec.zb (ms_ignore_file g)) W rg41 mm41
           STK_check_provenance sp0 [] ly S W mem md [] ly S mdq41 0 (-32) _ HJ).
        - apply (cpv_keep_aro B (rdW W mem) (rdW W mm41) (sp0 - STK_check_provenance) RLO_A RHI_A AG40 HROL HRO).
        - exact Qsp41.
        - reflexivity.
        - lia.
        - unfold STK_check_provenance, ESTACK; lia.
        - rewrite QG41, E3; exact Hgp.
        - rewrite QT41, E4; exact Htp.
        - exact QR41.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - apply (cpv_P_of W mm41 rg41 igf (want + 156) si (ms_ignore_file g));
            [exact QAv41 | exact QBv41 | lia | lia
            | exact SX41 | exact TX41 | exact AX41 | lia | rewrite Qsp41; unfold ESTACK; lia
            | exact SY41 | exact TY41 | exact AY41 | lia | rewrite Qsp41; unfold ESTACK; lia]. }
      cbv beta. intros Wc41 cc41 _ (-> & regs241 & mem241 & md241 & -> & HJ241 & HP241 & HQ241 & HK241).
      (* the wrapper answered 0: the two texts are the same bytes *)
      assert (NX41 : ~ In (Z_to_bv 8 0) (seg_spec.zb si))
        by (apply (proj2 (cpv_astr_of_strz SEGS W mm41 igf si SX41))).
      assert (NY41 : ~ In (Z_to_bv 8 0) (seg_spec.zb (ms_ignore_file g)))
        by (apply (proj2 (cpv_astr_of_strz SEGS W mm41 (want + 156) (ms_ignore_file g) SY41))).
      assert (ZX41 : seg_spec.zs (seg_spec.zb si) = si)
        by (exact (proj2 (proj2 (sa_strz_bytes SEGS (w_H W) mm41 igf si SX41)))).
      assert (ZY41 : seg_spec.zs (seg_spec.zb (ms_ignore_file g)) = (ms_ignore_file g))
        by (exact (proj2 (proj2 (sa_strz_bytes SEGS (w_H W) mm41 (want + 156) (ms_ignore_file g) SY41)))).
      assert (EQ41 : seg_spec.zb si = seg_spec.zb (ms_ignore_file g)).
      { apply (proj1 (cpv_bridge_strcmp _ _ NX41 NY41)). rewrite ZX41, ZY41. exact SAME2. }
      assert (A041 : getr regs241 10 = w64 0) by (apply (proj2 HQ241); exact EQ41).
      pose proof HJ241 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPs41 & _).
      jafter_call_keep_pi HS 40%nat regs241 (mrestrict (w_H W) mem241) HP241 [0; 3]%nat HSc41.
      cbn [ms_mem ms_regs restrict mkst] in HSc41.
      match type of HSc41 with ?tq -> _ => assert (HRK41 : tq); [|specialize (HSc41 HRK41); clear HRK41] end.
      { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        - apply (cpv_region_kept_win SEGS _ (w_H W) mm41 mem241 2 sp0).
          + rewrite E2. reflexivity.
          + intros a Ha. apply HK241; unfold ESTACK; lia.
          + intros a Ha. apply HPs41. rewrite HSTK. lia.
        - apply (cpv_region_kept_win SEGS _ (w_H W) mm41 mem241 12 want).
          + rewrite E12. apply unsigned_lit_small. lia.
          + intros a Ha. apply HK241; unfold ESTACK; lia.
          + intros a Ha. lia. }
      clear HS. rewrite <- restrict_mkst_fx in HSc41. rename HSc41 into HS.
      lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
        assert (A4441 : ew En 44 = Z_to_bv 64 0)
          by (change 44%nat with (40 + 4)%nat;
              rewrite (ew_havoc_new _ 40 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia);
              cbn [nth map]; exact A041) end.
      lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
        assert (HEIc41 : img_env VAL A_LIM (havoc Eo kk ws))
          by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
      cpv_reenv HAE 40%nat.
      clear SHOK. lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
        assert (SHOK : sh_ok SEGS Bxp [] En (mrestrict (w_H W) mem241)) by constructor end.
      assert (KEPT41 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
        rdW W mem241 a = rdW W mem a)
        by (intros a Ha Hn; etransitivity; [apply HK241; unfold ESTACK; lia | apply KEPT40; lia]).
      assert (AG41 : cpv_agree (rdW W mem) (rdW W mem241) (sp0 - STK_check_provenance))
        by (intros a Ha; apply KEPT41; lia).
      clear HJ. rename HJ241 into HJ.
      (* bnez a0 right after the call: the wrapper answered 0, so the abort arm is not taken *)
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { cpv_cond HBc41. exfalso. rewrite branch_ne_U in HBc41. apply negb_true_iff in HBc41.
        apply Z.eqb_neq in HBc41. apply HBc41. rewrite (U_atom _ 44 0 A4441) by lia. reflexivity. }
      cpv_cond HBc41. clear HBc41.
      (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
      paj_run_tok RUN HS HJ SHOK CPspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN42.
      clear HF HFr HG. cpv_reenv HAE 1024%nat.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
        assert (KEPT42 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
          rdW W (ms_mem msx) a = rdW W mem a)
          by (intros a Ha Hn; etransitivity; [apply UN42; lia | apply KEPT41; lia]) end.
      clear UN42.
      prreg HS (1%bv : bv 5) RR42.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
      split; [cbn [ms_regs]; rewrite RR42, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
      split.
      { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT42; lia. }
      unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
      exists (st_fs S). destruct S; reflexivity.
    }
    {
      (* ignore_set = 0: the ignore_file answer is NULL and the mask is 0 *)
      destruct oif as [si|]; cbn [same_text] in SAME2; [discriminate SAME2|].
      cbn [sa_ostr] in OS2.
      psrr_branch_tok RUN BR HS SHOK CPspan.
      { (* 0x8736c beq s0,a2 taken *)
        cpv_cond HBz43. clear HBz43.
        (* 0x87384 .. 0x87398: restore ra / s0 / s1 / s2, addi sp,sp,32, ret *)
        paj_run_tok RUN HS HJ SHOK CPspan.
        { awr_ok_tac. rewrite E2. reflexivity. }
        cpv_kept (@pa_segs _ seg_listing PI) sp0 E2 UN44.
        clear HF HFr HG. cpv_reenv HAE 1024%nat.
        lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
          assert (KEPT44 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK_check_provenance <= a < sp0) ->
            rdW W (ms_mem msx) a = rdW W mem a)
            by (intros a Ha Hn; etransitivity; [apply UN44; lia | apply KEPTs33; lia]) end.
        clear UN44.
        prreg HS (1%bv : bv 5) RR44.
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
        intros mat'. unfold apost_base.
        lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
        split; [cbn [ms_regs]; rewrite RR44, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
        split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
        split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]|].
        split.
        { unfold sa_kept. cbn [ms_mem]. intros a Ha Hn HE. apply KEPT44; lia. }
        unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
        exists (st_fs S). destruct S; reflexivity.
      }
      (* not taken: refuted, igf = 0 and the mask is 0 *)
      cpv_cond HBz43. exfalso. rewrite branch_eq_U in HBz43.
      rewrite (U_atom _ 11 igf E11) in HBz43 by lia.
      rewrite (cpv_mask0 _ 34 0 12 want 156 E34 eq_refl E12 ltac:(lia) ltac:(lia) ltac:(lia)) in HBz43.
      apply Z.eqb_neq in HBz43. exact (HBz43 OS2).
    }
  }
  (* not taken: refuted, rf = 0 and the mask is 0 *)
  cpv_cond HBr32. exfalso. rewrite branch_eq_U in HBr32.
  rewrite (U_atom _ 10 rf E10) in HBr32 by lia.
  rewrite (cpv_mask0 _ 33 0 12 want 60 E33 eq_refl E12 ltac:(lia) ltac:(lia) ltac:(lia)) in HBr32.
  apply Z.eqb_neq in HBr32. exact (HBr32 OS1).
}
Qed.
End f.
End e.
End c.
