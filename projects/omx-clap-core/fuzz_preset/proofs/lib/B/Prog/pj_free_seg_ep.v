(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_free's image-B walk (fuzz_preset asan-ubsan, B 0x86a24; lib/B/Prog/pj_free_defs.v), the
   EPILOGUE segment: from the cut pf_EP (+0x1a8) to the walk's goal pf_FIN.
     +0x1a8 .. +0x1d8  ld ra, s0, s1, s2 .. s11 from sp+120 .. sp+24 (13 loads)
     +0x1dc            addi sp, sp, 128
     +0x1e0            ret
   HOW: one engine stretch (YC80x / YC1fPx paj_run_tok_x with the R runner paj_run_xR at the walk's relation
   wle' SEGS RZ_cf, over YCbqG's ajournal_xR) from a symbolic state seated at the cut: the frame [sp, sp + 128)
   read-only, the 13 saved words as atoms 32 .. 44 (the entry's ra, s0 .. s11), then YC1fP's paj_ret_at, lifted into
   the relation by YA0nH.SRr_SRrG. The run stores nothing, so the memory is the cut's; the post is the cut's pf_Q (it
   reads no register and no model); the journal is the cut's (materialised); every callee-saved register is the
   entry's.
   proves no function (kind: segment lemma).
   Numerals: 128 / 120 .. 24 (LENGTH: the frame and its slots, PJF_SAVED); 2 ^ 46 / 2 ^ 47 (LENGTH: the stack band);
   atom numbers 32 .. 45 (DERIVED: the first atoms after the registers). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Existing Instance prh_img_B.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at pf_EP: the frame read-only, the 13 saved words as atoms 32 .. 44 ---- *)
Definition PFE_chunks : list YP09.chunk :=
  [YP09.mkChunk 120 (CVal 8 (SOff 32 0)); YP09.mkChunk 112 (CVal 8 (SOff 33 0));
   YP09.mkChunk 104 (CVal 8 (SOff 34 0)); YP09.mkChunk 96 (CVal 8 (SOff 35 0));
   YP09.mkChunk 88 (CVal 8 (SOff 36 0)); YP09.mkChunk 80 (CVal 8 (SOff 37 0));
   YP09.mkChunk 72 (CVal 8 (SOff 38 0)); YP09.mkChunk 64 (CVal 8 (SOff 39 0));
   YP09.mkChunk 56 (CVal 8 (SOff 40 0)); YP09.mkChunk 48 (CVal 8 (SOff 41 0));
   YP09.mkChunk 40 (CVal 8 (SOff 42 0)); YP09.mkChunk 32 (CVal 8 (SOff 43 0));
   YP09.mkChunk 24 (CVal 8 (SOff 44 0))].
Definition PFE_regions : smem := [YP09.mkRegion (Some 2%nat) 0 128 0 0 PFE_chunks].
Definition PFE_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition PFE_ss : sstate := mkSS PJF_EP sr_atoms PFE_regions None PFE_facts.
Definition PFE_Bx : sv := SOff 45 0.
Definition PFE_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition PFE_SH : list shent := [].
(* the entry's saved registers, in PJF_SAVED's order *)
Definition PFE_extra (r0 : bvmap 5 word) : list word := map (fun ro => getr r0 (Z_to_bv 5 (fst ro))) PJF_SAVED.

Section ep. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* one saved word as a chunk of the frame region *)
Lemma pfe_chunk : forall (E : env) (mem : word -> option byte) (base o : Z) (j : nat) (w : word),
  ew E (32 + j) = w -> val_mem SEGS mem (base + o) 8 (bv_unsigned w) ->
  YP09.chunk_ok SEGS E mem base (YP09.mkChunk o (CVal 8 (SOff (32 + j) 0))).
Proof.
intros E mem base o j w Hw Hv.
apply (chunk_ok_val SEGS E mem base o 8 (SOff (32 + j) 0) (bv_unsigned w)).
- cbn [sv_denot]. rewrite Hw, Z.add_0_r. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
- cbn. lia.
- exact Hv.
Qed.

Lemma pfe_st_ok : forall (W : world SEGS) mem (regs r0 : bvmap 5 word),
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  (forall r o, In (r, o) PJF_SAVED ->
     val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + o) 8 (bv_unsigned (getr r0 (Z_to_bv 5 r)))) ->
  st_ok_pi SEGS VAL (Eimg (PI := PA) (Ereg regs (PFE_extra r0))) PFE_ss
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + PJF_EP)) mem (seg_rom SEGS))).
Proof.
intros W mem regs r0 Hsp Hal HV.
set (E := Eimg (PI := PA) (Ereg regs (PFE_extra r0))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (PFE_extra r0)) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (PFE_extra r0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
rewrite restrict_mkst_fx. unfold PFE_ss.
apply (pa_entry_st_ok_full (PI := PA)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold PFE_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold PFE_chunks.
  repeat (apply Forall_cons;
    [ lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?n 0))) =>
        let j := eval vm_compute in (n - 32)%nat in
        change n with (32 + j)%nat;
        eapply (pfe_chunk E _ _ o j); [rewrite (EX j) by lia; cbn [nth PFE_extra map PJF_SAVED fst]; reflexivity |];
        apply HV; cbn [PJF_SAVED In]; tauto end |]).
  apply Forall_nil.
- cbn [PFE_regions pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [PFE_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal | lia].
Qed.
(* the saved word at atom N, as the entry's register *)
Ltac pfe_ex EX :=
  lazymatch goal with |- context [ew ?E ?N] =>
    let j := eval vm_compute in (N - 32)%nat in
    let H := fresh "X" in pose proof (EX j ltac:(lia)) as H; change (32 + j)%nat with N in H; rewrite H; clear H
  end.

Theorem pfs_EP_holds : forall FX, pfs_EP (SK := SK) B ARx FX.
Proof.
intros FX PB CTX0 en ly S Hp W regs mem md k HPRE [HFR HQ].
pose proof HFR as (HJ & HWIN & Hsp & HSV & _ & H3 & H4 & _ & HMN).
destruct HPRE as ((HAFN & _ & _) & _).
pose proof HAFN as (_ & Hret & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
unfold fe_sp1, fe_sp0, PJF_FR in *.
assert (Hsp1 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hal1 : spZ regs mod 16 = 0) by (rewrite Hsp; Z.div_mod_to_equations; lia).
pose proof (pfe_st_ok W mem regs (fe_regs en) Hsp1 Hal1 ltac:(intros r o Hro; rewrite Hsp; exact (HSV r o Hro))) as HS.
set (E := Eimg (PI := PA) (Ereg regs (PFE_extra (fe_regs en)))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (PFE_extra (fe_regs en))) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (PFE_extra (fe_regs en)) (Z_to_bv 64 0)).
{ intros j Hj. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (PFE_extra (fe_regs en))) E)
  by (split; [intros n Hn; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS PFE_Bx PFE_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok, PFE_SH; apply Forall_nil).
clearbody E.
unfold pf_cfg, SRr'.
set (R := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose (RUN := paj_run_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS R Rr Rt).
pose (RET := paj_ret_at (PL := PL) (PI := PA)).
(* +0x1a8 .. +0x1dc: the 13 loads and the addi; the runner stops at the ret *)
paj_run_tok_x RUN HS HJ SHOK PFE_Bspan.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold PFE_ss, PFE_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
(* the run stored nothing: the memory is the cut's *)
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  unfold PFE_ss, PFE_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (Z_to_bv 5 8) R8. prreg HS (Z_to_bv 5 9) R9.
prreg HS (Z_to_bv 5 18) R18. prreg HS (Z_to_bv 5 19) R19. prreg HS (Z_to_bv 5 20) R20.
prreg HS (Z_to_bv 5 21) R21. prreg HS (Z_to_bv 5 22) R22. prreg HS (Z_to_bv 5 23) R23.
prreg HS (Z_to_bv 5 24) R24. prreg HS (Z_to_bv 5 25) R25. prreg HS (Z_to_bv 5 26) R26.
prreg HS (Z_to_bv 5 27) R27.
assert (KR : forall r, In r [3%bv; 4%bv] -> getr (ms_regs ms) r = getr regs r).
{ exact (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs (PFE_extra (fe_regs en)) [3%bv; 4%bv] HS HAE
    ltac:(vm_compute; reflexivity)). }
(* +0x1e0: the ret, to the entry's ra (a step keeps the world: the plain fact lifts into R) *)
apply (SRr_SRrG SEGS R (wle_wle' SEGS RZ_cf)).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold pf_FIN, fpostWmR, fpostWR.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (YK11.mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists ly, S, Hp, r, m, d, k end.
split.
{ unfold YK0s.ret_ok in Hret. rewrite R1. pfe_ex EX. cbn [nth PFE_extra map PJF_SAVED fst].
  replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Hret. reflexivity. }
split; [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs R); exact HJ|].
split; [intros a Ha Hn; rewrite MM; exact (HWIN a Ha Hn)|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | Hr']]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R2, Usp, Hsp. replace (spZ (fe_regs en) - 128 + 128) with (spZ (fe_regs en)) by lia.
    unfold spZ. apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite (KR 3%bv) by (left; reflexivity). exact H3.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite (KR 4%bv) by (right; left; reflexivity). exact H4.
  - repeat (destruct Hr' as [-> | Hr']); try subst r;
    first [ rewrite R8 | rewrite R9 | rewrite R18 | rewrite R19 | rewrite R20 | rewrite R21 | rewrite R22
          | rewrite R23 | rewrite R24 | rewrite R25 | rewrite R26 | rewrite R27 ]; pfe_ex EX;
    cbn [nth PFE_extra map PJF_SAVED fst]; reflexivity. }
rewrite MM. split; [exact HQ | exact HMN].
Qed.

End ep.
