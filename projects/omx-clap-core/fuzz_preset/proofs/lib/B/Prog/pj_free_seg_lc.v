(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_free's image-B walk (fuzz_preset asan-ubsan, B 0x86a24; lib/B/Prog/pj_free_defs.v), the
   LOOP's SEATING and the BOUND-TEST segment pfs_LC_holds (lib/B/Prog/pj_free_lcut.v pfs_LC): from the cut pf_LC
   (+0x130) to pf_LH at slot i + 1 (+0xa8) or pf_LX (+0x14c).
     +0x130 lbu a0,0(s6); bnez (ASan check of v+40: decided by the shadow entry mkSHE 8 0 56)
     +0x138 ld a0,0(s2) (n, chunk 40 of v's header, atom 35); s10 += 1; s9 += 8; s8 += 56
     +0x148 bltu s10, a0: taken (i + 1 < n) -> +0xa8, not taken (i + 1 = n) -> +0x14c
   pfl_seat seats the loop's symbolic state at ANY pc from pf_vregs / pf_lregs and v's header words (the other loop
   segments seat with it); pfl_basics gives the kids block, i < 2 ^ 42 and the stack numbers at every loop cut. The
   walk's relation is wle' SEGS RZ_cf (pj_free_defs.v): the R runners (YC1fPx paj_run_xR / paj_run_to_xR,
   YSRrG.paj_branchR) with the journal at it.
   proves no function (kind: segment lemma). Section hypotheses: AR_laws_x at cf_head; ARx_frame_hull_vis (MARKED kit
   fact, YGcfFsVis.v; unused here, kept for the loop files' common Section).
   Numerals: 56 / 40 / 32 / 24 / 16 / 8 (LENGTH: struct pj and its fields, a slot, a key), 2 ^ 42 / 2 ^ 44 / 2 ^ 46 /
   2 ^ 47 / 2 ^ 48 / 4096 (LENGTH: index, shadow span, stack band, node range); atoms 32 .. 35 (DERIVED). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_free_defs pj_free_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_keep pj_free_lcut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- the seated state at the loop head: s0 = v (atom 8), s7 = the shadow offset (atom 23); v's fields as region
   chunks str / kids / keys / n (atoms 32 .. 35); s3 / s1 / s2 = v + 24 / v + 32 / v + 40, s11 / s4 / s6 their ASan
   cells, s5 = 56; s8 / s9 / s10 = 56 i / 8 i / i (atoms 24 .. 26) ---- *)
Definition pfl_cell (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 23 0).
Definition pfl_sregs : list sv :=
  Eval vm_compute in
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    9%bv (SOff 8 32)) 18%bv (SOff 8 40)) 19%bv (SOff 8 24)) 20%bv (pfl_cell (SOff 8 32))) 21%bv (SLit 56))
    22%bv (pfl_cell (SOff 8 40))) 27%bv (pfl_cell (SOff 8 24)).
Definition pfl_vhdr : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 56 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0));
     YP09.mkChunk 32 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 35 0))].
Definition pfl_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 (2 ^ 47 - 64) 3);
           (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 4096 (2 ^ 47 - 4096) 4);
           (24%nat, mkAF 0 (2 ^ 48) 3); (25%nat, mkAF 0 (2 ^ 45) 3); (26%nat, mkAF 0 (2 ^ 42) 0)] [] [].
Definition ss_pfl (pc : Z) : sstate := mkSS pc pfl_sregs [pfl_vhdr] None pfl_facts.
Definition PFL_Bx : sv := SOff 23 0.
Definition PFL_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pfl_SH : list shent := [mkSHE 8 0 56].
Lemma pfl_sregs_eq : pfl_sregs =
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    9%bv (SOff 8 32)) 18%bv (SOff 8 40)) 19%bv (SOff 8 24)) 20%bv (pfl_cell (SOff 8 32))) 21%bv (SLit 56))
    22%bv (pfl_cell (SOff 8 40))) 27%bv (pfl_cell (SOff 8 24)).
Proof. vm_compute. reflexivity. Qed.
Ltac pfl_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E; vm_compute in E; discriminate E.
Lemma pfl_denot_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* the loop's stretches store nothing: every region of their states is read-only *)
Ltac pfl_awr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  unfold awr_ok; intros a (r & Hin & Ha); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |]); destruct Hin.
Ltac pfl_mm HF M :=
  lazymatch type of HF with frame_of _ _ ?m ?m' =>
    assert (M : m' = m);
    [ apply functional_extensionality; let x := fresh "x" in intros x; apply HF;
      let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
      intros (r & Hin & Ha); vm_compute in Hin;
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |]); destruct Hin
    | ] end.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VISF : ARx_frame_hull_vis SEGS B ARx.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the loop's environment: the registers, then v's str / kids / keys / n as atoms 32 .. 35 *)
Definition PFL_E (regs : bvmap 5 word) (nd : PfNode) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)]).

(* ---- seating the loop's symbolic state at any pc of the loop, from the loop's registers at slot i ---- *)
Lemma pfl_seat : forall en nd i (W : world SEGS) regs mem pc,
  pf_vregs en regs -> pf_lregs en regs i ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  4096 <= fe_v en <= 2 ^ 47 - 64 -> fe_v en mod 8 = 0 ->
  rd_u64 SEGS (rdW W mem) (fe_v en + 16) (fn_str nd) -> rd_u64 SEGS (rdW W mem) (fe_v en + 24) (fn_kids nd) ->
  rd_u64 SEGS (rdW W mem) (fe_v en + 32) (fn_keys nd) -> rd_u64 SEGS (rdW W mem) (fe_v en + 40) (fn_n nd) ->
  4096 <= fn_kids nd <= 2 ^ 47 - 4096 -> fn_kids nd mod 16 = 0 -> 0 <= i < 2 ^ 42 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fe_v en) 56 -> amem_range (fe_v en) 56 ->
  st_ok_pi SEGS VAL (PFL_E regs nd) (ss_pfl pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PFL_Bx pfl_SH (PFL_E regs nd) (mrestrict (w_H W) mem).
Proof.
intros en nd i W regs mem pc HVR HLR Hsp Hal Hv Hv8 Hstr Hkids Hkeys Hnn Hkr Hk16 Hi Hra Hamr.
pose proof HVR as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HLR as (R20 & R21 & R24 & R25 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v := fe_v en) in *.
set (E := PFL_E regs nd).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFL_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFL_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = v + c).
{ intros c Hc. apply (U_atom_off E 8 v c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U23 : U E (SOff 23 0) = SHADOW_OFF).
{ apply (U_atom E 23 SHADOW_OFF); [rewrite (Er 23%nat 23%bv) by (first [lia | reflexivity]); exact R23 | unfold SHADOW_OFF; lia]. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Er 2%nat 2%bv) by (first [lia | reflexivity]); reflexivity).
assert (Uv : bv_unsigned (ew E 8) = v).
{ rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]). rewrite R8. apply unsigned_lit_small. lia. }
assert (Hcell : forall c, 0 <= c <= 56 -> U E (pfl_cell (SOff 8 c)) = (v + c) / 8 + SHADOW_OFF).
{ intros c Hc. unfold pfl_cell. apply pfg_U_cell; [apply U8; lia | exact U23 | lia]. }
split.
- rewrite restrict_mkst_fx. unfold ss_pfl. apply pa_entry_st_ok_full.
  + rewrite pfl_sregs_eq.
    apply regs_ok_pin; [|pfl_regne|rewrite R27, pfl_denot_U, Hcell by lia; reflexivity].
    apply regs_ok_pin; [|pfl_regne|rewrite R22, pfl_denot_U, Hcell by lia; reflexivity].
    apply regs_ok_pin; [|pfl_regne|rewrite R21, pfl_denot_U, U_SLit; reflexivity].
    apply regs_ok_pin; [|pfl_regne|rewrite R20, pfl_denot_U, Hcell by lia; reflexivity].
    apply regs_ok_pin; [|pfl_regne|rewrite R19, pfl_denot_U, U8 by lia; reflexivity].
    apply regs_ok_pin; [|pfl_regne|rewrite R18, pfl_denot_U, U8 by lia; reflexivity].
    apply regs_ok_pin; [|pfl_regne|rewrite R9, pfl_denot_U, U8 by lia; reflexivity].
    unfold E, PFL_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pfl_vhdr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uv.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 32 0) (fn_str nd));
        [rewrite pfl_denot_U, (U_atom E 32 (fn_str nd)); [reflexivity | exact (EX 0%nat ltac:(lia)) | exact (proj1 Hstr)]
        | cbn; exact (proj1 Hstr) | cbn; lia | exact (proj2 Hstr)].
    * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 33 0) (fn_kids nd));
        [rewrite pfl_denot_U, (U_atom E 33 (fn_kids nd)); [reflexivity | exact (EX 1%nat ltac:(lia)) | exact (proj1 Hkids)]
        | cbn; exact (proj1 Hkids) | cbn; lia | exact (proj2 Hkids)].
    * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 34 0) (fn_keys nd));
        [rewrite pfl_denot_U, (U_atom E 34 (fn_keys nd)); [reflexivity | exact (EX 2%nat ltac:(lia)) | exact (proj1 Hkeys)]
        | cbn; exact (proj1 Hkeys) | cbn; lia | exact (proj2 Hkeys)].
    * apply (chunk_ok_val SEGS E _ _ 40 8 (SOff 35 0) (fn_n nd));
        [rewrite pfl_denot_U, (U_atom E 35 (fn_n nd)); [reflexivity | exact (EX 3%nat ltac:(lia)) | exact (proj1 Hnn)]
        | cbn; exact (proj1 Hnn) | cbn; lia | exact (proj2 Hnn)].
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    unfold pfl_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uv.
    rewrite (Er 23%nat 23%bv), (Er 24%nat 24%bv), (Er 25%nat 25%bv), (Er 26%nat 26%bv) by (first [lia | reflexivity]).
    pose proof (EX 1%nat ltac:(lia)) as X1. change (32 + 1)%nat with 33%nat in X1. cbn [nth] in X1.
    rewrite R23, R24, R25, R26, X1. unfold w64.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hal; try exact Hv8; try lia.
    all: Z.div_mod_to_equations; lia.
- unfold sh_ok, pfl_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E PFL_Bx 8 v 56 v 0 56 Hra).
  + unfold PFL_Bx. exact U23.
  + rewrite U8 by lia. lia.
  + lia. + lia.
  + intros x Hx. unfold amem_range in Hamr. unfold SHADOW_OFF in *. lia.
Qed.
(* ---- what every loop cut gives: the kids block holds the n slots, the slot index and the stack numbers ---- *)
Lemma pfl_basics : forall PB FX CTX0 en nd i ly S Hp W regs mem md k,
  pf_pre B ARx PB FX CTX0 en -> pf_node en nd -> 0 <= i < fn_n nd ->
  pf_frameR (SK := SK) B ARx (wle' SEGS RZ_cf) en ly S Hp W regs mem md k ->
  (exists kk, In (fn_kids nd, kk) (fe_Lam en) /\ 56 * fn_n nd <= kk /\ fn_Dk nd = [(fn_kids nd, kk)] /\
     4096 <= fn_kids nd /\ fn_kids nd + kk <= YM05.alloc_ceiling /\ fn_kids nd mod 16 = 0) /\
  0 <= i < 2 ^ 42 /\ spZ regs = fe_sp0 en - 128 /\ 2 ^ 46 <= spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0 /\
  YM05.alloc_ceiling <= fe_sp0 en.
Proof.
intros PB FX CTX0 en nd i ly S Hp W regs mem md k HPRE HND Hi HFR.
pose proof HFR as (_ & _ & Hsp & _).
pose proof HPRE as (HFPRE0 & _ & _ & _ & _ & _ & _ & HLED0).
pose proof HFPRE0 as (HAFN0 & _ & _).
pose proof HAFN0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _ & _ & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HND as (_ & _ & _ & _ & HKIDSn & _).
pose proof (YM05.alloc_ceiling_value) as HAC0.
pose proof (@cf_head_nonneg cp) as Hc0.
pose proof (pfg_stk (fe_n en)) as ESTK.
assert (Hkk : exists kk, In (fn_kids nd, kk) (fe_Lam en) /\ 56 * fn_n nd <= kk /\ fn_Dk nd = [(fn_kids nd, kk)] /\
  4096 <= fn_kids nd /\ fn_kids nd + kk <= YM05.alloc_ceiling /\ fn_kids nd mod 16 = 0).
{ destruct HKIDSn as [(_ & Hn0 & _) | (kk & Hin & Hkn & HDk)]; [lia|].
  destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HLED0 Hin) as (Hk0 & Ha0 & Hak & Ha16 & _).
  exists kk. repeat split; first [assumption | lia]. }
split; [exact Hkk|].
destruct Hkk as (kk & _ & Hkkn & _ & Hkid4 & Hkidc & _).
assert (Hsp1 : spZ regs = fe_sp0 en - 128) by (rewrite Hsp; unfold fe_sp1, PJF_FR; lia).
unfold fe_sp0 in *. rewrite ESTK in *.
split; [lia|]. split; [exact Hsp1|]. split; [lia|]. split; [rewrite Hsp1; Z.div_mod_to_equations; lia|]. lia.
Qed.

(* ---- a stretch that stores nothing and keeps sp, gp, tp keeps pj_free's frame ---- *)
Lemma pfl_frame_same : forall en ly S Hp W regs regs' mem md md' k,
  pf_frameR (SK := SK) B ARx (wle' SEGS RZ_cf) en ly S Hp W regs mem md k ->
  ajournal_xR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en)
    (fe_FP en) (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  pf_frameR (SK := SK) B ARx (wle' SEGS RZ_cf) en ly S Hp W regs' mem md' k.
Proof.
intros en ly S Hp W regs regs' mem md md' k (HJ & HW & Hsp & HSV & HP & H3 & H4 & HR) HJ' E2 E3 E4.
split; [exact HJ'|]. split; [exact HW|]. split; [unfold spZ; rewrite E2; exact Hsp|]. split; [exact HSV|].
split; [exact HP|]. split; [rewrite E3; exact H3|]. split; [rewrite E4; exact H4 | exact HR].
Qed.

(* ---- THE BOUND TEST: +0x130 .. `bltu s10, a0` (+0x148) -> pf_LH (i + 1) or pf_LX ---- *)
Theorem pfs_LC_holds : forall PB FX CTX0 d', pfs_LC (SK := SK) B ARx PB FX CTX0 d'.
Proof.
intros PB FX CTX0 d' en nd i ly S Hp W regs mem md k HPRE HND HLC KLH KLX.
pose proof HLC as (En & Hi & HFR & HSP & HVR & HLR & Fd & Lam & Dr & Fr & HAC & HVN & HPD & HIT).
pose proof HFR as (HJ & _).
pose proof HVR as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HLR as (R20 & R21 & R24 & R25 & R26 & R27).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
destruct (pfl_basics PB FX CTX0 en nd i ly S Hp W regs mem md k HPRE HND Hi HFR)
  as ((kk & Hkkin & Hkkn & HDk & Hkid4 & Hkidc & Hkid16) & Hi42 & Hsp1 & Hspr & Hal & Hceil0).
pose proof (YM05.alloc_ceiling_value) as HAC0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pfl_seat en nd i W regs mem PJF_LC HVR HLR Hspr Hal ltac:(lia) Hv8 Hstr Hkids Hkeys Hnn
  ltac:(lia) Hkid16 Hi42 Hvra Hamr) as [HS SHOK].
set (E := PFL_E regs nd) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, PFL_E; apply Eimg_env).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFL_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFL_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (HAE : env_agree 32 (Ereg regs [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)]) E)
  by (unfold E, PFL_E; split; [intros n0 Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Ui : U E (SOff 26 0) = i).
{ apply (U_atom E 26 i); [rewrite (Er 26%nat 26%bv) by (first [lia | reflexivity]); exact R26 | lia]. }
assert (Un : U E (SOff 35 0) = fn_n nd).
{ pose proof (EX 3%nat ltac:(lia)) as X3. change (32 + 3)%nat with 35%nat in X3. cbn [nth] in X3.
  apply (U_atom E 35 (fn_n nd)); [exact X3 | exact (proj1 Hnn)]. }
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = fe_v en + c).
{ intros c Hc. apply (U_atom_off E 8 (fe_v en) c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U23 : U E (SOff 23 0) = SHADOW_OFF).
{ apply (U_atom E 23 SHADOW_OFF); [rewrite (Er 23%nat 23%bv) by (first [lia | reflexivity]); exact R23 | unfold SHADOW_OFF; lia]. }
assert (Ucell : forall c, 0 <= c <= 56 -> U E (pfl_cell (SOff 8 c)) = (fe_v en + c) / 8 + SHADOW_OFF).
{ intros c Hc. unfold pfl_cell. apply pfg_U_cell; [apply U8; lia | exact U23 | lia]. }
assert (U24 : U E (SOff 24 56) = 56 * (i + 1)).
{ rewrite (U_atom_off E 24 (56 * i) 56); [lia | rewrite (Er 24%nat 24%bv) by (first [lia | reflexivity]); exact R24 | lia | lia]. }
assert (U25 : U E (SOff 25 8) = 8 * (i + 1)).
{ rewrite (U_atom_off E 25 (8 * i) 8); [lia | rewrite (Er 25%nat 25%bv) by (first [lia | reflexivity]); exact R25 | lia | lia]. }
assert (U26 : U E (SOff 26 1) = i + 1).
{ apply (U_atom_off E 26 i 1); [rewrite (Er 26%nat 26%bv) by (first [lia | reflexivity]); exact R26 | lia | lia]. }
unfold pf_cfg, SRr'.
set (R := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose (RUN := @paj_run_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS R Rr Rt).
pose (RUNTO := @paj_run_to_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS R Rr Rt).
pose (BR := paj_branchR (fx := fx) (rc := rc) (L := B_prog_listing) (PI := PA) R).
(* +0x130 .. +0x144: the ASan check of v+40, n, i += 1, 8 i += 8, 56 i += 56; stop at `bltu s10, a0` *)
paj_run_tok_x RUN HS HJ SHOK PFL_Bspan; [pfl_awr|].
pfl_mm HF M1. clear HF HFr. rename HG into G1.
psrr_branch_tok RUN BR HS SHOK PFL_Bspan.
- (* taken: i + 1 < n, to the loop head at slot i + 1 *)
  assert (Hlt : i + 1 < fn_n nd).
  { rewrite branch_ltu_U, U26, Un in Hc. apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok_x RUNTO HS HJ SHOK PFL_Bspan PJF_LH; [pfl_awr|].
  pfl_mm HF M2. clear HF HFr. rename HG into G2.
  pfg_reg HS (9%bv : bv 5) Q9. pfg_reg HS (18%bv : bv 5) Q18. pfg_reg HS (19%bv : bv 5) Q19.
  pfg_reg HS (20%bv : bv 5) Q20. pfg_reg HS (21%bv : bv 5) Q21. pfg_reg HS (22%bv : bv 5) Q22.
  pfg_reg HS (24%bv : bv 5) Q24. pfg_reg HS (25%bv : bv 5) Q25. pfg_reg HS (26%bv : bv 5) Q26.
  pfg_reg HS (27%bv : bv 5) Q27.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ [2%bv; 3%bv; 4%bv; 8%bv; 23%bv] HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  rewrite M2, M1 in HJ |- *.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?pc)) _ _; cfg_model := ?dd |} _ =>
    replace pc with PJF_LH by (vm_compute; reflexivity);
    apply (KLH ly S Hp W rg mem dd k) end.
  split; [exact En|]. split; [lia|].
  split; [apply (pfl_frame_same en ly S Hp W regs _ mem md _ k HFR HJ); apply KR; cbn [In]; tauto|].
  split; [exact HSP|].
  split.
  { unfold pf_vregs. unfold w64.
    split; [rewrite (KR 8%bv) by (cbn [In]; tauto); exact R8|].
    split; [apply (pfg_reg_of_U E _ _ _ Q9); apply U8; lia|].
    split; [apply (pfg_reg_of_U E _ _ _ Q18); apply U8; lia|].
    split; [apply (pfg_reg_of_U E _ _ _ Q19); apply U8; lia|].
    split; [rewrite (KR 23%bv) by (cbn [In]; tauto); exact R23|].
    apply (pfg_reg_of_U E _ _ _ Q22). apply (Ucell 40); lia. }
  split.
  { unfold pf_lregs. unfold w64.
    split; [apply (pfg_reg_of_U E _ _ _ Q20); apply (Ucell 32); lia|].
    split; [apply (pfg_reg_of_U E _ _ _ Q21); rewrite U_SLit; reflexivity|].
    split; [apply (pfg_reg_of_U E _ _ _ Q24); exact U24|].
    split; [apply (pfg_reg_of_U E _ _ _ Q25); exact U25|].
    split; [apply (pfg_reg_of_U E _ _ _ Q26); exact U26|].
    apply (pfg_reg_of_U E _ _ _ Q27). apply (Ucell 24); lia. }
  exists Fd, Lam, Dr, Fr. split; [exact HAC|]. split; [exact HVN|]. split; [exact HPD | exact HIT].
- (* not taken: i + 1 = n, after the loop *)
  assert (Hge : fn_n nd <= i + 1).
  { rewrite branch_ltu_U, U26, Un in Hc. apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok_x RUNTO HS HJ SHOK PFL_Bspan PJF_LX; [pfl_awr|].
  pfl_mm HF M2. clear HF HFr. rename HG into G2.
  pfg_reg HS (9%bv : bv 5) Q9. pfg_reg HS (18%bv : bv 5) Q18. pfg_reg HS (19%bv : bv 5) Q19.
  pfg_reg HS (22%bv : bv 5) Q22.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ [2%bv; 3%bv; 4%bv; 8%bv; 23%bv] HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  rewrite M2, M1 in HJ |- *.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?pc)) _ _; cfg_model := ?dd |} _ =>
    replace pc with PJF_LX by (vm_compute; reflexivity);
    apply (KLX ly S Hp W rg mem dd k) end.
  replace (Z.to_nat (fn_n nd - (i + 1))) with O in HIT by lia. destruct HIT as [-> ->].
  split; [apply (pfl_frame_same en ly S Hp W regs _ mem md _ k HFR HJ); apply KR; cbn [In]; tauto|].
  split; [exact HSP|].
  split.
  { unfold pf_vregs. unfold w64.
    split; [rewrite (KR 8%bv) by (cbn [In]; tauto); exact R8|].
    split; [apply (pfg_reg_of_U E _ _ _ Q9); apply U8; lia|].
    split; [apply (pfg_reg_of_U E _ _ _ Q18); apply U8; lia|].
    split; [apply (pfg_reg_of_U E _ _ _ Q19); apply U8; lia|].
    split; [rewrite (KR 23%bv) by (cbn [In]; tauto); exact R23|].
    apply (pfg_reg_of_U E _ _ _ Q22). apply (Ucell 40); lia. }
  exists Fd, Lam. split; [exact HAC|]. split; [exact HVN|]. exact HPD.
Qed.

End l.
