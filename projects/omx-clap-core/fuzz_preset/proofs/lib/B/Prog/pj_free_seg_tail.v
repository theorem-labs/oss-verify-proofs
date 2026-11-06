(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_free's image-B walk (fuzz_preset asan-ubsan, B 0x86a24; lib/B/Prog/pj_free_defs.v), the
   TAIL segment: from the cut pf_LX (+0x14c) to the cut pf_EP (+0x1a8), then the epilogue segment.
     +0x14c .. +0x160  ASan check of the cell of v+24 (spilled at sp+8); kids := v->kids; jal fuzz_free
     +0x164 .. +0x178  ASan check of the cell of v+32 (spilled at sp+16); keys := v->keys; jal fuzz_free
     +0x17c .. +0x194  ASan check of the cell of v+16; str := v->str; jal fuzz_free
     +0x198 .. +0x1a4  memset (v, 0, 56) by jal __asan_memset; returns to +0x1a8 = pf_EP
   HOW: four engine stretches (YC80x / YC1fPx paj_run_tok_x with the R runner paj_run_xR at the walk's relation
   wle' SEGS RZ_cf, pj_free_defs.v, over YCbqG's ajournal_xR), each seated fresh at the frame
   read-only (sp+8 / sp+16, the spilled shadow indices) and v's header (str / kids / keys as atoms 32 .. 34), with
   s7's shadow offset as atom 23 and the shadow entry of v's 56 bytes: the engine decides the three ASan checks
   itself. Each of the three calls goes through YCbqGcallW.v aj_call_xW_spR at the callee window e1 = 0 with
   fuzz_free's instrumented text (lib/A/Prog/PjFreeCommon.v tfuzz_free_specO, m-form: it concludes SRr' SEGS RZ_cf, its
   post fpostmR at that relation), and the memset through YGcallMxmn.v aj_intrin_at_xm_frR (a plain step fact, lifted
   into the relation by YA0nH.SRr_SRrG); what the calls keep is pj_free_keep.v's (pfk_frame, pfk_vnode,
   pfk_acct_free / pfk_acct_null).
   proves no function (kind: segment lemma).
   Section hypotheses: AR_laws_x (the engine), ARx_frame_hull_vis (the kit's MARKED fact), PRH_Base.v's
   prh_head_wide (8 <= cf_head: at cf_head = 0 the memset of v's 56 bytes would overwrite the ledger head word of
   the live harness block that holds v, and pf_K0post's ledger would be false; the instance's cf_head is 16).
   Numerals: 128 / 120 .. 24 / 8 / 16 (LENGTH: the frame and its slots), 56 / 40 / 32 / 24 / 16 (LENGTH: struct pj
   and its fields), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 47 - 64 / 4096 (LENGTH: shadow span, stack band, the node's
   range); atoms 32 .. 34 (DERIVED: the first atoms after the registers); every pc offset is DERIVED. No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_free_defs pj_free_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_keep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- the return sites of the tail's three calls (DERIVED: PJF_PC + the listing's slot differences) ---- *)
Definition PFT_R1 : Z := PJF_PC + 356.     (* +0x164, after `jal fuzz_free` (kids) *)
Definition PFT_R2 : Z := PJF_PC + 380.     (* +0x17c, after `jal fuzz_free` (keys) *)
Definition PFT_R3 : Z := PJF_PC + 408.     (* +0x198, after `jal fuzz_free` (str) *)

(* ---- the symbolic state of every tail stretch: the frame's two spilled shadow indices read-only, v's header
   (str / kids / keys as atoms 32 .. 34), s3 = v + 24, s7's shadow offset (atom 23), v's 56 bytes addressable ---- *)
Definition pft_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 24 0 0
    [YP09.mkChunk 8 (CVal 8 (SAlu ALU_SRL (SOff 8 24) (SLit 3)));
     YP09.mkChunk 16 (CVal 8 (SAlu ALU_SRL (SOff 8 32) (SLit 3)))].
Definition pft_vhdr : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 56 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0));
     YP09.mkChunk 32 (CVal 8 (SOff 34 0))].
Definition pft_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 (2 ^ 47 - 64) 3);
           (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition pft_sregs : list sv := sr_set sr_atoms 19%bv (SOff 8 24).
Definition pft_ss (pc : Z) : sstate := mkSS pc pft_sregs [pft_frame; pft_vhdr] None pft_facts.
Definition PFT_Bx : sv := SOff 23 0.
Definition PFT_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pft_SH : list shent := [mkSHE 8 0 56].

Section tl. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VISF : ARx_frame_hull_vis SEGS B ARx.
Hypothesis HEAD8 : prh_head_wide.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the environment of a tail stretch: the registers, then v's header words as atoms 32 .. 34 *)
Definition pft_E (regs : bvmap 5 word) (nd : PfNode) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd)]).

(* ---- what holds at every tail cut: the frame (at wle' SEGS RZ_cf), the spills, v's registers, and the blocks still
   to free ---- *)
Definition pft_inv (FX : pf_obs) (en : PfEnt) (nd : PfNode) (R : list (Z * Z))
  (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  pf_frameR (SK := SK) B ARx (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_spill en W mem /\ pf_vregs en regs /\
  exists Fd Lam,
    pf_acct B FX en ly S Hp W mem Fd R Lam /\
    pf_vnode B en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ R).

(* ---- the stack numbers of the walk, from the entry's premises ---- *)
Lemma pft_nums : forall PB FX CTX0 en, pf_pre B ARx PB FX CTX0 en ->
  fe_sp1 en mod 16 = 0 /\ 2 ^ 46 <= fe_sp1 en /\ fe_sp1 en <= 2 ^ 47 /\
  YM05.alloc_ceiling + 16416 <= fe_sp1 en /\ 0 <= fe_d en /\ fe_d en mod 16 = 0 /\
  fe_sp0 en + fe_d en <= ly_top (fe_ly en) /\ fe_sp0 en + 64 <= ly_stk_hi (fe_ly en).
Proof.
intros PB FX CTX0 en HPRE.
pose proof HPRE as (HFPRE & _ & _ & _ & HWIN & _).
pose proof HFPRE as (HAFN & _ & HSTKHI & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pfg_stk (fe_n en)) as ESTK.
assert (HN1 : 1 <= Z.of_nat (S (fe_n en))) by lia.
unfold fe_sp1, fe_sp0, PJF_FR in *.
repeat split; lia.
Qed.

(* ---- the callee-saved registers the tail reads, across a call ---- *)
Lemma pft_pres : forall (r r' : bvmap 5 word), aregs_preserved r r' ->
  getr r' 2 = getr r 2 /\ getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4 /\ getr r' 8 = getr r 8 /\
  getr r' 9 = getr r 9 /\ getr r' 18 = getr r 18 /\ getr r' 19 = getr r 19 /\ getr r' 22 = getr r 22 /\
  getr r' 23 = getr r 23.
Proof.
intros r r' H.
assert (K : forall z (b : bv 5), acallee_saved z -> Z_to_bv 5 z = b -> getr r' b = getr r b)
  by (intros z b Hz <-; exact (H z Hz)).
repeat split.
- apply (K 2); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 3); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 4); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 8); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 9); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 18); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 19); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 22); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
- apply (K 23); [unfold acallee_saved; lia | apply bv_eq; reflexivity].
Qed.

(* ---- THE SEATED STATE of a tail stretch ---- *)
Lemma pft_seat : forall pc en nd ly S Hp W regs mem md k Lam PB FX CTX0,
  pf_pre B ARx PB FX CTX0 en ->
  pf_frameR (SK := SK) B ARx (wle' SEGS RZ_cf) en ly S Hp W regs mem md k -> pf_spill en W mem -> pf_vregs en regs ->
  pf_vnode B en nd ly S Lam W mem ->
  st_ok_pi SEGS VAL (pft_E regs nd) (pft_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PFT_Bx pft_SH (pft_E regs nd) (mrestrict (w_H W) mem) /\
  img_env VAL A_LIM (pft_E regs nd) /\
  env_agree 32 (Ereg regs [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd)]) (pft_E regs nd) /\
  (forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew (pft_E regs nd) n0 = getr regs r) /\
  ew (pft_E regs nd) 32 = w64 (fn_str nd) /\ ew (pft_E regs nd) 33 = w64 (fn_kids nd) /\
  ew (pft_E regs nd) 34 = w64 (fn_keys nd) /\ bv_unsigned (ew (pft_E regs nd) 8) = fe_v en.
Proof.
intros pc en nd ly S Hp W regs mem md k Lam PB FX CTX0 HPRE HFR HSP HVR HVN.
pose proof (pft_nums PB FX CTX0 en HPRE) as (Hsp16 & Hsp46 & Hsp47 & Hspc & Hd0 & Hd16 & Hdtop & Hhi).
pose proof HFR as (HJ & HWINk & Hsp & HSAV & HPRES & H3 & H4 & HROD).
pose proof HVR as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
pose proof HSP as (VS8 & VS16).
pose proof Hstr as (Hstr0 & Hstrv). pose proof Hkids as (Hkids0 & Hkidsv).
pose proof Hkeys as (Hkeys0 & Hkeysv).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r ->
  ew (pft_E regs nd) n0 = getr regs r).
{ intros n0 r Hn Hr. unfold pft_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (E32 : ew (pft_E regs nd) 32 = w64 (fn_str nd)).
{ unfold pft_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew (pft_E regs nd) 33 = w64 (fn_kids nd)).
{ unfold pft_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (E34 : ew (pft_E regs nd) 34 = w64 (fn_keys nd)).
{ unfold pft_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
assert (E2 : ew (pft_E regs nd) 2 = getr regs 2) by (apply Er; [lia | reflexivity]).
assert (Usp : bv_unsigned (ew (pft_E regs nd) 2) = fe_sp1 en) by (rewrite E2; exact Hsp).
assert (E8 : ew (pft_E regs nd) 8 = w64 (fe_v en))
  by (rewrite (Er 8%nat 8%bv ltac:(lia) ltac:(reflexivity)); exact R8).
assert (Uv : bv_unsigned (ew (pft_E regs nd) 8) = fe_v en)
  by (rewrite E8; apply unsigned_lit_small; lia).
assert (E23 : ew (pft_E regs nd) 23 = w64 SHADOW_OFF)
  by (rewrite (Er 23%nat 23%bv ltac:(lia) ltac:(reflexivity)); exact R23).
assert (Ush : bv_unsigned (ew (pft_E regs nd) 23) = SHADOW_OFF)
  by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
{ rewrite restrict_mkst_fx. unfold pft_ss. apply pa_entry_st_ok_full.
  - unfold pft_sregs. apply regs_ok_pin; [unfold pft_E; apply regs_ok_Eimg_Ereg | | ].
    + intros HC. apply (f_equal bv_unsigned) in HC. vm_compute in HC. discriminate HC.
    + cbn [sv_denot]. rewrite Uv. exact R19.
  - vm_compute. reflexivity.
  - unfold pft_frame, pft_vhdr.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS (pft_E regs nd) _ _ 8 8 (SAlu ALU_SRL (SOff 8 24) (SLit 3))
          ((fe_v en + 24) / 8)).
        -- apply (pfg_reg_of_U (pft_E regs nd) _ _ _ eq_refl).
           rewrite pfg_U_srl3, (U_atom_off (pft_E regs nd) 8 (fe_v en) 24 E8 ltac:(lia) ltac:(lia)).
           reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
           split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        -- cbn. lia.
        -- exact VS8.
      * apply (chunk_ok_val SEGS (pft_E regs nd) _ _ 16 8 (SAlu ALU_SRL (SOff 8 32) (SLit 3))
          ((fe_v en + 32) / 8)).
        -- apply (pfg_reg_of_U (pft_E regs nd) _ _ _ eq_refl).
           rewrite pfg_U_srl3, (U_atom_off (pft_E regs nd) 8 (fe_v en) 32 E8 ltac:(lia) ltac:(lia)).
           reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
           split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        -- cbn. lia.
        -- exact VS16.
    + cbn [base_val]. rewrite Uv. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS (pft_E regs nd) _ _ 16 8 (SOff 32 0) (fn_str nd));
        [ cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hstrv ].
      * apply (chunk_ok_val SEGS (pft_E regs nd) _ _ 24 8 (SOff 33 0) (fn_kids nd));
        [ cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hkidsv ].
      * apply (chunk_ok_val SEGS (pft_E regs nd) _ _ 32 8 (SOff 34 0) (fn_keys nd));
        [ cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hkeysv ].
  - apply pairwise_disjoint_of_extents.
    unfold pft_frame, pft_vhdr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uv.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    unfold pft_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uv, Ush. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
split.
{ unfold sh_ok, pft_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem (pft_E regs nd) PFT_Bx 8 (fe_v en) 56 (fe_v en) 0 56 Hvra).
  - unfold PFT_Bx. rewrite U_SOff, Ush, Z.add_0_r. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
  - rewrite U_SOff, Uv, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  - lia.
  - lia.
  - intros x Hx. unfold amem_range in Hamr. unfold SHADOW_OFF in *. lia. }
split; [unfold pft_E; apply Eimg_env|].
split; [unfold pft_E; split; [intros n0 Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]|].
split; [exact Er|]. split; [exact E32|]. split; [exact E33|]. split; [exact E34 | exact Uv].
Qed.

(* ---- a byte of a live ledger block's allocator range that hits v's node: that block IS v's place ---- *)
Lemma pft_apart_core : forall en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  pf_vnode B en nd ly S Lam W mem ->
  YM05.alloc_ceiling <= fe_sp0 en ->
  In (a, k) Lam ->
  a - cf_head <= x < a - cf_head + req_size (k + cf_head) ->
  fe_v en <= x < fe_v en + 56 ->
  ~ In (a, k) (fe_D en) /\ a <= fe_v en /\ fe_v en + 56 <= a + k.
Proof.
intros en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x HAR HLED HVN Hsp0 Hin Hx Hv.
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & _ & _ & _ & _ & _ & _ & _ & _ & Hplace).
pose proof (@cf_head_nonneg cp) as Hc0.
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hin)
  as (Hk0 & Ha0 & Hak & Ha16 & Hab & Hhp).
assert (Hkc : 0 <= k + cf_head) by lia.
pose proof (req_size_pos (k + cf_head) Hkc) as [Rk1 Rk2].
destruct Hplace as [(a' & k' & HaL & HaD & Hav & Hvk) | [(b & m & Hbm & HnL & Hbv & Hvm) |
  [(cid & pos & Hcp & Hf1 & Hf2) | (Hs0 & _)]]].
- destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED HaL)
    as (Hk0' & Ha0' & Hak' & _ & Hab' & _).
  assert (Hkc' : 0 <= k' + cf_head) by lia.
  pose proof (req_size_pos (k' + cf_head) Hkc') as [Rk1' Rk2'].
  destruct (Z.eq_dec a a') as [Ea | Hnea]; [destruct (Z.eq_dec k k') as [Ek | Hnek]|].
  + subst a' k'. split; [exact HaD | split; lia].
  + exfalso.
    assert (Hne2 : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head))
      by (intros Eq; injection Eq as E1 E2; apply Hnek; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab' Hne2) as HZ.
    unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
  + exfalso.
    assert (Hne2 : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head))
      by (intros Eq; injection Eq as E1 E2; apply Hnea; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab' Hne2) as HZ.
    unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
- exfalso.
  assert (Hne2 : (a - cf_head, k + cf_head) <> (b, m)).
  { intros Eq. injection Eq as E1 E2. apply HnL.
    replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia. exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hbm Hne2) as HZ.
  unfold zdisjoint in HZ. cbn [fst snd] in HZ.
  pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2]. lia.
- exfalso.
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) cid pos
    HAR Hab Hcp) as HZ.
  unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
- exfalso. lia.
Qed.

(* ---- the image's list membership, and the pc0-filtered trace of an empty chain ---- *)
Lemma pft_in_of_existsb : forall (l : list Z) (x : Z), existsb (Z.eqb x) l = true -> In x l.
Proof.
intros l x H. apply existsb_exists in H as (y & Hy & He). apply Z.eqb_eq in He. subst y. exact Hy.
Qed.
Lemma pft_trace : forall pc0 r, prh_trace pc0 r [] = pc0 :: (if r =? pc0 then [] else [r]).
Proof.
intros pc0 r. unfold prh_trace. cbn [flat_map app]. rewrite app_nil_r.
destruct (r =? pc0); reflexivity.
Qed.

(* ---- ONE `jal fuzz_free` of the tail: the next block of the order goes, the cut moves to the return site; at the
   walk's relation wle' SEGS RZ_cf (the free can hide shadow again: the text concludes SRr' SEGS RZ_cf) ---- *)
Lemma pft_call : forall PB FX CTX0 en nd R blk p ret E ss ms ly S Hp W mdc k Q,
  tfuzz_free_specO (PA := PA) B ARx SK PB FX ->
  pf_pre B ARx PB FX CTX0 en -> List.NoDup (fe_D en) ->
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_fuzz_free ->
  pft_inv FX en nd (blk ++ R) ly S Hp W (ms_regs ms) (ms_mem ms) mdc k ->
  (p = 0 /\ blk = [] \/ exists kk, blk = [(p, kk)] /\ In (p, kk) (fe_Lam en)) ->
  getr (ms_regs ms) 10 = w64 p ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + ret) ->
  In (BASE + ret) (pi_ret_sites F_pj_free RT_fuzz_free) ->
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2,
     pft_inv FX en nd R ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr' SEGS RZ_cf W (mkCfg ms mdc) Q.
Proof.
intros PB FX CTX0 en nd R blk p ret E ss ms ly S Hp W mdc k Q FFREE HPRE HND HS Hrv Hpc HI HBLK
  Ha0 Hra HRET Hret40 Hret2 KONT.
unfold SRr'.
set (RW := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, RW W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, RW W1 W2 -> RW W2 W3 -> RW W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose proof (pft_nums PB FX CTX0 en HPRE) as (Hsp16 & Hsp46 & Hsp47 & Hspc & Hd0 & Hd16 & Hdtop & Hhi).
pose proof HPRE as (HFPRE & HUNIV & _ & _ & _ & _ & HSAFE0 & _).
(* fpre's last conjunct FRM0-ENTRY: pj_free runs no float instruction, so its fuzz_free gets pj_free's own *)
pose proof HFPRE as (HAFN & HROD0 & HSTKHI & _ & HFRM0).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof HI as (HFR & HSP & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ & HWINk & Hsp & HSAV & HPRES & H3 & H4 & HRODk & HMNk).
pose proof HVR as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HAC as (HROOM & HLED & HPL & HPB & EF & HRE).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
pose proof (HSAFE0 ltac:(lia)) as HSAFE.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hc0.
pose proof (pfg_stk (fe_n en)) as ESTK.
pose proof pfg_stk_ff as ESTKF.
assert (HN1 : 1 <= Z.of_nat (Datatypes.S (fe_n en))) by lia.
assert (HBASE : 4096 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64)
  by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
assert (HCEIL : YM05.alloc_ceiling <= fe_sp0 en).
{ unfold fe_sp1, PJF_FR in Hspc. lia. }
assert (HEX : exists n, (p = 0 \/ In (p, n) Lam) /\
   ((p = 0 /\ blk = []) \/ (p <> 0 /\ blk = [(p, n)] /\ In (p, n) Lam))).
{ destruct HBLK as [(Hp0 & Eb) | (kk & Eb & Hin)].
  - exists 0. split; [left; exact Hp0 | left; split; [exact Hp0 | exact Eb]].
  - assert (HinL : In (p, kk) Lam).
    { apply (Permutation_in _ HPL) in Hin. apply in_app_or in Hin as [HinF | HinL]; [|exact HinL].
      exfalso. rewrite Eb in HPD. cbn [app] in HPD.
      pose proof (Permutation_NoDup HPD HND) as HN2.
      exact (NoDup_remove_2 _ _ _ HN2 (in_or_app _ _ _ (or_introl HinF))). }
    destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED HinL)
      as (Hk0 & Hp4096 & Hpceil & Hp16 & Hab & Hhp).
    exists kk. split; [right; exact HinL | right; split; [lia | split; [exact Eb | exact HinL]]]. }
destruct HEX as (n & HPN & HCASE2).
assert (HFP1 : forall x, inFP (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - cf_head, n + cf_head)]) x ->
   p <> 0 /\ p - cf_head <= x < p - cf_head + req_size (n + cf_head)).
{ intros x. destruct (Z.eqb_spec p 0) as [Hp0 | Hne]; intros Hx.
  - exfalso. exact (inFP_nil x Hx).
  - split; [exact Hne|].
    destruct (inFP_ablocks_fp_inv _ _ Hx) as (q & m & [Hq | []] & Hr).
    injection Hq as -> ->. exact Hr. }
assert (HBAB : p <> 0 -> In (p, n) Lam /\ In (p - cf_head, n + cf_head) (ablocks B ly S) /\
   4096 + cf_head <= p /\ p - cf_head + req_size (n + cf_head) <= YM05.alloc_ceiling).
{ intros Hne. destruct HCASE2 as [(Hp0 & _) | (_ & _ & HinL)]; [exfalso; exact (Hne Hp0)|].
  destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED HinL)
    as (Hk0 & Hp4096 & Hpceil & Hp16 & Hab & Hhp).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W (ms_mem ms) mdc _ _ HAR Hab) as (_ & _ & Hclim & _).
  split; [exact HinL | split; [exact Hab | split; [exact Hp4096 | exact Hclim]]]. }
assert (HFPlow : forall x, inFP (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - cf_head, n + cf_head)]) x ->
   x < YM05.alloc_ceiling).
{ intros x Hx. destruct (HFP1 x Hx) as (Hne & Hr). destruct (HBAB Hne) as (_ & _ & _ & Hclim). lia. }
assert (HSINK : ~ YI16.sink_open_fp (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - cf_head, n + cf_head)])).
{ destruct (Z.eqb_spec p 0) as [Hp0 | Hne].
  - apply sink_closed_pos. apply Forall_nil.
  - destruct (HBAB Hne) as (_ & _ & Hp4096 & _).
    apply sink_closed_ablocks_fp. constructor; [cbn [fst]; lia | apply Forall_nil]. }
(* the free's trace is a FIXED trace (prh_univ_closure's clauses 1-2), the premise of the instrumented text
   (PjFreeCommon.v tfuzz_free_specO) *)
assert (HTRf : In (call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms) []) (u_fix (as_universe B))).
{ assert (HRAZ : raZ (ms_regs ms) = BASE + ret)
    by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
  apply call_trace_in.
  - exact (proj1 HUNIV RT_fuzz_free).
  - rewrite call_trace_nil, HRAZ, <- pft_trace.
    change (pc_free_ra0 (as_code B)) with (prh_pc0 B RT_fuzz_free).
    eapply prh_univ_closure_lit; [exact HUNIV | exact HRET]. }
eapply (SRrG_bind SEGS RW Rt).
{ eapply (aj_call_xW_spR (fx := fx) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ B_prog_listing PA) RW Rr Rt
    W E ss ms
    (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp mdc k
    STK_fuzz_free 0 (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - cf_head, n + cf_head)])
    (fe_sp1 en - (fe_sp0 en + fe_d en)) (Z_to_bv 64 (BASE + ret)) [] _ HS Hrv HJ).
  - rewrite Hsp. lia.
  - unfold fe_sp1, PJF_FR. lia.
  - unfold fe_sp1, PJF_FR. lia.
  - lia.
  - unfold fe_sp1, PJF_FR. lia.
  - lia.
  - reflexivity.
  - unfold fe_sp1, PJF_FR. lia.
  - rewrite H3. exact Hgp0.
  - rewrite H4. exact Htp0.
  - exact Hra.
  - apply ret_ok_codeptr_v; [lia | exact Hret2].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite R8, pfg_w64_unsigned by lia. lia.
  - intros HPRE1 HWIN1.
    assert (HBASE2 : BASE < 2 ^ 40) by (apply Z.ltb_lt; vm_compute; reflexivity).
    assert (HFPRE1 : fpre (PA := PA) B ARx STK_fuzz_free ly S Hp W (ms_regs ms) (ms_mem ms) mdc []).
    { split; [exact HPRE1|]. split; [exact HRODk|]. split.
      - rewrite Hsp, Eshi. unfold fe_sp1, fe_sp0, PJF_FR in *. lia.
      - split; [|exact HFRM0]. unfold raZ. rewrite Hra, unsigned_lit_small by lia. lia. }
    assert (HPBS : PB S)
      by exact (pf_safe_here FX PB _ ly S (pf_safe_after FX PB _ _ _ _ _ _ HSAFE HRE)).
    eapply (SRrG_mono SEGS RW).
    { rewrite Hpc.
      exact (FFREE (fe_most en) (fe_own en) ly S Hp W (ms_regs ms) (ms_mem ms) mdc [] p n Lam
        (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en)
        HFPRE1 HROOM HPBS HTRf Ha0 HPN HLED). }
    cbv beta. intros W' c' _ HQ. apply (fpostW_x_of_apostR (SK := SK) SEGS B PST ARx RW). exact HQ.
  - intros x Hx. destruct (HFP1 x Hx) as (Hne & Hr). destruct (HBAB Hne) as (HinL & Hab & _).
    assert (HinD : In (p, n) (fe_D en)).
    { destruct HCASE2 as [(Hp0 & _) | (_ & Eb & _)]; [exfalso; exact (Hne Hp0)|].
      apply (Permutation_in _ (Permutation_sym HPD)). rewrite Eb. apply in_or_app. right.
      left. reflexivity. }
    left. unfold fe_FP.
    replace (fe_v en =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (inFP_ablocks_fp (prhPj_hbl (fe_D en)) (p - cf_head) (n + cf_head) (x - (p - cf_head))
      ltac:(unfold prhPj_hbl; apply in_map_iff; exists (p, n); split; [reflexivity | exact HinD])
      ltac:(lia)) as (r0 & Hr1 & Hr2).
    exists r0. split; [right; exact Hr1|].
    replace (p - cf_head + (x - (p - cf_head))) with x in Hr2 by lia. exact Hr2. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HXc & HP2 & HK).
unfold fQmn in HK. cbv beta in HK. destruct HK as ((HFX & HROOM2 & HARM) & HMNc).
replace (fe_sp0 en + fe_d en + (fe_sp1 en - (fe_sp0 en + fe_d en)) + 0) with (fe_sp1 en + 0) in HJc by lia.
pose proof (pft_pres _ _ HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P22 & P23).
destruct (pfk_frame B ARx RW RW PB FX CTX0 en ly S Hp W (ms_regs ms) (ms_mem ms) mdc k
  STK_fuzz_free 0 (if p =? 0 then @nil (Z * Z) else ablocks_fp [(p - cf_head, n + cf_head)])
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HFR HSP HJc HJ2 ltac:(rewrite ESTKF; lia) ltac:(lia) HSINK HFPlow
  ltac:(unfold spZ; rewrite P2; reflexivity) P3 P4 HMNc) as (HFR2 & HSP2).
apply (KONT ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1)).
split; [exact HFR2|]. split; [exact HSP2|].
split; [unfold pf_vregs; rewrite P8, P9, P18, P19, P23, P22; exact HVR|].
destruct HCASE2 as [(Hp0 & Eb) | (Hne & Eb & HinL)].
- subst p blk. cbn [app] in HAC, HPD.
  destruct HARM as [(_ & EHp & Eab & HLED2) | (Hne & _)]; [|exfalso; exact (Hne eq_refl)].
  exists Fd, Lam. split; [|split].
  + exact (pfk_acct_null B FX en ly S Hp W (ms_mem ms) Fd R Lam ly2 S2 Hp2 W2 mem2 HAC HFX HROOM2 Eab HLED2).
  + eapply (pfk_vnode B ARx LAWS VISF RW en nd ly S Hp W (ms_mem ms) mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam);
    [ exact HVN | exact HAR | exact HLED | exact HJc | exact HLED2 | | | | | | ].
    * intros x Hx. exfalso. exact (inFP_nil x Hx).
    * intros b Hin Hnin. exfalso. apply Hnin. rewrite Eab. exact Hin.
    * intros a kk Hin _. exact Hin.
    * intros a kk Hin. exact Hin.
    * exact HCEIL.
    * intros x Hx. exfalso. exact (inFP_nil x Hx).
  + exact HPD.
- subst blk. cbn [app] in HAC, HPD.
  destruct HARM as [(Hp0 & _) | (_ & EHp & (b1 & b2 & Eb1 & Eb2) & l1 & l2 & ELam & HLED2)];
    [exfalso; exact (Hne Hp0)|].
  replace (p =? 0) with false in HFX by (symmetry; apply Z.eqb_neq; exact Hne).
  assert (HinD : In (p, n) (fe_D en)).
  { apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. left. reflexivity. }
  destruct (HBAB Hne) as (_ & Hab & Hp4096 & Hclim).
  exists (Fd ++ [(p, n)]), (l1 ++ l2). split; [|split].
  + apply (pfk_acct_free B FX en ly S Hp W (ms_mem ms) Fd (p, n) R Lam ly2 S2 Hp2 W2 mem2 l1 l2
      HAC HFX HROOM2 ELam (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2))) HLED2).
  + eapply (pfk_vnode B ARx LAWS VISF RW en nd ly S Hp W (ms_mem ms) mdc Lam ly2 S2 Hp2 W2 mem2 md2 (l1 ++ l2));
    [ exact HVN | exact HAR | exact HLED | exact HJc | exact HLED2 | | | | | | ].
    * intros x Hx Hvx. destruct (HFP1 x Hx) as (_ & Hr).
      destruct (pft_apart_core en nd ly S Hp W (ms_mem ms) mdc Lam (fe_peak en) (fe_cnt en) (fe_fail en)
        (fe_ran en) (fe_most en) (fe_own en) p n x HAR HLED HVN HCEIL HinL Hr Hvx) as (HnD & _).
      exact (HnD HinD).
    * intros b Hin Hnin. exists p, n. split; [exact HinD | split; [exact HinL|]].
      rewrite Eb1 in Hin. rewrite Eb2 in Hnin.
      apply in_app_or in Hin as [G1 | [G2 | G3]].
      -- exfalso. apply Hnin. apply in_or_app. left. exact G1.
      -- symmetry. exact G2.
      -- exfalso. apply Hnin. apply in_or_app. right. exact G3.
    * intros a kk Hin Hnin. rewrite ELam in Hin. apply in_app_or in Hin as [G1 | [G2 | G3]].
      -- apply in_or_app. left. exact G1.
      -- exfalso. apply Hnin. rewrite <- G2. exact HinD.
      -- apply in_or_app. right. exact G3.
    * intros a kk Hin. rewrite ELam. apply in_app_or in Hin as [G1 | G1]; apply in_or_app;
        [left; exact G1 | right; right; exact G1].
    * exact HCEIL.
    * intros x Hx. destruct (HFP1 x Hx) as (_ & Hr). exists (p - cf_head), (n + cf_head).
      split; [exact Hab | exact Hr].
  + rewrite <- app_assoc. cbn [app]. exact HPD.
Qed.

(* ---- the cut rides through a stretch that stores nothing ---- *)
Lemma pft_inv_stretch : forall FX en nd R ly S Hp W regs mem md k regs' mem' md' k',
  pft_inv FX en nd R ly S Hp W regs mem md k -> mem' = mem ->
  ajournal_xR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp W mem' md' k' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  pft_inv FX en nd R ly S Hp W regs' mem' md' k'.
Proof.
intros FX en nd R ly S Hp W regs mem md k regs' mem' md' k' HI -> HJ' K2 K3 K4 K8 K9 K18 K19 K22 K23.
pose proof HI as ((HJ & HWIN & Hsp & HSAV & HPRES & H3 & H4 & HROD & HMN) & HSP & HVR & Fd & Lam & HAC & HVN & HPD).
split.
{ split; [exact HJ'|]. split; [exact HWIN|].
  split; [unfold spZ; rewrite K2; exact Hsp|].
  split; [exact HSAV|]. split; [exact HPRES|].
  split; [rewrite K3; exact H3|]. split; [rewrite K4; exact H4|]. split; [exact HROD | exact HMN]. }
split; [exact HSP|].
split; [unfold pf_vregs; rewrite K8, K9, K18, K19, K22, K23; exact HVR|].
exists Fd, Lam. split; [exact HAC | split; [exact HVN | exact HPD]].
Qed.

(* ---- v's 56 bytes are no image bytes ---- *)
Lemma pft_vimg : forall en nd ly S Hp W mem md Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  pf_vnode B en nd ly S Lam W mem -> YM05.alloc_ceiling <= fe_sp0 en ->
  forall x, fe_v en <= x < fe_v en + 56 -> ~ in_img SEGS x.
Proof.
intros en nd ly S Hp W mem md Lam peak cnt fail ran most own HAR HLED HVN HCEIL x Hx.
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & _ & _ & _ & _ & _ & _ & _ & _ & Hplace).
pose proof (@cf_head_nonneg cp) as Hc0.
destruct Hplace as [(a & k & HaL & _ & Hav & Hvk) | [(b & m & Hbm & _ & Hbv & Hvm) |
  [(cid & pos & Hcp & Hf1 & Hf2) | (Hs0 & _)]]].
- destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED HaL)
    as (Hk0 & Ha0 & Hak & _ & Hab & _).
  assert (Hkc : 0 <= k + cf_head) by lia.
  pose proof (req_size_pos (k + cf_head) Hkc) as [Rk1 Rk2].
  apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) x HAR Hab). lia.
- assert (Hm : 0 <= m) by lia. pose proof (req_size_pos m Hm) as [Rm1 Rm2].
  apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m x HAR Hbm). lia.
- apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HAR Hcp). lia.
- exfalso. lia.
Qed.

(* ---- a byte array of zeros from the bytes a view shows (pj_parse_seg_ent.v pje_garr8_of_aview) ---- *)
Lemma pft_val1_of_aview : forall H m a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv kk Hk. assert (Ek : kk = 0%nat) by lia. subst kk.
replace (a + Z.of_nat 0) with a by lia.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb.
rewrite YI04.le_byte_small by (cbn in Rb |- *; lia). cbn [Z.of_nat].
rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma pft_garr8_of_aview : forall H m p l, Forall (fun x => 0 <= x < 256) l ->
  (forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l Hl Hv j Hj. split.
- apply pft_val1_of_aview. exact (Hv j Hj).
- apply (proj1 (Forall_forall _ _) Hl). apply nth_In. exact Hj.
Qed.

Ltac pft_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ================================================================ the three calls ================ *)
Lemma pft_S1 : forall PB FX CTX0 en nd R ly S Hp W regs mem md k Q,
  tfuzz_free_specO (PA := PA) B ARx SK PB FX ->
  pf_pre B ARx PB FX CTX0 en -> pf_node en nd ->
  pft_inv FX en nd (fn_Dk nd ++ R) ly S Hp W regs mem md k ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2, pft_inv FX en nd R ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + PFT_R1)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr' SEGS RZ_cf W (pf_cfg PJF_LX regs mem md) Q.
Proof.
intros PB FX CTX0 en nd R ly S Hp W regs mem md k Q FFREE HPRE HNODE HI KONT.
pose proof HI as (HFR & HSP & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ & _).
pose proof HNODE as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
destruct (pft_seat PJF_LX en nd ly S Hp W regs mem md k Lam PB FX CTX0 HPRE HFR HSP HVR HVN)
  as (HS & SHOK & HEI & HAE & Er & E32 & E33 & E34 & Uv).
unfold pf_cfg, SRr'.
set (RW := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, RW W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, RW W1 W2 -> RW W2 W3 -> RW W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose (RUN := @paj_run_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS RW Rr Rt).
paj_run_tok_x RUN HS HJ SHOK PFT_Bspan.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold pft_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold pft_frame, pft_vhdr in Ha;
  cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  unfold pft_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold pft_frame, pft_vhdr in Ha;
  cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
pose proof (regs_kept_of_st_ok SEGS (pft_E regs nd) _ (restrict (w_H W) ms) regs
  [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd)]
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 22%bv; 23%bv] HS HAE ltac:(vm_compute; reflexivity)) as RK.
cbn [ms_regs restrict] in RK.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (19%bv : bv 5) Q19.
assert (Q19' : getr (ms_regs ms) 19 = getr regs 19).
{ rewrite Q19, Uv. pose proof HVR as (_ & _ & _ & R19 & _). rewrite R19. reflexivity. }
assert (QR : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PFT_R1))
  by (rewrite Q1; f_equal; vm_compute; reflexivity).
assert (HRET : In (BASE + PFT_R1) (pi_ret_sites F_pj_free RT_fuzz_free))
  by (apply pft_in_of_existsb; vm_compute; reflexivity).
assert (HNDL : List.NoDup (fe_D en)) by (apply NoDup_ListNoDup; exact HNDD).
apply (pft_call PB FX CTX0 en nd R (fn_Dk nd) (fn_kids nd) PFT_R1 _ _ ms ly S Hp W _ k Q
  FFREE HPRE HNDL HS).
- reflexivity.
- reflexivity.
- apply (pft_inv_stretch FX en nd (fn_Dk nd ++ R) ly S Hp W regs mem md k
    (ms_regs ms) (ms_mem ms) _ _ HI MM HJ
    (RK 2%bv ltac:(pft_in)) (RK 3%bv ltac:(pft_in)) (RK 4%bv ltac:(pft_in))
    (RK 8%bv ltac:(pft_in)) (RK 9%bv ltac:(pft_in)) (RK 18%bv ltac:(pft_in))
    Q19' (RK 22%bv ltac:(pft_in)) (RK 23%bv ltac:(pft_in))).
- destruct HKIDSn as [(H1 & _ & H2) | (kk & Hlin & _ & Heq)];
  [left; split; [exact H1 | exact H2] | right; exists kk; split; [exact Heq | exact Hlin]].
- rewrite Q10, E33. reflexivity.
- exact QR.
- exact HRET.
- split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.
- vm_compute. reflexivity.
- exact KONT.
Qed.

Lemma pft_S2 : forall PB FX CTX0 en nd R ly S Hp W regs mem md k Q,
  tfuzz_free_specO (PA := PA) B ARx SK PB FX ->
  pf_pre B ARx PB FX CTX0 en -> pf_node en nd ->
  pft_inv FX en nd (fn_Dy nd ++ R) ly S Hp W regs mem md k ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2, pft_inv FX en nd R ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + PFT_R2)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr' SEGS RZ_cf W (pf_cfg PFT_R1 regs mem md) Q.
Proof.
intros PB FX CTX0 en nd R ly S Hp W regs mem md k Q FFREE HPRE HNODE HI KONT.
pose proof HI as (HFR & HSP & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ & _).
pose proof HNODE as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
destruct (pft_seat PFT_R1 en nd ly S Hp W regs mem md k Lam PB FX CTX0 HPRE HFR HSP HVR HVN)
  as (HS & SHOK & HEI & HAE & Er & E32 & E33 & E34 & Uv).
unfold pf_cfg, SRr'.
set (RW := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, RW W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, RW W1 W2 -> RW W2 W3 -> RW W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose (RUN := @paj_run_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS RW Rr Rt).
paj_run_tok_x RUN HS HJ SHOK PFT_Bspan.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold pft_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold pft_frame, pft_vhdr in Ha;
  cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  unfold pft_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold pft_frame, pft_vhdr in Ha;
  cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
pose proof (regs_kept_of_st_ok SEGS (pft_E regs nd) _ (restrict (w_H W) ms) regs
  [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd)]
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 22%bv; 23%bv] HS HAE ltac:(vm_compute; reflexivity)) as RK.
cbn [ms_regs restrict] in RK.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (19%bv : bv 5) Q19.
assert (Q19' : getr (ms_regs ms) 19 = getr regs 19).
{ rewrite Q19, Uv. pose proof HVR as (_ & _ & _ & R19 & _). rewrite R19. reflexivity. }
assert (QR : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PFT_R2))
  by (rewrite Q1; f_equal; vm_compute; reflexivity).
assert (HRET : In (BASE + PFT_R2) (pi_ret_sites F_pj_free RT_fuzz_free))
  by (apply pft_in_of_existsb; vm_compute; reflexivity).
assert (HNDL : List.NoDup (fe_D en)) by (apply NoDup_ListNoDup; exact HNDD).
apply (pft_call PB FX CTX0 en nd R (fn_Dy nd) (fn_keys nd) PFT_R2 _ _ ms ly S Hp W _ k Q
  FFREE HPRE HNDL HS).
- reflexivity.
- reflexivity.
- apply (pft_inv_stretch FX en nd (fn_Dy nd ++ R) ly S Hp W regs mem md k
    (ms_regs ms) (ms_mem ms) _ _ HI MM HJ
    (RK 2%bv ltac:(pft_in)) (RK 3%bv ltac:(pft_in)) (RK 4%bv ltac:(pft_in))
    (RK 8%bv ltac:(pft_in)) (RK 9%bv ltac:(pft_in)) (RK 18%bv ltac:(pft_in))
    Q19' (RK 22%bv ltac:(pft_in)) (RK 23%bv ltac:(pft_in))).
- destruct HKEYSn as [(H1 & _ & H2) | (_ & kk & Hlin & _ & Heq)];
  [left; split; [exact H1 | exact H2] | right; exists kk; split; [exact Heq | exact Hlin]].
- rewrite Q10, E34. reflexivity.
- exact QR.
- exact HRET.
- split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.
- vm_compute. reflexivity.
- exact KONT.
Qed.

Lemma pft_S3 : forall PB FX CTX0 en nd R ly S Hp W regs mem md k Q,
  tfuzz_free_specO (PA := PA) B ARx SK PB FX ->
  pf_pre B ARx PB FX CTX0 en -> pf_node en nd ->
  pft_inv FX en nd (fn_Ds nd ++ R) ly S Hp W regs mem md k ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k2, pft_inv FX en nd R ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + PFT_R3)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr' SEGS RZ_cf W (pf_cfg PFT_R2 regs mem md) Q.
Proof.
intros PB FX CTX0 en nd R ly S Hp W regs mem md k Q FFREE HPRE HNODE HI KONT.
pose proof HI as (HFR & HSP & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ & _).
pose proof HNODE as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
destruct (pft_seat PFT_R2 en nd ly S Hp W regs mem md k Lam PB FX CTX0 HPRE HFR HSP HVR HVN)
  as (HS & SHOK & HEI & HAE & Er & E32 & E33 & E34 & Uv).
unfold pf_cfg, SRr'.
set (RW := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, RW W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, RW W1 W2 -> RW W2 W3 -> RW W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose (RUN := @paj_run_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS RW Rr Rt).
paj_run_tok_x RUN HS HJ SHOK PFT_Bspan.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold pft_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold pft_frame, pft_vhdr in Ha;
  cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  unfold pft_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold pft_frame, pft_vhdr in Ha;
  cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
pose proof (regs_kept_of_st_ok SEGS (pft_E regs nd) _ (restrict (w_H W) ms) regs
  [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd)]
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 22%bv; 23%bv] HS HAE ltac:(vm_compute; reflexivity)) as RK.
cbn [ms_regs restrict] in RK.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (19%bv : bv 5) Q19.
assert (Q19' : getr (ms_regs ms) 19 = getr regs 19).
{ rewrite Q19, Uv. pose proof HVR as (_ & _ & _ & R19 & _). rewrite R19. reflexivity. }
assert (QR : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PFT_R3))
  by (rewrite Q1; f_equal; vm_compute; reflexivity).
assert (HRET : In (BASE + PFT_R3) (pi_ret_sites F_pj_free RT_fuzz_free))
  by (apply pft_in_of_existsb; vm_compute; reflexivity).
assert (HNDL : List.NoDup (fe_D en)) by (apply NoDup_ListNoDup; exact HNDD).
apply (pft_call PB FX CTX0 en nd R (fn_Ds nd) (fn_str nd) PFT_R3 _ _ ms ly S Hp W _ k Q
  FFREE HPRE HNDL HS).
- reflexivity.
- reflexivity.
- apply (pft_inv_stretch FX en nd (fn_Ds nd ++ R) ly S Hp W regs mem md k
    (ms_regs ms) (ms_mem ms) _ _ HI MM HJ
    (RK 2%bv ltac:(pft_in)) (RK 3%bv ltac:(pft_in)) (RK 4%bv ltac:(pft_in))
    (RK 8%bv ltac:(pft_in)) (RK 9%bv ltac:(pft_in)) (RK 18%bv ltac:(pft_in))
    Q19' (RK 22%bv ltac:(pft_in)) (RK 23%bv ltac:(pft_in))).
- destruct HSTRn as [(H1 & H2) | (kk & Hlin & Heq)];
  [left; split; [exact H1 | exact H2] | right; exists kk; split; [exact Heq | exact Hlin]].
- rewrite Q10, E32. reflexivity.
- exact QR.
- exact HRET.
- split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.
- vm_compute. reflexivity.
- exact KONT.
Qed.

(* ================================================================ the memset and the cut pf_EP === *)
Lemma pft_S4 : forall PB FX CTX0 en nd ly S Hp W regs mem md k,
  pf_texts (SK := SK) B ARx PB FX -> pfs_EP (SK := SK) B ARx FX ->
  pf_pre B ARx PB FX CTX0 en -> pf_node en nd ->
  pft_inv FX en nd [] ly S Hp W regs mem md k ->
  SRr' SEGS RZ_cf W (pf_cfg PFT_R3 regs mem md) (pf_FIN (SK := SK) B ARx FX en).
Proof.
intros PB FX CTX0 en nd ly S Hp W regs mem md k TXT SEP HPRE HNODE HI.
destruct TXT as (FFREE & AMSET).
pose proof (pft_nums PB FX CTX0 en HPRE) as (Hsp16 & Hsp46 & Hsp47 & Hspc & Hd0 & Hd16 & Hdtop & Hhi).
pose proof HI as (HFR & HSP & HVR & Fd & Lam & HAC & HVN & HPD).
pose proof HFR as (HJ0 & HWINk & Hsp & HSAV & HPRES & H3 & H4 & HRODk & HMNk).
pose proof HVR as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HAC as (HROOM & HLED & HPL & HPB & EF & HRE).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
pose proof HPRE as (HFPRE & HUNIV & _ & _ & _ & _ & HSAFE & _).
pose proof HFPRE as (HAFN & HROD0 & HSTKHI & _).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof (ajxR_ar HJ0) as HAR. pose proof (ajxR_ly HJ0) as Hly. pose proof (ajxR_secs HJ0) as Hsecs.
pose proof (ajxR_rel HJ0) as Hwle. pose proof (ajxR_io HJ0) as Hios. pose proof (ajxR_frs HJ0) as Hfrs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hc0.
pose proof (pfg_stk (fe_n en)) as ESTK.
assert (HN1 : 1 <= Z.of_nat (Datatypes.S (fe_n en))) by lia.
assert (HES : ESTACK = 4096) by reflexivity.
assert (ESP1 : fe_sp1 en = fe_sp0 en - 128) by (unfold fe_sp1, PJF_FR; reflexivity).
pose proof Hstk0 as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop').
assert (HCEIL : YM05.alloc_ceiling <= fe_sp0 en) by lia.
destruct (pft_seat PFT_R3 en nd ly S Hp W regs mem md k Lam PB FX CTX0 HPRE HFR HSP HVR HVN)
  as (HS & SHOK & HEI & HAE & Er & E32 & E33 & E34 & Uv).
unfold pf_cfg, SRr'.
set (RW := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, RW W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, RW W1 W2 -> RW W2 W3 -> RW W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose (RUN := @paj_run_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS RW Rr Rt).
paj_run_tok_x RUN HS HJ0 SHOK PFT_Bspan.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold pft_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold pft_frame, pft_vhdr in Ha;
  cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  unfold pft_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold pft_frame, pft_vhdr in Ha;
  cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
pose proof (regs_kept_of_st_ok SEGS (pft_E regs nd) _ (restrict (w_H W) ms) regs
  [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd)]
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 22%bv; 23%bv] HS HAE ltac:(vm_compute; reflexivity)) as RK.
cbn [ms_regs restrict] in RK.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (QR : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PJF_EP))
  by (rewrite Q1; f_equal; vm_compute; reflexivity).
assert (Q10' : getr (ms_regs ms) 10 = w64 (fe_v en)).
{ rewrite Q10. unfold w64. rewrite <- Uv. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Q11' : getr (ms_regs ms) 11 = w64 0) by (rewrite Q11; apply bv_eq; vm_compute; reflexivity).
assert (Q12' : getr (ms_regs ms) 12 = w64 56) by (rewrite Q12; apply bv_eq; vm_compute; reflexivity).
assert (HSP2 : spZ (ms_regs ms) = fe_sp1 en)
  by (unfold spZ; rewrite (RK 2%bv ltac:(pft_in)); exact Hsp).
assert (HFPv : forall a, fe_v en <= a < fe_v en + 56 -> inFP (fe_FP en) a).
{ intros a Ha. unfold fe_FP. replace (fe_v en =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  exists (fe_v en, fe_v en + 56). split; [left; reflexivity | cbn [fst snd]; lia]. }
cbn [app] in Hfrs.
pmkst HS.
(* the memset keeps the world (a plain step fact over the journal at RW, lifted into RW) *)
eapply (SRrG_bind SEGS RW Rt).
{ apply (SRr_SRrG SEGS RW (wle_wle' SEGS RZ_cf)).
  eapply (aj_intrin_at_xm_frR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ B_prog_listing PA) RW Rr Rt
    OSet (SIGMA AS___asan_memset) AMSET W (ms_regs ms) (ms_mem ms)
    (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] ly S Hp _ k
    (fe_v en) 0 56 (fe_sp1 en - (fe_sp0 en + fe_d en)) _ HJ0).
  - exact Q10'.
  - exact Q11'.
  - exact Q12'.
  - lia.
  - lia.
  - lia.
  - rewrite HSP2. lia.
  - lia.
  - lia.
  - lia.
  - rewrite (RK 3%bv ltac:(pft_in)), H3. exact Hgp0.
  - rewrite (RK 4%bv ltac:(pft_in)), H4. exact Htp0.
  - exact QR.
  - apply ret_ok_codeptr_v;
    [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity].
  - intros a Ha. split.
    + destruct Hplace as [(a' & k' & HaL & _ & Hav & Hvk) | [(b & m & Hbm & _ & Hbv & Hvm) |
        [(cid & pos & Hcp & Hf1 & Hf2) | (Hs0 & _)]]].
      * left. right. left. split; [exact (HFPv a Ha)|].
        destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED HaL)
          as (Hk0 & Ha0 & Hak & _ & Hab & _).
        assert (Hkc : 0 <= k' + cf_head) by lia.
        pose proof (req_size_pos (k' + cf_head) Hkc) as [Rk1 Rk2].
        exists (a' - cf_head), (k' + cf_head). split; [exact Hab | lia].
      * left. right. left. split; [exact (HFPv a Ha)|].
        assert (Hm : 0 <= m) by lia. pose proof (req_size_pos m Hm) as [Rm1 Rm2].
        exists b, m. split; [exact Hbm | lia].
      * right. split; [exact (HFPv a Ha)|].
        exists cid, pos. split; [rewrite Hfrs in Hcp; exact Hcp|].
        unfold in_zr, frame_rng. cbn [fst snd]. lia.
      * exfalso. lia.
    + replace (fe_sp0 en + fe_d en + (fe_sp1 en - (fe_sp0 en + fe_d en))) with (fe_sp1 en) by lia.
      lia.
  - exact Hamr.
  - rewrite MM. exact Hvra.
  - intros _. rewrite MM. exact Hvhull.
  - exact I. }
cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & Hmn4).
replace (fe_sp0 en + fe_d en + (fe_sp1 en - (fe_sp0 en + fe_d en))) with (fe_sp1 en) in Hfr4 by lia.
pose proof (pft_pres _ _ HP4) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P22 & P23).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (fe_v en <= a < fe_v en + 56) ->
   ~ (fe_sp1 en - ESTACK <= a < fe_sp1 en) -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. rewrite <- MM. exact (Hfr4 a Ha H1 H2). }
apply (SEP PB CTX0 en ly S Hp W regs4 mem4 md4 k HPRE).
split.
{ split; [exact HJ4|].
  split.
  { intros a Ha Hn. rewrite KEEP; [exact (HWINk a Ha Hn) | | |];
    lia. }
  split; [unfold spZ; rewrite P2; exact HSP2|].
  split.
  { intros r o Hro. pose proof (pfk_saved_rng r o Hro) as Ho.
    apply (pfg_val_keep W W mem mem4 _ 8 _ (HSAV r o Hro)).
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP;
    lia. }
  split.
  { intros a Ha. apply Hpres4. rewrite MM. exact (HPRES a Ha). }
  split; [rewrite P3; rewrite (RK 3%bv ltac:(pft_in)); exact H3|].
  split; [rewrite P4; rewrite (RK 4%bv ltac:(pft_in)); exact H4|].
  split.
  { intros a Hro Hno Herr.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(sg & Hin & _ & Hr) | Hr];
      [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
    pose proof (@pa_segs_low _ _ PA a Hi) as Hlo.
    rewrite KEEP.
    - exact (HRODk a Hro Hno Herr).
    - lia.
    - intros Hvx. exact (pft_vimg en nd ly S Hp W mem md Lam (fe_peak en) (fe_cnt en) (fe_fail en)
        (fe_ran en) (fe_most en) (fe_own en) HAR HLED HVN HCEIL a Hvx Hi).
    - lia. }
  intros H0. apply Hmn4. rewrite MM. exact (HMNk H0). }
split.
{ split; [exact HROOM|].
  rewrite app_nil_r in HPD.
  exists Lam. split.
  { eapply Permutation_trans; [exact HPL|]. apply Permutation_app_tail.
    apply Permutation_sym. exact HPD. }
  split.
  { eapply Permutation_trans; [exact HPB|]. apply Permutation_app_tail.
    unfold prhPj_hbl. apply Permutation_map. apply Permutation_sym. exact HPD. }
  split.
  { apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem4 Lam _ _ _ _ _ _ HLED).
    - intros a Ha. pose proof (pst_in_img_B a Ha) as Hi.
      pose proof (@pa_segs_low _ _ PA a Hi) as Hlo.
      apply KEEP.
      + lia.
      + intros Hvx. exact (pft_vimg en nd ly S Hp W mem md Lam (fe_peak en) (fe_cnt en) (fe_fail en)
          (fe_ran en) (fe_most en) (fe_own en) HAR HLED HVN HCEIL a Hvx Hi).
      + lia.
    - intros a kk i Hin Hi.
      destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hin)
        as (Hk0 & Ha0 & Hak & Ha16 & Hab & Hhp).
      assert (Hkc : 0 <= kk + cf_head) by lia.
      pose proof (req_size_pos (kk + cf_head) Hkc) as [Rk1 Rk2].
      assert (Hrng : a - cf_head <= a - cf_head + i < a - cf_head + req_size (kk + cf_head))
        by (unfold prh_head_wide in HEAD8; lia).
      apply KEEP.
      + lia.
      + intros Hvx.
        destruct (pft_apart_core en nd ly S Hp W mem md Lam (fe_peak en) (fe_cnt en) (fe_fail en)
          (fe_ran en) (fe_most en) (fe_own en) a kk (a - cf_head + i) HAR HLED HVN HCEIL Hin Hrng Hvx) as (_ & Hav & _).
        unfold prh_head_wide in HEAD8. lia.
      + lia.
    - intros a kk Hin Hab. exact Hab.
    - apply Permutation_refl. }
  split; [intros H0; exfalso; lia|].
  intros _. unfold pj_zeroR. apply pft_garr8_of_aview.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
  - intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat.
    assert (Hj56 : 0 <= Z.of_nat j < 56) by lia.
    rewrite (Heff (Z.of_nat j) Hj56). reflexivity. }
exact HRE.
Qed.

(* ================================================================ THE SEGMENT ==================== *)
Theorem pfs_LX_holds : forall PB FX CTX0,
  pf_texts (SK := SK) B ARx PB FX -> pfs_EP (SK := SK) B ARx FX ->
  pfs_LX (SK := SK) B ARx PB FX CTX0.
Proof.
intros PB FX CTX0 TXT SEP en nd ly S Hp W regs mem md k HPRE HNODE HLX.
pose proof TXT as (FFREE & _).
apply (pft_S1 PB FX CTX0 en nd (fn_Dy nd ++ fn_Ds nd) ly S Hp W regs mem md k _ FFREE HPRE HNODE HLX).
intros ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HI1.
apply (pft_S2 PB FX CTX0 en nd (fn_Ds nd) ly1 S1 Hp1 W1 regs1 mem1 md1 k1 _ FFREE HPRE HNODE HI1).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HI2.
assert (HI2' : pft_inv FX en nd (fn_Ds nd ++ []) ly2 S2 Hp2 W2 regs2 mem2 md2 k2)
  by (rewrite app_nil_r; exact HI2).
apply (pft_S3 PB FX CTX0 en nd [] ly2 S2 Hp2 W2 regs2 mem2 md2 k2 _ FFREE HPRE HNODE HI2').
intros ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HI3.
exact (pft_S4 PB FX CTX0 en nd ly3 S3 Hp3 W3 regs3 mem3 md3 k3 TXT SEP HPRE HNODE HI3).
Qed.

End tl.
