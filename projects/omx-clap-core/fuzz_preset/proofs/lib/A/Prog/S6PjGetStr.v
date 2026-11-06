(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 509 of its 547 lines of code are new or changed and 740 lines of the source are left out. *)
(* fuzz_preset image A, slice S6: a Theorem Labs lane's program walk of pj_get_str (32 instructions) over the ONE image-A program
   listing (lib/A/Listing_prog.v, a Theorem Labs lane), generic in the image facts (Context PAImg A_prog_listing) and in the
   allocator relation ARx (LAWS : AR_laws_x .. cf_head), concluding the text tpj_get_str_specX from the text
   tpj_get_specX of its one callee pj_get, in srealizes / SRr form.
   THE MEMORY INVARIANT (a Theorem Labs lane's generic-P form): the walk is pj_get_str_holds_P, for every P with
   srr_inv_laws SEGS P, from tpj_get_specXP P to tpj_get_str_specXP P (a Theorem Labs lane's generalisations of the m-form texts,
   lib/A/Prog/S6PjStrcmp.v section (4), commit b45105596b2 blob c6208f606c8e; the call composes
   with the callee's text in that form, so no srr_inv_call). Its runs carry m |-> (P mem -> P m) (YSRrMemnorm.v
   paj_run_x_inv, laws srr_inv_laws_imp; 5ffa8525936b on the kit's cut 7cdbb61b5fa0). The kit's m-form text
   (on the cut PRH_FnPj.v 5aca5cbe2cfb) is the instance pj_get_str_holds at P := YAkMemnorm.memnorm SEGS (conversion
   tpj_get_str_specX_of_P). The old statement (the 3f0953cd536 text) has no corollary: The TEXT changed (fpostm, fpre's raZ
   bound, which the call of pj_get discharges from its return slot by PRW_StepKit.v pa_slot_lt_ceil_b, 0df3991c13f4, commit c50d0958c0b).
   Texts: the kit's cut 7cdbb61b5fa0 (lib/A/PRH_FnPj.v 5aca5cbe2cfb, PRH_Reader.v 4266e709561a, PRH_Base.v ef7c8ca98529).
   Engine on the cut: YC80x.v 14f84f225e8f / YC1fPx.v 7814b594066f (paj_run_x, paj_run_tok_x), YCbqG.v 219748197d6b
   (ajournal_x), YCbqGcall.v c1fcd07d2537 (aj_call_x_sp, the call of pj_get); lib/A/Prog/S1Ledger.v 8cf15eeb6311
   (prh_ledger_kept_aview); listing Listing_prog.v 7ed1529926bd / PAImg_prog.v 505a51ff7d08. History: first proved on
   the kit's preview walkkit-next 3f0953cd536 over listing v4 (a working branch 7c8ffeba5035). The code after the call runs from a FRESH seat (pa_entry_st_ok_full) of the state the call returns,
   whose node region names the member's type and str words.
   Rule 24: no donor (proof-index pj_get_str 2026-10-29: released hits are the plain / UBSan images' pj_get_str
   only; grep of the cold/h-hpreset-7-* and cold/h-rw-pre-* lane heads by name and A / B entry address).
   RE-FIT 2026-10-29 onto the #102 kit walkkit-next f97c8b2f046b (PRH_FnPj.v 908f34f0beaa, PRH_Base.v fdb45545469b,
   S1Ledger.v 8cf15eeb6311, S6PjStrcmp.v 08bc26a7e4e3): the ledger prh_ledger .. ran most own is threaded through
   gs_lam_low and the call of pj_get; fpre's last conjunct frm_zero (FRM0-ENTRY) passes from the entry's fpre to
   pj_get's (same float state fx).
   Numerals: 16 (LENGTH: pj_get_str's frame, the pi_frame F_pj_get_str), 24 / 28 (LENGTH: node-header and return-slot
   offsets), 4 (WORD: the tag of PjTree.JStr), 8 / 3 / 4 (LENGTH: word, granule log, stack alignment); 2 ^ 44 / 2 ^ 46
   / 2 ^ 47 / 2 ^ 47 - 2 ^ 23 (DERIVED: shadow and stack bounds); atom indices 2, 8, 10, 32 .. 35 (DERIVED: the engine's
   numbering). No address literal: addresses are pa_sigma / pa_val of PAImg_prog.v, offsets computed from its slots. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnPj CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon S6PjStrcmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* pj_get_str's offset in the listing (DERIVED: its slot times 4, PAImg_prog A_entry_pj_get_str) *)
Definition AF_gs : Z := 4 * Z.of_nat (A_prog_slot AS_pj_get_str).
(* the shadow base atom (an extra env slot, 32) and the span the token engine checks it against *)
Definition GS_Bx : sv := SOff 32 0.
Definition GS_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* ---- the entry seat: the own frame of 16 bytes below the entry sp (atom 2), the GOT word of the shadow base and the
   shadow-base cell ---- *)
Definition gs_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition gs_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_gs : sstate := mkSS AF_gs sr_atoms gs_regions None gs_facts.
(* ---- the seat after the call, at the call's return slot (AF_gs + 28), over the registers the call returns: sp is atom 2
   (the entry sp - 16), s0 the shadow base (atom 8, the second stretch's shadow base), a0 the member pj_get returned
   (atom 10); the frame holds the entry s0 (atom 32) and ra (atom 33); when a0 <> 0 the member's type word (atom 34)
   and str word (atom 35) ---- *)
Definition GS_Bx2 : sv := SOff 8 0.
Definition gs_stk2 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition gs_node : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0))].
Definition gs_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition gs_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (10%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3)] [] [].
Definition ss_gs2 : sstate := mkSS (AF_gs + 28) sr_atoms [gs_stk2; gs_node] None gs_facts2.
Definition ss_gs0 : sstate := mkSS (AF_gs + 28) sr_atoms [gs_stk2] None gs_facts0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg A_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).

Definition gs_E (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Definition gs_E2 (regs : bvmap 5 word) (s0 ra ty st : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (map (Z_to_bv 64) [s0; ra; ty; st])).
Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALib B.
(* image facts, discharged at PI_prog_A: the entry (DERIVED: slot * 4, PAImg_prog A_entry_pj_get_str), and the GOT word
   of the shadow base and the shadow cell lie in the image's segments *)
Hypothesis Hent : SIGMA AS_pj_get_str = BASE + AF_gs.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* image fact, discharged at PI_prog_A: the image starts at YImgTop.IMG_LO *)
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO.
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* alloc.c's statics (prh_img_A's generated addresses) are below alloc_ceiling *)
Lemma gs_pst_low : forall a, Exists (in_zr a) PST -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a H. apply Exists_exists in H as (r & Hin & Hr). pose proof asan_consts as (C1 & _).
vm_compute in Hin. unfold in_zr in Hr.
repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
(* a harness block of the ledger lies below alloc_ceiling, its head too *)
Lemma gs_lam_low : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> 4096 <= a - 16 /\ 0 <= k /\ a + k <= YM05.alloc_ceiling /\
    In (a - 16, k + 16) (ablocks B ly S) /\ In (a - 16) Hp.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & Hhp & _).
change (@cf_head CP) with 16 in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) HAR Hab) as (_ & H4096 & Hc & _).
rewrite gs_req in Hc by lia. repeat split; try lia; assumption.
Qed.

Lemma gs_frames : STK_pj_get_str (PI := prh_img_A) = 16 + STK_pj_get (PI := prh_img_A) /\
  STK_pj_get (PI := prh_img_A) = 80 + 2 * ESTACK.
Proof. split; vm_compute; reflexivity. Qed.

Lemma gs_entry : forall ly S Hp W (regs : bvmap 5 word) mem md ch,
  afn_pre_x SEGS B ARx (STK_pj_get_str (PI := prh_img_A)) ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (gs_E regs) ss_gs (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gs)) mem (seg_rom SEGS))) /\
  sh_ok SEGS GS_Bx [] (gs_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
pose proof (pal_got_cell B TL) as HgcD.
assert (HgL : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd).
{ intros i Hi. destruct (Hobj i Hi) as [H1 H2]. split; apply (@pa_segs_low _ _ PA); assumption. }
destruct (HgL 0 ltac:(lia)) as [HgotR HcellR]. destruct (HgL 7 ltac:(lia)) as [HgotR7 HcellR7].
destruct gs_frames as [FS FS2].
assert (Hes : ESTACK = 4096) by reflexivity.
set (E := gs_E regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold gs_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold gs_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold gs_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx. unfold ss_gs. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gs_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 GS_Bx SHADOW_OFF);
    [cbn [sv_denot GS_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold gs_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS FS2 Hes.
  unfold kLowMemEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [gs_facts f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
    revert Hslo Hshi H47 Hceil C1 FS FS2 Hes Hstk0 Hal16; clear; intros; repeat split; lia|].
  split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* a shadow check of a load from the member node (atom 10) inside the kids block's user range *)
Ltac gs_sh EM F8 S08 F10 Hz Hbs :=
lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
cbn [ms_mem]; rewrite ?EM; unfold GS_Bx2;
rewrite !U_SOff; rewrite ?ew_ewset_other by lia;
rewrite ?F8, ?S08, ?F10, ?Hz; unfold w64;
rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia);
rewrite ?zcanon_id by (unfold M64, SHADOW_OFF; lia);
lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
  change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
eapply block_shadow_range; [exact Hbs | lia | lia].

Theorem pj_get_str_holds_P : forall Pm : (word -> option byte) -> Prop, srr_inv_laws SEGS Pm ->
  tpj_get_specXP (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK Pm ->
  tpj_get_str_specXP (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK Pm.
Proof.
intros Pm PLAW GET. unfold tpj_get_str_specXP.
intros ly S Hp W regs mem md ch o k kname t D Lam peak cnt fail ran most own [HPRE [HROD [HTOP [HRAZ HFRM]]]] H10 H11 HO HK HLED.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct gs_frames as [FS FS2]. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (gs_entry ly S Hp W regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
remember (gs_E regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold gs_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold gs_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HPM : Pm mem -> Pm mem) by (intros h; exact h).
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW)).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_gs)) with (Z_to_bv 64 (BASE + AF_gs)).
(* ---- slots 0-6: the frame, s0 = the shadow base, the call of pj_get ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM GS_Bspan; [gs_awr regs Usp|].
(* ---- the call state: the frame's two words written, every other byte as at entry ---- *)
clear HF HG.
assert (Hsp47 : YM05.alloc_ceiling <= spZ regs - STK_pj_get_str (PI := prh_img_A) /\ spZ regs <= 2 ^ 47) by lia.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hn. apply (gs_mr_keep E (ss_mem ss_gs) _ _ a HFr); [|exact Ha].
  intros (r & Hin & Hr). vm_compute in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr|..]; lia. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; unfold aview, mbyte; rewrite (KM a Ha Hn); reflexivity).
assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KA; lia).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
assert (HspT : spZ (ms_regs ms) = spZ regs - 16)
  by (unfold spZ at 1; rewrite R2, Usp; rewrite unsigned_lit_small by lia; lia).
(* pj_get's premises at the call state *)
assert (HROD1 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) (ms_mem ms)))
  by exact (gs_rod_kept B W W mem (ms_mem ms) HROD KL).
assert (HK1 : cstr_ok (PA := PA) W (ms_mem ms) k kname) by exact (gs_cstr_kept W W mem (ms_mem ms) k kname HK KL).
assert (HLED1 : prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W (ms_mem ms) Lam peak cnt fail ran most own).
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W (ms_mem ms) Lam peak cnt fail ran most own HLED).
  - intros a Ha. apply KL. exact (gs_pst_low a Ha).
  - intros a k0 i Hin Hi. change (@cf_head CP) with 16.
    destruct (gs_lam_low ly S Hp W mem md Lam peak cnt fail ran most own a k0 HAR HLED Hin) as (H4 & Hk0 & Hc & _). apply KL. lia.
  - intros a k0 _ H. exact H.
  - apply Permutation_refl. }
assert (HO1 : o = 0 \/ pj_nodeR SEGS (mrestrict (w_H W) (ms_mem ms)) (prh_lin Lam) o t D /\
  prhPj_rslot (PA := PA) B (STK_pj_get (PI := prh_img_A)) ly S W (ms_regs ms) (ms_mem ms) o).
{ destruct HO as [Ho0 | (Hnode & Hrs)]; [left; exact Ho0 | right].
  destruct Hrs as (H4096 & Hplace & Hamr & Hwin & HRA & HHU).
  unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hamr.
  split.
  - apply (pj_nodeR_frame SEGS t (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) (prh_lin Lam) o D Hnode).
    apply gs_agree. intros x Hx. destruct Hx as [Hx | (b & Hb & Hx)].
    + apply KM; [lia|]. intros Hc. apply (Hwin x Hx). lia.
    + pose proof (pj_nodeR_lblk t _ _ _ _ Hnode b Hb) as Hl. unfold prh_lin in Hl. destruct b as [a0 k0].
      destruct (gs_lam_low ly S Hp W mem md Lam peak cnt fail ran most own a0 k0 HAR HLED Hl) as (H4 & _ & Hc & _).
      unfold pj_holdsR in Hx. cbn [fst snd] in Hx. apply KM; lia.
  - split; [exact H4096|]. split.
    { destruct Hplace as [Hp1 | [Hp2 | Hp3]]; [left; exact Hp1 | right; left; exact Hp2 | right; right; rewrite HspT; lia]. }
    split; [unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; exact Hamr|].
    split; [intros a Ha; rewrite HspT; intros Hc; apply (Hwin a Ha); lia|].
    split.
    + eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KL. lia.
    + intros s0 Hs. pose proof (gs_hull_low o 56 s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs). rewrite KL by lia. apply HHU. exact Hs. }
assert (Ha0 : getr (ms_regs ms) 10 = w64 o) by (rewrite R10, E10; exact H10).
assert (Ha1 : getr (ms_regs ms) 11 = w64 k) by (rewrite R11, E11; exact H11).
(* ---- the call of pj_get, by its text ---- *)
assert (HTOP1 : spZ (ms_regs ms) + 64 <= ly_stk_hi ly) by (rewrite HspT; lia).
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W E _ ms (STK_pj_get_str (PI := prh_img_A)) (spZ regs) []
    ly S Hp W mem md [] ly S Hp _ 0 (STK_pj_get (PI := prh_img_A)) [] (-16) _ [] _ HS eq_refl HJ).
  - exact HspT.
  - reflexivity.
  - lia.
  - rewrite FS2. lia.
  - rewrite FS. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - pose proof (pa_base_lo (PL := PL_prog_A) (PI := PA)) as HBLO. rewrite PAB in HBLO. unfold IMG_LO in HBLO.
    pose proof (@pa_B_ok _ _ PA) as HB. rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite R8, E32. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF. lia.
  - intros HPRE1.
    (* fpre's raZ bound: the call's return pc is a listing slot (PRW_StepKit.v pa_slot_lt_ceil_b, evar-free) *)
    assert (HRAZ1 : raZ (ms_regs ms) < YM05.alloc_ceiling).
    { unfold raZ. rewrite R1.
      lazymatch goal with |- bv_unsigned (Z_to_bv 64 (_ + ?N)) < _ =>
        pose proof (@pa_B_ok _ _ PA) as HB; pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) N) as HSL;
        rewrite unsigned_lit_small by lia;
        apply HSL; [lia | vm_compute; reflexivity] end. }
    exact (GET ly S Hp W (ms_regs ms) (ms_mem ms) _ [] o k kname t D Lam peak cnt fail ran most own
      (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 HFRM)))) Ha0 Ha1 HO1 HK1 HLED1).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HP2 & HQ2).
(* ---- after the call: registers, the frame's two words, the results ---- *)
destruct HQ2 as ((EHp & ES2 & Eab & HLED2 & HROOM2 & HRES2) & HK2). subst Hp2.
(* the invariant across the call: the run's, then pj_get's keep *)
assert (HPM2 : Pm mem -> Pm mem2) by (intros h; exact (HK2 (HPM h))). clear HPM HK2.
assert (P2 : getr regs2 2%bv = getr (ms_regs ms) 2%bv).
{ pose proof (HP2 2 ltac:(unfold acallee_saved; lia)) as H. replace (Z_to_bv 5 2) with (2%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (P8 : getr regs2 8%bv = getr (ms_regs ms) 8%bv).
{ pose proof (HP2 8 ltac:(unfold acallee_saved; lia)) as H. replace (Z_to_bv 5 8) with (8%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (Sp2 : spZ regs2 = spZ regs - 16) by (unfold spZ; rewrite P2; exact HspT).
assert (S08 : getr regs2 8%bv = Z_to_bv 64 SHADOW_OFF) by (rewrite P8, R8, E32; reflexivity).
assert (E8 : ew E 8 = getr regs 8%bv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
set (s0e := bv_unsigned (getr regs 8%bv)). set (rae := bv_unsigned (getr regs 1%bv)).
assert (Hs0r : 0 <= s0e < 2 ^ 64) by (subst s0e; pose proof (bv_unsigned_in_range 64 (getr regs 8%bv)) as H; exact H).
assert (Hrar : 0 <= rae < 2 ^ 64) by (subst rae; pose proof (bv_unsigned_in_range 64 (getr regs 1%bv)) as H; exact H).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & KJc & _).
assert (VSL : forall od e v, In (YP09.mkChunk od (CVal 8 e))
    [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  (od = -16 \/ od = -8) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs + od) 8 v).
{ intros od e v Hin Hod He Hv.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    pose proof (st_ok_region_nth SEGS E ss _ 0 (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0
      [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) HS eq_refl) as RG0 end.
  pose proof (slot_of_region SEGS E _ (spZ regs) _ _ _ _ _ od e v RG0 Usp Hin He Hv) as V0.
  cbn [ms_mem restrict] in V0.
  apply (val_mem_kept SEGS (w_H W) (w_H W2) (ms_mem ms) mem2 (spZ regs + od) 8 v); [|exact V0].
  intros kk Hkk. apply KJc; lia. }
assert (VS0 : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs + -16) 8 s0e).
{ apply (VSL (-16) (SOff 8 0) s0e (or_introl eq_refl) (or_introl eq_refl)); [|exact Hs0r].
  cbn [sv_denot]. rewrite E8, Z.add_0_r. subst s0e. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (VRA : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs + -8) 8 rae).
{ apply (VSL (-8) (SOff 1 0) rae (or_intror (or_introl eq_refl)) (or_intror eq_refl)); [|exact Hrar].
  cbn [sv_denot]. rewrite E1, Z.add_0_r. subst rae. rewrite Z_to_bv_bv_unsigned. reflexivity. }
clear VSL KJc.
(* the return slot's offset, computed (no typed value) *)
lazymatch eval vm_compute in (AF_gs + 28) with ?n => assert (EAF : AF_gs + 28 = n) by (vm_compute; reflexivity) end.
rewrite <- EAF.
(* ---- the tail with a0 = 0 ---- *)
match goal with |- ?G => assert (TAIL0 : getr regs2 10%bv = w64 0 ->
  (o = 0 \/ o <> 0 /\ pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) o t D /\
     prhPj_get_str_res (mrestrict (w_H W2) mem2) (prh_lin Lam) o t D kname 0) -> G) end.
{ intros Hz0 HR0.
  set (EZ := gs_E2 regs2 s0e rae 0 0).
  assert (EL2 : forall n, (n < A_TEXT)%nat -> ew EZ n = ew (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; 0; 0])) n)
    by (intros n Hn; subst EZ; unfold gs_E2; apply Eimg_low; exact Hn).
  assert (F2 : ew EZ 2 = getr regs2 2%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
  assert (F8 : ew EZ 8 = getr regs2 8%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
  assert (F32 : ew EZ 32 = Z_to_bv 64 s0e)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F33 : ew EZ 33 = Z_to_bv 64 rae)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (Usp2 : bv_unsigned (ew EZ 2) = spZ regs - 16) by (rewrite F2; exact Sp2).
  assert (HEI2 : img_env VAL A_LIM EZ) by (subst EZ; unfold gs_E2; apply Eimg_env).
  assert (HS2 : st_ok_pi SEGS VAL EZ ss_gs0
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + (AF_gs + 28))) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_gs0. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold gs_stk2. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp2.
      split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS EZ _ (spZ regs - 16) 0 8 (SOff 32 0) s0e);
          [cbn [sv_denot]; rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        replace (spZ regs - 16 + 0) with (spZ regs + -16) by lia. exact VS0.
      + apply (chunk_ok_val SEGS EZ _ (spZ regs - 16) 8 8 (SOff 33 0) rae);
          [cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact VRA.
    - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [gs_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp2, F8, S08, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  pose proof (st_ok_pi_pin_reg' (PI := PA) EZ ss_gs0 _ 10%bv 0 HS2 ltac:(cbn [ms_regs restrict mkst]; exact Hz0) eq_refl) as HS3.
  clear HS2.
  assert (SHOK3 : sh_ok SEGS GS_Bx2 [] EZ (mrestrict (w_H W2) mem2)) by constructor.
  paj_run_tok_x_inv RUN HS3 HJ2 SHOK3 HPM2 GS_Bspan; [gs_awr0|].
  (* slots 7, 23-26: a0 = 0, the frame back, ret *)
  eapply (RET W2 _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  assert (EM : ms_mem ms0 = mem2).
  { apply functional_extensionality. intros x. apply HF. intros (r & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  prreg HS3 (1%bv : bv 5) G1. prreg HS3 (2%bv : bv 5) G2. prreg HS3 (8%bv : bv 5) G8. prreg HS3 (10%bv : bv 5) G10.
  assert (GF2 : getr (ms_regs ms0) 2%bv = getr regs 2%bv).
  { rewrite G2, Usp2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
  assert (GF8 : getr (ms_regs ms0) 8%bv = getr regs 8%bv) by (rewrite G8, F32; unfold s0e; apply Z_to_bv_bv_unsigned).
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
    by (rewrite HE; split; [intros n Hn; unfold gs_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HAEZ : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; 0; 0])) EZ)
    by (split; [intros n Hn; subst EZ; unfold gs_E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok SEGS E _ _ regs [Z_to_bv 64 SHADOW_OFF] gs_kept HS HAE ltac:(vm_compute; reflexivity)) as K1.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) EZ _ _ regs2 _ gs_kept HS3 HAEZ ltac:(vm_compute; reflexivity)) as K3.
  unfold fpost, apost_base_x.
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp, r, m, d, (0 + k1) end.
  split; [cbn [ms_regs]; rewrite G1, F33; unfold rae; rewrite Z_to_bv_bv_unsigned, Hra; reflexivity|].
  split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ2|].
  split; [exact (gs_aregs regs (ms_regs ms) regs2 (ms_regs ms0) K1 HP2 K3 GF2 GF8)|].
  split; [|exact HPM2].
  split; [reflexivity|]. split; [exact ES2|]. split; [exact Eab|]. split; [rewrite EM; exact HLED2|]. split; [exact HROOM2|].
  destruct HR0 as [Ho0 | (Hon & Hnd & Hgs)].
  - left. split; [exact Ho0 | rewrite G10; reflexivity].
  - right. split; [exact Hon|]. split; [rewrite EM; exact Hnd|]. exists 0. split; [rewrite G10; reflexivity | rewrite EM; exact Hgs]. }
(* ---- the tail with a0 = the member pj_get found ---- *)
match goal with |- ?G => assert (TAIL2 : forall z (members : list (list Z * jv)) i v kids Di,
  t = JObj members -> o <> 0 -> getr regs2 10%bv = w64 z ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) o t D ->
  nth_error members i = Some (kname, v) ->
  (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) ->
  rd_u64 SEGS (mrestrict (w_H W2) mem2) (o + 24) kids -> z = kids + 56 * Z.of_nat i ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) z v Di -> incl Di D -> G) end.
{ intros z members i v kids Di Et Hon Hz Hnode2 Hnth Hfirst Hkids Ez Hnodez Hincl.
  pose proof HJ2 as (HAR2 & _).
  (* the object's kids block, a live harness block, holds the member's node *)
  pose proof Hnode2 as Hnode2'. rewrite Et in Hnode2'. cbn [pj_nodeR] in Hnode2'.
  destruct Hnode2' as (_ & _ & num0 & str0 & kids0 & keys0 & n0 & cap0 & Hhdr0 & Es0 & En0 & Hc0 & Hcap0 & _).
  destruct Hhdr0 as (_ & _ & _ & _ & Hk0 & _).
  pose proof (gs_val8_uniq _ _ _ _ (proj2 Hkids) (proj2 Hk0) (proj1 Hkids) (proj1 Hk0)) as EK. subst kids0.
  pose proof (pj_nth_lenR members i (kname, v) Hnth) as Hil.
  destruct Hcap0 as [(Hc00 & _) | (Hcp & Hlk & _)]; [lia|].
  unfold prh_lin in Hlk.
  destruct (gs_lam_low ly2 S2 Hp W2 mem2 md2 Lam peak cnt fail ran most own kids (56 * cap0) HAR2 HLED2 Hlk)
    as (Hk4 & _ & Hkc & Hkab & Hkhp).
  assert (Hzr : 4096 <= z /\ z + 56 <= kids + 56 * cap0) by (subst z; lia).
  (* the member's type and str words *)
  destruct (gs_node_hdr _ _ _ _ _ Hnodez) as (numz & strz & kidsz & keysz & nz & capz & Hhdrz).
  destruct Hhdrz as ((Hz8 & _) & (Hty0 & Hty) & _ & (Hst0 & Hst) & _).
  (* the shadow of the kids block's user bytes (AR_laws_x field 14, alx_hshadow, at the harness head cf_head) *)
  destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp W2 mem2 md2 (kids - 16) (56 * cap0 + 16) HAR2 Hkab Hkhp) as [Hbs _].
  change (@cf_head CP) with 16 in Hbs. rewrite gs_req in Hbs by lia.
  replace (kids - 16 + 16) with kids in Hbs by lia. replace (56 * cap0 + 16 - 16) with (56 * cap0) in Hbs by lia.
  assert (Hzz : 0 <= z < 2 ^ 64) by lia.
  set (EZ := gs_E2 regs2 s0e rae (tag v) strz).
  assert (EL2 : forall n, (n < A_TEXT)%nat -> ew EZ n = ew (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; tag v; strz])) n)
    by (intros n Hn; subst EZ; unfold gs_E2; apply Eimg_low; exact Hn).
  assert (F2 : ew EZ 2 = getr regs2 2%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
  assert (F8 : ew EZ 8 = getr regs2 8%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
  assert (F10 : ew EZ 10 = getr regs2 10%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 10 10%bv eq_refl)).
  assert (F32 : ew EZ 32 = Z_to_bv 64 s0e)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F33 : ew EZ 33 = Z_to_bv 64 rae)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F34 : ew EZ 34 = Z_to_bv 64 (tag v))
    by (rewrite EL2 by (unfold A_TEXT; lia); change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F35 : ew EZ 35 = Z_to_bv 64 strz)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (Usp2 : bv_unsigned (ew EZ 2) = spZ regs - 16) by (rewrite F2; exact Sp2).
  assert (Uz : bv_unsigned (ew EZ 10) = z) by (rewrite F10, Hz; unfold w64; apply unsigned_lit_small; exact Hzz).
  assert (HEI2 : img_env VAL A_LIM EZ) by (subst EZ; unfold gs_E2; apply Eimg_env).
  assert (HS2 : st_ok_pi SEGS VAL EZ ss_gs2
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + (AF_gs + 28))) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_gs2. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold gs_stk2, gs_node. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite Usp2. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS EZ _ (spZ regs - 16) 0 8 (SOff 32 0) s0e);
            [cbn [sv_denot]; rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
          replace (spZ regs - 16 + 0) with (spZ regs + -16) by lia. exact VS0.
        * apply (chunk_ok_val SEGS EZ _ (spZ regs - 16) 8 8 (SOff 33 0) rae);
            [cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
          replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact VRA.
      + rewrite Uz. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS EZ _ z 0 4 (SOff 34 0) (tag v));
            [cbn [sv_denot]; rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
          rewrite Z.add_0_r. exact Hty.
        * apply (chunk_ok_val SEGS EZ _ z 16 8 (SOff 35 0) strz);
            [cbn [sv_denot]; rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
          exact Hst.
    - apply pairwise_disjoint_of_extents. unfold gs_stk2, gs_node, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?Usp2, ?Uz.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - split; [|split; [exact I | exact I]].
      cbn [gs_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp2, Uz, F8, S08, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  assert (SHOK2 : sh_ok SEGS GS_Bx2 [] EZ (mrestrict (w_H W2) mem2)) by constructor.
  (* the shadow checks of the member's loads: inside the kids block's user range *)
  assert (UB : U EZ GS_Bx2 = SHADOW_OFF)
    by (unfold GS_Bx2; exact (U_atom EZ 8 SHADOW_OFF (eq_trans F8 S08) ltac:(unfold SHADOW_OFF; lia))).
  assert (UZ : U EZ (SOff 10 0) = z) by exact (U_atom EZ 10 z (eq_trans F10 Hz) Hzz).
  paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM2 GS_Bspan.
  all: try gs_awr0.
  all: try (match goal with |- range_addressable _ _ _ _ => idtac end;
    cbn [ms_mem]; rewrite ?UB, ?UZ;
    change (rd_of SEGS (mrestrict (w_H W2) mem2)) with (aview SEGS (w_H W2) mem2);
    eapply (block_shadow_range (aview SEGS (w_H W2) mem2) SHADOW_OFF kids (56 * cap0)); [exact Hbs | lia | lia]).
  gs_memeq HF EM1. clear HF HG.
  (* the registers the caller kept, for the post *)
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
    by (rewrite HE; split; [intros n Hn; unfold gs_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HAEZ : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; tag v; strz])) EZ)
    by (split; [intros n Hn; subst EZ; unfold gs_E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok SEGS E _ _ regs [Z_to_bv 64 SHADOW_OFF] gs_kept HS HAE ltac:(vm_compute; reflexivity)) as K1.
  (* slot 14: bne a1, a2 on the member's type word against JStr's tag *)
  psrr_branch_tok RUN BR HS2 SHOK2 GS_Bspan.
  - (* taken: the member is not a string; a0 = 0, the frame back, ret *)
    rewrite branch_ne_U in Hc. gs_tag_in Hc v F34. rewrite U_SLit in Hc.
    rewrite (zcanon_id 4) in Hc by (unfold M64; lia).
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM2 GS_Bspan; [gs_awr0|].
    gs_memeq HF EM2. clear HF HG.
    eapply (RET W2 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch type of HS2 with st_ok_pi _ _ ?E'' _ (restrict _ ?msF) =>
      assert (EMf : ms_mem msF = mem2) by (rewrite EM2; exact EM1);
      assert (HAE2 : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; tag v; strz])) E'')
        by (eapply env_agree_trans; [exact HAEZ | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
      pose proof (regs_kept_of_st_ok_pi (PI := PA) E'' _ _ regs2 _ gs_kept HS2 HAE2 ltac:(vm_compute; reflexivity)) as K3 end.
    prreg HS2 (1%bv : bv 5) G1. prreg HS2 (2%bv : bv 5) G2. prreg HS2 (8%bv : bv 5) G8. prreg HS2 (10%bv : bv 5) G10.
    rewrite ?ew_ewset_other in G1 by lia. rewrite ?ew_ewset_other in G2 by lia. rewrite ?ew_ewset_other in G8 by lia.
    assert (GF2 : getr (ms_regs ms1) 2%bv = getr regs 2%bv).
    { rewrite G2, Usp2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
    assert (GF8 : getr (ms_regs ms1) 8%bv = getr regs 8%bv) by (rewrite G8, F32; unfold s0e; apply Z_to_bv_bv_unsigned).
    unfold fpost, apost_base_x.
    lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp, r, m, d, (0 + k1) end.
    split; [cbn [ms_regs]; rewrite G1, F33; unfold rae; rewrite Z_to_bv_bv_unsigned, Hra; reflexivity|].
    split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ2|].
    split; [exact (gs_aregs regs (ms_regs ms) regs2 (ms_regs ms1) K1 HP2 K3 GF2 GF8)|].
    split; [|exact HPM2].
    split; [reflexivity|]. split; [exact ES2|]. split; [exact Eab|]. split; [rewrite EMf; exact HLED2|]. split; [exact HROOM2|].
    right. split; [exact Hon|]. split; [rewrite EMf; exact Hnode2|]. exists 0. split; [rewrite G10; reflexivity|].
    rewrite EMf, Et. unfold prhPj_get_str_res. right. exists i, v, kids.
    split; [exact Hnth|]. split; [exact Hfirst|]. split; [exact Hkids|].
    destruct v; try reflexivity. exfalso. apply Hc. reflexivity.
  - (* not taken: the member is a string; a0 = its str word *)
    rewrite branch_ne_U in Hc. gs_tag_in Hc v F34. rewrite U_SLit in Hc.
    rewrite (zcanon_id 4) in Hc by (unfold M64; lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    destruct (gs_tag4 v Hc) as (s & ->).
    paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM2 GS_Bspan.
    all: try gs_awr0.
    all: try gs_sh EM1 F8 S08 F10 Hz Hbs.
    gs_memeq HF EM2. clear HF HG.
    eapply (RET W2 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch type of HS2 with st_ok_pi _ _ ?E'' _ (restrict _ ?msF) =>
      assert (EMf : ms_mem msF = mem2) by (rewrite EM2; exact EM1);
      assert (HAE2 : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; tag (JStr s); strz])) E'')
        by (eapply env_agree_trans; [exact HAEZ | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
      pose proof (regs_kept_of_st_ok_pi (PI := PA) E'' _ _ regs2 _ gs_kept HS2 HAE2 ltac:(vm_compute; reflexivity)) as K3 end.
    prreg HS2 (1%bv : bv 5) G1. prreg HS2 (2%bv : bv 5) G2. prreg HS2 (8%bv : bv 5) G8. prreg HS2 (10%bv : bv 5) G10.
    rewrite ?ew_ewset_other in G1 by lia. rewrite ?ew_ewset_other in G2 by lia. rewrite ?ew_ewset_other in G8 by lia.
    rewrite ?ew_ewset_other in G10 by lia.
    assert (GF2 : getr (ms_regs ms1) 2%bv = getr regs 2%bv).
    { rewrite G2, Usp2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
    assert (GF8 : getr (ms_regs ms1) 8%bv = getr regs 8%bv) by (rewrite G8, F32; unfold s0e; apply Z_to_bv_bv_unsigned).
    (* the member's string, from its node *)
    pose proof Hnodez as Hnz. cbn [pj_nodeR] in Hnz.
    destruct Hnz as (_ & _ & num1 & str1 & kids1 & keys1 & n1 & cap1 & Hh1 & _ & _ & _ & _ & k1' & Hcs & ED).
    destruct Hh1 as (_ & _ & _ & (Hs10 & Hs1) & _).
    pose proof (gs_val8_uniq _ _ _ _ Hst Hs1 Hst0 Hs10) as Estr. subst str1.
    unfold fpost, apost_base_x.
    lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp, r, m, d, (0 + k1) end.
    split; [cbn [ms_regs]; rewrite G1, F33; unfold rae; rewrite Z_to_bv_bv_unsigned, Hra; reflexivity|].
    split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ2|].
    split; [exact (gs_aregs regs (ms_regs ms) regs2 (ms_regs ms1) K1 HP2 K3 GF2 GF8)|].
    split; [|exact HPM2].
    split; [reflexivity|]. split; [exact ES2|]. split; [exact Eab|]. split; [rewrite EMf; exact HLED2|]. split; [exact HROOM2|].
    right. split; [exact Hon|]. split; [rewrite EMf; exact Hnode2|]. exists strz. split; [rewrite G10, F35; reflexivity|].
    rewrite EMf, Et. unfold prhPj_get_str_res. right. exists i, (JStr s), kids.
    split; [exact Hnth|]. split; [exact Hfirst|]. split; [exact Hkids|].
    split; [rewrite <- Ez; split; [exact Hst0 | exact Hst]|].
    exists k1'. split; [exact Hcs|]. apply Hincl. rewrite ED. left. reflexivity. }
destruct HRES2 as [(Ho0 & Hz0) | (Hon & Hnode2 & z & Hz & Hres)].
{ apply TAIL0; [exact Hz0 | left; exact Ho0]. }
destruct t as [| | | txt bits | s | items | members]; cbn [prhPj_get_res] in Hres;
  try (subst z; apply TAIL0; [exact Hz | right; split; [exact Hon|]; split; [exact Hnode2 | reflexivity]]).
destruct Hres as [(Hnone & ->) | (i & v & kids & Di & Hnth & Hfirst & Hkids & Ez & Hnodez & Hincl)].
- apply TAIL0; [exact Hz | right; split; [exact Hon|]; split; [exact Hnode2|]]. cbn [prhPj_get_str_res]. left. split; [exact Hnone | reflexivity].
- exact (TAIL2 z members i v kids Di eq_refl Hon Hz Hnode2 Hnth Hfirst Hkids Ez Hnodez Hincl).
Qed.

(* The m-form text: the walk at the invariant YAkMemnorm.memnorm *)
Theorem pj_get_str_holds :
  tpj_get_specX (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK ->
  tpj_get_str_specX (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK.
Proof.
intros GET. apply (tpj_get_str_specX_of_P (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK).
exact (pj_get_str_holds_P (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS) GET).
Qed.

End f.
End d.

Print Assumptions pj_get_str_holds_P.
Print Assumptions pj_get_str_holds.
Set Printing All.
Check pj_get_str_holds_P.
Check pj_get_str_holds.
Unset Printing All.
