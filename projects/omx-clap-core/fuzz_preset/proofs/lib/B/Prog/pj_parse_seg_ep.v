(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: two lemmas of pj_parse's image-B walk (fuzz_preset asan-ubsan, B 0x862ec; the cuts of
   lib/B/Prog/pj_parse_defs.v).
   proves no function (kind: segment lemma).
   (1) pjp_seg_C3_holds: the epilogue from the cut pjp_C3 (+0x74): `ld ra, 40(sp); ld s0, 32(sp); addi sp, sp, 48;
       ret`. The symbolic state at the cut (pje_st_ok) has one READ-ONLY region, pj_parse's 48-byte frame at sp
       (atom 2), with the saved s0 at +32 and the saved ra at +40 as the extra atoms 33 and 32 (pjp_inv's val_mem
       facts). The runner (YC80x / YC1fPx paj_run_x) runs the two loads and the addi and stops at the ret; the ret is
       YC1fP's paj_ret_at. The journal is pjp_invR's at wle' SEGS RZ_cf (from the rebased entry, pj_parse_defs.v
       pjp_wb), so the run is the runner over R at that relation (paj_run_xR) and the segment concludes SRr' SEGS
       RZ_cf; the ret's SRr step is lifted (YA0nH.SRr_SRrG). The journal is unchanged by the run (no store: the region
       has an empty write range, so the memory is the cut's memory); at the ret it is unbased to the entry state at
       parse_value's budget WS (the kit's post at wbudget CW 0, fpostWF_xbR at wle': YCbqGwild.ajournal_xw_unbase0R with
       pjp_wb's wild-part inclusion); the window clause is pjp_invR's; the float state is
       the cut's (fpostWF's fx' := fy); the callee-saved registers are sp = sp1 + 48 = sp0, s0 restored, and
       PJP_KEPT untouched; pjp_Q is pjp_C3's (a0 untouched).
   (2) pjp_frame_kept_holds: what a callee's journal at (STK1 + e1) (sp1 + e1), e1 <= 32, keeps of pj_parse's state
       (both journals at wle', the keep statement's form).
       The bytes of [sp1 + 32, sp0 + d) lie above the callee's window and above alloc_ceiling (the journal's stack
       clause): the caller window (with pjp_inv's window clause), the saved ra / s0 and the frame's presence above
       sp1 + e1 (below it, the journal's presence clause). The cursor's shadow cells are below alloc_ceiling, so no
       journal clause keeps them: they read 0 by AR_laws_x's stack-shadow law at the callee's post state (the real
       stack [ly_stk_lo, ly_stk_hi) holds [sp1 + 8, sp1 + 32): 0 <= d). The read-only view is the journal's image
       clause (the callee's footprint leaves the sink shut; prh_pst is not read-only, S1ImgB.v pst_not_ro_B).
   Numerals: 8 / 16 / 24 / 32 / 40 / 48 (LENGTH: word, granule, slot offsets, frame); 2 ^ 46 / 2 ^ 47 (DERIVED:
   stack band); atom indices 2 / 8 / 10 / 32 / 33 / 34 (DERIVED: the engine's numbering, registers below 32, extra
   atoms from 32). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_parse_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Existing Instance prh_img_B.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at pjp_C3: the frame [sp, sp + 48) read-only, the saved s0 / ra as atoms 33 / 32 ---- *)
Definition PJE_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) 0 48 0 0
      [YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 32 0))] ].
Definition PJE_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition PJE_ss : sstate := mkSS PJP_C3 sr_atoms PJE_regions None PJE_facts.
Definition PJE_Bx : sv := SOff 34 0.
Definition PJE_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition PJE_SH : list shent := [].
Definition PJE_extra (r0 : bvmap 5 word) : list word := [getr r0 1; getr r0 8].

(* the In-list of a register literal written as Z_to_bv 5 r *)
Ltac pje_inkept :=
  unfold PJP_KEPT; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).

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
(* the allocator laws (lib/Reusable/YCbqG.v AR_laws_x, blob 83da015952), the engine's premise *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

(* pjp_Q (the kit's tpjP_Q) reads the registers only through a0 and never reads the model *)
Lemma pje_Q_a0 : forall en ly S Hp (W : world SEGS) regs regs' mem md md',
  getr regs' 10 = getr regs 10 ->
  pjp_Q B en ly S Hp W regs mem md -> pjp_Q B en ly S Hp W regs' mem md'.
Proof.
intros en ly S Hp W regs regs' mem md md' E10 HQ.
unfold pjp_Q, tpjP_Q, tpjP_ASome, tpjP_ANone in *. cbv beta in *. rewrite E10. exact HQ.
Qed.

(* ---- (2) the keep statement ---- *)
Theorem pjp_frame_kept_holds : pjp_frame_kept_stmt B ARx.
Proof.
intros en Sb fy ly S Hp W regs mem md k STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HINV HJ1 HSTK1 He1 Hd Hsink _.
destruct HINV as (_ & _ & HJ0 & HWIN & _ & Hra & Hs0 & _ & _ & HPRES & _ & HROD & _).
destruct HJ0 as (_ & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hast0 & _ & _).
destruct HJ1 as (HAR2 & Hly1 & _ & _ & _ & _ & _ & _ & F1 & _ & F3 & _ & _ & Hpres1 & Hast1 & _ & _).
destruct Hast0 as (_ & _ & _ & _ & A5 & A6 & _ & _ & _).
destruct Hast1 as (_ & _ & B3 & B4 & _ & _ & _ & _ & _).
destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L0lo & L0hi & _).
destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L1lo & L1hi & _).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold je_sp1, PJP_FR in *.
set (sp0 := je_sp0 en) in *.
assert (K : forall a, sp0 - 48 + e1 <= a < sp0 + je_d en ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply F1; lia. }
split.
{ intros a Ha. rewrite (K a ltac:(lia)). exact (HWIN a Ha). }
split.
{ intros kk Hk. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 _ (K (sp0 - 48 + 40 + Z.of_nat kk) ltac:(lia))).
  exact (Hra kk Hk). }
split.
{ intros kk Hk. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 _ (K (sp0 - 48 + 32 + Z.of_nat kk) ltac:(lia))).
  exact (Hs0 kk Hk). }
split.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 48 + e1)) as [Hlt | Hge].
  - apply Hpres1. lia.
  - apply (apresent_transfer SEGS (w_H W) (w_H W2) mem mem2 a).
    + lia.
    + intros Hi. pose proof (Hsegs a Hi). lia.
    + apply K. lia.
    + apply HPRES. lia. }
split.
{ intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  apply (alx_zshadow_byte _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 x HAR2). rewrite L1lo, L1hi. lia. }
intros a Hro Hos Her.
rewrite (F3 a); [exact (HROD a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsink].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
- intros Hp'. exact (pst_not_ro_B a Hp' Hro).
Qed.

(* ---- (1) the epilogue segment ---- *)
(* the symbolic state at the cut *)
Lemma pje_st_ok : forall (fy : YK11.FPState) (W : world SEGS) mem (regs r0 : bvmap 5 word),
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 40) 8 (raZ r0) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 32) 8 (s0Z r0) ->
  st_ok_pi (fx := fy) SEGS VAL (Eimg (PI := PA) (Ereg regs (PJE_extra r0))) PJE_ss
    (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + PJP_C3)) mem (seg_rom SEGS))).
Proof.
intros fy W mem regs r0 Hsp Hal Vra Vs0.
set (E := Eimg (PI := PA) (Ereg regs (PJE_extra r0))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (PJE_extra r0)) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = getr r0 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = getr r0 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
rewrite (restrict_mkst_fx (fx := fy)). unfold PJE_ss.
apply (pa_entry_st_ok_full (fx := fy) (PI := PA)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold PJE_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val SEGS E _ (spZ regs) 32 8 (SOff 33 0) (s0Z r0)).
    * cbn [sv_denot]. rewrite E33, Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold s0Z. apply u64_range.
    * cbn. lia.
    * exact Vs0.
  + apply (chunk_ok_val SEGS E _ (spZ regs) 40 8 (SOff 32 0) (raZ r0)).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold raZ. apply u64_range.
    * cbn. lia.
    * exact Vra.
- cbn [PJE_regions pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [PJE_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal | lia].
Qed.

Theorem pjp_seg_C3_holds : forall CTX0 CW, pjp_seg_C3 B ARx CTX0 CW.
Proof.
intros CTX0 CW en Sb fy ly S Hp W regs mem md k HPRE HWB [HINV HQ].
destruct HWB as (dp & WS & -> & HBUD & HINC).
pose proof HINV as (Hfz & Hfk & HJ & HWIN & Hsp & Hra & Hs0 & _ & HKEPT & _ & _ & _ & HMN).
unfold pjp_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as ((HAFN & _ & _) & _).
pose proof HAFN as (_ & Hret & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
assert (HSTK : 48 <= STK_pj_parse) by (apply Z.leb_le; vm_compute; reflexivity).
unfold je_sp1, je_sp0, PJP_FR in *.
assert (Hsp1 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hal1 : spZ regs mod 16 = 0) by (rewrite Hsp; Z.div_mod_to_equations; lia).
pose proof (pje_st_ok fy W mem regs (je_regs en) Hsp1 Hal1
  ltac:(rewrite Hsp; exact Hra) ltac:(rewrite Hsp; exact Hs0)) as HS.
set (E := Eimg (PI := PA) (Ereg regs (PJE_extra (je_regs en)))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (PJE_extra (je_regs en))) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E32 : ew E 32 = getr (je_regs en) 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = getr (je_regs en) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (PJE_extra (je_regs en))) E)
  by (split; [intros n Hn; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS PJE_Bx PJE_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok, PJE_SH; apply Forall_nil).
clearbody E.
unfold pjp_cfg.
(* the cut's journal is at wle' SEGS RZ_cf: the run is the runner over that relation, so the goal is SRrG at it *)
unfold SRr'.
pose (RUN := paj_run_xR (fx := fy) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RET := paj_ret_at (fx := fy) (PL := PL) (PI := PA)).
(* +0x74 .. +0x7c: the two loads and the addi; the runner stops at the ret (+0x80) *)
paj_run_tok_xR RUN HS HJ SHOK PJE_Bspan.
{ unfold awr_ok. intros a (r & Hin & Ha). unfold PJE_ss, PJE_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
(* the run stored nothing: the memory is the cut's *)
assert (MM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
  unfold PJE_ss, PJE_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10.
assert (KR : forall r, In r PJP_KEPT -> getr (ms_regs ms) r = getr (je_regs en) r).
{ intros r Hr. rewrite <- (HKEPT r Hr).
  exact (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs (PJE_extra (je_regs en)) PJP_KEPT HS HAE
    ltac:(vm_compute; reflexivity) r Hr). }
(* +0x80: the ret, to the entry's ra; it keeps the world, so its SRr step is lifted *)
apply (SRr_SRrG SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle_wle' SEGS YGcfRehidePost.RZ_cf)).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold pjp_FIN, fpostWFbm, fpostWFb, YCbqGwild.fpostWF_xbR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (YK11.mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists fy, ly, S, Hp, r, m, d, k, WS end.
split.
{ unfold YK0s.ret_ok in Hret. rewrite R1, E32, Hret. reflexivity. }
split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HBUD|].
(* the journal back at the entry state and parse_value's budget WS (YCbqGwild.ajournal_xw_unbase0R with the rebase's
   wild-part inclusion) *)
split; [apply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf))
          with (d := dp);
        [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS YGcfRehidePost.RZ_cf));
         exact HJ | exact HINC]|].
split; [intros a Ha _; rewrite MM; exact (HWIN a Ha)|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R2, Usp, Hsp. replace (spZ (je_regs en) - 48 + 48) with (spZ (je_regs en)) by lia.
    unfold spZ. apply Z_to_bv_bv_unsigned.
  - apply KR. pje_inkept.
  - apply KR. pje_inkept.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R8, E33. reflexivity.
  - apply KR. pje_inkept.
  - assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by lia.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; apply KR; pje_inkept. }
rewrite MM. unfold fQmn. split.
- apply (pje_Q_a0 en ly S Hp W regs _ mem md _); [rewrite R10, E10; reflexivity | exact HQ].
- (* the m-form keep: the cut's memory is normal (pjp_inv), and the epilogue stored nothing *)
  intros _. exact HMN.
Qed.

End ep.
