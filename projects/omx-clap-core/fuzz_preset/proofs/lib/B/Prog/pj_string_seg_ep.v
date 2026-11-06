(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment C2 of pj_string's image-B walk (fuzz_preset asan-ubsan; the cuts of
   lib/B/Prog/pj_string_defs.v): from PJS_C2 (+0x6c, fuzz_strdup's return site) to the walk's post pjs_FIN:
     +0x6c           s0 := v + 16
     +0x70 .. +0x7c  ASan check of the 8-byte store at v + 16: the engine reads the shadow byte as 0 (the shadow entry
                     [v, v + 56) of PJS2_SH, addressable at the cut)
     +0x80 .. +0x8c  a1 := (res != 0) - 1; v->str := res; a0 := a1
     +0x90 .. +0xa4  ra, s0, s1, s2 reloaded from the frame; sp += 32; ret
   The state at the cut is seated fresh (pjs2_ss): pj_string's frame at sp (atom 2) READ-ONLY with the four saved
   words as the extra atoms 32 .. 35, v's node at s0 (atom 8) with the write window [16, 24), s2 (atom 18) = the
   shadow offset (the engine's Bx). The run (pj_string_runf.v paj_run_xf_inv, YC80xf.v's frame runner carrying the
   memnorm keep as YC80x.v's memory invariant: the node may be in a caller's fake frame, which the footprint names)
   stops at the ret; YC1fP.v paj_ret_at returns to the entry ra (no memory change). The model-run position of the cut
   (fuzz_strdup's post implication at pj_string's entry position, keyed on res, and DEAD-PJSTRING from its OUTCOME
   conjunct: the kit's tip d607d12e4b0f, lib/A/PRH_FnAlloc.v:517-558) and the keep at the cut (pjs_C2,
   pjs_inv) are the walk's post's (fpostWm).
   The post: res = 0 (the chosen or refused failure) stores 0 over the zero str word, so the memory reads as at the
   cut everywhere and prh_alloc_post rides through unchanged; res <> 0 (success) writes only v + 16 .. v + 24, apart
   from the statics, every harness head (pj_string_glue.v pjs_pre_v), the new block and its head (pjs_C2) and every
   shadow byte (v is application memory). The node is lib/A/Prog/PjStringCommon.v's pjs_hdr / pjs_node_str / pjs_fd0.
   proves no function (kind: segment lemma). Section hypothesis: AR_laws_x SEGS B ARx cf_head.
   Numerals: 32 / 56 / 24 / 16 / 8 (LENGTH: frame, node, slots, str field); 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (LENGTH:
   shadow span, stack band, words); atom indices 2 / 8 / 10 / 18 / 32 .. 35 (DERIVED: the engine's numbering, the
   extras from 32). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_string_defs pj_string_glue
  pj_string_runf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Existing Instance prh_img_B.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the seated state at PJS_C2 ---- *)
Definition pjs2_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
   YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition pjs2_vreg : YP09.region := YP09.mkRegion (Some 8%nat) 0 56 16 24 [].
Definition pjs2_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 (2 ^ 47 - 64) 3);
           (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition pjs2_ss : sstate := mkSS PJS_C2 sr_atoms [pjs2_frame; pjs2_vreg] None pjs2_facts.
Definition PJS2_Bx : sv := SOff 18 0.
Definition PJS2_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition PJS2_SH : list shent := [mkSHE 8 0 56].
(* the extra atoms 32 .. 35: the entry's ra, s0, s1, s2 (the frame's saved words) *)
Definition pjs2_extra (r0 : bvmap 5 word) : list word := [getr r0 1; getr r0 8; getr r0 9; getr r0 18].

(* the chunk of a symbolic state at (base atom, offset, width) (pj_parse_seg_ent.v pje_cv / pje_cv_ok / pje_val) *)
Definition pjs2_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.

Section ep. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

Lemma pjs2_cv_ok : forall E ss ms j off w c, st_ok SEGS E ss ms -> pjs2_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold pjs2_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pjs2_val : forall E ss ms j off (w : N) e v b a, st_ok_pi SEGS VAL E ss ms ->
  pjs2_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pjs2_cv_ok E (abs_ss VAL ss) ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the seated state is a state of the cut *)
Lemma pjs2_st_ok : forall (W : world SEGS) mem (regs r0 : bvmap 5 word) v,
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 8 = w64 v -> 4096 <= v <= 2 ^ 47 - 64 -> v mod 8 = 0 -> v + 56 <= spZ regs ->
  getr regs 18 = w64 SHADOW_OFF ->
  val_mem SEGS (rdW W mem) (spZ regs + 24) 8 (raZ r0) ->
  val_mem SEGS (rdW W mem) (spZ regs + 16) 8 (s0Z r0) ->
  val_mem SEGS (rdW W mem) (spZ regs + 8) 8 (bv_unsigned (getr r0 9)) ->
  val_mem SEGS (rdW W mem) (spZ regs) 8 (bv_unsigned (getr r0 18)) ->
  (forall a, v + 16 <= a < v + 24 -> writable_at SEGS (rdW W mem) a) ->
  st_ok_pi (fx := fx) SEGS VAL (Eimg (PI := PA) (Ereg regs (pjs2_extra r0))) pjs2_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + PJS_C2)) mem (seg_rom SEGS))).
Proof.
intros W mem regs r0 v Hsp Hal H8 Hv Hv8 Hvsp H18 Vra Vs0 Vs1 Vs2 Hwr.
set (E := Eimg (PI := PA) (Ereg regs (pjs2_extra r0))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (pjs2_extra r0)) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (E32 : ew E 32 = getr r0 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = getr r0 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr r0 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr r0 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uv : bv_unsigned (ew E 8) = v) by (rewrite E8, H8; unfold w64; apply unsigned_lit_small; lia).
assert (Ush : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite E18, H18; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
rewrite (restrict_mkst_fx (fx := fx)). unfold pjs2_ss.
apply (pa_entry_st_ok_full (fx := fx) (PI := PA)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pjs2_frame, pjs2_vreg. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 0 8 (SOff 35 0) (bv_unsigned (getr r0 18))).
      -- cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
      -- cbn. lia.
      -- rewrite Z.add_0_r. exact Vs2.
    * apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 (SOff 34 0) (bv_unsigned (getr r0 9))).
      -- cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
      -- cbn. lia.
      -- exact Vs1.
    * apply (chunk_ok_val SEGS E _ (spZ regs) 16 8 (SOff 33 0) (s0Z r0)).
      -- cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold s0Z. rewrite Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold s0Z. apply u64_range.
      -- cbn. lia.
      -- exact Vs0.
    * apply (chunk_ok_val SEGS E _ (spZ regs) 24 8 (SOff 32 0) (raZ r0)).
      -- cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold raZ. apply u64_range.
      -- cbn. lia.
      -- exact Vra.
  + rewrite Uv. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia | constructor].
- cbn [pairwise_disjoint all_disjoint]. split; [|exact (conj I I)]. split; [|exact I].
  unfold extent_disjoint, pjs2_frame, pjs2_vreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uv. lia.
- split; [|split; [exact I | exact I]].
  cbn [pjs2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Uv, Ush. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* what the run keeps: every byte off v + 16 .. v + 24 *)
Lemma pjs2_keep : forall (Wx : world SEGS) E (m m' : word -> option byte) v,
  bv_unsigned (ew E 8) = v ->
  frame_of E (ss_mem pjs2_ss) (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  forall x : word, ~ (v + 16 <= bv_unsigned x < v + 24) -> mrestrict (w_H Wx) m' x = mrestrict (w_H Wx) m x.
Proof.
intros Wx E m m' v Hv HF x Hx. apply HF. intros (r & Hin & Hr). cbn [pjs2_ss ss_mem In] in Hin.
destruct Hin as [<- | [<- | []]]; cbn [pjs2_frame pjs2_vreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
rewrite Hv in Hr. lia.
Qed.

Theorem pjs_seg_C2_holds : forall CTX0, pjs_seg_C2 (SK := SK) B ARx CTX0.
Proof.
intros CTX0 en ly S Hp W regs mem md k HPRE HC2.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
destruct (pjs_pre_v B ARx LAWS CTX0 en HPRE) as (HPL & Hv4096 & Hv56 & Hv8 & Hvamr & Hvimg & Hvpst & Hvhd).
destruct en as [ly0 S0 Hp0 W0 r0 mem0 md0 ch0 d v s cs Lam peak cnt fail ran most own rpsm rpx rpos rpi rpH0 rphist].
unfold pjs_place in HPL.
unfold js_len, js_sp0, js_sp1 in *.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own] in *.
unfold pjs_pre in HPRE. cbv zeta in HPRE.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own]
  in HPRE.
destruct HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & HFWIN & HSLOT & HCEIL & _ & HSCASE & _ & HLED0 & _).
destruct HFPRE as ((HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD0 & HSTKHI).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HSLOT as (_ & _ & (_ & Hvrw) & _).
destruct HC2 as (HINV & HROOM & res & H10 & HRP0 & HRP1 & HDEAD & HPOST & HRES).
unfold pjs_inv in HINV.
unfold js_len, js_sp0, js_sp1 in HINV, HPOST, HRES.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own]
  in HINV, HPOST, HRES.
destruct HINV as (HJ & HWIN & HSP & VRA & VS0 & VS1 & VS2 & H8 & H18 & HKEPT & HFPRES & HROD & HVB & HVW & HVRA & HMN).
unfold PJS_FR in *.
set (sp0 := spZ r0) in *.
assert (HSTK : 32 <= STK_pj_string) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly.
(* res: 0, or a new block's user address below alloc_ceiling *)
assert (HRB : res = 0 \/ 4096 <= res - cf_head /\ res + Z.of_nat (length cs) + 1 <= YM05.alloc_ceiling).
{ destruct HPOST as [(_ & -> & _) | [(_ & -> & _) | (_ & H4 & _ & _ & _ & Eab & _)]]; [left; reflexivity | left; reflexivity|].
  right. assert (Hin : In (res - cf_head, Z.of_nat (length cs) + 1 + cf_head) (ablocks B ly S))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & Hb4 & Hc & _).
  assert (Rq : 1 <= req_size (Z.of_nat (length cs) + 1 + cf_head) /\
    Z.of_nat (length cs) + 1 + cf_head <= req_size (Z.of_nat (length cs) + 1 + cf_head)) by (apply req_size_pos; lia).
  lia. }
assert (Hres64 : 0 <= res < 2 ^ 64) by (destruct HRB as [-> | (Hr1 & Hr2)]; lia).
(* ---- the seated state ---- *)
assert (Hsp1 : spZ regs = sp0 - 32) by exact HSP.
pose proof (pjs2_st_ok W mem regs r0 v ltac:(lia) ltac:(rewrite Hsp1; Z.div_mod_to_equations; lia) H8 ltac:(lia)
  Hv8 ltac:(lia) H18 ltac:(rewrite Hsp1; exact VRA) ltac:(rewrite Hsp1; exact VS0) ltac:(rewrite Hsp1; exact VS1)
  ltac:(rewrite Hsp1; exact VS2) ltac:(intros a Ha; apply HVW; lia)) as HS.
set (E := Eimg (PI := PA) (Ereg regs (pjs2_extra r0))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (pjs2_extra r0)) i)
  by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (E32 : ew E 32 = getr r0 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = getr r0 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr r0 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr r0 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite E2; exact Hsp1).
assert (Uv : bv_unsigned (ew E 8) = v) by (rewrite E8, H8; unfold w64; apply unsigned_lit_small; lia).
assert (E10' : ew E 10 = Z_to_bv 64 res) by (rewrite E10, H10; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (pjs2_extra r0)) E)
  by (split; [intros n Hn; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS PJS2_Bx PJS2_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, PJS2_SH. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (UB : U E PJS2_Bx = SHADOW_OFF).
  { unfold PJS2_Bx. apply (U_atom E 18 SHADOW_OFF); [rewrite E18, H18; reflexivity | unfold SHADOW_OFF; lia]. }
  assert (UV : U E (SOff 8 0) = v) by (apply (U_atom E 8 v); [rewrite E8, H8; reflexivity | lia]).
  rewrite UB, UV. split.
  - replace (v + 0) with v by lia. replace (56 - 0) with 56 by lia. exact HVRA.
  - intros a Ha. unfold amem_range in Hvamr. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
clearbody E.
unfold pjs_cfg.
(* the memnorm keep from the entry memory, YC80x.v's runner invariant (YSRrMemnorm.v's instance) *)
pose (PMN := fun m => YAkMemnorm.memnorm SEGS mem0 -> YAkMemnorm.memnorm SEGS m).
pose proof (YSRrMemnorm.srr_inv_laws_imp SEGS _ mem0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) as PLAW.
fold PMN in PLAW.
assert (HPM : PMN (ms_mem (YK11.mkst regs (Z_to_bv 64 (BASE + PJS_C2)) mem (seg_rom SEGS)))) by exact HMN.
pose (RUN := @paj_run_xf_inv fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS PMN PLAW).
pose (RET := paj_ret_at (fx := fx) (PL := PL) (PI := PA)).
(* ---- +0x6c .. +0xa0: the str store and the epilogue; the run stops at the ret ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PJS2_Bspan.
{ (* the run writes v + 16 .. v + 24 only: in v's block (live at the cut) or the caller's fake frame of the entry *)
  intros a (r & Hin & Hr). cbn [pjs2_ss ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [pjs2_frame pjs2_vreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [lia|]. rewrite Uv in Hr.
  assert (HFP : inFP [(v, v + 56)] a) by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
  destruct HPL as [(a0 & k0 & Hin0 & Ha0 & Hk0) | [(b & m & Hin1 & _ & Hb & Hm) | (cid & pos & Hin2 & Hf & Hfm)]].
  - destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran a0 k0 most own HLED0 Hin0) as (Hk0' & Hab & _).
    assert (Rq : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head)) by (apply req_size_pos; lia).
    left. right; left. split; [exact HFP|]. exists (a0 - cf_head), (k0 + cf_head).
    split; [exact (pjs2_blocks_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST _ Hab)|]. lia.
  - pose proof (req_size_pos m ltac:(lia)) as [_ Rm].
    left. right; left. split; [exact HFP|]. exists b, m.
    split; [exact (pjs2_blocks_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST _ Hin1)|]. lia.
  - right. split; [exact HFP|]. exists cid, pos. split; [exact Hin2|].
    assert (Efa : frame_addr ly cid pos = frame_addr ly0 cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. lia. }
(* ---- after the run ---- *)
clear HF.
pose proof (pjs2_keep W E mem _ v Uv HFr) as KW. clear HFr.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. unfold aview. f_equal. unfold mbyte. rewrite (KW (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
prreg HS (18%bv : bv 5) R18.
assert (R10 : getr (ms_regs ms) 10 = sv_denot E PJS2_A0)
  by (rewrite (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS); reflexivity).
rewrite (pjs2_a0 E res E10' Hres64) in R10.
assert (KR : forall r, In r PJS_KEPT -> getr (ms_regs ms) r = getr r0 r).
{ intros r Hr. rewrite <- (HKEPT r Hr).
  exact (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs (pjs2_extra r0) PJS_KEPT HS HAE
    ltac:(vm_compute; reflexivity) r Hr). }
(* the str word res at v + 16 *)
assert (VSTR : val_mem SEGS (rdW W (ms_mem ms)) (v + 16) 8 res).
{ refine (pjs2_val E _ _ 8 16 8 (SOff 10 0) res v _ HS _ Uv _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (U_atom E 10 res E10' Hres64).
  - lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hres64. }
pose proof (pjs2_bytes_final W mem (ms_mem ms) v res HVB KV VSTR ltac:(lia) ltac:(lia)) as VB3.
assert (MG : mem_grows (rdW W mem) (rdW W (ms_mem ms))) by exact HG.
assert (HVW3 : forall a, v <= a < v + 56 -> writable_at SEGS (rdW W (ms_mem ms)) a)
  by (intros a Ha; exact (writable_at_grows SEGS _ _ a MG (HVW a Ha))).
(* ---- +0xa4: the ret, to the entry's ra ---- *)
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold pjs_FIN, fpostWm, fpostW.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (YK11.mkst ?rr _ ?mm _) ?dd = _ /\ _ =>
  exists ly, S, Hp, rr, mm, dd, k end.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_d js_v].
split.
{ unfold YK0s.ret_ok in Hret. rewrite R1, E32, Hret. reflexivity. }
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ|].
split.
{ intros a Ha _. rewrite KV by lia. exact (HWIN a Ha). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R2, Usp. replace (sp0 - 32 + 32) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned.
  - apply KR. unfold PJS_KEPT. cbn [In]. repeat (first [left; apply bv_eq; reflexivity | right]).
  - apply KR. unfold PJS_KEPT. cbn [In]. repeat (first [left; apply bv_eq; reflexivity | right]).
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8, E33. reflexivity.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9, E34. reflexivity.
  - assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by lia.
    destruct Hr' as [-> | Hr'].
    + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18, E35. reflexivity.
    + apply KR. unfold PJS_KEPT. cbn [In].
      destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
        repeat (first [left; apply bv_eq; reflexivity | right]). }
(* ---- the walk's post ---- *)
unfold fQmn. split; [|exact HPM].
unfold pjs_Q. cbn [js_ly js_S js_Hp js_W js_cs js_Lam js_v js_peak js_cnt js_fail js_ran js_most js_own js_sm js_x js_os js_i js_H0
  js_hist].
split; [exact HROOM|].
exists res.
split; [exact HRP0|].
split; [exact HRP1|].
split; [exact HDEAD|].
split.
{ apply (pjs2_post_keep B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem _ HPOST).
  - intros Hr0 a. subst res. apply (pjs2_full W mem _ v KW HVB VB3).
  - intros Hr0. destruct HRB as [Hr | (Hr1 & Hr2)]; [contradiction|].
    lia.
  - intros Hr0 a Ha. apply KV.
    + destruct Ha as [Ha | [(x & k1 & i & Hin & Hi & ->) | [Ha | Ha]]].
      * pose proof (pst_in_img_B a Ha) as Hi. pose proof (Hsegs a Hi). lia.
      * destruct HRB as [Hr | (Hr1 & Hr2)]; [contradiction|].
        destruct Hin as [E1 | Hin]; [injection E1 as <- <-; lia|].
        destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran x k1 most own HLED0 Hin) as (Hk1 & Hab & _).
        destruct (alx_blocks SEGS B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 _ _ HAR0 Hab) as (_ & H4 & Hc & _).
        assert (Rq1 : 1 <= req_size (k1 + cf_head) /\ k1 + cf_head <= req_size (k1 + cf_head))
          by (apply req_size_pos; lia). lia.
      * destruct HRB as [Hr | (Hr1 & Hr2)]; [contradiction|]. lia.
      * lia.
    + destruct (HRES Hr0) as (_ & HAPU & HAPH).
      destruct Ha as [Ha | [(x & k1 & i & Hin & Hi & ->) | [Ha | Ha]]].
      * intros Hx. exact (Hvpst a Ha ltac:(lia)).
      * destruct Hin as [E1 | Hin]; [injection E1 as <- <-; apply HAPH; lia|].
        exact (Hvhd x k1 i Hin Hi).
      * intros Hx. exact (HAPU a ltac:(lia) ltac:(lia)).
      * unfold amem_range in Hvamr. unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split.
- intros Hr0. split.
  + rewrite R10. replace (res =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr0). reflexivity.
  + destruct (HRES Hr0) as (HBY & HAPU & _).
    apply pjs_node_str.
    * apply pjs_hdr; [exact Hres64 | exact VB3 | split; [exact Hv8 | exact HVW3]].
    * split; [left; reflexivity|]. split; [lia|].
      split; [destruct HSCASE as [(_ & ->) | (_ & (_ & _ & _ & HL32 & _) & _)]; [cbn; lia | exact HL32]|].
      split.
      -- destruct HSCASE as [(_ & ->) | (_ & (Hcstr & _) & _)]; [constructor|].
         destruct Hcstr as (Hg & Hnz). apply Forall_forall. intros c Hc.
         destruct (In_nth _ _ 0 Hc) as (jj & Hjj & <-).
         destruct (Hg jj ltac:(rewrite length_app; cbn [length]; lia)) as [_ Hr].
         rewrite app_nth1 in Hr by exact Hjj.
         pose proof (proj1 (Forall_forall _ _) Hnz (nth jj cs 0) (nth_In _ _ Hjj)) as Hnz0. cbn beta in Hnz0. lia.
      -- unfold bytes_at in HBY. apply (garr8R_frame SEGS (rdW W mem) (rdW W (ms_mem ms)) res _ HBY).
         intros x Hx. apply (mbyte_of_aview SEGS). rewrite length_app in Hx. cbn [length] in Hx.
         apply KV; [destruct HRB as [Hr | (Hr1 & Hr2)]; [contradiction | lia]|].
         intros Hx'. exact (HAPU x ltac:(lia) ltac:(lia)).
    * intros x Hx. exact (HAPU x ltac:(lia)).
- intros Hr0. subst res. split.
  + rewrite R10. reflexivity.
  + rewrite pjs_bytes_0 in VB3. split; [split; [exact Hv8 | exact HVW3]|].
    split; [exact VB3|].
    apply pjs_fd0. apply pjs_hdr; [lia | rewrite pjs_bytes_0; exact VB3 | split; [exact Hv8 | exact HVW3]].
Qed.
End ep.
