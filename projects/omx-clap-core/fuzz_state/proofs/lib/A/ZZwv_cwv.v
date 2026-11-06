(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module names changed; 222 of its 422 lines of code are new or changed and 1492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cps.v; 309 of its 388 lines of code are new or changed and 343 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the two CALL SITES of the recursive callee
   write_value at the next level, each from a loop resume point to the next one.
   wvc_ind_item: the array arm's per-item indent returned (WVC_R_IND, wf_ty F = 5), segment ZZwv_runs2.wvc_seg_ind_arr,
     write_value of the i-th item, return WVC_R_ITEM.
   wvc_sep_item: the object arm's separator put returned (WVC_R_SEP, wf_ty F = 6), segment ZZwv_runs2.wvc_seg_sep,
     write_value of the i-th member's value, return WVC_R_ITEM.
   Both take the recursive spec one level down as a premise, `(k < 2)%nat -> write_value_spec_at B tfibsegs (S k)` with
   wf_m F = (2 - k)%nat, and the arm's depth premise `(depth (wf_t F) <= 2 - k)%nat`; the callee's stack is
   STK_write_value (2 - S k)%nat, inside write_value's own by ZZwv_call3.wvc_stk.
   Rule 24: no function proved here; these are call-site steps of write_value's container arms that use
   write_value_spec_at at the next level as a premise (write_value's lookup: lane record (internal path), CHECKER CONFIRM
   a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_call2
ZZwv_call3 ZZwv_res ZZwv_ret ZZwv_runs2 ZZwv_step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Ltac wvc_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
(* the arm instance: its fixed data and the entry state *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
(* the entry facts the arms' callers discharge once *)
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling.

(* ---- the frame chunk at offset 168 (xatom 17): write_value's saved ra, which the callee's chain clause reads in case
   1 (o = sp + 8) ---- *)
Lemma wvc_csL_ra : forall p, In (YP09.mkChunk 168 (CVal 8 (SOff (xatom 17) 0))) (wvc_csL p).
Proof.
intros p. unfold wvc_csL, wvc_cs0. apply in_or_app. right. right. cbn [seq map].
do 12 right. left. reflexivity.
Qed.

Lemma wvc_E_ra : forall regs ke key,
  sv_denot (wvc_E F regs0 regs ke key) (SOff (xatom 17) 0) = Z_to_bv 64 (raZ regs0).
Proof.
intros regs ke key.
assert (HR : 0 <= raZ regs0 < 2 ^ 64) by apply u64_range.
assert (H17 : ew (wvc_E F regs0 regs ke key) (xatom 17) = Z_to_bv 64 (raZ regs0)).
{ rewrite wvc_E_x. cbn [nth wvc_xs app map wvc_saved]. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
rewrite (wvc_den_val _ _ _ (wvc_u_off _ (xatom 17) (raZ regs0) 0 H17 HR ltac:(lia))).
rewrite Z.add_0_r. reflexivity.
Qed.

(* ---- the i-th item of the node (array item or object member's value): its node at kids + 56 * i, its blocks a slice
   of the parent's, plain, shallower ---- *)
Lemma wvc_item : forall (m : word -> option byte) i u,
  0 <= i ->
  PjStruct.pj_node tfibsegs m (fun a k => In (a, k) (wf_UL F)) (wf_v F) (wf_t F) (wf_D F) ->
  (exists num capn, PjStruct.pj_hdr tfibsegs m (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F)
     (wf_n F) capn) ->
  ((exists items, wf_t F = PjTree.JArr items /\ nth_error items (Z.to_nat i) = Some u) \/
   (exists members nm, wf_t F = PjTree.JObj members /\ nth_error members (Z.to_nat i) = Some (nm, u))) ->
  exists cap Du, In (wf_kids F, 56 * cap) (wf_D F) /\ wf_n F <= cap /\
    PjStruct.pj_node tfibsegs m (fun a k => In (a, k) (wf_UL F)) (wf_kids F + 56 * i) u Du /\
    (forall b, In b Du -> In b (wf_D F)) /\ jv_plain u /\
    (PjTree.depth u < PjTree.depth (wf_t F))%nat.
Proof.
intros m i u Hi0 HN (num1 & capn & HH) [(items & Ht & Hnth) | (members & nm & Ht & Hnth)].
- rewrite Ht in HN.
  destruct (wv_arr_item _ _ _ _ _ _ _ HN Hnth)
    as (num & kids & n & cap & Di & Dpre & Du & Dpost & HH2 & En & Hnc & _ & _ & ED & _ & HNu & HDu & _).
  assert (Ek : kids = wf_kids F).
  { destruct HH2 as (_ & _ & _ & _ & Hk2 & _). destruct HH as (_ & _ & _ & _ & Hk1 & _).
    exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk2 Hk1). }
  subst kids.
  assert (Enn : wf_n F = n).
  { destruct HE_ty as [(_ & items' & Ht' & En' & _) | (_ & members' & Ht' & _)];
      rewrite Ht in Ht'; [injection Ht' as Ei; subst items'; lia | discriminate]. }
  rewrite Z2Nat.id in HNu by exact Hi0.
  exists cap, Du. split; [rewrite ED; left; reflexivity|]. split; [lia|]. split; [exact HNu|].
  split; [exact HDu|]. split.
  + apply (wv_plain_item items (Z.to_nat i) u); [rewrite <- Ht; exact HE_plain | exact Hnth].
  + rewrite Ht. exact (wv_depth_item items (Z.to_nat i) u Hnth).
- rewrite Ht in HN.
  destruct (wv_obj_mem _ _ _ _ _ _ _ _ HN Hnth)
    as (num & kids & keys & n & cap & Di & Dpre & x & kk & Du & Dpost & HH2 & En & Hnc & _ & _ & _ & ED & _ & _ & _ &
        HNu & HDu & _).
  assert (Ek : kids = wf_kids F).
  { destruct HH2 as (_ & _ & _ & _ & Hk2 & _). destruct HH as (_ & _ & _ & _ & Hk1 & _).
    exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk2 Hk1). }
  subst kids.
  assert (Enn : wf_n F = n).
  { destruct HE_ty as [(_ & items' & Ht' & _) | (_ & members' & Ht' & En')];
      rewrite Ht in Ht'; [discriminate | injection Ht' as Ei; subst members'; lia]. }
  rewrite Z2Nat.id in HNu by exact Hi0.
  exists cap, Du. split; [rewrite ED; left; reflexivity|]. split; [lia|]. split; [exact HNu|].
  split; [exact HDu|]. split.
  + destruct (wv_plain_mem members (Z.to_nat i) nm u ltac:(rewrite <- Ht; exact HE_plain) Hnth) as (_ & Hp).
    exact Hp.
  + rewrite Ht. exact (wv_depth_mem members (Z.to_nat i) nm u Hnth).
Qed.

(* ================= the recursive call, from the call point the segment reached to the next resume point =========
   (shared by both sites: the item is the array's i-th item or the object's i-th member's value) *)
Lemma wvc_wv_call : forall r1 k i ke key Pd Rest u ly St U (W : world tfibsegs) ms mdc buf ms' mdc'
    (Q : world tfibsegs -> config -> Prop),
  ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) -> wf_m F = (2 - k)%nat ->
  (PjTree.depth (wf_t F) <= 2 - k)%nat ->
  wvc_WP F = Pd ++ WriterValue.wvpieces u (negb (wf_p F =? 0)) (wf_d F + 1) ++ Rest ->
  ((exists items, wf_t F = PjTree.JArr items /\ nth_error items (Z.to_nat i) = Some u) \/
   (exists members nm, wf_t F = PjTree.JObj members /\ nth_error members (Z.to_nat i) = Some (nm, u))) ->
  wvc_inv B F r1 i ke key Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly St U buf ->
  ms' = mkst (ms_regs ms') (w64 A_write_value) (ms_mem ms') (seg_rom tfibsegs) ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 [] ly St W
    (unpoison U (ms_mem ms')) mdc' (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly St U W (ms_mem ms') mdc' ->
  (forall x : word, ~ (wf_sp F - WVC_F <= bv_unsigned x < wf_sp F) ->
     mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 (ms_regs ms) ke key) (mrestrict (w_H W) (ms_mem ms'))
    (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_ITEM ->
  YK11.getr (ms_regs ms') 10%bv = ew (wvc_E F regs0 (ms_regs ms) ke key) 8 ->
  YK11.getr (ms_regs ms') 11%bv = w64 (wf_kids F + 56 * i) ->
  YK11.getr (ms_regs ms') 12%bv = ew (wvc_E F regs0 (ms_regs ms) ke key) 19 ->
  YK11.getr (ms_regs ms') 13%bv = w64 (wf_d F + 1) ->
  YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
  (forall q, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv ->
     YK11.getr (ms_regs ms') q = YK11.getr (ms_regs ms) q) ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F WVC_R_ITEM i ke key' (Pd ++ WriterValue.wvpieces u (negb (wf_p F =? 0)) (wf_d F + 1))
       ly0 S0 U0 W0 mem0 md0 regs0 W' (mkst regs' (Z_to_bv 64 WVC_R_ITEM) mem' (seg_rom tfibsegs)) md'
       ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_ITEM regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms' mdc') Q.
Proof.
intros r1 k i ke key Pd Rest u ly St U W ms mdc buf ms' mdc' Q HWV Hm Hdep HWP HSEL HINV Hms' HJ HARU HFR HCH
  R1 R10 R11 R12 R13 R2 RK K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
rewrite Hms'.
unfold wvc_inv in HINV. cbv zeta in HINV.
destruct HINV as (_ & HSEM0 & Q8 & Q9 & Q19 & Q21 & Q25 & Q3 & Q4 & Q18 & Q20 & Q22 & Q23 & Q24 & Q26 & Q27 &
  Qsp & Hi & Eke).
subst ke.
set (st := wvc_stP F Pd) in *.
set (Pc := WriterValue.wvpieces u (negb (wf_p F =? 0)) (wf_d F + 1)) in *.
set (regsC := ms_regs ms') in *. set (memC := ms_mem ms') in *.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _ & _ & _ & HSTKS).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly St U W (ms_mem ms) buf st HSEM0) as Hosp.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnev & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (Hlo : alloc_ceiling <= wf_sp F - WVC_F) by lia.
(* the writer facts at the call memory: the segment wrote write_value's own frame only *)
assert (HSEM : wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly St U W memC buf st).
{ apply (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly St U W (ms_mem ms) memC mdc' buf st HSEM0 HARU HFR Hlo); lia. }
pose proof HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN &
  HB0 & HRO & H8 & HC & HU0).
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _).
pose proof HBK as (HBK1 & HBK2 & _).
destruct HGL as (peak & Hpk & HG).
destruct (wvc_hdr_at B F ly0 S0 U0 W0 mem0 regs0 HE_hdr ly St U W memC buf st HSEM) as (num & capn & HHDR).
(* the item *)
destruct (wvc_item (mrestrict (w_H W) memC) i u (proj1 Hi) HN (ex_intro _ num (ex_intro _ capn HHDR)) HSEL)
  as (cap & Du & HinK & Hnc & HNu & HDu & Hpl & Hdu).
assert (Hk2 : (k < 2)%nat) by lia.
assert (Hdu2 : (PjTree.depth u <= 2 - S k)%nat) by lia.
pose proof (HWV Hk2) as HSPEC.
pose proof (wvc_stk (2 - S k)%nat) as (HSTKc0 & _).
assert (HSTKc : STK_write_value (2 - S k)%nat + WVC_F <= STK_write_value (wf_m F)).
{ apply HSTKS. rewrite Hm. lia. }
(* the call's registers *)
assert (RC : forall q z, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv ->
  YK11.getr (ms_regs ms) q = w64 z -> YK11.getr regsC q = w64 z).
{ intros q z Hq E. rewrite (RK q Hq). exact E. }
assert (Hsp : spZ regsC = wf_sp F - WVC_F) by (unfold spZ; rewrite R2; exact Qsp).
assert (G8 : YK11.getr regsC 8%bv = w64 (wf_o F)) by (apply RC; [wvc_in | exact Q8]).
assert (G9 : YK11.getr regsC 9%bv = w64 (wf_v F)) by (apply RC; [wvc_in | exact Q9]).
assert (G19 : YK11.getr regsC 19%bv = w64 (wf_p F)) by (apply RC; [wvc_in | exact Q19]).
assert (G21 : YK11.getr regsC 21%bv = w64 i) by (apply RC; [wvc_in | exact Q21]).
assert (G25 : YK11.getr regsC 25%bv = w64 (56 * i)) by (apply RC; [wvc_in | exact Q25]).
assert (G22 : YK11.getr regsC 22%bv = w64 (8 * i)) by (apply RC; [wvc_in | exact Q22]).
assert (G18 : YK11.getr regsC 18%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF)) by (apply RC; [wvc_in | exact Q18]).
assert (G20 : YK11.getr regsC 20%bv = w64 (wf_v F + 40)) by (apply RC; [wvc_in | exact Q20]).
assert (G23 : YK11.getr regsC 23%bv = w64 (wf_v F + 24)) by (apply RC; [wvc_in | exact Q23]).
assert (G24 : YK11.getr regsC 24%bv = w64 (wf_d F + 1)) by (apply RC; [wvc_in | exact Q24]).
assert (G26 : YK11.getr regsC 26%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF)) by (apply RC; [wvc_in | exact Q26]).
assert (G27 : YK11.getr regsC 27%bv = w64 (wf_v F / 8 + SHADOW_OFF)) by (apply RC; [wvc_in | exact Q27]).
assert (G3 : YK11.getr regsC 3%bv = YK11.getr regs0 3%bv) by (rewrite (RK 3%bv ltac:(wvc_in)); exact Q3).
assert (G4 : YK11.getr regsC 4%bv = YK11.getr regs0 4%bv) by (rewrite (RK 4%bv ltac:(wvc_in)); exact Q4).
assert (G10 : YK11.getr regsC 10%bv = w64 (wf_o F)).
{ rewrite R10, (wvc_E_r F regs0 (ms_regs ms) (wf_keys F + 8 * i) key 8%bv 8 eq_refl). exact Q8. }
assert (G12 : YK11.getr regsC 12%bv = w64 (wf_p F)).
{ rewrite R12, (wvc_E_r F regs0 (ms_regs ms) (wf_keys F + 8 * i) key 19%bv 19 eq_refl). exact Q19. }
assert (Hs0 : s0Z regsC = wf_o F).
{ unfold s0Z. rewrite G8. unfold w64. apply unsigned_lit_small. lia. }
assert (Hret : YK0s.ret_ok (YK11.getr regsC 1%bv)).
{ rewrite R1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. }
assert (Hra4 : 4096 <= raZ regsC).
{ unfold raZ. rewrite R1. unfold w64, WVC_R_ITEM. rewrite unsigned_lit_small by lia. lia. }
assert (Hgp : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite G3; exact HE_gp).
assert (Htp : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite G4; exact HE_tp).
(* case 1 of the chain clause: the word at sp - 8 is write_value's saved ra, the frame chunk at offset 168 *)
assert (HC1 : wf_o F = wf_sp F + 8 ->
  rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8) = Some (raZ regs0)).
{ intros _.
  rewrite (rdword_ext (aview tfibsegs (w_H W) memC) (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8)).
  2: { intros j Hj. apply aview_unpoison_out. apply (zwk_p_stack_not_ush B ly St U W memC mdc' _ HARU). lia. }
  apply AF0x.val_mem_rdword; [apply u64_range|].
  replace (wf_sp F - 8) with (wf_sp F - WVC_F + 168) by lia.
  refine (val_of_chunk_ok tfibsegs (wvc_E F regs0 (ms_regs ms) (wf_keys F + 8 * i) key) _ _ 168 8
    (SOff (xatom 17) 0) (raZ regs0) _ (wvc_E_ra (ms_regs ms) (wf_keys F + 8 * i) key) _ _).
  - exact (proj1 (Forall_forall _ _) HCH _ (wvc_csL_ra (wf_p F))).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
  - simpl. lia. }
(* the callee's fpreU, the chain clause at o and the window presence *)
assert (Hspot : wf_sp F <= wf_ot F) by lia.
assert (Hottop : wf_ot F <= ly_top ly) by (rewrite Etop; exact HE_top).
destruct (wvc_callpre B F ly0 S0 U0 W0 mem0 md0 regs0 ly St U W memC mdc' (wevk (wf_cap0 F) st) buf st regsC
  (STK_write_value (2 - S k)%nat) HJ HARU HSEM HC1 Hsp HE_sp16 HE_ot16 Hspot ltac:(lia) HSTKc Hret Hra4 Hgp Htp Hs0
  HE_oot Hottop HE_o8 Hlo) as (ch & _ & HPRE & HCHO & HPRES).
(* the frames bound, the room and the budget *)
assert (HFRL : Z.of_nat (length (frames St)) <= FRL_CRT_CALLEE) by (rewrite Hfrs; exact HE_frl).
assert (HROOM : Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat Pc)) + 1 <= WMAX).
{ pose proof (wv_room_mid (wvc_st0 F) Pd Pc) as R.
  assert (Et : WriterApp.w_text (wvc_st0 F) = wf_text0 F) by reflexivity. rewrite Et in R.
  pose proof HE_room as R0. rewrite HWP, app_assoc, wv_concat_app in R0.
  unfold st, wvc_stP. lia. }
assert (HB1 : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (Pd ++ Pc))).
{ pose proof HE_bud as HB. rewrite HWP, app_assoc in HB. unfold wvc_st0 in HB |- *.
  exact (wv_budget_pre_prefix S0 _ _ _ _ _ _ (Pd ++ Pc) Rest HE_cap0 HB). }
assert (HB2 : wbudget_pre St (WriterApp.w_cap st) (WriterApp.w_cnt st)
  (wf_live F + WriterApp.w_cap st - wf_cap0 F) (WriterApp.putN (wv_rst st) Pc)).
{ unfold wvc_st0 in HB1.
  pose proof (wv_budget_pre_mid S0 St (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
    Pd Pc HE_cap0 HB1 Hnev HBK2 HCNT) as H.
  replace (wf_live F + WriterApp.w_cap st - wf_cap0 F) with (wf_live F - wf_cap0 F + WriterApp.w_cap st) by lia.
  exact H. }
(* the item node: a pobj, apart from the buffer, its footprint off the window, its blocks the tree's *)
assert (Hic : i + 1 <= cap) by lia.
pose proof (HUL _ _ HinK) as HRB.
assert (HROOTk : WriterApp.w_cap st <> 0 ->
  wf_kids F + 56 * i + 56 <= buf - HEAD \/ buf + WriterApp.w_cap st <= wf_kids F + 56 * i).
{ intros Hz. pose proof HRB as (HinB & _ & _ & _). pose proof (HBIN Hz) as HinF.
  assert (Hne : (wf_kids F - HEAD, 56 * cap + HEAD) <> (buf - HEAD, WriterApp.w_cap st + HEAD)).
  { intros E. injection E as E1 _. apply (proj2 (HD _ _ HinK)). lia. }
  pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly St W (unpoison U memC) mdc' _ _ _ _
    (proj1 HARU) HinB HinF Hne) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
  pose proof (req_size_pos (56 * cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ1).
  pose proof (req_size_pos (WriterApp.w_cap st + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ2).
  unfold HEAD in *. lia. }
assert (HFOOTk : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_kids F + 56 * i) Du x).
{ intros x Hx Hf. apply (HE_foot x Hx).
  exact (wv_foot_sub (wf_v F) (wf_kids F + 56 * i) (wf_D F) Du HDu
    (wv_foot_kids (wf_v F) (wf_D F) (wf_kids F) cap i HinK ltac:(lia) ltac:(lia)) x Hf). }
assert (HNk : PjStruct.pj_node tfibsegs (mrestrict (w_H W) memC) (fun a kk => In (a, kk) (wf_D F))
  (wf_kids F + 56 * i) u Du).
{ apply (PjStruct.pj_node_frame tfibsegs u _ _ _ _ _ _ HNu).
  - intros a kk Hak. exact (HDu _ Hak).
  - intros x _. reflexivity. }
assert (HDuD : forall a kk, In (a, kk) Du -> In (a, kk) (wf_D F) /\ a <> buf).
{ intros a kk Hak. pose proof (HDu _ Hak) as H. split; [exact H | exact (proj2 (HD a kk H))]. }
pose proof (wv_kid_pobj B ly St U W memC mdc' (wf_kids F) cap i HARU HHD HRB (proj1 Hi) Hic) as HPOk.
(* the callee: write_value at the next level *)
change (SRr tfibsegs W (cfg_at tfibsegs A_write_value regsC memC mdc') Q).
refine (SRr_bind tfibsegs W _ _ Q
  (HSPEC ly St U W regsC memC mdc' ch (wf_ot F) (wf_o F) (wf_kids F + 56 * i) (wf_p F) (wf_d F + 1) u Du
     (wf_D F) buf (WriterApp.w_cap st) (WriterApp.w_failed st) (WriterApp.w_text st)
     (wf_live F + WriterApp.w_cap st - wf_cap0 F) peak (WriterApp.w_cnt st) (WriterApp.w_fail st)
     Hdu2 HPRE HHD HFRL G10 R11 G12 R13 HE_p ltac:(lia) ltac:(lia) ltac:(right; left; exact Hs0)
     HOUT HG HU0 ltac:(lia) HE_oot HE_ot16 Hottop HCHO HPRES HNk HPOk HUL HDuD HROOTk Hpl HFOOTk HROOM
     HBK1 ltac:(lia) HB2) _).
intros W' c' Hle (st' & buf' & U' & Est & HUS' & HPOST).
unfold wpost, fpostU in HPOST.
destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HOUT' & HBK' & HBS' & HWK' & _ & HGL').
subst c' st'.
(* the return: the loop invariant at WVC_R_ITEM *)
destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0 HE_p
  HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk WVC_R_ITEM i Pd Pc Rest ly St U W memC mdc' buf regsC (ms_regs ms)
  (wf_keys F + 8 * i) key (STK_write_value (2 - S k)%nat) peak ly' S' U' W' regs' mem' md' buf'
  HWP HJ HARU HSEM Hpk HCH Q9 Hsp G8 G9 G19 G21 G25 G22 G3 G4 G18 G20 G23 G24 G26 G27 Hi HJc OK' PO' HP
  ltac:(lia) HSTKc HUS' HOUT' HBK' HBS' HWK' HGL') as (key' & HINV').
rewrite R1. exact (K ly' S' U' W' regs' mem' md' buf' key' HINV').
Qed.

(* ================= the array arm: the per-item indent returned, call write_value of the i-th item ================= *)
Lemma wvc_ind_item : forall k i ke key Pd Rest items u ly St U (W : world tfibsegs) ms mdc buf
    (Q : world tfibsegs -> config -> Prop),
  ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) -> wf_m F = (2 - k)%nat ->
  wvc_WP F = Pd ++ WriterValue.wvpieces u (negb (wf_p F =? 0)) (wf_d F + 1) ++ Rest ->
  wvc_inv B F WVC_R_IND i ke key Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly St U buf ->
  (PjTree.depth (wf_t F) <= 2 - k)%nat ->
  wf_t F = PjTree.JArr items -> nth_error items (Z.to_nat i) = Some u ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F WVC_R_ITEM i ke key' (Pd ++ WriterValue.wvpieces u (negb (wf_p F =? 0)) (wf_d F + 1))
       ly0 S0 U0 W0 mem0 md0 regs0 W' (mkst regs' (Z_to_bv 64 WVC_R_ITEM) mem' (seg_rom tfibsegs)) md'
       ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_ITEM regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros k i ke key Pd Rest items u ly St U W ms mdc buf Q HWV Hm HWP HINV Hdep Ht Hnth K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof HE_kk as (Hk0 & Hkn & Hy0 & Hyn).
assert (Hty : wf_ty F = 5).
{ destruct HE_ty as [(E & _) | (_ & members & Ht' & _)]; [exact E | rewrite Ht in Ht'; discriminate]. }
pose proof HINV as HI. unfold wvc_inv in HI. cbv zeta in HI.
destruct HI as (HAT & HSEM & Q8 & Q9 & Q19 & Q21 & Q25 & Q3 & Q4 & Q18 & Q20 & Q22 & Q23 & Q24 & Q26 & Q27 &
  Qsp & Hi & Eke).
rewrite Hty in HAT.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly St U W (ms_mem ms) buf _ HSEM) as Hosp.
assert (Hd1 : wf_d F + 1 < 2 ^ 31).
{ pose proof HE_dd as Hdd. rewrite Ht in Hdd. cbn [PjTree.depth] in Hdd. lia. }
apply (wvc_seg_ind_arr B W ms mdc (wvc_E F regs0 (ms_regs ms) ke key) (wf_p F) i (wf_n F) (wf_d F) (wf_kids F)
  (wvc_STK F) (wf_ot F) (wf_sp F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 [] ly St U _ Q HAT).
- rewrite (wvc_E_r F regs0 (ms_regs ms) ke key 25%bv 25 eq_refl). exact Q25.
- rewrite wvc_E_x. reflexivity.
- rewrite wvc_E_x. reflexivity.
- exact Hi.
- lia.
- exact Hk0.
- exact Hkn.
- exact HE_d.
- exact Hd1.
- rewrite (wvc_E_r F regs0 (ms_regs ms) ke key 2%bv 2 eq_refl). exact Qsp.
- lia.
- unfold wvc_STK. lia.
- intros ms' mdc' Hms' HJ HARU HFR HCH R1 R10 R11 R12 R13 R2 RK.
  exact (wvc_wv_call WVC_R_IND k i ke key Pd Rest u ly St U W ms mdc buf ms' mdc' Q HWV Hm Hdep HWP
    (or_introl (ex_intro _ items (conj Ht Hnth))) HINV Hms' HJ HARU HFR HCH R1 R10 R11 R12 R13 R2 RK K).
Qed.

(* ================= the object arm: the separator's put returned, call write_value of the i-th member's value ===== *)
Lemma wvc_sep_item : forall k i ke key Pd Rest members nm u ly St U (W : world tfibsegs) ms mdc buf
    (Q : world tfibsegs -> config -> Prop),
  ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) -> wf_m F = (2 - k)%nat ->
  wvc_WP F = Pd ++ WriterValue.wvpieces u (negb (wf_p F =? 0)) (wf_d F + 1) ++ Rest ->
  wvc_inv B F WVC_R_SEP i ke key Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly St U buf ->
  (PjTree.depth (wf_t F) <= 2 - k)%nat ->
  wf_t F = PjTree.JObj members -> nth_error members (Z.to_nat i) = Some (nm, u) ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F WVC_R_ITEM i ke key' (Pd ++ WriterValue.wvpieces u (negb (wf_p F =? 0)) (wf_d F + 1))
       ly0 S0 U0 W0 mem0 md0 regs0 W' (mkst regs' (Z_to_bv 64 WVC_R_ITEM) mem' (seg_rom tfibsegs)) md'
       ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_ITEM regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros k i ke key Pd Rest members nm u ly St U W ms mdc buf Q HWV Hm HWP HINV Hdep Ht Hnth K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof HE_kk as (Hk0 & Hkn & Hy0 & Hyn).
assert (Hty : wf_ty F = 6).
{ destruct HE_ty as [(_ & items & Ht' & _) | (E & _)]; [rewrite Ht in Ht'; discriminate | exact E]. }
pose proof HINV as HI. unfold wvc_inv in HI. cbv zeta in HI.
destruct HI as (HAT & HSEM & Q8 & Q9 & Q19 & Q21 & Q25 & Q3 & Q4 & Q18 & Q20 & Q22 & Q23 & Q24 & Q26 & Q27 &
  Qsp & Hi & Eke).
rewrite Hty in HAT.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly St U W (ms_mem ms) buf _ HSEM) as Hosp.
assert (Hd1 : wf_d F + 1 < 2 ^ 31).
{ pose proof HE_dd as Hdd. rewrite Ht in Hdd. cbn [PjTree.depth] in Hdd. lia. }
apply (wvc_seg_sep B W ms mdc (wvc_E F regs0 (ms_regs ms) ke key) (wf_p F) i (wf_n F) (wf_d F) (wf_kids F)
  (wvc_STK F) (wf_ot F) (wf_sp F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 [] ly St U _ Q HAT).
- rewrite (wvc_E_r F regs0 (ms_regs ms) ke key 25%bv 25 eq_refl). exact Q25.
- rewrite wvc_E_x. reflexivity.
- rewrite wvc_E_x. reflexivity.
- exact Hi.
- lia.
- exact Hk0.
- exact Hkn.
- exact HE_d.
- exact Hd1.
- rewrite (wvc_E_r F regs0 (ms_regs ms) ke key 2%bv 2 eq_refl). exact Qsp.
- lia.
- unfold wvc_STK. lia.
- intros ms' mdc' Hms' HJ HARU HFR HCH R1 R10 R11 R12 R13 R2 RK.
  exact (wvc_wv_call WVC_R_SEP k i ke key Pd Rest u ly St U W ms mdc buf ms' mdc' Q HWV Hm Hdep HWP
    (or_intror (ex_intro _ members (ex_intro _ nm (conj Ht Hnth)))) HINV Hms' HJ HARU HFR HCH
    R1 R10 R11 R12 R13 R2 RK K).
Qed.

End A.

