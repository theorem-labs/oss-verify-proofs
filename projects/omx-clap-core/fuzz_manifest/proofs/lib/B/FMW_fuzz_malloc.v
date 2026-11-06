(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_fuzz_malloc.v (a working branch 7a6aa01e779), relocated by
   b_reloc.py (mal; revcheck report (internal path)), the call boundary moved by
   hand. B splits A's fuzz_malloc 0x8193c in two: fuzz_malloc 0x81b88 (frame 16: failing(), the size check, malloc (n + 16)
   at 0x81bcc, NULL -> 0) restores its frame and TAIL-CALLS the outlined own 0x81bfc (`j` at 0x81be4; own's frame is its
   own 32 bytes at the same entry sp: the shadow base from the .got, the inline checks of b and b + 7, the eight byte
   stores, poison (b, 16) at 0x81c88, then segment C, lib/B/FMW_fuzz_malloc_C.v, with own's UBSan trap 0x81cf0). One code
   table covers both (FMW_fuzz_malloc_lem.v tbl_fmm, 91 words).
   fuzz_malloc 0x81b88 (alloc.c:61-66; failing() :33-39 inlined, own() :41-49 outlined): the ASan walk. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0s YG0d YG0p YG0q YCbq YC5d YCbp YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0m YF0x YE2y YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCeg.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMpoisonS.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_fuzz_alloc_base FMW_fuzz_malloc_lem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_fuzz_malloc_Cpost FMW_fuzz_malloc_C.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* the head's eight one-byte chunks (n >> 8k) read back as the 8-byte value n *)
Lemma head_byte_ok : forall E (m : word -> option byte) base k e v,
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk k (CVal 1 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  mbyte tfibsegs m (base + k) = Some (Z_to_bv 8 v).
Proof.
intros E m base k e v Hc He Hv. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. rewrite Z.add_0_r in Hm. rewrite Hm. f_equal.
injection Hb as <-. unfold YP09.byte_of_word. rewrite He, Z.mul_0_r, Z.shiftr_0_r, unsigned_lit_small by lia. reflexivity.
Qed.

Lemma val_mem8_of_bytes : forall (m : word -> option byte) a v, 0 <= v < 2 ^ 64 ->
  (forall k, 0 <= k < 8 -> mbyte tfibsegs m (a + k) = Some (Z_to_bv 8 (Z.shiftr v (8 * k)))) ->
  val_mem tfibsegs m a 8 v.
Proof.
intros m a v Hv H k Hk. rewrite (H (Z.of_nat k)) by lia. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, YO0f.le_byte.
change (bv_modulus 8) with 256. change (8 * Z.of_nat 8) with 64.
rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite Zmod_mod. reflexivity.
Qed.

Lemma shiftr_range : forall n s, 0 <= n < 2 ^ 64 -> 0 <= s -> 0 <= Z.shiftr n s < 2 ^ 64.
Proof.
intros n s Hn Hs. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs) as Hp.
split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ n); [apply Z.div_le_upper_bound; nia | lia].
Qed.

Lemma denot_srl_atom : forall E k n s, ew E k = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 -> 0 <= s < 64 ->
  sv_denot E (SAlu Instr.ALU_SRL (SOff k 0) (SLit s)) = Z_to_bv 64 (Z.shiftr n s).
Proof.
intros E k n s Hk Hn Hs. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite zalu64_sound. f_equal. unfold zalu64, zalu_raw, zcanon, M64.
rewrite (Z.mod_small n), (Z.mod_small s) by lia.
replace (Z.land s 63) with s.
2:{ replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia. rewrite Z.mod_small; [reflexivity|].
    change (2 ^ 6) with 64. lia. }
apply Z.mod_small. apply shiftr_range; lia.
Qed.

Lemma region_ok_of_st_ok : forall {fx : YK11.FPState} E ss (H : word -> bool) ms i r,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok tfibsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros fx E ss H ms i r HS Hi. destruct (st_ok_mem_ok E ss H ms HS) as (_ & Hok & _).
exact (proj1 (Forall_forall _ _) Hok r (nth_error_In _ _ Hi)).
Qed.

(* the write windows of a concrete region list, case by case (the goal is then closed by the caller) *)
Ltac win_cases norm :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hw := fresh "Hw" in
  intros a (r & Hin & Hw);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; norm Hw|]);
  try destruct Hin.

(* a chunk of a concrete chunk list, found by value *)
Ltac chunk_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis TL : TfibLib B.
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B ameter_triv.
Hypothesis APOISON : apoison16_realizes tfibsegs B PC_poison.
#[local] Notation LAWS := (AR_laws_ok tfibsegs B).

(* entry atoms past the registers: 32 g_count, 33 g_fail_at, 34 the shadow base *)
Definition fmm_extra (cnt fail : Z) : list word := [w64 cnt; w64 fail; Z_to_bv 64 SB].
(* fuzz_malloc's own 16-byte frame below the entry sp; the .got slot of the shadow base and its cell, which own reads
   after the malloc call, are in the entry state already (read only, kept across the call) *)
Definition ss_fmm : sstate :=
  mkSS A_fuzz_malloc sr_atoms [stack_region 16; got_region; bcell_region 34; fm_wcell G_COUNT 32; fm_wcell G_FAIL 33]
    None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 28) 0); (34%nat, mkAF SB SB 0)] [] []).
(* own's frame below fuzz_malloc's: [sp0 - 32, sp0 - 16), added after the malloc call (malloc's stack is below sp0 - 16) *)
Definition own_lo_region : YP09.region := YP09.mkRegion (Some 2%nat) (-32) (-16) (-32) (-16) [].
(* the shadow band the inline checks' shadow loads may touch (donor YC4b.v Bspan) *)
Definition fmm_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Theorem fuzz_malloc_holds : forall CTX, fuzz_malloc_spec tfibsegs B CTX.
Proof.
intros CTX ly S W regs mem md ch n live peak cnt fail HPRE _ G10 Hn1 HnM HGL Hlive Hcnt Hev Hbb.
pose proof HPRE as (HAN & HRO).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof HGL as (GL & GP & GC & GF & Hlp & Hp64 & Hc64 & Hf64).
pose proof fma_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : STK_fuzz_malloc = 16416) by reflexivity.
unfold HEAD, MALLOC_MAX in HnM.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (tl_got_shadow B TL), (tl_shadow_cell B TL) in Kgot. rewrite (tl_shadow_cell B TL) in Kcell.
set (E := Ereg regs (fmm_extra cnt fail)).
assert (E1 : ew E 1 = getr regs 1) by exact (ew_Ereg_nat regs (fmm_extra cnt fail) 1 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (ew_Ereg_nat regs (fmm_extra cnt fail) 2 2%bv eq_refl).
assert (E10 : ew E 10 = w64 n) by exact (eq_trans (ew_Ereg_nat regs (fmm_extra cnt fail) 10 10%bv eq_refl) G10).
assert (E32 : ew E 32 = w64 cnt) by exact (ew_Ereg_extra regs (fmm_extra cnt fail) 0).
assert (E33 : ew E 33 = w64 fail) by exact (ew_Ereg_extra regs (fmm_extra cnt fail) 1).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by exact (ew_Ereg_extra regs (fmm_extra cnt fail) 2).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HS : st_ok tfibsegs E ss_fmm
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_fuzz_malloc) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok; fold E.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    + apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (-16)); [exact Usp | lia | lia |].
      intros a Ha. apply apresent_writable. apply Hpres. lia.
    + unfold region_ok, got_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val tfibsegs E _ 0 0x99c98 8 (SLit A_shadow_glob) A_shadow_glob);
        [reflexivity | unfold A_shadow_glob; lia | cbn; lia | rewrite Z.add_0_l; exact (val_mem_of_rdword _ _ _ _ Kgot)].
    + unfold region_ok, bcell_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val tfibsegs E _ 0 0xa2078 8 (SOff 34 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E34; reflexivity | unfold SHADOW_OFF; lia | cbn; lia | rewrite Z.add_0_l; exact (val_mem_of_rdword _ _ _ _ Kcell)].
    + apply (region_ok_fm_wcell _ _ G_COUNT 32 cnt); [exact GC | exact E32 | lia | unfold G_COUNT; lia | unfold G_COUNT; lia].
    + apply (region_ok_fm_wcell _ _ G_FAIL 33 fail); [exact GF | exact E33 | lia | unfold G_FAIL; lia | unfold G_FAIL; lia].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, stack_region, got_region, bcell_region, fm_wcell, G_COUNT, G_FAIL, A_GOT_shadow, A_shadow_glob.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp. repeat split; try exact I; lia.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp, E10, E34. unfold YG0d.w64.
    rewrite !unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat split; lia. }
unfold cfg_at. change (w64 A_fuzz_malloc) with (Z_to_bv 64 A_fuzz_malloc).
assert (E3 : ew E 3 = getr regs 3) by exact (ew_Ereg_nat regs (fmm_extra cnt fail) 3 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (ew_Ereg_nat regs (fmm_extra cnt fail) 4 4%bv eq_refl).
assert (E8 : ew E 8 = getr regs 8) by exact (ew_Ereg_nat regs (fmm_extra cnt fail) 8 8%bv eq_refl).
assert (E9 : ew E 9 = getr regs 9) by exact (ew_Ereg_nat regs (fmm_extra cnt fail) 9 9%bv eq_refl).
assert (HEE : E = Ereg regs (fmm_extra cnt fail)) by reflexivity.
clearbody E.
unfold YK0s.ret_ok in Hra.
pose proof (ajournal_init tfibsegs B STK_fuzz_malloc FM_PSTAT_FP ly S W regs mem md ch HAN) as J0.
(* entry .. 0x81bb0: prologue, failing()'s loads, g_count + 1 *)
srr_runG_with tbl_fmm_ok HS.
rename ms into ms1, HF into HF1, HFr into HFr1, HG into HG1, HH into HH1.
assert (WIN1 : forall a, in_wrange E (ss_mem ss_fmm) a -> fmm_winA (spZ regs) a) by win_solve Usp.
srr_branch_with tbl_fmm_ok HS.
- (* g_count <> g_fail_at: the size check (n <= 2^28, decided by the run) and malloc (n + 16) *)
  rewrite branch_ne_U, (U_atom E 32 cnt E32 ltac:(lia)), (U_atom E 33 fail E33 ltac:(lia)) in Hc.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  lazymatch goal with HS0 : st_ok _ _ ?ss _ |- _ =>
    assert (WIN2 : forall a, in_wrange E (ss_mem ss) a -> fmm_winA (spZ regs) a) by win_solve Usp end.
  srr_runG_with tbl_fmm_ok HS.
  rename ms into ms2, HF into HF2, HFr into HFr2, HG into HG2, HH into HH2.
  assert (RAW2 : forall x : word, ~ fmm_winA (spZ regs) (bv_unsigned x) -> ms_mem ms2 x = mem x).
  { intros x Hx. rewrite (HF2 x (fun H => Hx (WIN2 _ H))), (HF1 x (fun H => Hx (WIN1 _ H))). reflexivity. }
  assert (J1 : ajournal tfibsegs B STK_fuzz_malloc (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W (ms_mem ms2)
    (with_vm_backing (m_vm_lazy md) mat0 md) 0).
  { eapply (ajournal_stk_pstat B HB); [exact J0 | intros a Ha; exact Ha | | | | apply same_but_materialized_wvb_any].
    - intros x Hs Hp. unfold mrestrict. rewrite RAW2; [reflexivity|].
      intros [Hw|Hw]; [apply Hs; lia | apply Hp, fmm_cell_inFP; unfold fmm_cell; tauto].
    - intros x Hx. apply HG2, HG1, Hx.
    - intros x Hx. rewrite HH2, HH1 by exact Hx. reflexivity. }
  assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ fmm_winA (spZ regs) a ->
    aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) mem a).
  { intros a Ha Hw. apply aview_eq_of. unfold mrestrict. rewrite RAW2; [reflexivity|].
    rewrite unsigned_lit_small by lia. exact Hw. }
  assert (VL2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) G_LIVE 8 live).
  { eapply val_mem_kept; [exact GL | intros i Hi; apply AV2; unfold fmm_winA, G_FAIL, G_LIVE, G_PEAK, G_COUNT; cbn in Hi; lia]. }
  assert (VP2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) G_PEAK 8 peak).
  { eapply val_mem_kept; [exact GP | intros i Hi; apply AV2; unfold fmm_winA, G_FAIL, G_LIVE, G_PEAK, G_COUNT; cbn in Hi; lia]. }
  assert (VC2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) G_COUNT 8 (cnt + 1)).
  { eapply (val_mem_of_chunk8 E _ (ss_mem _) 3%nat G_COUNT (SOff 32 1) (cnt + 1));
      [exact (st_ok_mem_ok E _ (w_H W) ms2 HS) | vm_compute; reflexivity | | lia].
    cbn [sv_denot]. rewrite E32. unfold YG0d.w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (VF2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) G_FAIL 8 fail).
  { eapply (val_mem_of_chunk8 E _ (ss_mem _) 4%nat G_FAIL (SOff 33 0) fail);
      [exact (st_ok_mem_ok E _ (w_H W) ms2 HS) | vm_compute; reflexivity | | lia].
    cbn [sv_denot]. rewrite E33. unfold YG0d.w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms2 HS eq_refl). cbn [ss_pc].
  replace 339484 with (pc_wrap_malloc (as_code B)) by (rewrite (tl_code B TL); reflexivity).
  rreg HS (10%bv : bv 5) R10. rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2.
  rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (8%bv : bv 5) R8.
  assert (Usp2 : spZ (ms_regs ms2) = spZ regs - 16).
  { unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by lia. lia. }
  (* the malloc call at 0x81bcc, from fuzz_malloc's frame (sp = sp0 - 16) *)
  eapply SRr_bind.
  { eapply (AMALLOC4 W (ms_regs ms2) (ms_mem ms2) STK_fuzz_malloc (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S _ 0
      (n + 16) (-16) (Z_to_bv 64 0x81bd0) [] J1).
    - rewrite R10, E10. unfold YG0d.w64. rewrite unsigned_lit_small by lia. reflexivity.
    - unfold MALLOC_MAX. lia.
    - unfold HEAD in Hbb. lia.
    - rewrite Usp2. lia.
    - reflexivity.
    - lia.
    - unfold ASTACK. lia.
    - rewrite R3, E3. exact Hgp.
    - rewrite R4, E4. exact Htp.
    - exact R1.
    - apply ret_ok_even. vm_compute. reflexivity.
    - lia.
    - apply (achain_chain_pre ly _ (spZ (ms_regs ms2)) n [] (ms_regs ms2)); [apply achain_low; lia | lia | |].
      + unfold s0Z. rewrite R8, E10. unfold YG0d.w64. apply unsigned_lit_small. lia.
      + unfold raZ. rewrite R1. rewrite unsigned_lit_small by lia. lia.
    - rewrite call_trace_nil. unfold raZ. rewrite R1, unsigned_lit_small by lia. rewrite (tl_code B TL), (tl_universe B TL).
      apply memZL_In. vm_compute. reflexivity.
    - exact I. }
  intros W2 c2 Hwle2 (ly2 & S2 & regs3 & mem3 & md3 & res & -> & J2 & HP3 & Ha03 & Hfrs3 & Hres & Eab & HK & _).
  pose proof (proj1 J1) as HAR2. pose proof (proj1 J2) as HAR3.
  assert (Hin3 : In (res, n + 16) (ablocks B ly2 S2)) by (rewrite Eab; apply in_app_iff; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 res (n + 16) HAR3 Hin3) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _).
  assert (Hrq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
  rewrite Hrq in Hrceil, Hrapp, Hrpres.
  assert (HRES : 0 <= res < 2 ^ 64) by lia.
  destruct (al_const _ _ LAWS ly S W (ms_mem ms2) _ HAR2) as (Kcell2 & _ & Kgot2 & _).
  destruct (al_const _ _ LAWS ly2 S2 W2 mem3 md3 HAR3) as (Kcell3 & _ & Kgot3 & _).
  rewrite (tl_got_shadow B TL), (tl_shadow_cell B TL) in Kgot2, Kgot3. rewrite (tl_shadow_cell B TL) in Kcell2, Kcell3.
  unfold A_GOT_shadow, A_shadow_glob in Kgot2, Kgot3, Kcell2, Kcell3.
  pose proof J2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  assert (HP3' : YO0d.regs_preserved (ms_regs (restrict (w_H W) ms2)) regs3) by exact HP3.
  (* kept across the call: fuzz_malloc's frame [sp0 - 16, sp0) (above malloc's sp), the shadow-base slot and cell *)
  jafter_call_keep HS 35%nat regs3 (mrestrict (w_H W2) mem3) HP3' [0; 1; 2]%nat HS3.
  match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    - eapply (region_kept_stack_aj tfibsegs B); [exact HK | exact J2 | exact Usp | lia | lia | lia | lia | lia].
    - apply (region_kept_val tfibsegs E _ _ 0x99c98 8 0xa2078);
        [exact (val_mem_of_rdword _ _ _ _ Kgot2) | exact (val_mem_of_rdword _ _ _ _ Kgot3) | lia].
    - apply (region_kept_val tfibsegs E _ _ 0xa2078 8 SHADOW_OFF);
        [exact (val_mem_of_rdword _ _ _ _ Kcell2) | exact (val_mem_of_rdword _ _ _ _ Kcell3) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS3.
  set (Ec := havoc E 35 (map (getr regs3) CLOB)) in HS3.
  assert (Eco : forall k, (k < 35)%nat -> ew Ec k = ew E k) by (intros k Hk; apply ew_havoc_old; exact Hk).
  assert (Ec39 : ew Ec 39 = w64 res)
    by exact (eq_trans (ew_havoc_new E 35 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia)) Ha03).
  pose proof (st_ok_add_fact tfibsegs Ec _ _ 39 (mkAF 4096 140737479966720 4) HS3) as HS.
  match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK HS3] end.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ec39. unfold YG0d.w64. rewrite unsigned_lit_small by lia.
    change (2 ^ 4) with 16. lia. }
  (* own's frame below fuzz_malloc's, [sp0 - 32, sp0 - 16): present stack (the journal keeps it), malloc's frame before *)
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_add_region Ex ssx msx own_lo_region HS ltac:(vm_compute; reflexivity)) as HSo end.
  match type of HSo with ?t -> _ => assert (HRK : t); [|specialize (HSo HRK); clear HRK] end.
  { unfold region_ok, own_lo_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
    rewrite Eco by lia. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply apresent_writable. apply Hpres3. lia. }
  match type of HSo with ?t -> _ => assert (HRK : t); [|specialize (HSo HRK); clear HRK HS] end.
  { cbn [all_disjoint ss_mem add_atom]. unfold extent_disjoint, own_lo_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Eco by lia. rewrite Usp. unfold A_GOT_shadow, A_shadow_glob. repeat split; lia. }
  rename HSo into HS.
  assert (SHOK : sh_ok tfibsegs (SOff 34 0) [mkSHE 39 0 16] Ec (mrestrict (w_H W2) mem3)).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_block tfibsegs B LAWS ly2 S2 W2 mem3 md3 Ec (SOff 34 0) 39 res (n + 16) 0 16 HAR3 Hin3).
    - rewrite (U_atom Ec 34 SB (eq_trans (Eco 34%nat ltac:(lia)) E34) ltac:(unfold SB; lia)). reflexivity.
    - apply U_atom; [exact Ec39 | lia].
    - lia.
    - rewrite Hrq. lia. }
  pose proof LAWS as HLAWS. pose proof fma_segs_low as HSLOW.
  (* 0x81bd0 .. 0x81c44: NULL check (decided by the fact), fuzz_malloc's epilogue, `j own`, own's prologue, the shadow
     base from the .got, the inline checks of b and b + 7 (the token run) *)
  aj_run_to_tok tbl_fmm_ok HS J2 SHOK fmm_Bspan 0x81c44.
  { awr_ok_tac. all: rewrite Eco by lia; exact Usp. }
  rename ms into ms3, HF into HF3, HFr into HFr3, HG into HG3, J2 into J3.
  (* 0x81c44 .. the poisoning call: the eight byte stores of n into the head b[0..8) *)
  pose proof (blk_off_img B ly2 S2 W2 mem3 md3 res (n + 16) HAR3 Hin3) as Hrimg. rewrite Hrq in Hrimg. hnf in Hrimg.
  assert (Hnew : ~ In (res, n + 16) (ablocks B ly S)).
  { intros Hc0. pose proof (aftok_new_block tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (n + 16) J1 HAR3 Eab
      ltac:(lia) Hc0 0 ltac:(cbn [snd]; rewrite Hrq; lia)) as Hf0. cbn [fst] in Hf0. rewrite Z.add_0_r in Hf0.
    pose proof (fmm_pstat_range res Hf0). lia. }
  pose proof (proj1 J3) as HAR4.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms3) _ res (n + 16) HAR4 Hin3) as (_ & _ & _ & _ & Hrpres4 & _).
  rewrite Hrq in Hrpres4.
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_add_region Ex ssx msx (YP09.mkRegion (Some 39%nat) 0 8 0 8 []) HS ltac:(vm_compute; reflexivity)) as HS4 end.
  match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite Ec39. unfold YG0d.w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply apresent_writable. apply Hrpres4. lia. }
  match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK HS] end.
  { cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Ec39, Eco by lia. unfold YG0d.w64. rewrite unsigned_lit_small by lia. rewrite Usp.
    repeat split; lia. }
  aj_run tbl_fmm_ok HS4 J3.
  { eapply awr_ok_cons_tmp; [reflexivity | | exact Hin3 | exact Hnew | cbn; lia | cbn; rewrite Hrq; lia |].
    { rewrite Ec39. unfold YG0d.w64. apply unsigned_lit_small. lia. }
    awr_ok_tac. all: rewrite Eco by lia; exact Usp. }
  rename ms into ms4, HF into HF4, HFr into HFr4, HG into HG4, J3 into J4.
  assert (Ec10 : ew Ec 10 = w64 n) by (rewrite Eco by lia; exact E10).
  assert (Usp' : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite Eco by lia; exact Usp).
  assert (Ures : bv_unsigned (ew Ec 39) = res) by (rewrite Ec39; unfold YG0d.w64; apply unsigned_lit_small; lia).
  lazymatch goal with H3 : frame_of _ ?rs mem3 (ms_mem ms3) |- _ =>
    assert (WIN3 : forall a, in_wrange Ec rs a -> spZ regs - 32 <= a < spZ regs)
      by (win_cases ltac:(fun Hw => try rewrite Usp' in Hw; try rewrite Ures in Hw); lia) end.
  lazymatch goal with H4 : frame_of _ ?rs (ms_mem ms3) (ms_mem ms4) |- _ =>
    assert (WIN4 : forall a, in_wrange Ec rs a -> (spZ regs - 32 <= a < spZ regs) \/ (res <= a < res + 8))
      by (win_cases ltac:(fun Hw => try rewrite Usp' in Hw; try rewrite Ures in Hw); lia) end.
  (* the head holds n *)
  assert (VH : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms4)) res 8 n).
  { lazymatch type of HS4 with st_ok _ _ ?ss _ =>
      let r := eval vm_compute in (nth 0 (ss_mem ss) got_region) in
      pose proof (region_ok_of_st_ok Ec ss (w_H W2) ms4 0 r HS4 ltac:(vm_compute; reflexivity)) as HRh end.
    unfold region_ok in HRh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRh.
    destruct HRh as (_ & _ & _ & HC). rewrite Ures in HC.
    apply Forall_cons_iff in HC as [Q3 HC]. apply Forall_cons_iff in HC as [Q2 HC].
    apply Forall_cons_iff in HC as [Q1 HC]. apply Forall_cons_iff in HC as [Q0 HC].
    apply Forall_cons_iff in HC as [Q7 HC]. apply Forall_cons_iff in HC as [Q6 HC].
    apply Forall_cons_iff in HC as [Q5 HC]. apply Forall_cons_iff in HC as [Q4 _].
    apply val_mem8_of_bytes; [lia|]. intros k Hk.
    assert (Hk8 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
    destruct Hk8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]].
    - change (8 * 0) with 0. rewrite Z.shiftr_0_r. apply (head_byte_ok _ _ _ 0 _ _ Q0); [|lia].
      cbn [sv_denot]. rewrite Ec10. unfold YG0d.w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    - apply (head_byte_ok _ _ _ 1 _ _ Q1); [apply denot_srl_atom; [exact Ec10 | lia | lia] | apply shiftr_range; lia].
    - apply (head_byte_ok _ _ _ 2 _ _ Q2); [apply denot_srl_atom; [exact Ec10 | lia | lia] | apply shiftr_range; lia].
    - apply (head_byte_ok _ _ _ 3 _ _ Q3); [apply denot_srl_atom; [exact Ec10 | lia | lia] | apply shiftr_range; lia].
    - apply (head_byte_ok _ _ _ 4 _ _ Q4); [apply denot_srl_atom; [exact Ec10 | lia | lia] | apply shiftr_range; lia].
    - apply (head_byte_ok _ _ _ 5 _ _ Q5); [apply denot_srl_atom; [exact Ec10 | lia | lia] | apply shiftr_range; lia].
    - apply (head_byte_ok _ _ _ 6 _ _ Q6); [apply denot_srl_atom; [exact Ec10 | lia | lia] | apply shiftr_range; lia].
    - apply (head_byte_ok _ _ _ 7 _ _ Q7); [apply denot_srl_atom; [exact Ec10 | lia | lia] | apply shiftr_range; lia]. }
  (* own's frame holds the entry ra, s0 (at sp0 - 8, -16: fuzz_malloc's frame, reloaded and stored again) and s1
     (sp0 - 24, own_lo_region) *)
  lazymatch type of HS4 with st_ok _ _ ?ss _ =>
    let r := eval vm_compute in (nth 1 (ss_mem ss) got_region) in
    pose proof (region_ok_of_st_ok Ec ss (w_H W2) ms4 1 r HS4 ltac:(vm_compute; reflexivity)) as HRlo;
    let r2 := eval vm_compute in (nth 2 (ss_mem ss) got_region) in
    pose proof (region_ok_of_st_ok Ec ss (w_H W2) ms4 2 r2 HS4 ltac:(vm_compute; reflexivity)) as HRhi end.
  unfold region_ok in HRlo, HRhi.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRlo, HRhi.
  destruct HRlo as (_ & _ & _ & HClo). destruct HRhi as (_ & _ & _ & HChi). rewrite Usp' in HClo, HChi.
  pose proof (proj1 (Forall_forall _ _) HClo (YP09.mkChunk (-24) (CVal 8 (SOff 9 0))) ltac:(chunk_in)) as F24.
  pose proof (proj1 (Forall_forall _ _) HChi (YP09.mkChunk (-16) (CVal 8 (SOff 8 0))) ltac:(chunk_in)) as F16.
  pose proof (proj1 (Forall_forall _ _) HChi (YP09.mkChunk (-8) (CVal 8 (SOff 1 0))) ltac:(chunk_in)) as F8.
  assert (Hw64 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8)).
  { intros w. pose proof (bv_unsigned_in_range 64 w) as Hq. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq. exact Hq. }
  assert (VF8 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms4)) (spZ regs + -8) 8 (raZ regs)).
  { apply (val_of_chunk_ok tfibsegs Ec _ (spZ regs) (-8) 8 (SOff 1 0) (raZ regs) F8); [| apply Hw64 | cbn; lia].
    cbn [sv_denot]. rewrite Eco, E1 by lia. rewrite Z.add_0_r. reflexivity. }
  assert (VF16 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms4)) (spZ regs + -16) 8 (s0Z regs)).
  { apply (val_of_chunk_ok tfibsegs Ec _ (spZ regs) (-16) 8 (SOff 8 0) (s0Z regs) F16); [| apply Hw64 | cbn; lia].
    cbn [sv_denot]. rewrite Eco, E8 by lia. rewrite Z.add_0_r. reflexivity. }
  assert (VF24 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms4)) (spZ regs + -24) 8 (bv_unsigned (getr regs 9))).
  { apply (val_of_chunk_ok tfibsegs Ec _ (spZ regs) (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) F24); [| apply Hw64 | cbn; lia].
    cbn [sv_denot]. rewrite Eco, E9 by lia. rewrite Z.add_0_r. reflexivity. }
  (* the poisoning call __asan_poison_memory_region (b, 16) at 0x81c88, from own's frame (sp = sp0 - 32) *)
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) Ec _ ms4 HS4 eq_refl). cbn [ss_pc].
  rreg HS4 (10%bv : bv 5) P10. rreg HS4 (11%bv : bv 5) P11. rreg HS4 (1%bv : bv 5) P1.
  rreg HS4 (2%bv : bv 5) P2. rreg HS4 (3%bv : bv 5) P3. rreg HS4 (4%bv : bv 5) P4.
  rreg HS4 (8%bv : bv 5) P8. rreg HS4 (9%bv : bv 5) P9.
  assert (Usp4 : spZ (ms_regs ms4) = spZ regs + -32).
  { unfold spZ at 1. rewrite P2, Usp'. rewrite unsigned_lit_small by lia. reflexivity. }
  eapply SRr_bind.
  { change 344820 with PC_poison.
    eapply (APOISON ly2 S2 [] W2 (ms_regs ms4) (ms_mem ms4) _ res res (n + 16)).
    - unfold ecall_preU. rewrite unpoison_nil.
      split; [|split; [split; [constructor | exact I] | intros s Hs; discriminate Hs]].
      eapply (ecall_pre_at tfibsegs B STK_fuzz_malloc (spZ regs) FM_PSTAT_FP ly S W mem md [] ly2 S2 W2 _ _ 1 (ms_regs ms4) (-32) J4);
        [exact Usp4 | reflexivity | lia | unfold ESTACK; lia
        | rewrite P1; apply ret_ok_even; vm_compute; reflexivity
        | rewrite P3, Eco, E3 by lia; exact Hgp | rewrite P4, Eco, E4 by lia; exact Htp].
    - rewrite P10. exact Ec39.
    - rewrite P11. reflexivity.
    - split; [apply Forall_cons; [|apply Forall_nil] | split; [constructor | exact I]].
      cbn [fst snd]. split; [lia|]. split; [lia|]. split; [reflexivity|].
      exists res, (n + 16). split; [exact Hin3|]. split; [lia|]. rewrite Hrq. lia.
    - exact Hin3.
    - lia.
    - rewrite Hrq. lia. }
  intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HARU & HP5 & Hsm5 & Heq5 & Hpres5 & _).
  assert (J5 : ajournal tfibsegs B STK_fuzz_malloc (spZ regs) FM_PSTAT_FP ly S W mem md [] ly2 S2 W2
    (unpoison [(res, 16)] mem5) md5 1).
  { eapply (ajournal_poison16 B TL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms4) (-32) res mem5 md5 J4);
      [exact Usp4 | reflexivity | lia | unfold ESTACK; lia | exact HARU | exact Hsm5 | exact Heq5 | exact Hpres5]. }
  assert (Hra5 : raZ (ms_regs ms4) = 0x81c8c) by (unfold raZ; rewrite P1; apply unsigned_lit_small; lia).
  unfold cfg_at. rewrite Hra5.
  (* what survives the poisoning call: everything but its 64-byte frame and the head's two shadow bytes *)
  assert (K5 : forall a, 0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ (kHighMemBeg <= a /\ ~ (spZ regs - 96 <= a < spZ regs - 32))) ->
    aview tfibsegs (w_H W2) mem5 a = aview tfibsegs (w_H W2) (ms_mem ms4) a).
  { intros a Ha Hw. unfold SHADOW_OFF in Hw. apply Heq5; [exact Ha | rewrite Usp4; unfold PO_WIN; lia |].
    unfold shadow_addr, SHADOW_OFF. lia. }
  assert (Happ : res + (n + 16) <= SHADOW_OFF \/ kHighMemBeg <= res).
  { unfold in_app, kLowShadowBeg, ASAN_CEIL in Hrapp. unfold SHADOW_OFF. lia. }
  assert (VH5 : val_mem tfibsegs (mrestrict (w_H W2) mem5) res 8 n).
  { apply (YCbq.val_mem_kept tfibsegs (w_H W2) (w_H W2) (ms_mem ms4) mem5 res 8 n); [|exact VH].
    intros k Hk. cbn in Hk. apply K5; lia. }
  destruct HK as (K1 & K2 & K3 & K4 & K5' & K6).
  assert (TR : forall a, (G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/
      G_COUNT <= a < G_COUNT + 8) -> aview tfibsegs (w_H W2) mem5 a = aview tfibsegs (w_H W) (ms_mem ms2) a).
  { intros a Ha. assert (Hr : 0x99000 <= a < 0x5f7000) by (unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha; lia).
    rewrite K5 by (unfold SHADOW_OFF; lia).
    rewrite (aview_eq_of (w_H W2) (ms_mem ms3) (ms_mem ms4) a).
    2:{ unfold mrestrict. rewrite HF4; [reflexivity|]. rewrite unsigned_lit_small by lia. intros Hw. apply WIN4 in Hw. lia. }
    rewrite (aview_eq_of (w_H W2) mem3 (ms_mem ms3) a).
    2:{ unfold mrestrict. rewrite HF3; [reflexivity|]. rewrite unsigned_lit_small by lia. intros Hw. apply WIN3 in Hw. lia. }
    apply K3; [apply fma_in_img; lia | | rewrite (ts_errno B HB); unfold TFIB_ERRNO; unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha; lia].
    unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha.
    destruct Ha as [Ha|[Ha|[Ha|Ha]]];
      [apply (fma_not_owned_static B 0x9e260 0x9e268 a HB) | apply (fma_not_owned_static B 0x5d4700 0x5d4708 a HB)
      | apply (fma_not_owned_static B 0x5d4720 0x5d4728 a HB) | apply (fma_not_owned_static B 0x5d4740 0x5d4748 a HB)];
      first [vm_compute; reflexivity | lia]. }
  assert (TRv : forall g v, (g = G_FAIL \/ g = G_LIVE \/ g = G_PEAK \/ g = G_COUNT) ->
    val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms2)) g 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem5) g 8 v).
  { intros g v Hg Hv. apply (YCbq.val_mem_kept tfibsegs (w_H W) (w_H W2) (ms_mem ms2) mem5 g 8 v); [|exact Hv].
    intros k Hk. cbn in Hk. apply TR. destruct Hg as [->|[->|[->| ->]]]; lia. }
  assert (TRf : forall a v, spZ regs - 32 <= a -> a + 8 <= spZ regs ->
    val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms4)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem5) a 8 v).
  { intros a v H1 H2 Hv. apply (YCbq.val_mem_kept tfibsegs (w_H W2) (w_H W2) (ms_mem ms4) mem5 a 8 v); [|exact Hv].
    intros k Hk. cbn in Hk. apply K5; lia. }
  (* the callee-saved registers own does not save (gp, tp, s2 .. s11) still hold the entry values *)
  assert (HPr : forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 ->
    getr regs5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr H2 H8 H9. rewrite (HP5 r Hr).
    rewrite (st_ok_restrict_reg tfibsegs (w_H W2) Ec _ ms4 (Z_to_bv 5 r) HS4).
    assert (Hrr : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
      r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
    destruct Hrr as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]];
    match goal with |- context [sr_get ?srs ?rr] => let v := eval vm_compute in (sr_get srs rr) in change (sr_get srs rr) with v end;
    cbn [sv_denot]; rewrite Eco by lia; rewrite HEE;
    match goal with |- context [ew (Ereg regs ?ex) ?k] =>
      rewrite (ew_Ereg_nat regs ex k (Z_to_bv 5 (Z.of_nat k)) eq_refl) end;
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity. }
  eapply SRr_mono.
  { eapply (fmm_seg_C B); try exact HB; try exact TL.
    - exact HAN.
    - exact Hc.
    - exact Hn1.
    - exact HnM.
    - exact Hlive.
    - exact Hcnt.
    - exact Hlp.
    - exact Hp64.
    - lia.
    - exact Hf64.
    - exact J5.
    - exact (ARU_ok tfibsegs B ly2 S2 [(res, 16)] W2 mem5 md5 HARU).
    - exact (ARU_poisoned tfibsegs B ly2 S2 [(res, 16)] W2 mem5 md5 HARU).
    - exact Eab.
    - exact VH5.
    - transitivity (getr (ms_regs ms4) 2); [apply (HP5 2); unfold acallee_saved; lia|].
      rewrite P2, Usp'. unfold YG0d.w64. f_equal; lia.
    - transitivity (getr (ms_regs ms4) 8); [apply (HP5 8); unfold acallee_saved; lia|]. rewrite P8. exact Ec39.
    - transitivity (getr (ms_regs ms4) 9); [apply (HP5 9); unfold acallee_saved; lia|]. rewrite P9. exact Ec10.
    - exact HPr.
    - replace (spZ regs - 8) with (spZ regs + -8) by lia. apply TRf; [lia | lia | exact VF8].
    - replace (spZ regs - 16) with (spZ regs + -16) by lia. apply TRf; [lia | lia | exact VF16].
    - replace (spZ regs - 24) with (spZ regs + -24) by lia. apply TRf; [lia | lia | exact VF24].
    - apply TRv; [tauto | exact VL2].
    - apply TRv; [tauto | exact VP2].
    - apply TRv; [tauto | exact VC2].
    - apply TRv; [tauto | exact VF2]. }
  intros W' c' _ Hp. right. exact Hp.
- (* g_count = g_fail_at: failing() sets g_fail_at = SIZE_MAX and the result is NULL *)
  rewrite branch_ne_U, (U_atom E 32 cnt E32 ltac:(lia)), (U_atom E 33 fail E33 ltac:(lia)) in Hc.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc. subst fail.
  lazymatch goal with HS0 : st_ok _ _ ?ss _ |- _ =>
    assert (WIN2 : forall a, in_wrange E (ss_mem ss) a -> fmm_winA (spZ regs) a) by win_solve Usp end.
  srr_runG_with tbl_fmm_ok HS.
  rename ms into ms2, HF into HF2, HFr into HFr2, HG into HG2, HH into HH2.
  assert (RAW2 : forall x : word, ~ fmm_winA (spZ regs) (bv_unsigned x) -> ms_mem ms2 x = mem x).
  { intros x Hx. rewrite (HF2 x (fun H => Hx (WIN2 _ H))), (HF1 x (fun H => Hx (WIN1 _ H))). reflexivity. }
  assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ fmm_winA (spZ regs) a ->
    aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) mem a).
  { intros a Ha Hc. apply aview_eq_of. unfold mrestrict. rewrite RAW2; [reflexivity|].
    rewrite unsigned_lit_small by lia. exact Hc. }
  eapply (SRr_ret_at tfibsegs tbl_fmm tbl_fmm_ok Hwx W E); [exact HS | reflexivity | vm_compute; reflexivity |].
  intros mat2. rewrite wvb_collapse.
  left. split; [reflexivity|].
  unfold fpost, apost_base.
  exists ly, S, (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md) mat2 md).
  rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10.
  split; [rewrite R1, E1, Hra; reflexivity|].
  split.
  { eapply (ajournal_stk_pstat B HB); [exact J0 | intros a Ha; exact Ha | | | | apply same_but_materialized_wvb_any].
    - intros x Hs Hp. unfold mrestrict. rewrite RAW2; [reflexivity|].
      intros [Hw|Hw]; [apply Hs; lia | apply Hp, fmm_cell_inFP; unfold fmm_cell; tauto].
    - intros x Hx. apply HG2, HG1, Hx.
    - intros x Hx. rewrite HH2, HH1 by exact Hx. reflexivity. }
  split; [eapply aregs_preserved_of_st_ok; [exact HS | rewrite HEE; apply env_agree_refl | vm_compute; reflexivity]|].
  split; [rewrite R10; reflexivity|].
  split; [reflexivity|].
  split; [eapply val_mem_kept; [exact GL | intros i Hi; apply AV2; unfold fmm_winA, G_FAIL, G_LIVE, G_PEAK, G_COUNT; cbn in Hi; lia]|].
  split; [eapply val_mem_kept; [exact GP | intros i Hi; apply AV2; unfold fmm_winA, G_FAIL, G_LIVE, G_PEAK, G_COUNT; cbn in Hi; lia]|].
  split.
  { eapply (val_mem_of_chunk8 E _ (ss_mem _) 3%nat G_COUNT (SOff 32 1) (cnt + 1));
      [exact (st_ok_mem_ok E _ (w_H W) ms2 HS) | vm_compute; reflexivity | | lia].
    cbn [sv_denot]. rewrite E32. unfold YG0d.w64. rewrite unsigned_lit_small by lia. reflexivity. }
  split.
  { eapply (val_mem_of_chunk8 E _ (ss_mem _) 4%nat G_FAIL (SLit 18446744073709551615) SIZE_MAXZ);
      [exact (st_ok_mem_ok E _ (w_H W) ms2 HS) | vm_compute; reflexivity | reflexivity | unfold SIZE_MAXZ; lia]. }
  unfold SIZE_MAXZ. lia.
Qed.

End c.
