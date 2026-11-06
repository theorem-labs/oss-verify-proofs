(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module paths and module names changed; 222 of its 260 lines of code are new or changed and 320 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the strcmp LOOP of remember 0x89db4 (+0x5c .. +0x74), its two exits, and the
   symbolic state the walk rebuilds at its head.

   The loop body is `mv a0, s2; mv a1, s1; jal wrapper_strcmp` then `beqz a0` / `addi s6, s6, -1` /
   `addi s2, s2, 0x10` / `bnez s6`, so between two turns only the machine registers change and the memory does
   not change at all. A symbolic state cannot be carried across the call (`ss_after_call` havocs the
   caller-saved registers to fresh atoms, and the next call would need a bigger havoc base every turn), so the
   state is REBUILT at every head from the machine registers, with the eight saved words of the frame as the
   extra atoms 34..41 and s5 pinned to the shadow address of s0, which is the shape `match_x` (YCbn.v:77)
   reads at the store check +0xa8.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0e YK0v YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c remember_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import rememberPost rememberEntry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis HV : LinkVals (L := link_listing).

(* `regs_ok` with ONE register pinned to a shape the machine value matches (YP0l.v `regs_ok_set`, but keeping
   the register map as it is). *)
Lemma regs_ok_pin : forall E (sr : list sv) (rg : bvmap 5 word) (r : bv 5) e,
  regs_ok E sr rg -> bv_eqb r 0 = false -> sv_denot E e = getr rg r ->
  regs_ok E (sr_set sr r e) rg.
Proof.
intros E sr rg r e Hr Hr0 Hv r'.
unfold sr_set. rewrite Hr0.
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
- exact Hr.
Qed.

(* a logical shift right by 3 of a literal *)
Lemma rl_srl3 : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_srl.
rewrite !unsigned_lit_small by lia.
change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
reflexivity.
Qed.

Lemma rl_u64 : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof.
intros x. pose proof (bv_unsigned_in_range _ x).
change (bv_modulus 64) with (2 ^ 64)%Z in *. lia.
Qed.

(* a sub-range of an addressable / hull-visible range is addressable / hull-visible *)
Lemma rl_ra_sub : forall rd a n x m,
  range_addressable rd SHADOW_OFF a n -> a <= x -> x + m <= a + n ->
  range_addressable rd SHADOW_OFF x m.
Proof. intros rd a n x m H Hx Hm y Hy. apply H. lia. Qed.

Lemma rl_hull_sub : forall rd a n x m,
  shadow_hull_vis rd a n -> 0 <= a -> 0 < m -> a <= x -> x + m <= a + n ->
  shadow_hull_vis rd x m.
Proof.
intros rd a n x m H Ha Hm Hx Hxm s Hs. apply H.
unfold shadow_addr in *.
pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + x / 8) 8 ltac:(lia)
              ltac:(pose proof (Z.div_le_mono a x 8 ltac:(lia) ltac:(lia)); lia)) as D1.
pose proof (Z.div_le_mono (SHADOW_OFF + (x + m - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)
              ltac:(pose proof (Z.div_le_mono (x + m - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)); lia)) as D2.
lia.
Qed.

(* what the strcmp wrapper needs of the slot it reads at turn i *)
Lemma rem_slot_rt : forall (W : world pa_segs) memL regs p n gbs i,
  amarks_at pa_segs (rdW W memL) p gbs -> marks_wf gbs -> mk_n gbs = n ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memL) p -> 0 <= i < n ->
  astr_rt_ok pa_segs regs REMEMBER_AK (rdW W memL) (p + (MK_NAME + MARK_LEN * i))
    (cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)).
Proof.
intros W memL regs p n gbs i HMK HWF Hn HBLK Hi.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HBLK as (Hp0 & Hpm & Hpra & Hphv & Hptail & Hpap).
pose proof HMK as (HMKb & HMKlen). pose proof HMKb as (HMKbytes & HMKwr).
pose proof (amk_n_range gbs HWF) as Hnr. rewrite Hn in Hnr. unfold MARKS_MAX in Hnr.
pose proof (amk_slot_len gbs i HWF ltac:(lia)) as Hsl.
set (s := cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)) in *.
set (x := p + (MK_NAME + MARK_LEN * i)) in *.
assert (Hxlo : p + 4 <= x) by (unfold x, MK_NAME, MARK_LEN; lia).
assert (Hxhi : x + Z.of_nat (length s) + 8 <= p + 523)
  by (unfold x, MK_NAME, MARK_LEN; lia).
unfold astr_rt_ok.
split; [unfold x, MK_NAME, MARK_LEN; lia|].
split; [lia|].
split.
{ unfold amem_range, MK_SIZE in Hpm. unfold amem_range.
  destruct Hpm as [Hz | [Hz1 Hz2]]; [left; lia | right; split; lia]. }
split.
{ apply (rl_ra_sub _ p MK_SIZE); [exact Hpra | unfold x, MK_NAME, MARK_LEN; lia
                                  | unfold MK_SIZE, x, MK_NAME, MARK_LEN in *; lia]. }
split.
{ apply (rl_hull_sub _ p MK_SIZE); [exact Hphv | lia | lia | unfold x, MK_NAME, MARK_LEN; lia
                                    | unfold MK_SIZE, x, MK_NAME, MARK_LEN in *; lia]. }
split.
{ intros b Hb.
  pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)) as Hmd.
  destruct (Z_lt_le_dec b (p + MK_SIZE)) as [Hlt | Hge].
  - destruct HMKbytes as (_ & _ & Hnth).
    assert (Hb0 : (Z.to_nat (b - p) < length gbs)%nat) by (unfold MK_SIZE in *; lia).
    pose proof (Hnth (Z.to_nat (b - p)) Hb0) as Hbb.
    replace (p + Z.of_nat (Z.to_nat (b - p))) with b in Hbb by lia.
    intros Hc. unfold ard in Hc. rewrite Hbb in Hc.
    destruct (nth_error gbs (Z.to_nat (b - p))) eqn:Eg; [discriminate Hc|].
    apply nth_error_None in Eg. unfold MK_SIZE in *. lia.
  - apply Hptail. unfold MK_SIZE in *. lia. }
unfold apart_frame in *. unfold MK_SIZE, x, MK_NAME, MARK_LEN in *. lia.
Qed.

(* ==========================================================================
   The loop's state holds at any of its offsets (+0x5c the head, +0x68 just after the call),
   rebuilt from the machine registers
   ========================================================================== *)
Lemma rem_lentry : forall (W : world pa_segs) memL regs regsL p q n gbs off,
  getr regsL 2 = Z_to_bv 64 (spZ regs - 64) ->
  getr regsL 8 = Z_to_bv 64 p -> getr regsL 9 = Z_to_bv 64 q ->
  getr regsL 21 = Z_to_bv 64 (RSB + p / 8) ->
  val_mem pa_segs (rdW W memL) (spZ regs - 64 + 0) 8 (bv_unsigned (getr regs 22)) ->
  val_mem pa_segs (rdW W memL) (spZ regs - 64 + 8) 8 (bv_unsigned (getr regs 21)) ->
  val_mem pa_segs (rdW W memL) (spZ regs - 64 + 16) 8 (bv_unsigned (getr regs 20)) ->
  val_mem pa_segs (rdW W memL) (spZ regs - 64 + 24) 8 (bv_unsigned (getr regs 19)) ->
  val_mem pa_segs (rdW W memL) (spZ regs - 64 + 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem pa_segs (rdW W memL) (spZ regs - 64 + 40) 8 (bv_unsigned (getr regs 9)) ->
  val_mem pa_segs (rdW W memL) (spZ regs - 64 + 48) 8 (bv_unsigned (getr regs 8)) ->
  val_mem pa_segs (rdW W memL) (spZ regs - 64 + 56) 8 (bv_unsigned (getr regs 1)) ->
  amarks_at pa_segs (rdW W memL) p gbs -> marks_wf gbs -> mk_n gbs = n ->
  amarks_blk_ok pa_segs regs REMEMBER_AK (rdW W memL) p -> 4096 <= p ->
  0 < q -> q <= 2 ^ 47 - 1 ->
  alloc_ceiling <= spZ regs - REMEMBER_AK -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  (forall a, spZ regs - 64 <= a < spZ regs -> apresent (w_H W) memL a) ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regsL (l_extra n regs))) (l_ss_at off)
    (restrict (w_H W) (mkst regsL (Z_to_bv 64 (pa_val A_TEXT + off)) memL (seg_rom pa_segs))).
Proof.
intros W memL regs regsL p q n gbs off Hsp Hs0 Hs1 Hs5 F0 F1 F2 F3 F4 F5 F6 F7
  HMK HWF Hn HBLK H4096 Hq0 Hqb Hceil H47 Hal16 Hpres.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKv : REMEMBER_AK = 8256) by reflexivity.
pose proof HBLK as (Hp0 & Hpm & Hpra & Hphv & Hptail & Hpap).
pose proof HMK as (HMKb & HMKlen). pose proof HMKb as (HMKbytes & HMKwr).
assert (Hpbound : p + 524 <= 2 ^ 47 - 1)
  by (unfold amem_range, MK_SIZE in Hpm; destruct Hpm as [Hx | [_ Hx]]; lia).
pose proof (amk_n_range gbs HWF) as Hnr. rewrite Hn in Hnr. unfold MARKS_MAX in Hnr.
pose proof (amk_n_val pa_segs (rdW W memL) p gbs HMK) as HnV. rewrite Hn in HnV.
set (E := Eimg (Ereg regsL (l_extra n regs))).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regsL (l_extra n regs)) m)
  by (intros m Hm; subst E; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regsL 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regsL 8)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 8 8%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 RSB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (rewrite E2, Hsp; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = p)
  by (rewrite E8, Hs0; apply unsigned_lit_small; lia).
assert (Hdiv : 0 <= p / 8 < 2 ^ 44)
  by (pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); split; [lia | apply Z.div_lt_upper_bound; lia]).
rewrite restrict_mkst_fx. unfold l_ss_at. apply pa_entry_st_ok_full.
- (* every register is its own atom but s5, the shadow address of s0 *)
  unfold l_sr. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | reflexivity |].
  cbn [sv_denot]. fold E. rewrite E8, E32, Hs0, !Z.add_0_r.
  rewrite (unsigned_lit_small RSB) by (unfold RSB; lia).
  rewrite (unsigned_lit_small p) by lia.
  rewrite rl_srl3 by lia. rewrite alu_add_small by (unfold M64, RSB in *; lia).
  transitivity (Z_to_bv 64 (RSB + p / 8)); [f_equal; lia|]. symmetry. exact Hs5.
- vm_compute. reflexivity.
- unfold l_regions, frame_region, mk_region_loop.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    assert (A41 : ew E 41 = getr regs 22)
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 9)).
    assert (A40 : ew E 40 = getr regs 21)
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 8)).
    assert (A39 : ew E 39 = getr regs 20)
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 7)).
    assert (A38 : ew E 38 = getr regs 19)
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 6)).
    assert (A37 : ew E 37 = getr regs 18)
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 5)).
    assert (A36 : ew E 36 = getr regs 9)
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 4)).
    assert (A35 : ew E 35 = getr regs 8)
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 3)).
    assert (A34 : ew E 34 = getr regs 1)
      by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsL _ 2)).
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val pa_segs E _ (spZ regs - 64) 0 8 (SOff 41 0)
               (bv_unsigned (getr regs 22)));
        [cbn [sv_denot]; fold E; rewrite A41, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (rl_u64 (getr regs 22)); zside | zside | exact F0].
    * apply (chunk_ok_val pa_segs E _ (spZ regs - 64) 8 8 (SOff 40 0)
               (bv_unsigned (getr regs 21)));
        [cbn [sv_denot]; fold E; rewrite A40, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (rl_u64 (getr regs 21)); zside | zside | exact F1].
    * apply (chunk_ok_val pa_segs E _ (spZ regs - 64) 16 8 (SOff 39 0)
               (bv_unsigned (getr regs 20)));
        [cbn [sv_denot]; fold E; rewrite A39, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (rl_u64 (getr regs 20)); zside | zside | exact F2].
    * apply (chunk_ok_val pa_segs E _ (spZ regs - 64) 24 8 (SOff 38 0)
               (bv_unsigned (getr regs 19)));
        [cbn [sv_denot]; fold E; rewrite A38, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (rl_u64 (getr regs 19)); zside | zside | exact F3].
    * apply (chunk_ok_val pa_segs E _ (spZ regs - 64) 32 8 (SOff 37 0)
               (bv_unsigned (getr regs 18)));
        [cbn [sv_denot]; fold E; rewrite A37, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (rl_u64 (getr regs 18)); zside | zside | exact F4].
    * apply (chunk_ok_val pa_segs E _ (spZ regs - 64) 40 8 (SOff 36 0)
               (bv_unsigned (getr regs 9)));
        [cbn [sv_denot]; fold E; rewrite A36, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (rl_u64 (getr regs 9)); zside | zside | exact F5].
    * apply (chunk_ok_val pa_segs E _ (spZ regs - 64) 48 8 (SOff 35 0)
               (bv_unsigned (getr regs 8)));
        [cbn [sv_denot]; fold E; rewrite A35, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (rl_u64 (getr regs 8)); zside | zside | exact F6].
    * apply (chunk_ok_val pa_segs E _ (spZ regs - 64) 56 8 (SOff 34 0)
               (bv_unsigned (getr regs 1)));
        [cbn [sv_denot]; fold E; rewrite A34, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (rl_u64 (getr regs 1)); zside | zside | exact F7].
  + cbn [base_val]. fold E. rewrite U8. unfold MK_SIZE in *.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; cbn [ms_mem restrict mkst]; apply HMKwr; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val pa_segs E _ p 0 4 (SOff 33 0) n);
      [cbn [sv_denot]; fold E; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | cbn; lia | cbn; lia | cbn [ms_mem restrict mkst]; rewrite Z.add_0_r; exact HnV].
- apply pairwise_disjoint_of_extents.
  unfold l_regions, frame_region, mk_region_loop, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite Usp, U8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold MK_SIZE, apart_frame in *.
  revert Hpap Hceil H47 HKv. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [l_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, U8, E32, E33.
  assert (E9v : bv_unsigned (ew E 9) = q)
    by (rewrite EL by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regsL _ 9 9%bv eq_refl), Hs1; apply unsigned_lit_small; lia).
  rewrite E9v, !unsigned_lit_small by (unfold RSB; lia).
  try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  revert Hceil H47 Hal16 HKv H4096 Hpbound Hq0 Hqb Hnr C1a C1b. clear. unfold RSB. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia].
Qed.

End b.
End a.
