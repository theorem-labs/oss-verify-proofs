(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v:26-243 (the harness entry
   segment, tfib_lib_A_seg) at c8557374ad2e for fuzz_knock's ASan image (fuzz_knock.asan, sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118), and the S0/S1 boundary state from the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACf7.v:27-28 (ss_A2). rule 24: no function proved (a port of the released
   cgif_file_fuzzer harness walk structure). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgMain0.v, with its module paths changed; 308 of its 337 lines of code are new or changed and 277 lines of the source are left out. *)
(* Segment S0 of diginet_counter_text's walk in image A (fuzz_codec.asan 0x86120): ct_seg_S0 of
   diginet_counter_text_A_inv.v, from parts a (entry -> the frame request) and b (-> __asan_memset's return) and the
   last part here, 0x86258 .. the loop-1 head 0x862a4 or the loop-2 head 0x863d8:
   a0 = -1; 16(s1) := F, 24(s1) := F; the null tests of q, sg, dt (beqz, not taken: the atoms are >= 1); 8(s1) := dt;
   the instrumented check of the text byte at q (paid by the shadow entry mkSHE 22 0 1 from ct_now); lbu a1 = tb[0];
   s10 = F + 32; beqz a1: tb[0] = 0 -> 0x863b8 (s11 = -8, a3 = a2 = 0, a4 = 8, a5 = 1, a0 = sg) to 0x863d8, else
   s11 = 0, s3 = s6 = q + 1, s2 = 46 to 0x862a4. The state is built at 0x86258 with tb[0] as atom 33, whose range
   ([0, 0] or [1, 255]) decides beqz a1, so each case is one run. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgChkC CPgWalk CPgWalkKept.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkFrame diginet_counter_text_A_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_counter_text_A_s0_a diginet_counter_text_A_s0_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the state at 0x86258: s9 = SB (atom 32); the spill slots 8 .. 32(s1), the text's first byte at q (atom 22) as e:
   the literal 0, or atom 33 (tb[0], range [lo, hi]) *)
Definition ct_rs3 (e : sv) : smem :=
  [YP09.mkRegion (Some 9%nat) 8 32 8 32 []; YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 e)]].
Definition ct_G3 (lo hi : Z) : facts :=
  mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 2) 0); (20%nat, mkAF 1 (2 ^ 63) 0); (19%nat, mkAF 1 (2 ^ 63) 0);
           (33%nat, mkAF lo hi 0); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (32%nat, mkAF SB SB 0)] [] [].
Definition ct_SH3 : list shent := [mkSHE 22 0 1].

(* the write windows of the part: the spill slots 8 .. 32(s1), in the caller's stack window *)
Ltac ct3_awr U9 sp1 sp0 :=
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] ].
(* the first text byte decides between the two loop heads *)
Lemma ct_spec_empty : forall t, nth 0 t 0 = 0 -> (0 < length t)%nat ->
  counter_text_spec t = ct2_go 0 [] (repeat 0 8) 0 8 [] 0.
Proof.
intros [|c t] Hc Hl; [cbn in Hl; lia|]. cbn [nth] in Hc. subst c.
unfold counter_text_spec. cbn [ct1_lib]. reflexivity.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Variables (B : asyms) (MT : ameter_ops) (RLO RHI SEG7TBL : Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis AIS : aintrin_realizes tfibsegs B OSet 0x51e34.

(* 0x86258 -> the loop-1 head or the loop-2 head *)
Lemma ct_s0_p3 : forall g W2 c2, ct_pre B g -> ct_now B RLO RHI SEG7TBL g -> ct_s0_r2 B g W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => exists pos, ct_cut B MT g pos PC_L1 (P_L1 g pos (length (cg_tb g))) W3 c3 \/
                                               ct_cut B MT g pos PC_L2 (P_L2 g pos 8) W3 c3).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj] W2 c2 Hpre Hnow Hr2.
pose proof (ct_wr_where B _ Hpre) as HWR.
unfold ct_pre in Hpre.
unfold ct_s0_r2, ct_s0_j, ct_saves, ct_now, cg_len, cg_sp, cg_sp1, cg_F, cg_FL, ct_wr in Hpre, Hnow, HWR, Hr2.
cbn [cg_STK cg_sp0 cg_FP cg_ly cg_S cg_W0 cg_mem0 cg_md0 cg_own cg_lyc cg_Sc cg_W cg_memc cg_mdc cg_k cg_regs
  cg_q cg_sg cg_dt cg_tb cg_sj cg_dj] in Hpre, Hnow, HWR, Hr2.
destruct Hpre as (HE & H10 & Hstr & H11 & Hsg & Hsj & Hsjl & H12 & Hdt & Hdj & Hd1 & Hd2 & Hd3 & Hfr8).
destruct Hr2 as (-> & S2 & regs2 & mem2 & md2 & pos & -> & (HJ2 & HK2 & KW2 & Eab & Hfrs2 & Hnin & HSf & Hio & Hflag &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27) & GSH & GDOT & R2 & R9 & R8 & R3 & R4 &
  R18 & R24 & R19 & R20 & R22 & R21 & R23 & R25).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_counter_text HE
  ltac:(unfold T_counter_text, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJc & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJc as (HARc & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : T_counter_text = 4288) by reflexivity. rewrite TT in *.
pose proof Hsg as (Hsg0 & Hsg63 & _). pose proof Hdt as (Hdt0 & Hdt63 & _).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & (Hsp0al & _) & _).
assert (HP2 : Permutation (ablocks B lyc S2) (ablocks B lyc Sc)) by (rewrite Eab; apply Permutation_refl).
(* the text at this state (ct_now) *)
destruct (Hnow pos lyc S2 W mem2 md2 HJ2 HK2 HP2 Hnin) as ((Gtb & RAq) & _ & _ & _).
pose proof Hstr as (Hq0 & _ & Hin0 & (_ & Hqn & _ & _ & _ & Hqam & Hqwin)).
assert (Hlen : (0 < length tb)%nat) by (destruct tb; [destruct Hin0 | cbn; lia]).
destruct (Gtb 0%nat Hlen) as (Vtb0 & Rtb0). rewrite Z.add_0_r in Vtb0.
set (tb0 := nth 0 tb 0) in *.
assert (Hq47 : q + 1 <= 2 ^ 47 - 1).
{ unfold amem_range in Hqam. rewrite C4, C5 in Hqam. destruct Hqam as [Hl | [_ Hh]]; lia. }
set (F := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
destruct (sp1_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by lia. clear Hsp1r.
(* the start state *)
set (E := Ereg regs2 (cw_extra [tb0])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 tb0) by (subst E; exact (cw_ew_x regs2 [tb0] 0)).
assert (E22 : ew E 22 = Z_to_bv 64 q) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E20 : ew E 20 = Z_to_bv 64 sg) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E19 : ew E 19 = Z_to_bv 64 dt) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (U22 : bv_unsigned (ew E 22) = q) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs2 (cw_extra [tb0])) E) by (subst E; apply env_agree_refl).
assert (HSE : forall e lo hi, sv_denot E e = Z_to_bv 64 tb0 -> 0 <= lo -> lo <= tb0 <= hi -> hi <= 255 ->
  st_ok tfibsegs E (mkSS 0x86258 (sr_set sr_atoms 25%bv (SOff 32 0)) (ct_rs3 e) None (ct_G3 lo hi))
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x86258) mem2 (seg_rom tfibsegs)))).
{ intros e lo hi He Hlo Htb Hhi.
  rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra [tb0])) with E.
  - apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros Hx; discriminate Hx |].
    rewrite R25. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - vm_compute. reflexivity.
  - unfold ct_rs3. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable tfibsegs). apply HJpres2. lia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ q 0 1 e tb0); [exact He | zside | zside |].
      rewrite Z.add_0_r. exact Vtb0.
  - apply pairwise_disjoint_of_extents. unfold ct_rs3, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold coff_win in Hqwin. repeat split; lia.
  - split; [|split; exact I].
    unfold ct_G3. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U22, U2, U9, (EE 20%nat 20%bv eq_refl), (EE 19%nat 19%bv eq_refl), R20, R19, E33, E32.
    rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; try exact Hsp1al. }
clearbody E.
assert (SH0 : forall mem', range_addressable (aview tfibsegs (w_H W) mem') SHADOW_OFF q (Z.of_nat (length tb)) ->
  sh_ok tfibsegs CW_Bx ct_SH3 E (mrestrict (w_H W) mem')).
{ intros mem' Hrq. unfold ct_SH3. apply Forall_cons; [|apply Forall_nil].
  apply (cw_shent_ra W mem' E 22 q 1); [ | | lia | lia | lia | exact E22 | exact E32].
  - intros x Hx. apply Hrq. lia.
  - unfold amem_range in Hqam |- *. lia. }
(* what the part keeps: everything but the spill slots 8 .. 32(s1) *)
set (Xs := fun a => sp1 + 8 <= a < sp1 + 32).
assert (KC : forall mem3, (forall a, 0 <= a < 2 ^ 64 -> ~ Xs a -> aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
  tcj_kept tfibsegs B 4288 lyc Sc W memc W mem3 (spZ regs) (fun a => sg <= a < sg + 8 \/ dt <= a < dt + 1) /\
  (forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> ~ Xs x) ->
     val_mem tfibsegs (mrestrict (w_H W) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W) mem3) a n v) /\
  rdword (aview tfibsegs (w_H W) mem3) (F + 120) = Some FL /\
  garr8 tfibsegs (mrestrict (w_H W) mem3) (SB + F / 8) CT_FRAME_SHADOW /\
  (forall i, 0 <= i < 8 -> val_mem tfibsegs (mrestrict (w_H W) mem3) (F + 64 + 4 * i) 4 (nth (Z.to_nat i) (repeat 0 8) 0)) /\
  garr8 tfibsegs (mrestrict (w_H W) mem3) sg sj /\ val_mem tfibsegs (mrestrict (w_H W) mem3) dt 1 dj).
{ intros mem3 KX KP.
  assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 1 pos HAR2 Hin) as (HF4096 & HFceil & _).
  destruct (FFL _ _ _ _ _ 1 pos HAR2 Hin) as (_ & _ & _ & (HFL4096 & _ & HFLc)).
  change (fs_frame_bytes 1) with 128 in HFceil. fold F in HF4096, HFceil. fold FL in HFL4096, HFLc.
  assert (HF8 : F / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
  assert (HF0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  assert (KV : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> ~ Xs x) ->
     val_mem tfibsegs (mrestrict (w_H W) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W) mem3) a n v).
  { intros a n v H0 H1 H2 Hv. apply (cw_val_mem_kept (w_H W) (w_H W) mem2 mem3 a n v); [|exact Hv].
    intros x Hx. apply KX; [lia | exact (H2 x Hx)]. }
  assert (KWa : forall a, (sg <= a < sg + 8 \/ dt <= a < dt + 1) ->
     aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) memc a).
  { intros a Ha. rewrite <- (KW2 a Ha). pose proof (HWR a Ha) as (_ & Hw).
    apply KX; [destruct Ha; lia | unfold Xs; lia]. }
  split.
  { apply (cw_kept_step B LAWS 4288 lyc Sc W memc mdc W mem2 mem3 (spZ regs) _ Xs ltac:(lia) HARc HK2 KX); [|exact KP].
    intros a Ha. left. unfold Xs in Ha. lia. }
  split; [exact KV|].
  split.
  { apply rdword_of_val_mem; [|lia].
    apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia |].
    exact (val_mem_of_rdword tfibsegs _ _ _ _ Hflag). }
  split.
  { intros j Hj. destruct (GSH j Hj) as (Vj & Rj). split; [|exact Rj].
    cbn [length CT_FRAME_SHADOW] in Hj.
    apply KV; [unfold SB; lia | cbn; unfold SB; lia | intros x Hx; unfold Xs, SB in *; cbn in Hx; lia | exact Vj]. }
  split.
  { intros i Hi. rewrite nth_repeat.
    apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | exact (GDOT i Hi)]. }
  split.
  { intros j Hj. destruct (Hsj j Hj) as (Vj & Rj). split; [|exact Rj]. rewrite Hsjl in Hj.
    apply (cw_val_mem_kept (w_H W) (w_H W) memc mem3 _ 1 _); [|exact Vj].
    intros x Hx. cbn in Hx. apply KWa. left. lia. }
  apply (cw_val_mem_kept (w_H W) (w_H W) memc mem3 dt 1 dj); [|exact Hdj].
  intros x Hx. cbn in Hx. apply KWa. right. lia. }
assert (HFb : 4096 <= F /\ F + 128 <= alloc_ceiling).
{ assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 1 pos HAR2 Hin) as (HF4096 & HFceil & _).
  change (fs_frame_bytes 1) with 128 in HFceil. fold F in HF4096, HFceil. lia. }
(* the frame and the meter from the request on *)
destruct (cw_frame_start MT MTL MTF B lyc Sc S2 HSf) as (_ & HMO).
(* the runs take the newest journal *)
pose proof HJ2 as HJ3. clear HJ2. rename HJ3 into HJ2.
destruct (Z.eq_dec tb0 0) as [Htb0 | Htb0].
- (* tb[0] = 0: the loop-2 head *)
  pose proof (HSE (SLit 0) 0 0 ltac:(rewrite Htb0; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
  pose proof (SH0 mem2 RAq) as SHOK.
  cw_run_to ltac:(ct3_awr U9 sp1 sp0) 0x863d8.
  lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
    assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ Xs a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
    [ intros a Ha Hx; apply (ct_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx; unfold Xs;
      lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
      repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9 in Hb; lia | ]);
      destruct Hr
    | ];
    assert (KP : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
    clear HFr HG
  end.
  destruct (KC (ms_mem ms) KX KP) as (HK3 & KV & HFL3 & GSH3 & GDOT3 & GSJ3 & GDJ3).
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  lazymatch type of RG with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG end.
  rreg HS (2%bv : bv 5) G2. rreg HS (3%bv : bv 5) G3. rreg HS (4%bv : bv 5) G4. rreg HS (8%bv : bv 5) G8.
  rreg HS (9%bv : bv 5) G9. rreg HS (10%bv : bv 5) G10. rreg HS (12%bv : bv 5) G12. rreg HS (13%bv : bv 5) G13.
  rreg HS (14%bv : bv 5) G14. rreg HS (15%bv : bv 5) G15. rreg HS (20%bv : bv 5) G20. rreg HS (21%bv : bv 5) G21.
  rreg HS (23%bv : bv 5) G23. rreg HS (25%bv : bv 5) G25. rreg HS (26%bv : bv 5) G26. rreg HS (27%bv : bv 5) G27.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (AGv : forall n, (n < 34)%nat -> ew Ev n = ew E n) by (intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity) end.
  apply SRr_ret. exists pos. right.
  unfold ct_cut, P_L2, ct_common, ct_arrays, cg_len, cg_sp, cg_sp1, cg_F, cg_FL, ct_wr.
  cbn [cg_STK cg_sp0 cg_FP cg_ly cg_S cg_W0 cg_mem0 cg_md0 cg_own cg_lyc cg_Sc cg_W cg_memc cg_mdc cg_k cg_regs
    cg_q cg_sg cg_dt cg_tb cg_sj cg_dj].
  fold F FL sp1. rewrite TT.
  exists lyc, S2, (ms_regs ms), (ms_mem ms); eexists.
  split; [rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) at 1; reflexivity|].
  split; [exact HJ2|].
  split; [exact HK3|]. split; [exact HP2|]. split; [exact Hnin|].
  split; [eapply same_io_trans; [exact Hio | apply cw_same_io_wvb]|].
  split; [exact HMO|].
  split.
  { split; [rewrite G8, ?(AGv 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite G2, ?(AGv 2%nat ltac:(lia)); exact E2|].
    split; [rewrite G9, ?(AGv 9%nat ltac:(lia)); exact E9|].
    split; [rewrite G3, ?(AGv 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl); exact R3|].
    split; [rewrite G4, ?(AGv 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl); exact R4|].
    split; [rewrite G23, ?(AGv 23%nat ltac:(lia)), (EE 23%nat 23%bv eq_refl); exact R23|].
    split; [rewrite G25, ?(AGv 32%nat ltac:(lia)); exact E32|].
    do 13 (split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | assumption]|]).
    split; [eapply (ct_fld _ _ 9 _ _ _ _ _ _ 8 8%N 19%nat dt RG); [rewrite (AGv 9%nat ltac:(lia)); exact U9 | ct_in
      | rewrite (AGv 19%nat ltac:(lia)); exact E19 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia]|].
    split; [eapply (ct_fld _ _ 9 _ _ _ _ _ _ 16 8%N 18%nat F RG); [rewrite (AGv 9%nat ltac:(lia)); exact U9 | ct_in
      | rewrite (AGv 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl); exact R18 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia]|].
    split; [eapply (ct_fld _ _ 9 _ _ _ _ _ _ 24 8%N 24%nat F RG); [rewrite (AGv 9%nat ltac:(lia)); exact U9 | ct_in
      | rewrite (AGv 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl); exact R24 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia]|].
    split; [exact HFL3 | exact GSH3]. }
  exists 0, 0, 0, [], (repeat 0 8), [].
  split; [rewrite G10, ?(AGv 20%nat ltac:(lia)), Z.add_0_r; exact E20|].
  split; [rewrite G20, ?(AGv 20%nat ltac:(lia)), Z.add_0_r; exact E20|].
  split; [rewrite G12; reflexivity|].
  split; [rewrite G13; reflexivity|].
  split; [rewrite G14; reflexivity|].
  split; [rewrite G15; reflexivity|].
  split; [rewrite G21, ?(AGv 21%nat ltac:(lia)), (EE 21%nat 21%bv eq_refl); exact R21|].
  split; [rewrite G26, ?(AGv 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl), R24; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite G27; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
  split; [reflexivity|]. split; [lia|].
  split; [exact (ct_spec_empty tb Htb0 Hlen)|].
  split; [split; [exact ct_inv_0|]; split; [repeat constructor; lia|]; split; [reflexivity | constructor]|].
  split; [reflexivity|]. split; [constructor|]. split; [lia|].
  split; [split; [exact GDOT3 | intros i Hi; lia]|].
  split; [cbn [app skipn Z.to_nat]; exact GSJ3 | exact GDJ3].
- (* tb[0] <> 0: the loop-1 head *)
  pose proof (HSE (SOff 33 0) 1 255 ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
  pose proof (SH0 mem2 RAq) as SHOK.
  cw_run_to ltac:(ct3_awr U9 sp1 sp0) 0x862a4.
  lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
    assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ Xs a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
    [ intros a Ha Hx; apply (ct_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx; unfold Xs;
      lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
      repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9 in Hb; lia | ]);
      destruct Hr
    | ];
    assert (KP : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
    clear HFr HG
  end.
  destruct (KC (ms_mem ms) KX KP) as (HK3 & KV & HFL3 & GSH3 & GDOT3 & GSJ3 & GDJ3).
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  lazymatch type of RG with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG end.
  rreg HS (2%bv : bv 5) G2. rreg HS (3%bv : bv 5) G3. rreg HS (4%bv : bv 5) G4. rreg HS (8%bv : bv 5) G8.
  rreg HS (9%bv : bv 5) G9. rreg HS (11%bv : bv 5) G11. rreg HS (18%bv : bv 5) G18. rreg HS (19%bv : bv 5) G19.
  rreg HS (20%bv : bv 5) G20. rreg HS (21%bv : bv 5) G21. rreg HS (22%bv : bv 5) G22.
  rreg HS (23%bv : bv 5) G23. rreg HS (25%bv : bv 5) G25. rreg HS (26%bv : bv 5) G26. rreg HS (27%bv : bv 5) G27.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (AGv : forall n, (n < 34)%nat -> ew Ev n = ew E n) by (intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity) end.
  apply SRr_ret. exists pos. left.
  unfold ct_cut, P_L1, ct_common, ct_arrays, cg_len, cg_sp, cg_sp1, cg_F, cg_FL, ct_wr.
  cbn [cg_STK cg_sp0 cg_FP cg_ly cg_S cg_W0 cg_mem0 cg_md0 cg_own cg_lyc cg_Sc cg_W cg_memc cg_mdc cg_k cg_regs
    cg_q cg_sg cg_dt cg_tb cg_sj cg_dj].
  fold F FL sp1. rewrite TT.
  exists lyc, S2, (ms_regs ms), (ms_mem ms); eexists.
  split; [rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) at 1; reflexivity|].
  split; [exact HJ2|].
  split; [exact HK3|]. split; [exact HP2|]. split; [exact Hnin|].
  split; [eapply same_io_trans; [exact Hio | apply cw_same_io_wvb]|].
  split; [exact HMO|].
  split.
  { split; [rewrite G8, ?(AGv 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite G2, ?(AGv 2%nat ltac:(lia)); exact E2|].
    split; [rewrite G9, ?(AGv 9%nat ltac:(lia)); exact E9|].
    split; [rewrite G3, ?(AGv 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl); exact R3|].
    split; [rewrite G4, ?(AGv 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl); exact R4|].
    split; [rewrite G23, ?(AGv 23%nat ltac:(lia)), (EE 23%nat 23%bv eq_refl); exact R23|].
    split; [rewrite G25, ?(AGv 32%nat ltac:(lia)); exact E32|].
    do 13 (split; [apply KV; [lia | cbn; lia | intros x Hx; unfold Xs; cbn in Hx; lia | assumption]|]).
    split; [eapply (ct_fld _ _ 9 _ _ _ _ _ _ 8 8%N 19%nat dt RG); [rewrite (AGv 9%nat ltac:(lia)); exact U9 | ct_in
      | rewrite (AGv 19%nat ltac:(lia)); exact E19 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia]|].
    split; [eapply (ct_fld _ _ 9 _ _ _ _ _ _ 16 8%N 18%nat F RG); [rewrite (AGv 9%nat ltac:(lia)); exact U9 | ct_in
      | rewrite (AGv 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl); exact R18 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia]|].
    split; [eapply (ct_fld _ _ 9 _ _ _ _ _ _ 24 8%N 24%nat F RG); [rewrite (AGv 9%nat ltac:(lia)); exact U9 | ct_in
      | rewrite (AGv 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl); exact R24 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia]|].
    split; [exact HFL3 | exact GSH3]. }
  exists 0, 0, tb0, [], (repeat 0 8).
  split; [rewrite G11, ?(AGv 33%nat ltac:(lia)); exact E33|].
  split; [rewrite G18; reflexivity|].
  split; [rewrite G19, ?(AGv 22%nat ltac:(lia)), U22; replace (q + 0 + 1) with (q + 1) by lia; reflexivity|].
  split; [rewrite G22, ?(AGv 22%nat ltac:(lia)), U22; replace (q + 0 + 1) with (q + 1) by lia; reflexivity|].
  split; [rewrite G20, ?(AGv 20%nat ltac:(lia)); exact E20|].
  split; [rewrite G21, ?(AGv 21%nat ltac:(lia)), (EE 21%nat 21%bv eq_refl); exact R21|].
  split; [rewrite G26, ?(AGv 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl), R24; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite G27; reflexivity|].
  split; [lia|]. split; [rewrite Z.sub_0_r, Nat2Z.id; lia|].
  split; [reflexivity|]. split; [exact Htb0|].
  split; [destruct tb as [|c t]; [cbn in Hlen; lia|]; cbn [firstn]; constructor; [exact Htb0 | constructor]|].
  split; [reflexivity|].
  split; [split; [exact ct_inv_0|]; split; [repeat constructor; lia|]; split; [reflexivity | constructor]|].
  split; [split; [exact GDOT3 | intros i Hi; lia]|].
  split; [exact GSJ3 | exact GDJ3].
Qed.

(* S0: entry -> the frame request (part a) -> __asan_memset (part b) -> a loop head (above) *)
Theorem ct_s0_holds : ct_seg_S0 B MT RLO RHI SEG7TBL.
Proof.
unfold ct_seg_S0. intros g Hpre Hnow.
eapply SRr_bind; [eapply ct_s0_p1; eassumption|]. intros W2 c2 _ H1.
eapply SRr_bind; [eapply ct_s0_p2; eassumption|]. intros W3 c3 _ H2.
exact (ct_s0_p3 g W3 c3 Hpre Hnow H2).
Qed.
End s.
