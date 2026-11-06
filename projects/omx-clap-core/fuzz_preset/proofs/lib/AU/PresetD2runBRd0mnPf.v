(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: memnorm twin of lib/AU/PresetD2runBRd0Pf.v blob
   ee21d759ffa8efb2252a804a7877b5aa397640b0 (WalkMain, a Theorem Labs lane), lane MnPrefix (a Theorem Labs lane, 2026-10-29); the
   port/a2b.py (f5113cbc90e5) twin of lib/A/PresetD2runARd0mnPf.v (code(a2b(lib/A/PresetD2runARd0Pf.v)) =
   code(lib/AU/PresetD2runBRd0Pf.v), 0 lines).
   It proves the same two theorems at the NEW statements (lib/AU/PresetD2runB.v): rd0_file_tfa_cf and hdr_tfa_cf take
   `YAkMemnorm.memnorm tfibsegs (ms_mem ms)` of the full overlay after PINV, CwPinvB's gr_grow_cf_B takes it in its
   pre and its continuation, and the read check / memcpy / free sites end their posts with the memnorm keep. The read
   loop recurses, so memnorm is an INVARIANT of loop_seg_cf (its pre and its continuation) and a premise of
   loop_RP_cf. Changes from the donor file: rd_to_RW -> YD2mnSeg.rd_to_RW_mn, cp_run -> YD2mnSeg.cp_run_mn (at
   P := memnorm, laws YSRrMemnorm.srr_inv_laws_memnorm_k); the inline runner block of loop_seg_cf -> YA0oInv's
   srr_run_with_inv / srr_run_to_with_inv (srr_branch_with keeps the memory); lane CwRunqA's rd_step_eof_cf /
   rd_step_pos_cf / rd_chk_cf / rd_cpy_cf (lib/AU/PresetRdcfB.v) take and give memnorm; the hand steps add_rt_cf,
   reabs_RD and st_ok_agree keep the memory. tfib_rd0_dir_cf_B's statement does not carry memnorm; its proof is the
   donor's. The donor file's header follows.
   Donor header: for omx-clap-core/fuzz_preset (asan-ubsan image), the PROOFS of lane CwRunqA's read
   leaves tfib_rd0_dir_cf_B and tfib_rd0_file_cf_B (lib/AU/PresetD2runB.v, a working branch 16a514055f53),
   ported from proofs/cgif/cgif_file_fuzzer/lib/YD22.v:45 tfib_rd0_dir (relocated here as lib/Reusable/YD22.v) and
   YD1z.v:479 tfib_rd0_file (origin/ossv/recipes c8557374ad2; this unit's copy was deleted with the dead donor driver
   chain, 5394a607a7b). Lane CwRd0 (a Theorem Labs lane). Nothing in this file is a proof of a function (rule 24: the driver layer
   of a port).
   Changes from the donor, the same in every step: cgif's AR -> a8's ARcf at the ghost head set [] (lib/Reusable/
   YG0ncf.v); cgif's AR_laws -> a8's AR_laws_cf, proved (AR_laws_ok_cf, lib/Reusable/YG0lawscf.v), so it is a local
   definition, not a premise; the read-loop lemmas of YD24.v / YD25.v that mention AR -> lane CwRunqA's ARcf ports
   (lib/AU/PresetRdcfB.v: add_rt_cf, rd_dir_cf, ...), cited, never ported again; cgif's AR_after_run -> lane CwLoopB's
   AR_after_run_cf (lib/AU/PresetD1rBx.v); the AR-free lemmas of YD21.v / YD22.v / YD24.v / YD25.v / YD26.v (eagree,
   winP, rd_to_RW, reabs_RD, runs_at_frame, img_sub_DIR, the argv facts, ...) are cited from those files; cgif's
   event bound (`st_nev S <= 1`, the leaf's `st_nev S < EV_MAX`) is dropped (the cf instance has no event cap).
   STATUS: cb type-check on BASE f65cfdd5cac0 (FACTS 0b89c6c1bd) on the real core: the earlier core red (YD21.v:78 /
   YD2h.v:60 at a working branch a55b9c4d59d) is fixed by 069801ecd4b (generated YD2j roster + agreed DRV_IVS), merged here
   through a working branch 2e3fab42f5b. The kit of record a3bdeca3920 (reached only through lib/AU/PresetCfnB.v).
   A18 (lane CountDrvB, 2026-10-30): tfib_rd0_file_at_cf takes PresetDrvSecsA.drv_secs_cf S 65536 (the statement's new
   premise) into drv_minv_cf's last conjunct at cap = 65536; the read loop carries drv_minv_cf whole, and the grow
   arm keeps the conjunct (PresetPinvB23Pf.v gr_grow_cf, by lane CountDrvA's drv_secs_grow). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YL0a YL0b YL09 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t YD1y YD20.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD1v YD26 YD24 YD21 YD25 YD23 YD22.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE2k YD1u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB PresetD1preB PresetD1rBx PresetRdcfB PresetD2runB PresetPinvBcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvSecsA.
(* the memnorm tools: the runner twins (Imported for their tactics), the segment twins and the memnorm laws *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC80x YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0oInv.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YD2mnSeg.
(* Lane CwPinvA's PINV toolkit proofs and its grow-arm proofs, Required, written qualified (they Import PresetCfnB,
   whose names would shadow the driver's). *)
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetPinvBPf.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetPinvB23Pf.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PPf := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetPinvBPf.
Module P23 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetPinvB23Pf.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.
(* No sink instance may be inferred here (the image has none of its own in lib/Reusable; PresetCfnB.v:88-89 removes both
   globally, repeated locally after this file's imports). *)
#[local] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YE2k.tfib_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. RDD: YD22.v:45 tfib_rd0_dir, over ARcf. The directory arm reads once (EISDIR) and goes to the read-error leaf;
      no allocator call, so the leaf state's room (iface_room_np S), its qtight and its xs_placed_cf are not used. *)
Theorem tfib_rd0_dir_cf_B_holds : tfib_rd0_dir_cf_B.
Proof.
intros fx rc LS ci cp B NP HB RDERR.
pose (ARL := AR_laws_ok_cf tfibsegs B).
intros sp inp xw xd ws W ms md ly S a0 p pb Hargv Hsp Hva Hve Hfit Hdot HS HR HAI HAR _ _ HTOP Hbl _ Hpb Hfs Hfds.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
set (EL := YP08.E0 sp [a0; p] (in_envp inp) xw xd) in *.
set (E1 := havoc EL K_M1 ws) in *.
assert (HE1 : eagree sp inp xw xd a0 p E1) by (subst E1 EL; split; [intros k Hk; apply ew_havoc_old; exact Hk | reflexivity]).
pose proof (eagree_0 sp inp xw xd a0 p E1 HE1) as E1_0.
pose proof (add_rt_cf B HB sp inp xw xd a0 p Hsp E1 ss_rd0 W ms ly S md HE1 HS HAR (proj1 rd0_ext)) as HS'.
rewrite (proj1 with_rt_eqs) in HS'.
pose proof (reabs_RD EL E1 ss_rd0_rt ms (w_H W) (proj1 HE1) (proj2 HE1) HS' (proj1 (proj2 (proj2 (proj2 mem_RD_rt)))) (proj1 reabs_chk_RD)
ltac:(rewrite (proj1 mem_RD_rt); apply submem_refl)) as HSR.
cbn [ms_regs restrict] in HSR.
set (ER := E_RD EL (ms_regs ms)) in *.
pose proof ss_rd0_regs as (Q9 & Q19 & Q21 & _).
assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 0) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ss_rd0 ms 19%bv HS), Q19; reflexivity).
assert (R21 : getr (ms_regs ms) 21%bv = Z_to_bv 64 65536) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ss_rd0 ms 21%bv HS), Q21; reflexivity).
assert (A58 : ew ER A_LEN = Z_to_bv 64 0) by (subst ER; unfold A_LEN; change 58%nat with (K_M1 + 16)%nat; rewrite (E_RD_new EL _ 16) by (cbn; lia); exact R19).
assert (A59 : ew ER A_CAP = Z_to_bv 64 65536) by (subst ER; unfold A_CAP; change 59%nat with (K_M1 + 17)%nat; rewrite (E_RD_new EL _ 17) by (cbn; lia); exact R21).
specialize (HSR ltac:(unfold afact_ok, fact_len, fact_cap; cbn [af_lo af_hi af_al2]; rewrite A58, A59, !u64_lit by lia; repeat split; first [lia | rewrite Z.mod_1_r; reflexivity | change (2 ^ 16) with 65536; reflexivity])).
assert (HER : eagree sp inp xw xd a0 p ER) by (subst ER; split; [intros k Hk; apply E_RD_old; exact Hk | reflexivity]).
pose proof (eagree_0 sp inp xw xd a0 p ER HER) as ER0.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _
(rd_to_RW sp inp xw xd a0 p ER W ms md 0 65536 HER HSR ltac:(rewrite A58; apply u64_lit; lia) ltac:(rewrite A59; apply u64_lit; lia) ltac:(lia) ltac:(lia)) HAI).
intros W0 c0 _ HAI0 (-> & ms0 & mat0 & -> & HS0 & HF0 & HFr0). cbn [cfg_model] in HAI0.
rewrite Z.min_r in HS0 by lia.
set (E2 := ewset ER A_WANT (Z_to_bv 64 65536)) in *. set (md0 := with_vm_backing (m_vm_lazy md) mat0 md) in *.
assert (HE2 : eagree sp inp xw xd a0 p E2) by (subst E2; apply eagree_ewset; [exact HER | unfold A_WANT, K_M1; lia]).
pose proof (eagree_0 sp inp xw xd a0 p E2 HE2) as E2_0.
assert (HAR0 : ARcf tfibsegs B ly S [] W (ms_mem ms0) md0).
{ apply (AR_after_run_cf B HB ARL ly S [] W ER LH_mem (ms_mem ms) (ms_mem ms0) md mat0 HAR (proj1 win_ok_iter)); [rewrite ER0; exact Ulo | rewrite ER0; exact HCT | exact HF0 |].
rewrite ER0. intros a Ha. apply (apresent_some' (w_H W)). apply (winP sp Hsp E2 S_RW ms0 W (or_introl HS0) E2_0); [| exact Ha]. do 3 eexists; reflexivity. }
assert (HR0 : runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms0)) (runs_main_tfa true sp [a0; p] (in_envp inp))).
{ eapply (runs_at_frame ER RD_facts LH_mem); [exact (st_ok_facts_ok tfibsegs ER S_RD _ HSR) | exact (proj1 (proj2 wbs_iter2)) | exact HFr0 | rewrite ER0; lia | exact HR]. }
apply (SRr_srealizes tfibsegs W (mkCfg ms0 md0) _ _
(rd_dir_cf B HB sp inp xw xd a0 p Hsp E2 W ms0 md0 ly S 65536 HE2 HS0 ltac:(subst E2; rewrite ew_ewset_same; apply u64_lit; lia)
ltac:(lia) HAR0 HTOP ltac:(subst md0; rewrite wvb_fds'; exact Hfds)) HAI0).
intros W' c' _ HAI' (-> & ms' & md' & -> & HS2 & HAI2 & HAR2 & Hfds2 & Hfs2 & HF & HFr). cbn [cfg_model] in HAI'.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 S_DIR ms' HS2 eq_refl) as Hshape. rewrite Hshape.
(* ADDRESS 0x42e40: the read-error leaf's entry pc exactly as lane CwPreA states it (PresetD1preB.v:225, rderr_leaf_tfa_cf);
   the `change` checks it by conversion against the core's generated state S_DIR. PROVISIONAL with that statement. *)
change (Z_to_bv 64 (ss_pc S_DIR)) with (w64 YImgCellsB.B_WRAP_FPRINTF_PC).
pose proof (st_ok_mem_ok tfibsegs E2 S_DIR _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (HR2 : runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms')) (runs_main_tfa true sp [a0; p] (in_envp inp))).
{ eapply (runs_at_frame E2 (ss_facts S_DIR) LH_mem); [exact (st_ok_facts_ok tfibsegs E2 S_DIR _ HS2) | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 wbs_iter)))))) | exact HFr | rewrite E2_0; lia | exact HR0]. }
pose proof (runs_at_nth _ _ _ 2 _ _ HR2 eq_refl) as HBr. cbn [nth] in HBr.
pose proof (runs_at_bounds _ _ _ 2 _ _ HR2 eq_refl) as HBb. cbn [nth fst snd] in HBb. rewrite length_app in HBb. cbn [length] in HBb.
subst md0. rewrite ?wvb_fs in Hfs2. rewrite ?Hfs in Hfs2.
apply (RDERR E2 W (ms_regs ms') (ms_mem ms') md' ly S (bv_unsigned sp) p (z_argv (bv_unsigned sp) [a0; p] (in_envp inp) 1) (in_fs inp)).
- exact E2_0.
- lia.
- exact U16.
- exact (tid_of_st_ok E2 S_DIR _ HS2 ltac:(vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 10%bv HS2); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 11%bv HS2); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 12%bv HS2). pose proof S_DIR_facts as (_ & _ & _ & D12 & _). rewrite D12. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (proj1 HE2 2%nat) by (unfold K_M1; lia). subst EL. rewrite (YP08.ew2' sp [a0; p] (in_envp inp) Hsp Hva Hve) by (cbn; lia). reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 1%bv HS2); reflexivity.
- unfold spZ. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 2%bv HS2). pose proof S_DIR_facts as (_ & _ & _ & _ & _ & D2 & _). rewrite D2. cbn [sv_denot]. rewrite E2_0. apply u64_lit. unfold sp_window_lo in Ulo; lia.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 3%bv HS2); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 4%bv HS2); reflexivity.
- lia.
- pose proof (argv_str_fits' sp [a0; p] (in_envp inp) 1 Hfit ltac:(cbn; lia)) as Z1. cbn [nth] in Z1. exact Z1.
- exact (argv_no_nul [a0; p] Hva 1 ltac:(cbn; lia)).
- exact (argv_str_len [a0; p] Hva 1 ltac:(cbn; lia)).
- exact HBr.
- pose proof (argv_over_read sp (StackLayout.mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)) [a0; p] (in_envp inp) true _ 1 Hsp ltac:(cbn; lia) HR2) as OR1. cbn [nth] in OR1. exact OR1.
- exact (mem_ok_sub tfibsegs E2 _ _ IMG_REGIONS img_sub_DIR ltac:(reflexivity) HM2).
- intros a Ha. apply (winP sp Hsp E2 S_DIR ms' W (or_introl HS2) E2_0); [| exact Ha]. do 3 eexists; reflexivity.
- exact HAI2.
- exact HAR2.
- exact HTOP.
- rewrite Hfds2. rewrite wvb_fds'. rewrite Hfds. reflexivity.
- rewrite Hfs2. rewrite wvb_fs'. exact Hfs.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. RDF: YD1z.v:479 tfib_rd0_file, over ARcf. The read loop (donor YD1z.v:121-476): each round reads into the read
      state, checks it (RCHK), copies it into the buffer (MCPY); a full buffer either is refused at 2 ^ 26 (CwPinvA's
      gr_refused_cf_B) or grows (CwPinvB's gr_grow_cf_B: a malloc of 2 * cap, the copy, the free of the old buffer);
      end of file goes to the header leaf (HDR). Changes beyond the header's: every loop state carries the
      non-primary room NP S and xs_placed_cf ly S in place of the event bound `st_nev S + 2 * f <= 64`; the grow arm
      takes them over from gr_grow_cf_A's continuation (NP S', xs_placed_cf ly' S'); drv_minv -> CwSites'
      drv_minv_cf; FINV -> PCB.PINV at the start-up ledger (0 0), kept by CwPinvA's PINV toolkit (PresetPinvBPf.v
      finv_run_pinv_B_holds, finv_img_write_pinv_B_holds, finv_icpt_pinv_B_holds). The AR-free helpers below
      (pow2_mod_65536 .. blk_kept) are the donor's text (YD1z.v:20-39, :63-120), whose file this unit no longer has. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pow2_mod_65536 : forall cap e, 0 <= e -> cap = 2 ^ e -> 65536 <= cap -> cap mod 65536 = 0.
Proof.
intros cap e He -> Hge.
assert (16 <= e) by (destruct (Z.lt_ge_cases e 16) as [Hlt|]; [| lia]; exfalso; pose proof (Z.pow_lt_mono_r 2 e 16 ltac:(lia) ltac:(lia) Hlt); change (2 ^ 16) with 65536 in *; lia).
replace e with ((e - 16) + 16) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 16) with 65536. apply Z_mod_mult.
Qed.
Lemma file_read_slice : forall data len want j,
0 <= len -> 0 <= want ->
(j < length (file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)))%nat ->
len < 2 ^ 64 -> want < 2 ^ 64 ->
nth_error (file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)) j = nth_error data (Z.to_nat len + j)%nat.
Proof.
intros data len want j Hl Hw Hj Hl64 Hw64. rewrite file_read_unguarded in *. rewrite length_firstn in Hj.
rewrite nth_error_firstn. destruct (Nat.ltb_spec j (word_to_nat (Z_to_bv 64 want))); [|lia].
rewrite nth_error_skipn. unfold word_to_nat. rewrite u64_lit by lia. reflexivity.
Qed.
Lemma S_T_regs : sr_get (ss_regs S_T) 19%bv = sv_len1 /\ sr_get (ss_regs S_T) 21%bv = SOff A_CAP 0 /\ ss_pc S_T = TPC
/\ sr_get (ss_regs S_RDn) 9%bv = SOff A_BUF 0 /\ sr_get (ss_regs S_RDn) 19%bv = sv_len1 /\ sr_get (ss_regs S_RDn) 21%bv = SOff A_CAP 0
/\ ss_atoms_lt 78 S_HDR = true /\ facts_atoms_lt 60 RD_facts = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Section rf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
Variable NP : astate -> Prop.
Variable NR : ProcInput -> Prop.
Hypothesis HNPS : PCB.iface_room_np_step (cp := cp) NP.
Hypothesis HNPT : PCB.iface_room_np_tail (cp := cp) NP.
Hypothesis HMAX : 2 ^ 26 < @cf_malloc_max cp.
Hypothesis MSITE : malloc_site_tfa_cf B NP.
Hypothesis RCHK : read_check_tfa_cf B.
Hypothesis MCPY : memcpy_site_tfa_cf B.
Hypothesis FREE : free_site_cf B NP.
Hypothesis REFUSED : refused_leaf_tfa_cf B.
Hypothesis HDR : hdr_tfa_cf (LS := LS) B NP NR.
(* The grow arm's two cases, lane CwPinvA's statements (lib/AU/PresetPinvBcf.v:81-125, a working branch
   f50b650085f0), proved there (PresetPinvB23Pf.v:631 / :638); the closed result below cites the proofs. *)
Hypothesis GRR : gr_refused_cf_B.
Hypothesis GRG : gr_grow_cf_B.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
Hypothesis HNR : NR inp.
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
#[local] Notation eagree := (YD25.eagree sp inp xw xd a0 p).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Fixpoint canon_from (E : YP0m.env) (s k : nat) : list word :=
match k with O => [] | S k' => ew E s :: canon_from E (S s) k' end.
Definition canon (E : YP0m.env) (k : nat) : list word := canon_from E K_M1 k.
Lemma canon_from_length : forall E s k, length (canon_from E s k) = k.
Proof. intros E s k. revert s. induction k as [|k IH]; intros s; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma canon_from_nth : forall E k s i d, (i < k)%nat -> nth i (canon_from E s k) d = ew E (s + i)%nat.
Proof.
intros E k. induction k as [|k IH]; intros s i d Hi; [lia|]. cbn. destruct i as [|i].
- rewrite Nat.add_0_r. reflexivity.
- rewrite IH by lia. rewrite Nat.add_succ_r. reflexivity.
Qed.
Lemma canon_agree : forall E k, eagree E -> env_agree (K_M1 + k) E (havoc EL K_M1 (canon E k)).
Proof.
intros E k [HE HD]. split; [| unfold havoc; cbn; symmetry; exact HD].
intros n Hn. destruct (Nat.lt_ge_cases n K_M1) as [Hl|Hge].
- rewrite ew_havoc_old by exact Hl. symmetry. exact (HE n Hl).
- replace n with (K_M1 + (n - K_M1))%nat by lia.
rewrite (ew_havoc_new EL K_M1 (canon E k) (n - K_M1) (ew E K_M1)) by (unfold canon; rewrite canon_from_length; lia).
unfold canon. rewrite canon_from_nth by lia. reflexivity.
Qed.
Lemma rs_off_wrange : forall E rs x, forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp -> RS_LO <= x < RS_HI -> ~ in_wrange E rs x.
Proof.
intros E rs x Hok E0 Hx Hw. pose proof Hsp as (Ulo & _). unfold sp_window_lo in Ulo. unfold RS_LO, RS_HI in Hx.
apply (in_wrange_drv E rs x Hok) in Hw. rewrite E0 in Hw. destruct Hw as [Hw|Hw]; [lia|]. apply DRVW_cases in Hw. lia.
Qed.
Lemma rs_slice_frame : forall E rs (m m' : word -> option byte) bs n,
frame_of E rs m m' -> forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp -> 0 <= n -> RS_LO + n <= RS_HI ->
(forall i, 0 <= i < n -> m (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)) ->
(forall i, 0 <= i < n -> m' (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)).
Proof.
intros E rs m m' bs n HF Hok E0 Hn Hle Hb i Hi. rewrite <- (Hb i Hi). apply HF.
rewrite u64_lit by (unfold RS_LO, RS_HI in *; lia). apply (rs_off_wrange E rs); [exact Hok | exact E0 | lia].
Qed.
Lemma rs_slice_kept : forall (W : world tfibsegs) (m m' : word -> option byte) bs n lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) -> RS_HI <= lo \/ hi <= RS_LO ->
Z.of_nat (length bs) = n -> RS_LO + n <= RS_HI ->
(forall i, 0 <= i < n -> m (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)) ->
(forall i, 0 <= i < n -> m' (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)).
Proof.
intros W m m' bs n lo hi Hfr Hpres Hoff Hlen Hle Hb i Hi.
pose proof (Hb i Hi) as X. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:En; [| apply nth_error_None in En; lia].
pose proof (seg_win_visible W RS_LO 65536 (RS_LO + i) (proj2 rs_win_check) ltac:(lia) ltac:(unfold RS_LO; lia) ltac:(unfold RS_LO; lia)
ltac:(unfold RS_LO, RS_HI in *; lia)) as Eh.
pose proof (Hfr (RS_LO + i) ltac:(unfold RS_LO, RS_HI in *; lia) ltac:(lia)) as A.
unfold aview, mbyte, mrestrict in A. rewrite Eh, X in A. cbn in A.
destruct (Hpres (RS_LO + i) ltac:(split; [exact Eh | exists b; exact X])) as [_ [b' Hb']]. rewrite Hb' in A |- *. cbn in A.
injection A as A. f_equal. apply bv_eq. exact A.
Qed.
Lemma blk_kept : forall (H : word -> bool) (m m' : word -> option byte) buf len data lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
(forall a, buf <= a < buf + len -> ~ in_img tfibsegs a) -> 0 <= buf -> buf + len <= 2 ^ 64 -> (buf + len <= lo \/ hi <= buf) ->
blk H m buf len data -> blk H m' buf len data.
Proof.
intros H m m' buf len data lo hi Hfr Hni Hb0 Hbh Hoff HBk i Hi. rewrite <- (HBk i Hi).
apply (restrict_of_aview H m m' (buf + i)); [lia | apply Hni; lia |]. apply Hfr; lia.
Qed.
Lemma loop_seg_cf : forall (m : nat) (K : TSet) E (W : world tfibsegs) ms md ly S data (pb : sptr) (buf len cap : Z),
(Z.to_nat (cap - len) <= m)%nat ->
eagree E -> st_ok tfibsegs E S_RD (restrict (w_H W) ms) ->
bv_unsigned (ew E A_BUF) = buf -> bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md -> AI tfibsegs (w_H W) (w_A W) md -> top_ok usp ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = buf -> pb <> PNull -> NP S -> xs_placed_cf ly S -> drv_minv_cf B S cap (dlen data) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
blk (w_H W) (ms_mem ms) buf len data ->
0 <= len < cap -> len <= dlen data -> 65536 <= cap <= 2 ^ 26 -> (exists e, 0 <= e /\ cap = 2 ^ e) ->
PCB.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
fs_lookup (in_fs inp) p = Some data -> m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 len)) ->
(cap < 2 ^ 26 -> cap <= dlen data ->
forall (W' : world tfibsegs) ms' md' ly' S' (pb' : sptr),
let ER' := E_RD EL (ms_regs ms') in
st_ok tfibsegs ER' S_RD (restrict (w_H W') ms') ->
bv_unsigned (ew ER' A_BUF) = sptr_addr B ly' pb' -> bv_unsigned (ew ER' A_LEN) = cap -> bv_unsigned (ew ER' A_CAP) = 2 * cap ->
ARcf tfibsegs B ly' S' [] W' (ms_mem ms') md' -> AI tfibsegs (w_H W') (w_A W') md' -> top_ok usp ly' ->
blocks S' = [(pb', 2 * cap)] -> pb' <> PNull -> NP S' -> xs_placed_cf ly' S' -> drv_minv_cf B S' (2 * cap) (dlen data) ->
runs_at usp (mrestrict (w_H W') (ms_mem ms')) (runs_main_tfa true sp [a0; p] envp) ->
blk (w_H W') (ms_mem ms') (sptr_addr B ly' pb') cap data ->
PCB.PINV (aview tfibsegs (w_H W') (ms_mem ms')) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms') ->
YGcallStackUp.astack_up_x tfibsegs ly' W' usp (ms_mem ms') ->
m_fds md' = APSG.fds3 (FdFile p (Z_to_bv 64 cap)) -> m_fs md' = in_fs inp ->
srealizes tfibsegs (mkCfg ms' md') K) ->
srealizes tfibsegs (mkCfg ms md)
(if dlen data <? cap then POSTX (LS := LS) data (in_fs inp)
else if MAX_INPUT <=? cap then diag msg_refused (in_fs inp) else K).
Proof.
induction m as [|m IH]; intros K E W ms md ly S data pb buf len cap Hm HE HS E46 E58 E59 HAR HAI HTOP Hbl Hpb Hnn HNP HXS Hminv HR HBLK Hlen Hdl Hcap Hpow HFI HMN HUP Hlk Hfs Hfds CONT;
[lia|].
pose proof (YSRrMemnorm.srr_inv_laws_memnorm_k tfibsegs) as PLAW.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (eagree_0 _ _ _ _ _ _ E HE) as E0'. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl, <- Hpb; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W (ms_mem ms) md buf cap HAR Hin) as (Hbufm & Hb4096 & Hbce & Happ & _).
assert (Hcapr : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : buf <= a < buf + req_size cap) by lia.
exact (proj2 (alc_client_img _ _ ARL ly S [] W (ms_mem ms) md a HAR (or_introl (ex_intro _ buf (ex_intro _ cap (conj Hin Ha')))))). }
assert (Hcapm : cap mod 65536 = 0) by (destruct Hpow as (e & He & Hce); exact (pow2_mod_65536 cap e He Hce ltac:(lia))).
assert (FRD : facts_ok E RD_facts) by exact (st_ok_facts_ok tfibsegs E S_RD _ HS).
pose proof win_ok_iter as (WOK & WOKre & WOKchk & WOKcp & WOKcl).
unfold dlen in *.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _
(YD2mnSeg.rd_to_RW_mn _ PLAW sp inp xw xd a0 p E W ms md len cap HE HS E58 E59 ltac:(lia) ltac:(lia) HMN) HAI).
intros W0 c0 _ HAI0 [(-> & ms0 & mat0 & -> & HS0 & HF0 & HFr0) (ms0' & md0' & Ec0 & HMN0)]. cbn [cfg_model] in HAI0.
injection Ec0 as <- <-.
(* #102 (lane StackDrv): the live stack above usp across rd_to_RW (its frame is below usp) *)
assert (HUP0 : YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms0))
by exact (PresetStkUpB.stk_up_frame E LH_mem ly W (ms_mem ms) (ms_mem ms0) usp WOK E0' ltac:(lia) HTOP HF0 HUP).
set (want := Z.min (cap - len) 65536) in *. set (E1 := ewset E A_WANT (Z_to_bv 64 want)) in *.
set (md0 := with_vm_backing (m_vm_lazy md) mat0 md) in *.
assert (Hwant : 1 <= want <= 65536) by (subst want; lia).
assert (HE1 : eagree E1) by (subst E1; apply eagree_ewset; [exact HE | unfold A_WANT, K_M1; lia]).
pose proof (eagree_0 _ _ _ _ _ _ E1 HE1) as E1_0.
assert (E1old : forall n, (n < A_WANT)%nat -> ew E1 n = ew E n) by (intros n Hn; subst E1; apply ew_ewset_other; lia).
assert (E1_77 : bv_unsigned (ew E1 A_WANT) = want) by (subst E1; rewrite ew_ewset_same; apply u64_lit; lia).
assert (E1_46 : bv_unsigned (ew E1 A_BUF) = buf) by (rewrite E1old by (unfold A_BUF, A_WANT; lia); exact E46).
assert (E1_58 : bv_unsigned (ew E1 A_LEN) = len) by (rewrite E1old by (unfold A_LEN, A_WANT; lia); exact E58).
assert (E1_59 : bv_unsigned (ew E1 A_CAP) = cap) by (rewrite E1old by (unfold A_CAP, A_WANT; lia); exact E59).
assert (FRD1 : facts_ok E1 RD_facts).
{ apply (facts_ok_agree 60 E E1 RD_facts); [| exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_T_regs))))))) | exact FRD].
split; [| reflexivity]. intros k Hk. apply E1old. unfold A_WANT. lia. }
assert (HAR0 : ARcf tfibsegs B ly S [] W (ms_mem ms0) md0).
{ apply (AR_after_run_cf B HB ARL ly S [] W E LH_mem (ms_mem ms) (ms_mem ms0) md mat0 HAR WOK); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF0 |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP sp Hsp E1 S_RW ms0 W (or_introl HS0) E1_0); [| exact Ha].
do 3 eexists; reflexivity. }
assert (HR0 : runs_at usp (mrestrict (w_H W) (ms_mem ms0)) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame E RD_facts LH_mem); [exact FRD | exact (proj1 (proj2 wbs_iter2)) | exact HFr0 | rewrite E0'; lia | exact HR]. }
assert (HBLK0 : blk (w_H W) (ms_mem ms0) buf len data).
{ apply (blk_of_frame_r _ _ _ _ _ buf len data usp HFr0 WOK E0' Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK]. }
assert (Hfds0 : m_fds md0 = APSG.fds3 (FdFile p (Z_to_bv 64 len))) by (subst md0; rewrite wvb_fds'; exact Hfds).
assert (Hfs0 : m_fs md0 = in_fs inp) by (subst md0; rewrite wvb_fs'; exact Hfs).
assert (HFI0 : PCB.PINV (aview tfibsegs (w_H W) (ms_mem ms0)) 0 0) by exact (PPf.finv_run_pinv_B_holds (w_H W) E LH_mem _ _ usp 0 0 HFr0 WOK E0' Ulo HFI).
destruct (Z.eq_dec len (Z.of_nat (length data))) as [Heof | Hneof].
-
assert (Hltb : (Z.of_nat (length data) <? cap) = true) by (apply Z.ltb_lt; lia). rewrite Hltb.
apply (SRr_srealizes tfibsegs W (mkCfg ms0 md0) _ _
(rd_step_eof_cf B HB sp inp xw xd a0 p Hsp E1 W ms0 md0 ly S p data len cap want HE1 HS0 E1_58 E1_59 E1_77 HAR0 HTOP
ltac:(lia) Hwant Hfds0 ltac:(rewrite Hfs0; exact Hlk) Heof HMN0) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & md1 & -> & HS1 & HAI1' & HAR1 & Hstd & Hfs1 & HF1 & HFr1 & HMN1). cbn [cfg_model] in HAI1.
pose proof S_T_regs as (_ & _ & _ & _ & _ & _ & AT78 & _).
pose proof (st_ok_agree tfibsegs 78 E1 (havoc EL K_M1 (canon E1 36)) S_HDR _ HS1 (canon_agree E1 36 HE1) AT78) as HS1'.
pose proof (canon_agree E1 36 HE1) as [AGw _].
apply (HDR sp inp xw xd (canon E1 36) W ms1 md1 ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs HNR Hlk ltac:(unfold dlen; lia) HS1').
+ eapply (runs_at_frame E1 RD_facts LH_mem); [exact FRD1 | exact (proj1 (proj2 wbs_iter2)) | exact HFr1 | rewrite E1_0; lia | exact HR0].
+ exact HAI1'.
+ exact HAR1.
+ exact HNP.
+ exact HXS.
+ exact HTOP.
+ exact Hbl.
+ rewrite (AGw A_BUF) by (unfold A_BUF, K_M1; lia). rewrite E1_46. exact Hpb.
+ rewrite (AGw A_LEN) by (unfold A_LEN, K_M1; lia). unfold dlen. rewrite E1_58. exact Heof.
+ lia.
+ exact Hminv.
+ apply (proj1 (blk_bytes_at (w_H W) (ms_mem ms1) (sptr_addr B ly pb) data)). rewrite Hpb, <- Heof.
apply (blk_of_frame_r _ _ _ _ _ buf len data usp HFr1 WOK E1_0 Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK0].
(* st_ok_agree (HS1') keeps the configuration, so memnorm is rd_step_eof_cf's *)
+ exact (PPf.finv_run_pinv_B_holds (w_H W) E1 LH_mem _ _ usp 0 0 HFr1 WOK E1_0 Ulo HFI0).
+ exact HMN1.
+ exact (PresetStkUpB.stk_up_frame E1 _ ly W (ms_mem ms0) (ms_mem ms1) usp WOK E1_0 ltac:(lia) HTOP HF1 HUP0).
+ rewrite Hfs1. exact Hfs0.
+ exact Hstd.
-
assert (Hdl' : len < Z.of_nat (length data)) by lia.
apply (SRr_srealizes tfibsegs W (mkCfg ms0 md0) _ _
(rd_step_pos_cf B HB sp inp xw xd a0 p Hsp E1 W ms0 md0 ly S p data len cap want HE1 HS0 E1_58 E1_59 E1_77 HAR0 HTOP
ltac:(lia) Hwant ltac:(subst want; lia) ltac:(lia) Hfds0 ltac:(rewrite Hfs0; exact Hlk) Hdl' HMN0) HAI0).
intros W1 c1 _ HAI1 [(mem0 & md1 & Hn & HAI1' & HAR1 & Hfds1 & Hfs1 & Hrs & Hout & HFa & HFra & -> & ms2 & mat2 & -> & HS2 & HFb & HFrb)
(ms2' & md2' & Ec2 & HMN2)].
injection Ec2 as <- <-.
cbn [cfg_model] in HAI1.
set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)) in *. set (n := Z.of_nat (length bs)) in *.
assert (Hndl : n <= Z.of_nat (length data) - len) by (subst n bs; rewrite file_read_length, !u64_lit by lia; lia).
set (E2 := ewset E1 A_N (Z_to_bv 64 n)) in *. set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
assert (HE2 : eagree E2) by (subst E2; apply eagree_ewset; [exact HE1 | unfold A_N, K_M1; lia]).
pose proof (eagree_0 _ _ _ _ _ _ E2 HE2) as E2_0.
assert (E2old : forall k, (k < A_N)%nat -> ew E2 k = ew E1 k) by (intros k Hk; subst E2; apply ew_ewset_other; lia).
assert (E2_78 : bv_unsigned (ew E2 A_N) = n) by (subst E2; rewrite ew_ewset_same; apply u64_lit; lia).
assert (E2_46 : bv_unsigned (ew E2 A_BUF) = buf) by (rewrite E2old by (unfold A_BUF, A_N; lia); exact E1_46).
assert (E2_58 : bv_unsigned (ew E2 A_LEN) = len) by (rewrite E2old by (unfold A_LEN, A_N; lia); exact E1_58).
assert (E2_59 : bv_unsigned (ew E2 A_CAP) = cap) by (rewrite E2old by (unfold A_CAP, A_N; lia); exact E1_59).
assert (HBLKa : blk (w_H W) mem0 buf len data).
{ apply (blk_of_frame_r _ _ _ _ _ buf len data usp HFra WOK E1_0 Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK0]. }
assert (HBLK1 : blk (w_H W) (wbytes mem0 (Z_to_bv 64 RS_LO) bs) buf len data).
{ intros i Hi. rewrite <- (HBLKa i Hi). unfold mrestrict. destruct (w_H W (Z_to_bv 64 (buf + i))); [reflexivity|]. apply Hout.
rewrite u64_lit by lia. destruct (Z.lt_ge_cases (buf + i) RS_LO); [left; lia | right].
destruct (Z.le_gt_cases (RS_LO + n) (buf + i)); [lia|]. exfalso. apply (NIMG (buf + i) ltac:(lia)). apply rs_in_img. unfold RS_LO, RS_HI in *. lia. }
pose proof (st_ok_mem_ok tfibsegs E2 S_CHK _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (Hwin2 : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms2) a).
{ apply (winP sp Hsp E2 S_CHK ms2 W (or_introl HS2) E2_0). do 3 eexists; reflexivity. }
assert (HAR2 : ARcf tfibsegs B ly S [] W (ms_mem ms2) md2).
{ apply (AR_after_run_cf B HB ARL ly S [] W E2 (ss_mem S_RE) _ (ms_mem ms2) md1 mat2 HAR1 WOKre); [rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HFb |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin2 a Ha)). }
assert (HBLK2 : blk (w_H W) (ms_mem ms2) buf len data).
{ apply (blk_of_frame_r _ _ _ _ _ buf len data usp HFrb WOKre E2_0 Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK1]. }
assert (Hrs2 : forall i, 0 <= i < n -> ms_mem ms2 (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)).
{ apply (rs_slice_frame E2 (ss_mem S_RE) _ _ bs n HFb WOKre E2_0); [lia | unfold RS_LO, RS_HI; lia | exact Hrs]. }
assert (HR2 : runs_at usp (mrestrict (w_H W) (ms_mem ms2)) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame E2 (ss_facts S_CHK) (ss_mem S_RE)); [exact (st_ok_facts_ok tfibsegs E2 S_CHK _ HS2) | exact (proj1 (proj2 wbs_iter)) | exact HFrb | rewrite E2_0; lia |].
apply (runs_at_of_aview (w_H W) (w_H W) mem0 _ usp); [| exact Ulo |].
{ intros a Ha. unfold aview, mbyte, mrestrict. rewrite (Hout (Z_to_bv 64 a)) by (rewrite u64_lit by lia; right; unfold RS_LO, RS_HI, sp_window_lo in *; lia). reflexivity. }
eapply (runs_at_frame E1 (ss_facts S_RW) LH_mem); [exact (st_ok_facts_ok tfibsegs E1 S_RW _ HS0) | exact (proj1 wbs_iter2) | exact HFra | rewrite E1_0; lia | exact HR0]. }
(* #102 (lane StackDrv): the live stack above usp across the read (its run frames and its write into the read state
   below the image top) *)
assert (HUP2 : YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms2)).
{ apply (PresetStkUpB.stk_up_frame E2 (ss_mem S_RE) ly W _ (ms_mem ms2) usp WOKre E2_0 ltac:(lia) HTOP HFb).
  pose proof (PresetStkUpB.stk_up_frame E1 _ ly W (ms_mem ms0) mem0 usp WOK E1_0 ltac:(lia) HTOP HFa HUP0) as HUPa.
  pose proof HTOP as ((_ & T2) & _).
  intros a Ha. destruct (HUPa a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
  rewrite (Hout (Z_to_bv 64 a)) by (rewrite u64_lit by (unfold sp_window_lo, sp_window_hi in *; lia); right; unfold RS_LO, RS_HI, sp_window_lo in *; lia).
  exact Hb. }
apply (SRr_srealizes tfibsegs W (mkCfg ms2 md2) _ _ (rd_chk_cf B HB sp inp xw xd a0 p Hsp E1 W ms2 md2 ly S n len cap RCHK HE1 HS2 HAR2 HTOP ltac:(lia) HMN2) HAI1).
intros W2 c2 _ HAI3 (-> & regs3 & mem3 & md3 & -> & HS3 & HAR3 & Hs3 & Hfr3 & Hpres3 & HMN3). cbn [cfg_model] in HAI3.
(* #102: the live stack across the read check (its presence keep) *)
assert (HUP3 : YGcallStackUp.astack_up_x tfibsegs ly W usp mem3)
by exact (PresetStkUpB.stk_up_keep ly ly W W (ms_mem ms2) mem3 usp eq_refl (fun a _ => Hpres3 a) HUP2).
set (E3 := havoc E2 K_CHK (map (getr regs3) CLOB_CHK)) in *.
assert (HE3 : eagree E3) by (subst E3; apply eagree_havoc; [exact HE2 | unfold K_CHK, K_M1; lia]).
pose proof (eagree_0 _ _ _ _ _ _ E3 HE3) as E3_0.
assert (E3old : forall k, (k < K_CHK)%nat -> ew E3 k = ew E2 k) by (intros k Hk; subst E3; apply ew_havoc_old; exact Hk).
assert (E3_78 : bv_unsigned (ew E3 A_N) = n) by (rewrite E3old by (unfold K_CHK, A_N; lia); exact E2_78).
assert (E3_46 : bv_unsigned (ew E3 A_BUF) = buf) by (rewrite E3old by (unfold A_BUF, K_CHK; lia); exact E2_46).
assert (E3_58 : bv_unsigned (ew E3 A_LEN) = len) by (rewrite E3old by (unfold A_LEN, K_CHK; lia); exact E2_58).
assert (E3_59 : bv_unsigned (ew E3 A_CAP) = cap) by (rewrite E3old by (unfold A_CAP, K_CHK; lia); exact E2_59).
pose proof (same_but_materialized_frame _ _ Hs3) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds3 & _ & _ & Hfs3 & _).
assert (HBLK3 : blk (w_H W) mem3 buf len data).
{ apply (blk_kept (w_H W) (ms_mem ms2) mem3 buf len data (usp + ICPT_SP - ESTACK) (usp + ICPT_SP) Hfr3); [intros a Ha; apply NIMG; lia | lia | lia | unfold ICPT_SP, ESTACK; lia | exact HBLK2]. }
assert (Hrs3 : forall i, 0 <= i < n -> mem3 (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)).
{ apply (rs_slice_kept W (ms_mem ms2) mem3 bs n (usp + ICPT_SP - ESTACK) (usp + ICPT_SP) Hfr3 Hpres3); [unfold RS_HI, ICPT_SP, ESTACK, sp_window_lo in *; lia | reflexivity | unfold RS_LO, RS_HI; lia | exact Hrs2]. }
assert (HR3 : runs_at usp (mrestrict (w_H W) mem3) (runs_main_tfa true sp [a0; p] envp)).
{ apply (runs_at_of_aview (w_H W) (w_H W) (ms_mem ms2) mem3 usp); [| exact Ulo | exact HR2]. intros a Ha. apply Hfr3; unfold ICPT_SP, ESTACK; lia. }
apply (SRr_srealizes tfibsegs W _ _ _ (YD2mnSeg.cp_run_mn _ PLAW E3 W regs3 mem3 md3 HS3 HMN3) HAI3).
intros W3 c3 _ HAI4 [(-> & ms4 & mat4 & -> & HS4 & HFc & HFrc) (ms4' & md4' & Ec4 & HMN4)]. cbn [cfg_model] in HAI4.
injection Ec4 as <- <-.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
(* #102: the live stack across cp_run *)
assert (HUP4 : YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms4))
by exact (PresetStkUpB.stk_up_frame E3 (ss_mem S_CHK') ly W mem3 (ms_mem ms4) usp WOKchk E3_0 ltac:(lia) HTOP HFc HUP3).
assert (Hwin4 : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms4) a).
{ apply (winP sp Hsp E3 S_CP ms4 W (or_introl HS4) E3_0). do 3 eexists; reflexivity. }
assert (HAR4 : ARcf tfibsegs B ly S [] W (ms_mem ms4) md4).
{ apply (AR_after_run_cf B HB ARL ly S [] W E3 (ss_mem S_CHK') mem3 (ms_mem ms4) md3 mat4 HAR3 WOKchk); [rewrite E3_0; exact Ulo | rewrite E3_0; exact HCT | exact HFc |].
rewrite E3_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin4 a Ha)). }
assert (HBLK4 : blk (w_H W) (ms_mem ms4) buf len data).
{ apply (blk_of_frame_r _ _ _ _ _ buf len data usp HFrc WOKchk E3_0 Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK3]. }
assert (Hrs4 : forall i, 0 <= i < n -> ms_mem ms4 (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)).
{ apply (rs_slice_frame E3 (ss_mem S_CHK') _ _ bs n HFc WOKchk E3_0); [lia | unfold RS_LO, RS_HI; lia | exact Hrs3]. }
assert (HR4 : runs_at usp (mrestrict (w_H W) (ms_mem ms4)) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame E3 (ss_facts S_CP) (ss_mem S_CHK')); [exact (st_ok_facts_ok tfibsegs E3 S_CP _ HS4) | exact (proj1 (proj2 (proj2 wbs_iter))) | exact HFrc | rewrite E3_0; lia | exact HR3]. }
apply (SRr_srealizes tfibsegs W (mkCfg ms4 md4) _ _
(rd_cpy_cf B HB sp inp xw xd a0 p Hsp Hva Hve E3 W ms4 md4 ly S pb n buf len cap data bs MCPY HE3 HS4 E3_46 E3_58 E3_78 HAR4 HTOP Hbl Hpb
ltac:(lia) ltac:(lia) ltac:(subst want; lia) ltac:(lia) HBLK4 eq_refl Hrs4
ltac:(intros j Hj; subst bs; apply file_read_slice; try lia; pose proof (u64_range (ew E A_LEN)); rewrite E58 in *; lia) HMN4) HAI4).
intros W4 c4 _ HAI5 (-> & regs5 & mem5 & md5 & -> & HS5 & HAR5 & Hs5 & HBLK5 & Hfr5 & Hpres5 & HMN5). cbn [cfg_model] in HAI5.
(* #102: the live stack across the memcpy (its presence keep) *)
assert (HUP5 : YGcallStackUp.astack_up_x tfibsegs ly W usp mem5)
by exact (PresetStkUpB.stk_up_keep ly ly W W (ms_mem ms4) mem5 usp eq_refl (fun a _ => Hpres5 a) HUP4).
set (E5 := havoc E3 K_CP (map (getr regs5) CLOB)) in *.
assert (HE5 : eagree E5) by (subst E5; apply eagree_havoc; [exact HE3 | unfold K_CP, K_M1; lia]).
pose proof (eagree_0 _ _ _ _ _ _ E5 HE5) as E5_0.
assert (E5old : forall k, (k < K_CP)%nat -> ew E5 k = ew E3 k) by (intros k Hk; subst E5; apply ew_havoc_old; exact Hk).
assert (E5_78 : bv_unsigned (ew E5 A_N) = n) by (rewrite E5old by (unfold K_CP, A_N; lia); exact E3_78).
assert (E5_46 : bv_unsigned (ew E5 A_BUF) = buf) by (rewrite E5old by (unfold A_BUF, K_CP; lia); exact E3_46).
assert (E5_58 : bv_unsigned (ew E5 A_LEN) = len) by (rewrite E5old by (unfold A_LEN, K_CP; lia); exact E3_58).
assert (E5_59 : bv_unsigned (ew E5 A_CAP) = cap) by (rewrite E5old by (unfold A_CAP, K_CP; lia); exact E3_59).
pose proof (same_but_materialized_frame _ _ Hs5) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds5 & _ & _ & Hfs5 & _).
assert (HR5 : runs_at usp (mrestrict (w_H W) mem5) (runs_main_tfa true sp [a0; p] envp)).
{ apply (runs_at_of_aview (w_H W) (w_H W) (ms_mem ms4) mem5 usp); [| exact Ulo | exact HR4]. intros a Ha. apply Hfr5; unfold ESTACK; lia. }
assert (Hwin5 : forall a, usp - 65536 <= a < usp - 128 -> apresent (w_H W) mem5 a) by (intros a Ha; apply Hpres5; apply Hwin4; lia).
assert (G5 : gvals E5 buf cap \/ len + n < cap).
{ destruct (Z.eq_dec (len + n) cap) as [Heq|Hne]; [left | right; subst want; lia].
unfold gvals. rewrite E5_46, E5_59, E5_58, E5_78. repeat split; lia. }
assert (Ulen1 : U E5 sv_len1 = len + n).
{ unfold sv_len1. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, E5_58, E5_78, !Z.add_0_r.
rewrite (zcanon_id len), (zcanon_id n) by (unfold M64; lia). apply zcanon_id. unfold M64; lia. }
clear HF0 HFr0.
pose proof HS5 as HS6. pose proof HWXi as HWX. pose proof HMN5 as HMNb.
eapply (SRr_srealizes tfibsegs W (mkCfg (mkst regs5 (Z_to_bv 64 RA_CP) mem5 (seg_rom tfibsegs)) md5)); [| exact HAI5 |].
{ srr_run_with_inv tfibtbl_lp_ok PLAW HS6 HMNb. srr_branch_with tfibtbl_lp_ok HS6.
-
rewrite branch_eq_U in Hc. change (SAlu ALU_ADD (SOff 58 0) (SOff 78 0)) with sv_len1 in Hc. change (SOff 59 0) with (SOff A_CAP 0) in Hc.
rewrite Ulen1, U_SOff, E5_59, Z.add_0_r, (zcanon_id cap) in Hc by (unfold M64; lia).
apply Z.eqb_eq in Hc.
srr_run_with_inv tfibtbl_lp_ok PLAW HS6 HMNb.
apply SRr_ret. instantiate (1 := fun W' c' => W' = W /\ exists ms' mat, c' = mkCfg ms' (with_vm_backing (m_vm_lazy md5) mat md5) /\
((len + n = cap /\ st_ok tfibsegs E5 S_G (restrict (w_H W) ms')) \/ (len + n < cap /\ st_ok tfibsegs E5 S_RDn (restrict (w_H W) ms')))
/\ frame_of E5 (ss_mem S_CPp) mem5 (ms_mem ms') /\ frame_of E5 (ss_mem S_CPp) (mrestrict (w_H W) mem5) (mrestrict (w_H W) (ms_mem ms'))
/\ YAkMemnorm.memnorm tfibsegs (ms_mem ms')).
split; [reflexivity|]. lazymatch type of HS6 with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [left; split; [exact Hc | exact HS6]|].
pose proof S_T_shape as (SKT & _).
split; [apply (frame_of_trans E5 _ _ _ _ _ eq_refl HF); rewrite <- SKT; exact HF0 | split; [apply (frame_of_trans E5 _ _ _ _ _ eq_refl HFr); rewrite <- SKT; exact HFr0 | exact HMNb]].
-
rewrite branch_eq_U in Hc. change (SAlu ALU_ADD (SOff 58 0) (SOff 78 0)) with sv_len1 in Hc. change (SOff 59 0) with (SOff A_CAP 0) in Hc.
rewrite Ulen1, U_SOff, E5_59, Z.add_0_r, (zcanon_id cap) in Hc by (unfold M64; lia).
apply Z.eqb_neq in Hc.
srr_run_to_with_inv tfibtbl_lp_ok PLAW HS6 HMNb RDPC.
apply SRr_ret. split; [reflexivity|]. lazymatch type of HS6 with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [right; split; [subst want; lia | exact HS6]|].
pose proof S_T_shape as (SKT & _).
split; [apply (frame_of_trans E5 _ _ _ _ _ eq_refl HF); rewrite <- SKT; exact HF0 | split; [apply (frame_of_trans E5 _ _ _ _ _ eq_refl HFr); rewrite <- SKT; exact HFr0 | exact HMNb]]. }
cbv beta. intros W5 c5 _ HAI6 (-> & ms6 & mat6 & -> & CASE & HF6 & HFr6 & HMN6). cbn [cfg_model] in HAI6.
set (md6 := with_vm_backing (m_vm_lazy md5) mat6 md5) in *.
(* #102: the live stack across the run to the buffer-full test *)
assert (HUP6 : YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms6))
by exact (PresetStkUpB.stk_up_frame E5 (ss_mem S_CPp) ly W mem5 (ms_mem ms6) usp WOKcp E5_0 ltac:(lia) HTOP HF6 HUP5).
assert (HAR6 : forall ss, (st_ok tfibsegs E5 ss (restrict (w_H W) ms6)) ->
(exists c1 c2 rest, ss_mem ss = YP09.mkRegion (Some 0%nat) (-65536) (-128) (-65536) (-128) c1 :: YP09.mkRegion (Some 0%nat) (-128) 0 (-128) 0 c2 :: rest) ->
ARcf tfibsegs B ly S [] W (ms_mem ms6) md6).
{ intros ss HSx Hshape. apply (AR_after_run_cf B HB ARL ly S [] W E5 (ss_mem S_CPp) mem5 (ms_mem ms6) md5 mat6 HAR5 WOKcp); [rewrite E5_0; exact Ulo | rewrite E5_0; exact HCT | exact HF6 |].
rewrite E5_0. intros a Ha. apply (apresent_some' (w_H W)). apply (winP sp Hsp E5 ss ms6 W (or_introl HSx) E5_0 Hshape). exact Ha. }
assert (HBLK6 : blk (w_H W) (ms_mem ms6) buf (len + n) data).
{ apply (blk_of_frame_r _ _ _ _ _ buf (len + n) data usp HFr6 WOKcp E5_0 Ulo); [intros a Ha; apply NIMG; subst want; lia | lia | subst want; lia | exact HBLK5]. }
assert (Hfds6 : m_fds md6 = APSG.fds3 (FdFile p (Z_to_bv 64 (len + n)))).
{ subst md6. rewrite wvb_fds', Hfds5. subst md4. rewrite wvb_fds', Hfds3. subst md2. rewrite wvb_fds'. exact Hfds1. }
assert (Hfs6 : m_fs md6 = in_fs inp).
{ subst md6. rewrite wvb_fs', Hfs5. subst md4. rewrite wvb_fs', Hfs3. subst md2. rewrite wvb_fs', Hfs1. exact Hfs0. }
assert (HFI6 : PCB.PINV (aview tfibsegs (w_H W) (ms_mem ms6)) 0 0).
{ assert (HFIa : PCB.PINV (aview tfibsegs (w_H W) mem0) 0 0) by exact (PPf.finv_run_pinv_B_holds (w_H W) E1 LH_mem _ _ usp 0 0 HFra WOK E1_0 Ulo HFI0).
assert (HFI1 : PCB.PINV (aview tfibsegs (w_H W) (wbytes mem0 (Z_to_bv 64 RS_LO) bs)) 0 0).
{ apply (PPf.finv_img_write_pinv_B_holds (w_H W) mem0 _ RS_LO (RS_LO + n) 0 0 Hout); [apply (PCB.pinv_ivs_avoid_sub RS_LO RS_HI); [vm_compute; reflexivity | lia | unfold RS_LO, RS_HI in *; lia] | exact HFIa]. }
assert (HFI2 : PCB.PINV (aview tfibsegs (w_H W) (ms_mem ms2)) 0 0) by exact (PPf.finv_run_pinv_B_holds (w_H W) E2 (ss_mem S_RE) _ _ usp 0 0 HFrb WOKre E2_0 Ulo HFI1).
assert (HFI3 : PCB.PINV (aview tfibsegs (w_H W) mem3) 0 0).
{ apply (PPf.finv_icpt_pinv_B_holds fx rc ci cp B HB ARL ly S [] W (ms_mem ms2) md2 mem3 (fun _ => False) (usp + ICPT_SP - ESTACK) (usp + ICPT_SP) usp 0 0 HAR2 HTOP Ulo Uhi); [| unfold ICPT_SP, ESTACK; lia | unfold ICPT_SP; lia | intros a [] | exact HFI2].
intros a Ha _ Hs. exact (Hfr3 a Ha Hs). }
assert (HFI4 : PCB.PINV (aview tfibsegs (w_H W) (ms_mem ms4)) 0 0) by exact (PPf.finv_run_pinv_B_holds (w_H W) E3 (ss_mem S_CHK') _ _ usp 0 0 HFrc WOKchk E3_0 Ulo HFI3).
assert (HFI5 : PCB.PINV (aview tfibsegs (w_H W) mem5) 0 0).
{ apply (PPf.finv_icpt_pinv_B_holds fx rc ci cp B HB ARL ly S [] W (ms_mem ms4) md4 mem5 (fun a => buf + len <= a < buf + len + n) (usp - 128 - ESTACK) (usp - 128) usp 0 0 HAR4 HTOP Ulo Uhi Hfr5); [unfold ESTACK; lia | lia | | exact HFI4].
intros a Ha. exists buf, cap. split; [exact Hin | subst want; lia]. }
exact (PPf.finv_run_pinv_B_holds (w_H W) E5 (ss_mem S_CPp) _ _ usp 0 0 HFr6 WOKcp E5_0 Ulo HFI5). }
destruct CASE as [[Hfull HSG] | [Hpart HSn]].
+
assert (Hge : cap <= Z.of_nat (length data)) by (subst want; lia).
assert (Hnlt : (Z.of_nat (length data) <? cap) = false) by (apply Z.ltb_ge; lia). rewrite Hnlt.
destruct G5 as [G5 | ?]; [| lia].
assert (HR6 : runs_at usp (mrestrict (w_H W) (ms_mem ms6)) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame E5 (ss_facts S_G) (ss_mem S_CPp)); [exact (st_ok_facts_ok tfibsegs E5 S_G _ HSG) | exact (proj2 (proj2 (proj2 (proj2 wbs_iter2)))) | exact HFr6 | rewrite E5_0; lia | exact HR5]. }
pose proof (HAR6 S_G HSG ltac:(do 3 eexists; reflexivity)) as HAR6'.
destruct (Z.eq_dec cap (2 ^ 26)) as [Hmax | Hsmall].
* assert (Hle : (MAX_INPUT <=? cap) = true) by (apply Z.leb_le; unfold MAX_INPUT; lia). rewrite Hle.
exact (GRR fx rc ci cp B HB REFUSED sp inp xw xd a0 p Hsp Hva Hve E5 W ms6 md6 ly S p pb buf cap HE5 HSG G5 HAR6' HAI6 HTOP Hbl Hpb
HR6 ltac:(rewrite <- Hfull; exact Hfds6) Hfs6 HFI6 Hmax).
* assert (Hnle : (MAX_INPUT <=? cap) = false) by (apply Z.leb_gt; unfold MAX_INPUT; lia). rewrite Hnle.
pose proof (CONT ltac:(lia) ltac:(lia)) as CONT'.
apply (GRG fx rc ci cp B NP HB HNPT HNPS HMAX MSITE MCPY FREE sp inp xw xd a0 p Hsp Hva Hve E5 W ms6 md6 ly S p data pb buf cap HE5 HSG G5 HAR6' HAI6 HTOP Hbl Hpb
HNP HXS HR6 ltac:(rewrite <- Hfull; exact Hfds6) Hfs6 HFI6 HMN6 HUP6 K ltac:(lia) Hpow Hcapm Hnn ltac:(rewrite <- Hfull; exact HBLK6) Hminv ltac:(unfold dlen; lia)).
exact CONT'.
+
assert (HR6 : runs_at usp (mrestrict (w_H W) (ms_mem ms6)) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame E5 (ss_facts S_RDn) (ss_mem S_CPp)); [exact (st_ok_facts_ok tfibsegs E5 S_RDn _ HSn) | exact (proj1 (proj2 (proj2 (proj2 wbs_iter2)))) | exact HFr6 | rewrite E5_0; lia | exact HR5]. }
pose proof (HAR6 S_RDn HSn ltac:(do 3 eexists; reflexivity)) as HAR6'.
(* add_rt_cf and reabs_RD rebuild st_ok only: ms6 and its memnorm HMN6 are kept for the IH *)
pose proof (add_rt_cf B HB sp inp xw xd a0 p Hsp E5 S_RDn W ms6 ly S md6 HE5 HSn HAR6' (proj1 (proj2 rd0_ext))) as HS7.
rewrite (proj1 (proj2 with_rt_eqs)) in HS7.
pose proof (reabs_RD EL E5 S_RDn_rt ms6 (w_H W) (proj1 HE5) (proj2 HE5) HS7
(proj1 (proj2 (proj2 (proj2 (proj2 mem_RD_rt))))) (proj1 (proj2 reabs_chk_RD))
ltac:(rewrite (proj1 (proj2 mem_RD_rt)); apply submem_refl)) as HSR.
cbn [ms_regs restrict] in HSR.
pose proof S_T_regs as (_ & _ & _ & N9 & N19 & N21 & _).
assert (X19 : getr (ms_regs ms6) 19%bv = w64 (len + n)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E5 S_RDn ms6 19%bv HSn), N19. apply (YD23.denot_of_U). exact Ulen1. }
assert (X21 : getr (ms_regs ms6) 21%bv = w64 cap).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E5 S_RDn ms6 21%bv HSn), N21. apply YD23.denot_of_U. rewrite U_SOff, E5_59, Z.add_0_r. apply zcanon_id. unfold M64; lia. }
assert (X9 : getr (ms_regs ms6) 9%bv = w64 buf).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E5 S_RDn ms6 9%bv HSn), N9. apply YD23.denot_of_U. rewrite U_SOff, E5_46, Z.add_0_r. apply zcanon_id. unfold M64; lia. }
assert (A46 : ew (E_RD EL (ms_regs ms6)) A_BUF = w64 buf) by (unfold A_BUF; change 46%nat with (K_M1 + 4)%nat; rewrite (E_RD_new EL (ms_regs ms6) 4) by (cbn; lia); exact X9).
assert (A58 : ew (E_RD EL (ms_regs ms6)) A_LEN = w64 (len + n)) by (unfold A_LEN; change 58%nat with (K_M1 + 16)%nat; rewrite (E_RD_new EL (ms_regs ms6) 16) by (cbn; lia); exact X19).
assert (A59 : ew (E_RD EL (ms_regs ms6)) A_CAP = w64 cap) by (unfold A_CAP; change 59%nat with (K_M1 + 17)%nat; rewrite (E_RD_new EL (ms_regs ms6) 17) by (cbn; lia); exact X21).
specialize (HSR ltac:(unfold afact_ok, fact_len, fact_cap; cbn [af_lo af_hi af_al2]; rewrite A58, A59; unfold w64; rewrite !u64_lit by lia;
repeat split; first [lia | rewrite Z.mod_1_r; reflexivity | change (2 ^ 16) with 65536; exact Hcapm])).
apply (IH K (E_RD EL (ms_regs ms6)) W ms6 md6 ly S data pb buf (len + n) cap); try assumption; try lia.
* split; [intros k Hk; apply E_RD_old; exact Hk | reflexivity].
* rewrite A46. apply u64_lit. lia.
* rewrite A58. apply u64_lit. lia.
* rewrite A59. apply u64_lit. lia.
Qed.
Lemma RPX_S_cf data fs f cap :
RPX (LS := LS) data fs (S f) cap = if dlen data <? cap then POSTX (LS := LS) data fs else if MAX_INPUT <=? cap then diag msg_refused fs else RPX (LS := LS) data fs f (2 * cap).
Proof. reflexivity. Qed.
Theorem loop_RP_cf : forall (f : nat) E (W : world tfibsegs) ms md ly Sa data (pb : sptr) (buf len cap : Z),
eagree E -> st_ok tfibsegs E S_RD (restrict (w_H W) ms) ->
bv_unsigned (ew E A_BUF) = buf -> bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap ->
ARcf tfibsegs B ly Sa [] W (ms_mem ms) md -> AI tfibsegs (w_H W) (w_A W) md -> top_ok usp ly ->
blocks Sa = [(pb, cap)] -> sptr_addr B ly pb = buf -> pb <> PNull -> NP Sa -> xs_placed_cf ly Sa -> drv_minv_cf B Sa cap (dlen data) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
blk (w_H W) (ms_mem ms) buf len data ->
0 <= len < cap -> len <= dlen data -> 65536 <= cap <= 2 ^ 26 -> (exists e, 0 <= e /\ cap = 2 ^ e) -> 2 ^ 26 <= cap * 2 ^ (Z.of_nat f) ->
PCB.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
fs_lookup (in_fs inp) p = Some data -> m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 len)) ->
srealizes tfibsegs (mkCfg ms md) (RPX (LS := LS) data (in_fs inp) (S f) cap).
Proof.
induction f as [|f IH]; intros E W ms md ly Sa data pb buf len cap HE HS E46 E58 E59 HAR HAI HTOP Hbl Hpb Hnn HNP HXS Hminv HR HBLK
Hlen Hdl Hcap Hpow Hfuel HFI HMN HUP Hlk Hfs Hfds; rewrite RPX_S_cf.
- apply (loop_seg_cf (Z.to_nat (cap - len)) _ E W ms md ly Sa data pb buf len cap (Nat.le_refl _) HE HS E46 E58 E59 HAR HAI HTOP Hbl Hpb Hnn HNP HXS Hminv HR HBLK Hlen Hdl Hcap Hpow HFI HMN HUP Hlk Hfs Hfds).
intros Hsmall _. exfalso. change (2 ^ Z.of_nat 0) with 1 in Hfuel. lia.
- apply (loop_seg_cf (Z.to_nat (cap - len)) _ E W ms md ly Sa data pb buf len cap (Nat.le_refl _) HE HS E46 E58 E59 HAR HAI HTOP Hbl Hpb Hnn HNP HXS Hminv HR HBLK Hlen Hdl Hcap Hpow HFI HMN HUP Hlk Hfs Hfds).
intros Hsmall Hge.
intros W' ms' md' ly' S' pb' ER' HS' X46 X58 X59 HAR' HAI' HTOP' Hbl' Hnn' HNP' HXS' Hminv' HR' HBLK' HFI' HMN' HUP' Hfds' Hfs'.
assert (Hcap2 : 2 * cap <= 2 ^ 26) by (destruct Hpow as (e & He & Hce); exact (pow2_double_le cap e He Hce Hsmall)).
apply (IH ER' W' ms' md' ly' S' data pb' (sptr_addr B ly' pb') cap (2 * cap)); try assumption; try lia.
+ split; [intros k Hk; subst ER'; apply E_RD_old; exact Hk | reflexivity].
+ destruct Hpow as (e & He & Hce). exists (e + 1). split; [lia|]. rewrite Z.pow_add_r by lia. lia.
+ rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia. lia.
Qed.
Theorem tfib_rd0_file_at_cf : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr),
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs (havoc EL K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> NP S ->
xs_placed_cf ly S -> top_ok usp ly ->
blocks S = [(pb, 65536)] -> pb <> PNull -> sptr_addr B ly pb = bv_unsigned (ew (havoc EL K_M1 ws) A_BUF) ->
frames S = [] -> qtight S -> prim_pristine_except S [kBatchClass] ->
drv_depot_fixed B S ->
PresetDrvSecsA.drv_secs_cf S 65536 ->
PCB.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
srealizes tfibsegs (mkCfg ms md) (RPX (LS := LS) data (in_fs inp) READ_FUEL CAP0).
Proof.
intros ws W ms md ly S data pb Hlenp Hne Hnd Hlk HS HR HAI HAR HNP HXS HTOP Hbl Hnn Hpb HF0 HT0 HP0 HD0 HDS0 HFI HMN HUP Hfs Hfds.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
set (E1 := havoc EL K_M1 ws) in *.
assert (HE1 : eagree E1) by (subst E1; split; [intros k Hk; apply ew_havoc_old; exact Hk | reflexivity]).
pose proof (add_rt_cf B HB sp inp xw xd a0 p Hsp E1 ss_rd0 W ms ly S md HE1 HS HAR (proj1 rd0_ext)) as HS'.
rewrite (proj1 with_rt_eqs) in HS'.
pose proof (reabs_RD EL E1 ss_rd0_rt ms (w_H W) (proj1 HE1) (proj2 HE1) HS' (proj1 (proj2 (proj2 (proj2 mem_RD_rt)))) (proj1 reabs_chk_RD)
ltac:(rewrite (proj1 mem_RD_rt); apply submem_refl)) as HSR.
cbn [ms_regs restrict] in HSR.
set (ER := E_RD EL (ms_regs ms)) in *.
pose proof ss_rd0_regs as (Q9 & Q19 & Q21 & _).
assert (R9 : getr (ms_regs ms) 9%bv = ew E1 A_BUF) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ss_rd0 ms 9%bv HS), Q9; cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 0) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ss_rd0 ms 19%bv HS), Q19; reflexivity).
assert (R21 : getr (ms_regs ms) 21%bv = Z_to_bv 64 65536) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ss_rd0 ms 21%bv HS), Q21; reflexivity).
assert (A46 : ew ER A_BUF = ew E1 A_BUF) by (subst ER; unfold A_BUF; change 46%nat with (K_M1 + 4)%nat; rewrite (E_RD_new EL _ 4) by (cbn; lia); exact R9).
assert (A58 : ew ER A_LEN = Z_to_bv 64 0) by (subst ER; unfold A_LEN; change 58%nat with (K_M1 + 16)%nat; rewrite (E_RD_new EL _ 16) by (cbn; lia); exact R19).
assert (A59 : ew ER A_CAP = Z_to_bv 64 65536) by (subst ER; unfold A_CAP; change 59%nat with (K_M1 + 17)%nat; rewrite (E_RD_new EL _ 17) by (cbn; lia); exact R21).
specialize (HSR ltac:(unfold afact_ok, fact_len, fact_cap; cbn [af_lo af_hi af_al2]; rewrite A58, A59, !u64_lit by lia; repeat split; first [lia | rewrite Z.mod_1_r; reflexivity | change (2 ^ 16) with 65536; reflexivity])).
unfold READ_FUEL, CAP0.
(* add_rt_cf and reabs_RD (HSR) keep the configuration, so memnorm of ms is HMN *)
apply (loop_RP_cf 10 ER W ms md ly S data pb (sptr_addr B ly pb) 0 65536); try assumption.
- subst ER. split; [intros k Hk; apply E_RD_old; exact Hk | reflexivity].
- rewrite A46, <- Hpb. reflexivity.
- rewrite A58. apply u64_lit. lia.
- rewrite A59. apply u64_lit. lia.
- reflexivity.
- split; [left; reflexivity|]. split; [exact HP0|]. split; [exact HF0|]. split; [exact HT0|]. split; [exact HD0 | exact HDS0].
- intros i Hi. lia.
- lia.
- unfold dlen. lia.
- lia.
- exists 16. split; [lia | reflexivity].
- cbn. lia.
Qed.
End rf.

(* The closed result, at lane CwRunqA's statement (lib/AU/PresetD2runB.v:231-238, memnorm after PINV in rd0_file_tfa_cf
   and hdr_tfa_cf). The grow arm's cases are CwPinvA's proofs, cited (lib/AU/PresetPinvB23Pf.v gr_refused_cf_B_holds /
   gr_grow_cf_B_holds, gr_grow_cf_B with memnorm in its pre and its continuation). *)
Theorem tfib_rd0_file_cf_B_holds : tfib_rd0_file_cf_B.
Proof.
intros fx rc LS ci cp B NP NR HB HNPS HNPT HMAX MSITE RCHK MCPY FREE REFUSED HDR.
intros sp inp xw xd ws W ms md ly S a0 p data pb Hargv Hsp Hva Hve Hvfs HNR Hlen Hne Hnd Hlk HS HR HAI HAR HNP HXS HTOP Hbl Hnn Hpb
HF0 HT0 HP0 HD0 HDS0 HFI HMN HUP Hfs Hfds.
pose proof P23.gr_refused_cf_B_holds as GRR. pose proof P23.gr_grow_cf_B_holds as GRG.
eapply tfib_rd0_file_at_cf; eassumption.
Qed.

Print Assumptions tfib_rd0_dir_cf_B_holds.
Print Assumptions tfib_rd0_file_cf_B_holds.
