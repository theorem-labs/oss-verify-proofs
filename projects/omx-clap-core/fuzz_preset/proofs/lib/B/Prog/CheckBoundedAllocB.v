(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YC1fP.v, with its module paths and module names changed; 167 of its 196 lines of code are new or changed and 484 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43): the walk of
   fuzz_preset.c's check_bounded_alloc (#102 source :561-567, body unchanged; entry pa_sigma AS_check_bounded_alloc of
   the whole-program listing lib/B/Listing_prog.v) against the text tcheck_bounded_alloc_specX (lib/A/PRH_FnCheck.v:523-532,
   blob 9ecd8eb167c6, the #102 kit of record f97c8b2f046b: the ledger with `most own`, the five-conjunct fpre
   (raZ ceiling, frm_zero), the m-form post fpostm), proved VERBATIM. Generic in the allocator relation ARx (its laws
   LAWS : AR_laws_x .. ARx HL, the ONE premise), in CfParams / PrhRoomLive; at the program listing PL_prog_B / PI_prog_B
   and the generated image record prh_img_B. The B' instance is CheckBoundedAllocBInst.v check_bounded_alloc_holds_B_inst:
   B := YD2l.TfibB, h-mani-a8's allocator ARcf at CfParams_preset, LAWS discharged by PALibB.exvi_eh_laws (5baa19c890f7).
   RELOCATED from the old-pin walk (image B, pin f8f98a95, twin 3b5e1a09; donor origin/cold/h-rw-pre-5-b-cba
   ba1c537ab3d, blob a6849836adbf) by lane CbaBp of h-rw-pre-5: relocation only (48 bytes in both images;
   the instruction words are equal on both images, every pc-relative target the same symbol + offset); alreloc c4338d099cfb8025
   moved no numeral (the file holds no address literal).
   The code (12 words, neutral listing): the 16-byte frame and the ra spill; a1 := (size << 8) + (5 << 12);
   `bltu a1, a0` to the abort tail (__asan_handle_no_return; abort; unimp). The premises held <= PJ_ALLOC_BOUND size and
   size <= 2 ^ 40 (no wrap in the shift) REFUTE the branch: its taken arm is closed by contradiction, so the walk has
   no abort arm and no refusal exit (check_bounded_alloc holds no harness NULL site, the internal file tfib-walk-plan.md:125). The
   not-taken arm reloads ra, frees the frame and returns. No UBSan check branch (the internal file B-U-TRAPS.md:100), no call, no store
   outside the frame: the ledger is kept (S1Ledger's prh_ledger_kept_aview), the state does not change. The m-form post:
   the memory stays normal because the run's two frames (frame_of) change only the 16-byte stack frame, where no image
   segment lies (YAkMemnorm.memnorm_frame_off_segs with pa_segs_low). fpre's frm_zero (FRM0-ENTRY) and its raZ
   ceiling have no consumer here: the function calls nothing on the walked path.
   A' TWIN, the same text with the same one premise LAWS and the same proof skeleton: check_bounded_alloc_holds_A,
   lib/A/Prog/CheckBoundedAllocA.v blob 146cd9e79c09 (origin/cold/h-hreply-k1-p102-N10-CBAA 6dcbd0bcbca, in int102);
   this file differs from it only in the image names (B_prog_* / PI_prog_B / prh_img_B) and this header.
   REUSED (rule 24): the runner paj_run_x (YC1fPx), paj_branch / paj_ret_at / pa_entry_st_ok_full (YC1fP),
   ajournal_x_init / ajournal_x_materialize (YCbqG), prh_ledger_kept_aview (S1Ledger, c-omx-alloc),
   memnorm_frame_off_segs (YAkMemnorm). cba_aview_frame below is c-omx-alloc's OwnB.v ob_aview_frame (8b6f0ad380f),
   restated (OwnB.v is not importable without its poison kit). The old image-A stand-in twin
   cold/h-hpreset-7-walk-S9S11 e97cd4228957 lib/A/Prog/Wcheck_bounded_alloc.v:54 binds image A's old addresses.
   NUMERALS: 16 (the frame; the block alignment of YCbqG's ARx_blocks_law) LENGTH; 4096 (that law's lower bound,
   YCbqG.v ARx_blocks_law) DERIVED; 8 (the shift) and 20480 (= 5 << 12, the bound's constant as `lui a2, 5` loads it;
   PJ_ALLOC_BOUND's 32 * 8 * 64 + 4096) WORD; 63 (the shift mask) WORD; 2 ^ 4, 2 ^ 8, 2 ^ 40, 2 ^ 44, 2 ^ 46, 2 ^ 47,
   2 ^ 64 DERIVED bounds; atom indices 1 / 2 / 10 / 11 / 32 DERIVED (the engine's numbering: registers below 32, extra
   atoms from 32). port_addr_check 0767e70e074a (old B -> B'): 78 numerals, NON-ADDRESS-SAME 77, SAME-GEOMETRY 1 (the
   4096), no flag. No ADDRESS literal: the entry is B_prog_sigma AS_check_bounded_alloc, computed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
(* the PLAIN build's sink head must never fill SK here (YC1fP.v:23-33 does the same; repeated so this file is safe
   on its own): every SK below is passed explicitly *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".

Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at check_bounded_alloc's entry ----
   atoms: 1 = ra, 2 = entry sp, 10 = held, 11 = size, 32 = the shadow offset (the engine's shadow base; the walk reads
   no shadow); one region: the 16-byte frame, written (the ra spill); no shadow entry. *)
Definition CBA_K : Z := B_prog_sigma AS_check_bounded_alloc - B_prog_base.
Definition CBA_Bx : sv := SOff 32 0.
Definition CBA_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition cba_regions : smem := [stack_region 16].
Definition cba_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_cba : sstate := mkSS CBA_K sr_atoms cba_regions None cba_facts.
Definition cba_SH : list shent := [].

(* the program's statics (prh_pst at prh_img_B) are image bytes, far below the stack *)
Lemma cba_pst_low : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> 0 <= a < 2 ^ 46.
Proof.
intros a H. apply Exists_exists in H as (r & Hr & Ha). vm_compute in Hr.
repeat destruct Hr as [<-|Hr]; try contradiction; unfold in_zr in Ha; cbn [fst snd] in Ha; lia.
Qed.

(* the write windows of the frame region, off which a byte is kept by a run's frame *)
Ltac cba_notw Usp :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros (r & Hr & Ha); cbn [In ss_mem add_cond ss_cba cba_regions] in Hr;
  destruct Hr as [<-|[]]; cbn [stack_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite Usp in Ha; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
Definition CBA_EI (regs : bvmap 5 word) : env :=
  Eimg (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF])).

(* c-omx-alloc OwnB.v ob_aview_frame (8b6f0ad380f): a run's frame keeps the reader's view off its write windows *)
Lemma cba_aview_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hf Ha Hn. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the engine laws of the allocator relation, ONE named hypothesis (discharged at the instance) *)
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

Let RUN := @paj_run_x fx rc SK B_prog_listing PL_prog_B PI_prog_B B prh_pst ARx _ LAWS.
Let BR := paj_branch (L := B_prog_listing) (PI := PI_prog_B).
Let RET := paj_ret_at (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B).

(* the block law's placement part (YCbqG ARx_blocks_law) *)
Lemma cba_blocks : forall ly S Hp (W : world SEGS) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling.
Proof.
intros ly S Hp W mem md p n HA HI.
first [ destruct (alx_blocks _ _ _ _ LAWS ly S Hp W mem md p n HA HI) as (H1 & H2 & H3 & _)
      | destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HA HI) as (H1 & H2 & H3 & _)
      | destruct (alx_blocks LAWS ly S Hp W mem md p n HA HI) as (H1 & H2 & H3 & _) ].
split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* The kit's own text at image B', its whole-program listing and the generated image record, for every allocator
   relation ARx with the engine laws *)
Theorem check_bounded_alloc_holds_B :
  tcheck_bounded_alloc_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
unfold tcheck_bounded_alloc_specX, fpre, fpost.
(* fpre's five conjuncts (f97c): afn_pre_x, arodata_okP, the caller-frame margin, the raZ ceiling and frm_zero
   (FRM0-ENTRY). Only afn_pre_x is read: the walked path calls nothing, so frm_zero and the raZ ceiling have no
   callee to be supplied to. *)
intros ly S Hp W regs mem md ch held size Lam peak cnt fail ran most own (HPRE & HROD & HTOP & HRAC & HFRM)
  H10 H11 Hh Hs Hb HL0.
assert (WS : STK_check_bounded_alloc = 16) by reflexivity.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
rewrite WS in Hstk0, Hslo.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
remember (CBA_EI regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF])) k)
by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 held)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 size)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF])) E)
by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
(* the entry state *)
assert (HS : st_ok_pi SEGS VAL E ss_cba
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CBA_K)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cba. apply pa_entry_st_ok_full.
  - rewrite HE. unfold CBA_EI. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold cba_regions, stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros q Hq. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split].
    + cbn [cba_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity; try exact I.
    + cbn. tauto.
    + cbn. tauto. }
clear HE EL.
assert (SHOK : sh_ok SEGS CBA_Bx cba_SH E (mrestrict (w_H W) mem)) by constructor.
pose proof (ajournal_x_init (SK := SK) SEGS B prh_pst ARx STK_check_bounded_alloc [] ly S Hp W regs mem md ch HPRE) as HJ.
assert (Hent : @pa_sigma _ B_prog_listing PI_prog_B AS_check_bounded_alloc = BASE + CBA_K) by (vm_compute; reflexivity).
unfold cfg_at. rewrite Hent. change (w64 (BASE + CBA_K)) with (Z_to_bv 64 (BASE + CBA_K)).
(* the stretch to the bound's branch: the frame, the ra spill, a1 := (size << 8) + (5 << 12) *)
paj_run_tok_x RUN HS HJ SHOK CBA_Bspan.
{ intros a (r & Hr & Ha). cbn [ss_mem ss_cba cba_regions In] in Hr. destruct Hr as [<-|[]].
  cbn [stack_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. left. rewrite Usp in Ha. rewrite WS. lia. }
rename HFr into HFr1. rename HF into HF1. clear HG.
(* the bound's branch: taken only when held > PJ_ALLOC_BOUND size, which the premise refutes *)
psrr_branch_tok RUN BR HS SHOK CBA_Bspan.
- (* taken: (size << 8) + (5 << 12) <u held, i.e. held > PJ_ALLOC_BOUND size: refuted *)
  exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  repeat first [rewrite U_SAlu in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
  cbn [zalu_raw] in Hc. rewrite ?E10, ?E11 in Hc. rewrite ?unsigned_lit_small in Hc by lia.
  unfold zcanon, M64 in Hc. rewrite ?Z.add_0_r in Hc.
  change (Z.land (8 mod 2 ^ 64) 63) with 8 in Hc.
  rewrite ?Z.shiftl_mul_pow2 in Hc by lia.
  rewrite ?(Z.mod_small size) in Hc by lia. rewrite ?(Z.mod_small held) in Hc by lia.
  rewrite ?(Z.mod_small 20480) in Hc by lia.
  rewrite ?(Z.mod_small (size * 2 ^ 8)) in Hc by lia.
  rewrite ?(Z.mod_small (size * 2 ^ 8 + 20480)) in Hc by lia.
  unfold PJ_ALLOC_BOUND in Hb. lia.
- (* not taken: reload ra, free the frame, return *)
  paj_run_tok_x RUN HS HJ SHOK CBA_Bspan.
  { intros a (r & Hr & Ha). cbn [ss_mem add_cond In] in Hr. destruct Hr as [<-|[]].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. left. rewrite Usp in Ha. rewrite WS. lia. }
  rename HFr into HFr2. rename HF into HF2. clear HG.
  lazymatch goal with HSz : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ => set (mF := ms_mem msc) in * end.
  (* what the walk keeps: every byte off the frame window *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hn.
    rewrite (cba_aview_frame _ _ _ _ _ a HFr2 Ha) by (cba_notw Usp).
    apply (cba_aview_frame _ _ _ _ _ a HFr1 Ha). cba_notw Usp. }
  (* the statics: every prh_pst byte is kept, which is what the ledger and #102's two new cells (g_most,
     g_own_ran_out, fields `most own` of prh_ledger) read *)
  assert (KPST : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha. destruct (cba_pst_low a Ha) as [Ha0 Ha1]. apply KEEP; lia. }
  (* the ledger: the statics and every harness block's head are off the frame *)
  assert (HLn : prh_ledger B ly S Hp W mF Lam peak cnt fail ran most own).
  { eapply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mF); [exact HL0 | exact KPST | | |].
    - intros a k i Hin Hi.
      (* the kit's named projection (PRH_Base.v prh_ledger_blocks), not a positional destructuring *)
      pose proof HL0 as HLF. apply prh_ledger_blocks in HLF. rewrite Forall_forall in HLF.
      destruct (HLF (a, k) Hin) as (Hk0 & Hkin & _). cbn [fst snd] in Hk0, Hkin.
      pose proof cf_head_nonneg as Hcf0.
      destruct (cba_blocks ly S Hp W mem md _ _ HAR Hkin) as (Hp16 & Hp4096 & Hpceil).
      unfold req_size in Hpceil. destruct (Z.eqb_spec (k + cf_head) 0) as [E0|E0]; apply KEEP; lia.
    - intros a k _ H. exact H.
    - apply Permutation_refl. }
  (* the return: apost_base_x from the journal, the state unchanged *)
  lazymatch goal with HSz : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
    prreg HSz (1%bv : bv 5) R1;
    eapply (RET W _ _ _ _ _ HSz eq_refl ltac:(vm_compute; reflexivity));
    let mq := fresh "mq" in intros mq;
    unfold apost_base_x; cbv beta;
    exists ly, S, Hp, (ms_regs msc), (ms_mem msc); eexists; exists 0
  end.
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
  repeat rewrite wvb_collapse in HJ.
  split; [eapply (ajournal_x_materialize (SK := SK));
    solve [exact HJ | exact LAWS | exact (@pa_segs_low _ B_prog_listing PI_prog_B)] |].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs _ HS); [exact HAE | vm_compute; reflexivity] |].
  (* the post's own clauses. The text of record wraps Q in fQmn (fpostm), so the LAST conjunct is the memnorm keep *)
  split.
  { split; [reflexivity|]. split; [reflexivity|]. (* Hp' = Hp; S' = S, no allocator call: the exit state is the entry S *)
    split; [reflexivity|]. split; [intros Hr; exact Hr|]. exact HLn. }
  (* the memory stays normal: this walk's only writes are its own 16-byte frame, which lies in the stack
     (2 ^ 46 <= sp <= 2 ^ 47), where no image segment lies - pa_segs_low puts every segment below kLowMemEnd
     (the A' twin CheckBoundedAllocA.v 146cd9e79c09 closes it the same way) *)
  intros Hmn.
  apply (YAkMemnorm.memnorm_frame_off_segs SEGS mem mF (spZ regs - 16) (spZ regs) Hmn).
  + intros x Hx. rewrite (HF2 x) by (cba_notw Usp). exact (HF1 x ltac:(cba_notw Usp)).
  + first [ lia | unfold TASK_SIZE; lia | unfold TASK_SIZE in *; cbn in *; lia ].
  + intros x Hx. destruct (find_segment SEGS (bv_unsigned x) 1) as [sg|] eqn:Hsg; [exfalso|reflexivity].
    destruct (find_segment_some_spec SEGS (bv_unsigned x) 1 sg Hsg) as (Hin & Hlo & Hhi).
    assert (HIM : exists sg0, In sg0 SEGS /\
      Z.of_N (seg_base sg0) <= bv_unsigned x < Z.of_N (seg_base sg0) + Z.of_N (seg_size sg0))
      by (exists sg; split; [exact Hin | split; lia]).
    pose proof (@pa_segs_low _ B_prog_listing PI_prog_B (bv_unsigned x) HIM) as Hseglow.
    unfold kLowMemEnd in Hseglow. lia.
Qed.
End f.
End d.
