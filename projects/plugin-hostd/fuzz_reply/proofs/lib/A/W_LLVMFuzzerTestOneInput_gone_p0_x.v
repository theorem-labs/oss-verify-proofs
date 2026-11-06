(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's phase p0 (lib/A/W_LLVMFuzzerTestOneInput_gone_p0.v,
   a Theorem Labs lane's: the arm's entry 0x845e4 to the join 0x846f0), for the conversion of ARM_gone to the cut invariants of
   lib/A/W_LLVMFuzzerTestOneInput_cut_x.v (a Theorem Labs lane's route (b), step 7).  _gone_p0.v is not edited.
   - CITED from _gone_p0.v (they never read AR): the entry state's definitions (gp0_frA .. GP0_KEPT, outside its
     Section), gp0_byte, gp0_in_byte_rng, gp0_pres_grows, gp0_aframe_kept, gp0_kregs;
   - RESTATED here under their names + _x, with _gone_p0.v's proofs converted: gp0_entry_x (its shadow entry reads
     the live input block through the AR law, now base_x's gn_shent_in_block_x at the ghost list []), gp0_close_x
     (the join's predicate GJN_x; the arm's transport kit's tk_x lemmas), gp0_entry_join_x (the phase lemma);
   - copied verbatim (they are Local in _gone_p0.v): the write-obligation tactics gp0_awr / gp0_nowr.
   Every ghost list is [] (cut_x's HP0): the entry's (LFB0 cx, INV_A_x at []) and the cut's (lcut_x's Hp3, read off
   its journal by hp0g). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* _gone_p0.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* the arm's transport kit (lane p3 owns it; green and frozen) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p0.

(* _gone_p0.v:76 gp0_awr / :86 gp0_nowr (Local there), verbatim *)
(* a run's write obligation: both windows are in the function's own stack window, the input region is read-only *)
Local Ltac gp0_awr U9 :=
  cbn [ss_mem add_cond ss_gp0 gp0_reg];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [gp0_frA gp0_frB gp0_inA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK in *; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the two cells is outside every region's writable window *)
Local Ltac gp0_nowr U9 Hna Hnb :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gp0 gp0_reg In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [gp0_frA gp0_frB gp0_inA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?U9 in Hr; lia | ]);
  destruct Hin.

Section gp0_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* _gone_p0.v:109 HERR, verbatim (AR-free) *)
(* errno's place, the base's GN_ERRNO_LOW: the transport of aout_at across the two stores reads it *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* OWED: kit _x twin of al_blocks' last conjunct; W_kit_x.v's BLKN (tk_x's gk_ainput_kept_x / gk_amodel_kept_x and
   al0_blocks take it) *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* _gone_p0.v's AR-free lemmas that take section arguments, cited with them *)
Local Notation gp0_byte := (W_LLVMFuzzerTestOneInput_gone_p0.gp0_byte B).
Local Notation gp0_kregs := (W_LLVMFuzzerTestOneInput_gone_p0.gp0_kregs B XM_LIB RLO LSx RINV).
(* _gone_p0.v:112-114, over W_journal_x's generic chain *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* _gone_p0.v:117 gp0_entry *)
(* the entry state, both in.n cases (the base's gn_entryA, with the two narrow frame windows) *)
Lemma gp0_entry_x : forall (W : world segs) ly S mem md regs (more : bool) idv F tv,
  AR0 ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 26 = w64 SB -> getr regs 28 = w64 tv ->
  2 ^ 46 <= F -> F + 216 <= 2 ^ 47 -> F mod 32 = 0 -> awr W mem F 216 -> sv8 W mem (F + 32) 6129888 ->
  4096 <= tv <= 140737479966720 -> tv + 1 <= F -> 0 <= idv < 256 ->
  (more = true -> val_mem segs (arm W mem) tv 1 idv /\
     exists p n, In (p, n) (ablocks B ly S) /\ p <= tv /\ tv + 1 <= p + req_size n) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (gp0_extra idv))) (ss_gp0 more)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_gone)) mem (seg_rom segs)))
  /\ sh_ok segs gp0_Bx (gp0_SH more) (Eimg (Ereg regs (gp0_extra idv))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S mem md regs more idv F tv HAR R9 R26 R28 HF1 HF2 HF3 HFw HF32 Ht1 Ht2 Hid Hmore.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (gp0_extra idv))).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = SB) by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SB; lia).
  assert (U28 : bv_unsigned (ew E 28) = tv) by (rewrite (EE 28%nat 28%bv eq_refl), R28; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = idv) by (rewrite E32; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gp0. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + destruct more; vm_compute; reflexivity.
    + assert (RF : region_ok segs E (mrestrict (w_H W) mem) gp0_frA).
      { unfold region_ok, gp0_frA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ F 32 8 (SLit 6129888) 6129888); [reflexivity | lia | lia | exact HF32]. }
      assert (RFB : region_ok segs E (mrestrict (w_H W) mem) gp0_frB).
      { unfold region_ok, gp0_frB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|]. constructor. }
      destruct more; [|constructor; [exact RF | constructor; [exact RFB | constructor]]].
      destruct (Hmore eq_refl) as (Hv & _).
      constructor; [exact RF|]. constructor; [exact RFB|]. constructor; [|constructor].
      unfold region_ok, gp0_inA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U28. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ tv 0 1 (SOff 32 0) idv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | rewrite Z.add_0_r; exact Hv].
    + apply pairwise_disjoint_of_extents. destruct more; unfold gp0_reg, gp0_frA, gp0_frB, gp0_inA, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U28;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [gp0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U26, U28, U32. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - destruct more; unfold sh_ok, gp0_SH; [|constructor].
    destruct (Hmore eq_refl) as (_ & p & n & Hin & Hp1 & Hp2).
    constructor; [|constructor].
    apply (gn_shent_in_block_x B ARx LAWS ly S W mem md E gp0_Bx 28 tv p n 0 1 HAR Hin); try lia.
    + unfold gp0_Bx, U. cbn [sv_denot]. rewrite U26, Z.add_0_r, unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite U28, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
Qed.

(* _gone_p0.v:254 gp0_close *)
(* the join's predicate from the entry's cut facts, carried across the two stores *)
Lemma gp0_close_x : forall cx t m (W : world segs) mem mem' md md' regs' ly3 S3 k fpos,
  LFB0 cx ->
  AR0 ly3 S3 W mem md ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem' md' k ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> NP S3 -> LSx cx t m ly3 S3 -> RINV cx t m -> gn_op cx t m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 40 <= a < lf_F cx + 48) -> ~ (lf_F cx + 144 <= a < lf_F cx + 152) ->
     abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  sv8 W mem' (lf_F cx + 40) (c_p cx + gn_kq cx m) -> sv8 W mem' (lf_F cx + 144) (c_n cx - gn_kq cx m) ->
  gn_kregs B cx t (frame_addr ly3 1 fpos) regs' ->
  getr regs' 20 = w64 (rg_s fr_RG) -> getr regs' 21 = w64 (gn_id cx m) ->
  GJN_x B NP G_fr fr_FP PST ARx LSx RINV cx t m W
    (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_gn_join)) mem' (seg_rom segs)) md').
Proof.
  intros cx t m W mem mem' md md' regs' ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HJT HSEP HNP HLS HRI HOP KEEP WK
    SV40 SV144 KR R20 R21.
  destruct (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly3 S3 W mem' md'
              k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR').
  pose proof HB as (_ & HPRE). pose proof HPRE as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof gk_ceil_lo as HCL. pose proof HERR as (HE0 & HE1).
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; apply KEEP; unfold GK_CEIL8, LLVMF_STK in *; lia).
  unfold GJN_x. exists regs', mem', md', ly3, S3, k, fpos.
  split; [reflexivity|].
  split.
  { unfold gcom_x. split; [exact HJ|].
    split.
    { apply gframe_of_aframe. apply (gp0_aframe_kept cx true _ W W mem mem' HFR KEEP WK);
        unfold GK_CEIL8, SB, LLVMF_STK in *; lia. }
    split; [exact SV40|]. split; [exact SV144|].
    split; [exact (gk_ainput_kept_x B ARx LAWS BLKN cx ly3 S3 W mem md W mem' HAR HIN (eq_sym Hnlen) KL)|].
    split; [exact (gk_rom_kept W W mem mem' HRV KL)|].
    split; [exact (gk_jt_kept W W mem mem' HJT KL)|].
    (* the fake frame's flag word at FF + 120: kept like gframe's other fake-frame words, inside [0, GK_CEIL8) *)
    apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold GK_CEIL8; lia | exact HFL]. }
  split; [exact (gk_amodel_kept_x B ARx LAWS BLKN ly3 S3 W mem md W mem' m HAR HMOD HE0 HE1 KL)|].
  split; [exact HSEP|]. split; [exact HNP|]. split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|].
  split; [exact KR|]. split; [exact R20 | exact R21].
Qed.

(* ------------------------------------------------------------------ GP0: the entry 0x845e4 to the join 0x846f0 *)
(* _gone_p0.v:300 gp0_entry_join *)
Lemma gp0_entry_join_x : forall cx t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 5 cx [] t W c ->
  SRr segs W c (fun W' c' => exists m, GJN_x B NP G_fr fr_FP PST ARx LSx RINV cx t m W' c').
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP
                   & HRI & HR).
  hp0g HJ.
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as (HCOM & R6 & R7 & R27 & Ht & Hk & HO & R11 & HPK).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  (* the operation is 5: not a picking one, so t3 = in.p + 1, t4 = in.n - 1 (the cursor after the op byte) *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 5).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 5) with false in HPK. cbv iota in HPK.
  destruct HPK as (R28 & R29 & R21).
  assert (HOP : gn_op cx t m) by (split; [exact Hop | split; [exact HO | split; [exact Ht | exact Hk]]]).
  destruct (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly3 S3 W mem md
              k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HIN as [[(Hn0 & _) | (Hn & Hin)] HIG]; [lia|].
  destruct (al0_blocks B ARx LAWS BLKN ly3 S3 W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _).
  pose proof (asan_consts) as (C1c & C2c & C3c & C4c & C5c).
  assert (Hreq : c_n cx <= req_size (c_n cx)) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  pose proof HFR as (HSV & HAWR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFULL & _).
  destruct (HFULL eq_refl) as (HF32v & _).
  set (F := lf_F cx) in *. set (FF := frame_addr ly3 1 fpos) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (tv := c_p cx + lm_k m + 1).
  assert (R9 : getr regs 9 = w64 F) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R26 : getr regs 26 = w64 SB) by (rewrite (KR0 26%bv ltac:(cbv; tauto)); exact C26).
  assert (R28' : getr regs 28 = w64 tv) by (rewrite (KR0 28%bv ltac:(cbv; tauto)); exact R28).
  assert (R29' : getr regs 29 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KR0 29%bv ltac:(cbv; tauto)); exact R29).
  assert (P1 : 2 ^ 46 <= F) by (unfold LLVMF_STK in *; lia).
  assert (P2 : F + 216 <= 2 ^ 47) by lia.
  assert (P3 : awr W mem F 216) by (intros o Ho; apply HAWR; lia).
  assert (P4 : 4096 <= tv <= 140737479966720) by (unfold tv; lia).
  assert (P5 : tv + 1 <= F) by (unfold tv, LLVMF_STK in *; lia).
  destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hmore | Hmore].
  - (* in.n > 0 after the op byte: the id is in.p[0] *)
    set (idv := in_byte cx (lm_k m + 1)).
    assert (P6 : true = true -> val_mem segs (arm W mem) tv 1 idv /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n).
    { intros _. split; [unfold tv, idv; replace (c_p cx + lm_k m + 1) with (c_p cx + (lm_k m + 1)) by lia;
        exact (gp0_byte cx ly3 S3 W mem (lm_k m + 1) Hnlen HIN ltac:(lia))|].
      exists (c_p cx), (c_n cx). split; [exact Hin|]. unfold tv. lia. }
    destruct (gp0_entry_x W ly3 S3 mem md regs true idv F tv HAR R9 R26 R28'
      P1 P2 HF32 P3 HF32v P4 P5 (gp0_in_byte_rng cx (lm_k m + 1)) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra idv))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra idv)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 tv) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 29%nat 29%bv eq_refl); exact R29').
    assert (E32 : ew E 32 = Z_to_bv 64 idv)
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    (* 0x845e4 beqz t4: not taken, t4 = in.n - 1 > 0 *)
    psrr_branch_tok RUN BR HS SHOK gp0_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 29 _ E29), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + (* 0x845e8-0x84610: the instrumented check of in.p[0] (the error path is not reached), s4, s5, the cursor *)
      paj_run_to_tok_x RUNTO HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 40 <= a < F + 48) -> ~ (F + 144 <= a < F + 152) ->
          aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna Hnb; apply (aview_kept_out _ _ _ _ _ HFr a Ha); gp0_nowr U9 Hna Hnb).
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms)) a).
      { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
        intros Hp. exact (gp0_pres_grows W _ _ a HGr Hp). }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 40 <= a < F + 48) -> ~ (F + 144 <= a < F + 152) ->
          abyte_kept W mem W (ms_mem ms) a)
        by (intros a Ha Hna Hnb; split; [exact (K1 a Ha Hna Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      assert (SV40 : sv8 W (ms_mem ms) (F + 40) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with (tv + 1)
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 40 8%N (SOff 28 1) (tv + 1) RG0) end.
        - rewrite !ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E28, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with (c_n cx - lm_k m - 1 + -1)
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 144 8%N (SOff 29 (-1)) (c_n cx - lm_k m - 1 + -1) RG1) end.
        - rewrite !ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs (gp0_extra idv)) Ev)
          by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite !ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      (* s4 = &g_s[0] from F+32, s5 = in.p[0] (atom 32) *)
      prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply SRr_ret. exists m.
      apply (gp0_close_x cx t m W mem (ms_mem ms) md _ (ms_regs ms) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HNP HLS HRI HOP KEEP WK SV40 SV144 (gp0_kregs cx t FF regsD (ms_regs ms) KK HCOM R27)).
      * rewrite Q20. reflexivity.
      * rewrite Q21, E32. unfold gn_id, gn_more.
        destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [_ | Hlt]; [reflexivity | lia].
  - (* in.n = 0 after the op byte: fuzz_u8 gives 0 and consumes nothing *)
    assert (P6 : false = true -> val_mem segs (arm W mem) tv 1 0 /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n) by discriminate.
    destruct (gp0_entry_x W ly3 S3 mem md regs false 0 F tv HAR R9 R26 R28'
      P1 P2 HF32 P3 HF32v P4 P5 ltac:(lia) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra 0))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra 0)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 tv) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 29%nat 29%bv eq_refl); exact R29').
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    (* 0x845e4 beqz t4: taken, t4 = 0 *)
    psrr_branch_tok RUN BR HS SHOK gp0_Bspan.
    + (* 0x846e0-0x846ec: F+40 = in.p, F+144 = 0, s5 = 0, s4 = &g_s[0] *)
      paj_run_to_tok_x RUNTO HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 40 <= a < F + 48) -> ~ (F + 144 <= a < F + 152) ->
          aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna Hnb; apply (aview_kept_out _ _ _ _ _ HFr a Ha); gp0_nowr U9 Hna Hnb).
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms)) a).
      { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
        intros Hp. exact (gp0_pres_grows W _ _ a HGr Hp). }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 40 <= a < F + 48) -> ~ (F + 144 <= a < F + 152) ->
          abyte_kept W mem W (ms_mem ms) a)
        by (intros a Ha Hna Hnb; split; [exact (K1 a Ha Hna Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      assert (SV40 : sv8 W (ms_mem ms) (F + 40) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with tv
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 40 8%N (SOff 28 0) tv RG0).
        - exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with 0
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 144 8%N (SLit 0) 0 RG1).
        - exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      (* s4 = &g_s[0] from F+32, s5 = 0 *)
      prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply SRr_ret. exists m.
      apply (gp0_close_x cx t m W mem (ms_mem ms) md _ (ms_regs ms) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HNP HLS HRI HOP KEEP WK SV40 SV144 (gp0_kregs cx t FF regsD (ms_regs ms) KK HCOM R27)).
      * rewrite Q20. reflexivity.
      * rewrite Q21. unfold gn_id, gn_more.
        destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hlt | _]; [lia | reflexivity].
    + (* 0x845e4 beqz t4 not taken: t4 = in.n - 1 = 0, no such state *)
      exfalso. rewrite branch_eq_U, (U_atom E 29 _ E29), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): GP0 over the cut journal at a world relation R (cut_x's INV_A_xR, the base's
   GJN_xR).  The phase is straight-line code (no call), so it stays strict SRr over the R journal: its token runs are
   W_journal_x's paj_run_x_xR / paj_run_to_x_xR, its journal reads the _xR twins (ajournal_gx_AR_xR, gn_nums_xR); the
   proofs are the strict ones above with those names.  At R := wle each text is the strict one. *)
Section gp0_xR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
(* gp0_close_x over the journal at R *)
Lemma gp0_close_xR : forall cx t m (W : world segs) mem mem' md md' regs' ly3 S3 k fpos,
  LFB0 cx ->
  AR0 ly3 S3 W mem md ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem' md' k ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> NP S3 -> LSx cx t m ly3 S3 -> RINV cx t m -> gn_op cx t m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 40 <= a < lf_F cx + 48) -> ~ (lf_F cx + 144 <= a < lf_F cx + 152) ->
     abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  sv8 W mem' (lf_F cx + 40) (c_p cx + gn_kq cx m) -> sv8 W mem' (lf_F cx + 144) (c_n cx - gn_kq cx m) ->
  gn_kregs B cx t (frame_addr ly3 1 fpos) regs' ->
  getr regs' 20 = w64 (rg_s fr_RG) -> getr regs' 21 = w64 (gn_id cx m) ->
  GJN_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m W
    (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_gn_join)) mem' (seg_rom segs)) md').
Proof.
  intros cx t m W mem mem' md md' regs' ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HJT HSEP HNP HLS HRI HOP KEEP WK
    SV40 SV144 KR R20 R21.
  destruct (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly3 S3 W
              mem' md' k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR').
  pose proof HB as (_ & HPRE). pose proof HPRE as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof gk_ceil_lo as HCL. pose proof HERR as (HE0 & HE1).
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; apply KEEP; unfold GK_CEIL8, LLVMF_STK in *; lia).
  unfold GJN_xR. exists regs', mem', md', ly3, S3, k, fpos.
  split; [reflexivity|].
  split.
  { unfold gcom_xR. split; [exact HJ|].
    split.
    { apply gframe_of_aframe. apply (gp0_aframe_kept cx true _ W W mem mem' HFR KEEP WK);
        unfold GK_CEIL8, SB, LLVMF_STK in *; lia. }
    split; [exact SV40|]. split; [exact SV144|].
    split; [exact (gk_ainput_kept_x B ARx LAWS BLKN cx ly3 S3 W mem md W mem' HAR HIN (eq_sym Hnlen) KL)|].
    split; [exact (gk_rom_kept W W mem mem' HRV KL)|].
    split; [exact (gk_jt_kept W W mem mem' HJT KL)|].
    apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold GK_CEIL8; lia | exact HFL]. }
  split; [exact (gk_amodel_kept_x B ARx LAWS BLKN ly3 S3 W mem md W mem' m HAR HMOD HE0 HE1 KL)|].
  split; [exact HSEP|]. split; [exact HNP|]. split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|].
  split; [exact KR|]. split; [exact R20 | exact R21].
Qed.
(* GP0 at R: INV_A_xR at arm 5 to the join GJN_xR *)
Lemma gp0_entry_join_xR : forall cx t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 5 cx [] t W c ->
  SRr segs W c (fun W' c' => exists m, GJN_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m W' c').
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP
                   & HRI & HR).
  hp0gR HJ.
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as (HCOM & R6 & R7 & R27 & Ht & Hk & HO & R11 & HPK).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4).
  assert (Hop : in_byte cx (lm_k m) mod 10 = 5).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 5) with false in HPK. cbv iota in HPK.
  destruct HPK as (R28 & R29 & R21).
  assert (HOP : gn_op cx t m) by (split; [exact Hop | split; [exact HO | split; [exact Ht | exact Hk]]]).
  destruct (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly3 S3 W
              mem md k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HIN as [[(Hn0 & _) | (Hn & Hin)] HIG]; [lia|].
  destruct (al0_blocks B ARx LAWS BLKN ly3 S3 W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _).
  pose proof (asan_consts) as (C1c & C2c & C3c & C4c & C5c).
  assert (Hreq : c_n cx <= req_size (c_n cx)) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  pose proof HFR as (HSV & HAWR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFULL & _).
  destruct (HFULL eq_refl) as (HF32v & _).
  set (F := lf_F cx) in *. set (FF := frame_addr ly3 1 fpos) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (tv := c_p cx + lm_k m + 1).
  assert (R9 : getr regs 9 = w64 F) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R26 : getr regs 26 = w64 SB) by (rewrite (KR0 26%bv ltac:(cbv; tauto)); exact C26).
  assert (R28' : getr regs 28 = w64 tv) by (rewrite (KR0 28%bv ltac:(cbv; tauto)); exact R28).
  assert (R29' : getr regs 29 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KR0 29%bv ltac:(cbv; tauto)); exact R29).
  assert (P1 : 2 ^ 46 <= F) by (unfold LLVMF_STK in *; lia).
  assert (P2 : F + 216 <= 2 ^ 47) by lia.
  assert (P3 : awr W mem F 216) by (intros o Ho; apply HAWR; lia).
  assert (P4 : 4096 <= tv <= 140737479966720) by (unfold tv; lia).
  assert (P5 : tv + 1 <= F) by (unfold tv, LLVMF_STK in *; lia).
  destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hmore | Hmore].
  - set (idv := in_byte cx (lm_k m + 1)).
    assert (P6 : true = true -> val_mem segs (arm W mem) tv 1 idv /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n).
    { intros _. split; [unfold tv, idv; replace (c_p cx + lm_k m + 1) with (c_p cx + (lm_k m + 1)) by lia;
        exact (gp0_byte cx ly3 S3 W mem (lm_k m + 1) Hnlen HIN ltac:(lia))|].
      exists (c_p cx), (c_n cx). split; [exact Hin|]. unfold tv. lia. }
    destruct (gp0_entry_x W ly3 S3 mem md regs true idv F tv HAR R9 R26 R28'
      P1 P2 HF32 P3 HF32v P4 P5 (gp0_in_byte_rng cx (lm_k m + 1)) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra idv))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra idv)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 tv) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 29%nat 29%bv eq_refl); exact R29').
    assert (E32 : ew E 32 = Z_to_bv 64 idv)
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    psrr_branch_tok RUNR BR HS SHOK gp0_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 29 _ E29), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + paj_run_to_tok_x RUNTOR HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 40 <= a < F + 48) -> ~ (F + 144 <= a < F + 152) ->
          aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna Hnb; apply (aview_kept_out _ _ _ _ _ HFr a Ha); gp0_nowr U9 Hna Hnb).
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms)) a).
      { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
        intros Hp. exact (gp0_pres_grows W _ _ a HGr Hp). }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 40 <= a < F + 48) -> ~ (F + 144 <= a < F + 152) ->
          abyte_kept W mem W (ms_mem ms) a)
        by (intros a Ha Hna Hnb; split; [exact (K1 a Ha Hna Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      assert (SV40 : sv8 W (ms_mem ms) (F + 40) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with (tv + 1)
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 40 8%N (SOff 28 1) (tv + 1) RG0) end.
        - rewrite !ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E28, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with (c_n cx - lm_k m - 1 + -1)
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 144 8%N (SOff 29 (-1)) (c_n cx - lm_k m - 1 + -1) RG1) end.
        - rewrite !ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs (gp0_extra idv)) Ev)
          by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite !ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply SRr_ret. exists m.
      apply (gp0_close_xR cx t m W mem (ms_mem ms) md _ (ms_regs ms) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HNP HLS HRI HOP KEEP WK SV40 SV144 (gp0_kregs cx t FF regsD (ms_regs ms) KK HCOM R27)).
      * rewrite Q20. reflexivity.
      * rewrite Q21, E32. unfold gn_id, gn_more.
        destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [_ | Hlt]; [reflexivity | lia].
  - assert (P6 : false = true -> val_mem segs (arm W mem) tv 1 0 /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n) by discriminate.
    destruct (gp0_entry_x W ly3 S3 mem md regs false 0 F tv HAR R9 R26 R28'
      P1 P2 HF32 P3 HF32v P4 P5 ltac:(lia) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra 0))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra 0)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E28 : ew E 28 = Z_to_bv 64 tv) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28').
    assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 29%nat 29%bv eq_refl); exact R29').
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    psrr_branch_tok RUNR BR HS SHOK gp0_Bspan.
    + paj_run_to_tok_x RUNTOR HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 40 <= a < F + 48) -> ~ (F + 144 <= a < F + 152) ->
          aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna Hnb; apply (aview_kept_out _ _ _ _ _ HFr a Ha); gp0_nowr U9 Hna Hnb).
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms)) a).
      { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
        intros Hp. exact (gp0_pres_grows W _ _ a HGr Hp). }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 40 <= a < F + 48) -> ~ (F + 144 <= a < F + 152) ->
          abyte_kept W mem W (ms_mem ms) a)
        by (intros a Ha Hna Hnb; split; [exact (K1 a Ha Hna Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      assert (SV40 : sv8 W (ms_mem ms) (F + 40) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with tv
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 40 8%N (SOff 28 0) tv RG0).
        - exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with 0
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 144 8%N (SLit 0) 0 RG1).
        - exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply SRr_ret. exists m.
      apply (gp0_close_xR cx t m W mem (ms_mem ms) md _ (ms_regs ms) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HNP HLS HRI HOP KEEP WK SV40 SV144 (gp0_kregs cx t FF regsD (ms_regs ms) KK HCOM R27)).
      * rewrite Q20. reflexivity.
      * rewrite Q21. unfold gn_id, gn_more.
        destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hlt | _]; [lia | reflexivity].
    + exfalso. rewrite branch_eq_U, (U_atom E 29 _ E29), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
Qed.
End gp0_xR.

End gp0_x.
