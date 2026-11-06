(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's phase p0 on image B (lib/B/W_LLVMFuzzerTestOneInput_gone_p0.v,
   a Theorem Labs lane's, fee5272ac13: the arm's entry to the join), for the conversion of ARM_gone to the cut invariants of
   lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.  _gone_p0.v is not edited.
   - CITED from _gone_p0.v (they never read AR): the entry state's definitions (gp0_frA .. GP0_KEPT, outside its
     Section), gp0_byte, gp0_in_byte_rng, gp0_pres_grows, gp0_aframe_kept, gp0_kregs;
   - RESTATED here under their names + _x, merged per item with SmallX's image-A twin
     lib/A/W_LLVMFuzzerTestOneInput_gone_p0_x.v (95a5de32ab2): gp0_entry_x, gp0_close_x (the join's predicate GJN_x),
     gp0_entry_join_x (the phase lemma);
   - copied (they are Local in _gone_p0.v): the write-obligation tactics gp0_awr / gp0_nowr, over awr_ok_x.
   Every ghost list is [] (cut_x's HP0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_p0.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_p0.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the entry state at 0x849a0 *)
(* the frame windows F+16 (in.p), F+88 (t), F+144 (in.n), all written; for in.n > 0 also the byte at the cursor s4
   (atom 20), read into atom 32 *)
(* @@ MERGED Local_Ltac gp0_awr *)
Local Ltac gp0_awr U9 :=
  cbn [ss_mem add_cond ss_gp0 gp0_reg];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [gp0_frA gp0_frT gp0_frB gp0_inA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold YCfn.LLVMF_STK in *; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the three windows is outside every region's writable window *)
(* @@ MERGED Local_Ltac gp0_nowr *)
Local Ltac gp0_nowr U9 Hna Hnt Hnb :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gp0 gp0_reg In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [gp0_frA gp0_frT gp0_frB gp0_inA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.
(* @@ SECTION gp0 *)
Section gp0.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ MERGED Variable MT *)
Variable MT : ameter_ops.
(* @@ MERGED Variables XM_LIB *)
Variables XM_LIB : Z -> Z.
(* @@ MERGED Variables RLO *)
Variables RLO RHI : Z.
(* @@ MERGED Variable fr_live_pre *)
Variable fr_live_pre : astate -> Prop.
(* @@ AX-ONLY Variables LIBROOM *)
Variables LIBROOM NP : astate -> Prop.
(* @@ MERGED Variable G_fr *)
Variable G_fr : list (Z * Z).
(* @@ MERGED Variable fr_FP *)
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
(* @@ AX-ONLY Variable PST *)
Variable PST : list (Z * Z).
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* @@ AX-ONLY Hypothesis HP0 *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
(* @@ MERGED Hypothesis HG *)
Hypothesis HG : gx_ok segs B G_fr.
(* @@ AX-ONLY Variable LSx *)
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
(* @@ RESOLVED Variable RINV *)
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* errno's place, the base's GN_ERRNO_LOW: the transport of aout_at across the three stores reads it *)
(* @@ RESOLVED Hypothesis HERR *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* @@ AX-ONLY Hypothesis BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* @@ MERGED Let RUN *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ MERGED Let RUNTO *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ RESOLVED Let BR *)
Let BR := paj_branch (PI := PB_fr).
(* @@ AX-ONLY Local_Notation AR0 *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* @@ AX-ONLY Local_Notation AJ0 *)
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation AJi0 *)
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation AFN0 *)
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
(* @@ AX-ONLY Local_Notation LFB0 *)
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
(* @@ AX-ONLY Ltac hp0a *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
(* @@ AX-ONLY Ltac hp0g *)
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* _gone_p0.v's AR-free lemmas that take section arguments, cited with them *)
(* @@ ALIASES - *)
(* the AR file's AR-free names that take this Section's variables, cited with them *)
Local Notation gp0_byte := (W_LLVMFuzzerTestOneInput_gone_p0.gp0_byte B).
Local Notation gp0_kregs := (W_LLVMFuzzerTestOneInput_gone_p0.gp0_kregs B XM_LIB RLO LSx RINV).
(* @@ RESOLVED Lemma gp0_entry *)
Lemma gp0_entry_x : forall (W : world segs) ly S mem md regs (more : bool) idv F tv,
  AR0 ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 20 = w64 tv -> getr regs 23 = w64 1 -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F -> F + 216 <= 2 ^ 47 -> F mod 32 = 0 -> awr W mem F 216 ->
  4096 <= tv <= 140737479966720 -> tv + 1 <= F -> 0 <= idv < 256 ->
  (more = true -> val_mem segs (arm W mem) tv 1 idv /\
     exists p n, In (p, n) (ablocks B ly S) /\ p <= tv /\ tv + 1 <= p + req_size n) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (gp0_extra idv))) (ss_gp0 more)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_gone)) mem (seg_rom segs)))
  /\ sh_ok segs gp0_Bx (gp0_SH more) (Eimg (Ereg regs (gp0_extra idv))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S mem md regs more idv F tv HAR R9 R20 R23 R27 HF1 HF2 HF3 HFw Ht1 Ht2 Hid Hmore.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (gp0_extra idv))).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = tv) by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = 1) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SB; lia).
  assert (U32 : bv_unsigned (ew E 32) = idv) by (rewrite E32; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gp0. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + destruct more; vm_compute; reflexivity.
    + assert (RA : region_ok segs E (mrestrict (w_H W) mem) gp0_frA).
      { unfold region_ok, gp0_frA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|]. constructor. }
      assert (RT : region_ok segs E (mrestrict (w_H W) mem) gp0_frT).
      { unfold region_ok, gp0_frT. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|]. constructor. }
      assert (RB : region_ok segs E (mrestrict (w_H W) mem) gp0_frB).
      { unfold region_ok, gp0_frB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|]. constructor. }
      destruct more; [|constructor; [exact RA | constructor; [exact RT | constructor; [exact RB | constructor]]]].
      destruct (Hmore eq_refl) as (Hv & _).
      constructor; [exact RA|]. constructor; [exact RT|]. constructor; [exact RB|]. constructor; [|constructor].
      unfold region_ok, gp0_inA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ tv 0 1 (SOff 32 0) idv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | rewrite Z.add_0_r; exact Hv].
    + apply pairwise_disjoint_of_extents. destruct more; unfold gp0_reg, gp0_frA, gp0_frT, gp0_frB, gp0_inA, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U20;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [gp0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U20, U23, U27, U32. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - destruct more; unfold sh_ok, gp0_SH; [|constructor].
    destruct (Hmore eq_refl) as (_ & p & n & Hin & Hp1 & Hp2).
    constructor; [|constructor].
    apply (gn_shent_in_block_x B ARx LAWS ly S W mem md E gp0_Bx 20 tv p n 0 1 HAR Hin); try lia.
    + unfold gp0_Bx, U. cbn [sv_denot]. rewrite U27, Z.add_0_r, unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
Qed.

(* one input byte, as the program reads it (A's p0 gp0_byte, verbatim) *)
(* @@ RESOLVED Lemma gp0_byte *)
(* @@ CONFLICT Lemma gp0_kregs *)

(* the join's predicate from the entry's cut facts, carried across the three stores *)
(* @@ RESOLVED Lemma gp0_close *)
Lemma gp0_close_x : forall cx t m (W : world segs) mem mem' md md' regs' ly3 S3 k fpos,
  LFB0 cx ->
  AR0 ly3 S3 W mem md ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem' md' k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> NP S3 -> LSx cx t m ly3 S3 -> RINV cx t m -> gn_op cx t m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 16 <= a < lf_F cx + 24) -> ~ (lf_F cx + 88 <= a < lf_F cx + 96) ->
     ~ (lf_F cx + 144 <= a < lf_F cx + 152) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  sv8 W mem' (lf_F cx + 16) (c_p cx + gn_kq cx m) -> sv8 W mem' (lf_F cx + 144) (c_n cx - gn_kq cx m) ->
  sv8 W mem' (lf_F cx + 88) t ->
  gn_kregs B cx (frame_addr ly3 1 fpos) regs' ->
  getr regs' 24 = w64 (SB + frame_addr ly3 1 fpos / 8) -> getr regs' 26 = w64 HI_G_NOUT ->
  getr regs' 21 = w64 (gn_id cx m) ->
  GJN_x B NP G_fr fr_FP PST ARx LSx RINV cx t m W
    (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_gn_join)) mem' (seg_rom segs)) md').
Proof.
  intros cx t m W mem mem' md md' regs' ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HJT HSEP HNP HLS HRI HOP KEEP WK
    SV16 SV144 SV88 KR R24 R26 R21.
  destruct (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly3 S3 W mem' md'
              k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR').
  pose proof HB as (_ & HPRE). pose proof HPRE as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof gk_ceil_lo as HCL. pose proof HERR as (HE0 & HE1).
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; apply KEEP; unfold GK_CEIL8, YCfn.LLVMF_STK in *; lia).
  unfold GJN_x. exists regs', mem', md', ly3, S3, k, fpos.
  split; [reflexivity|].
  split.
  { unfold gcom_x. split; [exact HJ|].
    split.
    { apply gframe_of_aframe. apply (gp0_aframe_kept cx _ W W mem mem' HFR KEEP WK);
        unfold GK_CEIL8, SB, YCfn.LLVMF_STK in *; lia. }
    split.
    { apply (gk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KL.
      unfold GK_CEIL8 in *. lia. }
    split; [exact SV16|]. split; [exact SV144|]. split; [exact SV88|].
    split; [exact (gk_ainput_kept_x B ARx LAWS BLKN cx ly3 S3 W mem md W mem' HAR HIN (eq_sym Hnlen) KL)|].
    split; [exact (gk_rom_kept W W mem mem' HRV KL)|].
    exact (gk_jt_kept W W mem mem' HJT KL). }
  split; [exact (gk_amodel_kept_x B ARx LAWS BLKN ly3 S3 W mem md W mem' m HAR HMOD HE0 HE1 KL)|].
  split; [exact HSEP|]. split; [exact HNP|]. split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|].
  split; [exact KR|]. split; [exact R24|]. split; [exact R26 | exact R21].
Qed.

(* ------------------------------------------------------------------ GP0: the entry 0x849a0 to the join 0x84aa8 *)
(* @@ RESOLVED Lemma gp0_entry_join *)
Lemma gp0_entry_join_x : forall cx t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 5 cx [] t W c ->
  SRr segs W c (fun W' c' => exists m, GJN_x B NP G_fr fr_FP PST ARx LSx RINV cx t m W' c').
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP3 & HRI
                   & HR).
  hp0g HJ.
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as (HCOM & R25 & Ht & Hk & HO & R11 & HPK).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  (* the operation is 5: not a picking one, so s4 = in.p + k + 1, t1 = in.n - k - 1 (the cursor after the op byte) *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 5).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 5) with false in HPK. cbv iota in HPK.
  destruct HPK as (R20 & R6 & R21).
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
  pose proof HFR as (HSV & HAWR & _).
  set (F := lf_F cx) in *. set (FF := frame_addr ly3 1 fpos) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (tv := c_p cx + lm_k m + 1).
  assert (R9 : getr regs 9 = w64 F) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R27 : getr regs 27 = w64 SB) by (rewrite (KR0 27%bv ltac:(cbv; tauto)); exact C27).
  assert (R23 : getr regs 23 = w64 1) by (rewrite (KR0 23%bv ltac:(cbv; tauto)); exact C23).
  assert (R20' : getr regs 20 = w64 tv) by (rewrite (KR0 20%bv ltac:(cbv; tauto)); exact R20).
  assert (R6' : getr regs 6 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KR0 6%bv ltac:(cbv; tauto)); exact R6).
  assert (R25' : getr regs 25 = w64 t) by (rewrite (KR0 25%bv ltac:(cbv; tauto)); exact R25).
  assert (P1 : 2 ^ 46 <= F) by (unfold YCfn.LLVMF_STK in *; lia).
  assert (P2 : F + 216 <= 2 ^ 47) by lia.
  assert (P3 : awr W mem F 216) by (intros o Ho; apply HAWR; lia).
  assert (P4 : 4096 <= tv <= 140737479966720) by (unfold tv; lia).
  assert (P5 : tv + 1 <= F) by (unfold tv, YCfn.LLVMF_STK in *; lia).
  assert (Ht64 : 0 <= t < 2 ^ 64) by (unfold OPS_MAX in Ht; lia).
  destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hmore | Hmore].
  - (* in.n > 0 after the op byte: the id is in.p[0] *)
    set (idv := in_byte cx (lm_k m + 1)).
    assert (P6 : true = true -> val_mem segs (arm W mem) tv 1 idv /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n).
    { intros _. split; [unfold tv, idv; replace (c_p cx + lm_k m + 1) with (c_p cx + (lm_k m + 1)) by lia;
        exact (gp0_byte cx ly3 S3 W mem (lm_k m + 1) Hnlen HIN ltac:(lia))|].
      exists (c_p cx), (c_n cx). split; [exact Hin|]. unfold tv. lia. }
    destruct (gp0_entry_x W ly3 S3 mem md regs true idv F tv HAR R9 R20' R23 R27
      P1 P2 HF32 P3 P4 P5 (gp0_in_byte_rng cx (lm_k m + 1)) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra idv))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra idv)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E20 : ew E 20 = Z_to_bv 64 tv) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20').
    assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6').
    assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25').
    assert (E32 : ew E 32 = Z_to_bv 64 idv)
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    (* 0x849a0 sd s9,88(s1) *)
    paj_run_tok_x RUN HS HJ SHOK gp0_Bspan.
    { gp0_awr U9. }
    (* 0x849a4 beqz t1: not taken, t1 = in.n - k - 1 > 0 *)
    psrr_branch_tok RUN BR HS SHOK gp0_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 6 _ E6), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + (* 0x849a8-0x849d0: the trap (not taken), the instrumented check of in.p[0], the cursor, s5 = in.p[0] *)
      paj_run_to_tok_x RUNTO HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
      { intros a Ha Hna Hnt Hnb.
        rewrite (aview_kept_out _ _ _ _ _ HFr0 a Ha); [| gp0_nowr U9 Hna Hnt Hnb].
        apply (aview_kept_out _ _ _ _ _ HFr a Ha). gp0_nowr U9 Hna Hnt Hnb. }
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
      { intros a Hw. apply (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a);
          [intros Hp; exact (gp0_pres_grows W _ _ a HGr Hp)|].
        apply (writable_kept (w_H W) mem (ms_mem ms) a); [intros Hp; exact (gp0_pres_grows W _ _ a HG0 Hp) | exact Hw]. }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> abyte_kept W mem W (ms_mem ms0) a)
        by (intros a Ha Hna Hnt Hnb; split; [exact (K1 a Ha Hna Hnt Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
      assert (SV88 : sv8 W (ms_mem ms0) (F + 88) t).
      { unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 88 8%N (SOff 25 0) t RG1) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV16 : sv8 W (ms_mem ms0) (F + 16) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with (tv + 1)
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 16 8%N (SOff 20 1) (tv + 1) RG0) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E20, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms0) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with (c_n cx - lm_k m - 1 + -1)
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 144 8%N (SOff 6 (-1)) (c_n cx - lm_k m - 1 + -1) RG2) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E6, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs (gp0_extra idv)) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      destruct (gp0_kregs cx FF regsD (ms_regs ms0) KK HCOM) as (KRG & Q24 & Q26).
      (* s5 = in.p[0] (atom 32) *)
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply SRr_ret. exists m.
      apply (gp0_close_x cx t m W mem (ms_mem ms0) md _ (ms_regs ms0) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HNP3 HLS HRI HOP KEEP WK SV16 SV144 SV88 KRG Q24 Q26).
      rewrite Q21. cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite ?E32, ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
      unfold gn_id, gn_more. destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [_ | Hlt]; [reflexivity | lia].
  - (* in.n = 0 after the op byte: fuzz_u8 gives 0 and consumes nothing *)
    assert (P6 : false = true -> val_mem segs (arm W mem) tv 1 0 /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n) by discriminate.
    destruct (gp0_entry_x W ly3 S3 mem md regs false 0 F tv HAR R9 R20' R23 R27
      P1 P2 HF32 P3 P4 P5 ltac:(lia) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra 0))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra 0)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E20 : ew E 20 = Z_to_bv 64 tv) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20').
    assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6').
    assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25').
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    (* 0x849a0 sd s9,88(s1) *)
    paj_run_tok_x RUN HS HJ SHOK gp0_Bspan.
    { gp0_awr U9. }
    (* 0x849a4 beqz t1: taken, t1 = 0 *)
    psrr_branch_tok RUN BR HS SHOK gp0_Bspan.
    + (* 0x846e0-0x846ec: F+40 = in.p, F+144 = 0, s5 = 0, s4 = &g_s[0] *)
      paj_run_to_tok_x RUNTO HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
      { intros a Ha Hna Hnt Hnb.
        rewrite (aview_kept_out _ _ _ _ _ HFr0 a Ha); [| gp0_nowr U9 Hna Hnt Hnb].
        apply (aview_kept_out _ _ _ _ _ HFr a Ha). gp0_nowr U9 Hna Hnt Hnb. }
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
      { intros a Hw. apply (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a);
          [intros Hp; exact (gp0_pres_grows W _ _ a HGr Hp)|].
        apply (writable_kept (w_H W) mem (ms_mem ms) a); [intros Hp; exact (gp0_pres_grows W _ _ a HG0 Hp) | exact Hw]. }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> abyte_kept W mem W (ms_mem ms0) a)
        by (intros a Ha Hna Hnt Hnb; split; [exact (K1 a Ha Hna Hnt Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
      assert (SV88 : sv8 W (ms_mem ms0) (F + 88) t).
      { unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 88 8%N (SOff 25 0) t RG1) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV16 : sv8 W (ms_mem ms0) (F + 16) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with tv
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 16 8%N (SOff 20 0) tv RG0) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms0) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with 0
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 144 8%N (SLit 0) 0 RG2) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs (gp0_extra 0)) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      destruct (gp0_kregs cx FF regsD (ms_regs ms0) KK HCOM) as (KRG & Q24 & Q26).
      (* s5 = 0 *)
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply SRr_ret. exists m.
      apply (gp0_close_x cx t m W mem (ms_mem ms0) md _ (ms_regs ms0) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HNP3 HLS HRI HOP KEEP WK SV16 SV144 SV88 KRG Q24 Q26).
      rewrite Q21. unfold gn_id, gn_more.
      destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hlt | _]; [lia | reflexivity].
    + (* 0x849a4 beqz t1 not taken: t1 = in.n - k - 1 = 0, no such state *)
      exfalso. rewrite branch_eq_U, (U_atom E 6 _ E6), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
Qed.
(* @@ END gp0 *)
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twins of this phase over the R cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (Section gR), as SRrG walks with the G runs.  Strict text above
   unchanged. ---- *)
Section gp0R.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (PI := PB_fr) (R := R).

Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.

Lemma gp0_close_xR : forall cx t m (W : world segs) mem mem' md md' regs' ly3 S3 k fpos,
  LFB0 cx ->
  AR0 ly3 S3 W mem md ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem' md' k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> NP S3 -> LSx cx t m ly3 S3 -> RINV cx t m -> gn_op cx t m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 16 <= a < lf_F cx + 24) -> ~ (lf_F cx + 88 <= a < lf_F cx + 96) ->
     ~ (lf_F cx + 144 <= a < lf_F cx + 152) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  sv8 W mem' (lf_F cx + 16) (c_p cx + gn_kq cx m) -> sv8 W mem' (lf_F cx + 144) (c_n cx - gn_kq cx m) ->
  sv8 W mem' (lf_F cx + 88) t ->
  gn_kregs B cx (frame_addr ly3 1 fpos) regs' ->
  getr regs' 24 = w64 (SB + frame_addr ly3 1 fpos / 8) -> getr regs' 26 = w64 HI_G_NOUT ->
  getr regs' 21 = w64 (gn_id cx m) ->
  GJN_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m W
    (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_gn_join)) mem' (seg_rom segs)) md').
Proof.
  intros cx t m W mem mem' md md' regs' ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HJT HSEP HNP HLS HRI HOP KEEP WK
    SV16 SV144 SV88 KR R24 R26 R21.
  destruct (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly3 S3 W mem' md'
              k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR').
  pose proof HB as (_ & HPRE). pose proof HPRE as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof gk_ceil_lo as HCL. pose proof HERR as (HE0 & HE1).
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; apply KEEP; unfold GK_CEIL8, YCfn.LLVMF_STK in *; lia).
  unfold GJN_x. exists regs', mem', md', ly3, S3, k, fpos.
  split; [reflexivity|].
  split.
  { unfold gcom_x. split; [exact HJ|].
    split.
    { apply gframe_of_aframe. apply (gp0_aframe_kept cx _ W W mem mem' HFR KEEP WK);
        unfold GK_CEIL8, SB, YCfn.LLVMF_STK in *; lia. }
    split.
    { apply (gk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KL.
      unfold GK_CEIL8 in *. lia. }
    split; [exact SV16|]. split; [exact SV144|]. split; [exact SV88|].
    split; [exact (gk_ainput_kept_x B ARx LAWS BLKN cx ly3 S3 W mem md W mem' HAR HIN (eq_sym Hnlen) KL)|].
    split; [exact (gk_rom_kept W W mem mem' HRV KL)|].
    exact (gk_jt_kept W W mem mem' HJT KL). }
  split; [exact (gk_amodel_kept_x B ARx LAWS BLKN ly3 S3 W mem md W mem' m HAR HMOD HE0 HE1 KL)|].
  split; [exact HSEP|]. split; [exact HNP|]. split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|].
  split; [exact KR|]. split; [exact R24|]. split; [exact R26 | exact R21].
Qed.

Lemma gp0_entry_join_xR : forall cx t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 5 cx [] t W c ->
  YA0nH.SRrG segs R W c (fun W' c' => exists m, GJN_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m W' c').
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP3 & HRI
                   & HR).
  hp0gR HJ.
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as (HCOM & R25 & Ht & Hk & HO & R11 & HPK).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  (* the operation is 5: not a picking one, so s4 = in.p + k + 1, t1 = in.n - k - 1 (the cursor after the op byte) *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 5).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 5) with false in HPK. cbv iota in HPK.
  destruct HPK as (R20 & R6 & R21).
  assert (HOP : gn_op cx t m) by (split; [exact Hop | split; [exact HO | split; [exact Ht | exact Hk]]]).
  destruct (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly3 S3 W mem md
              k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HIN as [[(Hn0 & _) | (Hn & Hin)] HIG]; [lia|].
  destruct (al0_blocks B ARx LAWS BLKN ly3 S3 W mem md (c_p cx) (c_n cx) HAR Hin)
    as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _).
  pose proof (asan_consts) as (C1c & C2c & C3c & C4c & C5c).
  assert (Hreq : c_n cx <= req_size (c_n cx)) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  pose proof HFR as (HSV & HAWR & _).
  set (F := lf_F cx) in *. set (FF := frame_addr ly3 1 fpos) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (tv := c_p cx + lm_k m + 1).
  assert (R9 : getr regs 9 = w64 F) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R27 : getr regs 27 = w64 SB) by (rewrite (KR0 27%bv ltac:(cbv; tauto)); exact C27).
  assert (R23 : getr regs 23 = w64 1) by (rewrite (KR0 23%bv ltac:(cbv; tauto)); exact C23).
  assert (R20' : getr regs 20 = w64 tv) by (rewrite (KR0 20%bv ltac:(cbv; tauto)); exact R20).
  assert (R6' : getr regs 6 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KR0 6%bv ltac:(cbv; tauto)); exact R6).
  assert (R25' : getr regs 25 = w64 t) by (rewrite (KR0 25%bv ltac:(cbv; tauto)); exact R25).
  assert (P1 : 2 ^ 46 <= F) by (unfold YCfn.LLVMF_STK in *; lia).
  assert (P2 : F + 216 <= 2 ^ 47) by lia.
  assert (P3 : awr W mem F 216) by (intros o Ho; apply HAWR; lia).
  assert (P4 : 4096 <= tv <= 140737479966720) by (unfold tv; lia).
  assert (P5 : tv + 1 <= F) by (unfold tv, YCfn.LLVMF_STK in *; lia).
  assert (Ht64 : 0 <= t < 2 ^ 64) by (unfold OPS_MAX in Ht; lia).
  destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hmore | Hmore].
  - (* in.n > 0 after the op byte: the id is in.p[0] *)
    set (idv := in_byte cx (lm_k m + 1)).
    assert (P6 : true = true -> val_mem segs (arm W mem) tv 1 idv /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n).
    { intros _. split; [unfold tv, idv; replace (c_p cx + lm_k m + 1) with (c_p cx + (lm_k m + 1)) by lia;
        exact (gp0_byte cx ly3 S3 W mem (lm_k m + 1) Hnlen HIN ltac:(lia))|].
      exists (c_p cx), (c_n cx). split; [exact Hin|]. unfold tv. lia. }
    destruct (gp0_entry_x W ly3 S3 mem md regs true idv F tv HAR R9 R20' R23 R27
      P1 P2 HF32 P3 P4 P5 (gp0_in_byte_rng cx (lm_k m + 1)) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra idv))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra idv)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E20 : ew E 20 = Z_to_bv 64 tv) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20').
    assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6').
    assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25').
    assert (E32 : ew E 32 = Z_to_bv 64 idv)
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    (* 0x849a0 sd s9,88(s1) *)
    paj_run_tok_xR RUNG HS HJ SHOK gp0_Bspan.
    { gp0_awr U9. }
    (* 0x849a4 beqz t1: not taken, t1 = in.n - k - 1 > 0 *)
    psrr_branch_tok RUNG BRR HS SHOK gp0_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 6 _ E6), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + (* 0x849a8-0x849d0: the trap (not taken), the instrumented check of in.p[0], the cursor, s5 = in.p[0] *)
      paj_run_to_tok_xR RUNTOG HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
      { intros a Ha Hna Hnt Hnb.
        rewrite (aview_kept_out _ _ _ _ _ HFr0 a Ha); [| gp0_nowr U9 Hna Hnt Hnb].
        apply (aview_kept_out _ _ _ _ _ HFr a Ha). gp0_nowr U9 Hna Hnt Hnb. }
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
      { intros a Hw. apply (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a);
          [intros Hp; exact (gp0_pres_grows W _ _ a HGr Hp)|].
        apply (writable_kept (w_H W) mem (ms_mem ms) a); [intros Hp; exact (gp0_pres_grows W _ _ a HG0 Hp) | exact Hw]. }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> abyte_kept W mem W (ms_mem ms0) a)
        by (intros a Ha Hna Hnt Hnb; split; [exact (K1 a Ha Hna Hnt Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
      assert (SV88 : sv8 W (ms_mem ms0) (F + 88) t).
      { unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 88 8%N (SOff 25 0) t RG1) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV16 : sv8 W (ms_mem ms0) (F + 16) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with (tv + 1)
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 16 8%N (SOff 20 1) (tv + 1) RG0) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E20, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms0) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with (c_n cx - lm_k m - 1 + -1)
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 144 8%N (SOff 6 (-1)) (c_n cx - lm_k m - 1 + -1) RG2) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E6, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs (gp0_extra idv)) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      destruct (gp0_kregs cx FF regsD (ms_regs ms0) KK HCOM) as (KRG & Q24 & Q26).
      (* s5 = in.p[0] (atom 32) *)
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply (YA0nH.SRrG_ret _ R R_refl). exists m.
      apply (gp0_close_xR cx t m W mem (ms_mem ms0) md _ (ms_regs ms0) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HNP3 HLS HRI HOP KEEP WK SV16 SV144 SV88 KRG Q24 Q26).
      rewrite Q21. cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite ?E32, ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
      unfold gn_id, gn_more. destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [_ | Hlt]; [reflexivity | lia].
  - (* in.n = 0 after the op byte: fuzz_u8 gives 0 and consumes nothing *)
    assert (P6 : false = true -> val_mem segs (arm W mem) tv 1 0 /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n) by discriminate.
    destruct (gp0_entry_x W ly3 S3 mem md regs false 0 F tv HAR R9 R20' R23 R27
      P1 P2 HF32 P3 P4 P5 ltac:(lia) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra 0))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra 0)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E20 : ew E 20 = Z_to_bv 64 tv) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20').
    assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6').
    assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25').
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    (* 0x849a0 sd s9,88(s1) *)
    paj_run_tok_xR RUNG HS HJ SHOK gp0_Bspan.
    { gp0_awr U9. }
    (* 0x849a4 beqz t1: taken, t1 = 0 *)
    psrr_branch_tok RUNG BRR HS SHOK gp0_Bspan.
    + (* 0x846e0-0x846ec: F+40 = in.p, F+144 = 0, s5 = 0, s4 = &g_s[0] *)
      paj_run_to_tok_xR RUNTOG HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
      { intros a Ha Hna Hnt Hnb.
        rewrite (aview_kept_out _ _ _ _ _ HFr0 a Ha); [| gp0_nowr U9 Hna Hnt Hnb].
        apply (aview_kept_out _ _ _ _ _ HFr a Ha). gp0_nowr U9 Hna Hnt Hnb. }
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
      { intros a Hw. apply (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a);
          [intros Hp; exact (gp0_pres_grows W _ _ a HGr Hp)|].
        apply (writable_kept (w_H W) mem (ms_mem ms) a); [intros Hp; exact (gp0_pres_grows W _ _ a HG0 Hp) | exact Hw]. }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> abyte_kept W mem W (ms_mem ms0) a)
        by (intros a Ha Hna Hnt Hnb; split; [exact (K1 a Ha Hna Hnt Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
      assert (SV88 : sv8 W (ms_mem ms0) (F + 88) t).
      { unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 88 8%N (SOff 25 0) t RG1) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV16 : sv8 W (ms_mem ms0) (F + 16) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with tv
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 16 8%N (SOff 20 0) tv RG0) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms0) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with 0
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 144 8%N (SLit 0) 0 RG2) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs (gp0_extra 0)) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      destruct (gp0_kregs cx FF regsD (ms_regs ms0) KK HCOM) as (KRG & Q24 & Q26).
      (* s5 = 0 *)
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply (YA0nH.SRrG_ret _ R R_refl). exists m.
      apply (gp0_close_xR cx t m W mem (ms_mem ms0) md _ (ms_regs ms0) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HNP3 HLS HRI HOP KEEP WK SV16 SV144 SV88 KRG Q24 Q26).
      rewrite Q21. unfold gn_id, gn_more.
      destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hlt | _]; [lia | reflexivity].
    + (* 0x849a4 beqz t1 not taken: t1 = in.n - k - 1 = 0, no such state *)
      exfalso. rewrite branch_eq_U, (U_atom E 6 _ E6), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
Qed.

End gp0R.

End gp0.

