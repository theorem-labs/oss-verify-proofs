(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's phase p2 on image B (lib/B/W_LLVMFuzzerTestOneInput_gone_p2.v,
   a Theorem Labs lane's, fee5272ac13: the relay_reads loop, GL1 to GRG), for the conversion of ARM_gone to the cut invariants of
   lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.  _gone_p2.v is not edited.
   - CITED from _gone_p2.v: its AR-free names (the run states, g2_azs_sub, g2_slot_open, g2_reads_*, g2_abk_*,
     g2_cs_pres, g2_prefix_kept, g2_gframe_kept, ...), with the Section variables they were generalized over;
   - RESTATED over ARx at the ghost list []: B's own steps (image B calls relay_reads out of line, image A inlines it):
     g2_mid / g2_head (the call, through cut_x's RRDS_x and base_x's gn_afn_pre_x, the callee's journal lifted by
     W_journal_x's ajournal_gx_G_mono_x / ajournal_gx_sub_x), g2_tail_post / g2_tail (the store), g2_step (tk_x's kept
     lemmas), and, merged per item with SmallX's image-A twin lib/A/W_LLVMFuzzerTestOneInput_gone_p2_x.v (95a5de32ab2),
     g2_loop and the phase lemma gp2_l1_rig.
   Section hypotheses beyond cut_x's header: HZS / HERR verbatim (AR-free), cut_x's RRDS_x, BLKN (as on image A). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_p2.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_p2.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the phase's own address *)
(* @@ SECTION gp2aux *)
Section gp2aux.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED Variable B *)
Variable B : asyms.

(* zero-shadow ranges, narrowed (A's p2 g2_azs_sub) *)
(* @@ RESOLVED Lemma g2_azs_sub *)
Local Notation g2_azs_sub := (W_LLVMFuzzerTestOneInput_gone_p2.g2_azs_sub B).
(* @@ END gp2aux *)
End gp2aux.

(* ------------------------------------------------------------------ the entry states of the two runs *)
(* @@ MERGED Ltac g2_reg *)
Ltac g2_reg HS r H :=
  pose proof (st_ok_pi_restrict_reg (PI := PB_fr) _ _ _ _ (r : bv 5) HS) as H;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) (r : bv 5)) in
    change (sr_get (ss_regs ss) (r : bv 5)) with e in H end;
  cbn [ms_regs restrict mkst] in H.
(* @@ MERGED Ltac g2_U *)
Ltac g2_U := apply bv_eq;
  lazymatch goal with |- bv_unsigned (sv_denot ?Ev ?e) = _ =>
    change (bv_unsigned (sv_denot Ev e)) with (U Ev e) end.
(* a register the tail bumped by a constant *)
(* @@ SECTION gp2 *)
Section gp2.
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
(* g_s lies in the instance's zero-shadow ranges: the base's model obligation, verbatim (the shadow byte of
   g_s[q].open at 0x84af8 is 0, so the slow path 0x84b30 and the report 0x85134 are not reached) *)
(* @@ RESOLVED Hypothesis HZS *)
Hypothesis HZS : GN_HZS B.
(* errno's place: the base's model obligation, verbatim (amodel_at's aout_at reads errno across the call) *)
(* @@ HDR-CITED-IN-AX Hypothesis HERR *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* relay_reads (0x864e8): the cut's RRDS (lib/B/W_LLVMFuzzerTestOneInput_cut.v:707 at 61da015af91), text verbatim *)
(* @@ B-ONLY-AR[afn_pre,aleafx_post] Hypothesis RRDS *)
(* relay_reads (0x864e8): cut_x's Section hypothesis RRDS_x (W_LLVMFuzzerTestOneInput_cut_x.v:580), verbatim *)
Hypothesis RRDS_x : forall W ly S Hp (regs : bvmap 5 word) mem md ch T es HA h,
  afn_pre_x segs B ARx RRDS_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
  asrc_at B ly S W mem HA h ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
    (aleafx_post_x B PST ARx RRDS_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
            a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
         ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
(* @@ AX-ONLY Hypothesis BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* @@ RESTATED-LOCAL Let RUN *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ RESTATED-LOCAL Let RUNTO *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ RESTATED-LOCAL Let BR *)
Let BR := paj_branch (PI := PB_fr).

(* a run over read-only regions leaves the memory as it was *)
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
(* _gone_p2.v's AR-free items that take a section argument, cited with it *)
(* @@ B-ONLY-HDR Ltac g2_mem *)
Ltac g2_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* ------------------------------------------------------------------ 0x84af8 -> 0x84b10: the open test and,
   for an open slot, relay_reads(&g_s[q]).  The post is the state at the return site, with a0 = reads[q]. *)
(* @@ B-ONLY-AR[ajournal_gx] Definition g2_mid *)
Definition g2_mid (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (v : Z) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk',
    c' = cfg_at segs (fr_B0 + AF_gn_st) regs' mem' md' /\
    AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W' mem' md' kk' /\
    (forall r, In r G2_CS -> getr regs' r = getr regs r) /\
    getr regs' 25 = getr regs 25 /\ getr regs' 10 = w64 v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - RRDS_STK <= a < lf_F cx) -> abyte_kept W mem W' mem' a).

(* @@ B-ONLY-AR[LAWS,LSx,RUN,RUNTO,ajournal_gx,ajournal_gx_G_mono,ajournal_gx_sub,lf_base,paj_run] Lemma g2_head *)
Lemma g2_head : forall cx (q : nat) m fpos ly S kk (W : world segs) regs mem md,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  amodel_at B ly S W mem m -> rom_view segs W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) ->
  getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) ->
  getr regs 27 = w64 SB ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_l1) regs mem md)
    (g2_mid cx fpos ly S (gn_reads m q) W regs mem).
Proof.
  intros cx q m fpos ly S kk W regs mem md HB HJ HSV HMOD HROM Hq R2 R3 R4 R8 R20 R22 R25 R27.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S W mem md kk fpos
                HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  assert (HD2lo : 0 <= (rg_s fr_RG + 4) / 8) by (apply Z.div_pos; lia).
  assert (HD2hi : (rg_s fr_RG + 4) / 8 <= rg_s fr_RG + 4) by (apply Z.div_le_upper_bound; lia).
  set (open := g2_sopen (nth q (lm_hs m) None)) in *.
  pose proof HMOD as (Hlen4 & HSL & HREL & _).
  pose proof (g2_slot_open B ly S W mem q (nth q (lm_hs m) None) (HSL q ltac:(lia))) as Mopen.
  assert (Hopen01 : 0 <= open <= 1) by (unfold open, g2_sopen; destruct (nth q (lm_hs m) None); lia).
  assert (HZSA : azs B (rg_s fr_RG + ASRC * Z.of_nat q + 4) 8)
    by (apply (g2_azs_sub B (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | lia]).
  (* RRDS's shadow premise (cut 61da015af91): g_s[q]'s first four bytes, a sub-range of GN_HZS *)
  assert (HZS4 : azs B (rg_s fr_RG + ASRC * Z.of_nat q) 4)
    by (apply (g2_azs_sub B (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | lia]).
  assert (HSH : (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q = (rg_s fr_RG + ASRC * Z.of_nat q + 4) / 8)
    by (rewrite (g2_shift q Hq); reflexivity).
  set (A := rg_s fr_RG + ASRC * Z.of_nat q) in *.
  assert (HAe : A = 6131296 + 96 * Z.of_nat q) by (unfold A; rewrite HRS, HAS; reflexivity).
  assert (HA32 : A mod 32 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q) with ((191603 + 3 * Z.of_nat q) * 32) by lia;
        apply Z_mod_mult).
  assert (HA8 : A mod 8 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q) with ((766412 + 12 * Z.of_nat q) * 8) by lia;
        apply Z_mod_mult).
  assert (HA4 : (A + 4) mod 4 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q + 4) with ((1532825 + 24 * Z.of_nat q) * 4) by lia;
        apply Z_mod_mult).
  assert (HDlo : 0 <= (A + 4) / 8) by (apply Z.div_pos; lia).
  assert (HDhi : (A + 4) / 8 <= A + 4) by (apply Z.div_le_upper_bound; lia).
  assert (R25A : getr regs 25 = w64 (SB + (A + 4) / 8)) by (rewrite R25; unfold w64; f_equal; lia).
  (* the entry state *)
  remember (Eimg (Ereg regs (g2_x_head open))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (g2_x_head open)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (A + 4)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E22 : ew E 22 = Z_to_bv 64 A) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 open)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U20 : bv_unsigned (ew E 20) = A + 4) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = A) by (rewrite E22; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite E27; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = open) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_g2_head
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_l1)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_g2_head. apply pa_entry_st_ok_full.
    - unfold g2_sr_head. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]; rewrite <- HE.
      rewrite R25A. symmetry. apply bv_eq.
      change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))))
        with (U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
      rewrite (g2_USH E A E27 E20 ltac:(lia) ltac:(lia)).
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - vm_compute. reflexivity.
    - unfold g2_rg_head. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ A 4 4 (SOff 32 0) open);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact Mopen.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_head f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U20, U22, U27, U32.
      change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end;
        first [lia | exact HA4 | exact HA32 | reflexivity]. }
  assert (HBx : U E g2_Bx = SHADOW_OFF).
  { unfold U, g2_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity. }
  assert (UA20 : U E (SOff 20 0) = A + 4).
  { unfold U. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity. }
  assert (SHOK : sh_ok segs g2_Bx g2_SH_head E (mrestrict (w_H W) mem)).
  { unfold sh_ok, g2_SH_head. constructor; [|constructor].
    eapply shent_ok_of_range.
    - exact (azs_range_addressable_x B ARx LAWS ly S [] W mem md (A + 4) 8 HAR HZSA).
    - exact HBx.
    - exact UA20.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. lia. }
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_l1)) with (Z_to_bv 64 (BASE + AF_gn_l1)).
  (* 0x84af8-0x84b00: the shadow byte (0), the slow-path test (not taken), g_s[q].open *)
  paj_run_tok_x RUN HS HJ SHOK g2_span.
  { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                         | apply awr_ok_x_nil]. }
  g2_mem HF Em1. clear HF HFr HG0.
  (* 0x84b04 beqz a0: the closed slot, or the call *)
  psrr_branch_tok RUN BR HS SHOK g2_span.
  - (* g_s[q].open = 0: reads[q] = 0, already at 0x84b10 *)
    rewrite branch_eq_U, (U_atom E 32 open E32), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    assert (Hnone : nth q (lm_hs m) None = None).
    { unfold open, g2_sopen in Hc. destruct (nth q (lm_hs m) None) as [h|]; [lia | reflexivity]. }
    assert (Hr0 : gn_reads m q = 0) by (unfold gn_reads; rewrite Hnone; reflexivity).
    (* 0x84b04 -> 0x84b10 *)
    paj_run_to_tok_x RUNTO HS HJ SHOK g2_span AF_gn_st.
    { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                           | apply awr_ok_x_nil]. }
    g2_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (g2_x_head open)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (10%bv : bv 5) Q10. g2_reg HS (25%bv : bv 5) Q25.
    assert (Q25v : getr (ms_regs ms0) 25 = w64 (SB + (A + 4) / 8)).
    { rewrite Q25. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (g2_USH Ev A ltac:(rewrite ?ew_ewset_other by lia; exact E27)
                               ltac:(rewrite ?ew_ewset_other by lia; exact E20)
                               ltac:(lia) ltac:(lia)) end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    assert (Q10v : getr (ms_regs ms0) 10 = w64 (gn_reads m q)).
    { rewrite Q10, Hr0. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (U_atom Ev 32 open ltac:(rewrite ?ew_ewset_other by lia; exact E32)) by lia end.
      unfold open, g2_sopen. rewrite Hnone. unfold w64.
      rewrite unsigned_lit_small by lia. reflexivity. }
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. unfold g2_mid.
    lazymatch goal with |- exists _ _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
      exists r, mm, d, kk end.
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)); reflexivity|].
    split; [exact HJ|]. split; [exact KR|].
    split; [rewrite Q25v, R25A; reflexivity|].
    split; [exact Q10v|].
    intros a Ha Hno. apply g2_abk_refl.
  - (* g_s[q].open <> 0: the slot is open, and relay_reads(&g_s[q]) is called *)
    rewrite branch_eq_U, (U_atom E 32 open E32), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (Hsome : exists h, nth q (lm_hs m) None = Some h).
    { unfold open, g2_sopen in Hc. destruct (nth q (lm_hs m) None) as [h|]; [exists h; reflexivity | lia]. }
    destruct Hsome as (h & Hsome).
    assert (HSRC : asrc_at B ly S W mem A h)
      by (pose proof (HSL q ltac:(lia)) as HSLq; rewrite Hsome in HSLq; exact HSLq).
    (* 0x84b08-0x84b0c: a0 = &g_s[q], jal relay_reads *)
    paj_run_to_tok_x RUNTO HS HJ SHOK g2_span AF_fr_relay_reads.
    { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                           | apply awr_ok_x_nil]. }
    g2_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (g2_x_head open)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. g2_reg HS (10%bv : bv 5) Q10. g2_reg HS (25%bv : bv 5) Q25.
    assert (Q25v : getr (ms_regs ms0) 25 = w64 (SB + (A + 4) / 8)).
    { rewrite Q25. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (g2_USH Ev A ltac:(rewrite ?ew_ewset_other by lia; exact E27)
                               ltac:(rewrite ?ew_ewset_other by lia; exact E20)
                               ltac:(lia) ltac:(lia)) end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    assert (Q10v : getr (ms_regs ms0) 10 = w64 A).
    { rewrite Q10. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (U_atom Ev 22 A ltac:(rewrite ?ew_ewset_other by lia; exact E22)) by lia end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
      set (rc0 := r) in *; set (mdc := d) in * end.
    assert (Hsp1 : spZ rc0 = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(cbv [G2_CS In]; tauto)), R2. unfold w64.
      apply unsigned_lit_small. lia. }
    destruct (gn_afn_pre_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV
                cx ly S fpos kk W mem mdc rc0 RRDS_STK HB HJ HSV Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(cbv [G2_CS In]; tauto)). exact R3. }
    { rewrite (KR 4%bv ltac:(cbv [G2_CS In]; tauto)). exact R4. }
    { rewrite (KR 8%bv ltac:(cbv [G2_CS In]; tauto)). exact R8. }
    { unfold RRDS_STK, RSRC_STK. lia. }
    { unfold RRDS_STK, RSRC_STK. lia. }
    eapply SRr_bind.
    { exact (RRDS_x W ly S [] rc0 mem mdc ch (lm_G m) (lm_es m) A h HPREc Q10v
               ltac:(lia) HA8 HZS4 HSRC HREL HROM). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HKEEP & HA0).
    rewrite Hsp1 in HJc, HKEEP.
    (* relay_reads's journal inside this function's: W2's ajournal_gx_sub_x at G_fr, the callee's lifted from G = [] *)
    assert (HJc' : AJ0 G_fr 0 [] RRDS_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] RRDS_STK (lf_F cx) [] ly S [] W mem mdc []
                ly S [] W2 mem2 md2 0 _ HJc).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
       (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
       RRDS_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJc'
       ltac:(unfold RRDS_STK, RSRC_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply SRr_ret. unfold g2_mid.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1;
            change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)); reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (g2_cs_pres rc0 regs2 HP2 r ltac:(right; exact Hr)); exact (KR r Hr)|].
    split; [rewrite (g2_cs_pres rc0 regs2 HP2 25%bv ltac:(left; reflexivity)), R25A; exact Q25v|].
    split.
    { rewrite (g2_reads_of_post m q h (getr regs2 10) Hsome HA0). reflexivity. }
    exact HKEEP.
Qed.

(* ------------------------------------------------------------------ 0x84b10 -> 0x84af8 / 0x84b40: the store of
   reads[q] into the frame cell F + 192 + 4q (no instrumented check: the cell is in the function's stack window),
   the five pointer bumps and the latch *)
(* @@ B-ONLY-AR[ajournal_gx] Definition g2_tail_post *)
Definition g2_tail_post (cx : lfcx) (fpos : Z) (ly : alayout) (Sa : astate) (q : nat) (v : Z)
    (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' kk',
    AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly Sa W mem' md' kk' /\
    (forall r, In r G2_K2 -> getr regs' r = getr regs r) /\
    val_mem segs (arm W mem') (lf_F cx + 192 + 4 * Z.of_nat q) 4 v /\
    (forall a, 0 <= a < 2 ^ 64 ->
       ~ (lf_F cx + 192 + 4 * Z.of_nat q <= a < lf_F cx + 192 + 4 * Z.of_nat q + 4) ->
       abyte_kept W mem W mem' a) /\
    (* the store cell stays writable too (every byte's writability is kept: the runs only grow presence) *)
    (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) /\
    getr regs' 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat (S q) + 4) /\
    getr regs' 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat (S q)) /\
    getr regs' 23 = w64 (4 - Z.of_nat (S q)) /\
    getr regs' 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat (S q)) /\
    getr regs' 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat (S q)) /\
    (((S q < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_l1) regs' mem' md') \/
     ((S q) = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_rig) regs' mem' md')).

(* @@ B-ONLY-AR[RUN,RUNTO,ajournal_gx,paj_run] Lemma g2_tail *)
Lemma g2_tail : forall cx (q : nat) fpos ly Sa kk (W : world segs) regs mem md v,
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly Sa W mem md kk ->
  (q < 4)%nat -> 0 <= v <= 1 ->
  2 ^ 46 <= lf_F cx -> lf_F cx + 216 <= 2 ^ 47 -> lf_F cx mod 32 = 0 ->
  spZ (c_regs cx) - LLVMF_STK <= lf_F cx + 192 -> lf_F cx + 208 <= spZ (c_regs cx) ->
  awr W mem (lf_F cx + 192) 16 ->
  getr regs 10 = w64 v ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) ->
  getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 23 = w64 (4 - Z.of_nat q) ->
  getr regs 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) ->
  getr regs 27 = w64 SB ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_st) regs mem md) (g2_tail_post cx fpos ly Sa q v W regs mem).
Proof.
  intros cx q fpos ly Sa kk W regs mem md v HJ Hq Hv HF1 HF2 HF32 Hs1 Hs2 HW R10 R20 R22 R23 R24 R25 R27.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  assert (HD2lo : 0 <= (rg_s fr_RG + 4) / 8) by (apply Z.div_pos; lia).
  assert (HD2hi : (rg_s fr_RG + 4) / 8 <= rg_s fr_RG + 4) by (apply Z.div_le_upper_bound; lia).
  set (cell := lf_F cx + 192 + 4 * Z.of_nat q) in *.
  assert (Hce : cell = lf_F cx + 192 + 4 * Z.of_nat q) by reflexivity.
  assert (Hc4 : cell mod 4 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D.
    replace cell with ((8 * (lf_F cx / 32) + 48 + Z.of_nat q) * 4) by lia. apply Z_mod_mult. }
  remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q + 4))
    by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E22 : ew E 22 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q))
    by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E23 : ew E 23 = Z_to_bv 64 (4 - Z.of_nat q)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
  assert (E24 : ew E 24 = Z_to_bv 64 cell) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
  assert (E25 : ew E 25 = Z_to_bv 64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q))
    by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (U10 : bv_unsigned (ew E 10) = v) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = 4 - Z.of_nat q) by (rewrite E23; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = cell) by (rewrite E24; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite E27; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_g2_tail
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_st)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_g2_tail. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold g2_rg_tail. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U24. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil].
      intros o Ho. replace (cell + o) with (lf_F cx + 192 + (4 * Z.of_nat q + o)) by lia.
      apply HW. lia.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_tail f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U10, U23, U24, U27.
      change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [lia | exact Hc4 | reflexivity]. }
  assert (SHOK : sh_ok segs g2_Bx (@nil shent) E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)).
  (* 0x84b10-0x84b24: the store and the five bumps *)
  paj_run_tok_x RUN HS HJ SHOK g2_span.
  { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24 in Ha.
    left. split; [left; lia | lia]. }
  rename HF into HFst, HFr into HFrst, HG0 into HGst.
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms) a).
  { intros a Ha Hna. split.
    - apply (aview_kept_out _ _ _ _ _ HFrst a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_g2_tail g2_rg_tail In] in Hin.
      destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U24 in Hr. lia.
    - intros Hw. exact (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw). }
  (* 0x84b28 bnez s7: the next slot, or 0x84b2c j 84b40 *)
  psrr_branch_tok RUN BR HS SHOK g2_span.
  - (* 4 - q - 1 <> 0: back to the loop's head *)
    rewrite branch_ne_U, (U_atom_off E 23 _ (-1) ltac:(rewrite ?ew_ewset_other by lia; exact E23)), U_lit
      in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hq1 : (S q < 4)%nat) by lia.
    paj_run_to_tok_x RUNTO HS HJ SHOK g2_span AF_gn_l1.
    { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
      intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite ?ew_ewset_other in Ha by lia. rewrite U24 in Ha.
      left. split; [left; lia | lia]. }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (MV0 : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (cell + 0) (N.to_nat 4) v).
    { lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 24%nat cell _ _ _ _ _ 0 4%N (SOff 10 0) v RG1) end.
      - rewrite ?ew_ewset_other by lia. exact U24.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (MV : val_mem segs (arm W (ms_mem ms0)) cell 4 v)
      by (unfold arm; rewrite Z.add_0_r in MV0; change (N.to_nat 4) with 4%nat in MV0; exact MV0).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms0) a).
    { intros a Ha Hna. apply (g2_abk_trans W W W mem (ms_mem ms) (ms_mem ms0) a (KEEP0 a Ha Hna)).
      split.
      - apply (aview_kept_out _ _ _ _ _ HFr a Ha).
        intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite U24 in Hr; lia.
      - intros Hw. exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0) Hw). }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0)
            (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw))).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (20%bv : bv 5) Q20. g2_reg HS (22%bv : bv 5) Q22. g2_reg HS (23%bv : bv 5) Q23.
    g2_reg HS (24%bv : bv 5) Q24. g2_reg HS (25%bv : bv 5) Q25.
    pmkst HS.
    apply SRr_ret. unfold g2_tail_post. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |}] => exists r, mm, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. split; [exact MV|]. split; [exact KEEP|]. split; [exact WK|].
    split; [g2_off Q20 20%nat 96 E20|].
    split; [g2_off Q22 22%nat 96 E22|].
    split; [g2_off Q23 23%nat (-1) E23|].
    split; [g2_off Q24 24%nat 4 E24|].
    split; [g2_off Q25 25%nat 12 E25|].
    left. split; [exact Hq1|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_l1)) with (Z_to_bv 64 (BASE + AF_gn_l1)). reflexivity.
  - (* 4 - q - 1 = 0: 0x84b2c `j 84b40` *)
    rewrite branch_ne_U, (U_atom_off E 23 _ (-1) ltac:(rewrite ?ew_ewset_other by lia; exact E23)), U_lit
      in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (Hq4 : (S q) = 4%nat) by lia.
    paj_run_to_tok_x RUNTO HS HJ SHOK g2_span AF_gn_rig.
    { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
      intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite ?ew_ewset_other in Ha by lia. rewrite U24 in Ha.
      left. split; [left; lia | lia]. }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (MV0 : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (cell + 0) (N.to_nat 4) v).
    { lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 24%nat cell _ _ _ _ _ 0 4%N (SOff 10 0) v RG1) end.
      - rewrite ?ew_ewset_other by lia. exact U24.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (MV : val_mem segs (arm W (ms_mem ms0)) cell 4 v)
      by (unfold arm; rewrite Z.add_0_r in MV0; change (N.to_nat 4) with 4%nat in MV0; exact MV0).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms0) a).
    { intros a Ha Hna. apply (g2_abk_trans W W W mem (ms_mem ms) (ms_mem ms0) a (KEEP0 a Ha Hna)).
      split.
      - apply (aview_kept_out _ _ _ _ _ HFr a Ha).
        intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite U24 in Hr; lia.
      - intros Hw. exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0) Hw). }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0)
            (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw))).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (20%bv : bv 5) Q20. g2_reg HS (22%bv : bv 5) Q22. g2_reg HS (23%bv : bv 5) Q23.
    g2_reg HS (24%bv : bv 5) Q24. g2_reg HS (25%bv : bv 5) Q25.
    pmkst HS.
    apply SRr_ret. unfold g2_tail_post. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |}] => exists r, mm, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. split; [exact MV|]. split; [exact KEEP|]. split; [exact WK|].
    split; [g2_off Q20 20%nat 96 E20|].
    split; [g2_off Q22 22%nat 96 E22|].
    split; [g2_off Q23 23%nat (-1) E23|].
    split; [g2_off Q24 24%nat 4 E24|].
    split; [g2_off Q25 25%nat 12 E25|].
    right. split; [exact Hq4|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig)). reflexivity.
Qed.

(* the base's gframe across a call window [F - w, F) AND one 4-byte store at lo inside reads[] (F + 192 .. F + 208,
   which no sv8 of gframe names): tk's gk_gframe_kept with the store's cell excluded from the kept bytes and its
   writability given separately (the cell is inside gframe's awr F (sp0 - F)) *)
(* @@ CONFLICT Lemma g2_step *)
Lemma g2_step_x : forall (q : nat) cx t m W c,
  LFB0 cx ->
  GL1_x B NP G_fr fr_FP PST ARx LSx RINV cx t m q W c ->
  SRr segs W c (fun W' c' => GL1_x B NP G_fr fr_FP PST ARx LSx RINV cx t m (S q) W' c' \/
                             GRG_x B NP G_fr fr_FP PST ARx LSx RINV cx t m W' c').
Proof.
  intros q cx t m W c HB HL1.
  destruct HL1 as (regs & mem & md & ly & St & kk & fpos & Hc & HGST & HLS & HRI & HOP & HKR &
                   R26 & R21 & R22 & R20 & R23 & R24 & R25 & Hq & HCELLS & HAWR & HAT & HPRE).
  destruct HGST as (HCOM & HMOD & HSEP & HNP).
  destruct HCOM as (HJ & HFRM & HFL & HP16 & HN144 & HT88 & HIN & HROM & HJT).
  pose proof HKR as (K2 & K8 & K9 & K18 & K19 & K27 & K3 & K4).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly St W mem md
              kk fpos
                HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  pose proof YM05.alloc_ceiling_value as AC. pose proof gk_ceil_lo as HCL0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE2). pose proof HPRE2 as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof HERR as (HE0 & HE1).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (HCEIL : GK_CEIL8 = alloc_ceiling + 8) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HRSTK : RRDS_STK = 32) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (HFFs : 0 <= SB + FF / 8 /\ SB + FF / 8 + 16 <= GK_CEIL8).
  { pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)) as Hd1.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd2. lia. }
  rewrite Hc.
  (* 0x84af8 -> 0x84b10 *)
  eapply SRr_bind.
  { exact (g2_head cx q m fpos ly St kk W regs mem md HB HJ (proj1 HFRM) HMOD HROM Hq
             K2 K3 K4 K8 R20 R22 R25 K27). }
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & K25a & R10a & KP1).
  (* what the call kept *)
  assert (KH : forall a, F <= a < 2 ^ 64 -> abyte_kept W mem W1 mem1 a)
    by (intros a Ha; apply KP1; lia).
  assert (HAWR1 : awr W1 mem1 (F + 192) 16)
    by (apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact HAWR]).
  (* 0x84b10 -> 0x84af8 / 0x84b40 *)
  eapply SRr_bind.
  { apply (g2_tail cx q fpos ly St kk1 W1 regs1 mem1 md1 (gn_reads m q) HJ1 Hq (g2_reads_rng m q));
      [ lia | lia | exact HF32 | lia | lia | exact HAWR1 | exact R10a
      | rewrite (KR1 20%bv ltac:(cbv [G2_CS In]; tauto)); exact R20
      | rewrite (KR1 22%bv ltac:(cbv [G2_CS In]; tauto)); exact R22
      | rewrite (KR1 23%bv ltac:(cbv [G2_CS In]; tauto)); exact R23
      | rewrite (KR1 24%bv ltac:(cbv [G2_CS In]; tauto)); exact R24
      | rewrite K25a; exact R25
      | rewrite (KR1 27%bv ltac:(cbv [G2_CS In]; tauto)); exact K27 ]. }
  intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & kk2 & HJ2 & KR2 & MV & KP2 & WK2 & Q20 & Q22 & Q23 & Q24 & Q25 & Hpc).
  (* the two steps composed *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F - RRDS_STK <= a < F) ->
      ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha Hn1 Hn2; exact (g2_abk_trans W W1 W1 mem mem1 mem2 a (KP1 a Ha Hn1) (KP2 a Ha Hn2))).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha; apply KEEP; lia).
  assert (KHI : forall a, F <= a < 2 ^ 64 ->
      ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha Hn2; apply KEEP; [lia | lia | exact Hn2]).
  (* the cut's facts at the next cut point *)
  assert (HMOD2 : amodel_at B ly St W1 mem2 m)
    by (exact (gk_amodel_kept_x B ARx LAWS BLKN ly St W mem md W1 mem2 m HAR HMOD HE0 ltac:(lia) KL)).
  assert (HIN2 : ainput_at B cx ly St W1 mem2)
    by (exact (gk_ainput_kept_x B ARx LAWS BLKN cx ly St W mem md W1 mem2 HAR HIN (eq_sym Hnlen) KL)).
  assert (HROM2 : rom_view segs W1 mem2) by (exact (gk_rom_kept W W1 mem mem2 HROM KL)).
  assert (HJT2 : jt_rom W1 mem2) by (exact (gk_jt_kept W W1 mem mem2 HJT KL)).
  assert (HFRM2 : gframe cx fake_shadow_open FF W1 mem2).
  { apply (g2_gframe_kept cx fake_shadow_open FF W W1 mem mem2 RRDS_STK (F + 192 + 4 * Z.of_nat q) HFRM eq_refl);
      [ intros a Ha Hn Hcl; apply KEEP; [exact Ha | exact Hn | exact Hcl]
      | intros a Ha Hw; apply WK2; exact (proj2 (KP1 a ltac:(lia) ltac:(lia)) Hw)
      | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia ]. }
  assert (HFL2 : sv8 W1 mem2 (FF + 120) (flag_addr ly 1 fpos))
    by (apply (gk_sv8_kept W W1 mem mem2); [intros x Hx; apply KL; lia | exact HFL]).
  assert (KV8 : forall a v, F <= a -> a + 8 <= 2 ^ 64 ->
      (a + 8 <= F + 192 + 4 * Z.of_nat q \/ F + 192 + 4 * Z.of_nat q + 4 <= a) ->
      sv8 W mem a v -> sv8 W1 mem2 a v)
    by (intros a v H0 H1 H3 Hv; apply (gk_sv8_kept W W1 mem mem2); [|exact Hv];
        intros x Hx; apply KHI; lia).
  assert (HP16' : sv8 W1 mem2 (F + 16) (c_p cx + gn_kq cx m))
    by (apply KV8; [lia | lia | left; lia | exact HP16]).
  assert (HN144' : sv8 W1 mem2 (F + 144) (c_n cx - gn_kq cx m))
    by (apply KV8; [lia | lia | left; lia | exact HN144]).
  assert (HT88' : sv8 W1 mem2 (F + 88) t)
    by (apply KV8; [lia | lia | left; lia | exact HT88]).
  assert (HAT' : sv8 W1 mem2 (F + 208) 0)
    by (apply KV8; [lia | lia | right; lia | exact HAT]).
  assert (HAWR' : awr W1 mem2 (F + 192) 16).
  { intros i Hi. apply WK2. exact (HAWR1 i Hi). }
  assert (HPRE' : gn_prefix_at cx m W1 mem2 FF).
  { apply (g2_prefix_kept cx m W W1 mem mem2 FF HPRE). intros a Ha. apply KL. lia. }
  assert (CELLS : forall j, (j < S q)%nat -> gn_sv4 W1 mem2 (F + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. destruct (Nat.eq_dec j q) as [->|Hne]; [exact MV|].
    apply (akept_vm W mem); [|exact (HCELLS j ltac:(lia))].
    intros x Hx. cbn in Hx. apply KHI; [lia|].
    assert (Hjz : 0 <= Z.of_nat j <= 3) by lia.
    assert (Hjq : Z.of_nat j <> Z.of_nat q) by lia. lia. }
  assert (KREGS : gn_kregs B cx FF regs2).
  { unfold gn_kregs. repeat split;
      first [ rewrite (KR2 2%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 2%bv ltac:(cbv [G2_CS In]; tauto)); exact K2
            | rewrite (KR2 8%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 8%bv ltac:(cbv [G2_CS In]; tauto)); exact K8
            | rewrite (KR2 9%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 9%bv ltac:(cbv [G2_CS In]; tauto)); exact K9
            | rewrite (KR2 18%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 18%bv ltac:(cbv [G2_CS In]; tauto)); exact K18
            | rewrite (KR2 19%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 19%bv ltac:(cbv [G2_CS In]; tauto)); exact K19
            | rewrite (KR2 27%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 27%bv ltac:(cbv [G2_CS In]; tauto)); exact K27
            | rewrite (KR2 3%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 3%bv ltac:(cbv [G2_CS In]; tauto)); exact K3
            | rewrite (KR2 4%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 4%bv ltac:(cbv [G2_CS In]; tauto)); exact K4 ]. }
  assert (R26' : getr regs2 26 = w64 HI_G_NOUT)
    by (rewrite (KR2 26%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 26%bv ltac:(cbv [G2_CS In]; tauto)); exact R26).
  assert (R21' : getr regs2 21 = w64 (gn_id cx m))
    by (rewrite (KR2 21%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 21%bv ltac:(cbv [G2_CS In]; tauto)); exact R21).
  apply SRr_ret.
  destruct Hpc as [(Hq1 & ->) | (Hq4 & ->)].
  - left. exists regs2, mem2, md2, ly, St, kk2, fpos.
    split; [reflexivity|].
    split; [split; [split; [exact HJ2|]; split; [exact HFRM2|]; split; [exact HFL2|];
                    split; [exact HP16'|]; split; [exact HN144'|]; split; [exact HT88'|];
                    split; [exact HIN2|]; split; [exact HROM2 | exact HJT2]|];
            split; [exact HMOD2 | split; [exact HSEP | exact HNP]]|].
    split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|]. split; [exact KREGS|].
    split; [exact R26'|]. split; [exact R21'|].
    split; [exact Q22|]. split; [exact Q20|]. split; [exact Q23|]. split; [exact Q24|].
    split; [exact Q25|].
    split; [exact Hq1|]. split; [exact CELLS|].
    split; [exact HAWR'|]. split; [exact HAT' | exact HPRE'].
  - right. exists regs2, mem2, md2, ly, St, kk2, fpos.
    split; [reflexivity|].
    split; [split; [split; [exact HJ2|]; split; [exact HFRM2|]; split; [exact HFL2|];
                    split; [exact HP16'|]; split; [exact HN144'|]; split; [exact HT88'|];
                    split; [exact HIN2|]; split; [exact HROM2 | exact HJT2]|];
            split; [exact HMOD2 | split; [exact HSEP | exact HNP]]|].
    split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|]. split; [exact KREGS|].
    split; [exact R26'|]. split; [exact R21'|].
    split; [intros j Hj; apply CELLS; lia|].
    split; [exact HAWR'|]. split; [exact HAT' | exact HPRE'].
Qed.

(* ------------------------------------------------------------------ the loop, by the trips left *)
(* @@ RESOLVED Lemma g2_loop *)
Lemma g2_loop_x : forall (n q : nat) cx t m W c,
  (q + n = 4)%nat ->
  LFB0 cx ->
  GL1_x B NP G_fr fr_FP PST ARx LSx RINV cx t m q W c ->
  SRr segs W c (GRG_x B NP G_fr fr_FP PST ARx LSx RINV cx t m).
Proof.
  induction n as [|n IH]; intros q cx t m W c Hn HB HL1.
  - exfalso. pose proof HL1 as (regs & mem & md & ly & St & kk & fpos & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & Hq & _). lia.
  - eapply SRr_bind; [exact (g2_step_x q cx t m W c HB HL1)|].
    intros W' c' _ [HL1' | HRG]; [exact (IH (S q) cx t m W' c' ltac:(lia) HB HL1') |].
    apply SRr_ret. exact HRG.
Qed.

(* ================================================================== GP2 of
   lib/B/W_LLVMFuzzerTestOneInput_gone.v: the reads[] loop, 0x84af8 -> 0x84b40 *)
(* @@ RESOLVED Lemma gp2_l1_rig *)
Lemma gp2_l1_rig_x : forall q cx t m W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GL1_x B NP G_fr fr_FP PST ARx LSx RINV cx t m q W c ->
  SRr segs W c (GRG_x B NP G_fr fr_FP PST ARx LSx RINV cx t m).
Proof.
  intros q cx t m W c HB HL1.
  pose proof HL1 as (regs & mem & md & ly & St & kk & fpos & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & Hq & _).
  exact (g2_loop_x (4 - q)%nat q cx t m W c ltac:(lia) HB HL1).
Qed.
(* @@ END gp2 *)
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twins of this phase over the R cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (Section gR), as SRrG walks with the G runs.  Strict text above
   unchanged. ---- *)
Section gp2R.
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



Definition g2_mid_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (v : Z) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk',
    c' = cfg_at segs (fr_B0 + AF_gn_st) regs' mem' md' /\
    AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W' mem' md' kk' /\
    (forall r, In r G2_CS -> getr regs' r = getr regs r) /\
    getr regs' 25 = getr regs 25 /\ getr regs' 10 = w64 v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - RRDS_STK <= a < lf_F cx) -> abyte_kept W mem W' mem' a).

Lemma g2_head_xR : forall cx (q : nat) m fpos ly S kk (W : world segs) regs mem md,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  amodel_at B ly S W mem m -> rom_view segs W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) ->
  getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) ->
  getr regs 27 = w64 SB ->
  YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + AF_gn_l1) regs mem md)
    (g2_mid_xR cx fpos ly S (gn_reads m q) W regs mem).
Proof.
  intros cx q m fpos ly S kk W regs mem md HB HJ HSV HMOD HROM Hq R2 R3 R4 R8 R20 R22 R25 R27.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S W mem md kk fpos
                HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  assert (HD2lo : 0 <= (rg_s fr_RG + 4) / 8) by (apply Z.div_pos; lia).
  assert (HD2hi : (rg_s fr_RG + 4) / 8 <= rg_s fr_RG + 4) by (apply Z.div_le_upper_bound; lia).
  set (open := g2_sopen (nth q (lm_hs m) None)) in *.
  pose proof HMOD as (Hlen4 & HSL & HREL & _).
  pose proof (g2_slot_open B ly S W mem q (nth q (lm_hs m) None) (HSL q ltac:(lia))) as Mopen.
  assert (Hopen01 : 0 <= open <= 1) by (unfold open, g2_sopen; destruct (nth q (lm_hs m) None); lia).
  assert (HZSA : azs B (rg_s fr_RG + ASRC * Z.of_nat q + 4) 8)
    by (apply (g2_azs_sub B (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | lia]).
  (* RRDS's shadow premise (cut 61da015af91): g_s[q]'s first four bytes, a sub-range of GN_HZS *)
  assert (HZS4 : azs B (rg_s fr_RG + ASRC * Z.of_nat q) 4)
    by (apply (g2_azs_sub B (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | lia]).
  assert (HSH : (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q = (rg_s fr_RG + ASRC * Z.of_nat q + 4) / 8)
    by (rewrite (g2_shift q Hq); reflexivity).
  set (A := rg_s fr_RG + ASRC * Z.of_nat q) in *.
  assert (HAe : A = 6131296 + 96 * Z.of_nat q) by (unfold A; rewrite HRS, HAS; reflexivity).
  assert (HA32 : A mod 32 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q) with ((191603 + 3 * Z.of_nat q) * 32) by lia;
        apply Z_mod_mult).
  assert (HA8 : A mod 8 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q) with ((766412 + 12 * Z.of_nat q) * 8) by lia;
        apply Z_mod_mult).
  assert (HA4 : (A + 4) mod 4 = 0)
    by (rewrite HAe; replace (6131296 + 96 * Z.of_nat q + 4) with ((1532825 + 24 * Z.of_nat q) * 4) by lia;
        apply Z_mod_mult).
  assert (HDlo : 0 <= (A + 4) / 8) by (apply Z.div_pos; lia).
  assert (HDhi : (A + 4) / 8 <= A + 4) by (apply Z.div_le_upper_bound; lia).
  assert (R25A : getr regs 25 = w64 (SB + (A + 4) / 8)) by (rewrite R25; unfold w64; f_equal; lia).
  (* the entry state *)
  remember (Eimg (Ereg regs (g2_x_head open))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (g2_x_head open)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (A + 4)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E22 : ew E 22 = Z_to_bv 64 A) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 open)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U20 : bv_unsigned (ew E 20) = A + 4) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = A) by (rewrite E22; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite E27; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = open) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_g2_head
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_l1)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_g2_head. apply pa_entry_st_ok_full.
    - unfold g2_sr_head. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]; rewrite <- HE.
      rewrite R25A. symmetry. apply bv_eq.
      change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))))
        with (U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
      rewrite (g2_USH E A E27 E20 ltac:(lia) ltac:(lia)).
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - vm_compute. reflexivity.
    - unfold g2_rg_head. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ A 4 4 (SOff 32 0) open);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact Mopen.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_head f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U20, U22, U27, U32.
      change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end;
        first [lia | exact HA4 | exact HA32 | reflexivity]. }
  assert (HBx : U E g2_Bx = SHADOW_OFF).
  { unfold U, g2_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity. }
  assert (UA20 : U E (SOff 20 0) = A + 4).
  { unfold U. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity. }
  assert (SHOK : sh_ok segs g2_Bx g2_SH_head E (mrestrict (w_H W) mem)).
  { unfold sh_ok, g2_SH_head. constructor; [|constructor].
    eapply shent_ok_of_range.
    - exact (azs_range_addressable_x B ARx LAWS ly S [] W mem md (A + 4) 8 HAR HZSA).
    - exact HBx.
    - exact UA20.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. lia. }
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_l1)) with (Z_to_bv 64 (BASE + AF_gn_l1)).
  (* 0x84af8-0x84b00: the shadow byte (0), the slow-path test (not taken), g_s[q].open *)
  paj_run_tok_xR RUNG HS HJ SHOK g2_span.
  { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                         | apply awr_ok_x_nil]. }
  g2_mem HF Em1. clear HF HFr HG0.
  (* 0x84b04 beqz a0: the closed slot, or the call *)
  psrr_branch_tok RUNG BRR HS SHOK g2_span.
  - (* g_s[q].open = 0: reads[q] = 0, already at 0x84b10 *)
    rewrite branch_eq_U, (U_atom E 32 open E32), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    assert (Hnone : nth q (lm_hs m) None = None).
    { unfold open, g2_sopen in Hc. destruct (nth q (lm_hs m) None) as [h|]; [lia | reflexivity]. }
    assert (Hr0 : gn_reads m q = 0) by (unfold gn_reads; rewrite Hnone; reflexivity).
    (* 0x84b04 -> 0x84b10 *)
    paj_run_to_tok_xR RUNTOG HS HJ SHOK g2_span AF_gn_st.
    { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                           | apply awr_ok_x_nil]. }
    g2_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (g2_x_head open)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (10%bv : bv 5) Q10. g2_reg HS (25%bv : bv 5) Q25.
    assert (Q25v : getr (ms_regs ms0) 25 = w64 (SB + (A + 4) / 8)).
    { rewrite Q25. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (g2_USH Ev A ltac:(rewrite ?ew_ewset_other by lia; exact E27)
                               ltac:(rewrite ?ew_ewset_other by lia; exact E20)
                               ltac:(lia) ltac:(lia)) end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    assert (Q10v : getr (ms_regs ms0) 10 = w64 (gn_reads m q)).
    { rewrite Q10, Hr0. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (U_atom Ev 32 open ltac:(rewrite ?ew_ewset_other by lia; exact E32)) by lia end.
      unfold open, g2_sopen. rewrite Hnone. unfold w64.
      rewrite unsigned_lit_small by lia. reflexivity. }
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply (YA0nH.SRrG_ret _ R R_refl). unfold g2_mid_xR.
    lazymatch goal with |- exists _ _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
      exists r, mm, d, kk end.
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)); reflexivity|].
    split; [exact HJ|]. split; [exact KR|].
    split; [rewrite Q25v, R25A; reflexivity|].
    split; [exact Q10v|].
    intros a Ha Hno. apply g2_abk_refl.
  - (* g_s[q].open <> 0: the slot is open, and relay_reads(&g_s[q]) is called *)
    rewrite branch_eq_U, (U_atom E 32 open E32), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (Hsome : exists h, nth q (lm_hs m) None = Some h).
    { unfold open, g2_sopen in Hc. destruct (nth q (lm_hs m) None) as [h|]; [exists h; reflexivity | lia]. }
    destruct Hsome as (h & Hsome).
    assert (HSRC : asrc_at B ly S W mem A h)
      by (pose proof (HSL q ltac:(lia)) as HSLq; rewrite Hsome in HSLq; exact HSLq).
    (* 0x84b08-0x84b0c: a0 = &g_s[q], jal relay_reads *)
    paj_run_to_tok_xR RUNTOG HS HJ SHOK g2_span AF_fr_relay_reads.
    { apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia
                           | apply awr_ok_x_nil]. }
    g2_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (g2_x_head open)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. g2_reg HS (10%bv : bv 5) Q10. g2_reg HS (25%bv : bv 5) Q25.
    assert (Q25v : getr (ms_regs ms0) 25 = w64 (SB + (A + 4) / 8)).
    { rewrite Q25. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (g2_USH Ev A ltac:(rewrite ?ew_ewset_other by lia; exact E27)
                               ltac:(rewrite ?ew_ewset_other by lia; exact E20)
                               ltac:(lia) ltac:(lia)) end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    assert (Q10v : getr (ms_regs ms0) 10 = w64 A).
    { rewrite Q10. g2_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (U_atom Ev 22 A ltac:(rewrite ?ew_ewset_other by lia; exact E22)) by lia end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
      set (rc0 := r) in *; set (mdc := d) in * end.
    assert (Hsp1 : spZ rc0 = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(cbv [G2_CS In]; tauto)), R2. unfold w64.
      apply unsigned_lit_small. lia. }
    destruct (gn_afn_pre_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV R
                cx ly S fpos kk W mem mdc rc0 RRDS_STK HB HJ HSV Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(cbv [G2_CS In]; tauto)). exact R3. }
    { rewrite (KR 4%bv ltac:(cbv [G2_CS In]; tauto)). exact R4. }
    { rewrite (KR 8%bv ltac:(cbv [G2_CS In]; tauto)). exact R8. }
    { unfold RRDS_STK, RSRC_STK. lia. }
    { unfold RRDS_STK, RSRC_STK. lia. }
    eapply (YA0nH.SRrG_bind _ R R_trans).
    { apply (YA0nH.SRr_SRrG _ R WLE_R); exact (RRDS_x W ly S [] rc0 mem mdc ch (lm_G m) (lm_es m) A h HPREc Q10v
               ltac:(lia) HA8 HZS4 HSRC HREL HROM). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HKEEP & HA0).
    rewrite Hsp1 in HJc, HKEEP.
    (* relay_reads's journal inside this function's: W2's ajournal_gx_sub_x at G_fr, the callee's lifted from G = [] *)
    assert (HJc' : AJ0R G_fr 0 [] RRDS_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono_xR segs B PST ARx [] G_fr 0 [] RRDS_STK (lf_F cx) [] ly S [] W mem mdc []
                ly S [] W2 mem2 md2 0 _ (ajournal_gx_xR_mono segs B PST ARx (@wle segs) R WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc)).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
       (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
       RRDS_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJc'
       ltac:(unfold RRDS_STK, RSRC_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply (YA0nH.SRrG_ret _ R R_refl). unfold g2_mid_xR.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1;
            change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)); reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (g2_cs_pres rc0 regs2 HP2 r ltac:(right; exact Hr)); exact (KR r Hr)|].
    split; [rewrite (g2_cs_pres rc0 regs2 HP2 25%bv ltac:(left; reflexivity)), R25A; exact Q25v|].
    split.
    { rewrite (g2_reads_of_post m q h (getr regs2 10) Hsome HA0). reflexivity. }
    exact HKEEP.
Qed.

Definition g2_tail_post_xR (cx : lfcx) (fpos : Z) (ly : alayout) (Sa : astate) (q : nat) (v : Z)
    (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' kk',
    AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly Sa W mem' md' kk' /\
    (forall r, In r G2_K2 -> getr regs' r = getr regs r) /\
    val_mem segs (arm W mem') (lf_F cx + 192 + 4 * Z.of_nat q) 4 v /\
    (forall a, 0 <= a < 2 ^ 64 ->
       ~ (lf_F cx + 192 + 4 * Z.of_nat q <= a < lf_F cx + 192 + 4 * Z.of_nat q + 4) ->
       abyte_kept W mem W mem' a) /\
    (* the store cell stays writable too (every byte's writability is kept: the runs only grow presence) *)
    (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) /\
    getr regs' 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat (S q) + 4) /\
    getr regs' 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat (S q)) /\
    getr regs' 23 = w64 (4 - Z.of_nat (S q)) /\
    getr regs' 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat (S q)) /\
    getr regs' 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat (S q)) /\
    (((S q < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_l1) regs' mem' md') \/
     ((S q) = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_rig) regs' mem' md')).

Lemma g2_tail_xR : forall cx (q : nat) fpos ly Sa kk (W : world segs) regs mem md v,
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly Sa W mem md kk ->
  (q < 4)%nat -> 0 <= v <= 1 ->
  2 ^ 46 <= lf_F cx -> lf_F cx + 216 <= 2 ^ 47 -> lf_F cx mod 32 = 0 ->
  spZ (c_regs cx) - LLVMF_STK <= lf_F cx + 192 -> lf_F cx + 208 <= spZ (c_regs cx) ->
  awr W mem (lf_F cx + 192) 16 ->
  getr regs 10 = w64 v ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) ->
  getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 23 = w64 (4 - Z.of_nat q) ->
  getr regs 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) ->
  getr regs 27 = w64 SB ->
  YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + AF_gn_st) regs mem md) (g2_tail_post_xR cx fpos ly Sa q v W regs mem).
Proof.
  intros cx q fpos ly Sa kk W regs mem md v HJ Hq Hv HF1 HF2 HF32 Hs1 Hs2 HW R10 R20 R22 R23 R24 R25 R27.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  assert (HD2lo : 0 <= (rg_s fr_RG + 4) / 8) by (apply Z.div_pos; lia).
  assert (HD2hi : (rg_s fr_RG + 4) / 8 <= rg_s fr_RG + 4) by (apply Z.div_le_upper_bound; lia).
  set (cell := lf_F cx + 192 + 4 * Z.of_nat q) in *.
  assert (Hce : cell = lf_F cx + 192 + 4 * Z.of_nat q) by reflexivity.
  assert (Hc4 : cell mod 4 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D.
    replace cell with ((8 * (lf_F cx / 32) + 48 + Z.of_nat q) * 4) by lia. apply Z_mod_mult. }
  remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q + 4))
    by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E22 : ew E 22 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q))
    by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E23 : ew E 23 = Z_to_bv 64 (4 - Z.of_nat q)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
  assert (E24 : ew E 24 = Z_to_bv 64 cell) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
  assert (E25 : ew E 25 = Z_to_bv 64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q))
    by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (U10 : bv_unsigned (ew E 10) = v) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = 4 - Z.of_nat q) by (rewrite E23; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = cell) by (rewrite E24; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite E27; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_g2_tail
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_st)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_g2_tail. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold g2_rg_tail. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U24. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil].
      intros o Ho. replace (cell + o) with (lf_F cx + 192 + (4 * Z.of_nat q + o)) by lia.
      apply HW. lia.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_tail f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U10, U23, U24, U27.
      change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [lia | exact Hc4 | reflexivity]. }
  assert (SHOK : sh_ok segs g2_Bx (@nil shent) E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_st)) with (Z_to_bv 64 (BASE + AF_gn_st)).
  (* 0x84b10-0x84b24: the store and the five bumps *)
  paj_run_tok_xR RUNG HS HJ SHOK g2_span.
  { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24 in Ha.
    left. split; [left; lia | lia]. }
  rename HF into HFst, HFr into HFrst, HG0 into HGst.
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms) a).
  { intros a Ha Hna. split.
    - apply (aview_kept_out _ _ _ _ _ HFrst a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_g2_tail g2_rg_tail In] in Hin.
      destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U24 in Hr. lia.
    - intros Hw. exact (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw). }
  (* 0x84b28 bnez s7: the next slot, or 0x84b2c j 84b40 *)
  psrr_branch_tok RUNG BRR HS SHOK g2_span.
  - (* 4 - q - 1 <> 0: back to the loop's head *)
    rewrite branch_ne_U, (U_atom_off E 23 _ (-1) ltac:(rewrite ?ew_ewset_other by lia; exact E23)), U_lit
      in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hq1 : (S q < 4)%nat) by lia.
    paj_run_to_tok_xR RUNTOG HS HJ SHOK g2_span AF_gn_l1.
    { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
      intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite ?ew_ewset_other in Ha by lia. rewrite U24 in Ha.
      left. split; [left; lia | lia]. }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (MV0 : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (cell + 0) (N.to_nat 4) v).
    { lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 24%nat cell _ _ _ _ _ 0 4%N (SOff 10 0) v RG1) end.
      - rewrite ?ew_ewset_other by lia. exact U24.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (MV : val_mem segs (arm W (ms_mem ms0)) cell 4 v)
      by (unfold arm; rewrite Z.add_0_r in MV0; change (N.to_nat 4) with 4%nat in MV0; exact MV0).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms0) a).
    { intros a Ha Hna. apply (g2_abk_trans W W W mem (ms_mem ms) (ms_mem ms0) a (KEEP0 a Ha Hna)).
      split.
      - apply (aview_kept_out _ _ _ _ _ HFr a Ha).
        intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite U24 in Hr; lia.
      - intros Hw. exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0) Hw). }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0)
            (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw))).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (20%bv : bv 5) Q20. g2_reg HS (22%bv : bv 5) Q22. g2_reg HS (23%bv : bv 5) Q23.
    g2_reg HS (24%bv : bv 5) Q24. g2_reg HS (25%bv : bv 5) Q25.
    pmkst HS.
    apply (YA0nH.SRrG_ret _ R R_refl). unfold g2_tail_post_xR. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |}] => exists r, mm, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. split; [exact MV|]. split; [exact KEEP|]. split; [exact WK|].
    split; [g2_off Q20 20%nat 96 E20|].
    split; [g2_off Q22 22%nat 96 E22|].
    split; [g2_off Q23 23%nat (-1) E23|].
    split; [g2_off Q24 24%nat 4 E24|].
    split; [g2_off Q25 25%nat 12 E25|].
    left. split; [exact Hq1|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_l1)) with (Z_to_bv 64 (BASE + AF_gn_l1)). reflexivity.
  - (* 4 - q - 1 = 0: 0x84b2c `j 84b40` *)
    rewrite branch_ne_U, (U_atom_off E 23 _ (-1) ltac:(rewrite ?ew_ewset_other by lia; exact E23)), U_lit
      in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (Hq4 : (S q) = 4%nat) by lia.
    paj_run_to_tok_xR RUNTOG HS HJ SHOK g2_span AF_gn_rig.
    { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
      intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite ?ew_ewset_other in Ha by lia. rewrite U24 in Ha.
      left. split; [left; lia | lia]. }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (MV0 : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (cell + 0) (N.to_nat 4) v).
    { lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 24%nat cell _ _ _ _ _ 0 4%N (SOff 10 0) v RG1) end.
      - rewrite ?ew_ewset_other by lia. exact U24.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (MV : val_mem segs (arm W (ms_mem ms0)) cell 4 v)
      by (unfold arm; rewrite Z.add_0_r in MV0; change (N.to_nat 4) with 4%nat in MV0; exact MV0).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W (ms_mem ms0) a).
    { intros a Ha Hna. apply (g2_abk_trans W W W mem (ms_mem ms) (ms_mem ms0) a (KEEP0 a Ha Hna)).
      split.
      - apply (aview_kept_out _ _ _ _ _ HFr a Ha).
        intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?ew_ewset_other in Hr by lia; rewrite U24 in Hr; lia.
      - intros Hw. exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0) Hw). }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; exact (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a (g2_pres_grows W _ _ a HG0)
            (writable_kept (w_H W) mem (ms_mem ms) a (g2_pres_grows W _ _ a HGst) Hw))).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (20%bv : bv 5) Q20. g2_reg HS (22%bv : bv 5) Q22. g2_reg HS (23%bv : bv 5) Q23.
    g2_reg HS (24%bv : bv 5) Q24. g2_reg HS (25%bv : bv 5) Q25.
    pmkst HS.
    apply (YA0nH.SRrG_ret _ R R_refl). unfold g2_tail_post_xR. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |}] => exists r, mm, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. split; [exact MV|]. split; [exact KEEP|]. split; [exact WK|].
    split; [g2_off Q20 20%nat 96 E20|].
    split; [g2_off Q22 22%nat 96 E22|].
    split; [g2_off Q23 23%nat (-1) E23|].
    split; [g2_off Q24 24%nat 4 E24|].
    split; [g2_off Q25 25%nat 12 E25|].
    right. split; [exact Hq4|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig)). reflexivity.
Qed.

Lemma g2_step_xR : forall (q : nat) cx t m W c,
  LFB0 cx ->
  GL1_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m q W c ->
  YA0nH.SRrG segs R W c (fun W' c' => GL1_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m (S q) W' c' \/
                             GRG_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m W' c').
Proof.
  intros q cx t m W c HB HL1.
  destruct HL1 as (regs & mem & md & ly & St & kk & fpos & Hc & HGST & HLS & HRI & HOP & HKR &
                   R26 & R21 & R22 & R20 & R23 & R24 & R25 & Hq & HCELLS & HAWR & HAT & HPRE).
  destruct HGST as (HCOM & HMOD & HSEP & HNP).
  destruct HCOM as (HJ & HFRM & HFL & HP16 & HN144 & HT88 & HIN & HROM & HJT).
  pose proof HKR as (K2 & K8 & K9 & K18 & K19 & K27 & K3 & K4).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly St W mem md
              kk fpos
                HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  pose proof YM05.alloc_ceiling_value as AC. pose proof gk_ceil_lo as HCL0.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE2). pose proof HPRE2 as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof HERR as (HE0 & HE1).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (HCEIL : GK_CEIL8 = alloc_ceiling + 8) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HRSTK : RRDS_STK = 32) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (HFFs : 0 <= SB + FF / 8 /\ SB + FF / 8 + 16 <= GK_CEIL8).
  { pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)) as Hd1.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd2. lia. }
  rewrite Hc.
  (* 0x84af8 -> 0x84b10 *)
  eapply (YA0nH.SRrG_bind _ R R_trans).
  { exact (g2_head_xR cx q m fpos ly St kk W regs mem md HB HJ (proj1 HFRM) HMOD HROM Hq
             K2 K3 K4 K8 R20 R22 R25 K27). }
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & K25a & R10a & KP1).
  (* what the call kept *)
  assert (KH : forall a, F <= a < 2 ^ 64 -> abyte_kept W mem W1 mem1 a)
    by (intros a Ha; apply KP1; lia).
  assert (HAWR1 : awr W1 mem1 (F + 192) 16)
    by (apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact HAWR]).
  (* 0x84b10 -> 0x84af8 / 0x84b40 *)
  eapply (YA0nH.SRrG_bind _ R R_trans).
  { apply (g2_tail_xR cx q fpos ly St kk1 W1 regs1 mem1 md1 (gn_reads m q) HJ1 Hq (g2_reads_rng m q));
      [ lia | lia | exact HF32 | lia | lia | exact HAWR1 | exact R10a
      | rewrite (KR1 20%bv ltac:(cbv [G2_CS In]; tauto)); exact R20
      | rewrite (KR1 22%bv ltac:(cbv [G2_CS In]; tauto)); exact R22
      | rewrite (KR1 23%bv ltac:(cbv [G2_CS In]; tauto)); exact R23
      | rewrite (KR1 24%bv ltac:(cbv [G2_CS In]; tauto)); exact R24
      | rewrite K25a; exact R25
      | rewrite (KR1 27%bv ltac:(cbv [G2_CS In]; tauto)); exact K27 ]. }
  intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & kk2 & HJ2 & KR2 & MV & KP2 & WK2 & Q20 & Q22 & Q23 & Q24 & Q25 & Hpc).
  (* the two steps composed *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F - RRDS_STK <= a < F) ->
      ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha Hn1 Hn2; exact (g2_abk_trans W W1 W1 mem mem1 mem2 a (KP1 a Ha Hn1) (KP2 a Ha Hn2))).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha; apply KEEP; lia).
  assert (KHI : forall a, F <= a < 2 ^ 64 ->
      ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) -> abyte_kept W mem W1 mem2 a)
    by (intros a Ha Hn2; apply KEEP; [lia | lia | exact Hn2]).
  (* the cut's facts at the next cut point *)
  assert (HMOD2 : amodel_at B ly St W1 mem2 m)
    by (exact (gk_amodel_kept_x B ARx LAWS BLKN ly St W mem md W1 mem2 m HAR HMOD HE0 ltac:(lia) KL)).
  assert (HIN2 : ainput_at B cx ly St W1 mem2)
    by (exact (gk_ainput_kept_x B ARx LAWS BLKN cx ly St W mem md W1 mem2 HAR HIN (eq_sym Hnlen) KL)).
  assert (HROM2 : rom_view segs W1 mem2) by (exact (gk_rom_kept W W1 mem mem2 HROM KL)).
  assert (HJT2 : jt_rom W1 mem2) by (exact (gk_jt_kept W W1 mem mem2 HJT KL)).
  assert (HFRM2 : gframe cx fake_shadow_open FF W1 mem2).
  { apply (g2_gframe_kept cx fake_shadow_open FF W W1 mem mem2 RRDS_STK (F + 192 + 4 * Z.of_nat q) HFRM eq_refl);
      [ intros a Ha Hn Hcl; apply KEEP; [exact Ha | exact Hn | exact Hcl]
      | intros a Ha Hw; apply WK2; exact (proj2 (KP1 a ltac:(lia) ltac:(lia)) Hw)
      | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia ]. }
  assert (HFL2 : sv8 W1 mem2 (FF + 120) (flag_addr ly 1 fpos))
    by (apply (gk_sv8_kept W W1 mem mem2); [intros x Hx; apply KL; lia | exact HFL]).
  assert (KV8 : forall a v, F <= a -> a + 8 <= 2 ^ 64 ->
      (a + 8 <= F + 192 + 4 * Z.of_nat q \/ F + 192 + 4 * Z.of_nat q + 4 <= a) ->
      sv8 W mem a v -> sv8 W1 mem2 a v)
    by (intros a v H0 H1 H3 Hv; apply (gk_sv8_kept W W1 mem mem2); [|exact Hv];
        intros x Hx; apply KHI; lia).
  assert (HP16' : sv8 W1 mem2 (F + 16) (c_p cx + gn_kq cx m))
    by (apply KV8; [lia | lia | left; lia | exact HP16]).
  assert (HN144' : sv8 W1 mem2 (F + 144) (c_n cx - gn_kq cx m))
    by (apply KV8; [lia | lia | left; lia | exact HN144]).
  assert (HT88' : sv8 W1 mem2 (F + 88) t)
    by (apply KV8; [lia | lia | left; lia | exact HT88]).
  assert (HAT' : sv8 W1 mem2 (F + 208) 0)
    by (apply KV8; [lia | lia | right; lia | exact HAT]).
  assert (HAWR' : awr W1 mem2 (F + 192) 16).
  { intros i Hi. apply WK2. exact (HAWR1 i Hi). }
  assert (HPRE' : gn_prefix_at cx m W1 mem2 FF).
  { apply (g2_prefix_kept cx m W W1 mem mem2 FF HPRE). intros a Ha. apply KL. lia. }
  assert (CELLS : forall j, (j < S q)%nat -> gn_sv4 W1 mem2 (F + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. destruct (Nat.eq_dec j q) as [->|Hne]; [exact MV|].
    apply (akept_vm W mem); [|exact (HCELLS j ltac:(lia))].
    intros x Hx. cbn in Hx. apply KHI; [lia|].
    assert (Hjz : 0 <= Z.of_nat j <= 3) by lia.
    assert (Hjq : Z.of_nat j <> Z.of_nat q) by lia. lia. }
  assert (KREGS : gn_kregs B cx FF regs2).
  { unfold gn_kregs. repeat split;
      first [ rewrite (KR2 2%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 2%bv ltac:(cbv [G2_CS In]; tauto)); exact K2
            | rewrite (KR2 8%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 8%bv ltac:(cbv [G2_CS In]; tauto)); exact K8
            | rewrite (KR2 9%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 9%bv ltac:(cbv [G2_CS In]; tauto)); exact K9
            | rewrite (KR2 18%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 18%bv ltac:(cbv [G2_CS In]; tauto)); exact K18
            | rewrite (KR2 19%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 19%bv ltac:(cbv [G2_CS In]; tauto)); exact K19
            | rewrite (KR2 27%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 27%bv ltac:(cbv [G2_CS In]; tauto)); exact K27
            | rewrite (KR2 3%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 3%bv ltac:(cbv [G2_CS In]; tauto)); exact K3
            | rewrite (KR2 4%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 4%bv ltac:(cbv [G2_CS In]; tauto)); exact K4 ]. }
  assert (R26' : getr regs2 26 = w64 HI_G_NOUT)
    by (rewrite (KR2 26%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 26%bv ltac:(cbv [G2_CS In]; tauto)); exact R26).
  assert (R21' : getr regs2 21 = w64 (gn_id cx m))
    by (rewrite (KR2 21%bv ltac:(cbv [G2_K2 In]; tauto)), (KR1 21%bv ltac:(cbv [G2_CS In]; tauto)); exact R21).
  apply (YA0nH.SRrG_ret _ R R_refl).
  destruct Hpc as [(Hq1 & ->) | (Hq4 & ->)].
  - left. exists regs2, mem2, md2, ly, St, kk2, fpos.
    split; [reflexivity|].
    split; [split; [split; [exact HJ2|]; split; [exact HFRM2|]; split; [exact HFL2|];
                    split; [exact HP16'|]; split; [exact HN144'|]; split; [exact HT88'|];
                    split; [exact HIN2|]; split; [exact HROM2 | exact HJT2]|];
            split; [exact HMOD2 | split; [exact HSEP | exact HNP]]|].
    split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|]. split; [exact KREGS|].
    split; [exact R26'|]. split; [exact R21'|].
    split; [exact Q22|]. split; [exact Q20|]. split; [exact Q23|]. split; [exact Q24|].
    split; [exact Q25|].
    split; [exact Hq1|]. split; [exact CELLS|].
    split; [exact HAWR'|]. split; [exact HAT' | exact HPRE'].
  - right. exists regs2, mem2, md2, ly, St, kk2, fpos.
    split; [reflexivity|].
    split; [split; [split; [exact HJ2|]; split; [exact HFRM2|]; split; [exact HFL2|];
                    split; [exact HP16'|]; split; [exact HN144'|]; split; [exact HT88'|];
                    split; [exact HIN2|]; split; [exact HROM2 | exact HJT2]|];
            split; [exact HMOD2 | split; [exact HSEP | exact HNP]]|].
    split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|]. split; [exact KREGS|].
    split; [exact R26'|]. split; [exact R21'|].
    split; [intros j Hj; apply CELLS; lia|].
    split; [exact HAWR'|]. split; [exact HAT' | exact HPRE'].
Qed.

Lemma g2_loop_xR : forall (n q : nat) cx t m W c,
  (q + n = 4)%nat ->
  LFB0 cx ->
  GL1_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m q W c ->
  YA0nH.SRrG segs R W c (GRG_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m).
Proof.
  induction n as [|n IH]; intros q cx t m W c Hn HB HL1.
  - exfalso. pose proof HL1 as (regs & mem & md & ly & St & kk & fpos & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & Hq & _). lia.
  - eapply (YA0nH.SRrG_bind _ R R_trans); [exact (g2_step_xR q cx t m W c HB HL1)|].
    intros W' c' _ [HL1' | HRG]; [exact (IH (S q) cx t m W' c' ltac:(lia) HB HL1') |].
    apply (YA0nH.SRrG_ret _ R R_refl). exact HRG.
Qed.

Lemma gp2_l1_rig_xR : forall q cx t m W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GL1_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m q W c ->
  YA0nH.SRrG segs R W c (GRG_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m).
Proof.
  intros q cx t m W c HB HL1.
  pose proof HL1 as (regs & mem & md & ly & St & kk & fpos & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & Hq & _).
  exact (g2_loop_xR (4 - q)%nat q cx t m W c ltac:(lia) HB HL1).
Qed.

End gp2R.

End gp2.

