(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 299 of its 411 lines of code are new or changed and 1027 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module names changed; 210 of its 254 lines of code are new or changed and 367 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_tail: proves lc_tail_ok, the TAIL segment (lc_tail_stmt of
   lib/A/Prog/LLVMFuzzerTestOneInput_segs.v) of the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput:
   offsets +0x12ec .. +0x1304 of the listing lib/A/Prog/DgnTransportList.v (0x82550 .. 0x82568).

   What the code does. +0x12ec `li a0, 1022`; +0x12f0 `bltu a0, s5` (s5 = ops, 0 <= ops < OPS_MAX = 1024): taken
   only for ops = 1023, to the epilogue +0x150c; +0x12f4 `addiw s5, s5, 1` (ops + 1 <= 1023, so the 32-bit sum
   sign-extended is ops + 1); +0x12f8 `mv s9, s8`; +0x12fc `mv s11, s7`; +0x1300 `bnez s7` (s7 = fi_n cn): to the loop
   head +0x408 when bytes are left, else +0x1304 `j` to the epilogue. No memory access, no call.

   How it is proved. Each stretch is a run of the token engine over the cut's G journal (lib/A/Prog/TransportGRunA.v
   paj_run_x / paj_run_to_x) from a symbolic state with no region, so the runs write nothing (frame_of_read_only)
   and the journal they return is carried as it is; each branch is split by DgnTransportPaLib.v paj_branch. The next
   head's simulation facts are LLVMFuzzerTestOneInput_st.v lc_tail_agree / lc_tail_opok. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGRunA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac lt_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* The write obligation of a run from a state with no region: nothing is written. *)
Ltac lt_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

(* Words below 2 ^ 64: their unsigned value, unsigned order and equality. *)
Lemma lt_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_small. exact Hz.
Qed.
Lemma lt_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite (lt_u64 a Ha), (lt_u64 b Hb). reflexivity. Qed.
Lemma lt_eqb : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite (lt_u64 a Ha), (lt_u64 b Hb). reflexivity. Qed.

(* The denotations the branches and the registers read. *)
Lemma lt_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z. reflexivity. Qed.
Lemma lt_off : forall E (n : nat) x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n 0) = Z_to_bv 64 x.
Proof. intros E n x H. cbn [sv_denot]. rewrite H, Z.add_0_r. reflexivity. Qed.

(* +0x12f4 `addiw s5, s5, 1` on ops <= 1022: the 32-bit sum, sign-extended, is ops + 1. *)
Lemma lt_addiw : forall E (x : Z), 0 <= x < 2 ^ 31 - 1 -> bv_unsigned (ew E 21) = x ->
  sv_denot E (SAluw ALU_ADD (SOff 21 0) (SLit 1)) = Z_to_bv 64 (x + 1).
Proof.
intros E x Hx Hu.
rewrite denot_lit_U, U_of_S, S_SAluw, U_SOff, U_SLit, Hu, Z.add_0_r.
cbn [zalu_raw].
rewrite (zcanon_id x) by (unfold M64; lia).
change (zcanon 1 mod 2 ^ 32) with 1.
rewrite (Z.mod_small x (2 ^ 32)) by lia.
unfold bv_swrap. change (bv_half_modulus 32%N) with 2147483648.
rewrite (bv_wrap_small 32%N) by (change (bv_modulus 32%N) with 4294967296; lia).
rewrite (bv_wrap_small 64%N) by (change (bv_modulus 64%N) with (2 ^ 64); lia).
f_equal. lia.
Qed.

Section seg_tail. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The environment of a state with no region: every register an atom, the image's values above. *)
Definition lt_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma lt_ew_reg0 : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lt_E0 regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold lt_E0. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma lt_env_img0 : forall regs, img_env VAL A_LIM (lt_E0 regs).
Proof. intros regs. unfold lt_E0. apply Eimg_env. Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma lt_entry0 : forall {fx : YK11.FPState} (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (lt_E0 regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros fx W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Definition LT_B0 : Z * Z := (0, 0).
Definition LT_Bx : sv := SOff 26 0.

(* The register r of the run's state is register m of the cut's registers regs. *)
Ltac lt_keep HS regs n m mn H :=
  lt_reg HS (Z_to_bv 5 n) (YK11.getr regs (Z_to_bv 5 m)) H
    ltac:(cbn [sv_denot]; rewrite (lt_ew_reg0 regs mn (Z_to_bv 5 m) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).

(* The spill slots of the frame are the first two of the loop's. *)
Lemma lt_spill_sm : forall cx (r : Z -> option Z),
  lc_spills cx (lf_spill_loop (lc_F cx)) r -> lc_spills cx (lf_spill_sm (lc_F cx)) r.
Proof.
intros cx r H. unfold lc_spills, lf_spill_loop, lf_spill_init, lf_spill_scal in H.
apply Forall_app in H as [H _]. apply Forall_app in H as [H _]. apply Forall_app in H as [H _]. exact H.
Qed.

(* The epilogue's cut from the loop's facts at registers regs2 that keep s0, s1, sp, gp, tp, s2 and s10. *)
Lemma lt_exit_of : forall (cx : lcx) ly S (W : world segs) regs mem md e (regs2 : bvmap 5 word) (k : Z),
  lc_core B cx ly S W regs mem md e -> lc_fr cx regs ->
  lc_spills cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W) mem) ->
  lc_fsh cx (aview segs (w_H W) mem) false false ->
  0 <= k <= TC.OPS_MAX -> 0 <= e <= receive_cg.RECV_EV * k -> lc_meter MT cx S k ->
  YK11.getr regs2 (Z_to_bv 5 2) = YK11.getr regs (Z_to_bv 5 2) ->
  YK11.getr regs2 (Z_to_bv 5 3) = YK11.getr regs (Z_to_bv 5 3) ->
  YK11.getr regs2 (Z_to_bv 5 4) = YK11.getr regs (Z_to_bv 5 4) ->
  YK11.getr regs2 (Z_to_bv 5 8) = YK11.getr regs (Z_to_bv 5 8) ->
  YK11.getr regs2 (Z_to_bv 5 9) = YK11.getr regs (Z_to_bv 5 9) ->
  YK11.getr regs2 (Z_to_bv 5 18) = YK11.getr regs (Z_to_bv 5 18) ->
  YK11.getr regs2 (Z_to_bv 5 26) = YK11.getr regs (Z_to_bv 5 26) ->
  lc_st_exit B MT cx W (lc_cfg cx LO_EXIT regs2 mem md).
Proof.
intros cx ly S W regs mem md e regs2 k HC HFR HSP HFSH Hk He HMT K2 K3 K4 K8 K9 K18 K26.
destruct HC as (HJ & H1 & H2 & H3 & G2 & G8 & G9 & G3 & G4 & HR).
destruct HFR as (F18 & F26).
exists ly, S, regs2, mem, md, e, k.
split; [reflexivity|].
split; [exact (conj HJ (conj H1 (conj H2 (conj H3 (conj (eq_trans K2 G2) (conj (eq_trans K8 G8)
          (conj (eq_trans K9 G9) (conj (eq_trans K3 G3) (conj (eq_trans K4 G4) HR))))))))) |].
split; [exact (conj (eq_trans K18 F18) (eq_trans K26 F26)) |].
split; [exact (lt_spill_sm cx _ HSP) |].
split; [exact HFSH |].
split; [exact Hk |].
split; [exact He | exact HMT].
Qed.

Lemma lc_tail_ok : lc_tail_stmt B MT XL RLO RHI.
Proof.
unfold lc_tail_stmt. intros HP cx op W' c' HB HT.
destruct HT as (ly' & S' & regs' & mem' & md' & e & a & Bw & cn & k' & Ec & HL & Ha & Hm & Htw & Hcur & R20 & R22).
subst c'.
pose proof HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof HC as (HJ & HCr).
pose proof HOK as (HA & Hops & Hcin & Hn0 & Hk0).
(* the operation's end: the cursor in range and at most ops + 1 receptions *)
destruct (lc_tail_agree (l_pl cx) (lo_ops op) (lo_B op) (lo_c op) (lo_k op) a Bw cn k' HA Hops Hcin Hn0 Hk0 Ha Hm)
  as (_ & Hcn & Hk').
pose proof Hcn as (Hfo & Hfn & Hfs).
assert (Hpl : Z.of_nat (length (l_pl cx)) < 2 ^ 26).
{ pose proof HB as HB'. unfold lc_base, tfib_lib_pre_x in HB'.
  destruct HB' as (_ & _ & _ & _ & Hnp & Hlen & _). destruct Hnp as [[H0 _] | [H0 _]]; lia. }
assert (EO : TC.OPS_MAX = 1024) by reflexivity.
pose proof Hcur as (C24 & C23).
assert (R21' : YK11.getr regs' (Z_to_bv 5 21) = Z_to_bv 64 (lo_ops op)) by exact R21.
assert (U21 : bv_unsigned (ew (lt_E0 regs') 21) = lo_ops op)
  by (rewrite (lt_ew_reg0 regs' 21%nat (Z_to_bv 5 21) eq_refl), R21'; apply lt_u64; lia).
assert (U23 : bv_unsigned (ew (lt_E0 regs') 23) = TOP.fi_n cn)
  by (rewrite (lt_ew_reg0 regs' 23%nat (Z_to_bv 5 23) eq_refl), C23; apply lt_u64; lia).
(* the runs over the cut's journal *)
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof (lt_entry0 (fx := l_fx cx) W' regs' mem' LO_TAIL) as HS.
assert (SHOK : sh_ok segs LT_Bx (@nil shent) (lt_E0 regs') (mrestrict (w_H W') mem')) by constructor.
assert (HEI : img_env VAL A_LIM (lt_E0 regs')) by apply lt_env_img0.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_TAIL)) mem'
    (YK11.seg_rom segs)) md') Q) end.
(* +0x12ec `li a0, 1022`, up to the `bltu` *)
paj_run_tok RUN HS HJ SHOK LT_B0.
{ lt_awr0. }
assert (Em1 : ms_mem ms = mem') by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
clear HF HFr HG.
(* +0x12f0 `bltu a0, s5`: 1022 < ops *)
psrr_branch_tok RUN BR HS SHOK LT_B0.
- (* ops = 1023: the epilogue *)
  cbn [branch_taken] in Hc. rewrite lt_lit, (lt_off _ 21%nat (lo_ops op) U21) in Hc.
  rewrite lt_ltu in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hgt.
  paj_run_to_tok RUNTO HS HJ SHOK LT_B0 LO_EXIT.
  { lt_awr0. }
  assert (Em2 : ms_mem ms0 = mem')
    by (rewrite <- Em1; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
  lt_keep HS regs' 2 2 2%nat K2. lt_keep HS regs' 3 3 3%nat K3. lt_keep HS regs' 4 4 4%nat K4.
  lt_keep HS regs' 8 8 8%nat K8. lt_keep HS regs' 9 9 9%nat K9. lt_keep HS regs' 18 18 18%nat K18.
  lt_keep HS regs' 26 26 26%nat K26.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) in * end.
  apply SRr_ret. right. rewrite Em2 in HJ |- *.
  exact (lt_exit_of cx ly' S' W' regs' mem' md2 e (ms_regs ms0) (Z.of_nat k')
    (conj HJ HCr) HFR HSP HFSH ltac:(lia) He HMT K2 K3 K4 K8 K9 K18 K26).
- (* ops <= 1022 *)
  cbn [branch_taken] in Hc. rewrite lt_lit, (lt_off _ 21%nat (lo_ops op) U21) in Hc.
  rewrite lt_ltu in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hle.
  (* +0x12f0 .. +0x12fc: s5 = ops + 1, s9 = s8, s11 = s7, up to the `bnez` *)
  paj_run_tok RUN HS HJ SHOK LT_B0.
  { lt_awr0. }
  assert (Em2 : ms_mem ms0 = mem')
    by (rewrite <- Em1; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
  clear HF HFr HG.
  (* +0x1300 `bnez s7`: bytes left *)
  psrr_branch_tok RUN BR HS SHOK LT_B0.
  + (* fi_n cn <> 0: the next head *)
    cbn [branch_taken] in Hc. rewrite (lt_off _ 23%nat (TOP.fi_n cn) U23), lt_lit in Hc.
    rewrite lt_eqb in Hc by lia.
    assert (Hnz : TOP.fi_n cn <> 0) by (intros Hz; rewrite Hz in Hc; cbn in Hc; discriminate Hc).
    pose proof (lc_tail_opok (l_pl cx) (lo_ops op) (lo_B op) (lo_c op) (lo_k op) a Bw cn k' HA Hops Hcin Hn0 Hk0 Ha
      Hm ltac:(lia) Hnz) as HOK'.
    paj_run_to_tok RUNTO HS HJ SHOK LT_B0 LO_HEAD.
    { lt_awr0. }
    assert (Em3 : ms_mem ms1 = mem')
      by (rewrite <- Em2; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
    lt_keep HS regs' 2 2 2%nat K2. lt_keep HS regs' 3 3 3%nat K3. lt_keep HS regs' 4 4 4%nat K4.
    lt_keep HS regs' 8 8 8%nat K8. lt_keep HS regs' 9 9 9%nat K9. lt_keep HS regs' 18 18 18%nat K18.
    lt_keep HS regs' 26 26 26%nat K26. lt_keep HS regs' 20 20 20%nat K20. lt_keep HS regs' 22 22 22%nat K22.
    lt_keep HS regs' 25 24 24%nat K25. lt_keep HS regs' 27 23 23%nat K27.
    lt_reg HS (Z_to_bv 5 21) (Z_to_bv 64 (lo_ops op + 1)) K21 ltac:(apply lt_addiw; [lia | exact U21]).
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) in * end.
    apply SRr_ret. left. rewrite Em3 in HJ |- *.
    exists (mkLop (lo_ops op + 1) Bw cn k'). split; [reflexivity|].
    exists ly', S', (ms_regs ms1), mem', md2, e.
    split; [reflexivity|].
    destruct HCr as (H1 & H2 & H3 & G2 & G8 & G9 & G3 & G4 & HR).
    destruct HFR as (F18 & F26).
    split.
    { split; [exact (conj HJ (conj H1 (conj H2 (conj H3 (conj (eq_trans K2 G2) (conj (eq_trans K8 G8)
                (conj (eq_trans K9 G9) (conj (eq_trans K3 G3) (conj (eq_trans K4 G4) HR))))))))) |].
      split; [exact (conj (eq_trans K18 F18) (eq_trans K26 F26)) |].
      split; [exact HSP |].
      split; [exact HFSH |].
      split; [exact HOK' |].
      split; [exact He |].
      split; [exact HMT | exact K21]. }
    split; [exact Htw |].
    split; [exact (conj (eq_trans K25 C24) (eq_trans K27 C23)) |].
    split; [exact (eq_trans K20 R20) | exact (eq_trans K22 R22)].
  + (* fi_n cn = 0: +0x1304 `j` to the epilogue *)
    paj_run_to_tok RUNTO HS HJ SHOK LT_B0 LO_EXIT.
    { lt_awr0. }
    assert (Em3 : ms_mem ms1 = mem')
      by (rewrite <- Em2; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
    lt_keep HS regs' 2 2 2%nat K2. lt_keep HS regs' 3 3 3%nat K3. lt_keep HS regs' 4 4 4%nat K4.
    lt_keep HS regs' 8 8 8%nat K8. lt_keep HS regs' 9 9 9%nat K9. lt_keep HS regs' 18 18 18%nat K18.
    lt_keep HS regs' 26 26 26%nat K26.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) in * end.
    apply SRr_ret. right. rewrite Em3 in HJ |- *.
    exact (lt_exit_of cx ly' S' W' regs' mem' md2 e (ms_regs ms1) (Z.of_nat k')
      (conj HJ HCr) HFR HSP HFSH ltac:(lia) He HMT K2 K3 K4 K8 K9 K18 K26).
Qed.

End seg_tail.

Print Assumptions lc_tail_ok.
