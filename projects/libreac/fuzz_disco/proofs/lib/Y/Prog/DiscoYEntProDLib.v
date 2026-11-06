(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 4602 of its 4661 lines of code are new or changed and 310 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntStep.v, with its module paths and module names changed; 200 of its 290 lines of code are new or changed and 4571 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC85 YC88 YCkd YC1g YC1h YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntSeat DiscoYEntProCuts DiscoYEntProSeat DiscoYEntProDCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pd_in_f : forall o j, (j < dobj_off o / 8 \/ (dobj_off o + dobj_size o + 7) / 8 <= j) -> dsh_in o j = false.
Proof.
intros o j [Hlt | Hge]; unfold dsh_in.
- apply andb_false_intro1. apply Z.leb_gt. exact Hlt.
- apply andb_false_intro2. apply Z.ltb_ge. exact Hge.
Qed.

Lemma pd_in_t : forall o j, dobj_off o / 8 <= j < (dobj_off o + dobj_size o + 7) / 8 -> dsh_in o j = true.
Proof.
intros o j [H1 H2]. unfold dsh_in. apply andb_true_intro. split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2].
Qed.

Lemma pd_sh_T : forall j, 270 <= j < 320 -> dsh_loop j = 0.
Proof.
intros j Hj. unfold dsh_loop, dsh. cbn [dsh_look dobjs].
rewrite (pd_in_f OCUR j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((32 + 144 + 7) / 8); lia)).
rewrite (pd_in_f OO j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((240 + 1296 + 7) / 8); lia)).
rewrite (pd_in_f OUSED j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1664 + 32 + 7) / 8); lia)).
rewrite (pd_in_f OMAC j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1728 + 18 + 7) / 8); lia)).
rewrite (pd_in_f ONM j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1792 + 24 + 7) / 8); lia)).
rewrite (pd_in_f OTOK j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1856 + 24 + 7) / 8); lia)).
rewrite (pd_in_f ODISP j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1920 + 48 + 7) / 8); lia)).
rewrite (pd_in_f OWID j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((2000 + 24 + 7) / 8); lia)).
rewrite (pd_in_f OAGE j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((2064 + 24 + 7) / 8); lia)).
rewrite (pd_in_f OOUR j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((2128 + 6 + 7) / 8); lia)).
rewrite (pd_in_t OT j ltac:(cbn [dobj_off dobj_size]; vm_compute (2160 / 8); vm_compute ((2160 + 400 + 7) / 8); lia)).
cbn [live_loop]. unfold dsh_live. cbn [dobj_off dobj_size].
rewrite (proj2 (Z.ltb_lt _ _)); [reflexivity | vm_compute ((2160 + 400) / 8); lia].
Qed.

Lemma pd_sh_G : forall j, 328 <= j < 361 -> dsh_loop j = 0.
Proof.
intros j Hj. unfold dsh_loop, dsh. cbn [dsh_look dobjs].
rewrite (pd_in_f OCUR j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((32 + 144 + 7) / 8); lia)).
rewrite (pd_in_f OO j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((240 + 1296 + 7) / 8); lia)).
rewrite (pd_in_f OUSED j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1664 + 32 + 7) / 8); lia)).
rewrite (pd_in_f OMAC j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1728 + 18 + 7) / 8); lia)).
rewrite (pd_in_f ONM j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1792 + 24 + 7) / 8); lia)).
rewrite (pd_in_f OTOK j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1856 + 24 + 7) / 8); lia)).
rewrite (pd_in_f ODISP j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((1920 + 48 + 7) / 8); lia)).
rewrite (pd_in_f OWID j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((2000 + 24 + 7) / 8); lia)).
rewrite (pd_in_f OAGE j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((2064 + 24 + 7) / 8); lia)).
rewrite (pd_in_f OOUR j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((2128 + 6 + 7) / 8); lia)).
rewrite (pd_in_f OT j ltac:(cbn [dobj_off dobj_size]; right; vm_compute ((2160 + 400 + 7) / 8); lia)).
rewrite (pd_in_t OG j ltac:(cbn [dobj_off dobj_size]; vm_compute (2624 / 8); vm_compute ((2624 + 264 + 7) / 8); lia)).
cbn [live_loop]. unfold dsh_live. cbn [dobj_off dobj_size].
rewrite (proj2 (Z.ltb_lt _ _)); [reflexivity | vm_compute ((2624 + 264) / 8); lia].
Qed.

Lemma pd_sh_L0 : dsh_loop 370 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma pd_sh_L1 : dsh_loop 371 = 4.
Proof. vm_compute. reflexivity. Qed.

Lemma pd_sh_O : dsh_loop 266 = 6.
Proof. vm_compute. reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pd_sh_val : forall (cx : dcx) (shf : Z -> Z) acs (W : world SEGS) m,
  sh_region_ok shf (fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH (dsh_chunks shf)) = true ->
  0 <= shadow_addr (d_FB cx) < 2 ^ 64 ->
  p_frame cx shf acs W m ->
  forall k, 0 <= k < DFRAME_SH -> aview SEGS (w_H W) m (shadow_addr (d_FB cx) + k) = Some (shf k).
Proof.
intros cx shf acs W m Hok Hsh (E & HE & HRG & _) k Hk.
pose proof HE as (_ & _ & _ & _ & _ & ESH).
unfold p_regions in HRG. apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv in HRG.
destruct (sh_region_bytes SEGS E (rd W m) shf _ Hok HRG k Hk) as (Hr & Hm).
assert (Hb : base_val E (YP09.r_base (fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH (dsh_chunks shf)))
             = shadow_addr (d_FB cx)).
{ cbn [base_val YP09.r_base fshadow_region]. rewrite ESH. unfold w64. apply unsigned_lit_small. exact Hsh. }
rewrite Hb in Hm. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

Definition pd_sr_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 19%nat => SOff 32 0 | 27%nat => SOff AT_SH 0
  | _ => SOff (AT_X + r) 0
  end.
Definition pd_vals (regs : bvmap 5 word) (h : Z) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ [w64 h].
Definition pd_acs : list YP09.chunk := [YP09.mkChunk 184 (CVal 8 (SOff (AT_X + 32) 0))].
Definition pd_sr : list sv := map pd_sr_x (seq 0 32).


Lemma pd_ra_range : forall (cx : dcx) (shf : Z -> Z) (W : world SEGS) m off n,
  (forall k, 0 <= k < DFRAME_SH -> aview SEGS (w_H W) m (shadow_addr (d_FB cx) + k) = Some (shf k)) ->
  d_FB cx mod 8 = 0 -> 0 <= off -> 0 <= n -> off + n <= 8 * DFRAME_SH ->
  (forall q, 0 <= q < n -> saddr_ok (off + q) (shf ((off + q) / 8))) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + off) n.
Proof.
intros cx shf W m off n HS HFB Hoff Hn Hlim Hok x Hx.
set (q := x - (d_FB cx + off)).
assert (Hq : 0 <= q < n) by (unfold q; lia).
assert (Hdiv : x / 8 = d_FB cx / 8 + (off + q) / 8).
{ replace x with (d_FB cx + (off + q)) by (unfold q; lia).
  rewrite (Z.div_mod (d_FB cx) 8) at 1 by lia. rewrite HFB, Z.add_0_r.
  rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
assert (Hmod : x mod 8 = (off + q) mod 8).
{ replace x with (d_FB cx + (off + q)) by (unfold q; lia).
  rewrite Zplus_mod, HFB, Z.add_0_l, Zmod_mod. reflexivity. }
exists (shf ((off + q) / 8)). split.
- unfold shadow_of_addr. rewrite Hdiv.
  replace (SHADOW_OFF + (d_FB cx / 8 + (off + q) / 8)) with (shadow_addr (d_FB cx) + (off + q) / 8)
    by (unfold shadow_addr; lia).
  apply HS. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
- unfold saddr_ok. rewrite Hmod. exact (Hok q Hq).
Qed.

Lemma pd_rok_move : forall E (m m' : word -> option byte) r,
  region_ok SEGS E m r ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  (forall c, In c (YP09.r_chunks r) -> forall i, 0 <= i < YP09.c_len c ->
     mbyte SEGS m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     mbyte SEGS m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  region_ok SEGS E m' r.
Proof.
intros E m m' r HR Hw Hc. unfold region_ok in HR |- *. cbv zeta in HR |- *.
destruct HR as (H1 & H2 & _ & H4).
split; [exact H1|]. split; [exact H2|]. split; [exact Hw|].
apply Forall_forall. intros c Hcin i Hi.
destruct (proj1 (Forall_forall _ _) H4 c Hcin i Hi) as (b & Hb & Hm).
exists b. split; [exact Hb|]. rewrite (Hc c Hcin i Hi). exact Hm.
Qed.

Lemma pd_val_kept : forall (W : world SEGS) m (W2 : world SEGS) m2 a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W2 m2) a n v.
Proof.
intros W m W2 m2 a n v HK HV j Hj. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) m m2).
- exact (HV j Hj).
- apply HK. lia.
Qed.

Lemma pd_regs_ok : forall cx E regs h (B : asyms), d_E cx E -> p_rbase cx regs B ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= shadow_addr (d_FB cx) < 2 ^ 64 ->
  regs_ok (d_env cx E (pd_vals regs h)) pd_sr regs.
Proof.
intros cx E regs h B HE HL HA HSH.
destruct HE as (HER & H32 & _ & HA60 & _ & HSH529).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H27).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx))
  by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx))
  by (rewrite (HER 2%nat 2%bv eq_refl); unfold d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
change AT_A with 60%nat in HA60. change AT_SH with 529%nat in HSH529.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
          | rewrite HSH529; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27 ]
  | rewrite Z.add_0_r; unfold d_env, havoc, pd_vals;
    cbn [ew Nat.ltb Nat.leb Nat.sub nth map seq app Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Lemma pd_chain : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  bad_next (d_S cx) (ly_top ly3) (s0Z (c_regs cx)) = true \/
  fpchain (rdword (aview SEGS (w_H W3) mem3)) (s0Z (c_regs cx)) (ly_top ly3) [].
Proof.
intros cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
destruct HB as ((HPRE & _) & _).
destruct HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _ & Hch & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly3 & _ & _ & _ & _ & _ & _ & Hkeep & _).
destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
rewrite Etop. change (spZ (c_regs cx)) with (d_S cx) in *.
pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hs0r.
change (bv_unsigned (getr (c_regs cx) 8)) with (s0Z (c_regs cx)) in Hs0r.
destruct Hch as [(Hv & _) | (Hv1 & Hv2 & Hv3 & Hfp & _)].
- left. unfold bad_next. destruct Hv as [Hv | [Hv | Hv]].
  + apply Bool.orb_true_iff; left; apply Bool.orb_true_iff; left; apply Z.leb_le. unfold LLVMF_STK in *. lia.
  + apply Bool.orb_true_iff; left; apply Bool.orb_true_iff; right; apply Z.leb_le. lia.
  + apply Bool.orb_true_iff; right. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hv.
- right. cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hr2). exists r. split; [|exact Hr2].
  rewrite <- Hr. apply rdword_ext. intros kk Hkk. apply Hkeep; unfold LLVMF_STK in *; lia.
Qed.
Lemma pd_achain : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_A cx + 16 <= d_S cx -> d_S cx mod 8 = 0 ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 8) = Some RA_LLVMF ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 16) = Some (s0Z (c_regs cx)) ->
  exists ch, achain ly3 (aview SEGS (w_H W3) mem3) (d_A cx) (d_S cx) ch.
Proof.
intros cx ly3 S3 W3 mem3 md3 k HC HA16 HS8 HR8 HR16.
pose proof (pd_chain cx ly3 S3 W3 mem3 md3 k HC) as HCH.
destruct (Z_lt_le_dec (d_S cx) (ly_top ly3 - 16)) as [Hlt | Hge].
- exists [(d_S cx, RA_LLVMF, s0Z (c_regs cx))]. right.
  split; [lia|]. split; [lia|]. split; [exact HS8|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact HS8|]. split; [exact HR8|]. split; [exact HR16|].
    split; [unfold RA_LLVMF; lia|].
    destruct (bad_next (d_S cx) (ly_top ly3) (s0Z (c_regs cx))) eqn:Hbn; [reflexivity|].
    destruct HCH as [Hb | Hf]; [congruence | exact Hf].
  + apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Section fx.
Context {fx : YK11.FPState}.
Lemma pd_aj_callF : forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) spw raw ch1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  YP0l.st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom SEGS)) mdc)
     (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
        c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
        (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
        (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
        ajournal SEGS B STK1 (spZ (ms_regs ms)) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
        aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr SEGS W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
       (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
       ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o spw raw ch1 K
  HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite YP0m.denot_SOff, HE2, Hspw. apply YP0m.zcanon_small. lia. }
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr & Hcs & HJ1 & HP & HK).
exists fx', ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hfr|]. split; [exact Hcs|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End fx.
End h.
Lemma pd_frm0 : forall (fa fb : YK11.FPState), lib.Lib.FP.frm0 (@YK11.fp_csr fa) ->
  (@YK11.fp_csr fb = @YK11.fp_csr fa \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fb)) 5) 7 = 0) ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fb).
Proof. intros fa fb H [E | E]; [rewrite E; exact H | exact E]. Qed.
End f.
End d.
