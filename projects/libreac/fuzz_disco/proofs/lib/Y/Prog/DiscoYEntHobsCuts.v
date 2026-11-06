(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 4602 of its 4661 lines of code are new or changed and 310 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntStep.v, with its module paths changed; 197 of its 257 lines of code are new or changed and 4601 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_frame_clean_len_c slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require RoleOf CheckTable CheckSighting.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition HB_P1 : Z := 0xdfc.
Definition HB_P2 : Z := 0xe18.
Definition HB_P3 : Z := 0xe88.
Definition HB_P4 : Z := 0xea0.

Lemma hb_frm0_post : forall fx fx' : YK11.FPState, lib.Lib.FP.frm0 (@YK11.fp_csr fx) ->
  (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fx').
Proof. intros fx fx' H0 [E | E]; [rewrite E; exact H0 | exact E]. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).

Definition hb_mac (cx : dcx) (nb fr len : Z) : list byte :=
  if 11 <? len then sub (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) 6 6 else our_of (c_pl cx).
Definition hb_X (cx : dcx) (op nb fr len : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  op mod 4 = 2 /\ 0 <= op < 256 /\ d_frm cx nb fr len W m /\
  d_spREC cx nb fr len W m /\ d_spOP cx op W m /\
  len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7).
Definition hb_role (cx : dcx) (h nb fr len v : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  (v = -1 \/ v = 0 \/ v = 1 \/ v = 2) /\
  exists H0 : list byte, length H0 = 480%nat /\
    garr8 SEGS (rd W m) h (map (fun b : byte => bv_unsigned b) H0) /\
    (v = 1 -> exists j, 0 <= j < n_of (sub H0 0 400) /\ mac_of (sub H0 0 400) j = hb_mac cx nb fr len /\
       role_of_e (sub H0 0 400) j = 1).
Definition hb_sg (cx : dcx) (nb fr len : Z) (A : list byte) (W : world SEGS) (m : word -> option byte) : Prop :=
  length A = 24%nat /\ garr8 SEGS (rd W m) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) A) /\
  sighting_facts A (firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx))
    (reac_frame_clean_len_model len) 1.

Definition hb_R1 (cx : dcx) (h i n now op nb fr len v : Z) : world SEGS -> config -> Prop :=
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx HB_P1 h i n now (dxb fr len) dsh_rec
    (fun regs => getr regs 22 = w64 1 /\ getr regs 26 = w64 now /\ getr regs 10 = w64 v /\
       getr regs 21 = w64 h)
    (fun W m => hb_X cx op nb fr len W m /\ hb_role cx h nb fr len v W m).
Definition hb_R2 (cx : dcx) (h i n now op nb fr len v r : Z) : world SEGS -> config -> Prop :=
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx HB_P2 h i n now (dxb fr len) dsh_rec
    (fun regs => getr regs 22 = w64 1 /\ getr regs 26 = w64 now /\ getr regs 23 = w64 v /\
       getr regs 10 = w64 r)
    (fun W m => hb_X cx op nb fr len W m /\ (v = -1 \/ v = 0 \/ v = 1 \/ v = 2) /\
       (r = -1 \/ r = 0 \/ r = 1) /\
       (0 <= r -> exists A, hb_sg cx nb fr len A W m /\ (v = 1 -> s_role A <> 2))).
Definition hb_R3 (cx : dcx) (h i n now op nb fr len v : Z) : world SEGS -> config -> Prop :=
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx HB_P3 h i n now (dxb fr len) dsh_rec
    (fun regs => getr regs 22 = w64 1 /\ getr regs 23 = w64 v)
    (fun W m => hb_X cx op nb fr len W m /\ (v = -1 \/ v = 0 \/ v = 1 \/ v = 2) /\
       exists A, hb_sg cx nb fr len A W m /\ (v = 1 -> s_role A <> 2)).
Definition hb_R4 (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx HB_P4 h i n now (dxb fr len) dsh_rec
    (fun regs => True) (fun W m => hb_X cx op nb fr len W m).

Definition hb_L1_stmt : Prop := forall cx h i n now op nb fr len W c,
  hobs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c ->
  SRr SEGS W c (fun W' c' => exists v, hb_R1 cx h i n now op nb fr len v W' c').
Definition hb_L2_stmt : Prop := forall cx h i n now op nb fr len v W c,
  hb_R1 cx h i n now op nb fr len v W c ->
  SRr SEGS W c (fun W' c' => exists r, hb_R2 cx h i n now op nb fr len v r W' c').
Definition hb_L3_stmt : Prop := forall cx h i n now op nb fr len v r W c,
  hb_R2 cx h i n now op nb fr len v r W c ->
  SRr SEGS W c (fun W' c' => hb_R3 cx h i n now op nb fr len v W' c' \/
     hb_R4 cx h i n now op nb fr len W' c').
Definition hb_L4_stmt : Prop := forall cx h i n now op nb fr len v W c,
  hb_R3 cx h i n now op nb fr len v W c -> SRr SEGS W c (hb_R4 cx h i n now op nb fr len).
Definition hb_L5_stmt : Prop := forall cx h i n now op nb fr len W c,
  hb_R4 cx h i n now op nb fr len W c ->
  SRr SEGS W c (r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len).

Theorem hb_compose : hb_L1_stmt -> hb_L2_stmt -> hb_L3_stmt -> hb_L4_stmt -> hb_L5_stmt ->
  hobs_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros L1 L2 L3 L4 L5. unfold hobs_spec. intros cx h i n now op nb fr len W c Hin.
eapply SRr_bind; [exact (L1 _ _ _ _ _ _ _ _ _ _ _ Hin)|]. intros W1 c1 _ (v & H1).
eapply SRr_bind; [exact (L2 _ _ _ _ _ _ _ _ _ _ _ _ H1)|]. intros W2 c2 _ (r & H2).
eapply SRr_bind; [exact (L3 _ _ _ _ _ _ _ _ _ _ _ _ _ H2)|]. intros W3 c3 _ [H3 | H4].
- eapply SRr_bind; [exact (L4 _ _ _ _ _ _ _ _ _ _ _ _ H3)|]. intros W4 c4 _ H4.
  exact (L5 _ _ _ _ _ _ _ _ _ _ _ H4).
- exact (L5 _ _ _ _ _ _ _ _ _ _ _ H4).
Qed.

Section g.
Hypothesis LAWS : AR_laws SEGS B.
#[local] Notation DCTX := (d_ctx B MT XM_LIB RLO RHI tfib_K).

Lemma hb_obj_read : forall cx ly3 S3 (W : world SEGS) m md k o stk,
  DCTX cx ly3 S3 W m md k -> d_shadow cx dsh_rec W m -> cl_obj_shb o = true -> 0 <= stk <= 16640 ->
  0 < d_obj cx o /\ d_obj cx o + dobj_size o <= 2 ^ 63 /\ d_obj cx o mod 8 = 0 /\
  amem_range (d_obj cx o) (dobj_size o) /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_obj cx o) (dobj_size o) /\
  shadow_hull_vis (aview SEGS (w_H W) m) (d_obj cx o) (dobj_size o) /\ off_img (d_obj cx o) (dobj_size o) /\
  d_obj cx o + dobj_size o <= d_A cx - stk /\
  (forall a, d_obj cx o <= a < d_obj cx o + dobj_size o -> apresent (w_H W) m a).
Proof.
intros cx ly3 S3 W m md k o stk HC Hsh Hb Hstk.
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (_ & Hlo & _ & HF0 & HFc & HFia & HFo & HFal & HFpres & _ & _ & HAR & Hfin & Efa & _).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & _).
pose proof alloc_ceiling_lt as HCL.
assert (Hob : dobj_off o + dobj_size o <= 3072 /\ 0 <= dobj_off o /\ 0 < dobj_size o /\ dobj_off o mod 8 = 0)
  by (destruct o; cbn; lia).
assert (HF8 : d_FB cx mod 8 = 0) by (rewrite <- (Z.mod_mod (d_FB cx) 32) in HFal by lia; lia).
pose proof (cl_obj_ra cx W m o Hsh HF8 ltac:(lia) Hb) as HRA.
unfold d_obj in *.
split; [lia|]. split; [lia|]. split; [clear - HF8 Hob; lia|].
split; [apply (amem_range_sub_app (d_FB cx) 4096); [exact HFia | lia | lia | lia | lia]|].
split; [exact HRA|].
split; [apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W m md DFRAME_CLASS (c_fpos cx));
  [exact HAR | exact Hfin | rewrite Efa; lia | rewrite Efa, cl_fs6; lia | lia]|].
split; [unfold off_img in *; lia|].
split; [unfold MFRAME, LLVMF_STK in *; lia|].
intros a Ha. apply HFpres. lia.
Qed.

Lemma hb_blk_read : forall cx h n shf nb fr len ly3 S3 (W : world SEGS) m md k stk,
  DCTX cx ly3 S3 W m md k -> d_body B cx h n (dxb fr len) shf ly3 S3 W m -> d_frm cx nb fr len W m ->
  len <= nb -> 0 < len -> 0 <= stk <= 16640 ->
  In (fr, len) (ablocks B ly3 S3) /\ 0 < fr /\ fr + len <= 2 ^ 63 /\ amem_range fr len /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF fr len /\ shadow_hull_vis (aview SEGS (w_H W) m) fr len /\
  off_img fr len /\ fr + len <= d_A cx - stk /\ (fr + req_size len <= d_FB cx \/ d_FB cx + 4096 <= fr) /\
  (forall a, fr <= a < fr + len -> apresent (w_H W) m a).
Proof.
intros cx h n shf nb fr len ly3 S3 W m md k stk HC HB (F1 & F2 & F3 & F4) Hlen H0 Hstk.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hbl & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (_ & Hlo & _ & HF0 & HFc & _ & _ & _ & _ & _ & _ & HAR & Hfin & Efa & _).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & _).
pose proof alloc_ceiling_lt as HCL.
assert (Hne : fr <> 0) by (intros E0; specialize (F2 E0); lia).
assert (Exb : dxb fr len = [(fr, len)])
  by (unfold dxb; replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne); reflexivity).
pose proof Hbl as (Hp & _ & _ & Hof).
rewrite Exb in Hp, Hof.
assert (Hin : In (fr, len) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp | left; reflexivity]).
apply Forall_inv_tail in Hof. apply Forall_inv in Hof. cbn [fst snd] in Hof.
destruct (al_blocks _ _ LAWS ly3 S3 W m md fr len HAR Hin) as (_ & Hfr0 & Hfrc & _ & Hfrp & _).
pose proof (req_size_pos len ltac:(lia)) as Hrq.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W m md fr len DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
rewrite Efa, cl_fs6 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
split; [exact Hin|]. split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly3 S3 W m md fr len fr len HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly3 S3 W m md fr len fr len HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W m md fr len fr len HAR Hin ltac:(lia) ltac:(lia) H0)|].
split; [unfold off_img in *; lia|].
split; [unfold MFRAME, LLVMF_STK in *; lia|].
split; [lia|].
intros a Ha. exact (proj1 (Hfrp a ltac:(lia))).
Qed.

Lemma hb_hblk_read : forall cx h n xb shf ly3 S3 (W : world SEGS) m md k stk,
  DCTX cx ly3 S3 W m md k -> d_body B cx h n xb shf ly3 S3 W m -> 0 <= stk <= 16640 ->
  In (h, HUNT_SIZE) (ablocks B ly3 S3) /\ 0 < h /\ h mod 8 = 0 /\ h + HUNT_SIZE <= 2 ^ 63 /\
  amem_range h HUNT_SIZE /\ range_addressable (aview SEGS (w_H W) m) SHADOW_OFF h HUNT_SIZE /\
  shadow_hull_vis (aview SEGS (w_H W) m) h HUNT_SIZE /\ off_img h HUNT_SIZE /\ h + HUNT_SIZE <= d_A cx - stk /\
  (h + HUNT_SIZE <= d_FB cx \/ d_FB cx + 4096 <= h) /\
  (forall a, h <= a < h + HUNT_SIZE -> apresent (w_H W) m a).
Proof.
intros cx h n xb shf ly3 S3 W m md k stk HC HB Hstk.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hbl & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (_ & Hlo & _ & HF0 & HFc & _ & _ & _ & _ & _ & _ & HAR & Hfin & Efa & _).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & _).
pose proof alloc_ceiling_lt as HCL.
pose proof Hbl as (Hp & _ & _ & Hof).
assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp | apply in_or_app; right; left; reflexivity]).
apply Forall_inv in Hof. cbn [fst snd] in Hof.
destruct (al_blocks _ _ LAWS ly3 S3 W m md h HUNT_SIZE HAR Hin) as (H16 & Hh0 & Hhc & _ & Hhp & _).
assert (HS : 0 < HUNT_SIZE) by (unfold HUNT_SIZE; lia).
pose proof (req_size_pos HUNT_SIZE ltac:(lia)) as Hrq.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W m md h HUNT_SIZE DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
rewrite Efa, cl_fs6 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
split; [exact Hin|]. split; [lia|]. split; [clear - H16; lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly3 S3 W m md h HUNT_SIZE h HUNT_SIZE HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly3 S3 W m md h HUNT_SIZE h HUNT_SIZE HAR Hin
  ltac:(lia) ltac:(lia))|].
split; [exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W m md h HUNT_SIZE h HUNT_SIZE HAR Hin
  ltac:(lia) ltac:(lia) HS)|].
split; [unfold off_img in *; lia|].
split; [unfold MFRAME, LLVMF_STK in *; lia|].
split; [lia|].
intros a Ha. exact (proj1 (Hhp a ltac:(lia))).
Qed.

Lemma hb_aj_call : forall (fq : YK11.FPState) (W : world SEGS) E ss (ms : machine_state) STK sp0 FP ly S W0 mem md own
  lyc Sc mdc k STK1 FP1 EV1 (o : Z) spw raw ch1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok (fx := fq) SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg (mkst (fx := fq) (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom SEGS)) mdc)
     (apost_base (fx := fq) SEGS B STK1 FP1 (ms_regs ms) lyc Sc W (ms_mem ms) mdc EV1 K)) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr SEGS W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       (@YK11.fp_csr fx' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
       ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros fq W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o spw raw ch1 K
  HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply YP0m.zcanon_small. appn; lia. }
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & _ & Hcsr & HJ1 & HP & HK).
exists fx', ly2, S2, regs2, mem2, md2. split; [rewrite Hra; reflexivity|]. split; [exact Hcsr|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | appn; lia | appn; lia | exact HF].
Qed.
End g.
End h.
End f.
End d.
