(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module names changed; 562 of its 602 lines of code are new or changed and 5 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC45 YC81 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt DiscoEntSeat DiscoRo DiscoEntBodyStmt DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_table reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model
disco_json_lemmas slot_ser_defs slot_ser_pure slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoArm3FieldCut DiscoArm3FieldMDBKit DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableAge.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition mdba_srx (c21 c24 : Z) (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0
  | 9%nat => SOff AT_A 0
  | 18%nat => SOff 32 0
  | 21%nat => SOff AT_F c21
  | 24%nat => SOff AT_F c24
  | _ => SOff (AT_X + r) 0
  end.
Definition mdba_sr (p : Z) : list sv := map (mdba_srx (240 + 144 * p) (2160 + 48 * p)) (seq 0 32).
Definition mdba_a3 (tk : bool) : sv :=
  if tk then SLit 0 else
  SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SOff 563 0) (SMd M_MUL (SOff 564 0) (SLit (-1)))) (SLit a3f_KDV))
    (SLit 18).
Definition mdba_fin_srx (c21 c24 : Z) (tk : bool) (r : nat) : sv :=
  match r with
  | 1%nat => SOff A_TEXT MDS_OFF
  | 10%nat => SOff AT_F 2064
  | 11%nat => SLit 24
  | 12%nat => SOff (A_OBJ 18) 0
  | 13%nat => mdba_a3 tk
  | 19%nat => SOff AT_F 2064
  | _ => mdba_srx c21 c24 r
  end.
Definition mdba_fin_sr (p : Z) (tk : bool) : list sv :=
  map (mdba_fin_srx (240 + 144 * p) (2160 + 48 * p) tk) (seq 0 32).
Definition mdba_acs : list YP09.chunk := [YP09.mkChunk 344 (CVal 8 (SOff 563 0))].
Definition mdba_fcs (p : Z) : list YP09.chunk := [YP09.mkChunk (2200 + 48 * p) (CVal 8 (SOff 564 0))].
Definition mdba_x : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 17)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit a3f_KDV))].
Definition mdba_rs (p : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ mdba_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ mdba_fcs p);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 258 261 (dsh_chunks dsh_md);
   got_regionP; bcell_regionP 32; mdba_x].
Definition mdba_ss0 (p : Z) : sstate := mkSS MO_OFF (mdba_sr p) (mdba_rs p) None (d_facts [] []).

Lemma mdba_subw : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.

Lemma mdba_submem : forall p, submem (mdba_rs p) (d_kregions dsh_md mdba_acs (mdba_fcs p) ++ [mdba_x]).
Proof.
  intros p. unfold mdba_rs, d_kregions, fshadow_region. cbn [app].
  apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply mdba_subw; lia|].
  apply submem_keep; [apply mdba_subw; lia|].
  apply submem_keep; [apply mdba_subw; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply subregion_refl|].
  apply submem_nil.
Qed.

Lemma mdba_wf : forall p, 0 <= p < 8 -> regions_wf (mdba_rs p) = true.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma mdba_kwf : forall p, 0 <= p < 8 -> regions_wf (d_kregions dsh_md mdba_acs (mdba_fcs p) ++ [mdba_x]) = true.
Proof.
  intros p Hp. assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma mdba_inw : forall E p a, in_wrange E (mdba_rs p) a ->
  base_val E (Some AT_SH) + 258 <= a < base_val E (Some AT_SH) + 261.
Proof.
  intros E p a (r & Hin & Hr). unfold mdba_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [] ] ] ] ] ] ] ];
    unfold got_regionP, bcell_regionP, mdba_x in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.

Lemma mdba_awr_skel : forall E rs rs' STK sp0 FP bl0 blc ly own,
  awr_ok E rs' STK sp0 FP bl0 blc ly own -> skeleton rs = skeleton rs' -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs rs' STK sp0 FP bl0 blc ly own H Hsk a Ha. apply H. eapply in_wrange_skeleton; [exact Hsk | exact Ha].
Qed.

Lemma mdba_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.

Lemma mdba_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, mdba_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Lemma mdba_u8_range : forall (T : list byte) (k : Z), 0 <= disco_table_c.u_at T k 8 < 2 ^ 64.
Proof.
  intros T k. unfold disco_table_c.u_at.
  pose proof (disco_table.ble_range (disco_table_c.sub T k 8)) as H.
  assert (HL : (length (disco_table_c.sub T k 8) <= 8)%nat).
  { unfold disco_table_c.sub. rewrite length_firstn. lia. }
  assert (HP : 2 ^ (8 * Z.of_nat (length (disco_table_c.sub T k 8))) <= 2 ^ 64).
  { apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma mdba_age_denot : forall E x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> y < x ->
  U E (SOff 563 0) = x -> U E (SOff 564 0) = y ->
  sv_denot E (mdba_a3 false) = Z_to_bv 64 ((x - y) / 1000000).
Proof.
  intros E x y Hx Hy Hxy H3 H4.
  transitivity (Z_to_bv 64 (U E (mdba_a3 false))); [unfold U; symmetry; apply Z_to_bv_bv_unsigned|].
  f_equal. cbn [mdba_a3].
  rewrite !U_SAlu, !U_SMd, !U_SAlu, !U_SMd, H3, H4, !U_SLit.
  cbn [zalu_raw zmd_raw]. change (Z.of_N 64) with 64.
  unfold zcanon, M64.
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace (a3f_KDV mod 2 ^ 64) with a3f_KDV by reflexivity.
  replace (Z.land (18 mod 2 ^ 64) 63) with 18 by reflexivity.
  assert (E1 : (x + (y * (2 ^ 64 - 1)) mod 2 ^ 64) mod 2 ^ 64 = x - y).
  { rewrite Z.add_mod_idemp_r by lia. replace (x + y * (2 ^ 64 - 1)) with ((x - y) + y * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite E1. rewrite !Z.shiftr_div_pow2 by lia.
  assert (HK : 0 <= a3f_KDV < 2 ^ 64) by (unfold a3f_KDV; lia).
  assert (HM : 0 <= (x - y) * a3f_KDV / 2 ^ 64 < 2 ^ 64).
  { split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small ((x - y) * a3f_KDV / 2 ^ 64)) by exact HM.
  assert (HD : 0 <= (x - y) * a3f_KDV / 2 ^ 64 / 2 ^ 18 < 2 ^ 64).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small _ _ HD).
  exact (a3f_quot (x - y) ltac:(lia)).
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma mdba_app_nsh : forall F lo n x, in_app lo n -> 0 <= F -> F + 4096 <= CEIL_MAX ->
  lo <= x < lo + n -> ~ (shadow_addr F <= x < shadow_addr F + 512).
Proof.
  intros F lo n x Ha HF0 HF1 Hx Hs. unfold in_app, kLowShadowBeg, kHighMemBeg in Ha.
  unfold shadow_addr, SHADOW_OFF in Hs. destruct Ha as (Ha1 & [Ha2 | (Ha2 & _)]); lia.
Qed.

Lemma mdba_fsh_nrd : forall (B : asyms) (cx : dcx) h a,
  in_app (d_FB cx) 4096 -> 0 <= d_FB cx -> d_FB cx + 4096 <= CEIL_MAX -> in_app h 480 ->
  (0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))) ->
  (forall x, in_roP SEGS pa_relro_lo pa_relro_hi x -> 0 <= x < kLowMemEnd) ->
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ d_rdset B cx h a.
Proof.
  intros B cx h a HF HF0 HF1 Hh Hp Hro Ha Hr.
  unfold d_rdset, d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. unfold HUNT_SIZE in Hr.
  destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
  - exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdba_app_nsh (d_FB cx) h 480 a Hh HF0 HF1 ltac:(lia) Ha).
  - pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    exact (mdba_app_nsh (d_FB cx) (c_p cx) (req_size (c_n cx)) a (Hp Hc) HF0 HF1 ltac:(lia) Ha).
  - assert (Hra : 0 <= a < kLowMemEnd) by (first [exact (Hro a Hr) | exact (Hro a (proj1 Hr))]).
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  - unfold AE2k.FF_canary, shadow_addr, SHADOW_OFF in *. pose proof (Z.div_pos (d_FB cx) 8 HF0 ltac:(lia)). lia.
Qed.

Lemma mdba_env_reg : forall (cx : dcx) (E : env) (regs : bvmap 5 word) (ex : list word) (r : bv 5) (a : nat),
  a = (AT_X + Z.to_nat (bv_unsigned r))%nat -> ew (d_env cx E (a3f_vals regs ++ ex)) a = getr regs r.
Proof.
  intros cx E regs ex r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (rewrite length_app; unfold a3f_vals; rewrite length_map, length_seq; lia).
  rewrite app_nth1 by (unfold a3f_vals; rewrite length_map, length_seq; lia).
  unfold a3f_vals.
  set (f := fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))).
  rewrite (nth_indep _ (Z_to_bv 64 0) (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. unfold f. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma mdba_env_ex : forall (cx : dcx) (E : env) (regs : bvmap 5 word) (ex : list word) (j : nat),
  (j < length ex)%nat -> ew (d_env cx E (a3f_vals regs ++ ex)) (AT_X + (32 + j)) = nth j ex (Z_to_bv 64 0).
Proof.
  intros cx E regs ex j Hj.
  assert (L : length (a3f_vals regs) = 32%nat) by (unfold a3f_vals; rewrite length_map, length_seq; reflexivity).
  rewrite d_env_x by (rewrite length_app, L; lia).
  rewrite app_nth2 by (rewrite L; lia). rewrite L. f_equal. lia.
Qed.

Lemma mdba_regs_ok : forall (cx : dcx) (E : env) (regs : bvmap 5 word) (ex : list word) (c21 c24 : Z),
  d_E cx E -> 0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 64 ->
  getr regs 9 = w64 (d_A cx) -> getr regs 18 = w64 SHADOW_OFF ->
  getr regs 21 = w64 (d_FB cx + c21) -> getr regs 24 = w64 (d_FB cx + c24) ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) (map (mdba_srx c21 c24) (seq 0 32)) regs.
Proof.
  intros cx E regs ex c21 c24 HE HA HF H9 H18 H21 H24.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as (HER & H32 & _ & HA60 & HF516 & _).
  unfold AT_A in HA60. unfold AT_F in HF516.
  assert (UA : bv_unsigned (ew (d_env cx E (a3f_vals regs ++ ex)) 60) = d_A cx).
  { rewrite HA60. unfold w64. apply unsigned_lit_small. exact HA. }
  assert (UF : bv_unsigned (ew (d_env cx E (a3f_vals regs ++ ex)) 516) = d_FB cx).
  { rewrite HF516. unfold w64. apply unsigned_lit_small. exact HF. }
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<- | Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | rewrite UA, Z.add_0_r; exact H9
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18
    | rewrite UF; first [exact H21 | exact H24]
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (mdba_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.

Definition mdba_run_stmt (p : Z) : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E (mdba_ss0 p) (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (mdba_rs p) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall (tk : bool) (ss : sstate) (ms' : machine_state) (mat' : list word),
     branch_taken BC_GEU (sv_denot E (SOff 564 0)) (sv_denot E (SOff 563 0)) = tk ->
     ss_regs ss = mdba_fin_sr p tk -> ss_resv ss = None ->
     d_land_chk dsh_age (ss_mem ss) = true ->
     YP0l.st_ok (fx := fq) SEGS E (YP0l.setpc ss (SIGMA DS___interceptor_trampoline_snprintf)) (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (mdba_rs p) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.

Ltac mdba_post POST HS HJ HF2 HG2 HFr1 HG1 Hc tk :=
  try (rewrite wvb_collapse in HJ); try rewrite wvb_collapse;
  lazymatch type of HS with
  | st_ok _ _ (setpc ?s _) _ =>
    apply (POST tk s _ _ Hc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) HS HJ);
    [ refine (frame_of_trans _ _ _ _ _ _ _ HFr1 HF2); vm_compute; reflexivity
    | exact (mem_grows_trans _ _ _ HG1 HG2) ]
  end.

Lemma mdba_run : forall p, 0 <= p < 8 -> mdba_run_stmt p.
Proof.
  intros p Hp8 fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ Hawr POST.
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  assert (Hp : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct Hp as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  ( paj_run_tok RUN HS HJ SHOK (0, 0);
    [ exact Hawr
    | rename HF into HF1; rename HFr into HFr1; rename HG into HG1;
      psrr_branch_tok RUN BR HS SHOK (0, 0);
      [ paj_run_tok RUN HS HJ SHOK (0, 0);
        [ apply (mdba_awr_skel _ _ _ _ _ _ _ _ _ _ Hawr); vm_compute; reflexivity
        | mdba_post POST HS HJ HFr HG HFr1 HG1 Hc true ]
      | paj_run_tok RUN HS HJ SHOK (0, 0);
        [ apply (mdba_awr_skel _ _ _ _ _ _ _ _ _ _ Hawr); vm_compute; reflexivity
        | mdba_post POST HS HJ HFr HG HFr1 HG1 Hc false ] ] ]).
Qed.

Lemma mdba_main : forall p, 0 <= p < 8 -> mdba_run_stmt p -> mdbA_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp8 RUNJ cx h i n now op W0 c0 T0 T1 buf count os vpad W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R26 & R21 & R24) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
destruct HY as (HSL & H392 & H408 & HUSED). destruct HSL as (Hp & H368 & H336).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (a3f_count T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296).
{ rewrite (mdba_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (LU : length (a3f_used (p + 1)) = 32%nat) by (unfold a3f_used; reflexivity).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & _).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as (Hceil & _).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
assert (Hinh : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. right. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinh) as (_ & _ & _ & HhA & _).
change (req_size HUNT_SIZE) with 480 in HhA.
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hcn. pose proof HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (HSTR : dimg_strs W mem3).
{ destruct (DCRO LAWS (conj DRO (conj GM (HV))) ly3 S3 W mem3 md3 HAR3 HIMG) as (_ & _ & _ & HS4 & _).
  exact HS4. }
pose proof HSTR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K17 & _).
pose proof HSP0 as (S232 & S344).
assert (HLS : val_mem SEGS (rd W mem3) (d_FB cx + (2200 + 48 * p)) 8 (disco_table_c.last_of T1 p)).
{ replace (d_FB cx + (2200 + 48 * p)) with (d_obj cx OT + (48 * p + 40)) by (unfold d_obj, dobj_off; lia).
  unfold disco_table_c.last_of.
  apply (ReacDiscoTableAge.age_val (rd W mem3) T1 (d_obj cx OT) (48 * p + 40) 8 HGT); [lia | rewrite HLT1; lia]. }
assert (HLSr : 0 <= disco_table_c.last_of T1 p < 2 ^ 64)
  by (unfold disco_table_c.last_of; apply mdba_u8_range).
remember (a3f_vals regs ++ [Z_to_bv 64 now; Z_to_bv 64 (disco_table_c.last_of T1 p)]) as vals eqn:Hvals.
assert (E563 : ew (d_env cx E vals) 563 = Z_to_bv 64 now).
{ rewrite Hvals. change 563%nat with (AT_X + (32 + 0))%nat. rewrite mdba_env_ex by (cbn; lia). reflexivity. }
assert (E564 : ew (d_env cx E vals) 564 = Z_to_bv 64 (disco_table_c.last_of T1 p)).
{ rewrite Hvals. change 564%nat with (AT_X + (32 + 1))%nat. rewrite mdba_env_ex by (cbn; lia). reflexivity. }
pose proof (d_E_env cx E vals HE) as HE'.
pose proof HE' as (EE' & E32' & HEI' & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E vals) AT_A) = d_A cx)
  by (rewrite E60'; unfold w64; apply unsigned_lit_small; lia).
assert (U516 : bv_unsigned (ew (d_env cx E vals) AT_F) = d_FB cx)
  by (rewrite EF'; unfold w64; apply unsigned_lit_small; lia).
assert (U529 : bv_unsigned (ew (d_env cx E vals) AT_SH) = shadow_addr (d_FB cx)).
{ rewrite ESH'. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (U2 : bv_unsigned (ew (d_env cx E vals) AT_STK) = d_S cx).
{ unfold AT_STK. rewrite (EE' 2%nat 2%bv eq_refl). reflexivity. }
assert (U32 : bv_unsigned (ew (d_env cx E vals) 32) = SHADOW_OFF).
{ rewrite E32'. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U17 : bv_unsigned (ew (d_env cx E vals) (A_OBJ 17)) = VAL (A_OBJ 17))
  by (apply HEI'; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U1 : bv_unsigned (ew (d_env cx E vals) (A_OBJ 1)) = VAL (A_OBJ 1))
  by (apply HEI'; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U66 : bv_unsigned (ew (d_env cx E vals) (A_OBJ 66)) = VAL (A_OBJ 66))
  by (apply HEI'; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (V17 : VAL (A_OBJ 17) = 0x10370) by exact (pa_obj_val 17 ltac:(vm_compute; lia)).
assert (V1 : VAL (A_OBJ 1) = 0xa0510) by exact (pa_obj_val 1 ltac:(vm_compute; lia)).
assert (V66 : VAL (A_OBJ 66) = 0xa90b8) by exact (pa_obj_val 66 ltac:(vm_compute; lia)).
assert (Hregs : regs_ok (d_env cx E vals) (mdba_sr p) regs).
{ unfold mdba_sr. rewrite Hvals.
  apply (mdba_regs_ok cx E regs _ _ _ HE ltac:(lia) ltac:(lia) Rs1 Rs2).
  - rewrite R21; unfold w64, d_obj, dobj_off; f_equal; lia.
  - rewrite R24; unfold w64, d_obj, dobj_off; f_equal; lia. }
assert (HGf : facts_ok (d_env cx E vals) (d_facts [] [])).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HCTX HE); exact I. }
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) mdba_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 344 8%N (SOff 563 0) now).
  - cbn [sv_denot]. rewrite E563, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact S344. }
assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) (mdba_fcs p)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) (2200 + 48 * p) 8%N (SOff 564 0) (disco_table_c.last_of T1 p)).
  - cbn [sv_denot]. rewrite E564, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact HLS. }
assert (Hext : Forall (region_ok SEGS (d_env cx E vals) (rd W mem3)) [mdba_x]).
{ apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, mdba_x. cbv zeta.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U17, V17. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ 0x10370 0 8%N (SLit a3f_KDV) a3f_KDV).
  - reflexivity.
  - unfold a3f_KDV. cbn. lia.
  - cbn. lia.
  - rewrite Z.add_0_r, <- V17. exact K17. }
assert (Hdx : Forall (fun r => all_disjoint (d_env cx E vals) r (d_kregions dsh_md mdba_acs (mdba_fcs p))) [mdba_x]).
{ apply Forall_cons; [|apply Forall_nil].
  unfold d_kregions, mdba_x, fshadow_region, got_regionP, bcell_regionP. cbn [all_disjoint].
  unfold extent_disjoint. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U2, U60, U516, U529, U17, U1, U66, V17, V1, V66.
  change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in GFoff.
  unfold shadow_addr, SHADOW_OFF.
  repeat split; lia. }
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E MO_OFF (mdba_sr p) vals mdba_acs (mdba_fcs p)
  [mdba_x] (d_facts [] []) HCTX HE HREG HFLAG Hregs HGf Hacs Hfcs Hext (conj I I) Hdx (mdba_kwf p Hp8)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (mdba_rs p) HS0 (mdba_submem p) (mdba_wf p Hp8)) as HS.
clear HS0.
assert (Hawr : awr_ok (d_env cx E vals) (mdba_rs p) LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx))
  (ablocks B ly3 S3) ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ unfold mdba_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ AT_SH (shadow_addr (d_FB cx))); [reflexivity | exact U529 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold mdba_x; cbn; lia|].
  apply awr_ok_nil. }
unfold cfg_at, w64.
apply (RUNJ fq W (d_env cx E vals) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + MO_OFF)) mem3 (YK11.seg_rom SEGS))
  md3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 k _
  HEI' HS HJ Hawr).
intros tk ss ms1 mat1 Htk Hsr Hrv Hchk HS1 HJ1 HFr1 HG1.
cbn [ms_mem YK11.mkst] in HFr1, HG1.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  rd W (ms_mem ms1) (Z_to_bv 64 a) = rd W mem3 (Z_to_bv 64 a)).
{ intros a Ha H2. apply HFr1. rewrite unsigned_lit_small by lia. intros Hw. apply mdba_inw in Hw.
  change (base_val (d_env cx E vals) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E vals) AT_SH)) in Hw.
  rewrite U529 in Hw. lia. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  mbyte SEGS (rd W (ms_mem ms1)) a = mbyte SEGS (rd W mem3) a).
{ intros a Ha H2. unfold mbyte. rewrite (KM a Ha H2). reflexivity. }
assert (KVA : forall off v, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + off) 8 v).
{ intros off v H0 H1 Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KB; [lia |].
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (KGF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms1)) a l).
{ intros a l H0 H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia |]. exact (mdba_app_nsh (d_FB cx) (d_FB cx) 4096 x GFapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (KGB : forall l, Z.of_nat (length l) <= req_size (Z.max (slot_ser_defs.ser_cap op) 1) ->
  garr8 SEGS (rd W mem3) buf l -> garr8 SEGS (rd W (ms_mem ms1)) buf l).
{ intros l H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia |]. exact (mdba_app_nsh (d_FB cx) buf _ x Hbapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (QR : forall r, getr (ms_regs ms1) r = sv_denot (d_env cx E vals) (sr_get (mdba_fin_sr p tk) r)).
{ intros r. rewrite (st_ok_restrict_reg SEGS (w_H W) (d_env cx E vals) _ ms1 r HS1). cbn [ss_regs YP0l.setpc].
  rewrite Hsr. reflexivity. }
assert (QA : forall (r : bv 5) (a : nat), a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  sr_get (mdba_fin_sr p tk) r = SOff a 0 -> getr (ms_regs ms1) r = getr regs r).
{ intros r a Ha Hs. rewrite QR, Hs. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite Hvals.
  exact (mdba_env_reg cx E regs _ r a Ha). }
assert (Q2 : getr (ms_regs ms1) 2 = getr regs 2) by exact (QA 2%bv 533%nat eq_refl eq_refl).
assert (Q3 : getr (ms_regs ms1) 3 = getr regs 3) by exact (QA 3%bv 534%nat eq_refl eq_refl).
assert (Q4 : getr (ms_regs ms1) 4 = getr regs 4) by exact (QA 4%bv 535%nat eq_refl eq_refl).
assert (Q8 : getr (ms_regs ms1) 8 = getr regs 8) by exact (QA 8%bv 539%nat eq_refl eq_refl).
assert (Q20 : getr (ms_regs ms1) 20 = getr regs 20) by exact (QA 20%bv 551%nat eq_refl eq_refl).
assert (Q25 : getr (ms_regs ms1) 25 = getr regs 25) by exact (QA 25%bv 556%nat eq_refl eq_refl).
assert (Q26 : getr (ms_regs ms1) 26 = getr regs 26) by exact (QA 26%bv 557%nat eq_refl eq_refl).
assert (Q1 : getr (ms_regs ms1) 1 = w64 (BASE + MDS_OFF)).
{ transitivity (sv_denot (d_env cx E vals) (SOff A_TEXT MDS_OFF)); [exact (QR (1%bv : bv 5))|].
  rewrite (codeptr_val _ MDS_OFF HEI'). reflexivity. }
assert (Q9 : getr (ms_regs ms1) 9 = w64 (d_A cx)).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_A 0)); [exact (QR (9%bv : bv 5))|].
  cbn [sv_denot]. rewrite U60. unfold w64; f_equal; lia. }
assert (Q18 : getr (ms_regs ms1) 18 = w64 SHADOW_OFF).
{ transitivity (sv_denot (d_env cx E vals) (SOff 32 0)); [exact (QR (18%bv : bv 5))|].
  cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity. }
assert (Q10 : getr (ms_regs ms1) 10 = w64 (d_obj cx OAGE)).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_F 2064)); [exact (QR (10%bv : bv 5))|].
  cbn [sv_denot]. rewrite U516. unfold w64, d_obj, dobj_off; f_equal; lia. }
assert (Q19 : getr (ms_regs ms1) 19 = w64 (d_obj cx OAGE)).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_F 2064)); [exact (QR (19%bv : bv 5))|].
  cbn [sv_denot]. rewrite U516. unfold w64, d_obj, dobj_off; f_equal; lia. }
assert (Q11 : getr (ms_regs ms1) 11 = w64 24).
{ transitivity (sv_denot (d_env cx E vals) (SLit 24)); [exact (QR (11%bv : bv 5))|]. reflexivity. }
assert (Q12 : getr (ms_regs ms1) 12 = w64 (VAL (A_OBJ 18))).
{ transitivity (sv_denot (d_env cx E vals) (SOff (A_OBJ 18) 0)); [exact (QR (12%bv : bv 5))|].
  cbn [sv_denot]. rewrite (HEI' (A_OBJ 18) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r. reflexivity. }
assert (Q21 : getr (ms_regs ms1) 21 = w64 (d_obj cx OO + 144 * p)).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_F (240 + 144 * p))); [exact (QR (21%bv : bv 5))|].
  cbn [sv_denot]. rewrite U516. unfold w64, d_obj, dobj_off; f_equal; lia. }
assert (Q13 : getr (ms_regs ms1) 13 = w64 (a3f_age T1 now p)).
{ transitivity (sv_denot (d_env cx E vals) (mdba_a3 tk)); [exact (QR (13%bv : bv 5))|].
  assert (U563 : U (d_env cx E vals) (SOff 563 0) = now) by (apply U_atom; [exact E563 | lia]).
  assert (U564 : U (d_env cx E vals) (SOff 564 0) = disco_table_c.last_of T1 p)
    by (apply U_atom; [exact E564 | exact HLSr]).
  rewrite branch_geu_U, U564, U563 in Htk.
  unfold a3f_age, disco_json_text.age_of.
  destruct tk.
  - apply negb_true_iff, Z.ltb_ge in Htk.
    replace (disco_table_c.last_of T1 p <? now) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  - apply negb_false_iff, Z.ltb_lt in Htk.
    rewrite (proj2 (Z.ltb_lt _ _) Htk).
    rewrite (mdba_age_denot (d_env cx E vals) now (disco_table_c.last_of T1 p) Hnow HLSr Htk U563 U564).
    reflexivity. }
pose proof (KVA 216 h ltac:(lia) ltac:(lia) H216) as H216'.
pose proof (KVA 152 (h + 440) ltac:(lia) ltac:(lia) H152) as H152'.
assert (HS1p : st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals)
  (YP0l.setpc ss (SIGMA DS___interceptor_trampoline_snprintf - BASE)) (restrict (w_H W) ms1)).
{ unfold st_ok_pi, abs_ss, YP0l.setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
  replace (BASE + (SIGMA DS___interceptor_trampoline_snprintf - BASE)) with (SIGMA DS___interceptor_trampoline_snprintf)
    by lia.
  exact HS1. }
assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat1 md3) k)
  by exact (conj HBASE (conj HJ1 HFR)).
destruct (DLAND LAWS FFL fq cx h dsh_age ly3 S3 W (with_vm_backing (m_vm_lazy md3) mat1 md3) k (d_env cx E vals) _ ms1
  HCTX1 HE' (d_env_fl cx E vals) HS1p Hchk H216' H152') as (HFRM1 & HSHD1).
assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_age ly3 S3 W (ms_mem ms1)).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_md dsh_age ly3 S3 W mem3 (ms_mem ms1) (d_A cx) (d_A cx)
    (d_fsh cx) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right.
    unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
    exact (mdba_fsh_nrd B cx h a GFapp ltac:(lia) ltac:(lia) HhA HpA Hro Ha).
  - intros a Ha Hna. apply (aview_eq_of SEGS). apply KM; [exact Ha|].
    intros H'. apply Hna. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. exact H'.
  - intros a _ Ha. eapply apresent_grows; [exact HG1 | exact Ha].
  - exact HFRM1.
  - exact HSHD1.
  - lia. }
pose proof HSP1 as ((H232 & H344) & H224 & H248).
rewrite (st_ok_restrict_mkst SEGS (w_H W) (d_env cx E vals) _ ms1 HS1 Hrv).
apply SRr_ret.
unfold mdb_c1, a3f_st. split; [exact Hfrom|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md3) mat1 md3), k, acc.
split.
{ unfold cfg_at, w64. cbn [ss_pc YP0l.setpc].
  replace (BASE + (SIGMA DS___interceptor_trampoline_snprintf - BASE)) with (SIGMA DS___interceptor_trampoline_snprintf)
    by lia.
  reflexivity. }
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rL. split; [unfold spZ in Rsp |- *; rewrite Q2; exact Rsp|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
  split; [exact Q9|]. split; [exact Q18|]. split; [rewrite Q20; exact Rs4|].
  rewrite Q25; exact Rs9. }
split.
{ split; [rewrite Q26; exact R26|].
  split; [exact Q1|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|].
  split; [exact Q13|]. split; [exact Q19|]. exact Q21. }
split.
{ split.
  { split; [split|].
    - apply KVA; [lia | lia | exact H232].
    - apply KVA; [lia | lia | exact H344].
    - split; [apply KVA; [lia | lia | exact H224] | apply KVA; [lia | lia | exact H248]]. }
  split.
  { split; [exact (proj1 HTAB)|].
    apply KGF; [unfold d_obj, dobj_off; lia | | exact HGT].
    rewrite length_map, HLT1. unfold d_obj, dobj_off. lia. }
  split.
  { split; [exact Hr2|]. apply KGB; [|exact HGB]. rewrite Lb. lia. }
  split; [exact HJR|]. split; [exact HVP|].
  split.
  { apply KGF; [unfold d_obj, dobj_off; lia | | exact HOO].
    rewrite length_map. unfold d_obj, dobj_off. lia. }
  split.
  { split; [exact Hp|]. split; [apply KVA; [lia | lia | exact H368] | apply KVA; [lia | lia | exact H336]]. }
  split; [apply KVA; [lia | lia | exact H392]|].
  split; [apply KVA; [lia | lia | exact H408]|].
  apply KGF; [unfold d_obj, dobj_off; lia | | exact HUSED].
  rewrite LU. unfold d_obj, dobj_off. lia. }
split.
{ split; [apply KVA; [lia | lia | exact S232] | apply KVA; [lia | lia | exact S344]]. }
exact HBODY1.
Qed.

Theorem a3f_mdbA : forall p, 0 <= p < 8 -> mdbA_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof. intros p Hp. exact (mdba_main p Hp (mdba_run p Hp)). Qed.

End h.
End f.
End d.
