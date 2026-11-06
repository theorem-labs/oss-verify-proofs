(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module paths and module names changed; 241 of its 274 lines of code are new or changed and 12 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFKit DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfa_o (j : Z) : Z := 2160 + 48 * (j - 1).

Definition pfa_srx (j : Z) (r : nat) : sv :=
  match r with
  | 25%nat => SLit j
  | 26%nat => SOff AT_F (pfa_o j + 2)
  | 27%nat => SOff AT_SH 0
  | _ => a3f_srx 0 r
  end.
Definition pfa_sr (j : Z) : list sv := map (pfa_srx j) (seq 0 32).

Definition pfa_fcs (j : Z) : list YP09.chunk :=
  map (fun k : nat => YP09.mkChunk (pfa_o j + Z.of_nat k) (CVal 1 (SOff (563 + k) 0))) (seq 0 6).
Definition pfa_fa : list (nat * afact) := map (fun k : nat => ((563 + k)%nat, mkAF 0 255 0)) (seq 0 6).
Definition pfa_G : facts := d_facts pfa_fa [].
Definition pfa_x : YP09.region := YP09.mkRegion (Some AT_A) (-16) 0 (-16) (-8) [].
Definition pfa_xc : YP09.chunk := YP09.mkChunk (-16) (CVal 8 (SOff 568 0)).
Definition pfa_rs (j : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ []);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ pfa_fcs j);
   fshadow_region AT_SH DFRAME_CLASS 216 219 (dsh_chunks dsh_ser2);
   got_regionP; bcell_regionP 32; pfa_x].
Definition pfa_ss0 (j : Z) : sstate := mkSS PF_OFF (pfa_sr j) (pfa_rs j) None pfa_G.

Lemma pfa_subw : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.

Lemma pfa_submem : forall j, submem (pfa_rs j) (d_kregions dsh_ser2 [] (pfa_fcs j) ++ [pfa_x]).
Proof.
  intros j. unfold pfa_rs, d_kregions, fshadow_region. cbn [app].
  apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply pfa_subw; lia|].
  apply submem_keep; [apply pfa_subw; lia|].
  apply submem_keep; [apply pfa_subw; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply subregion_refl|].
  apply submem_nil.
Qed.

Lemma pfa_wf : forall j, 1 <= j <= 8 -> regions_wf (pfa_rs j) = true.
Proof.
  intros j Hj. assert (E : j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->] ] ] ] ] ] ]; vm_compute; reflexivity.
Qed.

Lemma pfa_kwf : forall j, 1 <= j <= 8 -> regions_wf (d_kregions dsh_ser2 [] (pfa_fcs j) ++ [pfa_x]) = true.
Proof.
  intros j Hj. assert (E : j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->] ] ] ] ] ] ]; vm_compute; reflexivity.
Qed.

Lemma pfa_inw : forall E j a, in_wrange E (pfa_rs j) a ->
  base_val E (Some AT_A) - 16 <= a < base_val E (Some AT_A) - 8 \/
  base_val E (Some AT_SH) + 216 <= a < base_val E (Some AT_SH) + 219.
Proof.
  intros E j a (r & Hin & Hr). unfold pfa_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [] ] ] ] ] ] ] ];
    unfold got_regionP, bcell_regionP, pfa_x, fshadow_region in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Lemma pfa_app_nsh : forall F lo n x, in_app lo n -> 0 <= F -> F + 4096 <= CEIL_MAX ->
  lo <= x < lo + n -> ~ (shadow_addr F <= x < shadow_addr F + 512).
Proof.
  intros F lo n x Ha HF0 HF1 Hx Hs. unfold in_app, kLowShadowBeg, kHighMemBeg in Ha.
  unfold shadow_addr, SHADOW_OFF in Hs. destruct Ha as (Ha1 & [Ha2 | (Ha2 & _)]); lia.
Qed.

Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition pfa_vals (regs : bvmap 5 word) (T1 : list byte) (j : Z) : list word :=
  a3f_vals regs ++ map (fun k : nat => Z_to_bv 64 (pf_mb T1 j (Z.of_nat k))) (seq 0 6).

Lemma pfa_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  ew (d_env cx E (a3f_vals regs ++ ex)) a = getr regs r.
Proof.
  intros cx E regs ex r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (unfold a3f_vals; rewrite length_app, length_map, length_seq; lia).
  unfold a3f_vals. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite (nth_indep _ _ ((fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) 0%nat))
    by (rewrite length_map, length_seq; lia).
  pose proof (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat
    (Z.to_nat (bv_unsigned r))) as Hm.
  cbv beta in Hm |- *. rewrite Hm, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma pfa_byte : forall cx E regs T1 j (q : nat), (q < 6)%nat ->
  ew (d_env cx E (pfa_vals regs T1 j)) (563 + q) = Z_to_bv 64 (pf_mb T1 j (Z.of_nat q)).
Proof.
  intros cx E regs T1 j q Hq. unfold pfa_vals. replace (563 + q)%nat with (AT_X + (32 + q))%nat by (unfold AT_X; lia).
  rewrite d_env_x by (unfold a3f_vals; rewrite length_app, !length_map, !length_seq; lia).
  rewrite app_nth2 by (unfold a3f_vals; rewrite length_map, length_seq; lia).
  unfold a3f_vals. rewrite length_map, length_seq. replace (32 + q - 32)%nat with q by lia.
  set (f := fun k : nat => Z_to_bv 64 (pf_mb T1 j (Z.of_nat k))).
  rewrite (nth_indep (map f (seq 0 6)) (Z_to_bv 64 0) (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Section h.
Variable B : asyms.

Lemma pfa_regs_ok : forall cx E regs ex j, d_E cx E -> d_rL B cx regs ->
  getr regs 25 = w64 j -> getr regs 26 = w64 (d_obj cx OT + 48 * (j - 1) + 2) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 47 ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) (pfa_sr j) regs.
Proof.
  intros cx E regs ex j HE HL R25 R26 HA HF.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & HF516 & HSH).
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  assert (U60 : bv_unsigned (ew (d_env cx E (a3f_vals regs ++ ex)) AT_A) = d_A cx)
    by (rewrite HA60; unfold w64; apply unsigned_lit_small; lia).
  assert (U516 : bv_unsigned (ew (d_env cx E (a3f_vals regs ++ ex)) AT_F) = d_FB cx)
    by (rewrite HF516; unfold w64; apply unsigned_lit_small; lia).
  assert (U529 : bv_unsigned (ew (d_env cx E (a3f_vals regs ++ ex)) AT_SH) = shadow_addr (d_FB cx))
    by (rewrite HSH; unfold w64; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get (pfa_sr ?jj) ?r) =>
         let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
         change (sr_get (pfa_sr jj) r) with (pfa_srx jj n); cbn [pfa_srx a3f_srx] end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | exact R25
    | rewrite U516, R26; unfold w64, pfa_o, d_obj, dobj_off; f_equal; lia
    | rewrite U529, Z.add_0_r; exact H27
    | rewrite U60, Z.add_0_r;
      first [ rewrite <- Hsp; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact H9 ]
    | change AT_STK with 2%nat; rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8;
      unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
    | exact H18
    | exact H20
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (pfa_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Lemma pfa_fsh_nrd : forall (cx : dcx) h a,
  in_app (d_FB cx) 4096 -> 0 <= d_FB cx -> d_FB cx + 4096 <= CEIL_MAX -> in_app h 480 ->
  (0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))) ->
  (forall x, in_roP SEGS pa_relro_lo pa_relro_hi x -> 0 <= x < kLowMemEnd) ->
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ d_rdset B cx h a.
Proof.
  intros cx h a HF HF0 HF1 Hh Hp Hro Ha Hr.
  unfold d_rdset, d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. unfold HUNT_SIZE in Hr.
  destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
  - exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (pfa_app_nsh (d_FB cx) h 480 a Hh HF0 HF1 ltac:(lia) Ha).
  - pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    exact (pfa_app_nsh (d_FB cx) (c_p cx) (req_size (c_n cx)) a (Hp Hc) HF0 HF1 ltac:(lia) Ha).
  - pose proof (Hro a (proj1 Hr)) as Hra. unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  - unfold FF_canary, shadow_addr, SHADOW_OFF in *. lia.
Qed.

Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.

Lemma pfa_seat : forall (fq : YK11.FPState) cx ly3 S3 (W : world SEGS) regs mem3 md3 k E T1 j,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_E cx E ->
  Forall (region_ok SEGS E (rd W mem3)) (d_regions cx dsh_ser2) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  d_rL B cx regs -> getr regs 25 = w64 j -> getr regs 26 = w64 (d_obj cx OT + 48 * (j - 1) + 2) ->
  garr8 SEGS (rd W mem3) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1) -> length T1 = 400%nat ->
  1 <= j <= 8 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (pfa_vals regs T1 j)) (pfa_ss0 j)
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PF_OFF)) mem3 (YK11.seg_rom SEGS))).
Proof.
  intros fq cx ly3 S3 W regs mem3 md3 k E T1 j HCTX HE HREG HFLAG HRL R25 R26 HGT HLT1 Hj.
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
  pose proof alloc_ceiling_value as (Hceil & _). pose proof (YM05.alloc_ceiling_lt) as Hceil47.
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
  unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
  assert (HMB : forall kk, 0 <= kk < 6 ->
    val_mem SEGS (rd W mem3) (d_obj cx OT + (48 * (j - 1) + kk)) 1 (pf_mb T1 j kk) /\ 0 <= pf_mb T1 j kk < 256).
  { intros kk Hkk. unfold pf_mb. apply (garr8_nthZ SEGS _ _ _ _ HGT); [lia|]. rewrite length_map, HLT1. lia. }
  set (vals := pfa_vals regs T1 j).
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
  assert (Hregs : regs_ok (d_env cx E vals) (pfa_sr j) regs).
  { unfold vals, pfa_vals. apply (pfa_regs_ok cx E regs _ j HE HRL R25 R26); lia. }
  assert (HAF : forall q, (q < 6)%nat -> afact_ok (d_env cx E vals) (563 + q) (mkAF 0 255 0)).
  { intros q Hq. unfold afact_ok. cbn [af_lo af_hi af_al2]. unfold vals. rewrite pfa_byte by exact Hq.
    destruct (HMB (Z.of_nat q) ltac:(lia)) as (_ & Hr). rewrite unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  assert (HGf : facts_ok (d_env cx E vals) pfa_G).
  { apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals pfa_fa [] HCTX HE); [|exact I].
    unfold pfa_fa. cbn [map seq atoms_ok].
    repeat (apply conj; [apply HAF; lia|]). exact I. }
  assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) (pfa_fcs j)).
  { unfold pfa_fcs. apply Forall_map. apply Forall_forall. intros kk Hkk. apply in_seq in Hkk.
    destruct (HMB (Z.of_nat kk) ltac:(lia)) as (Hv & Hr).
    apply (chunk_ok_val SEGS _ _ (d_FB cx) (pfa_o j + Z.of_nat kk) 1%N (SOff (563 + kk) 0) (pf_mb T1 j (Z.of_nat kk))).
    - cbn [sv_denot]. unfold vals. rewrite pfa_byte by lia. rewrite unsigned_lit_small by lia.
      rewrite Z.add_0_r. reflexivity.
    - cbn. lia.
    - cbn. lia.
    - change (N.to_nat 1) with 1%nat.
      replace (d_FB cx + (pfa_o j + Z.of_nat kk)) with (d_obj cx OT + (48 * (j - 1) + Z.of_nat kk))
        by (unfold pfa_o, d_obj, dobj_off; lia).
      exact Hv. }
  assert (Hext : Forall (region_ok SEGS (d_env cx E vals) (rd W mem3)) [pfa_x]).
  { apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, pfa_x. cbv zeta.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U60. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply GSTK. unfold LLVMF_STK. lia. }
  assert (Hdx : Forall (fun r => all_disjoint (d_env cx E vals) r (d_kregions dsh_ser2 [] (pfa_fcs j))) [pfa_x]).
  { apply Forall_cons; [|apply Forall_nil].
    pose proof (pa_obj_img 0 ltac:(vm_compute; lia)) as HO0. pose proof (pa_obj_img 12 ltac:(vm_compute; lia)) as HO12.
    unfold IMG_LO, IMG_TOP in HO0, HO12.
    unfold d_kregions, pfa_x, fshadow_region, got_regionP, bcell_regionP. cbn [all_disjoint].
    unfold extent_disjoint. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U2, U60, U516, U529, (HEI' (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)),
      (HEI' (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
    unfold shadow_addr, SHADOW_OFF.
    repeat split; lia. }
  pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PF_OFF (pfa_sr j) vals [] (pfa_fcs j) [pfa_x]
    pfa_G HCTX HE HREG HFLAG Hregs HGf (Forall_nil _) Hfcs Hext (conj I I) Hdx (pfa_kwf j Hj)) as HS0.
  exact (st_ok_pi_submem _ _ _ (pfa_rs j) HS0 (pfa_submem j) (pfa_wf j Hj)).
Qed.

End h.
End f.
End d.
