(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module names changed; 510 of its 549 lines of code are new or changed and 6 lines of the source are left out. *)
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
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoArm3FieldCut DiscoArm3FieldPFKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoArm3FieldCall.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfa_o (j : Z) : Z := 2160 + 48 * (j - 1).

Definition pfa_srg (o21 o22 o27 : Z) : list sv :=
  [SLit 0; SOff 531 0; SOff AT_A 0; SOff 533 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0;
   SOff 538 0; SOff AT_A 0; SOff 540 0; SOff AT_SH 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0;
   SOff 546 0; SOff 547 0; SOff 32 0; SOff 549 0; SOff 550 0; SOff AT_SH o21;
   SOff AT_F o22; SOff 553 0; SOff 554 0; SOff 555 0; SOff 556 0; SOff AT_F o27;
   SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0].
Definition pfa_sr (j : Z) : list sv := pfa_srg (270 + 6 * (j - 1)) (pfa_o j) (pfa_o j + 2).

Definition pfa_fin_sr (j : Z) : list sv :=
  [SLit 0; SOff A_TEXT 7772; SOff AT_A (-16); SOff 533 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0;
   SOff 538 0; SOff AT_A 0; SOff AT_F 1728; SLit 18; SOff (A_OBJ 10) 0; SOff 562 0; SOff 563 0; SOff 564 0;
   SOff 565 0; SOff 566 0; SOff 32 0; SOff AT_F 1728; SOff 550 0; SOff AT_SH (270 + 6 * (j - 1));
   SOff AT_F (pfa_o j); SOff 553 0; SOff 554 0; SOff 555 0; SOff 556 0; SOff AT_F (pfa_o j + 2);
   SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0].

Definition pfa_fcs (j : Z) : list YP09.chunk :=
  map (fun k : nat => YP09.mkChunk (pfa_o j + Z.of_nat k) (CVal 1 (SOff (562 + k) 0))) (seq 0 6).
Definition pfa_fa : list (nat * afact) := map (fun k : nat => ((562 + k)%nat, mkAF 0 255 0)) (seq 0 6).
Definition pfa_x : YP09.region := YP09.mkRegion (Some AT_A) (-16) 0 (-16) (-8) [].
Definition pfa_xc : YP09.chunk := YP09.mkChunk (-16) (CVal 8 (SOff 567 0)).
Definition pfa_rs (j : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ []);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ pfa_fcs j);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 216 219 (dsh_chunks dsh_ser2);
   got_regionP; bcell_regionP 32; pfa_x].
Definition pfa_ss0 (j : Z) : sstate := mkSS PF_OFF (pfa_sr j) (pfa_rs j) None (d_facts pfa_fa []).

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
    unfold got_regionP, bcell_regionP, pfa_x in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.

Lemma pfa_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.

Lemma pfa_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, pfa_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Lemma pfa_app_nsh : forall F lo n x, in_app lo n -> 0 <= F -> F + 4096 <= CEIL_MAX ->
  lo <= x < lo + n -> ~ (shadow_addr F <= x < shadow_addr F + 512).
Proof.
  intros F lo n x Ha HF0 HF1 Hx Hs. unfold in_app, kLowShadowBeg, kHighMemBeg in Ha.
  unfold shadow_addr, SHADOW_OFF in Hs. destruct Ha as (Ha1 & [Ha2 | (Ha2 & _)]); lia.
Qed.

Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfa_fsh_nrd : forall (B : asyms) (cx : dcx) h a,
  in_app (d_FB cx) 4096 -> 0 <= d_FB cx -> d_FB cx + 4096 <= CEIL_MAX -> in_app h 480 ->
  (0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))) ->
  (forall x, in_roP SEGS pa_relro_lo pa_relro_hi x -> 0 <= x < kLowMemEnd) ->
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ d_rdset B cx h a.
Proof.
  intros B cx h a HF HF0 HF1 Hh Hp Hro Ha Hr.
  unfold d_rdset, d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. unfold HUNT_SIZE in Hr.
  destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
  - exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (pfa_app_nsh (d_FB cx) h 480 a Hh HF0 HF1 ltac:(lia) Ha).
  - pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    exact (pfa_app_nsh (d_FB cx) (c_p cx) (req_size (c_n cx)) a (Hp Hc) HF0 HF1 ltac:(lia) Ha).
  - assert (Hra : 0 <= a < kLowMemEnd) by (first [exact (Hro a Hr) | exact (Hro a (proj1 Hr))]).
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  - unfold AE2k.FF_canary, shadow_addr, SHADOW_OFF in *. lia.
Qed.

Lemma pfa_regs_ok : forall (cx : dcx) (E : env) (R : bvmap 5 word) (ex : list word) o21 o22 o27, d_E cx E ->
  spZ R = d_A cx -> getr R 9 = w64 (d_A cx) -> getr R 11 = w64 (shadow_addr (d_FB cx)) ->
  getr R 18 = w64 SHADOW_OFF ->
  getr R 21 = w64 (shadow_addr (d_FB cx) + o21) ->
  getr R 22 = w64 (d_FB cx + o22) -> getr R 27 = w64 (d_FB cx + o27) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx -> d_FB cx + 4096 <= CEIL_MAX ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs) ++ ex)) (pfa_srg o21 o22 o27) R.
Proof.
  intros cx E R ex o21 o22 o27 HE Rsp R9 R11 R18 R21 R22 R27 HA HF0 HF1.
  destruct HE as (_ & E32 & _ & E60 & EF & ESH).
  assert (S60 : sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ ex)) (SOff 60 0) = w64 (d_A cx)).
  { cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite E60.
    unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  assert (S529 : forall c, sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ ex)) (SOff 529 c) =
    w64 (shadow_addr (d_FB cx) + c)).
  { intros c. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). change 529%nat with AT_SH. rewrite ESH.
    unfold w64. rewrite unsigned_lit_small; [reflexivity|]. unfold shadow_addr, SHADOW_OFF. lia. }
  assert (S516 : forall c, sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ ex)) (SOff 516 c) =
    w64 (d_FB cx + c)).
  { intros c. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite EF.
    unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (S32 : sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ ex)) (SOff 32 0) = w64 SHADOW_OFF).
  { cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). rewrite E32.
    unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r. reflexivity. }
  assert (R2 : getr R 2 = w64 (d_A cx)) by (rewrite <- Rsp; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  regs_ok_cases_pre ltac:(first
    [ rewrite getr_zero; reflexivity
    | rewrite S60; first [exact R2 | exact R9]
    | rewrite S32; exact R18
    | rewrite S529; first [ exact R21 | rewrite R11; unfold w64; f_equal; lia ]
    | rewrite S516; first [ exact R22 | exact R27 ] ]).
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

Definition pfa_run_stmt (j : Z) : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E (pfa_ss0 j) (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (pfa_rs j) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall (ss : sstate) (ms' : machine_state) (mat' : list word),
     ss_regs ss = pfa_fin_sr j -> ss_resv ss = None ->
     d_land_chk dsh_mac (ss_mem ss) = true ->
     existsb (region_cover AT_A (-16) 0 [pfa_xc]) (ss_mem ss) = true ->
     YP0l.st_ok (fx := fq) SEGS E (YP0l.setpc ss (SIGMA DS___interceptor_trampoline_snprintf)) (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (pfa_rs j) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.

Lemma pfa_main : forall j, 1 <= j <= 8 -> pfa_run_stmt j -> pfA_stmt B MT XM_LIB RLO RHI tfib_K j.
Proof.
intros j Hj8 RUNJ cx h i n now op W0 c0 T0 T1 buf count os vpad p W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R26 & R11 & R21 & R22 & R23 & R24 & R27) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & (HSL & Hjp & H392 & H408 & HUSED)).
destruct HSL as (Hp & H368 & H336).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (a3f_count T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296).
{ rewrite (pfa_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (LU : length (a3f_used p) = 32%nat) by (unfold a3f_used; reflexivity).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & _).
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
{ intros Hc. pose proof HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (HMB : forall kk, 0 <= kk < 6 ->
  val_mem SEGS (rd W mem3) (d_obj cx OT + (48 * (j - 1) + kk)) 1 (pf_mb T1 j kk) /\ 0 <= pf_mb T1 j kk < 256).
{ intros kk Hkk. unfold pf_mb. apply (garr8_nthZ SEGS _ _ _ _ HGT); [lia|]. rewrite length_map, HLT1. lia. }
remember (map (getr regs) (tl all_regs) ++ map (fun kk : nat => Z_to_bv 64 (pf_mb T1 j (Z.of_nat kk))) (seq 0 6))
  as vals eqn:Hvals.
assert (EB : forall kk, (kk < 6)%nat -> ew (d_env cx E vals) (562 + kk) = Z_to_bv 64 (pf_mb T1 j (Z.of_nat kk))).
{ intros kk Hkk. replace (562 + kk)%nat with (AT_X + (31 + kk))%nat by (unfold AT_X; lia).
  rewrite d_env_x by (rewrite Hvals, length_app, !length_map, length_seq; cbn; lia).
  rewrite Hvals, app_nth2 by (rewrite length_map; cbn; lia).
  rewrite length_map. change (length (tl all_regs)) with 31%nat.
  replace (31 + kk - 31)%nat with kk by lia.
  set (f := fun kk0 : nat => Z_to_bv 64 (pf_mb T1 j (Z.of_nat kk0))).
  rewrite (nth_indep (map f (seq 0 6)) (Z_to_bv 64 0) (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity. }
assert (EX : forall jj, (jj < 31)%nat -> ew (d_env cx E vals) (AT_X + jj) = getr regs (nth jj (tl all_regs) 0%bv)).
{ intros jj Hjj. rewrite d_env_x by (rewrite Hvals, length_app, !length_map, length_seq; cbn; lia).
  rewrite Hvals, app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr regs 0%bv)) by (rewrite length_map; cbn; lia). apply map_nth. }
destruct (HMB 0 ltac:(lia)) as (_ & HR0). destruct (HMB 1 ltac:(lia)) as (_ & HR1).
destruct (HMB 2 ltac:(lia)) as (_ & HR2). destruct (HMB 3 ltac:(lia)) as (_ & HR3).
destruct (HMB 4 ltac:(lia)) as (_ & HR4). destruct (HMB 5 ltac:(lia)) as (_ & HR5).
assert (B0 : ew (d_env cx E vals) 562 = Z_to_bv 64 (pf_mb T1 j 0)) by exact (EB 0%nat ltac:(lia)).
assert (B1 : ew (d_env cx E vals) 563 = Z_to_bv 64 (pf_mb T1 j 1)) by exact (EB 1%nat ltac:(lia)).
assert (B2 : ew (d_env cx E vals) 564 = Z_to_bv 64 (pf_mb T1 j 2)) by exact (EB 2%nat ltac:(lia)).
assert (B3 : ew (d_env cx E vals) 565 = Z_to_bv 64 (pf_mb T1 j 3)) by exact (EB 3%nat ltac:(lia)).
assert (B4 : ew (d_env cx E vals) 566 = Z_to_bv 64 (pf_mb T1 j 4)) by exact (EB 4%nat ltac:(lia)).
assert (B5 : ew (d_env cx E vals) 567 = Z_to_bv 64 (pf_mb T1 j 5)) by exact (EB 5%nat ltac:(lia)).
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
assert (Hregs : regs_ok (d_env cx E vals) (pfa_sr j) regs).
{ unfold pfa_sr. rewrite Hvals.
  apply (pfa_regs_ok cx E regs _ _ _ _ HE Rsp Rs1 R11 Rs2).
  - rewrite R21; unfold w64; f_equal; lia.
  - rewrite R22; unfold w64, pfa_o, d_obj, dobj_off; f_equal; lia.
  - rewrite R27; unfold w64, pfa_o, d_obj, dobj_off; f_equal; lia.
  - lia.
  - lia.
  - lia. }
assert (HAF : forall kk, (kk < 6)%nat -> afact_ok (d_env cx E vals) (562 + kk) (mkAF 0 255 0)).
{ intros kk Hkk. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EB by exact Hkk.
  destruct (HMB (Z.of_nat kk) ltac:(lia)) as (_ & Hr). rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (HGf : facts_ok (d_env cx E vals) (d_facts pfa_fa [])).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals pfa_fa [] HCTX HE); [|exact I].
  unfold pfa_fa. cbn [map seq atoms_ok].
  repeat (apply conj; [apply HAF; lia|]). exact I. }
assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) (pfa_fcs j)).
{ unfold pfa_fcs. apply Forall_map. apply Forall_forall. intros kk Hkk. apply in_seq in Hkk.
  destruct (HMB (Z.of_nat kk) ltac:(lia)) as (Hv & Hr).
  apply (chunk_ok_val SEGS _ _ (d_FB cx) (pfa_o j + Z.of_nat kk) 1%N (SOff (562 + kk) 0) (pf_mb T1 j (Z.of_nat kk))).
  - cbn [sv_denot]. rewrite EB by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
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
  pose proof (pa_obj_img 1 ltac:(vm_compute; lia)) as HO1. pose proof (pa_obj_img 66 ltac:(vm_compute; lia)) as HO66.
  unfold IMG_LO, IMG_TOP in HO1, HO66.
  unfold d_kregions, pfa_x, fshadow_region, got_regionP, bcell_regionP. cbn [all_disjoint].
  unfold extent_disjoint. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U2, U60, U516, U529, (HEI' (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)),
    (HEI' (A_OBJ 66) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
  unfold shadow_addr, SHADOW_OFF.
  repeat split; lia. }
pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PF_OFF (pfa_sr j) vals [] (pfa_fcs j) [pfa_x]
  (d_facts pfa_fa []) HCTX HE HREG HFLAG Hregs HGf (Forall_nil _) Hfcs Hext (conj I I) Hdx (pfa_kwf j Hj8)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (pfa_rs j) HS0 (pfa_submem j) (pfa_wf j Hj8)) as HS.
clear HS0.
assert (Hawr : awr_ok (d_env cx E vals) (pfa_rs j) LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx))
  (ablocks B ly3 S3) ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ unfold pfa_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ AT_SH (shadow_addr (d_FB cx))); [reflexivity | exact U529 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ AT_A (d_A cx - d_S cx));
    [reflexivity | rewrite U60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_nil. }
unfold cfg_at, w64.
apply (RUNJ fq W (d_env cx E vals) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PF_OFF)) mem3 (YK11.seg_rom SEGS)) md3
  LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 k _
  HEI' HS HJ Hawr).
intros ss ms1 mat1 Hsr Hrv Hchk Hxr HS1 HJ1 HFr1 HG1.
cbn [ms_mem YK11.mkst] in HFr1, HG1.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 16 <= a < d_A cx - 8) ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  rd W (ms_mem ms1) (Z_to_bv 64 a) = rd W mem3 (Z_to_bv 64 a)).
{ intros a Ha H1 H2. apply HFr1. rewrite unsigned_lit_small by lia. intros Hw. apply pfa_inw in Hw.
  change (base_val (d_env cx E vals) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals) AT_A)) in Hw.
  change (base_val (d_env cx E vals) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E vals) AT_SH)) in Hw.
  rewrite U60, U529 in Hw. lia. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 16 <= a < d_A cx - 8) ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  mbyte SEGS (rd W (ms_mem ms1)) a = mbyte SEGS (rd W mem3) a).
{ intros a Ha H1 H2. unfold mbyte. rewrite (KM a Ha H1 H2). reflexivity. }
assert (KVA : forall off v, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + off) 8 v).
{ intros off v H0 H1 Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KB; [lia | lia |].
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (KGF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms1)) a l).
{ intros a l H0 H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia | lia |]. exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 x GFapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (KGB : forall l, Z.of_nat (length l) <= req_size (Z.max (slot_ser_defs.ser_cap op) 1) ->
  garr8 SEGS (rd W mem3) buf l -> garr8 SEGS (rd W (ms_mem ms1)) buf l).
{ intros l H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia | lia |]. exact (pfa_app_nsh (d_FB cx) buf _ x Hbapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (QR : forall r, getr (ms_regs ms1) r = sv_denot (d_env cx E vals) (sr_get (pfa_fin_sr j) r)).
{ intros r. rewrite (st_ok_restrict_reg SEGS (w_H W) (d_env cx E vals) _ ms1 r HS1). cbn [ss_regs YP0l.setpc].
  rewrite Hsr. reflexivity. }
assert (Q1 : getr (ms_regs ms1) 1 = w64 (BASE + PFR1_OFF)).
{ transitivity (sv_denot (d_env cx E vals) (SOff A_TEXT 7772)); [exact (QR (1%bv : bv 5))|].
  rewrite (codeptr_val _ 7772 HEI'). reflexivity. }
assert (Q2s : spZ (ms_regs ms1) = d_A cx + -16).
{ unfold spZ. transitivity (bv_unsigned (sv_denot (d_env cx E vals) (SOff AT_A (-16))));
    [rewrite (QR (2%bv : bv 5)); reflexivity|].
  cbn [sv_denot]. rewrite U60. apply unsigned_lit_small. lia. }
assert (Q3 : getr (ms_regs ms1) 3 = getr regs 3).
{ transitivity (sv_denot (d_env cx E vals) (SOff 533 0)); [exact (QR (3%bv : bv 5))|].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 2%nat ltac:(lia)). }
assert (Q4 : getr (ms_regs ms1) 4 = getr regs 4).
{ transitivity (sv_denot (d_env cx E vals) (SOff 534 0)); [exact (QR (4%bv : bv 5))|].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 3%nat ltac:(lia)). }
assert (Q8 : getr (ms_regs ms1) 8 = getr regs 8).
{ transitivity (sv_denot (d_env cx E vals) (SOff 538 0)); [exact (QR (8%bv : bv 5))|].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 7%nat ltac:(lia)). }
assert (Q20 : getr (ms_regs ms1) 20 = getr regs 20).
{ transitivity (sv_denot (d_env cx E vals) (SOff 550 0)); [exact (QR (20%bv : bv 5))|].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 19%nat ltac:(lia)). }
assert (Q23 : getr (ms_regs ms1) 23 = getr regs 23).
{ transitivity (sv_denot (d_env cx E vals) (SOff 553 0)); [exact (QR (23%bv : bv 5))|].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 22%nat ltac:(lia)). }
assert (Q24 : getr (ms_regs ms1) 24 = getr regs 24).
{ transitivity (sv_denot (d_env cx E vals) (SOff 554 0)); [exact (QR (24%bv : bv 5))|].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 23%nat ltac:(lia)). }
assert (Q25 : getr (ms_regs ms1) 25 = getr regs 25).
{ transitivity (sv_denot (d_env cx E vals) (SOff 555 0)); [exact (QR (25%bv : bv 5))|].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 24%nat ltac:(lia)). }
assert (Q26 : getr (ms_regs ms1) 26 = getr regs 26).
{ transitivity (sv_denot (d_env cx E vals) (SOff 556 0)); [exact (QR (26%bv : bv 5))|].
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 25%nat ltac:(lia)). }
assert (Q9 : getr (ms_regs ms1) 9 = w64 (d_A cx)).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_A 0)); [exact (QR (9%bv : bv 5))|].
  cbn [sv_denot]. rewrite U60. unfold w64; f_equal; lia. }
assert (Q10 : getr (ms_regs ms1) 10 = w64 (d_obj cx OMAC)).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_F 1728)); [exact (QR (10%bv : bv 5))|].
  cbn [sv_denot]. rewrite U516. unfold w64, d_obj, dobj_off; f_equal; lia. }
assert (Q11 : getr (ms_regs ms1) 11 = w64 18).
{ transitivity (sv_denot (d_env cx E vals) (SLit 18)); [exact (QR (11%bv : bv 5))|]. reflexivity. }
assert (Q12 : getr (ms_regs ms1) 12 = w64 (VAL (A_OBJ 10))).
{ transitivity (sv_denot (d_env cx E vals) (SOff (A_OBJ 10) 0)); [exact (QR (12%bv : bv 5))|].
  cbn [sv_denot]. rewrite (HEI' (A_OBJ 10) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r. reflexivity. }
assert (Q13 : getr (ms_regs ms1) 13 = w64 (pf_mb T1 j 0)).
{ transitivity (sv_denot (d_env cx E vals) (SOff 562 0)); [exact (QR (13%bv : bv 5))|].
  cbn [sv_denot]. rewrite B0, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q14 : getr (ms_regs ms1) 14 = w64 (pf_mb T1 j 1)).
{ transitivity (sv_denot (d_env cx E vals) (SOff 563 0)); [exact (QR (14%bv : bv 5))|].
  cbn [sv_denot]. rewrite B1, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q15 : getr (ms_regs ms1) 15 = w64 (pf_mb T1 j 2)).
{ transitivity (sv_denot (d_env cx E vals) (SOff 564 0)); [exact (QR (15%bv : bv 5))|].
  cbn [sv_denot]. rewrite B2, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q16 : getr (ms_regs ms1) 16 = w64 (pf_mb T1 j 3)).
{ transitivity (sv_denot (d_env cx E vals) (SOff 565 0)); [exact (QR (16%bv : bv 5))|].
  cbn [sv_denot]. rewrite B3, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q17 : getr (ms_regs ms1) 17 = w64 (pf_mb T1 j 4)).
{ transitivity (sv_denot (d_env cx E vals) (SOff 566 0)); [exact (QR (17%bv : bv 5))|].
  cbn [sv_denot]. rewrite B4, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q18 : getr (ms_regs ms1) 18 = w64 SHADOW_OFF).
{ transitivity (sv_denot (d_env cx E vals) (SOff 32 0)); [exact (QR (18%bv : bv 5))|].
  cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity. }
assert (Q19 : getr (ms_regs ms1) 19 = w64 (d_obj cx OMAC)).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_F 1728)); [exact (QR (19%bv : bv 5))|].
  cbn [sv_denot]. rewrite U516. unfold w64, d_obj, dobj_off; f_equal; lia. }
assert (Q21 : getr (ms_regs ms1) 21 = w64 (shadow_addr (d_FB cx) + 270 + 6 * (j - 1))).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_SH (270 + 6 * (j - 1)))); [exact (QR (21%bv : bv 5))|].
  cbn [sv_denot]. rewrite U529. unfold w64; f_equal; lia. }
assert (Q22 : getr (ms_regs ms1) 22 = w64 (d_obj cx OT + 48 * (j - 1))).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_F (pfa_o j))); [exact (QR (22%bv : bv 5))|].
  cbn [sv_denot]. rewrite U516. unfold w64, pfa_o, d_obj, dobj_off; f_equal; lia. }
assert (Q27 : getr (ms_regs ms1) 27 = w64 (d_obj cx OT + 48 * (j - 1) + 2)).
{ transitivity (sv_denot (d_env cx E vals) (SOff AT_F (pfa_o j + 2))); [exact (QR (27%bv : bv 5))|].
  cbn [sv_denot]. rewrite U516. unfold w64, pfa_o, d_obj, dobj_off; f_equal; lia. }
pose proof (st_ok_mem_ok SEGS _ _ _ HS1) as (_ & HMOK & _).
cbn [ss_mem YP0l.setpc restrict ms_mem] in HMOK.
apply existsb_exists in Hxr. destruct Hxr as (rx & Hrx & Hcov).
pose proof (proj1 (Forall_forall _ _) HMOK rx Hrx) as Hrxok.
pose proof (region_cover_ok SEGS (d_env cx E vals) _ AT_A (-16) 0 0 0 [pfa_xc] rx Hcov Hrxok
  ltac:(intros o Ho; lia)) as RX.
pose proof (field_of_region (d_env cx E vals) _ AT_A (d_A cx) [pfa_xc] (-16) 0 0 0 (-16) 8%N (SOff 567 0) (pf_mb T1 j 5)
  RX U60 (in_eq _ _) ltac:(cbn [sv_denot]; rewrite B5, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as V16.
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
destruct (DLAND LAWS FFL fq cx h dsh_mac ly3 S3 W (with_vm_backing (m_vm_lazy md3) mat1 md3) k (d_env cx E vals) _ ms1
  HCTX1 HE' (d_env_fl cx E vals) HS1p Hchk H216' H152') as (HFRM1 & HSHD1).
assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_mac ly3 S3 W (ms_mem ms1)).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_ser2 dsh_mac ly3 S3 W mem3 (ms_mem ms1) (d_A cx - 16) (d_A cx - 8)
    (fun a => (d_A cx - 16 <= a < d_A cx - 8) \/ d_fsh cx a) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a [Ha | Ha]; [left; exact Ha | right].
    unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
    exact (pfa_fsh_nrd B cx h a GFapp ltac:(lia) ltac:(lia) HhA HpA Hro Ha).
  - intros a Ha Hna. apply (aview_eq_of SEGS). apply KM; [exact Ha | |].
    + intros H'. apply Hna. left. exact H'.
    + intros H'. apply Hna. right. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. exact H'.
  - intros a _ Ha. eapply apresent_grows; [exact HG1 | exact Ha].
  - exact HFRM1.
  - exact HSHD1.
  - lia. }
pose proof HSP1 as ((H232 & H344) & H224 & H248).
rewrite (st_ok_restrict_mkst SEGS (w_H W) (d_env cx E vals) _ ms1 HS1 Hrv).
apply SRr_ret.
unfold pf_c1, a3f_stg. split; [exact Hfrom|].
unfold d_at.
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
{ unfold d_rLs. split; [exact Q2s|]. split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|].
  split; [rewrite Q8; exact Rs0|]. split; [exact Q9|]. split; [exact Q18|].
  split; [rewrite Q20; exact Rs4|]. rewrite Q25. exact Rs9. }
split; [rewrite Q26; exact R26|].
split.
{ split; [exact Q1|]. split.
  { unfold pf_Rj. split; [exact Q21|]. split; [exact Q22|]. split; [rewrite Q23; exact R23|].
    split; [rewrite Q24; exact R24|]. exact Q27. }
  split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|].
  split; [exact Q14|]. split; [exact Q15|]. split; [exact Q16|]. split; [exact Q17|]. exact Q19. }
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
  { unfold pf_Y, a3f_slots. split.
    { split; [exact Hp|]. split; [apply KVA; [lia | lia | exact H368] | apply KVA; [lia | lia | exact H336]]. }
    split; [exact Hjp|]. split; [apply KVA; [lia | lia | exact H392]|].
    split; [apply KVA; [lia | lia | exact H408]|].
    apply KGF; [unfold d_obj, dobj_off; lia | | exact HUSED].
    rewrite LU. unfold d_obj, dobj_off. lia. }
  replace (d_A cx - 16) with (d_A cx + -16) by lia. exact V16. }
split.
{ pose proof HSP0 as (S232 & S344).
  split; [apply KVA; [lia | lia | exact S232] | apply KVA; [lia | lia | exact S344]]. }
exact HBODY1.
Qed.

End h.
End f.
End d.
