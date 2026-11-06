(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module names changed; 424 of its 463 lines of code are new or changed and 6 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoArm3FieldCut DiscoArm3FieldMDBKit.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition mdbd_sr : list sv := SLit 0 :: atom_regs 531 8 ++ SOff 60 0 :: SLit 1 :: atom_regs 541 21.
Definition mdbd_fin_sr (p : Z) : list sv :=
  SLit 0 :: atom_regs 531 8 ++ SOff 60 0 :: SOff 529 0 :: SLit 18446744073709551608 :: SLit (p + 1) ::
  atom_regs 543 8 ++ SOff 562 0 :: SOff 516 2160 :: atom_regs 553 9.
Definition mdbd_acs (p : Z) : list YP09.chunk :=
  [YP09.mkChunk 368 (CVal 8 (SLit p)); YP09.mkChunk 336 (CVal 8 (SOff 562 0))].
Definition mdbd_rs (p : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 368 376 (dslot_chunks ++ mdbd_acs p);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ []);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 224 261 (dsh_chunks dsh_age);
   got_regionP; bcell_regionP 32].
Definition mdbd_ss0 (p : Z) : sstate := mkSS MDJ_OFF mdbd_sr (mdbd_rs p) None (d_facts [] []).
Definition mdbd_c368 (p : Z) : list YP09.chunk := [YP09.mkChunk 368 (CVal 8 (SLit (p + 1)))].

Lemma mdbd_subw : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.

Lemma mdbd_submem : forall p, submem (mdbd_rs p) (d_kregions dsh_age (mdbd_acs p) [] ++ []).
Proof.
  intros p. unfold mdbd_rs, d_kregions, fshadow_region. rewrite app_nil_r.
  apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply mdbd_subw; lia|].
  apply submem_keep; [apply mdbd_subw; lia|].
  apply submem_keep; [apply mdbd_subw; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply subregion_refl|].
  apply submem_nil.
Qed.

Lemma mdbd_wf : forall p, regions_wf (mdbd_rs p) = true.
Proof. intros p. vm_compute. reflexivity. Qed.

Lemma mdbd_kwf : forall p, regions_wf (d_kregions dsh_age (mdbd_acs p) [] ++ []) = true.
Proof. intros p. vm_compute. reflexivity. Qed.

Lemma mdbd_inw : forall E p a, in_wrange E (mdbd_rs p) a ->
  base_val E (Some AT_A) + 368 <= a < base_val E (Some AT_A) + 376 \/
  base_val E (Some AT_SH) + 224 <= a < base_val E (Some AT_SH) + 261.
Proof.
  intros E p a (r & Hin & Hr). unfold mdbd_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.

Lemma mdbd_awr_skel : forall E rs rs' STK sp0 FP bl0 blc ly own,
  awr_ok E rs' STK sp0 FP bl0 blc ly own -> skeleton rs = skeleton rs' -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs rs' STK sp0 FP bl0 blc ly own H Hsk a Ha. apply H. eapply in_wrange_skeleton; [exact Hsk | exact Ha].
Qed.

Lemma mdbd_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.

Lemma mdbd_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, mdbd_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Lemma mdbd_app_nsh : forall F lo n x, in_app lo n -> 0 <= F -> F + 4096 <= CEIL_MAX ->
  lo <= x < lo + n -> ~ (shadow_addr F <= x < shadow_addr F + 512).
Proof.
  intros F lo n x Ha HF0 HF1 Hx Hs. unfold in_app, kLowShadowBeg, kHighMemBeg in Ha.
  unfold shadow_addr, SHADOW_OFF in Hs. destruct Ha as (Ha1 & [Ha2 | (Ha2 & _)]); lia.
Qed.


Lemma mdbd_x : forall cx E (R : bvmap 5 word) c (j : nat), (j < 31)%nat ->
  ew (d_env cx E (map (getr R) (tl all_regs) ++ [c])) (AT_X + j) = getr R (nth j (tl all_regs) 0%bv).
Proof.
  intros cx E R c j Hj. rewrite d_env_x by (rewrite length_app, length_map; cbn; lia).
  rewrite app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr R 0%bv)) by (rewrite length_map; cbn; lia).
  apply map_nth.
Qed.

Lemma mdbd_atom : forall cx E (R : bvmap 5 word) c (j : nat), (j < 31)%nat ->
  sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c])) (SOff (AT_X + j) 0) = getr R (nth j (tl all_regs) 0%bv).
Proof.
  intros cx E R c j Hj. cbn [sv_denot]. rewrite mdbd_x by exact Hj. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma mdbd_regs_ok : forall cx E (R : bvmap 5 word) c,
  getr R 9 = w64 (d_A cx) -> getr R 10 = w64 1 ->
  ew E AT_A = w64 (d_A cx) -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs) ++ [c])) mdbd_sr R.
Proof.
  intros cx E R c R9 R10 E60 HA.
  assert (S60 : sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c])) (SOff 60 0) = w64 (d_A cx)).
  { cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite E60.
    unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                               | rewrite S60; exact R9
                               | rewrite R10; reflexivity ]).
Qed.

Lemma mdbd_fsh_nrd : forall (B : asyms) (cx : dcx) h a,
  in_app (d_FB cx) 4096 -> 0 <= d_FB cx -> d_FB cx + 4096 <= CEIL_MAX -> in_app h 480 ->
  (0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))) ->
  (forall x, in_roP SEGS pa_relro_lo pa_relro_hi x -> 0 <= x < kLowMemEnd) ->
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ d_rdset B cx h a.
Proof.
  intros B cx h a HF HF0 HF1 Hh Hp Hro Ha Hr.
  unfold d_rdset, d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. unfold HUNT_SIZE in Hr.
  destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
  - exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 a HF HF0 HF1 ltac:(lia) Ha).
  - exact (mdbd_app_nsh (d_FB cx) h 480 a Hh HF0 HF1 ltac:(lia) Ha).
  - pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    exact (mdbd_app_nsh (d_FB cx) (c_p cx) (req_size (c_n cx)) a (Hp Hc) HF0 HF1 ltac:(lia) Ha).
  - assert (Hra : 0 <= a < kLowMemEnd) by (first [exact (Hro a Hr) | exact (Hro a (proj1 Hr))]).
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  - unfold AE2k.FF_canary, shadow_addr, SHADOW_OFF in *. pose proof (Z.div_pos (d_FB cx) 8 HF0 ltac:(lia)). lia.
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

Definition mdbd_run_stmt (p : Z) : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E (mdbd_ss0 p) (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (mdbd_rs p) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall (tk : bool) (ss : sstate) (ms' : machine_state) (mat' : list word),
     branch_taken BC_NE (sv_denot E (SLit (p + 1))) (sv_denot E (SOff 562 0)) = tk ->
     ss_pc ss = (if tk then PH_OFF else R14_OFF) ->
     ss_regs ss = mdbd_fin_sr p -> ss_resv ss = None ->
     d_land_chk dsh_ser2 (ss_mem ss) = true ->
     existsb (region_cover AT_A 368 376 (mdbd_c368 p)) (ss_mem ss) = true ->
     st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (mdbd_rs p) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.

Ltac mdbd_post POST HS HJ HF2 HG2 HFr1 HG1 Hc tk :=
  rewrite wvb_collapse in HJ; rewrite wvb_collapse;
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?s _ =>
    apply (POST tk s _ _ Hc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HS HJ);
    [ refine (frame_of_trans _ _ _ _ _ _ _ HFr1 HF2); vm_compute; reflexivity
    | exact (mem_grows_trans _ _ _ HG1 HG2) ]
  end.

Lemma mdbd_run : forall p, 0 <= p < 8 -> mdbd_run_stmt p.
Proof.
  intros p Hp8 fq W E ms mdc STK sp0 FP ly S W0 mem md own lyc Sc k Q HEI HS HJ Hawr POST.
  pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
  pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
  pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
  assert (Hp : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct Hp as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  ( paj_run_to_shc RUNTOP HS HJ PH_OFF;
    [ exact Hawr
    | rename HF into HF1; rename HFr into HFr1; rename HG into HG1;
      psrr_branch_pi RUNP BR HS;
      [ paj_run_to_shc RUNTOP HS HJ PH_OFF;
        [ apply (mdbd_awr_skel _ _ _ _ _ _ _ _ _ _ Hawr); vm_compute; reflexivity
        | mdbd_post POST HS HJ HFr HG HFr1 HG1 Hc true ]
      | paj_run_to_shc RUNTOP HS HJ R14_OFF;
        [ apply (mdbd_awr_skel _ _ _ _ _ _ _ _ _ _ Hawr); vm_compute; reflexivity
        | mdbd_post POST HS HJ HFr HG HFr1 HG1 Hc false ] ] ]).
Qed.

Lemma mdbd_main : forall p, 0 <= p < 8 -> mdbd_run_stmt p -> mdbD_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp8 RUNJ cx h i n now op W0 c0 T0 T1 buf count os vpad W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R26 & R10) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
destruct HY as (HSL & H392 & H408 & HUSED). destruct HSL as (Hp & H368 & H336).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (a3f_count T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296).
{ rewrite (mdbd_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (LU : length (a3f_used (p + 1)) = 32%nat) by (unfold a3f_used; reflexivity).
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
{ intros Hcn. pose proof HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
remember (map (getr regs) (tl all_regs) ++ [Z_to_bv 64 count]) as vals eqn:Hvals.
assert (E562 : ew (d_env cx E vals) 562 = Z_to_bv 64 count).
{ rewrite Hvals. exact (d_env_x cx E (map (getr regs) (tl all_regs) ++ [Z_to_bv 64 count]) 31
    ltac:(rewrite length_app, length_map; cbn; lia)). }
assert (QX : forall j, (j < 31)%nat ->
  sv_denot (d_env cx E vals) (SOff (AT_X + j) 0) = getr regs (nth j (tl all_regs) 0%bv)).
{ intros j Hj. rewrite Hvals. exact (mdbd_atom cx E regs _ j Hj). }
pose proof HE as (EEo & E32o & HEIo & E60o & EFo & ESHo).
pose proof (d_E_env cx E vals HE) as HE'.
pose proof HE' as (EE' & E32' & HEI' & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E vals) 60) = d_A cx).
{ change 60%nat with AT_A. rewrite E60'. unfold w64. apply unsigned_lit_small. lia. }
assert (U516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx).
{ change 516%nat with AT_F. rewrite EF'. unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : bv_unsigned (ew (d_env cx E vals) 529) = shadow_addr (d_FB cx)).
{ change 529%nat with AT_SH. rewrite ESH'. unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (Hregs : regs_ok (d_env cx E vals) mdbd_sr regs).
{ rewrite Hvals. apply (mdbd_regs_ok cx E regs (Z_to_bv 64 count) Rs1 R10 E60o). lia. }
assert (HGf : facts_ok (d_env cx E vals) (d_facts [] [])).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HCTX HE); exact I. }
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) (mdbd_acs p)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 368 8%N (SLit p) p); [reflexivity | cbn; lia | cbn; lia | exact H368].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 336 8%N (SOff 562 0) count).
    + cbn [sv_denot]. rewrite E562, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + exact H336. }
pose proof (DSEAT LAWS PAL fq cx dsh_age ly3 S3 W regs mem3 md3 k E MDJ_OFF mdbd_sr vals (mdbd_acs p) [] []
  (d_facts [] []) HCTX HE HREG HFLAG Hregs HGf Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _)
  (mdbd_kwf p)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (mdbd_rs p) HS0 (mdbd_submem p) (mdbd_wf p)) as HS.
clear HS0.
assert (Hawr : awr_ok (d_env cx E vals) (mdbd_rs p) LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx))
  (ablocks B ly3 S3) ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ unfold mdbd_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
    [reflexivity | rewrite U60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx))); [reflexivity | exact U529 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply awr_ok_nil. }
unfold cfg_at, w64.
apply (RUNJ fq W (d_env cx E vals) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + MDJ_OFF)) mem3 (YK11.seg_rom SEGS))
  md3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 k _
  HEI' HS HJ Hawr).
intros tk ss ms1 mat1 Htk Hpc Hsr Hrv Hchk Hxr HS1 HJ1 HFr1 HG1.
cbn [ms_mem YK11.mkst] in HFr1, HG1.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 368 <= a < d_A cx + 376) ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  rd W (ms_mem ms1) (Z_to_bv 64 a) = rd W mem3 (Z_to_bv 64 a)).
{ intros a Ha H1 H2. apply HFr1. rewrite unsigned_lit_small by lia. intros Hw. apply mdbd_inw in Hw.
  change (base_val (d_env cx E vals) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals) AT_A)) in Hw.
  change (base_val (d_env cx E vals) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E vals) AT_SH)) in Hw.
  change (ew (d_env cx E vals) AT_A) with (ew (d_env cx E vals) 60) in Hw.
  change (ew (d_env cx E vals) AT_SH) with (ew (d_env cx E vals) 529) in Hw.
  rewrite U60, U529 in Hw. lia. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 368 <= a < d_A cx + 376) ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  mbyte SEGS (rd W (ms_mem ms1)) a = mbyte SEGS (rd W mem3) a).
{ intros a Ha H1 H2. unfold mbyte. rewrite (KM a Ha H1 H2). reflexivity. }
assert (KVA : forall off v, 0 <= off -> off + 8 <= 368 \/ 376 <= off ->
  off + 8 <= 472 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + off) 8 v).
{ intros off v H0 H1 H2 Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KB; [lia | lia |].
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (KGF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms1)) a l).
{ intros a l H0 H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia | lia |]. exact (mdbd_app_nsh (d_FB cx) (d_FB cx) 4096 x GFapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (KGB : forall l, Z.of_nat (length l) <= req_size (Z.max (slot_ser_defs.ser_cap op) 1) ->
  garr8 SEGS (rd W mem3) buf l -> garr8 SEGS (rd W (ms_mem ms1)) buf l).
{ intros l H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia | lia |]. exact (mdbd_app_nsh (d_FB cx) buf _ x Hbapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (QR : forall r, getr (ms_regs ms1) r = sv_denot (d_env cx E vals) (sr_get (mdbd_fin_sr p) r)).
{ intros r. rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS1). rewrite Hsr. reflexivity. }
assert (Q2 : getr (ms_regs ms1) 2 = getr regs 2) by (rewrite QR; exact (QX 1%nat ltac:(lia))).
assert (Q3 : getr (ms_regs ms1) 3 = getr regs 3) by (rewrite QR; exact (QX 2%nat ltac:(lia))).
assert (Q4 : getr (ms_regs ms1) 4 = getr regs 4) by (rewrite QR; exact (QX 3%nat ltac:(lia))).
assert (Q8 : getr (ms_regs ms1) 8 = getr regs 8) by (rewrite QR; exact (QX 7%nat ltac:(lia))).
assert (Q18 : getr (ms_regs ms1) 18 = getr regs 18) by (rewrite QR; exact (QX 17%nat ltac:(lia))).
assert (Q20 : getr (ms_regs ms1) 20 = getr regs 20) by (rewrite QR; exact (QX 19%nat ltac:(lia))).
assert (Q25 : getr (ms_regs ms1) 25 = getr regs 25) by (rewrite QR; exact (QX 24%nat ltac:(lia))).
assert (Q26 : getr (ms_regs ms1) 26 = getr regs 26) by (rewrite QR; exact (QX 25%nat ltac:(lia))).
assert (Q9 : getr (ms_regs ms1) 9 = w64 (d_A cx)).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 9) with (SOff 60 0). cbn [sv_denot]. rewrite U60.
  unfold w64. f_equal; lia. }
assert (Q10 : getr (ms_regs ms1) 10 = w64 (shadow_addr (d_FB cx))).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 10) with (SOff 529 0). cbn [sv_denot]. rewrite U529.
  unfold w64. f_equal; lia. }
assert (Q22 : getr (ms_regs ms1) 22 = w64 (d_obj cx OT)).
{ rewrite QR. change (sr_get (mdbd_fin_sr p) 22) with (SOff 516 2160). cbn [sv_denot]. rewrite U516.
  unfold w64, d_obj, dobj_off. f_equal; lia. }
pose proof (st_ok_mem_ok SEGS _ _ _ HS1) as (_ & HMOK & _).
cbn [ss_mem abs_ss setpc restrict ms_mem] in HMOK.
apply existsb_exists in Hxr. destruct Hxr as (rx & Hrx & Hcov).
pose proof (proj1 (Forall_forall _ _) HMOK rx Hrx) as Hrxok.
pose proof (region_cover_ok SEGS (d_env cx E vals) _ AT_A 368 376 0 0 (mdbd_c368 p) rx Hcov Hrxok
  ltac:(intros o Ho; lia)) as RX.
pose proof (field_of_region (d_env cx E vals) _ 60 (d_A cx) (mdbd_c368 p) 368 376 0 0 368 8%N (SLit (p + 1)) (p + 1)
  RX U60 (in_eq _ _) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V368.
pose proof (KVA 216 h ltac:(lia) ltac:(lia) ltac:(lia) H216) as H216'.
pose proof (KVA 152 (h + 440) ltac:(lia) ltac:(lia) ltac:(lia) H152) as H152'.
assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat1 md3) k)
  by exact (conj HBASE (conj HJ1 HFR)).
destruct (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W (with_vm_backing (m_vm_lazy md3) mat1 md3) k (d_env cx E vals) _ ms1
  HCTX1 HE' (d_env_fl cx E vals) HS1 Hchk H216' H152') as (HFRM1 & HSHD1).
assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem ms1)).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_age dsh_ser2 ly3 S3 W mem3 (ms_mem ms1)
    (d_A cx + 368) (d_A cx + 376) (fun a => (d_A cx + 368 <= a < d_A cx + 376) \/ d_fsh cx a) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a [Ha | Ha]; [left; exact Ha | right].
    unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
    exact (mdbd_fsh_nrd B cx h a GFapp ltac:(lia) ltac:(lia) HhA HpA Hro Ha).
  - intros a Ha Hna. apply (aview_eq_of SEGS). apply KM; [exact Ha | |].
    + intros H'. apply Hna. left. exact H'.
    + intros H'. apply Hna. right. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. exact H'.
  - intros a _ Ha. eapply apresent_grows; [exact HG1 | exact Ha].
  - exact HFRM1.
  - exact HSHD1.
  - lia. }
pose proof HSP1 as ((H232 & H344) & H224 & H248).
pose proof HSP0 as (S232 & S344).
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS1 Hrv). rewrite Hpc.
apply SRr_ret.
destruct tk.
- assert (Hne : p + 1 <> count).
  { rewrite branch_ne_U in Htk. apply negb_true_iff in Htk. apply Z.eqb_neq in Htk.
    rewrite (U_lit _ (p + 1) ltac:(lia)) in Htk. rewrite U_SOff, E562 in Htk.
    rewrite unsigned_lit_small in Htk by lia. rewrite Z.add_0_r in Htk.
    first [ rewrite zcanon_id in Htk by (rewrite M64_val; lia)
          | rewrite YP0m.zcanon_small in Htk by lia ]. exact Htk. }
  left. split; [lia|].
  unfold f_ph, a3f_st. split; [exact Hfrom|]. unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md3) mat1 md3), k, acc.
  split; [reflexivity|].
  split; [assumption|]. split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { unfold d_rL. split; [unfold spZ in Rsp |- *; rewrite Q2; exact Rsp|].
    split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
    split; [exact Q9|]. split; [rewrite Q18; exact Rs2|]. split; [rewrite Q20; exact Rs4|].
    rewrite Q25; exact Rs9. }
  split; [split; [rewrite Q26; exact R26 | exact Q22]|].
  split.
  { split.
    { split; [split|].
      - apply KVA; [lia | lia | lia | exact H232].
      - apply KVA; [lia | lia | lia | exact H344].
      - split; [apply KVA; [lia | lia | lia | exact H224] | apply KVA; [lia | lia | lia | exact H248]]. }
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
    { split; [lia|]. split; [exact V368|]. apply KVA; [lia | lia | lia | exact H336]. }
    apply KGF; [unfold d_obj, dobj_off; lia | | exact HUSED].
    rewrite LU. unfold d_obj, dobj_off. lia. }
  split.
  { split; [apply KVA; [lia | lia | lia | exact S232] | apply KVA; [lia | lia | lia | exact S344]]. }
  exact HBODY1.
- right. unfold r14_in. split; [exact Hfrom|]. unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md3) mat1 md3), k, acc.
  split; [reflexivity|].
  split; [assumption|]. split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { unfold d_rL. split; [unfold spZ in Rsp |- *; rewrite Q2; exact Rsp|].
    split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
    split; [exact Q9|]. split; [rewrite Q18; exact Rs2|]. split; [rewrite Q20; exact Rs4|].
    rewrite Q25; exact Rs9. }
  split; [split; [exact Q10 | rewrite Q26; exact R26]|].
  split.
  { split.
    { split; [split|].
      - apply KVA; [lia | lia | lia | exact H232].
      - apply KVA; [lia | lia | lia | exact H344].
      - split; [apply KVA; [lia | lia | lia | exact H224] | apply KVA; [lia | lia | lia | exact H248]]. }
    split; [exact (proj1 HTAB)|].
    apply KGF; [unfold d_obj, dobj_off; lia | | exact HGT].
    rewrite length_map, HLT1. unfold d_obj, dobj_off. lia. }
  split.
  { split; [apply KVA; [lia | lia | lia | exact S232] | apply KVA; [lia | lia | lia | exact S344]]. }
  exact HBODY1.
Qed.

Theorem a3f_mdbD : forall p, 0 <= p < 8 -> mdbD_stmt B MT XM_LIB RLO RHI tfib_K p.
Proof. intros p Hp. exact (mdbd_main p Hp (mdbd_run p Hp)). Qed.

End h.
End f.
End d.
