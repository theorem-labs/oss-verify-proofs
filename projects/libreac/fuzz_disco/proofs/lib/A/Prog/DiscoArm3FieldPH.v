(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 326 of its 384 lines of code are new or changed and 438 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFKit.v; 305 of its 378 lines of code are new or changed and 311 lines of the source are left out. *)
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
DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt DiscoEntSeat DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacBoxName ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model disco_json_lemmas
slot_ser_defs slot_ser_pure slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoArm3FieldCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition ph_sr : list sv :=
  SLit 0 :: atom_regs 531 8 ++ SOff 60 0 :: atom_regs 540 12 ++ SOff 516 2160 :: atom_regs 553 9.
Definition ph_acs (p : Z) : list YP09.chunk := [YP09.mkChunk 368 (CVal 8 (SLit p))].
Definition ph_fcs : list YP09.chunk := [YP09.mkChunk 2544 (CVal 4 (SOff 562 0))].
Definition ph_G : facts := d_facts [(562%nat, mkAF 1 8 0)] [].
Definition ph_rs (p : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 392 416 (dslot_chunks ++ ph_acs p);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ ph_fcs);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 0 0 (dsh_chunks dsh_ser2);
   got_regionP; bcell_regionP 32].

Lemma ph_subregion : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.
Lemma ph_subrefl : forall r, subregion r r.
Proof.
  intros [b lo hi wlo whi cs]. apply ph_subregion. lia.
Qed.
Lemma ph_submem : forall p, submem (ph_rs p) (d_kregions dsh_ser2 (ph_acs p) ph_fcs ++ []).
Proof.
  intros p. unfold ph_rs, d_kregions, fshadow_region. rewrite app_nil_r.
  apply submem_keep; [apply ph_subrefl|].
  apply submem_keep; [apply ph_subregion; lia|].
  apply submem_keep; [apply ph_subregion; lia|].
  apply submem_keep; [apply ph_subregion; lia|].
  apply submem_keep; [apply ph_subrefl|].
  apply submem_keep; [apply ph_subrefl|].
  apply submem_nil.
Qed.
Lemma ph_wf : forall p, regions_wf (ph_rs p) = true.
Proof. intros p. vm_compute. reflexivity. Qed.
Lemma ph_kwf : forall p, regions_wf (d_kregions dsh_ser2 (ph_acs p) ph_fcs ++ []) = true.
Proof. intros p. vm_compute. reflexivity. Qed.
Lemma ph_inw : forall E p a, in_wrange E (ph_rs p) a ->
  base_val E (Some AT_A) + 392 <= a < base_val E (Some AT_A) + 416.
Proof.
  intros E p a (r & Hin & Hr). unfold ph_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma ph_awr : forall E p STK sp0 FP bl0 blc ly own a,
  bv_unsigned (ew E 60) = a -> sp0 - STK <= a + 392 -> a + 416 <= sp0 ->
  awr_ok E (ph_rs p) STK sp0 FP bl0 blc ly own.
Proof.
  intros E p STK sp0 FP bl0 blc ly own a Ha H1 H2. unfold ph_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (a - sp0)); [reflexivity | lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|]. apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply awr_ok_nil.
Qed.

Definition ph_finA (p : Z) : YP09.region :=
  YP09.mkRegion (Some 60%nat) 0 472 392 416
    (YP09.mkChunk 392 (CVal 8 (SOff 516 (240 + 144 * p))) :: YP09.mkChunk 408 (CVal 8 (SLit (2 ^ 64 - 1))) ::
     dslot_chunks ++ ph_acs p).
Definition ph_fin_sr (p : Z) : list sv :=
  [SLit 0; SOff 531 0; SOff 532 0; SOff 533 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0;
   SOff 60 0; SOff 516 (240 + 144 * p); SOff 529 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0; SOff 546 0;
   SOff 547 0; SOff 548 0; SOff 549 0; SOff 550 0; SOff 529 270; SOff 516 2160; SLit 0; SLit 1; SOff 555 0;
   SOff 556 0; SOff 516 2162; SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0].
Definition ph_fin (p : Z) : sstate :=
  mkSS PF_OFF (ph_fin_sr p)
    [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks; ph_finA p;
     YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ ph_fcs);
     YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 0 0 (dsh_chunks dsh_ser2);
     got_regionP; bcell_regionP 32] None ph_G.
Lemma ph_chk : forall p, d_land_chk dsh_ser2 (ss_mem (ph_fin p)) = true.
Proof. intros p. vm_compute. reflexivity. Qed.
Lemma ph_soff : forall E n z b, bv_unsigned (ew E n) = b -> sv_denot E (SOff n z) = Z_to_bv 64 (b + z).
Proof. intros E n z b Hb. cbn [sv_denot]. rewrite Hb. reflexivity. Qed.

Lemma ph_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.
Lemma ph_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat -> Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length]. rewrite length_app, IHl, ph_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ph_x : forall cx E (R : bvmap 5 word) c (j : nat), (j < 31)%nat ->
  ew (d_env cx E (map (getr R) (tl all_regs) ++ [c])) (AT_X + j) = getr R (nth j (tl all_regs) 0%bv).
Proof.
  intros cx E R c j Hj. rewrite d_env_x by (rewrite length_app, length_map; cbn; lia).
  rewrite app_nth1 by (rewrite length_map; cbn; lia).
  rewrite (nth_indep _ _ (getr R 0%bv)) by (rewrite length_map; cbn; lia).
  apply map_nth.
Qed.
Lemma ph_atom : forall cx E (R : bvmap 5 word) c (j : nat), (j < 31)%nat ->
  sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c])) (SOff (AT_X + j) 0) = getr R (nth j (tl all_regs) 0%bv).
Proof.
  intros cx E R c j Hj. cbn [sv_denot]. rewrite ph_x by exact Hj. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma ph_regs_ok : forall cx E (R : bvmap 5 word) c,
  getr R 9 = w64 (d_A cx) -> getr R 22 = w64 (d_obj cx OT) ->
  ew E AT_A = w64 (d_A cx) -> ew E AT_F = w64 (d_FB cx) -> 0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx ->
  d_FB cx + 4096 <= 2 ^ 64 ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs) ++ [c])) ph_sr R.
Proof.
  intros cx E R c R9 R22 E60 E516 HA HF0 HF1.
  assert (S60 : sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c])) (SOff 60 0) = w64 (d_A cx)).
  { cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite E60.
    unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  assert (S516 : sv_denot (d_env cx E (map (getr R) (tl all_regs) ++ [c])) (SOff 516 2160) = w64 (d_obj cx OT)).
  { cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite E516.
    unfold w64. rewrite unsigned_lit_small by lia. unfold d_obj, dobj_off. reflexivity. }
  regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                               | rewrite S60; exact R9
                               | rewrite S516; exact R22 ]).
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
Hypothesis DBRT : d_body_rt_stmt B.

Theorem a3f_ph : seg_ph_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad p W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R26 & R22) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & (HSL & HUSED)).
destruct HSL as (Hp & H368 & H336).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (a3f_count T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296).
{ rewrite (ph_objs_len buf vpad os HVP Lo6), Los. lia. }
pose proof (ReacDiscoTableAge.age_val (rd W mem3) T1 (d_obj cx OT) 384 4 HGT ltac:(lia) ltac:(rewrite HLT1; lia)) as HTN.
rewrite (ReacDiscoTableAge.u_of_n T1 HLT1 ltac:(lia)), <- Ec in HTN.
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & _).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_lt as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo. clear GS16 GA32 GF32.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LU : length (a3f_used p) = 32%nat) by (unfold a3f_used; reflexivity).
remember (map (getr regs) (tl all_regs) ++ [Z_to_bv 64 count]) as vals eqn:Hvals.
assert (E562 : ew (d_env cx E vals) 562 = Z_to_bv 64 count).
{ rewrite Hvals. exact (d_env_x cx E (map (getr regs) (tl all_regs) ++ [Z_to_bv 64 count]) 31
    ltac:(rewrite length_app, length_map; cbn; lia)). }
assert (Hregs : regs_ok (d_env cx E vals) ph_sr regs).
{ rewrite Hvals. apply (ph_regs_ok cx E regs (Z_to_bv 64 count) Rs1 R22 E60 EF); lia. }
assert (HGf : facts_ok (d_env cx E vals) ph_G).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [(562%nat, mkAF 1 8 0)] [] HCTX HE); [|exact I].
  cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E562, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) (ph_acs p)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 368 8%N (SLit p) p); [reflexivity | cbn; lia | cbn; lia | exact H368]. }
assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) ph_fcs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) 2544 4%N (SOff 562 0) count).
  - cbn [sv_denot]. rewrite E562, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj, dobj_off; lia). exact HTN. }
pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PH_OFF ph_sr vals (ph_acs p) ph_fcs [] ph_G
  HCTX HE HREG HFLAG Hregs HGf Hacs Hfcs (Forall_nil _) I (Forall_nil _) (ph_kwf p)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (ph_rs p) HS0 (ph_submem p) (ph_wf p)) as HS.
clear HS0. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS.
pose proof (d_E_env cx E vals HE) as HE'.
pose proof HE' as (EE' & E32' & HEI' & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E vals) 60) = d_A cx).
{ rewrite (E60' : ew (d_env cx E vals) 60 = w64 (d_A cx)). unfold w64. apply unsigned_lit_small. lia. }
assert (U516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx).
{ rewrite (EF' : ew (d_env cx E vals) 516 = w64 (d_FB cx)). unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : bv_unsigned (ew (d_env cx E vals) 529) = shadow_addr (d_FB cx)).
{ rewrite (ESH' : ew (d_env cx E vals) 529 = w64 (shadow_addr (d_FB cx))). unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] |].
  assert (d_FB cx / 8 <= d_FB cx) by (apply Z.div_le_upper_bound; lia). lia. }
assert (QX : forall j, (j < 31)%nat ->
  sv_denot (d_env cx E vals) (SOff (AT_X + j) 0) = getr regs (nth j (tl all_regs) 0%bv)).
{ intros j Hj. rewrite Hvals. exact (ph_atom cx E regs _ j Hj). }
assert (POST : forall (ms : machine_state) (mat : list word),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) (ph_fin p) (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  frame_of (d_env cx E vals) (ph_rs p) (rd W mem3) (rd W (ms_mem ms)) ->
  mem_grows (rd W mem3) (rd W (ms_mem ms)) ->
  SRr SEGS W (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3))
    (f_pf B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p 1)).
{ intros ms mat HS1 HJ1 HFr1 HG1.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 392 <= a < d_A cx + 416) ->
    rd W (ms_mem ms) (Z_to_bv 64 a) = rd W mem3 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply HFr1. rewrite unsigned_lit_small by lia. intros Hw. apply ph_inw in Hw.
    change (base_val (d_env cx E vals) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals) 60)) in Hw.
    rewrite U60 in Hw. lia. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 392 <= a < d_A cx + 416) ->
    mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a).
  { intros a Ha Hna. unfold mbyte. rewrite (KM a Ha Hna). reflexivity. }
  assert (KV : forall a (nn : nat) v, 0 <= a -> a + Z.of_nat nn <= d_A cx + 392 ->
    val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v).
  { intros a nn v H0 H1 Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
    intros x Hx. apply KB; lia. }
  assert (KG : forall a l, 0 <= a -> a + Z.of_nat (length l) <= d_A cx + 392 ->
    garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l).
  { intros a l H0 H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx. apply KB; lia. }
  assert (Q : forall r : bv 5, getr (ms_regs ms) r = sv_denot (d_env cx E vals) (sr_get (ph_fin_sr p) r))
    by (intros r; exact (st_ok_pi_restrict_reg _ _ _ _ r HS1)).
  assert (Q2 : getr (ms_regs ms) 2 = getr regs 2) by (rewrite Q; exact (QX 1%nat ltac:(lia))).
  assert (Q3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite Q; exact (QX 2%nat ltac:(lia))).
  assert (Q4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite Q; exact (QX 3%nat ltac:(lia))).
  assert (Q8 : getr (ms_regs ms) 8 = getr regs 8) by (rewrite Q; exact (QX 7%nat ltac:(lia))).
  assert (Q18 : getr (ms_regs ms) 18 = getr regs 18) by (rewrite Q; exact (QX 17%nat ltac:(lia))).
  assert (Q20 : getr (ms_regs ms) 20 = getr regs 20) by (rewrite Q; exact (QX 19%nat ltac:(lia))).
  assert (Q25 : getr (ms_regs ms) 25 = getr regs 25) by (rewrite Q; exact (QX 24%nat ltac:(lia))).
  assert (Q26 : getr (ms_regs ms) 26 = getr regs 26) by (rewrite Q; exact (QX 25%nat ltac:(lia))).
  assert (Q9 : getr (ms_regs ms) 9 = w64 (d_A cx)).
  { rewrite Q. change (sr_get (ph_fin_sr p) 9) with (SOff 60 0). rewrite (ph_soff _ _ _ _ U60).
    unfold w64. f_equal. lia. }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (shadow_addr (d_FB cx))).
  { rewrite Q. change (sr_get (ph_fin_sr p) 11) with (SOff 529 0). rewrite (ph_soff _ _ _ _ U529).
    unfold w64. f_equal. lia. }
  assert (Q21 : getr (ms_regs ms) 21 = w64 (shadow_addr (d_FB cx) + 270 + 6 * (1 - 1))).
  { rewrite Q. change (sr_get (ph_fin_sr p) 21) with (SOff 529 270). rewrite (ph_soff _ _ _ _ U529).
    unfold w64. f_equal. lia. }
  assert (Q22 : getr (ms_regs ms) 22 = w64 (d_obj cx OT + 48 * (1 - 1))).
  { rewrite Q. change (sr_get (ph_fin_sr p) 22) with (SOff 516 2160). rewrite (ph_soff _ _ _ _ U516).
    unfold w64. f_equal. unfold d_obj, dobj_off. lia. }
  assert (Q23 : getr (ms_regs ms) 23 = w64 (1 - 1)) by (rewrite Q; reflexivity).
  assert (Q24 : getr (ms_regs ms) 24 = w64 1) by (rewrite Q; reflexivity).
  assert (Q27 : getr (ms_regs ms) 27 = w64 (d_obj cx OT + 48 * (1 - 1) + 2)).
  { rewrite Q. change (sr_get (ph_fin_sr p) 27) with (SOff 516 2162). rewrite (ph_soff _ _ _ _ U516).
    unfold w64. f_equal. unfold d_obj, dobj_off. lia. }
  pose proof (st_ok_pi_region_nth _ (ph_fin p) _ 1%nat (ph_finA p) HS1 eq_refl) as RA.
  change (ms_mem (restrict (w_H W) ms)) with (rd W (ms_mem ms)) in RA. unfold ph_finA in RA.
  pose proof (field_of_region _ _ 60 (d_A cx) _ _ _ _ _ 392 8%N (SOff 516 (240 + 144 * p)) (d_obj cx OO + 144 * p)
    RA U60 (in_eq _ _) ltac:(rewrite (ph_soff _ _ _ _ U516); f_equal; unfold d_obj, dobj_off; lia)
    ltac:(cbn; unfold d_obj, dobj_off; lia) ltac:(cbn; lia)) as V392.
  pose proof (field_of_region _ _ 60 (d_A cx) _ _ _ _ _ 408 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1)
    RA U60 (in_cons _ _ _ (in_eq _ _)) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V408.
  pose proof (KV (d_A cx + 216) 8%nat h ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia) H216) as H216'.
  pose proof (KV (d_A cx + 152) 8%nat (h + 440) ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia) H152) as H152'.
  assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k)
    by exact (conj HBASE (conj HJ1 HFR)).
  pose proof (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W (with_vm_backing (m_vm_lazy md3) mat md3) k
    (d_env cx E vals) (ph_fin p) ms HCTX1 HE' (d_env_fl cx E vals) HS1 (ph_chk p) H216' H152') as (HFRM1 & HSHD1).
  assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem ms)).
  { apply (DBRT cx h n n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W mem3 (ms_mem ms) (d_A cx + 392) (d_A cx + 416)
      (fun a => d_A cx + 392 <= a < d_A cx + 416) HBODY).
    - unfold LLVMF_STK. lia.
    - lia.
    - intros a Ha. left. exact Ha.
    - intros a Ha Hna. apply (aview_eq_of SEGS). apply KM; [exact Ha | exact Hna].
    - intros; eapply apresent_grows; [exact HG1 | eassumption].
    - exact HFRM1.
    - exact HSHD1.
    - lia. }
  pose proof HSP1 as ((H232 & H344) & H224 & H248).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS1 eq_refl).
  apply SRr_ret.
  unfold f_pf, a3f_st. split; [exact Hfrom|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md3) mat md3), k, acc.
  split; [reflexivity|].
  split; [assumption|]. split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { unfold d_rL. split; [unfold spZ in Rsp |- *; rewrite Q2; exact Rsp|].
    split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
    split; [exact Q9|]. split; [rewrite Q18; exact Rs2|]. split; [rewrite Q20; exact Rs4|].
    rewrite Q25; exact Rs9. }
  split.
  { cbv beta. split; [rewrite Q26; exact R26|].
    split; [exact Q11|]. split; [exact Q21|]. split; [exact Q22|]. split; [exact Q23|].
    split; [exact Q24|]. exact Q27. }
  split.
  { cbv beta.
    split; [split; [split|split]|].
    - apply KV; [lia | change (Z.of_nat 8) with 8; lia | exact H232].
    - apply KV; [lia | change (Z.of_nat 8) with 8; lia | exact H344].
    - apply KV; [lia | change (Z.of_nat 8) with 8; lia | exact H224].
    - apply KV; [lia | change (Z.of_nat 8) with 8; lia | exact H248].
    - split; [split; [exact (proj1 HTAB)|]|].
      + apply KG; [unfold d_obj, dobj_off; lia | | exact HGT].
        rewrite length_map, HLT1. change (Z.of_nat 400) with 400. unfold d_obj, dobj_off. lia.
      + split; [split; [exact Hr2|]|].
        * apply KG; [lia | | exact HGB]. rewrite Lb. lia.
        * split; [exact HJR|]. split; [exact HVP|]. split.
          -- apply KG; [unfold d_obj, dobj_off; lia | | exact HOO].
             rewrite length_map. unfold d_obj, dobj_off. lia.
          -- split; [split; [exact Hp|]; split|].
             ++ apply KV; [lia | change (Z.of_nat 8) with 8; lia | exact H368].
             ++ apply KV; [lia | change (Z.of_nat 8) with 8; lia | exact H336].
             ++ split; [lia|]. split; [exact V392|]. split; [exact V408|].
                apply KG; [unfold d_obj, dobj_off; lia | | exact HUSED].
                rewrite LU. change (Z.of_nat 32) with 32. unfold d_obj, dobj_off. lia. }
  split.
  { split.
    - apply KV; [lia | change (Z.of_nat 8) with 8; lia | exact H232].
    - apply KV; [lia | change (Z.of_nat 8) with 8; lia | exact H344]. }
  exact HBODY1. }
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
unfold cfg_at, w64.
assert (Hp8 : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
destruct Hp8 as [Ep|[Ep|[Ep|[Ep|[Ep|[Ep|[Ep|Ep]]]]]]];
  (rewrite Ep in HS;
   paj_run_to_shc RUNTOP HS HJ PF_OFF;
   [ apply (ph_awr _ _ _ _ _ _ _ _ _ (d_A cx)); [exact U60 | unfold LLVMF_STK; lia | lia]
   | apply POST;
     [ lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
         replace (ph_fin p) with s by (rewrite Ep; vm_compute; reflexivity); exact HS end
     | exact HJ
     | rewrite Ep; exact HFr
     | exact HG ] ]).
Qed.
End h.
End f.
End d.
