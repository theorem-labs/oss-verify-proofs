(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module paths and module names changed; 353 of its 387 lines of code are new or changed and 11 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition PH_CNT : nat := 563%nat.
Definition ph_acs (p : Z) : list YP09.chunk := [YP09.mkChunk 368 (CVal 8 (SLit p))].
Definition ph_fcs : list YP09.chunk := [YP09.mkChunk 2544 (CVal 4 (SOff PH_CNT 0))].
Definition ph_fa : list (nat * afact) := [(PH_CNT, mkAF 1 8 0)].
Definition ph_G : facts := d_facts ph_fa [].
Definition ph_rs (p : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 408 416 (dslot_chunks ++ ph_acs p);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ ph_fcs);
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_ser2);
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
Proof. intros [b lo hi wlo whi cs]. apply ph_subregion. lia. Qed.
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
  base_val E (Some AT_A) + 408 <= a < base_val E (Some AT_A) + 416.
Proof.
  intros E p a (r & Hin & Hr). unfold ph_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP, fshadow_region in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma ph_awr : forall E p STK sp0 FP bl0 blc ly own a,
  bv_unsigned (ew E AT_A) = a -> sp0 - STK <= a + 408 -> a + 416 <= sp0 ->
  awr_ok E (ph_rs p) STK sp0 FP bl0 blc ly own.
Proof.
  intros E p STK sp0 FP bl0 blc ly own a Ha H1 H2. unfold ph_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ AT_A (a - sp0)); [reflexivity | lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [unfold fshadow_region; cbn; lia|].
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply awr_ok_nil.
Qed.
Lemma ph_soff : forall E n z b, bv_unsigned (ew E n) = b -> sv_denot E (SOff n z) = Z_to_bv 64 (b + z).
Proof. intros E n z b Hb. cbn [sv_denot]. rewrite Hb. reflexivity. Qed.

Lemma ph_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.
Lemma ph_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, ph_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Ltac ph_bvne := let Hq := fresh "Hq" in intro Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ph_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
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

Section h.
Variable B : asyms.

Lemma ph_regs_ok : forall cx E regs ex, d_E cx E -> d_rL B cx regs ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) (a3f_sr 0) regs.
Proof.
  intros cx E regs ex HE HL.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & _ & HSH). unfold AT_A in HA60. unfold AT_SH in HSH.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned;
      first [ rewrite <- Hsp; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact H9 ]
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8; unfold w64, d_S, spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
    | exact H18
    | exact H20
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (ph_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

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
destruct P as (Hi & Hn & Hnow & HRL & (R24 & _) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & (HSL & HUSED)).
destruct HSL as (Hp & H368 & H360).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFSpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
set (vals := a3f_vals regs ++ [Z_to_bv 64 count]).
assert (Lv : length vals = 33%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (ECNT : ew (d_env cx E vals) PH_CNT = Z_to_bv 64 count)
  by (unfold PH_CNT; exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia))).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
  by (intros nn Hnn; apply d_env_old; exact Hnn).
assert (U60 : bv_unsigned (ew (d_env cx E vals) AT_A) = d_A cx)
  by (rewrite EO by (unfold AT_FL, AT_A; lia); rewrite E60; apply unsigned_lit_small; lia).
assert (U516 : bv_unsigned (ew (d_env cx E vals) AT_F) = d_FB cx)
  by (rewrite EO by (unfold AT_FL, AT_F; lia); rewrite EF; apply unsigned_lit_small; lia).
assert (UCNT : bv_unsigned (ew (d_env cx E vals) PH_CNT) = count)
  by (rewrite ECNT; apply unsigned_lit_small; lia).
assert (HVC : val_mem SEGS (rd W mem3) (d_obj cx OT + 384) 4 count).
{ rewrite Ec. rewrite <- (ReacDiscoTableAge.ta_n_val T1 HLT1 (proj1 HTOK1)).
  apply (ReacDiscoTableAge.ta_vm_of_ga (rd W mem3) (d_obj cx OT) T1 384 4 HGT ltac:(lia)).
  rewrite HLT1. cbn [Z.of_nat]. lia. }
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) (ph_acs p)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 368 8%N (SLit p) p); [reflexivity | cbn; lia | cbn; lia | exact H368]. }
assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) ph_fcs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) 2544 4%N (SOff PH_CNT 0) count).
  - cbn [sv_denot]. rewrite UCNT, Z.add_0_r. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj, dobj_off; lia). exact HVC. }
assert (HGf : facts_ok (d_env cx E vals) ph_G).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals ph_fa [] HCTX HE); [|exact I].
  cbn [ph_fa atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite UCNT, Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PH_OFF (a3f_sr 0) vals (ph_acs p) ph_fcs []
  ph_G HCTX HE HREG HFLAG (ph_regs_ok cx E regs [Z_to_bv 64 count] HE HRL) HGf Hacs Hfcs
  (Forall_nil _) I (Forall_nil _) (ph_kwf p)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (ph_rs p) HS0 (ph_submem p) (ph_wf p)) as HS.
clear HS0. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PI := PI) B LAWS) as RUNTOP.
unfold cfg_at, w64.
assert (POST : forall (ms : machine_state) (mat : list word),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) (mkSS PF_OFF (ss_regs (ss_d PH_OFF (a3f_sr 0) dsh_ser2 (ph_acs p) ph_fcs [] ph_G)) (ph_rs p) None ph_G) (restrict (w_H W) ms) ->
  True -> True -> True -> True).
{ intros. exact I. }
clear POST.
assert (Hp8 : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
destruct Hp8 as [Ep|[Ep|[Ep|[Ep|[Ep|[Ep|[Ep|Ep]]]]]]]; rewrite Ep in HS.
all: paj_run_to_shc RUNTOP HS HJ PF_OFF.
all: try (apply (ph_awr _ _ _ _ _ _ _ _ _ (d_A cx)); [exact U60 | unfold LLVMF_STK; lia | lia]).
all: set (R := ms_regs ms) in *.
all: set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
all: assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 408 <= a < d_A cx + 416) ->
       aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
     by (intros a Ha Hna; apply (aview_eq_of SEGS); apply HFr;
         rewrite unsigned_lit_small by lia; intros Hw; apply ph_inw in Hw;
         change (base_val (d_env cx E vals) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals) AT_A)) in Hw;
         rewrite U60 in Hw; lia).
all: assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 408 <= a < d_A cx + 416) ->
       mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a)
     by (intros a Ha Hna; apply (mbyte_of_aview SEGS); apply KM; assumption).
all: assert (KV : forall a (nn : nat) v, 0 <= a -> a + Z.of_nat nn <= d_A cx + 408 ->
       val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v)
     by (intros a nn v H0 H1 Hv; apply (val_mem_frame SEGS (rd W mem3)); [intros x Hx; apply KB; lia | exact Hv]).
all: assert (KG : forall a l, 0 <= a -> a + Z.of_nat (length l) <= d_A cx + 408 ->
       garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l)
     by (intros a l H0 H1 Hg; apply (garr8_frame SEGS (rd W mem3)); [exact Hg | intros x Hx; apply KB; lia]).
all: assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k)
     by exact (conj HBASE (conj HJ HFR)).
all: assert (HHS1 : d_hslots cx h W (ms_mem ms))
     by (apply (d_hslots_kept cx h W W mem3 (ms_mem ms));
         [intros a Ha; apply KM; lia | exact (d_hslots_of_frame cx h dsh_ser2 W mem3 HFRM)]).
all: pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W md' k
       (d_env cx E vals) _ ms HCTX1 (d_E_env cx E vals HE) (d_env_fl cx E vals) HS
       ltac:(vm_compute; reflexivity) HHS1) as (HFRM1 & HSHD1).
all: assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem ms))
     by (apply (DBRT cx h n n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W mem3 (ms_mem ms)
         (d_A cx + 408) (d_A cx + 416) (fun a => d_A cx + 408 <= a < d_A cx + 416) HBODY);
       [ unfold LLVMF_STK; lia | lia | intros a Ha; left; exact Ha
       | intros a Ha Hna; apply KM; [exact Ha | exact Hna]
       | intros a _ Hpr; eapply apresent_grows; [exact HG | exact Hpr]
       | exact HFRM1 | exact HSHD1 | lia ]).
all: assert (V408 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 408) 8 (d_obj cx OO + 144 * p))
     by (pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RA;
         cbn [ms_mem restrict] in RA;
         exact (field_of_region (d_env cx E vals) _ AT_A (d_A cx) _ 0 472 408 416 408 8%N _
           (d_obj cx OO + 144 * p) RA U60 ltac:(cbn [In]; left; reflexivity)
           ltac:(rewrite (ph_soff _ _ _ _ U516); f_equal; unfold d_obj, dobj_off; subst p; lia)
           ltac:(unfold d_obj, dobj_off; subst p; lia) ltac:(cbn; lia))).
all: prreg HS (2%bv : bv 5) Q2.
all: prreg HS (3%bv : bv 5) Q3.
all: prreg HS (4%bv : bv 5) Q4.
all: prreg HS (8%bv : bv 5) Q8.
all: prreg HS (9%bv : bv 5) Q9.
all: prreg HS (18%bv : bv 5) Q18.
all: prreg HS (19%bv : bv 5) Q19.
all: prreg HS (20%bv : bv 5) Q20.
all: prreg HS (22%bv : bv 5) Q22.
all: prreg HS (23%bv : bv 5) Q23.
all: prreg HS (24%bv : bv 5) Q24.
all: prreg HS (25%bv : bv 5) Q25.
all: prreg HS (26%bv : bv 5) Q26.
all: prreg HS (27%bv : bv 5) Q27.
all: assert (U2w : ew (d_env cx E vals) 2 = w64 (d_S cx))
     by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
         unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
all: assert (U60w : ew (d_env cx E vals) AT_A = w64 (d_A cx))
     by (rewrite EO by (unfold AT_FL, AT_A; lia); exact E60).
all: assert (U32w : ew (d_env cx E vals) 32 = w64 SHADOW_OFF)
     by (rewrite EO by (unfold AT_FL; lia); exact E32).
all: assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3))
     by (apply (Permutation_in _ (Permutation_sym (proj1 HBLK))); unfold a3_xb; cbn [app]; left; reflexivity).
all: pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & _).
all: pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
all: pose proof HBUF as (Hr2 & HGB).
all: assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
     by (unfold a3_r; rewrite length_app; cbn [length]; lia).
all: assert (LU : length (a3f_used p) = 32%nat) by (unfold a3f_used; reflexivity).
all: assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296)
     by (rewrite (ph_objs_len buf vpad os HVP Lo6), Los; lia).
all: assert (X3 : ew (d_env cx E vals) 534 = getr regs 3)
     by exact (ph_env_reg cx E regs [Z_to_bv 64 count] (3%bv : bv 5) 534%nat eq_refl).
all: assert (X4 : ew (d_env cx E vals) 535 = getr regs 4)
     by exact (ph_env_reg cx E regs [Z_to_bv 64 count] (4%bv : bv 5) 535%nat eq_refl).
all: assert (X24 : ew (d_env cx E vals) 555 = getr regs 24)
     by exact (ph_env_reg cx E regs [Z_to_bv 64 count] (24%bv : bv 5) 555%nat eq_refl).
all: assert (X27 : ew (d_env cx E vals) 558 = getr regs 27)
     by exact (ph_env_reg cx E regs [Z_to_bv 64 count] (27%bv : bv 5) 558%nat eq_refl).
all: assert (U516n : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx)
     by (change 516%nat with AT_F; exact U516).
all: pose proof HSP1 as ((H208 & H320) & H192 & H200).
all: rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl).
all: cbn [ss_pc].
all: apply SRr_ret.
all: unfold f_pf, a3f_st.
all: split; [exact Hfrom|].
all: unfold d_arm_at_pf, d_at.
all: exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
all: split; [reflexivity|].
all: split; [exact HFRM0|].
all: split; [exact HBASE|].
all: split; [exact HJ|].
all: split; [exact HFR|].
all: split; [exact Hk|].
all: split; [exact Hnev|].
all: split; [exact HMO|].
all: split; [exact Hacc|].
all: split; [exact Hi|].
all: split; [exact Hn|].
all: split; [exact Hnow|].
all: split;
  [ split; [unfold spZ; rewrite Q2; change (ew (d_env cx E vals) 60) with (ew (d_env cx E vals) AT_A);
            rewrite U60w; unfold w64; apply unsigned_lit_small; lia|];
    split; [rewrite Q3, X3; exact Rgp|];
    split; [rewrite Q4, X4; exact Rtp|];
    split; [rewrite Q8, U2w; reflexivity|];
    split; [rewrite Q9; change (ew (d_env cx E vals) 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; reflexivity|];
    split; [rewrite Q19, U32w; reflexivity|];
    split; [rewrite Q18; unfold w64, WS_MASK; reflexivity|];
    split; [rewrite Q20; reflexivity|];
    rewrite Q27, X27; exact Rs27 |].
all: split;
  [ cbv beta;
    split; [rewrite Q24, X24; exact R24|];
    split; [rewrite Q22; unfold w64; f_equal; lia|];
    split; [rewrite Q23; unfold w64; f_equal; lia|];
    split; [rewrite Q25; unfold w64; f_equal; lia|];
    rewrite Q26, U516n; unfold w64, d_obj, dobj_off; f_equal; lia |].
all: split;
  [ cbv beta;
    split;
      [ split; [split; [apply KV; [lia | cbn [Z.of_nat]; lia | exact H208]
                       | apply KV; [lia | cbn [Z.of_nat]; lia | exact H320]]|];
        split; [apply KV; [lia | cbn [Z.of_nat]; lia | exact H192]
               | apply KV; [lia | cbn [Z.of_nat]; lia | exact H200]] |];
    split;
      [ split; [exact (proj1 HTAB)|];
        apply KG; [unfold d_obj, dobj_off; lia
                  | rewrite length_map, HLT1; cbn [Z.of_nat]; unfold d_obj, dobj_off; lia
                  | exact HGT] |];
    split;
      [ split; [exact Hr2|];
        apply KG; [lia | rewrite Lb; lia | exact HGB] |];
    split; [exact HJR|];
    split; [exact HVP|];
    split;
      [ apply KG; [unfold d_obj, dobj_off; lia
                  | rewrite length_map; unfold d_obj, dobj_off; lia
                  | exact HOO] |];
    split;
      [ split; [exact Hp|];
        split; [apply KV; [lia | cbn [Z.of_nat]; lia | exact H368]
               | apply KV; [lia | cbn [Z.of_nat]; lia | exact H360]] |];
    split; [lia|];
    split; [exact V408|];
    apply KG; [unfold d_obj, dobj_off; lia | rewrite LU; cbn [Z.of_nat]; unfold d_obj, dobj_off; lia | exact HUSED] |].
all: split;
  [ split; [apply KV; [lia | cbn [Z.of_nat]; lia | exact H208]
           | apply KV; [lia | cbn [Z.of_nat]; lia | exact H320]] |].
all: exact HBODY1.
Qed.
End h.
End f.
End d.
