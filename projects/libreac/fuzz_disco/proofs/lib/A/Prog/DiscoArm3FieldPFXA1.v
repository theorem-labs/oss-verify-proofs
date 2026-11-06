(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module names changed; 600 of its 638 lines of code are new or changed and 7 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC81 YC45 YC88 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoRo DiscoArm3 DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs DiscoArm3FieldCall DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntBody DiscoArm3FieldMDKit DiscoArm3FieldMDFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacHuntRole.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_json_text disco_json_reader_model reac_disco_table_json_c reac_disco_table_age_c
slot_ser_defs slot_ser_tokb disco_jscalar_model jtok_is_c printf_facts_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition px1_acs : list YP09.chunk :=
  [YP09.mkChunk 392 (CVal 8 (SOff AT_F 384)); YP09.mkChunk 408 (CVal 8 (SLit 1))].
Definition px1_fcs (r : Z) : list YP09.chunk :=
  [YP09.mkChunk 1668 (CVal 4 (SLit 0)); YP09.mkChunk 2216 (CVal 4 (SLit r))].
Definition px1_narrow (l : smem) : smem :=
  match l with
  | [r0; r1; r2; r3; r4; r5] =>
      [set_window r0 0 0; set_window r1 0 0; set_window r2 1668 1672; set_window r3 0 0; set_window r4 0 0;
       set_window r5 0 0]
  | _ => l
  end.

Lemma px1_sw_sub : forall r a b, (b <= a \/ (YP09.r_wlo r <= a /\ b <= YP09.r_whi r)) -> subregion (set_window r a b) r.
Proof.
intros r a b H. unfold subregion, set_window.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact H | intros c Hc; exact Hc].
Qed.

Lemma px1_narrow_sub : forall shf acs fcs, submem (px1_narrow (d_kregions shf acs fcs)) (d_kregions shf acs fcs).
Proof.
intros shf acs fcs. unfold d_kregions, px1_narrow.
apply submem_keep; [apply px1_sw_sub; left; lia|].
apply submem_keep; [apply px1_sw_sub; left; lia|].
apply submem_keep; [apply px1_sw_sub; right; cbn [YP09.r_wlo YP09.r_whi]; unfold DFRAME_SIZE; lia|].
apply submem_keep; [apply px1_sw_sub; left; lia|].
apply submem_keep; [apply px1_sw_sub; left; lia|].
apply submem_keep; [apply px1_sw_sub; left; lia|].
apply submem_nil.
Qed.

Ltac px1_preg SR5 HP SR regs4 R r z :=
  transitivity (getr regs4 r); [exact (SR5 r ltac:(cbv; tauto)) |];
  transitivity (getr R r); [exact (HP z ltac:(unfold acallee_saved; lia)) | exact (SR r ltac:(cbv; tauto))].
Ltac px1_kb := intros kk Hkk; cbn in Hkk; split; [|split]; lia.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma px1_kept_of : forall E rs (H : word -> bool) (m m' : word -> option byte) lo hi,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF HW a Ha Hn. unfold aview, mbyte, mrestrict. cbv beta.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros Hw. exact (Hn (HW a Hw)).
Qed.

Lemma px1_g8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l HK G j Hj. destruct (G j Hj) as [V Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS H H' m m' (a + Z.of_nat j) 1 (nth j l 0)); [|exact V].
intros kk Hkk. change (Z.of_nat 1) with 1 in Hkk.
replace (a + Z.of_nat j + kk) with (a + (Z.of_nat j + kk)) by lia. apply HK. lia.
Qed.

Lemma px1_g8_w1 : forall (m : word -> option byte) a, val_mem SEGS m a 4 1 -> garr8 SEGS m a [1; 0; 0; 0].
Proof.
intros m a V j Hj. cbn [length] in Hj. split.
- intros kk Hkk. assert (Ek : kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (V j Hj). destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
- destruct j as [|[|[|[|j]]]]; cbn [nth]; lia.
Qed.

Lemma px1_same_reg : forall (fq : YK11.FPState) E ss ss' ms ms' (H H' : word -> bool) (r : bv 5),
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) -> st_ok (fx := fq) SEGS E ss' (restrict H' ms') ->
  sr_get (ss_regs ss') r = sr_get (ss_regs ss) r -> getr (ms_regs ms') r = getr (ms_regs ms) r.
Proof.
intros fq E ss ss' ms ms' H H' r HS HS' Hr.
rewrite (st_ok_restrict_reg SEGS H' E ss' ms' r HS'), (st_ok_pi_restrict_reg H E ss ms r HS), Hr. reflexivity.
Qed.

Lemma px1_dE_hi : forall cx E k ws, d_E cx E -> (AT_FL <= k)%nat -> d_E cx (havoc E k ws).
Proof.
intros cx E k ws (EE & E32 & HEI & E60 & EF & ESH) Hk. unfold d_E.
rewrite !ew_havoc_old by (unfold AT_FL, AT_A, AT_F, AT_SH in *; lia).
split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
- intros nn r Hn. rewrite ew_havoc_old; [exact (EE nn r Hn)|].
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL in Hk. lia.
- apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL in *; lia].
Qed.

Lemma px1_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma px1_regs2 : forall (cx : dcx) (E : env) (R : bvmap 5 word) (ret : Z),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + ret) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT ret :: atom_regs 532 30) R.
Proof.
intros cx E R ret HEI H1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                              | rewrite H1; symmetry; exact (codeptr_val _ ret HEId) ]).
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
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis MCRO : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Theorem a3f_pfxa_1 : seg_pfa_p_spec B MT XM_LIB RLO RHI tfib_K 1.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs.
unfold f_pfx, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R14) & (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED).
pose proof HSLOTS as (Hpc & H368 & H336).
pose proof HTAB as ((removed & Hage & Hpost) & HOT).
pose proof Hpost as (LT1 & _ & _ & _ & _ & _ & TOK1 & _).
destruct (a3f_count T1 now count os LT1 TOK1 Hnow HJR) as (Ecnt & Hc8 & Los & H6 & Hinb & Hg33 & Hlen).
assert (Hrole : disco_table_c.role_of_e T1 1 = 0 \/ disco_table_c.role_of_e T1 1 = 1 \/
  disco_table_c.role_of_e T1 1 = 2) by (pose proof TOK1 as (_ & T2 & _); apply T2; lia).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HBASE | split; [exact HJ | exact HFRS]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (Tb & Gb & Lkb & HHb & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HdE & HREG & HFLAG & H216 & H152).
pose proof HdE as (HER & HE32 & HEI0 & HEA & HEF & HESH).
assert (HA64 : 0 <= d_A cx < 2 ^ 64) by lia.
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44) by lia.
assert (HFU : bv_unsigned (ew E AT_F) = d_FB cx)
  by (rewrite HEF; unfold w64; apply unsigned_lit_small; lia).
assert (HEI : img_env VAL A_LIM (d_env cx E (a3f_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
assert (V1668 : val_mem SEGS (rd W mem3) (d_FB cx + 1668) 4 0).
{ assert (EU : a3f_used 1 = map (fun b : byte => bv_unsigned b) (map (Z_to_bv 8) (a3f_used 1)))
    by (vm_compute; reflexivity).
  pose proof HUSED as HU0. rewrite EU in HU0.
  pose proof (ReacHuntRole.hunt_val4 SEGS (rd W mem3) (d_obj cx OUSED) _ 4 HU0 ltac:(lia)
    ltac:(rewrite length_map, a3f_used_bytes by lia; lia)) as V.
  replace (disco_table_c.u_at (map (Z_to_bv 8) (a3f_used 1)) 4 4) with 0 in V by (vm_compute; reflexivity).
  unfold d_obj, dobj_off in V. replace (d_FB cx + 1664 + 4) with (d_FB cx + 1668) in V by lia. exact V. }
assert (V2216 : val_mem SEGS (rd W mem3) (d_FB cx + 2216) 4 (disco_table_c.role_of_e T1 1)).
{ rewrite <- (a3f_role_u T1 1) by lia.
  pose proof (ReacHuntRole.hunt_val4 SEGS (rd W mem3) (d_obj cx OT) T1 (48 * 1 + 8) HOT ltac:(lia)
    ltac:(rewrite LT1; lia)) as V.
  unfold d_obj, dobj_off in V. replace (d_FB cx + 2160 + (48 * 1 + 8)) with (d_FB cx + 2216) in V by lia. exact V. }
assert (Hr02 : 0 <= disco_table_c.role_of_e T1 1 <= 2) by lia.
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (a3f_vals regs)) (rd W mem3) (d_A cx)) px1_acs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply chunk_ok_val with (v := d_obj cx OO + 144 * 1).
    + cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
      unfold d_obj, dobj_off. f_equal. lia.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold d_obj, dobj_off. lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H392.
  - eapply chunk_ok_val with (v := 1).
    + reflexivity.
    + lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H408. }
assert (HFCS : Forall (YP09.chunk_ok SEGS (d_env cx E (a3f_vals regs)) (rd W mem3) (d_FB cx))
  (px1_fcs (disco_table_c.role_of_e T1 1))).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply chunk_ok_val with (v := 0); [reflexivity | lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. exact V1668.
  - eapply chunk_ok_val with (v := disco_table_c.role_of_e T1 1);
      [reflexivity | change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. exact V2216. }
assert (H14 : sv_denot (d_env cx E (a3f_vals regs)) (SOff AT_F 2160) = getr regs 14).
{ cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  rewrite R14. unfold d_obj, dobj_off, w64. reflexivity. }
rewrite Ec. unfold cfg_at. change (w64 (BASE + PFX_OFF)) with (Z_to_bv 64 (BASE + PFX_OFF)).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (a3f_vals regs)) (mrestrict (w_H W) mem3)) by apply Forall_nil.
assert (CONT : forall ms mat,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_FB cx + 1668 <= a < d_FB cx + 1672) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  mem_grows (rd W mem3) (rd W (ms_mem ms)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 8104) ->
  getr (ms_regs ms) 10 = Z_to_bv 64 (d_FB cx + 408) ->
  getr (ms_regs ms) 11 = Z_to_bv 64 1 ->
  getr (ms_regs ms) 12 = w64 (VAL (A_OBJ (a3f_roleobj (disco_table_c.role_of_e T1 1)))) ->
  getr (ms_regs ms) 24 = Z_to_bv 64 (d_FB cx + 2208) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r) ->
  d_frame cx h dsh_ser2 W (ms_mem ms) -> d_shadow cx dsh_ser2 W (ms_mem ms) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_FB cx + 1668) 4 1 ->
  SRr SEGS W (mkCfg (YK11.mkst (fx := fq) (ms_regs ms) (Z_to_bv 64 (BASE + AF_jtok_is)) (ms_mem ms)
    (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md3) mat md3))
    (f_r1 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 1)).
{ intros ms mat HJr KC HG Q1 Q10 Q11 Q12x Q24 SR HFRMc HSHDc V1668c.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
set (R := ms_regs ms) in *.
assert (SpR : spZ R = d_A cx) by (unfold spZ; rewrite (SR 2%bv ltac:(cbv; tauto)); exact Rsp).
assert (KV : forall a nn v, (forall kk, 0 <= kk < Z.of_nat nn -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_FB cx + 1668 <= a + kk < d_FB cx + 1672)) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v).
{ intros a nn v Hb V. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms) a nn v); [|exact V].
  intros kk Hkk. destruct (Hb kk Hkk) as [Hb1 Hb2]. exact (KC _ Hb1 Hb2). }
assert (KG : forall a l, (forall kk, 0 <= kk < Z.of_nat (length l) -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_FB cx + 1668 <= a + kk < d_FB cx + 1672)) ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l).
{ intros a l Hb Gx. apply (px1_g8_kept (w_H W) (w_H W) mem3 (ms_mem ms) a l); [|exact Gx].
  intros kk Hkk. destruct (Hb kk Hkk) as [Hb1 Hb2]. exact (KC _ Hb1 Hb2). }
assert (H216c : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 216) 8 h)
  by (apply KV; [intros kk Hkk; cbn in Hkk; split; lia | exact H216]).
assert (H152c : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 152) 8 (h + 440))
  by (apply KV; [intros kk Hkk; cbn in Hkk; split; lia | exact H152]).
destruct (a3f_used_split 1 ltac:(lia)) as (Lpre & Esp2 & Esp3).
assert (GU : garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OUSED) (a3f_used (1 + 1))).
{ rewrite Esp3. pose proof HUSED as G0. rewrite Esp2 in G0.
  apply garr8_app in G0 as [Gp G0]. apply garr8_app in G0 as [_ Gs].
  apply garr8_app. split.
  - apply KG; [|exact Gp]. intros kk Hkk. rewrite Lpre in Hkk. unfold d_obj, dobj_off. split; lia.
  - apply garr8_app. split.
    + rewrite Lpre. replace (d_obj cx OUSED + Z.of_nat (Z.to_nat (4 * 1))) with (d_FB cx + 1668)
        by (unfold d_obj, dobj_off; lia).
      exact (px1_g8_w1 _ _ V1668c).
    + apply KG; [|exact Gs]. intros kk Hkk.
      assert (Lsuf : length (skipn (Z.to_nat (4 * 1 + 4)) (a3f_used 1)) = 24%nat) by (vm_compute; reflexivity).
      rewrite Lsuf in Hkk. rewrite Lpre. unfold d_obj, dobj_off. cbn [length]. split; lia. }
assert (HBODYc : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem ms)).
{ apply (d_body_rt B cx h n n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx)
    (fun a => d_FB cx + 1668 <= a < d_FB cx + 1672) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right. intros Hrd. cbv beta in Ha.
    unfold d_rdset, d_objr in Hrd. unfold d_obj in Hrd. cbn [dobj_off dobj_size] in Hrd.
    pose proof HGEO as (Gf0 & Gfc & Gh0 & Ghc & Gcs & Gpl & Gfh & Gin). pose proof fs6 as F6.
    destruct Hrd as [Hx | [Hx | [Hx | [Hx | [Hx | [(Hn0 & Hx) | [(Hro & _ & _) | Hcn]]]]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + destruct Gfh; lia.
    + destruct (Gin Hn0) as (_ & _ & Gd & _). lia.
    + exact (off_img_not_img _ _ a HOFF ltac:(rewrite fs6; lia) (in_roP_img a Hro)).
    + exact (off_img_not_img _ _ a HOFF ltac:(rewrite fs6; lia) (proj2 (proj2 HCAN) a Hcn)).
  - intros a Ha Hna. exact (KC a Ha Hna).
  - intros a _ (Hh & b & Hb). split; [exact Hh|].
    pose proof (HG (Z_to_bv 64 a)) as G1. unfold mrestrict in G1. rewrite Hh, Hb in G1.
    assert (G2 : ms_mem ms (Z_to_bv 64 a) <> None) by (apply G1; discriminate).
    destruct (ms_mem ms (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | congruence].
  - exact HFRMc.
  - exact HSHDc.
  - lia. }
assert (HCTXc : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k) by exact (conj HBASE (conj HJr HFRS)).
pose proof (proj1 HJr) as HARc.
pose proof HBODYc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HIMGc & _).
pose proof (mc_cv_ok B W (ms_mem ms) MCRO MCUN HIMGc) as HCV.
pose proof (DCRO LAWS (conj DRO (conj GM (HV))) ly3 S3 W (ms_mem ms) md' HARc HIMGc) as (_ & _ & _ & HSTR & _).
pose proof (a3f_rolestr W (ms_mem ms) _ Hr02 HSTR) as HRS.
destruct (mdf_rostr_x W (ms_mem ms) _ _ HRS) as (slack & XNZ & XG & XSL & X0 & X63 & X32 & XAM & XRA & XSH & XLE).
pose proof (proj1 (proj1 HRS)) as FR.
pose proof (a3f_obj T1 now count os 1 LT1 TOK1 Hnow HJR ltac:(lia)) as HOB. cbv zeta in HOB.
destruct HOB as (_ & JTR & _).
change (disco_json_text.e_role (reac_disco_table_json_c.tj_entry T1 1)) with (disco_table_c.role_of_e T1 1) in JTR.
set (tk := nth 1 (nth (Z.to_nat 1) os []) disco_json_reader_model.tok_none) in *.
pose proof HBLK as (HPm & _ & _ & _).
assert (Inb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPm)). unfold a3_xb. cbn [app In]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Inb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W (ms_mem ms) md' buf _ DFRAME_CLASS (c_fpos cx) HARc Inb HFin3) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EFA3, fs6 in Hsep.
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as Hrq.
pose proof HBUF as (Hr2 & GBUF). unfold a3_r in Hr2.
assert (GOOc : garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OO)
  (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))).
{ apply KG; [|exact HOO]. intros kk Hkk. rewrite length_map, (mdk_objs_len buf vpad os HVP H6), Los in Hkk.
  unfold d_obj, dobj_off. split; lia. }
assert (GBUFc : garr8 SEGS (rd W (ms_mem ms)) buf (a3_text T1 now ++ [0])).
{ apply KG; [|exact GBUF]. intros kk Hkk. rewrite length_app in Hkk. cbn [length] in Hkk. split; lia. }
destruct (mdk_site SEGS (rd W (ms_mem ms)) T1 now count os 1 1 (d_obj cx OO) buf
  (d_obj cx OO + 144 * 1 + 24 * Z.of_nat 1) 1 vpad (disco_json_text.rolename (disco_table_c.role_of_e T1 1)) tk
  LT1 TOK1 Hnow HJR ltac:(lia) ltac:(lia) HVP GOOc GBUFc ltac:(lia) ltac:(lia) eq_refl ltac:(lia) FR JTR eq_refl)
  as (J1 & J2 & J3 & F1 & F2 & F3 & Hvp & Hvn & JM & HlenP & GP & Hvp0 & Hvp63).
destruct (mdk_obj_tok os count 1 1 Los H6 ltac:(lia) ltac:(lia)) as (Ho & Ht0 & Ho6).
pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Hinb _ (nth_error_In _ _ Ho)) tk
  (nth_error_In _ _ Ht0)) as Hib.
destruct Hib as [Hz | (Hs0 & Hl0 & Hsl)]; [rewrite J1 in Hz; discriminate Hz|].
unfold disco_jscalar_model.jlen in Hsl.
destruct (mdf_frame_range B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md' k h n (a3_xb buf op) dsh_ser2
  240 1296 (d_obj cx OO + 144 * 1 + 24 * Z.of_nat 1) 20 HCTXc HBODYc ltac:(vm_compute; reflexivity) ltac:(lia)
  ltac:(unfold DFRAME_SIZE; lia) ltac:(unfold d_obj; cbn [dobj_off]; lia) ltac:(unfold d_obj; cbn [dobj_off]; lia)
  ltac:(lia)) as (AMv & RAv & SHv).
assert (LTr : length (printf_facts_c.pf_bytes (disco_json_text.rolename (disco_table_c.role_of_e T1 1))) =
  length (disco_json_text.rolename (disco_table_c.role_of_e T1 1))) by (unfold printf_facts_c.pf_bytes; apply length_map).
assert (Lr7 : (length (disco_json_text.rolename (disco_table_c.role_of_e T1 1)) <= 7)%nat).
{ unfold disco_json_text.rolename. destruct (_ =? 1); [|destruct (_ =? 2)]; cbn; lia. }
assert (Hobj : (a3f_roleobj (disco_table_c.role_of_e T1 1) < disco_nobj)%nat).
{ unfold a3f_roleobj, disco_nobj. destruct (_ =? 2); [|destruct (_ =? 1)]; lia. }
pose proof (pa_obj_img _ Hobj) as HXI.
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
eapply SRr_bind.
{ apply (aj_jtok_at B LAWS TJTOK fq W R (ms_mem ms) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md' k (d_A cx - d_S cx) (d_obj cx OO + 144 * 1 + 24 * Z.of_nat 1)
    (VAL (A_OBJ (a3f_roleobj (disco_table_c.role_of_e T1 1)))) 1 (disco_json_reader_model.tv_kind tk)
    (buf + snd (fst tk)) (snd tk) (printf_facts_c.pf_bytes (disco_json_text.rolename (disco_table_c.role_of_e T1 1)))
    slack (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (a3_text T1 now) tk)) HJr).
  - rewrite SpR. lia.
  - lia.
  - lia.
  - unfold TJTOK_IS_STK, ESTACK, LLVMF_STK. lia.
  - rewrite (SR 3%bv ltac:(cbv; tauto)). exact Rgp.
  - rewrite (SR 4%bv ltac:(cbv; tauto)). exact Rtp.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - exact HIMGc.
  - exact HCV.
  - rewrite Q10. unfold w64, d_obj, dobj_off. f_equal. lia.
  - exact Q11.
  - exact Q12x.
  - lia.
  - rewrite J1. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - exact F1.
  - exact F2.
  - exact F3.
  - exact Hvp.
  - exact Hvn.
  - exact AMv.
  - exact RAv.
  - exact SHv.
  - left. rewrite SpR. unfold d_obj, dobj_off, TJTOK_IS_STK, ESTACK. lia.
  - exact XNZ.
  - exact XG.
  - exact XSL.
  - exact X0.
  - exact X63.
  - exact X32.
  - exact XAM.
  - exact XRA.
  - exact XSH.
  - left. rewrite SpR. unfold TJTOK_IS_STK, ESTACK, IMG_TOP in *. unfold printf_facts_c.pf_bytes in *. lia.
  - intros _ _. split; [exact HlenP|]. split; [exact GP|]. split; [exact Hvp0|]. split; [exact Hvp63|].
    rewrite LTr. split.
    { apply (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md' buf _ _ _ HARc Inb); lia. }
    split.
    { apply (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md' buf _ _ _ HARc Inb); lia. }
    split.
    { intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md' buf _ _ _ HARc Inb); lia. }
    left. rewrite SpR. unfold TJTOK_IS_STK, ESTACK. lia. }
cbv beta. intros W2 c2 HWW2 (fq2 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hcsr2 & HJ4 & HJc & HP & HPerm & Hfr & Hres).
destruct Hres as [(_ & R10') | (Hnm & _)]; [| exfalso; exact (Hnm JM)].
clear HG.
pose proof HJc as (_ & _ & _ & HWle & _ & HfrC & _).
assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFRS).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 8240 <= a < d_A cx) ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha Hna. apply Hfr; [exact Ha | rewrite SpR; unfold TJTOK_IS_STK, ESTACK; lia]. }
assert (KV4 : forall a nn v, (forall kk, 0 <= kk < Z.of_nat nn -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_A cx - 8240 <= a + kk < d_A cx)) ->
  val_mem SEGS (rd W (ms_mem ms)) a nn v -> val_mem SEGS (rd W2 mem4) a nn v).
{ intros a nn v Hb V. apply (val_mem_kept SEGS (w_H W) (w_H W2) (ms_mem ms) mem4 a nn v); [|exact V].
  intros kk Hkk. destruct (Hb kk Hkk) as [Hb1 Hb2]. exact (KM _ Hb1 Hb2). }
assert (KG4 : forall a l, (forall kk, 0 <= kk < Z.of_nat (length l) -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_A cx - 8240 <= a + kk < d_A cx)) ->
  garr8 SEGS (rd W (ms_mem ms)) a l -> garr8 SEGS (rd W2 mem4) a l).
{ intros a l Hb Gx. apply (px1_g8_kept (w_H W) (w_H W2) (ms_mem ms) mem4 a l); [|exact Gx].
  intros kk Hkk. destruct (Hb kk Hkk) as [Hb1 Hb2]. exact (KM _ Hb1 Hb2). }
pose proof HFRMc as (E2 & HdE2 & HREG2 & HFLAG2 & _ & _).
pose proof HdE2 as (EE2 & E322 & HEI2 & E602 & EF2 & ESH2).
pose proof (DSEAT LAWS PAL fq2 cx dsh_ser2 ly3 S3 W R (ms_mem ms) md' k E2 AF_jtok_is
  (SLit 0 :: SOff A_TEXT 8104 :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTXc HdE2 HREG2 HFLAG2 (px1_regs2 cx E2 R 8104 HEI2 Q1)
  (DFACTS LAWS cx ly3 S3 W (ms_mem ms) md' k E2 (map (getr R) (tl all_regs)) [] [] HCTXc HdE2 I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
assert (HEId : img_env VAL A_LIM (d_env cx E2 (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI2 | unfold AT_FL, A_LIM; lia]).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W2) mem4) HP [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict YK11.mkst]. pose proof fs6 as F6. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (px1_kept _ (w_H W) (w_H W2) (ms_mem ms) mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite (EE2 2%nat 2%bv eq_refl). reflexivity.
    + intros a Ha. apply KM; lia.
    + intros a Ha. lia.
  - eapply (px1_kept _ (w_H W) (w_H W2) (ms_mem ms) mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite E602. unfold w64.
      apply unsigned_lit_small. lia.
    + intros a Ha. apply KM; lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (px1_kept _ (w_H W) (w_H W2) (ms_mem ms) mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite EF2. unfold w64.
      apply unsigned_lit_small. lia.
    + intros a Ha. apply KM; lia.
    + intros a Ha. apply GFpres4. unfold DFRAME_SIZE in Ha. lia.
  - eapply (px1_kept _ (w_H W) (w_H W2) (ms_mem ms) mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). change 529%nat with AT_SH. rewrite ESH2. unfold w64.
      apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KM; unfold shadow_addr, SHADOW_OFF in *; lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. unfold DFRAME_SH in Ha. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (HE2' : d_E cx (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply px1_dE_hi; [apply d_E_env; exact HdE2 | unfold AT_FL; lia]).
assert (HFL2 : ew (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
  Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (H216m : val_mem SEGS (rd W2 mem4) (d_A cx + 216) 8 h)
  by (apply KV4; [intros kk Hkk; cbn in Hkk; split; lia | exact H216c]).
assert (H152m : val_mem SEGS (rd W2 mem4) (d_A cx + 152) 8 (h + 440))
  by (apply KV4; [intros kk Hkk; cbn in Hkk; split; lia | exact H152c]).
pose proof (DLAND LAWS FFL fq2 cx h dsh_ser2 ly4 S4 W2 md4 k _ _
  (YK11.mkst (fx := fq2) regs4 (Z_to_bv 64 (BASE + 8104)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2' HFL2 HS2 ltac:(vm_compute; reflexivity) H216m H152m) as (HFRM4 & HSHD4).
pose proof (d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W
  (ms_mem ms) ly4 S4 W2 mem4 md4 k (d_A cx - 8240) (d_A cx) HBODYc (conj HBASE HJ4)
  ltac:(unfold LLVMF_STK; lia) ltac:(lia) ltac:(intros a Ha Hna; exact (KM a Ha Hna)) HPerm HFRM4 HSHD4) as HBODY4.
rewrite Q1.
pose proof (ast_ok_pi_set_reg_fp _ _ _ (10%bv : bv 5) (SLit 1) HS2 eq_refl) as HS3.
match type of HS3 with ?Q -> _ => assert (H10 : Q) end.
{ cbn [sv_denot ms_regs restrict YK11.mkst]. rewrite R10'. reflexivity. }
specialize (HS3 H10). clear H10.
pose proof (st_ok_pi_submem _ _ _ [] HS3 (submem_nil _) eq_refl) as HS4.
cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS4. norm_ss HS4. clear HS2 HS3.
pose proof HS4 as HS4c.
pose proof (paj_run_to (fx := fq2) (PI := PI) B LAWS) as RUNTO.
assert (SHOK4 : sh_ok SEGS (SOff 32 0) [] (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562
  (map (getr regs4) CLOB)) (mrestrict (w_H W2) mem4)) by apply Forall_nil.
assert (HEI4 : img_env VAL A_LIM (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply img_env_havoc_hi; [exact HEId | unfold A_LIM; lia]).
paj_run_to_tok RUNTO HS4 HJ4 SHOK4 (0, 0) R1_OFF.
{ intros a (r & Hin & _). destruct Hin. }
match goal with Hf : frame_of _ _ mem4 (ms_mem ?m5) |- _ =>
  assert (Emem5 : ms_mem m5 = mem4)
    by (apply functional_extensionality; intros x; apply Hf; intros (r & Hin & _); destruct Hin) end.
pmkst HS4.
assert (SR5 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 24; 25; 26]%bv -> getr (ms_regs ms0) r = getr regs4 r).
{ intros r Hr. apply (px1_same_reg fq2 _ _ _ _ _ (w_H W2) (w_H W2) r HS4c HS4).
  cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (P2 : getr (ms_regs ms0) 2 = getr regs 2) by px1_preg SR5 HP SR regs4 R (2%bv : bv 5) 2%Z.
assert (P3 : getr (ms_regs ms0) 3 = getr regs 3) by px1_preg SR5 HP SR regs4 R (3%bv : bv 5) 3%Z.
assert (P4 : getr (ms_regs ms0) 4 = getr regs 4) by px1_preg SR5 HP SR regs4 R (4%bv : bv 5) 4%Z.
assert (P8 : getr (ms_regs ms0) 8 = getr regs 8) by px1_preg SR5 HP SR regs4 R (8%bv : bv 5) 8%Z.
assert (P9 : getr (ms_regs ms0) 9 = getr regs 9) by px1_preg SR5 HP SR regs4 R (9%bv : bv 5) 9%Z.
assert (P18 : getr (ms_regs ms0) 18 = getr regs 18) by px1_preg SR5 HP SR regs4 R (18%bv : bv 5) 18%Z.
assert (P20 : getr (ms_regs ms0) 20 = getr regs 20) by px1_preg SR5 HP SR regs4 R (20%bv : bv 5) 20%Z.
assert (P25 : getr (ms_regs ms0) 25 = getr regs 25) by px1_preg SR5 HP SR regs4 R (25%bv : bv 5) 25%Z.
assert (P26 : getr (ms_regs ms0) 26 = getr regs 26) by px1_preg SR5 HP SR regs4 R (26%bv : bv 5) 26%Z.
assert (P24 : getr (ms_regs ms0) 24 = w64 (d_obj cx OT + 48 * 1)).
{ transitivity (getr regs4 24); [exact (SR5 24%bv ltac:(cbv; tauto))|].
  transitivity (getr R 24); [exact (HP 24 ltac:(unfold acallee_saved; lia))|].
  rewrite Q24. unfold w64, d_obj, dobj_off. f_equal. lia. }
assert (K34 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_FB cx + 1668 <= a < d_FB cx + 1672) ->
  ~ (d_A cx - 8240 <= a < d_A cx) -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hb1 Hb2. rewrite (KM a Ha Hb2). exact (KC a Ha Hb1). }
assert (KV34 : forall a nn v, (forall kk, 0 <= kk < Z.of_nat nn -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_FB cx + 1668 <= a + kk < d_FB cx + 1672) /\ ~ (d_A cx - 8240 <= a + kk < d_A cx)) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W2 mem4) a nn v).
{ intros a nn v Hb V. apply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4 a nn v); [|exact V].
  intros kk Hkk. destruct (Hb kk Hkk) as (Hb1 & Hb2 & Hb3). exact (K34 _ Hb1 Hb2 Hb3). }
assert (KG34 : forall a l, (forall kk, 0 <= kk < Z.of_nat (length l) -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_FB cx + 1668 <= a + kk < d_FB cx + 1672) /\ ~ (d_A cx - 8240 <= a + kk < d_A cx)) ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W2 mem4) a l).
{ intros a l Hb Gx. apply (px1_g8_kept (w_H W) (w_H W2) mem3 mem4 a l); [|exact Gx].
  intros kk Hkk. destruct (Hb kk Hkk) as (Hb1 & Hb2 & Hb3). exact (K34 _ Hb1 Hb2 Hb3). }
pose proof HSP1 as ((S232 & S344) & S224 & S248).
assert (M232 : val_mem SEGS (rd W2 mem4) (d_A cx + 232) 8 i) by (apply KV34; [px1_kb | exact S232]).
assert (M344 : val_mem SEGS (rd W2 mem4) (d_A cx + 344) 8 now) by (apply KV34; [px1_kb | exact S344]).
assert (M224 : val_mem SEGS (rd W2 mem4) (d_A cx + 224) 8 n) by (apply KV34; [px1_kb | exact S224]).
assert (M248 : val_mem SEGS (rd W2 mem4) (d_A cx + 248) 8 (d_cur cx n)) by (apply KV34; [px1_kb | exact S248]).
assert (M368 : val_mem SEGS (rd W2 mem4) (d_A cx + 368) 8 1) by (apply KV34; [px1_kb | exact H368]).
assert (M336 : val_mem SEGS (rd W2 mem4) (d_A cx + 336) 8 count) by (apply KV34; [px1_kb | exact H336]).
assert (M392 : val_mem SEGS (rd W2 mem4) (d_A cx + 392) 8 (d_obj cx OO + 144 * 1))
  by (apply KV34; [px1_kb | exact H392]).
assert (M408 : val_mem SEGS (rd W2 mem4) (d_A cx + 408) 8 1) by (apply KV34; [px1_kb | exact H408]).
assert (GOT4 : garr8 SEGS (rd W2 mem4) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1)).
{ apply KG34; [|exact HOT]. intros kk Hkk. rewrite length_map, LT1 in Hkk. unfold d_obj, dobj_off.
  split; [|split]; lia. }
assert (GBUF4 : garr8 SEGS (rd W2 mem4) buf (a3_text T1 now ++ [0])).
{ apply KG4; [|exact GBUFc]. intros kk Hkk. rewrite length_app in Hkk. cbn [length] in Hkk.
  unfold LLVMF_STK in *. split; lia. }
assert (GOO4 : garr8 SEGS (rd W2 mem4) (d_obj cx OO)
  (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))).
{ apply KG4; [|exact GOOc]. intros kk Hkk. rewrite length_map, (mdk_objs_len buf vpad os HVP H6), Los in Hkk.
  unfold d_obj, dobj_off. split; lia. }
assert (GU4 : garr8 SEGS (rd W2 mem4) (d_obj cx OUSED) (a3f_used (1 + 1))).
{ apply KG4; [|exact GU]. intros kk Hkk. rewrite (a3f_used_bytes (1 + 1) ltac:(lia)) in Hkk.
  unfold d_obj, dobj_off. split; lia. }
rewrite Emem5.
apply SRr_ret.
unfold f_r1, a3f_st. split.
{ destruct HFROM as (HA3 & HW0 & HLT0 & HEX). exact (conj HA3 (conj (wle_trans _ _ _ _ HW0 HWle) (conj HLT0 HEX))). }
unfold d_arm_at_pf, d_at.
exists fq2, ly4, S4, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), k, acc.
split; [unfold cfg_at, w64, R1_OFF; reflexivity|].
split; [destruct Hcsr2 as [Hcs | Hcs]; [rewrite Hcs; assumption | exact Hcs]|]. split; [exact HBASE|].
split; [rewrite <- Emem5; exact HJ4|].
split; [exact HFR4|]. split; [exact Hk|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rL. split; [unfold spZ; rewrite P2; exact Rsp|]. split; [rewrite P3; exact Rgp|].
  split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact R8|]. split; [rewrite P9; exact R9|].
  split; [rewrite P18; exact R18|]. split; [rewrite P20; exact R20|]. rewrite P25; exact R25. }
split; [split; [rewrite P26; exact R26 | exact P24]|].
split.
{ split; [split; [split; [exact M232 | exact M344] | split; [exact M224 | exact M248]]|].
  split; [split; [exact (ex_intro _ removed (conj Hage Hpost)) | exact GOT4]|].
  split; [split; [exact Hr2 | exact GBUF4]|].
  split; [exact HJR|]. split; [exact HVP|]. split; [exact GOO4|].
  unfold a3f_pyk, a3f_slots. split; [split; [exact Hpc | split; [exact M368 | exact M336]]|].
  split; [exact M392|]. split; [exact M408|]. exact GU4. }
split; [split; [exact M232 | exact M344]|].
exact HBODY4.
}
destruct Hrole as [Er | [Er | Er]]; rewrite Er in HFCS.
all: pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PFX_OFF (a3f_sr 0) (a3f_vals regs)
  px1_acs _ [] (d_facts [] []) HCTX HdE HREG HFLAG
  (a3f_regs_ok cx E 0 regs HdE HA64 ltac:(rewrite Z.add_0_r; exact Rsp) R8 R9 R18 R20 R25)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (a3f_vals regs) [] [] HCTX HdE I I) HACS HFCS (Forall_nil _) I
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
all: unfold ss_d in HS0.
all: rewrite app_nil_r in HS0.
all: pose proof (st_ok_pi_submem _ _ _ _ HS0 (px1_narrow_sub dsh_ser2 px1_acs _) ltac:(vm_compute; reflexivity)) as HS1.
all: clear HS0.
all: cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
all: pose proof (ast_ok_pi_set_reg_fp _ _ _ (14%bv : bv 5) (SOff AT_F 2160) HS1 eq_refl H14) as HS.
all: clear HS1.
all: norm_ss HS.
all: pose proof HS as HS0c.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
  assert (WR : forall a, in_wrange Ex (ss_mem ssx) a -> d_FB cx + 1668 <= a < d_FB cx + 1672)
    by (intros a (r & Hin & Ha); cbn [ss_mem In] in Hin;
        destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; try lia;
        rewrite d_env_old in Ha by (unfold AT_FL; lia); change 516%nat with AT_F in Ha; rewrite HFU in Ha; lia) end.
all: paj_run_tok RUN HS HJ SHOK (0, 0).
all: try solve [intros a Hw; pose proof (WR a Hw) as Ha; exact (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia)))].
all: rewrite pa_sigma_jtok_is in HS.
all: pose proof (px1_kept_of _ _ (w_H W) mem3 (ms_mem ms) _ _ HF WR) as KC.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
  pose proof (HS : st_ok_pi SEGS VAL Ex (setpc ssx AF_jtok_is) msx) as HSp end.
all: prreg HS (1%bv : bv 5) Q1.
all: prreg HS (10%bv : bv 5) Q10.
all: prreg HS (11%bv : bv 5) Q11.
all: prreg HS (12%bv : bv 5) Q12.
all: prreg HS (24%bv : bv 5) Q24.
all: try rewrite d_env_old in Q10 by (unfold AT_FL; lia).
all: try rewrite d_env_old in Q12 by (unfold AT_FL; lia).
all: try rewrite d_env_old in Q24 by (unfold AT_FL; lia).
all: try change 516%nat with AT_F in Q10.
all: try change 516%nat with AT_F in Q24.
all: try rewrite HFU in Q10.
all: try rewrite HFU in Q24.
all: assert (SR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r)
  by (intros r Hr; apply (px1_same_reg fq _ _ _ _ _ (w_H W) (w_H W) r HS0c HS); cbv [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr).
all: assert (Q12x : getr (ms_regs ms) 12 = w64 (VAL (A_OBJ (a3f_roleobj (disco_table_c.role_of_e T1 1)))))
  by (rewrite Q12, Er; unfold w64; lazymatch goal with |- ew ?Ex ?nn = _ =>
        transitivity (Z_to_bv 64 (bv_unsigned (ew Ex nn))); [symmetry; apply Z_to_bv_bv_unsigned|] end;
      f_equal; apply HEI0; cbv; lia).
all: assert (H216c : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 216) 8 h)
  by (apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms));
      [intros kk Hkk; cbn in Hkk; apply KC; lia | exact H216]).
all: assert (H152c : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 152) 8 (h + 440))
  by (apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms));
      [intros kk Hkk; cbn in Hkk; apply KC; lia | exact H152]).
all: pose proof (DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W (with_vm_backing (m_vm_lazy md3) mat md3) k
  (d_env cx E (a3f_vals regs)) _ ms (conj HBASE (conj HJ HFRS)) (d_E_env cx E (a3f_vals regs) HdE)
  (d_env_fl cx E (a3f_vals regs)) HSp ltac:(vm_compute; reflexivity) H216c H152c) as (HFRMc & HSHDc).
all: lazymatch type of HSp with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx msx 2 r HSp ltac:(vm_compute; reflexivity)) as RF end.
all: assert (V1668c : val_mem SEGS (rd W (ms_mem ms)) (d_FB cx + 1668) 4 1)
  by (eapply (field_of_region _ _ 516%nat (d_FB cx) _ _ _ _ _ 1668 4 (SLit 1) 1 RF);
      [rewrite d_env_old by (unfold AT_FL; lia); change 516%nat with AT_F; exact HFU | left; reflexivity |
       reflexivity | lia | lia]).
all: exact (CONT ms mat HJ KC HG Q1 Q10 Q11 Q12x Q24 SR HFRMc HSHDc V1668c).
Qed.

End h.
End f.
End d.
