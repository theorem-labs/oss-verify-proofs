(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 329 of its 381 lines of code are new or changed and 444 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3JsonA1.v; 198 of its 259 lines of code are new or changed and 320 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC81 YC4b YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonMs DiscoArm3JsonADefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs reac_disco_table_age_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition ja3_sr : list sv := SLit 0 :: atom_regs 531 8 ++ SOff AT_A 0 :: atom_regs 540 22.
Definition ja3_rs : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 368 416 dslot_chunks;
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 dfhdr_chunks;
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_scr);
   got_regionP; bcell_regionP 32].

Lemma ja3_neg : forall r, 0 <= r < 2 ^ 64 -> alu64 ALU_SUB (Z_to_bv 64 0) (Z_to_bv 64 r) = w64 (- r).
Proof.
  intros r Hr. rewrite zalu64_sound. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold zalu64, zalu_raw, zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zmod_0_l, (Z.mod_small r) by lia. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma ja3_subm : submem ja3_rs (d_kregions dsh_scr [] []).
Proof.
  unfold ja3_rs, d_kregions, fshadow_region.
  repeat (apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
    let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; rewrite ?app_nil_r; exact Hc|]).
  apply submem_nil.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ja3_dx : forall (cx : dcx) E (regs : bvmap 5 word) (nn j : nat), nn = (AT_X + j)%nat -> (j < 31)%nat ->
  ew (d_env cx E (map (getr regs) (tl all_regs))) nn = getr regs (nth j (tl all_regs) (0%bv : bv 5)).
Proof.
  intros cx E regs nn j -> Hj. rewrite d_env_x by (cbn; lia).
  change (Z_to_bv 64 0) with (getr regs (0%bv : bv 5)). apply map_nth.
Qed.

Lemma ja3_present : forall (H : word -> bool) (m : word -> option byte) (nb : nat) p,
  (forall a, p <= a < p + Z.of_nat nb -> apresent H m a) ->
  exists A : list byte, length A = nb /\ garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) A).
Proof.
  intros H m nb. induction nb as [|nb IH]; intros p Hp.
  - exists []. split; [reflexivity|]. apply garr8_nil.
  - destruct (Hp p ltac:(lia)) as (Hh & b & Hb).
    destruct (IH (p + 1) ltac:(intros a Ha; apply Hp; lia)) as (A & HA & HG).
    exists (b :: A). split; [cbn [length]; rewrite HA; reflexivity|]. cbn [map].
    assert (Hav : aview SEGS H m p = Some (bv_unsigned b)).
    { unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
    destruct (val_mem1_of_aview SEGS H m p (bv_unsigned b) Hav) as (Hv & Hr).
    exact (garr8_cons_x SEGS _ p _ _ Hv Hr HG).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.

Theorem jA_S3 : jA_S3_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin W c Hms.
destruct Hms as (HFROM & Hv).
unfold d_arm_at_pf, d_at in Hv.
destruct Hv as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HCSR & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R22 & R26 & R10 & R23 & R24) & (HSP1 & HTAB & HBUF & (HJF & HJO) & HZ) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (T & G & Lk & HL & HFRM & _ & _ & HBLK & _).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
pose proof (alloc_ceiling_lt (rc := rc)) as Hceil.
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBLK as (HPerm0 & _ & _ & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & _).
assert (Hrq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hrq in Hbceil.
destruct HBUF as (Hr2 & HgB).
destruct HTAB as ((rem & Hage & Hpost) & HgT).
pose proof Hpost as (HlenT1 & _).
pose proof HJF as (_ & _ & _ & Hjlen & _).
assert (Har : 0 <= a3_r T1 now <= 969) by (unfold a3_r; lia).
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
assert (E60 : ew E 60%nat = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
pose proof (d_E_env cx E (map (getr regs) (tl all_regs)) HE) as HE'.
pose proof HE' as (EE' & E32' & HEI' & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E (map (getr regs) (tl all_regs))) AT_A) = d_A cx).
{ rewrite E60'. unfold w64. apply unsigned_lit_small. lia. }
assert (HRO : regs_ok (d_env cx E (map (getr regs) (tl all_regs))) ja3_sr regs).
{ regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
    | lazymatch goal with |- _ = sv_denot _ (SOff 60 0) =>
        cbn [sv_denot]; rewrite d_env_old by (unfold AT_FL; lia); rewrite E60; unfold w64;
        rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; exact Rs1 end ]). }
pose proof (DSEAT LAWS PAL fq cx dsh_scr ly3 S3 W regs mem3 md3 k E JA_RET2 ja3_sr (map (getr regs) (tl all_regs))
  [] [] [] (d_facts [] []) HCTX HE HREG HFLAG HRO
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr regs) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ ja3_rs HS0 ja3_subm ltac:(vm_compute; reflexivity)) as HS.
clear HS0.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (map (getr regs) (tl all_regs))) (mrestrict (w_H W) mem3))
  by (unfold sh_ok; constructor).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
unfold cfg_at, w64.
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) OBJ_OFF.
{ cbn [ss_mem]. unfold ja3_rs.
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|].
  eapply awr_ok_cons_stack_off with (n := AT_A) (d := d_A cx - d_S cx);
    [reflexivity | rewrite U60; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|].
  apply awr_ok_cons_ro; [unfold fshadow_region; cbn [YP09.r_whi YP09.r_wlo]; lia|].
  apply awr_ok_cons_ro; [unfold got_regionP; cbn [YP09.r_whi YP09.r_wlo]; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn [YP09.r_whi YP09.r_wlo]; lia|].
  apply awr_ok_nil. }
pmkst HS.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HCTX' : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md' k HCTX')
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GSTK' & _ & _ & _ & _).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 368 <= a < d_A cx + 416) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hno. unfold aview, mbyte. cbv beta. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (r & Hin & Hr). cbn [ss_mem] in Hin. unfold ja3_rs in Hin.
  cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  unfold fshadow_region, got_regionP, bcell_regionP in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  first [lia | rewrite U60 in Hr; lia]. }
assert (KVm : forall a nb v, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat nb -> ~ (d_A cx + 368 <= x < d_A cx + 416)) ->
  val_mem SEGS (rd W mem3) a nb v -> val_mem SEGS (rd W (ms_mem ms)) a nb v).
{ intros a nb v H0 H1 H2 Hv. apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 (ms_mem ms) a nb v); [|exact Hv].
  intros x Hx. apply KA; [lia | exact (H2 x Hx)]. }
assert (KV8 : forall off v, 0 <= off -> off + 8 <= 368 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v).
{ intros off v H0 H1 Hv. apply KVm; [lia | lia | intros x Hx; lia | exact Hv]. }
assert (KG : forall p L, 0 <= p -> p + Z.of_nat (length L) <= 2 ^ 64 ->
  (forall x, p <= x < p + Z.of_nat (length L) -> ~ (d_A cx + 368 <= x < d_A cx + 416)) ->
  garr8 SEGS (rd W mem3) p L -> garr8 SEGS (rd W (ms_mem ms)) p L).
{ intros p L H0 H1 H2 Hg. apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms) p L); [|exact Hg].
  intros x Hx. apply KA; [lia | exact (H2 x Hx)]. }
assert (Hkept : d_kept (fun a => d_S cx - LLVMF_STK <= a < d_S cx) W mem3 W (ms_mem ms)).
{ intros a Ha HnR. apply KA; [exact Ha|]. unfold LLVMF_STK in HnR. lia. }
assert (Hpres : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a).
{ intros a (Hh & b & Hb). split; [exact Hh|].
  assert (Hg2 : mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a) <> None).
  { apply HG. unfold mrestrict. rewrite Hh, Hb. discriminate. }
  unfold mrestrict in Hg2. rewrite Hh in Hg2.
  destruct (ms_mem ms (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; exact (Hg2 eq_refl)]. }
assert (H216' : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 216) 8 h) by (apply KV8; [lia | lia | exact H216]).
assert (H152' : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 152) 8 (h + 440)) by (apply KV8; [lia | lia | exact H152]).
pose proof (DLAND LAWS FFL fq cx h dsh_scr ly3 S3 W md' k (d_env cx E (map (getr regs) (tl all_regs))) _ ms
  HCTX' HE' (d_env_fl cx E _) HS ltac:(vm_compute; reflexivity) H216' H152') as (HFRM' & HSHD').
pose proof (d_body_rt B cx h n n (a3_xb buf op) dsh_scr dsh_scr ly3 S3 W mem3 (ms_mem ms) (d_S cx - LLVMF_STK) (d_S cx)
  (fun a => d_S cx - LLVMF_STK <= a < d_S cx) HBODY ltac:(lia) ltac:(lia) (fun a Ha => or_introl Ha) Hkept
  (fun a _ Hp => Hpres a Hp) HFRM' HSHD' ltac:(lia)) as HBODY'.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite (ja3_dx cx E regs 532 1 eq_refl ltac:(lia)) in Q2. rewrite (ja3_dx cx E regs 533 2 eq_refl ltac:(lia)) in Q3.
rewrite (ja3_dx cx E regs 534 3 eq_refl ltac:(lia)) in Q4. rewrite (ja3_dx cx E regs 538 7 eq_refl ltac:(lia)) in Q8.
rewrite (ja3_dx cx E regs 548 17 eq_refl ltac:(lia)) in Q18. rewrite (ja3_dx cx E regs 552 21 eq_refl ltac:(lia)) in Q19.
rewrite (ja3_dx cx E regs 550 19 eq_refl ltac:(lia)) in Q20. rewrite (ja3_dx cx E regs 552 21 eq_refl ltac:(lia)) in Q22.
rewrite (ja3_dx cx E regs 553 22 eq_refl ltac:(lia)) in Q23. rewrite (ja3_dx cx E regs 554 23 eq_refl ltac:(lia)) in Q24.
rewrite (ja3_dx cx E regs 555 24 eq_refl ltac:(lia)) in Q25. rewrite (ja3_dx cx E regs 556 25 eq_refl ltac:(lia)) in Q26.
cbn [nth tl all_regs] in Q2, Q3, Q4, Q8, Q18, Q19, Q20, Q22, Q23, Q24, Q25, Q26.
rewrite d_env_old in Q9 by (unfold AT_FL; lia). rewrite E60 in Q9.
rewrite R22 in Q19. unfold w64 in Q19. rewrite (ja3_neg (a3_r T1 now) ltac:(lia)) in Q19.
destruct (ja3_present (w_H W) (ms_mem ms) 4 (d_A cx + 444) ltac:(intros a Ha; apply GSTK'; unfold LLVMF_STK; lia))
  as (vpad & Hvl & Hvg).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as R60.
cbn [ms_mem restrict] in R60.
pose proof (field_of_region _ _ _ _ _ _ _ _ _ 408 8%N (SLit 0) 0 R60 U60 ltac:(right; left; reflexivity) eq_refl
  ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn [Z.of_N]; lia)) as V408.
assert (D556 : sv_denot (d_env cx E (map (getr regs) (tl all_regs))) (SOff 556 1) = Z_to_bv 64 (buf + 1)).
{ cbn [sv_denot]. rewrite (ja3_dx cx E regs 556 25 eq_refl ltac:(lia)). cbn [nth tl all_regs]. rewrite R26. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
pose proof (field_of_region _ _ _ _ _ _ _ _ _ 368 8%N (SOff 556 1) (buf + 1) R60 U60 ltac:(left; reflexivity) D556
  ltac:(cbn [Z.of_N]; change (8 * 8) with 64; lia) ltac:(cbn [Z.of_N]; lia)) as V368.
change (N.to_nat 8) with 8%nat in V408, V368.
assert (HLB : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (Hob : map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad [jobj_empty]) = repeat 0 144)
  by (vm_compute; reflexivity).
unfold jcur in HZ. rewrite Z.mul_0_r, Z.add_0_r in HZ.
destruct HSP1 as ((H232 & H344) & H224 & H248).
apply SRr_ret. exists vpad.
unfold jobj_in, jcut. split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [reflexivity|].
split; [exact HCSR|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite Q2; exact Rsp|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
  split; [exact Q9|]. split; [rewrite Q18; exact Rs2|]. split; [rewrite Q20; exact Rs4|].
  rewrite Q25; exact Rs9. }
split.
{ split; [rewrite Q22; exact R22|]. split; [rewrite Q26; exact R26|].
  split; [rewrite Q24; exact R24|]. split; [exact Q19|]. split; [exact Q27|]. rewrite Q23; exact R23. }
split.
{ split.
  { split; [split; [apply KV8; [lia | lia | exact H232] | apply KV8; [lia | lia | exact H344]]|].
    split; [apply KV8; [lia | lia | exact H224] | apply KV8; [lia | lia | exact H248]]. }
  split.
  { split; [exists rem; split; [exact Hage | exact Hpost]|].
    apply KG; [unfold d_obj, dobj_off; lia | rewrite length_map, HlenT1; unfold d_obj, dobj_off; lia
      | intros x Hx; rewrite length_map, HlenT1 in Hx; unfold d_obj, dobj_off in Hx; lia | exact HgT]. }
  split.
  { split; [exact Hr2|].
    apply KG; [lia | rewrite HLB; lia | intros x Hx; rewrite HLB in Hx; lia | exact HgB]. }
  split; [exact HJF|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [exact HJO|].
  cbn [app].
  split; [exact V408|]. split; [exact V368|]. split; [exact Hvl|]. split; [exact Hvg|].
  split; [|constructor; [reflexivity | constructor]].
  rewrite Hob.
  apply KG; [unfold d_obj, dobj_off; lia | rewrite repeat_length; unfold d_obj, dobj_off; lia
    | intros x Hx; rewrite repeat_length in Hx; unfold d_obj, dobj_off in Hx; lia | exact HZ]. }
split; [destruct HSP0 as (H232b & H344b); split; [apply KV8; [lia | lia | exact H232b] | apply KV8; [lia | lia | exact H344b]]|].
exact HBODY'.
Qed.
End h.
End f.
End d.
