(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 365 of its 397 lines of code are new or changed and 37 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntLatch.v, with its module paths and numbers changed; 293 of its 375 lines of code are new or changed and 315 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC81 YC85 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame reac_frame_clean_len_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntRecCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition ya_sr : list sv :=
  [SLit 0; SOff 531 0; SOff AT_A 0; SOff 3 0; SOff 4 0; SOff 532 0; SOff 533 0; SOff 534 0;
   SOff AT_STK 0; SOff AT_A 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 539 0; SOff 540 0;
   SOff 541 0; SOff 542 0; SLit WS_MASK; SOff 32 0; SLit 32; SOff 543 0; SLit 1; SOff 544 0;
   SOff 545 0; SOff 546 0; SOff 547 0; SOff AT_SH 0; SOff 548 0; SOff 549 0; SOff 550 0; SOff 551 0].

Definition ya_vals (regs : bvmap 5 word) (fr : Z) : list word :=
  [getr regs 1; getr regs 5; getr regs 6; getr regs 7; getr regs 10; getr regs 11; getr regs 12; getr regs 13;
   getr regs 14; getr regs 15; getr regs 16; getr regs 17; getr regs 21; getr regs 23; getr regs 24; getr regs 25;
   getr regs 26; getr regs 28; getr regs 29; getr regs 30; getr regs 31; Z_to_bv 64 fr].

Definition ya_acs : list YP09.chunk :=
  [YP09.mkChunk 136 (CVal 8 (SLit 0)); YP09.mkChunk 368 (CVal 8 (SOff 552 0))].

Definition ya_rs : smem := [YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ ya_acs)].

Lemma ya_sub : forall shf, submem ya_rs (d_kregions shf ya_acs [] ++ []).
Proof.
intros shf. unfold ya_rs, d_kregions. cbn [app].
apply submem_drop. apply submem_keep; [|apply submem_nil].
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
intros c Hc. exact Hc.
Qed.

Lemma ya_rfcl : forall len, 0 <= len -> 0 <= reac_frame_clean_len_model len <= len.
Proof.
intros len Hl. unfold reac_frame_clean_len_model.
destruct ((54 <=? len) && ((len - 52) mod 36 =? 2)) eqn:E; [|lia].
apply andb_prop in E as [E _]. apply Z.leb_le in E. lia.
Qed.

Ltac ya_after_run :=
  lazymatch goal with HF : frame_of _ _ (ms_mem _) (ms_mem _) |- _ =>
    let M := fresh "M" in pose proof (y_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M;
    clear HF; repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.

Ltac ya_leaf_mem :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msf; cfg_model := _ |} _ =>
  lazymatch goal with HBD : d_body _ _ _ _ _ _ _ _ _ ?m0 |- _ =>
  let MEQ := fresh "MEQ" in
  assert (MEQ : forall x, ms_mem msf x = m0 x)
    by (intros x; repeat match goal with Mx : forall x, ms_mem _ x = _ |- _ => rewrite Mx; clear Mx end; reflexivity)
  end end.

Ltac ya_rg HS HROK RG :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms) =>
  lazymatch type of HROK with regs_ok _ _ ?regs =>
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 26; 27]%bv ->
     getr (ms_regs ms) r = getr regs r)
    by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
        rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS), (HROK r);
        cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr)
  end end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma ya_vm_ext : forall (W : world SEGS) (m m' : word -> option byte) a q v,
  (forall x, m' x = m x) -> val_mem SEGS (rd W m) a q v -> val_mem SEGS (rd W m') a q v.
Proof. intros W m m' a q v HM Hv j Hj. rewrite (y_mbyte_ext SEGS (w_H W) m m' HM). exact (Hv j Hj). Qed.

Lemma ya_frm_ext : forall cx nb fr len (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_frm cx nb fr len W m -> d_frm cx nb fr len W m'.
Proof.
intros cx nb fr len W m m' HM (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
intros j Hj. destruct (F4 j Hj) as (Hv & Hb). split; [exact (ya_vm_ext W m m' _ _ _ HM Hv) | exact Hb].
Qed.

Lemma ya_rec_ext : forall cx nb fr len (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_spREC cx nb fr len W m -> d_spREC cx nb fr len W m'.
Proof.
intros cx nb fr len W m m' HM (V1 & V2 & V3 & V4).
exact (conj (ya_vm_ext W m m' _ _ _ HM V1) (conj (ya_vm_ext W m m' _ _ _ HM V2)
  (conj (ya_vm_ext W m m' _ _ _ HM V3) (ya_vm_ext W m m' _ _ _ HM V4)))).
Qed.

Lemma ya_op_ext : forall cx op (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_spOP cx op W m -> d_spOP cx op W m'.
Proof. intros cx op W m m' HM (V1 & V2). exact (conj (ya_vm_ext W m m' _ _ _ HM V1) (ya_vm_ext W m m' _ _ _ HM V2)). Qed.

Lemma ya_sp0_ext : forall cx i now (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_sp0 cx i now W m -> d_sp0 cx i now W m'.
Proof. intros cx i now W m m' HM (V1 & V2). exact (conj (ya_vm_ext W m m' _ _ _ HM V1) (ya_vm_ext W m m' _ _ _ HM V2)). Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Section g.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.

Lemma ya_keep : forall cx (regs regs' : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 26; 27]%bv -> getr regs' r = getr regs r) ->
  d_rL B cx regs -> d_rL B cx regs'.
Proof. intros cx regs regs' RG HR. unfold d_rL, spZ in *. rewrite !RG by (cbv; tauto). exact HR. Qed.

Lemma ya_land : forall (fq : YK11.FPState) (cx : dcx) (h i n now : Z) (xb : list (Z * Z)) (shf : Z -> Z)
  ly3 S3 (W3 : world SEGS) mem3 md' k acc (E : env) (ss : sstate) (ms : machine_state) (pc : Z)
  (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 (ms_mem ms) md' k ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  (forall x, ms_mem ms x = mem3 x) ->
  d_rL B cx (ms_regs ms) -> R (ms_regs ms) -> X W3 (ms_mem ms) ->
  d_sp0 cx i now W3 mem3 -> d_body B cx h n xb shf ly3 S3 W3 mem3 ->
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx pc h i n now xb shf R X W3 (mkCfg ms md').
Proof.
intros fq cx h i n now xb shf ly3 S3 W3 mem3 md' k acc E ss ms pc R X
  HFQ (HB & HJ & HFR) Hk Hev Hmo Hacc Ri Rn Rnow HS Hrv Hpc MEQ HrL HR HX HSP HBD.
pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFQ|].
split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Ri|]. split; [exact Rn|]. split; [exact Rnow|]. split; [exact HrL|]. split; [exact HR|].
split; [exact HX|]. split; [exact (ya_sp0_ext cx i now W3 mem3 (ms_mem ms) MEQ HSP)|].
exact (y_body_ext B BRT cx h n xb shf ly3 S3 W3 mem3 (ms_mem ms) MEQ HBD).
Qed.

Lemma ya_cls_ok : forall (fq : YK11.FPState) (cx : dcx) (h i n now op nb fr len : Z) ly3 S3 (W : world SEGS) mem3
  md' k acc (E : env) (ss : sstate) (ms : machine_state) (regs : bvmap 5 word),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  (op mod 4 = 0 \/ op mod 4 = 1) -> 0 <= op < 256 -> d_frm cx nb fr len W mem3 -> d_spREC cx nb fr len W mem3 ->
  d_spOP cx op W mem3 -> len <= nb -> nb - len <= Z.max 0 (c_n cx - 7) ->
  d_sp0 cx i now W mem3 -> d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W mem3 ->
  d_rL B cx regs -> getr regs 22 = w64 1 -> getr regs 12 = w64 len ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ss_pc ss = (if op mod 4 =? 0 then CLS_OFF else CLSS_OFF) ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r) ->
  cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W (mkCfg ms md').
Proof.
intros fq cx h i n now op nb fr len ly3 S3 W mem3 md' k acc E ss ms regs
  HFQ Hk Hev Hmo Hacc Ri Rn Rnow Hop Rop HFM HREC HOP Rlen Rnb HSP HBD HR H22 H12 HCX HS Hrv Hpc MEQ RG.
unfold cls_in.
apply (ya_land fq cx h i n now (dxb fr len) dsh_rec ly3 S3 W mem3 md' k acc E ss ms _ (dR_cls cx nb fr len)
  (fun W m => (op mod 4 = 0 \/ op mod 4 = 1) /\ 0 <= op < 256 /\ d_frm cx nb fr len W m /\
     d_spREC cx nb fr len W m /\ d_spOP cx op W m /\ len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7))
  HFQ HCX Hk Hev Hmo Hacc Ri Rn Rnow HS Hrv Hpc MEQ (ya_keep cx regs (ms_regs ms) RG HR)).
- unfold dR_cls. rewrite (RG 22%bv ltac:(cbv; tauto)), (RG 12%bv ltac:(cbv; tauto)). exact (conj H22 H12).
- exact (conj Hop (conj Rop (conj (ya_frm_ext cx nb fr len W mem3 (ms_mem ms) MEQ HFM)
    (conj (ya_rec_ext cx nb fr len W mem3 (ms_mem ms) MEQ HREC) (conj (ya_op_ext cx op W mem3 (ms_mem ms) MEQ HOP)
    (conj Rlen Rnb)))))).
- exact HSP.
- exact HBD.
Qed.

Lemma ya_hobs_ok : forall (fq : YK11.FPState) (cx : dcx) (h i n now op nb fr len : Z) ly3 S3 (W : world SEGS) mem3
  md' k acc (E : env) (ss : sstate) (ms : machine_state) (regs : bvmap 5 word),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  op mod 4 = 2 -> 0 <= op < 256 -> d_frm cx nb fr len W mem3 -> d_spREC cx nb fr len W mem3 ->
  d_spOP cx op W mem3 -> len <= nb -> nb - len <= Z.max 0 (c_n cx - 7) ->
  d_sp0 cx i now W mem3 -> d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W mem3 ->
  d_rL B cx regs -> getr regs 22 = w64 1 -> getr regs 26 = w64 now ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = HOBS_OFF ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r) ->
  getr (ms_regs ms) 11 = w64 (if 11 <? len then fr + 6 else d_obj cx OOUR) ->
  hobs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W (mkCfg ms md').
Proof.
intros fq cx h i n now op nb fr len ly3 S3 W mem3 md' k acc E ss ms regs
  HFQ Hk Hev Hmo Hacc Ri Rn Rnow Hop Rop HFM HREC HOP Rlen Rnb HSP HBD HR H22 H26 HCX HS Hrv Hpc MEQ RG H11.
unfold hobs_in.
apply (ya_land fq cx h i n now (dxb fr len) dsh_rec ly3 S3 W mem3 md' k acc E ss ms _ (dR_hobs cx h nb fr len now)
  (fun W m => op mod 4 = 2 /\ 0 <= op < 256 /\ d_frm cx nb fr len W m /\
     0 <= reac_frame_clean_len_model len <= len /\
     d_spREC cx nb fr len W m /\ d_spOP cx op W m /\ len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7))
  HFQ HCX Hk Hev Hmo Hacc Ri Rn Rnow HS Hrv Hpc MEQ (ya_keep cx regs (ms_regs ms) RG HR)).
- unfold dR_hobs. rewrite (RG 22%bv ltac:(cbv; tauto)), (RG 26%bv ltac:(cbv; tauto)). exact (conj H22 (conj H26 H11)).
- exact (conj Hop (conj Rop (conj (ya_frm_ext cx nb fr len W mem3 (ms_mem ms) MEQ HFM)
    (conj (ya_rfcl len (proj1 (proj1 HFM))) (conj (ya_rec_ext cx nb fr len W mem3 (ms_mem ms) MEQ HREC)
    (conj (ya_op_ext cx op W mem3 (ms_mem ms) MEQ HOP) (conj Rlen Rnb))))))).
- exact HSP.
- exact HBD.
Qed.

Theorem yr_pb_arm : yr_arm_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold yr_arm_stmt. intros cx h i n now op nb fr len W c Hpre.
destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFQ & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  Ri & Rn & Rnow & HR & HRR & HX & HSP & HBD).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof asan_consts as (C1 & _).
pose proof HB as ((HPRE & _ & _ & _ & HINdisj & _) & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (c_regs cx)) with (d_S cx) in Hslo, Hshi.
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTK & HWR).
pose proof HFRM as (E & HE & HRG & HFL & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
pose proof HR as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
pose proof HRR as (H22 & H21 & H26 & H23 & H12 & H24 & H25).
pose proof HX as (Rop & Rop3 & Rfr & HFM & HREC & HOP & Rlen & Rnb).
pose proof HFM as (Rlen0 & _ & _ & _).
pose proof HREC as (_ & _ & V368 & _).
pose proof (y_A_range (d_S cx) ltac:(clear - C1 Hceil Hslo; unfold MFRAME, LLVMF_STK in *; lia)) as HAr.
change (32 * ((d_S cx - MFRAME) / 32)) with (d_A cx) in HAr.
assert (RA : 0 <= d_A cx < 2 ^ 64) by (clear - C1 Hceil Hslo Hshi H47 HAr; unfold MFRAME, LLVMF_STK in *; lia).
destruct (y_geom B LAWS MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k HC) as
  (GS16 & GSlo & GShi & GFB0 & GFBc & GFBapp & GFBimg & GFBmod & GFpres & GSHpres & GWpres & GAR & Gfin & GEFB & GEFL).
assert (RFB : 0 <= d_FB cx < 2 ^ 64) by (clear - GFB0 GFBc C1; lia).
assert (Hdxb : dxb fr len = [(fr, len)])
  by (unfold dxb; replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
assert (Hin : In (fr, len) (ablocks B ly3 S3)).
{ pose proof HBLK as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
  rewrite Hdxb. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len GAR Hin) as (_ & _ & Hfrc & _).
pose proof (req_size_pos len (proj1 Rlen0)) as Hrq.
assert (Rfr64 : 4096 <= fr /\ fr + 6 < 2 ^ 64) by (clear - Rfr Hfrc Hrq C1; lia).
pose proof (y_E_env cx E (ya_vals regs fr) HE) as HEd.
pose proof HEd as (_ & _ & HEI' & _).
set (Ed := d_env cx E (ya_vals regs fr)) in *.
assert (AO : forall q, (q < AT_FL)%nat -> ew Ed q = ew E q) by (intros q Hq; apply y_env_old; exact Hq).
assert (AX : forall j q, q = (AT_X + j)%nat -> Nat.ltb j 22 = true ->
  ew Ed q = nth j (ya_vals regs fr) (Z_to_bv 64 0))
  by (intros j q -> Hj; apply y_env_x; apply Nat.ltb_lt in Hj; cbn [length ya_vals]; exact Hj).
assert (DX : forall j q, q = (AT_X + j)%nat -> Nat.ltb j 22 = true ->
  sv_denot Ed (SOff q 0) = nth j (ya_vals regs fr) (Z_to_bv 64 0))
  by (intros j q Hq Hj; rewrite sv_denot_SOff0; exact (AX j q Hq Hj)).
assert (D60 : sv_denot Ed (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot Ed (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D3 : sv_denot Ed (SOff 3 0) = w64 (as_gp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0).
assert (D4 : sv_denot Ed (SOff 4 0) = w64 (as_tp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 4%nat 4%bv eq_refl); exact Htp0).
assert (D32 : sv_denot Ed (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E32).
assert (D529 : sv_denot Ed (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E529).
assert (A516 : bv_unsigned (ew Ed 516) = d_FB cx)
  by (rewrite (AO 516%nat ltac:(unfold AT_FL; lia)), E516; unfold w64; apply unsigned_lit_small; exact RFB).
assert (HROK : regs_ok Ed ya_sr regs).
{ apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
  repeat (destruct Hz as [<-|Hz];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
      lazymatch goal with
      | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
      | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 | exact H22 ]
      | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
          first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
      | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
      | |- _ = sv_denot _ (SOff 3 0) => rewrite D3; exact Hgp
      | |- _ = sv_denot _ (SOff 4 0) => rewrite D4; exact Htp
      | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
      | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
      | |- _ = sv_denot _ (SOff ?q 0) =>
          let j := eval vm_compute in (q - 531)%nat in
          rewrite (DX j q eq_refl eq_refl); cbn [nth ya_vals]; reflexivity
      end
    | ]).
  destruct Hz. }
assert (HFACTS : facts_ok Ed (d_facts [] []))
  by exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E (ya_vals regs fr) [] [] HC HE I I).
assert (HACS : Forall (YP09.chunk_ok SEGS Ed (rd W mem3) (d_A cx)) ya_acs).
{ unfold ya_acs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ 0); [reflexivity | cbn; lia | lia | exact V136].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ fr);
      [rewrite (DX 21%nat 552%nat eq_refl eq_refl); reflexivity | cbn; clear - Rfr64; lia | lia | exact V368]. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E MID_OFF ya_sr
  (ya_vals regs fr) ya_acs [] [] (d_facts [] []) HC HE HRG HFL HROK HFACTS HACS
  (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ ya_rs HS0 (ya_sub dsh_rec) ltac:(vm_compute; reflexivity)) as HS.
fold Ed in HS.
assert (A23 : ew Ed 544 = Z_to_bv 64 (op mod 4)) by (rewrite (AX 13%nat 544%nat eq_refl eq_refl); exact H23).
assert (A12 : ew Ed 537 = Z_to_bv 64 len) by (rewrite (AX 6%nat 537%nat eq_refl eq_refl); exact H12).
assert (A552 : ew Ed 552 = Z_to_bv 64 fr) by (rewrite (AX 21%nat 552%nat eq_refl eq_refl); reflexivity).
assert (U552 : bv_unsigned (ew Ed 552) = fr) by (rewrite A552; apply unsigned_lit_small; clear - Rfr64; lia).
assert (R23 : 0 <= op mod 4 < 4) by (apply Z.mod_pos_bound; lia).
assert (RL : 0 <= len < 2 ^ 64) by (clear - Rlen0; unfold REC_MAX in Rlen0; lia).
clear HS0 HFACTS HACS HRG HFL HE EE HEI HOBJ HINP HIMG HOFF HGEO HCAN HSTK HWR HSHD HPRE HINdisj.
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + MID_OFF)) with (Z_to_bv 64 (BASE + MID_OFF)).
psrr_branch_pi RUNP BR HS.
- rewrite branch_eq_U, (U_atom Ed 544 (op mod 4) A23 ltac:(clear - R23; lia)), (U_lit Ed 0 ltac:(clear; lia)) in Hc.
  apply Z.eqb_eq in Hc.
  paj_run_to_sh RUNTO HS HJ CLS_OFF; [awr_ok_tac | ya_after_run].
  ya_leaf_mem. ya_rg HS HROK RG.
  apply SRr_ret. left. split; [clear - Hc; lia|].
  lazymatch goal with MEQ : forall x, ms_mem _ x = _ |- _ =>
  apply (ya_cls_ok fq cx h i n now op nb fr len ly3 S3 W mem3 _ k acc _ _ _ regs HFQ Hk Hev Hmo Hacc Ri Rn Rnow
    (or_introl Hc) Rop HFM HREC HOP Rlen Rnb HSP HBD HR H22 H12 (conj HB (conj HJ HFR)) HS eq_refl
    ltac:(rewrite Hc; reflexivity) MEQ RG) end.
- rewrite branch_eq_U, (U_atom Ed 544 (op mod 4) A23 ltac:(clear - R23; lia)), (U_lit Ed 0 ltac:(clear; lia)) in Hc.
  apply Z.eqb_neq in Hc.
  paj_run_to_sh RUNTO HS HJ HOBS_OFF; [awr_ok_tac | ya_after_run].
  psrr_branch_pi RUNP BR HS.
  + rewrite branch_ne_U, (U_atom Ed 544 (op mod 4) A23 ltac:(clear - R23; lia)), (U_lit Ed 2 ltac:(clear; lia)) in Hc0.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
    assert (Hop1 : op mod 4 = 1) by (clear - Hc Hc0 Rop3 R23; lia).
    paj_run_to_sh RUNTO HS HJ CLSS_OFF; [awr_ok_tac | ya_after_run].
    ya_leaf_mem. ya_rg HS HROK RG.
    apply SRr_ret. left. split; [exact Hc0|].
    lazymatch goal with MEQ : forall x, ms_mem _ x = _ |- _ =>
    apply (ya_cls_ok fq cx h i n now op nb fr len ly3 S3 W mem3 _ k acc _ _ _ regs HFQ Hk Hev Hmo Hacc Ri Rn Rnow
      (or_intror Hop1) Rop HFM HREC HOP Rlen Rnb HSP HBD HR H22 H12 (conj HB (conj HJ HFR)) HS eq_refl
      ltac:(rewrite Hop1; reflexivity) MEQ RG) end.
  + rewrite branch_ne_U, (U_atom Ed 544 (op mod 4) A23 ltac:(clear - R23; lia)), (U_lit Ed 2 ltac:(clear; lia)) in Hc0.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_to_sh RUNTO HS HJ HOBS_OFF; [awr_ok_tac | ya_after_run].
    psrr_branch_pi RUNP BR HS.
    * rewrite branch_ltu_U, (U_atom Ed 537 len A12 RL), (U_lit Ed 12 ltac:(clear; lia)) in Hc1.
      apply Z.ltb_lt in Hc1.
      paj_run_to_sh RUNTO HS HJ HOBS_OFF; [awr_ok_tac | ya_after_run].
      ya_leaf_mem. ya_rg HS HROK RG.
      apply SRr_ret. right. split; [exact Hc0|].
      lazymatch goal with MEQ : forall x, ms_mem _ x = _ |- _ =>
      apply (ya_hobs_ok fq cx h i n now op nb fr len ly3 S3 W mem3 _ k acc _ _ _ regs HFQ Hk Hev Hmo Hacc Ri Rn Rnow
        Hc0 Rop HFM HREC HOP Rlen Rnb HSP HBD HR H22 H26 (conj HB (conj HJ HFR)) HS eq_refl eq_refl MEQ RG) end.
      yr_rg HS (11%bv : bv 5) R11. rewrite R11.
      replace (11 <? len) with false by (symmetry; apply Z.ltb_ge; clear - Hc1; lia).
      cbn [sv_denot]. rewrite A516. reflexivity.
    * rewrite branch_ltu_U, (U_atom Ed 537 len A12 RL), (U_lit Ed 12 ltac:(clear; lia)) in Hc1.
      apply Z.ltb_ge in Hc1.
      paj_run_to_sh RUNTO HS HJ HOBS_OFF; [awr_ok_tac | ya_after_run].
      psrr_branch_pi RUNP BR HS.
      -- paj_run_to_sh RUNTO HS HJ HOBS_OFF; [awr_ok_tac | ya_after_run].
         ya_leaf_mem. ya_rg HS HROK RG.
         apply SRr_ret. right. split; [exact Hc0|].
         lazymatch goal with MEQ : forall x, ms_mem _ x = _ |- _ =>
         apply (ya_hobs_ok fq cx h i n now op nb fr len ly3 S3 W mem3 _ k acc _ _ _ regs HFQ Hk Hev Hmo Hacc Ri Rn Rnow
           Hc0 Rop HFM HREC HOP Rlen Rnb HSP HBD HR H22 H26 (conj HB (conj HJ HFR)) HS eq_refl eq_refl MEQ RG) end.
         yr_rg HS (11%bv : bv 5) R11. rewrite R11.
         replace (11 <? len) with true by (symmetry; apply Z.ltb_lt; clear - Hc1; lia).
         cbn [sv_denot]. rewrite U552. reflexivity.
      -- exfalso.
         rewrite branch_geu_U, U_SOff, U552, (zcanon_id (fr + 6) ltac:(unfold M64; clear - Rfr64; lia)),
           (U_lit Ed 7 ltac:(clear; lia)) in Hc2.
         apply Bool.negb_false_iff, Z.ltb_lt in Hc2. clear - Hc2 Rfr64. lia.
Qed.
End g.
End h.
End f.
End d.
