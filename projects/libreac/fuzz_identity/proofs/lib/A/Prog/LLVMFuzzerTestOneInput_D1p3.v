(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its addresses and numbers changed; 308 of its 383 lines of code are new or changed and 1068 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g YK0w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv reac_identity_ingest.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_D1cut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* Segment D1, phase 3 (0x80bf4..0x80c1c): `before`'s shadow (sb zero,4..7(s3); sb s5,8(s3)), then
   s2 := [mf+184] = &id and checked_memcpy(before, id, 38), returning to 0x80c1c.
   It proves no function (kind: segment lemma). *)

(* The state at 0x80bf4: the shadow cells sh+4..8 are written (base s3 = x19); mf+184 holds &id (base s1 = x9,
   read only) and is named by the extra atom 32. *)
Definition p3_sh : YP09.region := YP09.mkRegion (Some 19%nat) 4 9 4 9 [].
Definition p3_mf : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 184 184
  [YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
Definition p3_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition p3_ss : sstate := mkSS 0x4e8 sr_atoms [p3_sh; p3_mf] None p3_facts.
Definition p3_extra (SF : Z) : list word := map (Z_to_bv 64) [SF + V_id].

Lemma d3_garr8_mv : forall segs H H' (m m' : word -> option byte) a b l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (b + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') b l.
Proof.
intros segs H H' m m' a b l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (b + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. replace (b + Z.of_nat j + kk) with (b + (Z.of_nat j + kk)) by lia.
replace (a + Z.of_nat j + kk) with (a + (Z.of_nat j + kk)) by lia. apply Hk. lia.
Qed.
Lemma d3_mod16 : forall mf sp0, mf mod 32 = 0 -> sp0 mod 16 = 0 -> (mf - sp0) mod 16 = 0.
Proof.
intros mf sp0 H1 H2. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia].
apply Z.mod_divide; [lia|]. destruct H1 as [q1 E1]. destruct H2 as [q2 E2]. exists (2 * q1 - q2). lia.
Qed.

Ltac d3_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac d3_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; unfold acallee_saved; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
#[local] Notation NUMS := (d1_nums B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).

Theorem d1_ph3 : d1_ph3_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3 HC HR.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ2 & Hfrs2 & Hk2 & MLE2 & MOK2 & HEC & Hi & _ & _ & _ & HRL).
destruct HRL as (_ & _ & _ & (Bid2 & _ & SHid2) & _ & _ & Hmid & _). unfold mf_id in Hmid.
destruct HR as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfrs3 & Hperm3 & Hhs3 & MLE3 & KEEP3 & HP).
destruct HP as ((R2 & R9 & R8 & R3 & R4 & R19 & R20 & R21 & R24) & R25 & R22 & R27 & R26 & R18 & V144 & Bpl).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
set (k := D1k g i) in *.
assert (Hkr : 0 <= k <= 255) by (apply SlotModel.rec_k_range).
set (sp0 := e_sp0 g) in *.
set (SF := SFa g pos) in *.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
assert (Hsh2 : SHADOW_OFF <= sh /\ sh + 128 <= kHighMemBeg).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (Hmfr : 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47) by (clear - Hmf0 Hmfb H47 C1 Has; lia).
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SF) by (unfold SF, SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hinpl : In (pl, k) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). left. reflexivity. }
pose proof (req_size_pos k ltac:(lia)) as Hrq0.
(* What the run may write: the shadow cells sh+4..8, `before`, and the callees' stack below mf. *)
assert (NB : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + req_size m ->
  0 <= a < 2 ^ 64 /\ ~ (sh + 4 <= a < sh + 9) /\ ~ (SF + 32 <= a < SF + 70) /\ ~ (mf - 4096 <= a < mf)).
{ intros b m a Hb Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR3 Hb) as (_ & Hb4096 & Hbce & Hbapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b m 4 pos HAR3 Hb Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa3, HFB in Hdf.
  split; [clear - Ha Hb4096 Hbce C1; lia|].
  split; [intros Hs; apply (fshadow_not_app SF 128 b (req_size m) a); [exact HSF0 | clear - HSF1 C1; lia | exact Hbapp
    | rewrite Esh in Hs; unfold SHADOW_OFF in Hs; clear - Hs; lia | exact Ha]|].
  split; [clear - Ha Hdf; lia|]. clear - Ha Hbce Hmf0 Has; lia. }
assert (NF : forall a, SF <= a < SF + 1024 ->
  0 <= a < 2 ^ 64 /\ ~ (sh + 4 <= a < sh + 9) /\ ~ (mf - 4096 <= a < mf)).
{ intros a Ha. split; [clear - Ha HSF0 HSF1 C1; lia|].
  split; [intros Hs; apply (fshadow_not_app SF 128 SF 1024 a); [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | rewrite Esh in Hs; unfold SHADOW_OFF in Hs; clear - Hs; lia | exact Ha]|].
  clear - Ha HSF1 Hmf0 Has; lia. }
assert (NS : forall a, sh <= a < sh + 128 ->
  0 <= a < 2 ^ 64 /\ ~ (SF + 32 <= a < SF + 70) /\ ~ (mf - 4096 <= a < mf)).
{ intros a Ha. split; [clear - Ha Hsh1 C1; lia|].
  split; [intros Hf; apply (fshadow_not_app SF 128 SF 1024 a); [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia | clear - Hf; lia]|].
  clear - Ha Hsh1 Hmf0 Has; lia. }
(* Not in WR0: kept from the segment's start. *)
assert (NW : forall a, ~ WR1 g pos mf a -> ~ WR0 g pos mf a) by (intros a H H0; apply H; left; exact H0).
assert (KST : forall a, mf + 168 <= a < sp0 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KEEP3.
  - clear - Ha Hmf0 Hmfb H47 C1 Has. lia.
  - left. clear - Ha Hmf0 Hmfb Has. lia.
  - apply NW. apply (d1_nwr_stack g pos mf a Hmf0 HSF0 HSF1); clear - Ha; lia. }
assert (KID : forall a, SF + V_id <= a < SF + V_id + N_id -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KEEP3.
  - clear - Ha HSF0 HSF1 C1. unfold V_id, N_id in Ha. lia.
  - right; left. unfold V_id, N_id in Ha. clear - Ha. lia.
  - unfold WR0. change (SFa g pos) with SF. unfold V_id, N_id in Ha.
    intros [H|[H|[H|[H|[H|H]]]]];
      [ clear - H Ha Hmf0 HSF1 Has; lia | clear - H Ha Hmf0 HSF1 Has; lia
      | unfold V_before, N_before in H; clear - H Ha; lia | unfold V_again, N_again in H; clear - H Ha; lia | | ];
      (apply (fshadow_not_app SF 128 SF 1024 a HSF0 ltac:(clear - HSF1 C1; lia) HSFapp);
       [unfold shadow_addr, SHADOW_OFF in H |- *; clear - H; lia | clear - Ha; lia]). }
assert (KIDS : forall a, sh + 44 <= a < sh + 49 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KEEP3.
  - clear - Ha Hsh1 C1. lia.
  - right; right. clear - Ha. lia.
  - apply NW. apply (d1_nwr_fshadow g pos mf a Hmf0 HSF0 HSF1 HSFapp);
      change (shadow_addr (SFa g pos)) with sh; clear - Ha; lia. }
assert (V184 : val_mem SEGS (rd W3 mem3) (mf + 184) 8 (SF + V_id)).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (mf + 184) (mf + 184) 8 _); [|exact Hmid].
  intros kk Hkk. apply KST. clear - Hkk Hmfb. lia. }
assert (Bid3 : bytes_at8 W3 mem3 (SF + V_id) (m_id g i)).
{ apply (d1_bytes_moved W2 W3 mem2 mem3 _ _); [|exact Bid2].
  intros kk Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  unfold RcIdentModel.ID_SIZE in Hkk. apply KID. unfold N_id. clear - Hkk. lia. }
assert (SHid3 : sh_blk W3 mem3 (SF + V_id) N_id).
{ apply (d1_shblk_moved W2 W3 mem2 mem3 _ _); [|exact SHid2].
  intros kk Hkk. unfold N_id in Hkk.
  replace (shadow_addr (SF + V_id) + kk) with (sh + (44 + kk)) by (unfold shadow_addr, V_id; rewrite Esh;
    clear - Hkk; lia).
  apply KIDS. clear - Hkk. lia. }
remember (Eimg (Ereg regs3 (p3_extra SF))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (ER : regs_ok E sr_atoms regs3) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn'; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn').
assert (E32 : ew E 32 = Z_to_bv 64 (SF + V_id)).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs3 (p3_extra SF) 0%nat). }
clear HE.
assert (UA : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v)
  by (intros n v Hn' Hv; rewrite Hn'; apply unsigned_lit_small; exact Hv).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (apply UA; [rewrite (EE 9%nat 9%bv eq_refl); exact R9 | clear - Hmfr; lia]).
assert (U2 : bv_unsigned (ew E 2) = mf)
  by (apply UA; [rewrite (EE 2%nat 2%bv eq_refl); exact R2 | clear - Hmfr; lia]).
assert (U19 : bv_unsigned (ew E 19) = sh)
  by (apply UA; [rewrite (EE 19%nat 19%bv eq_refl); exact R19 | clear - Hsh1 C1; lia]).
assert (HS0 : st_ok_pi SEGS VAL E p3_ss
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x4e8)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold p3_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, p3_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      refine (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly3 S3 W3 mem3 md3 (4 * Z.of_nat i + 1) (sh + o) HJ3 _)).
      right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
      unfold in_zr; cbn [fst snd]. rewrite EFa3, HFB. fold sh. clear - Ho; lia.
    + unfold region_ok, p3_mf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmfr; lia|]. split; [clear - Hmfr; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 32 0) (SF + V_id));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold V_id; clear - HSF0 HSF1 C1; lia | lia | exact V184].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, p3_sh, p3_mf. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19, U9. clear - Hsh1 Hmf0 Has. first [left; lia | right; lia].
  - unfold facts_ok, p3_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite U2, U9.
    change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    clear - Hmfr Hmf32. repeat match goal with |- _ /\ _ => split end; try lia; try exact I. }
unfold cfg_at. change (w64 (BASE + 0x4e8)) with (Z_to_bv 64 (BASE + 0x4e8)).
paj_run_shc RUNP RUNC HS0 HJ3.
{ change (ss_mem p3_ss) with [p3_sh; p3_mf].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat sh); [reflexivity | exact U19 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi p3_sh] in Ha. right; right; right. exists 4, pos.
    split; [left; reflexivity|]. right. unfold in_zr; cbn [fst snd]. rewrite EFa3, HFB. fold sh. clear - Ha; lia. }
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
    [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo p3_mf]; clear - Hmfb HSTK' Has; lia
    | cbn [YP09.r_whi p3_mf]; clear - Hmfb; lia |].
  apply awr_ok_nil. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 4 <= a < sh + 9) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H0.
  apply (kept_of_frame E (ss_mem p3_ss) (w_H W3) mem3 (ms_mem ms)
    (fun x => sh + 4 <= x < sh + 9 \/ mf + 184 <= x < mf + 184) HFr);
    [| exact Ha | intros [H|H]; [exact (H0 H) | clear - H; lia]].
  intros bb wlo whi aa Hin Hr. unfold p3_ss, p3_sh, p3_mf, windows in Hin. cbn in Hin. cbv beta.
  repeat (destruct Hin as [Eq | Hin];
    [injection Eq as <- <- <-; cbn [base_val] in Hr; first [rewrite U19 in Hr | rewrite U9 in Hr]; clear - Hr; lia|]);
  destruct Hin. }
clear HF HFr HG.
prreg HS0 (10%bv : bv 5) Q10. prreg HS0 (11%bv : bv 5) Q11. prreg HS0 (12%bv : bv 5) Q12. prreg HS0 (1%bv : bv 5) Q1.
prreg HS0 (2%bv : bv 5) Q2. prreg HS0 (3%bv : bv 5) Q3. prreg HS0 (4%bv : bv 5) Q4. prreg HS0 (8%bv : bv 5) Q8.
prreg HS0 (9%bv : bv 5) Q9. prreg HS0 (18%bv : bv 5) Q18. prreg HS0 (19%bv : bv 5) Q19. prreg HS0 (20%bv : bv 5) Q20.
prreg HS0 (21%bv : bv 5) Q21. prreg HS0 (22%bv : bv 5) Q22. prreg HS0 (24%bv : bv 5) Q24. prreg HS0 (25%bv : bv 5) Q25.
prreg HS0 (26%bv : bv 5) Q26. prreg HS0 (27%bv : bv 5) Q27.
rewrite (EE 24%nat 24%bv eq_refl), R24 in Q10, Q24. rewrite E32 in Q11, Q18.
rewrite (EE 2%nat 2%bv eq_refl), R2 in Q2. rewrite (EE 3%nat 3%bv eq_refl), R3 in Q3.
rewrite (EE 4%nat 4%bv eq_refl), R4 in Q4. rewrite (EE 8%nat 8%bv eq_refl), R8 in Q8.
rewrite (EE 9%nat 9%bv eq_refl), R9 in Q9. rewrite (EE 19%nat 19%bv eq_refl), R19 in Q19.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Q20. rewrite (EE 21%nat 21%bv eq_refl), R21 in Q21.
rewrite (EE 22%nat 22%bv eq_refl), R22 in Q22. rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25.
rewrite (EE 26%nat 26%bv eq_refl), R26 in Q26. rewrite (EE 27%nat 27%bv eq_refl), R27 in Q27.
pose proof (st_ok_region_nth (segs := SEGS) E _ _ 0 _ HS0 eq_refl) as RG0.
destruct RG0 as (_ & _ & _ & CH0).
cbn [ms_mem restrict YP09.r_base YP09.r_chunks base_val] in CH0.
rewrite U19 in CH0. rewrite Forall_forall in CH0.
assert (A0 : forall j, 4 <= j < 8 -> aview SEGS (w_H W3) (ms_mem ms) (sh + j) = Some 0).
{ intros j Hj. apply (aview_of_val_mem1 SEGS); [|lia].
  assert (Hc : j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]];
  match goal with |- val_mem _ _ (sh + ?o) _ _ =>
    exact (val_of_chunk_ok SEGS E _ sh o 1 (SLit 0) 0 (CH0 (YP09.mkChunk o (CVal 1 (SLit 0))) ltac:(d3_in))
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) end. }
assert (A8 : aview SEGS (w_H W3) (ms_mem ms) (sh + 8) = Some 6).
{ apply (aview_of_val_mem1 SEGS); [|lia].
  apply (val_of_chunk_ok SEGS E _ sh 8 1 (SOff 21 0) 6 (CH0 (YP09.mkChunk 8 (CVal 1 (SOff 21 0))) ltac:(d3_in))); [|cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite (EE 21%nat 21%bv eq_refl), R21. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
clear CH0.
assert (SHbeB : sh_blk W3 (ms_mem ms) (SF + V_before) N_before).
{ unfold sh_blk, block_shadow, V_before, N_before. split; [clear - HSF64; lia|]. split; [lia|].
  intros ii Hii. unfold shadow_of_addr.
  replace (SHADOW_OFF + (SF + 32) / 8 + ii) with (sh + (4 + ii)) by (rewrite Esh; clear - Hii HSF64; lia).
  assert (Hc : ii = 0 \/ ii = 1 \/ ii = 2 \/ ii = 3 \/ ii = 4) by (clear - Hii; lia).
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]];
  [ rewrite (A0 (4 + 0)) by lia | rewrite (A0 (4 + 1)) by lia | rewrite (A0 (4 + 2)) by lia
  | rewrite (A0 (4 + 3)) by lia | replace (4 + 4) with 8 by lia; rewrite A8 ]; reflexivity. }
assert (SHidB : sh_blk W3 (ms_mem ms) (SF + V_id) N_id).
{ apply (d1_shblk_moved W3 W3 mem3 (ms_mem ms) _ _); [|exact SHid3].
  intros kk Hkk. unfold N_id in Hkk.
  replace (shadow_addr (SF + V_id) + kk) with (sh + (44 + kk)) by (unfold shadow_addr, V_id; rewrite Esh;
    clear - Hkk HSF64; lia).
  apply KB; [clear - Hkk Hsh1 C1; lia | clear - Hkk; lia]. }
assert (BidB : bytes_at8 W3 (ms_mem ms) (SF + V_id) (m_id g i)).
{ apply (d1_bytes_moved W3 W3 mem3 (ms_mem ms) _ _); [|exact Bid3].
  intros kk Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  unfold RcIdentModel.ID_SIZE, V_id in *.
  destruct (NF (SF + 352 + kk) ltac:(clear - Hkk; lia)) as (H0 & H1 & _).
  apply KB; [exact H0 | exact H1]. }
assert (Usp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Q2; apply unsigned_lit_small; clear - Hmfr; lia).
pmkst HS0.
pose proof HJ3 as (HAR4 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR4 Hin4) as (_ & _ & HFpres & _).
rewrite EFa3, HFB in HFpres.
eapply SRr_mono.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA IS___asan_memcpy) AMEMCPY W3 (ms_regs ms) (ms_mem ms)
    LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 _ (4 * Z.of_nat i + 1)
    (SF + V_before) (SF + V_id) 38 (mf - sp0) (Z_to_bv 64 (BASE + 1296)) HJ3 Q10 Q11 Q12).
  - lia.
  - unfold V_before. clear - HSF0. lia.
  - unfold V_before. clear - HSF1 C1. lia.
  - rewrite Usp. clear. lia.
  - exact (d3_mod16 mf sp0 Hmf32 Hsp0al).
  - clear - Hmfb. lia.
  - rewrite Hes. clear - HSTKm Hmfb Has. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. unfold V_before in Ha. split.
    + right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite EFa3, HFB. clear - Ha. lia.
    + rewrite Hes. clear - Ha HSF1 Hmf0 Has. lia.
  - apply (amem_range_sub_app SF 1024 (SF + V_before) 38); [exact HSFapp | exact HSF1 | unfold V_before; lia
    | unfold V_before; lia | lia].
  - apply (block_shadow_range _ SHADOW_OFF (SF + V_before) N_before (SF + V_before) 38 SHbeB); unfold N_before; lia.
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ 4 pos); [exact HAR4 | exact Hin4
    | rewrite EFa3; unfold V_before; lia | rewrite EFa3, HFB; unfold V_before; lia | lia].
  - split; [unfold V_id; clear - HSF0; lia|]. split; [unfold V_id; clear - HSF1 C1; lia|].
    split.
    { intros a Ha. unfold V_id in Ha. split.
      - apply (aview_some_of_apresent SEGS). apply (proj1 (HFpres a ltac:(clear - Ha; lia))).
      - rewrite Usp, Hes. clear - Ha HSF1 Hmf0 Has. lia. }
    split; [unfold V_id, V_before; lia|].
    split; [apply (amem_range_sub_app SF 1024 (SF + V_id) 38); [exact HSFapp | exact HSF1 | unfold V_id; lia
      | unfold V_id; lia | lia]|].
    split; [apply (block_shadow_range _ SHADOW_OFF (SF + V_id) N_id (SF + V_id) 38 SHidB);
      unfold N_id; lia|].
    intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ 4 pos); [exact HAR4 | exact Hin4
      | rewrite EFa3; unfold V_id; lia | rewrite EFa3, HFB; unfold V_id; lia | lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & _ & Heff & Hfr4 & _ & _).
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (SF + 32 <= a < SF + 70) -> ~ (mf - 4096 <= a < mf) ->
  aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) (ms_mem ms) a).
{ intros a Ha H1 H2. apply Hfr4; [exact Ha | unfold V_before; clear - H1; lia | rewrite Hes; clear - H2; lia]. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 4 <= a < sh + 9) -> ~ (SF + 32 <= a < SF + 70) ->
  ~ (mf - 4096 <= a < mf) -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H0 H1 H2. rewrite (KC a Ha H1 H2). exact (KB a Ha H0). }
unfold D1S. exists ly3, S3, regs4, mem4, md4.
split; [reflexivity|].
split; [exact HJ4|].
split; [exact Hfrs3|].
split; [exact Hperm3|].
split; [exact Hhs3|].
split; [exact MLE3|].
split.
{ intros a Ha Hz Hw. rewrite KM; [exact (KEEP3 a Ha Hz Hw) | exact Ha | | |];
  unfold WR0 in Hw; change (SFa g pos) with SF in Hw; change (shadow_addr SF) with sh in Hw;
  unfold V_before, N_before, V_again, N_again in Hw.
  - intros H. apply Hw. right. right. right. right. left. exact H.
  - intros H. apply Hw. right. right. left. clear - H. lia.
  - intros H. apply Hw. left. rewrite Has. clear - H. lia. }
unfold P3, RC. change (SFa g pos) with SF. change (shadow_addr SF) with sh.
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs4 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (d1_presv (ms_regs ms) regs4 r HP4 Hr)).
split.
{ split; [rewrite PR by d3_cs; exact Q2|]. split; [rewrite PR by d3_cs; exact Q9|].
  split; [rewrite PR by d3_cs; exact Q8|]. split; [rewrite PR by d3_cs; exact Q3|].
  split; [rewrite PR by d3_cs; exact Q4|]. split; [rewrite PR by d3_cs; exact Q19|].
  split; [rewrite PR by d3_cs; exact Q20|]. split; [rewrite PR by d3_cs; exact Q21|].
  rewrite PR by d3_cs; exact Q24. }
split; [rewrite PR by d3_cs; exact Q25|].
split; [rewrite PR by d3_cs; exact Q22|].
split; [rewrite PR by d3_cs; exact Q27|].
split; [rewrite PR by d3_cs; exact Q26|].
split; [rewrite PR by d3_cs; exact Q18|].
split.
{ apply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 mem4 (mf + 144) (mf + 144) 8 _); [|exact V144].
  intros kk Hkk. apply KM; clear - Hkk Hmfr Hsh1 HSF0 HSF1 Hmf0 Has C1; lia. }
split.
{ apply (d1_bytes_moved W3 W3 mem3 mem4 _ _); [|exact Bpl].
  intros kk Hkk. rewrite SlotModel.rec_pl_length in Hkk. change (SlotModel.rec_k (e_pl g) i) with k in Hkk.
  destruct (NB pl k (pl + kk) Hinpl ltac:(clear - Hkk Hrq0 Hkr; lia)) as (H0 & H1 & H2 & H3).
  apply KM; assumption. }
split.
{ apply (d1_shblk_moved W3 W3 (ms_mem ms) mem4 _ _); [|exact SHbeB].
  intros kk Hkk. unfold N_before in Hkk.
  replace (shadow_addr (SF + V_before) + kk) with (sh + (4 + kk)) by (unfold shadow_addr, V_before; rewrite Esh;
    clear - Hkk HSF64; lia).
  destruct (NS (sh + (4 + kk)) ltac:(clear - Hkk; lia)) as (H0 & H1 & H2).
  apply KC; [exact H0 | exact H1 | exact H2]. }
unfold bytes_at8 in *.
apply (d3_garr8_mv SEGS (w_H W3) (w_H W3) (ms_mem ms) mem4 (SF + V_id) (SF + V_before) _); [|exact BidB].
intros kk Hkk. rewrite length_map in Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
unfold RcIdentModel.ID_SIZE in Hkk. exact (Heff kk ltac:(clear - Hkk; lia)).
Qed.

End c.
End b.
End a.
