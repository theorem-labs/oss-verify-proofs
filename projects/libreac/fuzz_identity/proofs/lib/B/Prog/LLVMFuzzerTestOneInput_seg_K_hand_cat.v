(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8w.v:289-290, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* seg_K piece `cat` of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): +0x1ad8 .. +0x1ae8 of the entry
   (fuzz_identity.asan-ubsan 0x8224c .. 0x8225c), the n_r = 0 path. 0x8224c stores a zero byte at s7 + 90 (s7 =
   shadow_addr SF: the shadow cell of `count` at SF+720, its scope unpoison); 0x82250 stores the zero word at s2
   (= SF + 720, count := 0); 0x82254 copies s2 to a0; 0x82258 calls reac_box_catalogue, which writes the box count
   11 through a0 and returns BOX_CATALOGUE. The three slots before the call run on the plain engine (paj_run_shc,
   no checked access) with two writable regions in the entry's own frame (4, pos): count's shadow cell (base s7)
   and count (base s2). The call goes through the callee's caller-journal contract reac_box_catalogue.tcat_spec
   (base k_hcat), with cat_pR_ok's left disjunct: count lies in the frame (4, pos) and its shadow cell holds the
   0 the store at 0x8224c wrote. kkeep is rebuilt from the incoming kkeep, what the run kept (only the two written
   ranges change) and the callee's tcj_kept (its stack window and [pR, pR + 8)). The call's event bound
   `st_nev S2 + EV_CAT <= EV_MAX` uses the contract's HEV, added as a Section hypothesis after HPRE. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_K_hand_stmt LLVMFuzzerTestOneInput_seg_K_base.
Import ListNotations. Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number". Open Scope bv_scope. Open Scope Z_scope.

(* The symbolic state at +0x1ad8. Region 0: count's shadow byte, base s7 (atom 23 = shadow_addr SF), the cell
   at offset 90 written by 0x8224c. Region 1: count itself, base s2 (atom 18 = SF + 720), the 8 bytes written by
   0x82250. No load and no branch: the run ends at the jal of 0x82258 (PRS_call IB_reac_box_catalogue). *)
Definition kc_rsh : YP09.region := YP09.mkRegion (Some 23%nat) 90 91 90 91 [].
Definition kc_rcnt : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 8 [].
Definition kc_ss : sstate := mkSS 0x1ad8 sr_atoms [kc_rsh; kc_rcnt] None (mkFacts [] [] []).

Lemma kcat_m16 : forall a, a mod 32 = 0 -> a mod 16 = 0.
Proof.
intros a Ha. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide; [lia|]. destruct Ha as [p ->]. exists (2 * p). ring.
Qed.
Lemma kcat_m8 : forall a, a mod 64 = 0 -> (a + 720) mod 8 = 0.
Proof.
intros a Ha. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide; [lia|]. destruct Ha as [p ->].
exists (8 * p + 90). ring.
Qed.
Lemma kcat_sh90 : forall a, SHADOW_OFF + (a + 720) / 8 = SHADOW_OFF + a / 8 + 90.
Proof.
intros a. replace (a + 720) with (90 * 8 + a) by ring. rewrite Z.div_add_l by lia. ring.
Qed.
Lemma kcat_pres : forall (r : bv 5) regs regs', aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof.
intros r regs regs' HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
(* The callee-saved side condition, with the register literal computed. *)
Ltac kcat_cs :=
unfold acallee_saved;
match goal with
| |- context [bv_unsigned ?x] =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v
end; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Section b. Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms. Variable MT : ameter_ops. Variables XM_LIB XN_LIB : Z -> Z. Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type. Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
Hypothesis HPRE : KPRE B RLO RHI LLVMF_STK arodata_okS G.
(* The contract's HEV (lib/B/Prog/LLVMFuzzerTestOneInput.v:114): reac_box_catalogue's event bound at the call. *)
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Let LAWS := k_laws B RLO RHI LLVMF_STK arodata_okS G HPRE.
Let RUN := paj_run B LAWS.  Let RUNTO := paj_run_to B LAWS.  Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.  Let RUNC := SRr_run_pi_AJ_call B LAWS.  Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

Lemma k_cat : k_cat_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G.
Proof.
unfold k_cat_stmt.
intros _ g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC R18 HK.
destruct HKC as (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh).
pose proof (k_geom B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
  arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & Hin4).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof (k_psig B RLO RHI LLVMF_STK arodata_okS G HPRE) as PSIG.
(* the event bound at the call: the journal, KH's 4 * nrec + 7 <= EV_LLVMF, HEV and the entry's pre *)
assert (HNEV : st_nev S2 + reac_box_catalogue.EV_CAT <= EV_MAX).
{ pose proof HKH as (_ & _ & HKk & _ & _ & HEC & _).
  destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HPREe & _).
  unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPREe.
  destruct HPREe as (_ & _ & _ & _ & _ & _ & _ & _ & Hnev0 & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
  unfold reac_box_catalogue.EV_CAT. clear - Hnev0 Hnev2 HKk HEV. lia. }
(* the entry frame and its own shadow do not meet *)
assert (Esh : shadow_addr (SFa g pos) = 2147450880 + SFa g pos / 8) by reflexivity.
assert (HSFsh : shadow_addr (SFa g pos) + 128 <= SFa g pos \/ SFa g pos + 1024 <= shadow_addr (SFa g pos)).
{ destruct (Z.le_gt_cases (shadow_addr (SFa g pos) + 128) (SFa g pos)) as [H1|H1]; [left; exact H1|].
  destruct (Z.le_gt_cases (SFa g pos + 1024) (shadow_addr (SFa g pos))) as [H2|H2]; [right; exact H2|].
  exfalso.
  apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 (Z.max (shadow_addr (SFa g pos)) (SFa g pos)));
  [ exact G8 | clear - G9 C1; lia | exact G10
  | rewrite <- Esh; clear - H1 H2; lia | clear - H1 H2; lia ]. }
assert (Esh90 : shadow_addr (SFa g pos + V_cnt) = shadow_addr (SFa g pos) + 90).
{ change (shadow_addr (SFa g pos + V_cnt)) with (SHADOW_OFF + (SFa g pos + 720) / 8).
  rewrite G13. apply kcat_sh90. }
(* the two written ranges: count's shadow cell and count, both in the entry's own frame (4, pos) *)
assert (WSH : forall a, shadow_addr (SFa g pos) + 90 <= a < shadow_addr (SFa g pos) + 91 ->
  awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
{ intros a Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite G12. change (fs_frame_bytes 4 / 8) with 128. clear - Ha. lia. }
assert (WCNT : forall a, SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8 ->
  awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
{ intros a Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite G12. change (fs_frame_bytes 4) with 1024. unfold V_cnt in Ha. clear - Ha. lia. }
(* the environment *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U23 : bv_unsigned (ew E 23) = shadow_addr (SFa g pos)).
{ rewrite (EE 23%nat 23%bv eq_refl), Rsh. unfold w64. apply unsigned_lit_small. clear - G14 G15 C1. lia. }
assert (U18 : bv_unsigned (ew E 18) = SFa g pos + V_cnt).
{ rewrite (EE 18%nat 18%bv eq_refl), R18. unfold w64. apply unsigned_lit_small. unfold V_cnt. clear - G8 G9 C1. lia. }
(* the symbolic state at +0x1ad8 *)
assert (HS : st_ok_pi SEGS VAL E kc_ss
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x1ad8)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kc_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold kc_rsh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U23. split; [clear - G14; lia|]. split; [clear - G15 C1; lia|].
      split; [|constructor]. intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
        (WSH (shadow_addr (SFa g pos) + o) ltac:(clear - Ho; lia)))).
    + unfold kc_rcnt, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U18. split; [unfold V_cnt; clear - G8; lia|]. split; [unfold V_cnt; clear - G9 C1; lia|].
      split; [|constructor]. intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
        (WCNT (SFa g pos + V_cnt + o) ltac:(clear - Ho; lia)))).
  - cbn [pairwise_disjoint all_disjoint]. unfold kc_rsh, kc_rcnt, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U23, U18.
    repeat match goal with |- _ /\ _ => split end; try exact I.
    unfold V_cnt. clear - HSFsh. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x1ad8)) with (Z_to_bv 64 (BASE + 0x1ad8)).
(* ---- the run: 0x8224c sb zero,90(s7); 0x82250 sd zero,0(s2); 0x82254 mv a0,s2; 0x82258 jal ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold kc_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold kc_rsh, kc_rcnt in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - rewrite U23 in Ha. exact (WSH a Ha).
  - rewrite U18, Z.add_0_r in Ha. exact (WCNT a Ha). }
(* what the run kept: every byte outside the two written ranges *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (shadow_addr (SFa g pos) + 90 <= a < shadow_addr (SFa g pos) + 91) ->
  ~ (SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem a).
{ intros a Ha Hw1 Hw2.
  apply (kept_of_frame E _ (w_H W2) mem (ms_mem ms)
    (fun x => (shadow_addr (SFa g pos) + 90 <= x < shadow_addr (SFa g pos) + 91) \/
              (SFa g pos + V_cnt <= x < SFa g pos + V_cnt + 8)) HFr);
  [| exact Ha | intros [Hx | Hx]; [exact (Hw1 Hx) | exact (Hw2 Hx)]].
  intros bb wlo whi aa Hin Hr. unfold kc_ss, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-;
  cbn [base_val] in Hr; rewrite ?U23, ?U18 in Hr.
  - left. clear - Hr. lia.
  - right. clear - Hr. lia. }
(* count's shadow cell after the store at 0x8224c: 0 *)
assert (HR0 : region_ok SEGS E (ms_mem (restrict (w_H W2) ms))
  (YP09.mkRegion (Some 23%nat) 90 91 90 91 [YP09.mkChunk 90 (CVal 1 (SLit 0))])).
{ exact (st_ok_region_nth (segs := SEGS) E _ _ 0%nat _ HS eq_refl). }
pose proof (field_of_region_any E _ 23%nat _ _ 90 91 90 91 90 1%N (SLit 0) HR0 U23 (or_introl eq_refl)
  ltac:(lia)) as V0.
cbn [ms_mem restrict] in V0.
assert (SH0 : aview SEGS (w_H W2) (ms_mem ms) (shadow_addr (SFa g pos + V_cnt)) = Some 0).
{ rewrite Esh90. unfold aview. pose proof (V0 0%nat ltac:(lia)) as V. cbn [Z.of_nat] in V.
  rewrite Z.add_0_r in V. rewrite V. vm_compute. reflexivity. }
clear HF HFr HG HR0 V0.
(* the registers at the call *)
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10. prreg HS (18%bv : bv 5) R18c.
prreg HS (21%bv : bv 5) R21. prreg HS (23%bv : bv 5) R23.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in R2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in R3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in R4. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in R8.
rewrite (EE 9%nat 9%bv eq_refl), Rs1 in R9. rewrite (EE 18%nat 18%bv eq_refl), R18 in R10, R18c.
rewrite (EE 21%nat 21%bv eq_refl), Rtk in R21. rewrite (EE 23%nat 23%bv eq_refl), Rsh in R23.
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. clear - G1 G2 G3 C1. lia. }
(* ---- reac_box_catalogue (&count) at 0x82258, through its caller-journal contract ---- *)
pmkst HS. rewrite (PSIG IB_reac_box_catalogue AF_reac_box_catalogue eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q' =>
  change (SRr SEGS W2 (cfg_at SEGS (BASE + AF_reac_box_catalogue) rg mm mdx) Q') end.
eapply SRr_bind.
{ apply (k_hcat B RLO RHI LLVMF_STK arodata_okS G HPRE LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g)
    (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat (m_nrec g) + 7) (ms_regs ms) (SFa g pos + V_cnt) HJ).
  - exact (proj1 (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
      ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) _ HJ)).
  - rewrite R1. apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - unfold raZ. rewrite R1. rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
  - exact R3.
  - exact R4.
  - exact R10.
  - rewrite Usp. apply kcat_m16. exact G6.
  - rewrite Usp. unfold reac_box_catalogue.CAT_STK, ESTACK. clear - G7. lia.
  - rewrite Usp. clear - G2. lia.
  - apply kcat_m8. exact G11.
  - right. rewrite Usp. unfold reac_box_catalogue.CAT_STK, ESTACK, V_cnt. clear - G1 G9. lia.
  - intros a Ha.
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (WCNT a Ha)) as [Hp Ho].
    split; [exact (WCNT a Ha)|]. split; [exact Hp|]. split; [exact Ho|].
    rewrite Usp. unfold ESTACK, V_cnt in *. clear - Ha G1 G9. lia.
  - unfold reac_box_catalogue.cat_pR_ok. left. exists 4, pos. split; [exact Hin4|].
    split; [|exact SH0].
    intros a Ha. unfold in_zr, frame_rng. cbn [fst snd]. rewrite G12. change (fs_frame_bytes 4) with 1024.
    unfold V_cnt in Ha. clear - Ha. lia.
  - exact HNEV. }
cbv beta. intros W3 c3 _ Hpost. unfold reac_box_catalogue.tcat_post in Hpost.
destruct Hpost as (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Q10 & V3 & HTCJ).
rewrite R1.
change (SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ae8) regs3 mem3 md3) Q).
rewrite Usp in HTCJ. destruct HTCJ as (T1 & T2 & T3 & T4 & T5 & T6).
destruct HKP as (K1 & K2 & K3).
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (kcat_pres r _ _ HP3 Hr)).
replace (4 * Z.of_nat (m_nrec g) + 7 + reac_box_catalogue.EV_CAT) with (4 * Z.of_nat (m_nrec g) + 7) in HJ3
  by (unfold reac_box_catalogue.EV_CAT; ring).
apply HK.
- unfold KC. split; [exact HJ3|].
  split.
  { unfold kkeep. split; [|split].
    - intros a Ha Hw.
      assert (A1 : ~ (mf - reac_box_catalogue.CAT_STK <= a < mf))
        by (unfold reac_box_catalogue.CAT_STK, ESTACK in *; clear - Hw; lia).
      assert (A2 : ~ (SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8)) by (unfold V_cnt; clear - Ha G9; lia).
      assert (A3 : ~ (shadow_addr (SFa g pos) + 90 <= a < shadow_addr (SFa g pos) + 91)) by (clear - Ha G15; lia).
      rewrite (T1 a Ha A1 A2). rewrite (KEEP1 a ltac:(clear - Ha C1; lia) A3 A2). exact (K1 a Ha Hw).
    - intros b n i Hin Hi.
      destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms) _ b n (proj1 HJ) Hin) as (_ & Hb4096 & Hbce & _).
      assert (B1 : ~ (SFa g pos + V_cnt <= b + i < SFa g pos + V_cnt + 8)).
      { intros Hx. apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 (ms_mem ms) _ b n i 4 pos (proj1 HJ) Hin Hin4 Hi).
        left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite G12. change (fs_frame_bytes 4) with 1024.
        unfold V_cnt in Hx. clear - Hx. lia. }
      assert (B2 : ~ (shadow_addr (SFa g pos) + 90 <= b + i < shadow_addr (SFa g pos) + 91)).
      { intros Hx. apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 (ms_mem ms) _ b n i 4 pos (proj1 HJ) Hin Hin4 Hi).
        right. unfold in_zr. cbn [fst snd]. rewrite G12. change (fs_frame_bytes 4 / 8) with 128.
        clear - Hx. lia. }
      rewrite (T2 b n i Hin Hi B1). rewrite (KEEP1 (b + i) ltac:(clear - Hi Hb4096 Hbce C1; lia) B2 B1).
      exact (K2 b n i Hin Hi).
    - intros a Hr Hc Hs.
      assert (Ha : 0 <= a < 2 ^ 64).
      { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; rewrite G12 in Hr;
        [change (fs_frame_bytes 4) with 1024 in Hr | change (fs_frame_bytes 4 / 8) with 128 in Hr];
        clear - Hr G8 G9 G14 G15 C1; lia. }
      assert (A3 : ~ (shadow_addr (SFa g pos) + 90 <= a < shadow_addr (SFa g pos) + 91)) by (clear - Hs; lia).
      rewrite (T4 4 pos a Hin4 Hr Hc). rewrite (KEEP1 a Ha A3 Hc). exact (K3 a Hr Hc Hs). }
  split; [rewrite (P 2%bv ltac:(kcat_cs)); exact R2|].
  split; [rewrite (P 9%bv ltac:(kcat_cs)); exact R9|].
  split; [rewrite (P 8%bv ltac:(kcat_cs)); exact R8|].
  split; [rewrite (P 3%bv ltac:(kcat_cs)); exact R3|].
  split; [rewrite (P 4%bv ltac:(kcat_cs)); exact R4|].
  split; [rewrite (P 21%bv ltac:(kcat_cs)); exact R21|].
  rewrite (P 23%bv ltac:(kcat_cs)); exact R23.
- rewrite (P 18%bv ltac:(kcat_cs)). exact R18c.
- exact Q10.
- exact V3.
Qed.
Check (k_cat : k_cat_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G).
End c. End b. End a.
Print Assumptions k_cat.
