(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/RepPrfcf.v (commit 4d286b2e618d, file sha256 663ff3168aef) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 19 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 1 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepPrfcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 542489ba4f26) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 19 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 19 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker's class-full report walk, slice F2): __sanitizer::Printf's silent path,
   from VSNPrintf's contract and AppendToErrorMessageBuffer's.  The states and the four runs are RepPrfS.v.
   rule 24: proves function __sanitizer::Printf (reuse search: ossv proof index v5, built 2026-10-30T01:54:20Z,
   `proof-index VSNPrintf Printf SharedPrintfCode AppendNumber AppendToErrorMessageBuffer MmapOrDie`
   2026-10-30T02:25:54Z exit 0: the unit's ten lines are all `address` rows of its symbol and decode tables,
   nothing reusable; rule-24 check RepLookupCheck CONFIRM). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl2 YFl3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK1a YK15 YG04 YG03 YG0s YG0q YO0d YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG AGif0n. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFk5cf. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RepIFcf RepPrfD RepPrfS RepPrfE RepPrfT.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".
Ltac numconst := unfold kHighMemBeg, kHighMemEnd, TFIB_IMG_END, TFIB_IMG_LO, PR_STK, APP_STK, VSN_STK,
  A_PRINTF, A_VSNPRINTF, A_APPEND, C_PFCB, C_SILENT in *.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Notation SEED_okH := SEED_ok.
Notation imemsetH := imemset_stretch_stk.

Lemma uw64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.
(* the chunk list of the buffer region: entry i is the line's byte i *)
Lemma in_combine_seq : forall (l : list Z) s i b, In (i, b) (combine (seq s (length l)) l) ->
  (s <= i < s + length l)%nat /\ nth (i - s) l 0 = b.
Proof.
induction l as [|x t IH]; intros s i b H; cbn [combine seq length] in H; [destruct H|].
destruct H as [E|H].
- injection E as -> ->. split; [cbn [length]; lia|]. rewrite Nat.sub_diag. reflexivity.
- destruct (IH (S s) i b H) as [Hr Hn]. split; [cbn [length]; lia|].
  replace (i - s)%nat with (S (i - S s))%nat by lia. cbn [nth]. exact Hn.
Qed.
Lemma class_size_small : forall c, 1 <= c <= 31 -> 0 <= class_size c < 2 ^ 64.
Proof.
intros c Hc.
assert (A : forallb (fun c => (0 <=? class_size c) && (class_size c <? 2 ^ 64)) (map Z.of_nat (seq 1 31)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A.
assert (Hin : In c (map Z.of_nat (seq 1 31))) by (apply in_map_iff; exists (Z.to_nat c); split; [lia|]; apply in_seq; lia).
pose proof (A c Hin) as Hb. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma R_NUL_wf : forall out, YP09.region_wf (R_NUL out) = true.
Proof.
intros out. assert (HL : 0 <= Z.of_nat (length out)) by lia.
unfold R_NUL, YP09.region_wf, YP09.chunk_inside.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off YP09.c_val YP09.c_len YP09.cv_len forallb].
apply andb_true_iff; split; [apply andb_true_iff; split|].
- apply Z.leb_le. lia.
- apply orb_true_iff. right. apply andb_true_iff; split; apply Z.leb_le; lia.
- apply andb_true_iff; split; [| reflexivity].
  apply andb_true_iff; split; [apply andb_true_iff; split|]; apply Z.leb_le; cbn [Z.of_N]; lia.
Qed.
Lemma R_BUF_wf : forall out, YP09.region_wf (R_BUF out) = true.
Proof.
intros out. unfold R_BUF, YP09.region_wf.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
apply andb_true_iff; split; [apply andb_true_iff; split|].
- apply Z.leb_le. lia.
- apply orb_true_iff. left. apply Z.leb_le. lia.
- apply forallb_forall. intros c Hc. unfold bufchunks in Hc. apply in_map_iff in Hc as ((i, b) & <- & Hib).
  destruct (in_combine_seq out 0 i b Hib) as [Hi _].
  assert (HZ : (Z.of_nat i < Z.of_nat (length out))%Z) by (apply inj_lt; lia).
  assert (HZ0 : (0 <= Z.of_nat i)%Z) by apply Nat2Z.is_nonneg.
  unfold YP09.chunk_inside.
  cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len YP09.r_lo YP09.r_hi fst snd].
  apply andb_true_iff; split; [apply andb_true_iff; split|].
  + apply Z.leb_le. lia.
  + apply Z.leb_le. cbn [Z.of_N]. lia.
  + cbn [Z.of_N]. reflexivity.
Qed.
Lemma P3end_atoms : forall out, ss_atoms_lt 51 (P3end out) = true.
Proof.
intros out. unfold ss_atoms_lt, P3end. cbn [ss_regs ss_mem ss_facts ss_resv].
unfold mem_atoms_lt. cbn [forallb].
repeat rewrite Bool.andb_true_iff. repeat split; try (vm_compute; reflexivity).
unfold R_BUF. cbn [YP09.r_chunks].
apply forallb_forall. intros c Hc. unfold bufchunks in Hc. apply in_map_iff in Hc as ((i, b) & <- & _).
reflexivity.
Qed.

Lemma OUTS_bytes : forall out, In out OUTS -> forall i, (i < length out)%nat -> 0 < nth i out 0 < 256.
Proof.
intros out Hin i Hi.
assert (A : forallb (fun o => forallb (fun b => (0 <? b) && (b <? 256)) o) OUTS = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A. pose proof (A out Hin) as Ao. rewrite forallb_forall in Ao.
pose proof (Ao (nth i out 0) (nth_In out 0 Hi)) as Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma not_clobp_cases : forall r : bv 5, reg_in r CLOBP = false -> r = 0%bv \/ acallee_saved (bv_unsigned r).
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin. unfold acallee_saved.
repeat (destruct Hin as [<-|Hin];
  [first [ left; reflexivity
         | revert Hr; vm_compute; discriminate
         | right; match goal with |- context [bv_unsigned ?x] =>
             let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia ] |]).
destruct Hin.
Qed.
Lemma clobp_pres : forall (regs0 regs1 : bvmap 5 word), aregs_preserved regs0 regs1 ->
  forall r : bv 5, reg_in r CLOBP = false -> getr regs1 r = getr regs0 r.
Proof.
intros regs0 regs1 HP r Hr. destruct (not_clobp_cases r Hr) as [-> | Hcs].
- rewrite !getr_zero. reflexivity.
- specialize (HP (bv_unsigned r) Hcs). rewrite Z_to_bv_bv_unsigned in HP. exact HP.
Qed.
Lemma same_io_wvb : forall l p (md : Model), same_io md (with_vm_backing l p md).
Proof. intros l p md. unfold same_io. repeat split; reflexivity. Qed.


Section g.
Variables (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
#[local] Notation Hd := (w_H W).
#[local] Notation P := (bv_unsigned (getr regs 2%bv)).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis V_pfcb : val_mem tfibsegs (mrestrict Hd mem) C_PFCB 8 A_APPEND.
Hypothesis V_silent : val_mem tfibsegs (mrestrict Hd mem) C_SILENT 8 1.
Hypothesis Hsp16 : P mod 16 = 0.
Hypothesis Hsplo : ly_stk_lo ly <= P - PR_STK.
Hypothesis Hsphi : P <= ly_stk_hi ly.
Hypothesis P_stk : forall a, P - PR_STK <= a < P -> apresent Hd mem a.

Definition E0 : env := Ereg regs [].
Definition env32 (E : env) : Prop := (forall k, (k < 32)%nat -> ew E k = ew E0 k) /\ ed E = ed E0.
Lemma E2 : ew E0 2 = getr regs 2%bv. Proof. exact (ew_Ereg_nat regs [] 2 2%bv eq_refl). Qed.
Lemma EwR : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs r.
Proof. intros k r H. exact (ew_Ereg_nat regs [] k r H). Qed.
Lemma bE2 : forall E, env32 E -> base_val E (Some 2%nat) = P.
Proof. intros E [HE _]. cbn [base_val]. rewrite (HE 2%nat ltac:(lia)), E2. reflexivity. Qed.
Lemma Pfacts : kHighMemBeg + PR_STK <= P /\ P <= kHighMemEnd.
Proof.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). split; [lia | lia].
Qed.
Ltac pf := pose proof Pfacts as (PF1 & PF2).

(* Every window of the seed is in [P - PR_STK, P), above the image. *)
Lemma wr_PMEM0 : forall E, env32 E -> forall a, in_wrange E PMEM0 a -> P - PR_STK <= a < P.
Proof.
intros E HE a Hw. pose proof (bE2 E HE) as HB. cbn [base_val] in HB.
destruct Hw as (r & Hin & Hr). unfold PMEM0, PCONST, R_LOW, R_NB, R_TOP, lit8 in Hin. cbn [app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?HB in Hr; numconst; lia.
Qed.
Lemma wr_high : forall E, env32 E -> forall a, in_wrange E PMEM0 a -> TFIB_IMG_END <= a < 2 ^ 64.
Proof.
intros E HE a Hw. pose proof (wr_PMEM0 E HE a Hw) as Hx. pf. numconst. lia.
Qed.
Lemma HE0 : env32 E0. Proof. split; [intros k Hk | ]; reflexivity. Qed.
Lemma env32_havoc : forall E k ws, env32 E -> (32 <= k)%nat -> env32 (havoc E k ws).
Proof.
intros E k ws [HE HD] Hk. split; [intros n Hn | rewrite ed_havoc; exact HD].
rewrite ew_havoc_old by lia. exact (HE n Hn).
Qed.
Lemma env32_agree : forall E, env32 E -> env_agree 32 E0 E.
Proof. intros E [HE HD]. split; [exact HE | exact HD]. Qed.
(* a region list with the seed's windows keeps the seed's window bound *)
Lemma wr_any : forall E rs, env32 E -> windows rs = windows PMEM0 ->
  forall a, in_wrange E rs a -> P - PR_STK <= a < P.
Proof.
intros E rs HE Hwin a Ha. apply (wr_PMEM0 E HE).
apply (in_wrange_of_windows E rs PMEM0 a); [symmetry; exact Hwin | exact Ha].
Qed.
Lemma wr_any_high : forall E rs, env32 E -> windows rs = windows PMEM0 ->
  forall a, in_wrange E rs a -> TFIB_IMG_END <= a < 2 ^ 64.
Proof.
intros E rs HE Hwin a Ha. pose proof (wr_any E rs HE Hwin a Ha) as Hx. pf. numconst. lia.
Qed.

(* The prefix: Printf's and SharedPrintfCode's prologues, internal_memset of the buffer, and
   SharedPrintfCodeNoBuffer's prologue, to VSNPrintf's entry. *)
Lemma to_vsn : forall (Q : world tfibsegs -> config -> Prop),
  (forall E2 ms2 mat2, env32 E2 ->
     st_ok tfibsegs E2 (fst P2r) (restrict Hd ms2) ->
     (forall x : word, ~ (P - PR_STK <= bv_unsigned x < P) -> ms_mem ms2 x = mem x) ->
     (forall a, apresent Hd mem a -> apresent Hd (ms_mem ms2) a) ->
     SRr tfibsegs W (mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (w64 A_PRINTF) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros Q HK. pose proof Hwx_tfa as Hwx. pf.
pose proof (SEED_okH W ly regs mem LY V_pfcb V_silent Hsp16 Hsplo Hsphi P_stk) as HS.
srr_run_to_sh reptbl_ok HS 0x64ba4. rename HF into HF1. clear HFr.
lazymatch type of HS with st_ok _ _ ?ss1 (restrict _ ?ms1) =>
assert (PR1 : forall a, apresent Hd mem a -> apresent Hd (ms_mem ms1) a)
  by (apply (pres_after_run Hd E0 ss1 PMEM0 (mkst regs (w64 A_PRINTF) mem (seg_rom tfibsegs)) ms1 HS HF1
        ltac:(vm_compute; reflexivity) (wr_any_high E0 PMEM0 HE0 eq_refl)));
assert (FR1 : forall x : word, ~ (P - PR_STK <= bv_unsigned x < P) -> ms_mem ms1 x = mem x)
  by (intros x Hx; apply HF1; intros Hw; apply Hx; exact (wr_any E0 _ HE0 eq_refl _ Hw))
end.
rreg HS (1%bv : bv 5) G1. rreg HS (10%bv : bv 5) G10. rreg HS (11%bv : bv 5) G11. rreg HS (12%bv : bv 5) G12.
fold E0 in G10. rewrite E2 in G10.
replace (bv_unsigned (getr regs 2%bv) + -512) with (bv_unsigned (getr regs 2%bv) - 512) in G10 by lia.
eapply (imemsetH W 32 E0 _ _ _ (P - 512) 400 0x67fa0 Q HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | exact G10 | exact G11 | exact G12 | exact G1 | lia | numconst; lia | numconst; lia | reflexivity | numconst; lia
  | | | | ].
- intros a Ha. apply PR1. apply P_stk. numconst. lia.
- pose proof (bE2 E0 HE0) as HB. cbn [base_val] in HB.
  intros r Hr. cbn [ss_mem PMEM0 PCONST app In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  unfold R_LOW, R_NB, R_TOP, lit8; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite ?HB; numconst; lia.
- pose proof (bE2 E0 HE0) as HB. cbn [base_val] in HB.
  intros r a Hr Ha. revert Ha. cbn [ss_mem PMEM0 PCONST app In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  unfold R_LOW, R_NB, R_TOP, lit8; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite ?HB; numconst; lia.
- intros regs' mem' mat' HS2 G10' Hregs Hfr Hpres.
  srr_run_to_sh reptbl_ok HS2 A_VSNPRINTF. rename HF into HF3. clear HFr.
  assert (HE2 : env32 (havoc E0 32 (map (getr regs') [11; 12; 13]%bv))) by (apply env32_havoc; [exact HE0 | lia]).
  lazymatch type of HS2 with st_ok _ ?E3 _ (restrict _ ?ms3) => apply (HK E3 ms3 _ HE2 HS2) end.
  + intros x Hx.
    lazymatch type of HF3 with frame_of _ ?rs2 _ _ =>
      assert (WIN2 : windows rs2 = windows PMEM0) by (vm_compute; reflexivity);
      rewrite (HF3 x); [| intros Hw; apply Hx; exact (wr_any _ rs2 HE2 WIN2 _ Hw)] end.
    rewrite (Hfr x); [| numconst; lia].
    apply FR1. exact Hx.
  + intros a Ha.
    lazymatch type of HS2 with st_ok _ _ ?ss3 (restrict _ ?ms3) =>
    lazymatch type of HF3 with frame_of _ ?rs2 _ _ =>
      assert (WIN2 : windows rs2 = windows PMEM0) by (vm_compute; reflexivity);
      assert (WIN3 : windows (ss_mem ss3) = windows rs2) by (vm_compute; reflexivity);
      apply (pres_after_run Hd _ ss3 rs2 (mkst regs' (w64 0x67fa0) mem' (seg_rom tfibsegs)) ms3 HS2 HF3 WIN3
        (wr_any_high _ rs2 HE2 WIN2)) end end.
    apply Hpres. apply PR1. exact Ha.
Qed.

(* Every window of the state at the callback's entry is in the same [P - PR_STK, P). *)
Lemma wr_P3s : forall E out, env32 E -> 0 <= Z.of_nat (length out) < 400 ->
  forall a, in_wrange E (ss_mem (P3s out)) a -> P - PR_STK <= a < P.
Proof.
intros E out HE Hlen a Ha. pose proof (bE2 E HE) as HB. cbn [base_val] in HB.
destruct Ha as (r & Hin & Hr). cbn [ss_mem pin addreg P2c PCONST In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
unfold R_BUF, R_NUL, R_LOW, R_NB, R_TOP, lit8 in Hr;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?HB in Hr; numconst; lia.
Qed.
Lemma wr_P3s_high : forall E out, env32 E -> 0 <= Z.of_nat (length out) < 400 ->
  forall a, in_wrange E (ss_mem (P3s out)) a -> TFIB_IMG_END <= a < 2 ^ 64.
Proof.
intros E out HE Hlen a Ha. pose proof (wr_P3s E out HE Hlen a Ha) as Hx. pf. numconst. lia.
Qed.
Lemma wr_P3s_buf : forall E out, env32 E -> 0 <= Z.of_nat (length out) < 400 ->
  forall a, in_wrange E (ss_mem (P3s out)) a -> ~ (P - 512 <= a < P - 512 + Z.of_nat (length out)).
Proof.
intros E out HE Hlen a Ha. pose proof (bE2 E HE) as HB. cbn [base_val] in HB.
destruct Ha as (r & Hin & Hr). cbn [ss_mem pin addreg P2c PCONST In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
unfold R_BUF, R_NUL, R_LOW, R_NB, R_TOP, lit8 in Hr;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?HB in Hr; numconst; lia.
Qed.

(* The VSNPrintf call and the state it leaves at AppendToErrorMessageBuffer's entry. *)
Lemma to_append : forall (Q : world tfibsegs -> config -> Prop) (fmt : Z) (out : list Z),
  vsn_spec_cf ->
  vsn_img_facts (mrestrict Hd mem) ->
  getr regs 4%bv = w64 TFIB_TP ->
  getr regs 10%bv = w64 fmt ->
  ((fmt = FMT_OOM1 /\ getr regs 11%bv = w64 A_TOOLNAME /\ out = render1) \/
   (exists c sz, fmt = FMT_OOM2 /\ 1 <= c <= 31 /\ sz = class_size c /\ getr regs 11%bv = w64 REGION_MB /\
      getr regs 12%bv = w64 c /\ getr regs 13%bv = w64 sz /\ out = render2 c sz)) ->
  Z.of_nat (length out) < 400 ->
  (forall E4 ms4 mat4, env32 E4 -> In out OUTS ->
     st_ok tfibsegs E4 (P3end out) (restrict Hd ms4) ->
     (forall x : word, ~ (P - PR_STK <= bv_unsigned x < P) -> ms_mem ms4 x = mem x) ->
     (forall a, apresent Hd mem a -> apresent Hd (ms_mem ms4) a) ->
     (forall i, (i < length out)%nat ->
        val_mem tfibsegs (mrestrict Hd (ms_mem ms4)) (P - 512 + Z.of_nat i) 1 (nth i out 0)) ->
     val_mem tfibsegs (mrestrict Hd (ms_mem ms4)) (P - 512 + Z.of_nat (length out)) 1 0 ->
     SRr tfibsegs W (mkCfg ms4 (with_vm_backing (m_vm_lazy md) mat4 md)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (w64 A_PRINTF) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros Q fmt out VSN Hvsn Htp Hfmt Hcase Hlen HK.
pose proof Hwx_tfa as Hwx. pf.
assert (LN : 0 <= Z.of_nat (length out)) by lia.
assert (Hin : In out OUTS).
{ destruct Hcase as [(_ & _ & ->)|(c & sz & _ & Hc & -> & _ & _ & _ & ->)];
  [left; reflexivity | apply OUTS_render2; exact Hc]. }
apply to_vsn. intros Ev ms2 mat2 HEv HS2 FR2 PR2.
pose proof (bE2 Ev HEv) as HB. cbn [base_val] in HB.
rreg HS2 (1%bv : bv 5) Gv1. rreg HS2 (2%bv : bv 5) Gv2. rreg HS2 (4%bv : bv 5) Gv4.
rreg HS2 (10%bv : bv 5) Gv10. rreg HS2 (11%bv : bv 5) Gv11. rreg HS2 (12%bv : bv 5) Gv12.
rreg HS2 (13%bv : bv 5) Gv13.
rewrite (proj1 HEv 2%nat ltac:(lia)), E2 in Gv2, Gv10, Gv13.
rewrite (proj1 HEv 4%nat ltac:(lia)), (EwR 4 4%bv eq_refl), Htp in Gv4.
rewrite (proj1 HEv 10%nat ltac:(lia)), (EwR 10 10%bv eq_refl), Hfmt in Gv12.
assert (Hfmt64 : 0 <= fmt < 2 ^ 64)
  by (destruct Hcase as [(-> & _)|(c & sz & -> & _)]; unfold FMT_OOM1, FMT_OOM2; lia).
replace (bv_unsigned (getr regs 2%bv) + -512) with (P - 512) in Gv10 by lia.
replace (bv_unsigned (getr regs 2%bv) + -640) with (P - 640) in Gv2 by lia.
replace (bv_unsigned (getr regs 2%bv) + -56) with (P - 56) in Gv13 by lia.
assert (SPV : bv_unsigned (getr (ms_regs ms2) 2%bv) = P - 640)
  by (rewrite Gv2; apply unsigned_lit_small; numconst; lia).
(* the two presence facts VSNPrintf needs *)
assert (PRv : forall a, P - 1152 <= a < P - 640 -> apresent Hd (ms_mem ms2) a)
  by (intros a Ha; apply PR2; apply P_stk; numconst; lia).
assert (PRb : forall a, P - 512 <= a < P - 112 -> apresent Hd (ms_mem ms2) a)
  by (intros a Ha; apply PR2; apply P_stk; numconst; lia).
(* the va slots, from SharedPrintfCode's frame *)
assert (FC : fmt_case (mrestrict Hd (ms_mem ms2)) fmt (P - 56) out).
{ destruct Hcase as [(-> & Ha1 & ->)|(c & sz & -> & Hc & Hsz & Ha1 & Ha2 & Ha3 & ->)].
  - left. split; [reflexivity|]. split; [| reflexivity].
    memv HS2 2%nat 8%nat;
      [ rewrite HB; lia
      | cbn [sv_denot]; rewrite (proj1 HEv 11%nat ltac:(lia)), (EwR 11 11%bv eq_refl), Ha1,
          uw64 by (unfold A_TOOLNAME; lia); f_equal; lia
      | unfold A_TOOLNAME; lia ].
  - right. exists c, sz. split; [reflexivity|]. split; [exact Hc|]. split; [exact Hsz|].
    pose proof (class_size_small c Hc) as Hcs. rewrite <- Hsz in Hcs.
    split; [| split; [| split; [| reflexivity]]].
    + memv HS2 2%nat 8%nat;
        [ rewrite HB; lia
        | cbn [sv_denot]; rewrite (proj1 HEv 11%nat ltac:(lia)), (EwR 11 11%bv eq_refl), Ha1,
            uw64 by (unfold REGION_MB; lia); f_equal; lia
        | unfold REGION_MB; lia ].
    + memv HS2 2%nat 7%nat;
        [ rewrite HB; lia
        | cbn [sv_denot]; rewrite (proj1 HEv 12%nat ltac:(lia)), (EwR 12 12%bv eq_refl), Ha2,
            uw64 by lia; f_equal; lia
        | lia ].
    + memv HS2 2%nat 6%nat;
        [ rewrite HB; lia
        | cbn [sv_denot]; rewrite (proj1 HEv 13%nat ltac:(lia)), (EwR 13 13%bv eq_refl), Ha3,
            uw64 by lia; f_equal; lia
        | lia ]. }
(* the image bytes VSNPrintf reads are below the stack, so the prefix did not touch them *)
assert (VMLOW : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= TFIB_IMG_END ->
  val_mem tfibsegs (mrestrict Hd mem) a n v -> val_mem tfibsegs (mrestrict Hd (ms_mem ms2)) a n v).
{ intros a n v Ha Han Hv. apply (val_mem_frame Hd mem (ms_mem ms2) a n v); [| exact Hv].
  intros k Hk. apply FR2. rewrite unsigned_lit_small by (numconst; lia). numconst; lia. }
assert (VI2 : vsn_img_facts (mrestrict Hd (ms_mem ms2))).
{ destruct Hvsn as [F1 F2 FT JS JU].
  assert (L1 : Z.of_nat (length FMT1_BYTES) = 20) by (vm_compute; reflexivity).
  assert (L2 : Z.of_nat (length FMT2_BYTES) = 66) by (vm_compute; reflexivity).
  assert (LT : Z.of_nat (length (str_z "AddressSanitizer"%string ++ [0])) = 17) by (vm_compute; reflexivity).
  constructor.
  - intros i Hi. apply VMLOW; [unfold FMT_OOM1; lia | unfold FMT_OOM1, TFIB_IMG_END; lia | exact (F1 i Hi)].
  - intros i Hi. apply VMLOW; [unfold FMT_OOM2; lia | unfold FMT_OOM2, TFIB_IMG_END; lia | exact (F2 i Hi)].
  - intros i Hi. apply VMLOW; [unfold A_TOOLNAME; lia | unfold A_TOOLNAME, TFIB_IMG_END; lia | exact (FT i Hi)].
  - apply VMLOW; [lia | unfold TFIB_IMG_END; lia | exact JS].
  - apply VMLOW; [lia | unfold TFIB_IMG_END; lia | exact JU]. }
(* shape the machine state and call VSNPrintf *)
assert (Hpc : ss_pc (fst P2r) = A_VSNPRINTF) by (vm_compute; reflexivity).
pose proof (st_ok_restrict_mkst tfibsegs Hd Ev (fst P2r) ms2 HS2 ltac:(vm_compute; reflexivity)) as Hsh.
rewrite Hpc in Hsh. rewrite Hsh.
eapply SRr_bind.
{ eapply (VSN W ly (ms_regs ms2) (ms_mem ms2) _ (P - 512) fmt (P - 56) out);
  [ exact LY | exact IMG | exact Gv10 | exact Gv11 | exact Gv12 | exact Gv13 | exact Gv4
  | rewrite Gv1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small; lia
  | exact FC | exact VI2 | exact Hlen
  | rewrite SPV; numconst; lia
  | rewrite SPV; numconst; lia
  | rewrite SPV; intros a Ha; apply PRv; numconst; lia
  | rewrite SPV; lia
  | numconst; lia
  | intros a Ha; apply PRb; lia
  | right; lia
  | rewrite SPV; lia
  | numconst; lia ]. }
intros W1 c1 Hle (-> & regs3 & mem3 & mat3 & Ec & Hrp3 & Glen3 & Hfr3 & Hap3 & Hbuf3 & Hnul3).
subst c1. rewrite Gv1. srr_norm_model.
(* rebuild the symbolic state at the return 0x6860c *)
assert (MK : forall a, 0 <= a < 2 ^ 64 -> ~ (P - 1152 <= a < P - 640) ->
  ~ (P - 512 <= a <= P - 512 + Z.of_nat (length out)) -> mem3 (Z_to_bv 64 a) = ms_mem ms2 (Z_to_bv 64 a)).
{ intros a Ha H1 H2. apply Hfr3.
  - rewrite SPV, unsigned_lit_small by lia. intros C. apply H1. numconst. lia.
  - rewrite unsigned_lit_small by lia. exact H2. }
assert (FR3 : forall x : word, ~ (P - PR_STK <= bv_unsigned x < P) -> mem3 x = mem x).
{ intros x Hx. transitivity (ms_mem ms2 x); [| apply FR2; exact Hx]. apply Hfr3.
  - rewrite SPV. intros C. apply Hx. numconst. lia.
  - intros C. apply Hx. numconst. lia. }
assert (PR3 : forall a, apresent Hd mem a -> apresent Hd mem3 a) by (intros a Ha; apply Hap3; apply PR2; exact Ha).
assert (PW3 : forall a, P - PR_STK <= a < P -> writable_at tfibsegs (mrestrict Hd mem3) a).
{ intros a Ha. apply apresent_writable; [numconst; lia|]. apply PR3. apply P_stk. exact Ha. }
(* the regions kept over the call *)
assert (RK : Forall (region_kept tfibsegs Ev (mrestrict Hd (ms_mem ms2)) (mrestrict Hd mem3)) (skipn 1 (ss_mem (fst P2r)))).
{ cbn [ss_mem skipn].
  repeat (apply Forall_cons;
    [ split;
      [ intros a Ha; apply mbyte_mrestrict_same;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?HB in Ha; apply MK; numconst; lia
      | intros a Ha Hw; apply (writable_at_eq tfibsegs (mrestrict Hd (ms_mem ms2)) (mrestrict Hd mem3) a);
        [ unfold mrestrict; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?HB in Ha;
          rewrite MK by (numconst; lia); reflexivity
        | exact Hw ] ] | ]).
  apply Forall_nil. }
(* the state after the call, with the buffer's two regions and R_LOW added back *)
pose proof (st_ok_after_call tfibsegs 35 Ev (fst P2r) (restrict Hd ms2) regs3 (mrestrict Hd mem3)
  (skipn 1 (ss_mem (fst P2r))) 0x6860c HS2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(cbn [ss_mem]; apply submem_drop; apply submem_refl) ltac:(vm_compute; reflexivity) Hrp3 RK) as HS3.
set (E3 := havoc Ev 35 (map (getr regs3) CLOB)) in HS3.
assert (HE3 : env32 E3) by (apply env32_havoc; [exact HEv | lia]).
pose proof (bE2 E3 HE3) as HB3. cbn [base_val] in HB3.
change (ss_after_call (fst P2r) (skipn 1 (ss_mem (fst P2r))) 35 0x6860c) with P2c in HS3.
rewrite <- restrict_mkst_fx in HS3.
assert (HSa : st_ok tfibsegs E3 (addreg R_LOW P2c) (restrict Hd (mkst regs3 (w64 0x6860c) mem3 (seg_rom tfibsegs)))).
{ apply (st_ok_add_region E3 P2c _ R_LOW HS3 ltac:(vm_compute; reflexivity)).
  - cbn [ms_mem restrict mkst].
    apply (region_ok_window E3 (mrestrict Hd mem3) 2%nat P); [exact HB3 | numconst; lia | numconst; lia |].
    intros a Ha. apply PW3. numconst. lia.
  - apply all_disjoint_of_extents. unfold P2c, R_LOW, extent_of_region.
    cbn [map ss_mem YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?HB3.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; lia. }
assert (HSb : st_ok tfibsegs E3 (addreg (R_NUL out) (addreg R_LOW P2c))
  (restrict Hd (mkst regs3 (w64 0x6860c) mem3 (seg_rom tfibsegs)))).
{ apply (st_ok_add_region E3 _ _ (R_NUL out) HSa (R_NUL_wf out)).
  - cbn [ms_mem restrict mkst]. unfold region_ok, R_NUL.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite HB3.
    split; [numconst; lia|]. split; [numconst; lia|].
    split; [intros o Ho; apply PW3; numconst; lia|].
    apply Forall_cons; [| apply Forall_nil].
    eapply (chunk_ok_val tfibsegs E3 (mrestrict Hd mem3) P (-512 + Z.of_nat (length out)) 1 (SLit 0) 0);
      [reflexivity | cbn; lia | cbn; lia |].
    replace (P + (-512 + Z.of_nat (length out))) with (P - 512 + Z.of_nat (length out)) by lia.
    exact Hnul3.
  - apply all_disjoint_of_extents. unfold P2c, R_LOW, R_NUL, extent_of_region.
    cbn [map ss_mem addreg YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?HB3.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; lia. }
assert (HSc : st_ok tfibsegs E3 (addreg (R_BUF out) (addreg (R_NUL out) (addreg R_LOW P2c)))
  (restrict Hd (mkst regs3 (w64 0x6860c) mem3 (seg_rom tfibsegs)))).
{ apply (st_ok_add_region E3 _ _ (R_BUF out) HSb (R_BUF_wf out)).
  - cbn [ms_mem restrict mkst]. unfold region_ok, R_BUF.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite HB3.
    split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. unfold bufchunks in Hc. apply in_map_iff in Hc as ((i, b) & <- & Hib).
    destruct (in_combine_seq out 0 i b Hib) as [Hi Hn]. rewrite Nat.sub_0_r in Hn.
    cbn [fst snd].
    eapply (chunk_ok_val tfibsegs E3 (mrestrict Hd mem3) P (-512 + Z.of_nat i) 1 (SLit b) b);
      [reflexivity | | cbn; lia |].
    + pose proof (OUTS_bytes out Hin i ltac:(lia)) as Hb. rewrite Hn in Hb. cbn. lia.
    + replace (P + (-512 + Z.of_nat i)) with (P - 512 + Z.of_nat i) by lia.
      rewrite <- Hn. apply Hbuf3. lia.
  - apply all_disjoint_of_extents. unfold P2c, R_LOW, R_NUL, R_BUF, extent_of_region.
    cbn [map ss_mem addreg YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?HB3.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; lia. }
assert (HSp : st_ok tfibsegs E3 (P3s out) (restrict Hd (mkst regs3 (w64 0x6860c) mem3 (seg_rom tfibsegs)))).
{ unfold P3s. apply (st_ok_pin_reg E3 _ _ 10%bv (SLit (Z.of_nat (length out))) HSc ltac:(discriminate)).
  cbn [sv_denot ms_regs restrict mkst]. symmetry. exact Glen3. }
(* run 3, to the callback's entry *)
pose proof (proj1 (Forall_forall _ _) P3_ends out Hin) as HR3.
eapply (SRr_run_to_sh_gen tfibsegs reptbl reptbl_ok Hwx W FUEL A_APPEND E3 (P3s out) (P3end out) RS_running
  (mkst regs3 (w64 0x6860c) mem3 (seg_rom tfibsegs)) _ _ HSp HR3).
intros ms4 mat4 HS4 HF4 HFr4. srr_norm_model.
apply (HK E3 ms4 _ HE3 Hin HS4).
- intros x Hx. transitivity (mem3 x); [| apply FR3; exact Hx].
  apply HF4. intros Hw. apply Hx. exact (wr_P3s E3 out HE3 (conj LN Hlen) _ Hw).
- intros a Ha.
  apply (pres_after_run Hd E3 (P3end out) (ss_mem (P3s out))
    (mkst regs3 (w64 0x6860c) mem3 (seg_rom tfibsegs)) ms4 HS4 HF4 ltac:(reflexivity)
    (wr_P3s_high E3 out HE3 (conj LN Hlen))).
  apply PR3. exact Ha.
- intros i Hi. apply (val_mem_frame Hd mem3 (ms_mem ms4) (P - 512 + Z.of_nat i) 1 (nth i out 0));
    [| apply Hbuf3; exact Hi].
  intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
  apply HF4. intros Hw. pose proof (wr_P3s_buf E3 out HE3 (conj LN Hlen) _ Hw) as Hb.
  rewrite unsigned_lit_small in Hb by (numconst; lia). lia.
- memv HS4 1%nat 0%nat;
    [unfold R_NUL; cbn [YP09.r_base YP09.c_off base_val]; rewrite HB3; lia | reflexivity | lia].
Qed.

(* Every window of the tail state is in [P - PR_STK, P) too. *)
Lemma wr_P4S : forall E, env32 E -> forall a, in_wrange E (ss_mem P4S) a -> P - PR_STK <= a < P.
Proof.
intros E HE a Ha. pose proof (bE2 E HE) as HB. cbn [base_val] in HB.
destruct Ha as (r & Hin & Hr). cbn [ss_mem P4S In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?HB in Hr; numconst; lia.
Qed.
Lemma wr_P4S_high : forall E, env32 E -> forall a, in_wrange E (ss_mem P4S) a -> TFIB_IMG_END <= a < 2 ^ 64.
Proof.
intros E HE a Ha. pose proof (wr_P4S E HE a Ha) as Hx. pf. numconst. lia.
Qed.

(* The tail: LogMessageOnPrintf, UnmapOrDie(0, 0) and the three epilogues, to Printf's ret. *)
Lemma to_ret : forall (W5 : world tfibsegs) (E5 : env) (ms5 : machine_state) (md5 : Model)
    (Q : world tfibsegs -> config -> Prop),
  env32 E5 -> YK0s.ret_ok (getr regs 1%bv) ->
  st_ok tfibsegs E5 P4S (restrict (w_H W5) ms5) ->
  (forall regs6 mem6 mat6,
     regs_preserved regs regs6 ->
     (forall x : word, ~ (P - PR_STK <= bv_unsigned x < P) -> mem6 x = ms_mem ms5 x) ->
     (forall a, apresent (w_H W5) (ms_mem ms5) a -> apresent (w_H W5) mem6 a) ->
     Q W5 (cfg_at tfibsegs (raZ regs) regs6 mem6 (with_vm_backing (m_vm_lazy md5) mat6 md5))) ->
  SRr tfibsegs W5 (mkCfg ms5 md5) Q.
Proof.
intros W5 E5 ms5 md5 Q HE5 Hra HS5 HK. pose proof Hwx_tfa as Hwx. pf.
eapply (SRr_run_to_sh_gen tfibsegs reptbl reptbl_ok Hwx W5 FUEL 0x67f6c E5 P4S P4E RS_running ms5 _ _ HS5 P4_run).
intros ms6 mat6 HS6 HF6 HFr6. srr_norm_model.
eapply (SRr_ret_at tfibsegs reptbl reptbl_ok Hwx W5 E5 P4E ms6 _ Q HS6
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
intros mat7. srr_norm_model.
rreg HS6 (1%bv : bv 5) Gr1.
rewrite (proj1 HE5 1%nat ltac:(lia)), (EwR 1 1%bv eq_refl) in Gr1.
rewrite Gr1, Hra.
replace (mkCfg (mkst (ms_regs ms6) (getr regs 1%bv) (ms_mem ms6) (seg_rom tfibsegs))
           (with_vm_backing (m_vm_lazy md5) mat7 md5))
  with (cfg_at tfibsegs (raZ regs) (ms_regs ms6) (ms_mem ms6) (with_vm_backing (m_vm_lazy md5) mat7 md5))
  by (unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
apply HK.
- apply (regs_preserved_of_st_ok tfibsegs E5 P4E (restrict (w_H W5) ms6) regs [] HS6
    (env32_agree E5 HE5) ltac:(vm_compute; reflexivity)).
- intros x Hx. apply HF6. intros Hw. apply Hx. exact (wr_P4S E5 HE5 _ Hw).
- intros a Ha. apply (pres_after_run (w_H W5) E5 P4E (ss_mem P4S) ms5 ms6 HS6 HF6 ltac:(reflexivity)
    (wr_P4S_high E5 HE5)). exact Ha.
Qed.

End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
Section f. Context {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* A literal cell of TfibSyms' as_const, read off the relation. *)
Lemma const_val : forall (ly' : alayout) (S' : astate) (Hp' : list Z) (W'' : world tfibsegs)
    (mem'' : word -> option byte) (md'' : Model) (a : Z) (w : nat) (v : Z),
  TfibSyms B -> ARcf tfibsegs B ly' S' Hp' W'' mem'' md'' ->
  YF0x.cell_lookup (Tfib_const ly') (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  val_mem tfibsegs (mrestrict (w_H W'') mem'') a w v.
Proof.
intros ly' S' Hp' W'' mem'' md'' a w v TS AR Hlk.
destruct AR as (M & _). pose proof (amc_const _ _ _ _ _ M) as HC. rewrite (ts_const B TS) in HC.
pose proof (YF0x.cell_lookup_In _ _ _ Hlk) as Hin.
exact (YF0x.cell_holds_val_mem B ly' (w_H W'') mem'' (ANum a) w (ANum v)
        (proj1 (Forall_forall _ _) HC _ Hin)).
Qed.

(* The held lock word is in the allocator's space, far above the image, so the reset leaves image bytes alone. *)
Lemma held_img : forall lk (ly' : alayout) (m : word -> option byte) a,
  layout_ok ly' -> lk_ok ly' lk -> 0 <= a < TFIB_IMG_END ->
  held_mem lk m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros lk ly' m a LY' LKO Ha. destruct lk as [z|]; [| reflexivity].
cbn [held_mem]. destruct (in8 z (Z_to_bv 64 a)) eqn:E; [exfalso | reflexivity].
destruct LKO as [Hd0 | (c & Hc & Hd0)]; [discriminate|]. injection Hd0 as ->.
unfold in8 in E. apply andb_prop in E as [E1 _]. apply Z.leb_le in E1.
rewrite rp_w64u in E1 by (unfold TFIB_IMG_END in Ha; lia).
unfold region_lock_addr in E1.
pose proof (lo_space_in ly' LY') as [S1 _]. pose proof (lo_high ly' LY') as [H1 _].
unfold TFIB_IMG_END, kRegionInfoOff, kHighMemBeg in *. lia.
Qed.

Theorem printf_ok : printf_of_parts_t B.
Proof.
intros VSN AP R Hp ly S W regs mem md fmt out lk K Q PRE ROOM REGS Hfmt Hcase Hlen HK.
pose proof PRE as PRE0.
destruct PRE as (OB & EO & LY & IMG & TS & TSD & ARL & XM & WFP & QL & EX & EB & RI & _).
destruct REGS as (Hgp & Htp & Hra & Hra4096 & Hsp16 & Hsplo & Hsphi & P_stk).
unfold YG0d.spZ in Hsp16, Hsplo, Hsphi, P_stk, ROOM |- *.
pose proof (rif_callback W mem RI) as V_cb.
pose proof (rif_silent W mem RI) as V_sil.
pose proof (rif_vsn W mem RI) as V_vsn.
pose proof (rp_stk_bounds ly LY) as (K1 & K2 & K3 & K4).
apply (amreal_SRr_pre tfibsegs _ W _ Q
  (fun W' c' => W' = W /\ exists E4 ms4 mat4,
     env32 regs E4 /\ In out OUTS /\
     st_ok tfibsegs E4 (P3end out) (restrict (w_H W) ms4) /\
     (forall x : word, ~ (bv_unsigned (getr regs 2%bv) - PR_STK <= bv_unsigned x < bv_unsigned (getr regs 2%bv)) -> ms_mem ms4 x = mem x) /\
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms4) a) /\
     (forall i, (i < length out)%nat ->
        val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms4)) (bv_unsigned (getr regs 2%bv) - 512 + Z.of_nat i) 1 (nth i out 0)) /\
     val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms4)) (bv_unsigned (getr regs 2%bv) - 512 + Z.of_nat (length out)) 1 0 /\
     c' = mkCfg ms4 (with_vm_backing (m_vm_lazy md) mat4 md))).
- apply (to_append W ly regs mem md LY IMG V_cb V_sil Hsp16 Hsplo Hsphi P_stk _ fmt out
    VSN V_vsn Htp Hfmt Hcase Hlen).
  intros E4 ms4 mat4 HE4 Hin HS4 FR4 PR4 BUF4 NUL4.
  apply SRr_ret. split; [reflexivity|]. exists E4, ms4, mat4.
  split; [exact HE4|]. split; [exact Hin|]. split; [exact HS4|]. split; [exact FR4|].
  split; [exact PR4|]. split; [exact BUF4|]. split; [exact NUL4 | reflexivity].
- intros W1 c1 Hle (-> & E4 & ms4 & mat4 & HE4 & Hin & HS4 & FR4 & PR4 & BUF4 & NUL4 & ->).
  rreg HS4 (1%bv : bv 5) Ga1. rreg HS4 (2%bv : bv 5) Ga2. rreg HS4 (3%bv : bv 5) Ga3.
  rreg HS4 (4%bv : bv 5) Ga4. rreg HS4 (10%bv : bv 5) Ga10.
  rewrite (proj1 HE4 2%nat ltac:(lia)), (E2 regs) in Ga2, Ga10.
  rewrite (proj1 HE4 3%nat ltac:(lia)), (EwR regs 3 3%bv eq_refl), Hgp in Ga3.
  rewrite (proj1 HE4 4%nat ltac:(lia)), (EwR regs 4 4%bv eq_refl), Htp in Ga4.
  replace (bv_unsigned (getr regs 2%bv) + -640) with (bv_unsigned (getr regs 2%bv) - 640) in Ga2 by (unfold spZ; lia).
  replace (bv_unsigned (getr regs 2%bv) + -512) with (bv_unsigned (getr regs 2%bv) - 512) in Ga10 by (unfold spZ; lia).
  assert (SPR : 0 <= bv_unsigned (getr regs 2%bv) - 640 < 2 ^ 64).
  { clear - LY Hsplo Hsphi. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
    unfold PR_STK, APP_STK in Hsplo. unfold kHighMemEnd in T4. unfold kHighMemBeg in T7.
    change (2 ^ 64) with 18446744073709551616. clear LY. lia. }
  assert (SPA : bv_unsigned (getr (ms_regs ms4) 2%bv) = bv_unsigned (getr regs 2%bv) - 640)
    by (rewrite Ga2; apply rp_w64u; exact SPR).
  assert (RAA : raZ (ms_regs ms4) = 0x68640) by (unfold raZ; rewrite Ga1; apply rp_w64u; lia).
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E4 (P3end out) ms4 HS4 eq_refl) as Hsh4.
  change (ss_pc (P3end out)) with A_APPEND in Hsh4. rewrite Hsh4.
  apply (AP R Hp ly S W (ms_regs ms4) (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)
    (bv_unsigned (getr regs 2%bv) - 512) out lk K Q).
  + apply (pre_stack_keep_wvb B lk Hp ly S W mem md (ms_mem ms4) mat4 (bv_unsigned (getr regs 2%bv) - PR_STK) (bv_unsigned (getr regs 2%bv))
      PRE0 Hsplo Hsphi FR4). intros a Ha. apply PR4. apply P_stk. exact Ha.
  + exact ROOM.
  + unfold errb_call_regs, YG0d.spZ. split; [exact Ga3|]. split; [exact Ga4|].
    split; [rewrite Ga1; apply YK0s.ret_ok_even; rewrite rp_w64u; lia|].
    split; [rewrite Ga1, rp_w64u; lia|].
    split; [rewrite SPA; numconst; lia|].
    split; [rewrite SPA; numconst; lia|].
    split; [rewrite SPA; numconst; lia|].
    rewrite SPA. intros a Ha. apply PR4. apply P_stk. numconst. lia.
  + exact Ga10.
  + unfold YG0d.spZ. rewrite SPA. lia.
  + numconst. lia.
  + unfold ERRB_INIT. lia.
  + intros i Hi. split; [apply BUF4; exact Hi | exact (OUTS_bytes out Hin i Hi)].
  + exact NUL4.
  + intros S' W' c' HPost. pose proof HPost as HPost0.
    destruct HPost as (ly' & regs5 & mem5 & md5 & Ec & PRE5 & SZ5 & LL5 & WLE5 & AR5 & IO5 & AV5 & MF5 & MN5 & PRS5).
    subst c'. rewrite RAA.
    destruct (rp_layout_le_stk _ _ _ LL5) as [Llo Lhi].
    pose proof PRE5 as PRE5'. destruct PRE5' as (_ & _ & LY' & _ & _ & _ & ARL' & _).
    destruct ARL' as (LKO' & AR' & _). destruct ARL as (LKO & _ & _).
    (* the bytes the tail still needs, at the post state *)
    assert (MK5 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned (getr regs 2%bv) - 1152 <= a < bv_unsigned (getr regs 2%bv) - 640) ->
      ly_stk_lo ly <= a < ly_stk_hi ly -> mem5 (Z_to_bv 64 a) = ms_mem ms4 (Z_to_bv 64 a)).
    { intros a Ha H1 H2. apply MF5.
      - rewrite rp_w64u by lia. exact (rp_stack_not_AOX B lk Hp ly S W mem md a PRE0 H2).
        - rewrite rp_w64u by lia.
        apply (rp_stack_not_AOX B lk Hp ly' S' W' mem5 md5 a PRE5). rewrite Llo, Lhi. exact H2.
      - unfold YG0d.spZ. rewrite SPA, rp_w64u by lia. numconst. lia. }
    assert (PRS5' : forall a, bv_unsigned (getr regs 2%bv) - PR_STK <= a < bv_unsigned (getr regs 2%bv) -> apresent (w_H W') mem5 a).
    { intros a Ha. destruct (Z_le_dec (bv_unsigned (getr regs 2%bv) - 1152) a) as [A1|A1];
        [destruct (Z_lt_dec a (bv_unsigned (getr regs 2%bv) - 640)) as [A2|A2]|].
      - apply PRS5. unfold YG0d.spZ. rewrite SPA. numconst. lia.
      - destruct (PR4 a (P_stk a Ha)) as [Hh [b Hb]]. split.
        + destruct (w_H W' (Z_to_bv 64 a)) eqn:Eh; [|reflexivity]. unfold wle, hsub in WLE5.
          rewrite (WLE5 _ Eh) in Hh. discriminate.
        + exists b. rewrite <- Hb. apply MK5; numconst; lia.
      - destruct (PR4 a (P_stk a Ha)) as [Hh [b Hb]]. split.
        + destruct (w_H W' (Z_to_bv 64 a)) eqn:Eh; [|reflexivity]. unfold wle, hsub in WLE5.
          rewrite (WLE5 _ Eh) in Hh. discriminate.
        + exists b. rewrite <- Hb. apply MK5; numconst; lia. }
    apply (amreal_SRr_pre tfibsegs _ W' _ Q
      (fun W'' c'' => W'' = W' /\ exists regs6 mem6 mat6,
         regs_preserved regs regs6 /\
         (forall x : word, ~ (bv_unsigned (getr regs 2%bv) - PR_STK <= bv_unsigned x < bv_unsigned (getr regs 2%bv)) -> mem6 x = mem5 x) /\
         (forall a, apresent (w_H W') mem5 a -> apresent (w_H W') mem6 a) /\
         c'' = cfg_at tfibsegs (raZ regs) regs6 mem6 (with_vm_backing (m_vm_lazy md5) mat6 md5))).
    * (* the tail run *)
      assert (HS4' : st_ok tfibsegs E4 (P3end out) (restrict (w_H W') ms4))
        by exact (st_ok_wle tfibsegs W W' E4 (P3end out) ms4 WLE5 HS4).
      assert (RK5 : Forall (region_kept tfibsegs E4 (mrestrict (w_H W') (ms_mem ms4))
                              (mrestrict (w_H W') mem5)) P4keep).
      { pose proof (bE2 regs E4 HE4) as HB4. cbn [base_val] in HB4.
        cbn [P4keep].
        repeat (apply Forall_cons;
          [ split;
            [ intros a Ha; apply mbyte_mrestrict_same;
              unfold R_NB3, R_TOP3 in Ha;
              cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite ?HB4 in Ha;
              apply MK5; unfold spZ in *; numconst; lia
            | intros a Ha Hw; apply (writable_at_eq tfibsegs (mrestrict (w_H W') (ms_mem ms4))
                (mrestrict (w_H W') mem5) a);
              [ unfold mrestrict; unfold R_NB3, R_TOP3 in Ha;
                cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?HB4 in Ha;
                rewrite MK5 by (unfold spZ in *; numconst; lia); reflexivity
              | exact Hw ] ] | ]).
        apply Forall_nil. }
      pose proof (st_ok_after_stretch tfibsegs 51 E4 (P3end out) (restrict (w_H W') ms4) regs5
        (mrestrict (w_H W') mem5) P4keep 0x68640 CLOBP HS4' eq_refl (P3end_atoms out)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(cbn [ss_mem P3end P3tail app]; do 3 apply submem_drop;
              apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
              do 2 apply submem_drop; apply submem_nil)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(intros r Hr; cbn [ms_regs restrict]; exact (clobp_pres (ms_regs ms4) regs5 AR5 r Hr)) RK5) as HS5.
      set (E5 := havoc E4 51 (map (getr regs5) CLOBP)) in HS5.
      assert (HE5 : env32 regs E5) by (apply env32_havoc; [exact HE4 | lia]).
      pose proof (bE2 regs E5 HE5) as HB5. cbn [base_val] in HB5.
      rewrite <- restrict_mkst_fx in HS5.
      assert (CELL : forall a (w : nat) v,
        YF0x.cell_lookup (Tfib_const ly') (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
        0 <= a -> a + Z.of_nat w <= TFIB_IMG_END -> val_mem tfibsegs (mrestrict (w_H W') mem5) a w v).
      { intros a w v Hlk Ha Haw.
        apply (val_mem_frame (w_H W') (held_mem lk mem5) mem5 a w v).
        - intros k Hk. symmetry. apply (held_img lk ly' mem5 (a + Z.of_nat k) LY' LKO'). lia.
        - exact (const_val ly' S' Hp W' (held_mem lk mem5) md5 a w v TS AR' Hlk). }
      assert (HSx : st_ok tfibsegs E5 (P4s out)
        (restrict (w_H W') (mkst regs5 (w64 0x68640) mem5 (seg_rom tfibsegs)))).
      { unfold P4s.
        apply (st_ok_add_region E5 _ _ R_SYSLOG); [| vm_compute; reflexivity | |].
        - apply (st_ok_add_region E5 _ _ R_CFG); [| vm_compute; reflexivity | |].
          + apply (st_ok_add_region E5 _ _ R_LOW HS5 ltac:(vm_compute; reflexivity)).
            * cbn [ms_mem restrict mkst].
              apply (region_ok_window E5 (mrestrict (w_H W') mem5) 2%nat (bv_unsigned (getr regs 2%bv)));
                [exact HB5 | numconst; lia | numconst; lia |].
              intros a Ha. apply apresent_writable; [numconst; lia|]. apply PRS5'. numconst. lia.
            * apply all_disjoint_of_extents. unfold P4keep.
              unfold R_LOW, R_NB3, R_TOP3, extent_of_region.
              cbn [map ss_mem ss_after_stretch YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?HB5.
              cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; lia.
          + cbn [ms_mem restrict mkst]. unfold R_CFG.
            apply (region_ok_lit E5 (mrestrict (w_H W') mem5) 0xa2840 8 0x13d228);
              [apply CELL; [vm_compute; reflexivity | lia | unfold TFIB_IMG_END; cbn; lia]
              | cbn; lia | cbn; lia | lia | cbn; lia].
          + apply all_disjoint_of_extents.
            unfold P4keep. unfold R_CFG, R_LOW, R_NB3, R_TOP3, extent_of_region, lit8.
            cbn [map ss_mem addreg ss_after_stretch YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?HB5.
            cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; lia.
        - cbn [ms_mem restrict mkst]. unfold R_SYSLOG.
          apply (region_ok_lit E5 (mrestrict (w_H W') mem5) 0x13d268 8 0);
            [apply CELL; [vm_compute; reflexivity | lia | unfold TFIB_IMG_END; cbn; lia]
            | cbn; lia | cbn; lia | lia | cbn; lia].
        - apply all_disjoint_of_extents.
          unfold P4keep. unfold R_SYSLOG, R_CFG, R_LOW, R_NB3, R_TOP3, extent_of_region, lit8.
          cbn [map ss_mem addreg ss_after_stretch YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?HB5.
          cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. numconst. repeat split; lia. }
      rewrite (P4s_const out) in HSx.
      apply (to_ret ly regs LY Hsplo Hsphi W' E5
               (mkst regs5 (w64 0x68640) mem5 (seg_rom tfibsegs)) md5 _ HE5 Hra HSx).
      intros regs6 mem6 mat6 Hrp6 Hfr6 Hpr6.
      split; [reflexivity|]. exists regs6, mem6, mat6.
      split; [exact Hrp6|]. split; [exact Hfr6|]. split; [exact Hpr6 | reflexivity].
    * intros W2 c2 Hle2 (-> & regs6 & mem6 & mat6 & Hrp6 & Hfr6 & Hpr6 & ->).
      apply HK.
      apply (post_compose B lk (Z.of_nat (length out)) Hp ly S S' W W' regs mem md
               (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md) (ms_regs ms4) regs5 mem5 md5
               mem6 (with_vm_backing (m_vm_lazy md5) mat6 md5) regs6 PRE0).
      -- unfold errb_call_regs, YG0d.spZ.
         split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hra|]. split; [exact Hra4096|].
         split; [exact Hsp16|]. split; [exact Hsplo|]. split; [exact Hsphi | exact P_stk].
      -- exact FR4.
      -- intros a Ha. apply PR4. apply P_stk. exact Ha.
      -- apply same_io_wvb.
      -- unfold YG0d.spZ. rewrite SPA. numconst. lia.
      -- unfold YG0d.spZ. rewrite SPA. lia.
      -- exact HPost0.
      -- exact Hfr6.
      -- exact Hpr6.
      -- apply m_vmmaps_wvb.
      -- apply m_vm_lazy_wvb.
      -- apply eager_used_wvb.
      -- apply same_io_wvb.
      -- exact (aregs_of_regs_preserved regs regs6 Hrp6).
Qed.

End f.
End a.
