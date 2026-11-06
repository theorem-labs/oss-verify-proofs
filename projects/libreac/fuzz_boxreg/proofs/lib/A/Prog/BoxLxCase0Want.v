(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths and module names changed; 2249 of its 2361 lines of code are new or changed and 693 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxCase3.v, with its module paths and module names changed; 581 of its 624 lines of code are new or changed and 2318 lines of the source are left out. *)
(* The part of LLVMFuzzerTestOneInput's case 0 (fuzz_boxreg.c:226-238) on the ASan build from the cut N (0x80520,
   BoxLxCase0Defs.v: read_name returned the name in a0) to the cut W (0x8093c: `want` is in the spill slot 0x30).
   `mv s7, a0` keeps the name; `li a0, -1; sd a0, 0x30(s1)` stores want = -1; then four tests skip to 0x8093c with
   want = -1: fabric < nch (blt s9, s3 at 0x8052c), nch - 2 >u 38 (bltu at 0x80538), nch odd (andi / bnez at 0x80540)
   and n > 4 (ld a1, 0x48(s1); blt at 0x8054c). With base < 0 (bltz s10 at 0x80550) the walk calls
   lowest_free (&prev, nch, fabric) at 0x80934 (from 0x80928) and stores its result at 0x80938; else it calls
   range_free (&prev, base, nch, fabric) at 0x80564 and stores ((a0 != 0) - 1) | base (snez / addiw / or at
   0x80568 .. 0x80570, j 0x80938). &prev is the slot 0x78; both callees are composed with YC85.v cl_callS, their
   afobj premise from the frame (GB_CID, fp) and the zero shadow of prev (BoxLxSeat.v gb_prev_ra), the bytes of prev
   from gprev. Each path lands at W with c0w_land; Pau's c0_want comes from the branch facts (c0_wtest, c0_even,
   c0_lts56) and the callees' results. No branch of this stretch leads to a report or abort body. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b YC1g YC1h YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxLxDefs ReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import RangeFree LowestFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require read_name_c reac_boxreg_declare_c range_free_c lowest_free_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxSeat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The shadow base for the runner; the spill slot 0x30 (the one window the walk writes) and the slots it reads,
   n (0x48) and &prev (0x78), as the extra atoms 32 and 33. *)
Definition C0W_SB : Z := 0x7fff8000.
Definition C0W_R30 : YP09.region := YP09.mkRegion (Some 9%nat) 0x30 0x38 0x30 0x38 [].
Definition C0W_R48 : YP09.region := YP09.mkRegion (Some 9%nat) 0x48 0x80 0 0
  [YP09.mkChunk 0x48 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x78 (CVal 8 (SOff 33 0))].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TRANGEFREE : trange_free_spec B.
Hypothesis TLOWFREE : tlowest_free_spec B.

(* The callee-saved registers but s7 (x23), which the walk sets to the name. *)
Definition c0w_csl23 : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma c0w_cs_in23 : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 23 -> In r c0w_csl23.
Proof.
intros r H H23. rewrite <- (Z_to_bv_bv_unsigned _ r). unfold acallee_saved in H.
assert (Hc : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
  bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/
  bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
repeat (destruct Hc as [Hc|Hc]; [rewrite Hc; cbn [c0w_csl23 In]; repeat (first [left; apply bv_eq; reflexivity | right])|]).
rewrite Hc; cbn [c0w_csl23 In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* The landing at W: a state at 0x8093c whose callee-saved registers but s7 are those of N, s7 = the name, whose
   memory is N's outside the slot 0x30 on every byte N's facts speak about (gb_keep_at with r and the name's
   block), and whose slot 0x30 holds want for Pau's c0_want. *)
Lemma c0w_land : forall i POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) r bs pos op nm (regs : bvmap 5 word) mem md want,
  gb_from B MT POST (C0_W B MT i) ->
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c0_ms cx fp GC_N ms3 -> c0_turn B MT i cx fp k acc ly3 S3 W3 ms3 r bs pos op nm -> greg B ly3 S3 W3 ms3 r bs ->
  getr (ms_regs ms3) 19 = w64 (c0_nch cx pos) -> getr (ms_regs ms3) 22 = w64 op ->
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) ->
  getr (ms_regs ms3) 26 = w64 (c0_base cx pos * 2 ^ 56) -> getr (ms_regs ms3) 27 = w64 (c0_base cx pos) ->
  (forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> bv_unsigned r0 <> 23 -> getr regs r0 = getr (ms_regs ms3) r0) ->
  getr regs 23 = w64 nm ->
  (forall a, 0 <= a < 2 ^ 64 -> gb_keep_at cx fp [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] a ->
     ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) -> aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 0x30) = Some (want mod 2 ^ 64) ->
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nch cx pos) (c0_base cx pos) want -> -1 <= want < 128 ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + GC_W)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros i POST cx fp k acc ly3 S3 W3 ms3 r bs pos op nm regs mem md want
  HWc HB HJ HFR HMO HMS HT HREG R19 R22 R25 R26 R27 KP K23 KM S30 HWANT HWR.
pose proof HT as (HMF & Hi & Hk & Hacc & HBL & HINV & Hpos & HCUR & Hnm & HNAME & Hop & Hop3 & R20).
pose proof HMS as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
pose proof (c0_geo LAWS cx fp k ly3 S3 W3 mem md HB HJ HFR) as (Hinp & EgF & HF0 & HF1 & HF64 & HSH).
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _).
assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
assert (Hnmin : In (nm, c0_nk cx pos + 1) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hrin) as (_ & Hr4096 & Hrceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hnmin) as (_ & Hn4096 & Hnceil & _ & _ & _ & Hnk).
change (req_size REG_SIZE) with 288 in Hrceil.
pose proof (req_size_pos (c0_nk cx pos + 1) ltac:(lia)) as (_ & Hrq).
assert (HSHr : gSH cx fp + 64 <= alloc_ceiling).
{ rewrite HSH. unfold SHADOW_OFF. pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 (BASE + GC_W)) mem (seg_rom SEGS))) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. cbn [ms_mem mkst]. apply KM.
  - apply (c0_zone_range cx fp a Hinp HF0 HF1 HSH); [lia | exact Ha].
  - destruct Ha as [Ha|[Ha|[Ha|Ha]]]; unfold gb_keep_at.
    + left. lia.
    + right; left. exact Ha.
    + right; right; left. change (fs_frame_bytes GB_CID) with 512. exact Ha.
    + right; right; right; left. change (fs_frame_bytes GB_CID / 8) with 64. exact Ha.
  - destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia | lia]. }
assert (HMF2 : c0_mf i cx fp W3 (mkst regs (Z_to_bv 64 (BASE + GC_W)) mem (seg_rom SEGS)) r bs)
  by exact (c0_mf_keep2 i cx fp W3 W3 ms3 _ r bs HB KZ HMF).
assert (KB : forall b n j, In (b, n) [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] -> 0 <= j < n -> b + j < alloc_ceiling ->
  aview SEGS (w_H W3) mem (b + j) = aview SEGS (w_H W3) (ms_mem ms3) (b + j)).
{ intros b n j Hb Hj Hc. apply KM; [destruct Hb as [E1|[E1|[]]]; injection E1 as <- <-; unfold REG_SIZE in *; lia | |lia].
  unfold gb_keep_at. right; right; right; right. apply Exists_exists. exists (b, n). split; [exact Hb | cbn [fst snd]; lia]. }
eapply (HWc cx fp k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + GC_W)) mem (seg_rom SEGS)) md HB HJ HFR HMO).
exists r, bs, pos, op, nm, want.
destruct HCUR as (Hpos2 & C88 & C90).
destruct HREG as (Hrin' & HL & HRB).
split.
{ unfold c0_ms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. unfold gregs. cbn [ms_regs mkst].
  split; [rewrite KP; [exact G2 | c0_cs | cbv; lia]|]. split; [rewrite KP; [exact G8 | c0_cs | cbv; lia]|].
  split; [rewrite KP; [exact G9 | c0_cs | cbv; lia]|]. split; [rewrite KP; [exact G3 | c0_cs | cbv; lia]|].
  split; [rewrite KP; [exact G4 | c0_cs | cbv; lia]|]. split; [rewrite KP; [exact G18 | c0_cs | cbv; lia]|].
  rewrite KP; [exact G24 | c0_cs | cbv; lia]. }
split.
{ split; [exact HMF2|]. split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|].
  split; [exact HINV|]. split; [exact Hpos|].
  split; [split; [exact Hpos2|]; unfold gslot in *; cbn [ms_mem mkst]; split; [rewrite <- C88 | rewrite <- C90]; apply rdword_ext; intros j Hj; apply KM; unfold gb_keep_at; lia|].
  split; [exact Hnm|].
  split; [intros j Hj; cbn [ms_mem mkst]; rewrite (KB nm (c0_nk cx pos + 1) j) by (first [right; left; reflexivity | lia]); exact (HNAME j Hj)|].
  split; [exact Hop|]. split; [exact Hop3|].
  cbn [ms_regs mkst]. rewrite KP; [exact R20 | c0_cs | cbv; lia]. }
split.
{ split; [exact Hrin'|]. split; [exact HL|]. intros j Hj. cbn [ms_mem mkst].
  rewrite (KB r REG_SIZE j) by (first [left; reflexivity | unfold REG_SIZE in *; lia]). exact (HRB j Hj). }
split; [exact HWANT|]. split; [exact HWR|].
split; [unfold gslot; cbn [ms_mem mkst]; exact S30|].
cbn [ms_regs mkst].
split; [exact K23|].
split; [rewrite KP; [exact R19 | c0_cs | cbv; lia]|].
split; [rewrite KP; [exact R22 | c0_cs | cbv; lia]|].
split; [rewrite KP; [exact R25 | c0_cs | cbv; lia]|].
split; [rewrite KP; [exact R26 | c0_cs | cbv; lia]|].
rewrite KP; [exact R27 | c0_cs | cbv; lia].
Qed.

(* The write window of a run: the slot 0x30 of the spill area, inside the stack window of the journal. *)
Ltac c0w_awr cx U9 := awr_ok_tac;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.

(* After a run: the memory is N's outside the slot 0x30 (M, carried from run to run by the run's frame_of). *)
Ltac c0w_keep cx W3 ms3 E U9 :=
  lazymatch goal with
  | M : forall a, 0 <= a < 2 ^ 64 -> _ -> aview _ _ (ms_mem ?msp) a = _,
    HF : frame_of _ _ (ms_mem ?msp) (ms_mem ?msn) |- _ =>
    let M' := fresh "M" in
    assert (M' : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) ->
               aview SEGS (w_H W3) (ms_mem msn) a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a Ha Hw; transitivity (aview SEGS (w_H W3) (ms_mem msp) a); [|exact (M a Ha Hw)];
          apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha); unfold in_wrange;
          cbn [ss_mem add_cond];
          intros (rr & [<- | [<- | []]] & Hb); try unfold C0W_R30, C0W_R48 in Hb;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; [rewrite U9 in Hb|]; lia);
    clear M HF; rename M' into M
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* A skip to W with want = -1 (the slot 0x30 holds the -1 stored at 0x80528): run to 0x8093c and land. *)
Ltac c0w_exit cx W3 ms3 E U9 EE R10 HAE :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1) GC_W; [c0w_awr cx U9 |] end;
  c0w_keep cx W3 ms3 E U9;
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msn), M : forall a, 0 <= a < 2 ^ 64 -> _ -> _ |- _ =>
    let KP := fresh "KP" in let T23 := fresh "T23" in let HR30 := fresh "HR30" in let S30 := fresh "S30" in
    assert (KP : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> bv_unsigned r0 <> 23 ->
                   getr (ms_regs msn) r0 = getr (ms_regs ms3) r0)
      by (intros r0 Hr H23; exact (regs_kept_of_st_ok_pi E _ (restrict (w_H W3) msn) (ms_regs ms3) _ c0w_csl23 HS HAE
                                     ltac:(vm_compute; reflexivity) r0 (c0w_cs_in23 r0 Hr H23)));
    prreg HS (23%bv : bv 5) T23; rewrite (EE 10%nat 10%bv eq_refl), R10 in T23;
    pose proof (st_ok_pi_region_nth E _ _ 0%nat _ HS eq_refl) as HR30; cbn [ms_mem restrict] in HR30;
    assert (S30 : rdword (aview SEGS (w_H W3) (ms_mem msn)) (c_sp1 cx + 0x30) = Some ((-1) mod 2 ^ 64))
      by (change ((-1) mod 2 ^ 64) with 18446744073709551615;
          apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msn)); [|lia];
          apply (field_of_region E _ 9%nat (c_sp1 cx) _ 48 56 48 56 48 8%N (SLit 18446744073709551615) 18446744073709551615 HR30 U9);
          [left; reflexivity | reflexivity | cbn; lia | cbn; lia]);
    pmkst HS;
    eapply c0w_land with (want := -1) (regs := ms_regs msn) (mem := ms_mem msn);
    [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
    | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
    | exact KP | exact T23 | exact (fun a Ha _ Hw => M a Ha Hw) | exact S30 | | lia ]
  end.

(* The decided branches: a signed test of two small words, and nch & 1 = 0. *)
Lemma c0w_br_lt : forall E a b va vb, sv_denot E a = Z_to_bv 64 va -> sv_denot E b = Z_to_bv 64 vb ->
  - 2 ^ 63 <= va < 2 ^ 63 -> - 2 ^ 63 <= vb < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (va <? vb).
Proof. intros E a b va vb Ha Hb Hva Hvb. cbn [branch_taken]. rewrite Ha, Hb. apply Boxreg.lts_lit; lia. Qed.

Lemma c0w_and1 : forall k, 0 <= k < 2 ^ 64 ->
  bv_eqb (alu64 ALU_AND (Z_to_bv 64 k) (Z_to_bv 64 1)) (Z_to_bv 64 0) = (k mod 2 =? 0).
Proof.
intros k Hk. unfold alu64. cbn [alu]. unfold bv_eqb. rewrite bv_and_unsigned.
change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
rewrite BoxregStep.bx_land1 by exact Hk. reflexivity.
Qed.

Theorem c0_want_ok : forall i POST, gb_from B MT POST (C0_W B MT i) -> gb_from B MT POST (C0_N B MT i).
Proof.
intros i POST HW cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & pos & op & nm & HMS & HT & HREG & R10 & R19 & R22 & R25 & R26 & R27).
pose proof HT as (HMF & Hi & Hk & Hacc & HBL & HINV & Hpos & HCUR & Hnm & HNAME & Hop & Hop3 & R20).
pose proof HMF as (HSV & HSH & HFL & HFR5 & HIN & HPV & HSR & S68 & S48).
pose proof HFR5 as (F18 & F28 & F70 & F78 & F80).
pose proof HMS as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hsplo & Hsphi & Hsp1).
pose proof (gb_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & _ & _ & HSHeq).
pose proof asan_consts as (C1 & _).
pose proof HINV as ((HL288 & HB1 & HB2 & HB3 & _) & _).
unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in HB1, HB2.
set (nb := Boxreg.bx_n bs) in *. set (fab := Boxreg.bx_fabric bs) in *.
set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 nb; Z_to_bv 64 (gF cx fp + GO_PREV)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (E32 : ew E 32 = Z_to_bv 64 nb) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (gF cx fp + GO_PREV)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).

assert (DR : forall q (rr : bv 5) v, Z.of_nat q = bv_unsigned rr -> getr (ms_regs ms3) rr = w64 v -> sv_denot E (SOff q 0) = Z_to_bv 64 v)
  by (intros q rr v Hq Hv; rewrite c0_denot_off0, (EE q rr Hq), Hv; reflexivity).
assert (ER : forall q (rr : bv 5) v, Z.of_nat q = bv_unsigned rr -> getr (ms_regs ms3) rr = w64 v -> ew E q = Z_to_bv 64 v)
  by (intros q rr v Hq Hv; rewrite (EE q rr Hq), Hv; reflexivity).
assert (Hnch : 0 <= c0_nch cx pos < 256) by apply LLVMFuzzerTestOneInput_case0.c0_nch_range.
assert (Hbase : -128 <= c0_base cx pos < 128) by apply LLVMFuzzerTestOneInput_case0.c0_base_range.
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [Z_to_bv 64 nb; Z_to_bv 64 (gF cx fp + GO_PREV)]) E)
  by (split; [intros q Hq; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (M : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by reflexivity.

pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (HS : st_ok_pi SEGS VAL E (mkSS GC_N sr_atoms [C0W_R30; C0W_R48] None (mkFacts [(9%nat, mkAF 140735332483072 140737488355328 5)] [] [])) (restrict (w_H W3) ms3)).
{ rewrite (c0_mkst cx fp GC_N ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, C0W_R30. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold GB_STK. lia.
    + unfold region_ok, C0W_R48. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS _ _ _ 0x48 8%N (SOff 32 0) nb); [rewrite c0_denot_off0; exact E32 | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S48.
      * apply (chunk_ok_val SEGS _ _ _ 0x78 8%N (SOff 33 0) (gF cx fp + GO_PREV)); [rewrite c0_denot_off0; exact E33 | cbn; unfold GO_PREV; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact F78.
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, C0W_R30, C0W_R48. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9. lia.
  - cbn. split; [|split; exact I]. split; [|exact I]. unfold afact_ok. rewrite U9. pose proof (gb_sp1_al B MT cx HB) as Hal32. cbn [af_lo af_hi af_al2]. change (2 ^ 5) with 32.
    split; [lia|]. split; [exact Hal32 | lia]. }
assert (SHOK : sh_ok SEGS (SLit C0W_SB) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.

paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1); [c0w_awr cx U9 |].
c0w_keep cx W3 ms3 E U9.
psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1);
rewrite (c0w_br_lt E _ _ fab (c0_nch cx pos) (DR 25%nat 25%bv _ eq_refl R25) (DR 19%nat 19%bv _ eq_refl R19)) in Hc by lia.
- (* fabric < nch: want = -1 *)
  apply Z.ltb_lt in Hc.
  c0w_exit cx W3 ms3 E U9 EE R10 HAE.
  left. split; [|reflexivity]. intros ((_ & _ & Hle) & _). lia.

- (* nch <= fabric *)
  apply Z.ltb_ge in Hc. rename Hc into Hc1.
  paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1); [c0w_awr cx U9 |].
  c0w_keep cx W3 ms3 E U9.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1).

  all: change (sv_denot E (SLit 38)) with (Z_to_bv 64 38) in Hc;
    rewrite (c0_denot_off_val E 19 (c0_nch cx pos) (-2) (ER 19%nat 19%bv _ eq_refl R19)) in Hc by lia;
    cbn [branch_taken] in Hc; rewrite LLVMFuzzerTestOneInput_case0.c0_wtest in Hc by lia.
  + (* nch outside 2 .. 40: want = -1 *)
    c0w_exit cx W3 ms3 E U9 EE R10 HAE.
    left. split; [|reflexivity]. intros ((_ & Hr & _) & _).
    destruct (Z.leb_spec 2 (c0_nch cx pos)), (Z.leb_spec (c0_nch cx pos) 40); cbn in Hc; try discriminate; lia.

  + (* 2 <= nch <= 40 *)
    apply negb_false_iff in Hc. apply andb_true_iff in Hc. destruct Hc as (Hw1 & Hw2). apply Z.leb_le in Hw1, Hw2.
    paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1); [c0w_awr cx U9 |].
    c0w_keep cx W3 ms3 E U9.
    psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1).

    all: cbn [branch_taken sv_denot] in Hc; rewrite (ER 19%nat 19%bv _ eq_refl R19), unsigned_lit_small, Z.add_0_r, c0w_and1 in Hc by lia.
    * (* nch odd: want = -1 *)
      c0w_exit cx W3 ms3 E U9 EE R10 HAE.
      left. split; [|reflexivity]. intros ((Hev & _) & _). apply LLVMFuzzerTestOneInput_case0.c0_even_mod in Hev.
      rewrite Hev in Hc. discriminate Hc.
    * (* nch even *)
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hc3.
      paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1); [c0w_awr cx U9 |].
      c0w_keep cx W3 ms3 E U9.
      psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1).

      all: rewrite (c0w_br_lt E (SLit 4) (SOff 32 0) 4 nb eq_refl ltac:(rewrite c0_denot_off0; exact E32)) in Hc by lia.
      -- (* n > 4: want = -1 *)
        apply Z.ltb_lt in Hc.
        c0w_exit cx W3 ms3 E U9 EE R10 HAE.
        left. split; [|reflexivity]. intros (_ & Hn5). fold nb in Hn5. lia.
      -- (* n <= 4 *)
        apply Z.ltb_ge in Hc. rename Hc into Hc4.
        paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1); [c0w_awr cx U9 |].
        c0w_keep cx W3 ms3 E U9.
        psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1).

        all: cbn [branch_taken] in Hc; rewrite (DR 26%nat 26%bv _ eq_refl R26) in Hc;
          change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc; rewrite LLVMFuzzerTestOneInput_case0.c0_lts56 in Hc by lia.
        ++ (* base < 0: lowest_free (&prev, nch, fabric) *)
          apply Z.ltb_lt in Hc. rename Hc into Hc5.
          paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1); [c0w_awr cx U9 |].
          c0w_keep cx W3 ms3 E U9.

          pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
          pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & EgF & HF0' & HF1' & HF64 & HSH').
          assert (ZR : forall a, c0_zone cx fp a -> 0 <= a < 2 ^ 64) by (intros a; apply c0_zone_range; first [exact Hinp | lia | exact HSH']).
          assert (ZW : forall a, c0_zone cx fp a -> ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38)).
          { intros a Ha. pose proof (c0_sp cx HB) as (Hsp' & _). unfold GB_STK in Hsp'.
            destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia |].
            rewrite HSH' in Ha. unfold SHADOW_OFF in Ha. pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
          lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msn) |- _ =>
            assert (HMF1 : c0_mf i cx fp W3 msn r bs)
              by (apply (c0_mf_keep2 i cx fp W3 W3 ms3 msn r bs HB); [intros a Ha; exact (M a (ZR a Ha) (ZW a Ha)) | exact HMF]);
            assert (KP1 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> bv_unsigned r0 <> 23 -> getr (ms_regs msn) r0 = getr (ms_regs ms3) r0)
              by (intros r0 Hr H23; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msn) (ms_regs ms3) _ c0w_csl23 HS HAE ltac:(vm_compute; reflexivity) r0 (c0w_cs_in23 r0 Hr H23)))
          end.
          prreg HS (23%bv : bv 5) T23. rewrite (EE 10%nat 10%bv eq_refl), R10 in T23.
          pmkst HS.
          prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
          prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
          rewrite pa_sigma_lowest_free.

          assert (Usp : spZ (ms_regs ms1) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
          pose proof (c0_sp cx HB) as (Hsp & _ & Hsp32 & _). unfold GB_STK in Hsp.
          assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx))
            by (apply (c0_achain cx fp k ly3 S3 W3 _ _ _ HB HJ); [exact (proj1 HMF1) | lia]).
          assert (HOBJ : afobj SEGS B ly3 S3 W3 (ms_mem ms1) (gF cx fp + GO_PREV) REG_SIZE).
          { split; [|split].
            - exists GB_CID, fp. rewrite HFR, EgF. split; [left; reflexivity|]. change (fs_frame_bytes GB_CID) with 512.
              unfold GB_CID, GO_PREV, REG_SIZE. split; [lia|]. split; [|lia].
              apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF64; [|lia]. destruct HF64 as [q Hq]. exists (8 * q). lia.
            - unfold GO_PREV. apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF64; [|lia]. destruct HF64 as [q Hq]. exists (8 * q + 8). lia.
            - pose proof (gb_prev_ra B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ HFR 0 REG_SIZE (proj1 (proj2 HMF1)) ltac:(lia) ltac:(lia)) as HRA.
              rewrite Z.add_0_r in HRA. exact HRA. }
          eapply SRr_bind.
          { eapply (cl_callS B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
                [(GB_CID, fp)] ly3 S3 _ k LOWEST_FREE_STK [] 0 (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 2540)) (gch cx)
                (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
                   exists z, getr regs2 10 = w64 z /\ lowest_free_c.lowest_free_res bs (c0_nch cx pos) fab z) HJ).
            - rewrite Usp. lia.
            - apply c0_sub_mod16; [exact Hsp32 | exact Hal16].
            - lia.
            - change LOWEST_FREE_STK with 4176. lia.
            - change LOWEST_FREE_STK with 4176. unfold GB_STK. lia.
            - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
            - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
            - exact Q1.
            - apply ret_ok_codeptr_v; [lia | reflexivity].
            - rewrite unsigned_lit_small by lia. lia.
            - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
              replace (s0Z (ms_regs ms1)) with (spZ (c_regs cx))
                by (unfold s0Z; rewrite Q8, (EE 8%nat 8%bv eq_refl), G8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
              exact HCH.
            - intros HPRE1. eapply SRr_mono.
              + pose proof (TLOWFREE ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ (gch cx) (gF cx fp + GO_PREV) (c0_nch cx pos) fab bs HPRE1) as HC.
                unfold cfg_at, A_lowest_freeP, w64 in HC. eapply HC.
                * rewrite Q10, E33. reflexivity.
                * rewrite Q11, (ER 19%nat 19%bv _ eq_refl R19). reflexivity.
                * rewrite Q12, (ER 25%nat 25%bv _ eq_refl R25). reflexivity.
                * lia.
                * lia.
                * exact HOBJ.
                * exact HL288.
                * exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HMF1)))))).
                * exact HB1.
                * exact HB2.
                * exact HB3.
              + cbv beta. intros Wq cq _ (lyq & Sq & regsq & memq & mdq & -> & HJ1 & HP & HQ).
                exists lyq, Sq, regsq, memq, mdq. split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HQ]]].
            - intros a Ha. exfalso. exact (inFP_nil a Ha). }
          cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & z & Hz & Hres)).

          rewrite Z.add_0_r in HJ2.
          replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
          pose proof HJ as (HAR3 & _).
          assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
          assert (Hnmin : In (nm, c0_nk cx pos + 1) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
          destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hnmin) as (_ & _ & _ & _ & _ & _ & Hnk).
          pose proof (gb_keep_call B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ HFR [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] LOWEST_FREE_STK
            (ms_mem ms1) _ mem2 md2 0 ltac:(lia) ltac:(intros p n Hp; rewrite HBL; apply in_or_app; left; exact Hp)
            ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
                  [exists REG_SIZE; split; [exact Hrin | change (req_size REG_SIZE) with 288; unfold REG_SIZE; lia]
                  | exists (c0_nk cx pos + 1); split; [exact Hnmin | pose proof (req_size_pos (c0_nk cx pos + 1) ltac:(lia)); lia]])
            HJc) as KC.
          assert (MK : forall a, 0 <= a < 2 ^ 64 -> gb_keep_at cx fp [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] a ->
                    ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a)
            by (intros a Ha Hka Hw; rewrite (KC a Hka); exact (M a Ha Hw)).
          assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms1) r0)
            by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
          clear KC HJc HCH HOBJ.
          set (E2 := Eimg (Ereg regs2 [])).
          assert (HEIq : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
          assert (EE2 : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E2 q = getr regs2 r)
            by (intros q r0 Hq; subst E2; apply ew_Eimg_Ereg_nat; exact Hq).
          assert (U92 : bv_unsigned (ew E2 9) = c_sp1 cx)
            by (rewrite (EE2 9%nat 9%bv eq_refl), KP2, KP1, G9 by (first [c0_cs | cbv; lia]); apply unsigned_lit_small; lia).
          pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
          assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS 2540 sr_atoms [C0W_R30] None (mkFacts [(9%nat, mkAF 140735332483072 140737488355328 5)] [] []))
            (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + 2540)) mem2 (seg_rom SEGS)))).
          { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
            - apply regs_ok_Eimg_Ereg.
            - vm_compute. reflexivity.
            - apply Forall_cons; [|apply Forall_nil].
              unfold region_ok, C0W_R30. cbv zeta.
              cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U92.
              split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
              intros o Ho. apply (apresent_writable SEGS). apply HJpres2. unfold GB_STK. lia.
            - cbn [YP09.pairwise_disjoint]. split; exact I.
            - cbn. split; [|split; exact I]. split; [|exact I]. unfold afact_ok. rewrite U92. pose proof (gb_sp1_al B MT cx HB) as Hal32.
              cbn [af_lo af_hi af_al2]. change (2 ^ 5) with 32. split; [lia|]. split; [exact Hal32 | lia]. }
          assert (SHOK2 : sh_ok SEGS (SLit C0W_SB) [] E2 (mrestrict (w_H W3) mem2)) by constructor.
          clear HS SHOK.
          paj_run_to_tok (paj_run_to B LAWS) HS2 HJ2 SHOK2 (C0W_SB, C0W_SB + 2 ^ 44 - 1) GC_W;
            [ awr_ok_tac; eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
              [reflexivity | rewrite U92; lia | cbn; unfold GB_STK; lia | cbn; lia |]; apply awr_ok_nil |].

          assert (MKf : forall a, 0 <= a < 2 ^ 64 -> gb_keep_at cx fp [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] a ->
                    ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
          { intros a Ha Hka Hw. rewrite <- (MK a Ha Hka Hw). apply (c0_keep_outside E2 _ _ _ (w_H W3) a HF Ha). unfold in_wrange.
            cbn [ss_mem]. intros (rr & [<- | []] & Hb). unfold C0W_R30 in Hb. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
            rewrite U92 in Hb. lia. }
          clear HF HFr HG.
          assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (split; [intros q Hq; subst E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
          assert (KP3 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr (ms_regs ms) r0 = getr regs2 r0)
            by (intros r0 Hr; exact (regs_kept_of_st_ok_pi E2 _ (restrict (w_H W3) ms) regs2 _ c0_csl HS2 HAE2 ltac:(vm_compute; reflexivity) r0 (c0_cs_in r0 Hr))).
          assert (KPf : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> bv_unsigned r0 <> 23 -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
            by (intros r0 Hr H23; rewrite (KP3 r0 Hr), (KP2 r0 Hr); exact (KP1 r0 Hr H23)).
          assert (T23f : getr (ms_regs ms) 23 = w64 nm) by (rewrite (KP3 23%bv), (KP2 23%bv) by c0_cs; exact T23).
          pose proof (st_ok_pi_region_nth E2 _ _ 0%nat _ HS2 eq_refl) as HR30. cbn [ms_mem restrict] in HR30.
          assert (S30 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx + 0x30) = Some (z mod 2 ^ 64)).
          { apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|apply Z.mod_pos_bound; lia].
            apply (field_of_region E2 _ 9%nat (c_sp1 cx) _ 48 56 48 56 48 8%N (SOff 10 0) (z mod 2 ^ 64) HR30 U92).
            - left. reflexivity.
            - rewrite c0_denot_off0, (EE2 10%nat 10%bv eq_refl), Hz. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
              change (bv_modulus 64) with (2 ^ 64). symmetry. apply Z.mod_mod. lia.
            - cbn [Z.of_N]. change (8 * 8) with 64. apply Z.mod_pos_bound. lia.
            - cbn; lia. }
          pmkst HS2.
          eapply c0w_land with (want := z) (regs := ms_regs ms) (mem := ms_mem ms);
            [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
            | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
            | exact KPf | exact T23f | exact MKf | exact S30 | | ].
          ** right. right. split; [split; [apply LLVMFuzzerTestOneInput_case0.c0_even; exact Hc3 | lia]|].
             split; [fold nb; lia|]. split; [lia | exact Hres].
          ** destruct Hres as [(-> & _) | (Hz1 & _ & _)]; lia.

        ++ (* base >= 0: range_free (&prev, base, nch, fabric) *)
          apply Z.ltb_ge in Hc. rename Hc into Hc5.
          paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0W_SB, C0W_SB + 2 ^ 44 - 1); [c0w_awr cx U9 |].
          c0w_keep cx W3 ms3 E U9.

          pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
          pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & EgF & HF0' & HF1' & HF64 & HSH').
          assert (ZR : forall a, c0_zone cx fp a -> 0 <= a < 2 ^ 64) by (intros a; apply c0_zone_range; first [exact Hinp | lia | exact HSH']).
          assert (ZW : forall a, c0_zone cx fp a -> ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38)).
          { intros a Ha. pose proof (c0_sp cx HB) as (Hsp' & _). unfold GB_STK in Hsp'.
            destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia |].
            rewrite HSH' in Ha. unfold SHADOW_OFF in Ha. pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
          lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msn) |- _ =>
            assert (HMF1 : c0_mf i cx fp W3 msn r bs)
              by (apply (c0_mf_keep2 i cx fp W3 W3 ms3 msn r bs HB); [intros a Ha; exact (M a (ZR a Ha) (ZW a Ha)) | exact HMF]);
            assert (KP1 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> bv_unsigned r0 <> 23 -> getr (ms_regs msn) r0 = getr (ms_regs ms3) r0)
              by (intros r0 Hr H23; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msn) (ms_regs ms3) _ c0w_csl23 HS HAE ltac:(vm_compute; reflexivity) r0 (c0w_cs_in23 r0 Hr H23)))
          end.
          prreg HS (23%bv : bv 5) T23. rewrite (EE 10%nat 10%bv eq_refl), R10 in T23.
          pmkst HS.
          prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
          prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
          prreg HS (13%bv : bv 5) Q13. rewrite pa_sigma_range_free.

          assert (Usp : spZ (ms_regs ms1) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
          pose proof (c0_sp cx HB) as (Hsp & _ & Hsp32 & _). unfold GB_STK in Hsp.
          assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx))
            by (apply (c0_achain cx fp k ly3 S3 W3 _ _ _ HB HJ); [exact (proj1 HMF1) | lia]).
          assert (HOBJ : afobj SEGS B ly3 S3 W3 (ms_mem ms1) (gF cx fp + GO_PREV) REG_SIZE).
          { split; [|split].
            - exists GB_CID, fp. rewrite HFR, EgF. split; [left; reflexivity|]. change (fs_frame_bytes GB_CID) with 512.
              unfold GB_CID, GO_PREV, REG_SIZE. split; [lia|]. split; [|lia].
              apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF64; [|lia]. destruct HF64 as [q Hq]. exists (8 * q). lia.
            - unfold GO_PREV. apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF64; [|lia]. destruct HF64 as [q Hq]. exists (8 * q + 8). lia.
            - pose proof (gb_prev_ra B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ HFR 0 REG_SIZE (proj1 (proj2 HMF1)) ltac:(lia) ltac:(lia)) as HRA.
              rewrite Z.add_0_r in HRA. exact HRA. }
          eapply SRr_bind.
          { eapply (cl_callS B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
                [(GB_CID, fp)] ly3 S3 _ k RANGE_FREE_STK [] 0 (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 1564)) (gch cx)
                (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
                   ((range_free_c.range_free_ok bs (c0_base cx pos) (c0_nch cx pos) fab /\ getr regs2 10 = w64 1) \/
                    (~ range_free_c.range_free_ok bs (c0_base cx pos) (c0_nch cx pos) fab /\ getr regs2 10 = w64 0))) HJ).
            - rewrite Usp. lia.
            - apply c0_sub_mod16; [exact Hsp32 | exact Hal16].
            - lia.
            - change RANGE_FREE_STK with 4112. lia.
            - change RANGE_FREE_STK with 4112. unfold GB_STK. lia.
            - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
            - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
            - exact Q1.
            - apply ret_ok_codeptr_v; [lia | reflexivity].
            - rewrite unsigned_lit_small by lia. lia.
            - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
              replace (s0Z (ms_regs ms1)) with (spZ (c_regs cx))
                by (unfold s0Z; rewrite Q8, (EE 8%nat 8%bv eq_refl), G8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
              exact HCH.
            - intros HPRE1. eapply SRr_mono.
              + pose proof (TRANGEFREE ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ (gch cx) (gF cx fp + GO_PREV) (c0_base cx pos) (c0_nch cx pos) fab bs HPRE1) as HC.
                unfold cfg_at, A_range_freeP, w64 in HC. eapply HC.
                * rewrite Q10, E33. reflexivity.
                * rewrite Q11, (ER 27%nat 27%bv _ eq_refl R27). reflexivity.
                * rewrite Q12, (ER 19%nat 19%bv _ eq_refl R19). reflexivity.
                * rewrite Q13, (ER 25%nat 25%bv _ eq_refl R25). reflexivity.
                * lia.
                * lia.
                * lia.
                * exact HOBJ.
                * exact HL288.
                * exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HMF1)))))).
                * exact HB1.
                * exact HB2.
                * exact HB3.
              + cbv beta. intros Wq cq _ (lyq & Sq & regsq & memq & mdq & -> & HJ1 & HP & HQ).
                exists lyq, Sq, regsq, memq, mdq. split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HQ]]].
            - intros a Ha. exfalso. exact (inFP_nil a Ha). }
          cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & Hres)).

          rewrite Z.add_0_r in HJ2.
          replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
          pose proof HJ as (HAR3 & _).
          assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
          assert (Hnmin : In (nm, c0_nk cx pos + 1) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
          destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hnmin) as (_ & _ & _ & _ & _ & _ & Hnk).
          pose proof (gb_keep_call B MT LAWS cx fp W3 ms1 ly3 S3 _ k HB HJ HFR [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] RANGE_FREE_STK
            (ms_mem ms1) _ mem2 md2 0 ltac:(lia) ltac:(intros p n Hp; rewrite HBL; apply in_or_app; left; exact Hp)
            ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
                  [exists REG_SIZE; split; [exact Hrin | change (req_size REG_SIZE) with 288; unfold REG_SIZE; lia]
                  | exists (c0_nk cx pos + 1); split; [exact Hnmin | pose proof (req_size_pos (c0_nk cx pos + 1) ltac:(lia)); lia]])
            HJc) as KC.
          assert (MK : forall a, 0 <= a < 2 ^ 64 -> gb_keep_at cx fp [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] a ->
                    ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a)
            by (intros a Ha Hka Hw; rewrite (KC a Hka); exact (M a Ha Hw)).
          assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms1) r0)
            by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
          clear KC HJc HCH HOBJ.
          set (E2 := Eimg (Ereg regs2 [])).
          assert (HEIq : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
          assert (EE2 : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E2 q = getr regs2 r)
            by (intros q r0 Hq; subst E2; apply ew_Eimg_Ereg_nat; exact Hq).
          assert (U92 : bv_unsigned (ew E2 9) = c_sp1 cx)
            by (rewrite (EE2 9%nat 9%bv eq_refl), KP2, KP1, G9 by (first [c0_cs | cbv; lia]); apply unsigned_lit_small; lia).
          pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
          assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS 1564 sr_atoms [C0W_R30] None (mkFacts [(9%nat, mkAF 140735332483072 140737488355328 5)] [] []))
            (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + 1564)) mem2 (seg_rom SEGS)))).
          { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
            - apply regs_ok_Eimg_Ereg.
            - vm_compute. reflexivity.
            - apply Forall_cons; [|apply Forall_nil].
              unfold region_ok, C0W_R30. cbv zeta.
              cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U92.
              split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
              intros o Ho. apply (apresent_writable SEGS). apply HJpres2. unfold GB_STK. lia.
            - cbn [YP09.pairwise_disjoint]. split; exact I.
            - cbn. split; [|split; exact I]. split; [|exact I]. unfold afact_ok. rewrite U92. pose proof (gb_sp1_al B MT cx HB) as Hal32.
              cbn [af_lo af_hi af_al2]. change (2 ^ 5) with 32. split; [lia|]. split; [exact Hal32 | lia]. }
          assert (SHOK2 : sh_ok SEGS (SLit C0W_SB) [] E2 (mrestrict (w_H W3) mem2)) by constructor.
          clear HS SHOK.

          destruct Hres as [(HOK & Ha0) | (HNOK & Ha0)].
          *** (* range_free returned 1: want = base *)
            pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 1 HS2 ltac:(cbn [ms_regs restrict mkst]; exact Ha0) eq_refl) as HS3.
            clear HS2. rename HS3 into HS2. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_atoms] in HS2.
            paj_run_to_tok (paj_run_to B LAWS) HS2 HJ2 SHOK2 (C0W_SB, C0W_SB + 2 ^ 44 - 1) GC_W;
              [ awr_ok_tac; eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                [reflexivity | rewrite U92; lia | cbn; unfold GB_STK; lia | cbn; lia |]; apply awr_ok_nil |].

            assert (D30 : sv_denot E2 (SAlu ALU_OR (SLit 0) (SOff 27 0)) = Z_to_bv 64 (c0_base cx pos)).
            { cbn [sv_denot]. rewrite (EE2 27%nat 27%bv eq_refl), KP2, KP1, R27 by (first [c0_cs | cbv; lia]). unfold alu64. cbn [alu]. apply bv_eq.
              rewrite bv_or_unsigned. unfold w64. rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r, Z.lor_0_l.
              rewrite Z_to_bv_bv_unsigned. reflexivity. }

            assert (MKf : forall a, 0 <= a < 2 ^ 64 -> gb_keep_at cx fp [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] a ->
                      ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
            { intros a Ha Hka Hw. rewrite <- (MK a Ha Hka Hw). apply (c0_keep_outside E2 _ _ _ (w_H W3) a HF Ha). unfold in_wrange.
              cbn [ss_mem]. intros (rr & [<- | []] & Hb). unfold C0W_R30 in Hb. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
              rewrite U92 in Hb. lia. }
            clear HF HFr HG.
            assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (split; [intros q Hq; subst E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
            assert (KP3 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr (ms_regs ms) r0 = getr regs2 r0)
              by (intros r0 Hr; exact (regs_kept_of_st_ok_pi E2 _ (restrict (w_H W3) ms) regs2 _ c0_csl HS2 HAE2 ltac:(vm_compute; reflexivity) r0 (c0_cs_in r0 Hr))).
            assert (KPf : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> bv_unsigned r0 <> 23 -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
              by (intros r0 Hr H23; rewrite (KP3 r0 Hr), (KP2 r0 Hr); exact (KP1 r0 Hr H23)).
            assert (T23f : getr (ms_regs ms) 23 = w64 nm) by (rewrite (KP3 23%bv), (KP2 23%bv) by c0_cs; exact T23).
            pose proof (st_ok_pi_region_nth E2 _ _ 0%nat _ HS2 eq_refl) as HR30. cbn [ms_mem restrict] in HR30.

            assert (S30 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx + 0x30) = Some (c0_base cx pos mod 2 ^ 64)).
            { rewrite Z.mod_small by lia.
              apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
              apply (field_of_region E2 _ 9%nat (c_sp1 cx) _ 48 56 48 56 48 8%N (SAlu ALU_OR (SLit 0) (SOff 27 0)) (c0_base cx pos) HR30 U92);
                [left; reflexivity | exact D30 | cbn [Z.of_N]; lia | cbn; lia]. }
            pmkst HS2.
            eapply c0w_land with (want := c0_base cx pos) (regs := ms_regs ms) (mem := ms_mem ms);
              [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
              | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
              | exact KPf | exact T23f | exact MKf | exact S30 | | lia ].
            right. left. split; [split; [apply LLVMFuzzerTestOneInput_case0.c0_even; exact Hc3 | lia]|].
            split; [fold nb; lia|]. split; [lia|]. left. split; [exact HOK | reflexivity].

          *** (* range_free returned 0: want = -1 *)
            pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS2 ltac:(cbn [ms_regs restrict mkst]; exact Ha0) eq_refl) as HS3.
            clear HS2. rename HS3 into HS2. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_atoms] in HS2.
            paj_run_to_tok (paj_run_to B LAWS) HS2 HJ2 SHOK2 (C0W_SB, C0W_SB + 2 ^ 44 - 1) GC_W;
              [ awr_ok_tac; eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                [reflexivity | rewrite U92; lia | cbn; unfold GB_STK; lia | cbn; lia |]; apply awr_ok_nil |].

            assert (D31 : sv_denot E2 (SAlu ALU_OR (SLit 18446744073709551615) (SOff 27 0)) = Z_to_bv 64 18446744073709551615).
            { cbn [sv_denot]. unfold alu64. cbn [alu]. apply bv_eq. rewrite bv_or_unsigned.
              change (bv_unsigned (Z_to_bv 64 18446744073709551615)) with 18446744073709551615.
              rewrite LLVMFuzzerTestOneInput_case0.c0_lor1. reflexivity. }

            assert (MKf : forall a, 0 <= a < 2 ^ 64 -> gb_keep_at cx fp [(r, REG_SIZE); (nm, c0_nk cx pos + 1)] a ->
                      ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
            { intros a Ha Hka Hw. rewrite <- (MK a Ha Hka Hw). apply (c0_keep_outside E2 _ _ _ (w_H W3) a HF Ha). unfold in_wrange.
              cbn [ss_mem]. intros (rr & [<- | []] & Hb). unfold C0W_R30 in Hb. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
              rewrite U92 in Hb. lia. }
            clear HF HFr HG.
            assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (split; [intros q Hq; subst E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
            assert (KP3 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr (ms_regs ms) r0 = getr regs2 r0)
              by (intros r0 Hr; exact (regs_kept_of_st_ok_pi E2 _ (restrict (w_H W3) ms) regs2 _ c0_csl HS2 HAE2 ltac:(vm_compute; reflexivity) r0 (c0_cs_in r0 Hr))).
            assert (KPf : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> bv_unsigned r0 <> 23 -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
              by (intros r0 Hr H23; rewrite (KP3 r0 Hr), (KP2 r0 Hr); exact (KP1 r0 Hr H23)).
            assert (T23f : getr (ms_regs ms) 23 = w64 nm) by (rewrite (KP3 23%bv), (KP2 23%bv) by c0_cs; exact T23).
            pose proof (st_ok_pi_region_nth E2 _ _ 0%nat _ HS2 eq_refl) as HR30. cbn [ms_mem restrict] in HR30.

            assert (S30 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx + 0x30) = Some ((-1) mod 2 ^ 64)).
            { change ((-1) mod 2 ^ 64) with 18446744073709551615.
              apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
              apply (field_of_region E2 _ 9%nat (c_sp1 cx) _ 48 56 48 56 48 8%N (SAlu ALU_OR (SLit 18446744073709551615) (SOff 27 0)) 18446744073709551615 HR30 U92);
                [left; reflexivity | exact D31 | cbn [Z.of_N]; lia | cbn; lia]. }
            pmkst HS2.
            eapply c0w_land with (want := -1) (regs := ms_regs ms) (mem := ms_mem ms);
              [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
              | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
              | exact KPf | exact T23f | exact MKf | exact S30 | | lia ].
            right. left. split; [split; [apply LLVMFuzzerTestOneInput_case0.c0_even; exact Hc3 | lia]|].
            split; [fold nb; lia|]. split; [lia|]. right. split; [exact HNOK | reflexivity].
Qed.

End c.
End b.
End a.
