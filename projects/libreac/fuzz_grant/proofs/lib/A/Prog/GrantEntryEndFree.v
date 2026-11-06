(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryEndFree), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* The first half of the end phase of the walk of fuzz_grant's entry function
   LLVMFuzzerTestOneInput on the ASan build: the slots 0x817c8 .. 0x818b4, which end at
   the cut `GI_leave` (0x818b8).

   0x817c8 puts the head-amp table into a0 and 0x817cc calls the wrapper for free through
   its trampoline; the call is taken by its contract (`afree04_rule`), and it returns to
   0x817d0, the third free site of `GE_FSITES`. Then 55 one-byte stores through s6 mark
   the frame's objects unusable again (0xf8 in the frame's shadow bytes), and two loads
   put the frame back into s3 and s5.

   After the free the phase seats a symbolic state whose shadow region carries no chunk:
   the stores only need the write window [0, 104) of the frame's shadow, and the cut
   `GI_leave` asks only that some shadow list holds (`ge_land_ex`). The two spill slots
   the loads read hold the frame's address as the atom GA_F, so the state the engine runs
   on has no free variable. No slot of this cut branches, so no slot reaches the error
   path. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaRun PaShadow PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantACjr ACj1 GrantACja ACbf.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySeat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Ltac bvne := let Hq := fresh "Hq" in
  intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate.

Lemma gef_reg_other : forall (regs : bvmap 5 word) (rd : bv 5) (v : word) (r : bv 5),
  r <> rd -> getr (regupd regs rd v) r = getr regs r.
Proof. intros regs rd v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact Hr. Qed.

Lemma gef_reg_same : forall (regs : bvmap 5 word) (rd : bv 5) (v : word),
  bv_eqb rd 0 = false -> getr (regupd regs rd v) rd = v.
Proof. intros regs rd v H. unfold getr. rewrite H. apply regupd_same. Qed.

Lemma gef_rdword_keep : forall (rd rd' : reader) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
  intros rd rd' a v K Hr.
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* A word of a region, from the word the phase's invariant gives. *)
Lemma gef_chunk : forall (E : env) (H : word -> bool) (mem : word -> option byte) n sp off v,
bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
rdword (aview SEGS H mem) (sp + off) = Some v ->
YP09.chunk_ok SEGS E (mrestrict H mem) sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E H mem n sp off v Hn Hv Hr.
apply (chunk_ok_val SEGS E (mrestrict H mem) sp off 8 (SOff n 0) v).
- cbn [sv_denot]. rewrite Z.add_0_r, Hn. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn; lia.
- exact (val_mem_of_rdword SEGS _ _ _ _ Hr).
Qed.

(* An array of bytes is kept by a change of memory that keeps each of its bytes. *)
Lemma gef_garr8 : forall (H H' : word -> bool) (m m' : word -> option byte) p (l : list Z),
  (forall j, (j < length l)%nat -> aview SEGS H' m' (p + Z.of_nat j) = aview SEGS H m (p + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) p l -> garr8 SEGS (mrestrict H' m') p l.
Proof.
  intros H H' m m' p l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k Hkk. assert (k = 0)%nat by lia. subst k.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (mbyte_of_aview SEGS H H' m m' (p + Z.of_nat j) (HK j Hj)).
  exact Hv0.
Qed.

(* The registers of the state after the free: the five the body keeps (the realigned
   stack pointer in sp and s1, the caller's sp in s0, gp and tp), the frame's shadow
   base in s6, and one fresh atom N + i for every other register. *)
Definition gef_sr (N : nat) : list sv :=
  [SLit 0; SOff (N + 1) 0; SOff GA_SP1 0; SOff 3%nat 0; SOff 4%nat 0;
   SOff (N + 5) 0; SOff (N + 6) 0; SOff (N + 7) 0; SOff GA_SP 0; SOff GA_SP1 0;
   SOff (N + 10) 0; SOff (N + 11) 0; SOff (N + 12) 0; SOff (N + 13) 0; SOff (N + 14) 0;
   SOff (N + 15) 0; SOff (N + 16) 0; SOff (N + 17) 0; SOff (N + 18) 0; SOff (N + 19) 0;
   SOff (N + 20) 0; SOff (N + 21) 0; SOff GA_FSH 0; SOff (N + 23) 0; SOff (N + 24) 0;
   SOff (N + 25) 0; SOff (N + 26) 0; SOff (N + 27) 0; SOff (N + 28) 0; SOff (N + 29) 0;
   SOff (N + 30) 0; SOff (N + 31) 0].

Ltac gef_case Hat Ha2 Ha8 Ha9 Ha3 Ha4 Ha22 i :=
  lazymatch goal with |- getr ?rg ?rr = sv_denot ?Ex (sr_get ?srl ?rr2) =>
    let v := eval vm_compute in (sr_get srl rr2) in change (sr_get srl rr2) with v;
    first [ rewrite getr_zero; cbn [sv_denot]; reflexivity
          | rewrite ge_sv_SOff0; symmetry;
            first [ exact Ha2 | exact Ha8 | exact Ha9 | exact Ha3 | exact Ha4 | exact Ha22
                  | exact (Hat i rr ltac:(lia) ltac:(vm_compute; reflexivity)) ]
          | match goal with |- ?g => idtac "RO:" g end; fail ]
  end.

Lemma gef_regs_ok : forall (E : env) (N : nat) (regs : bvmap 5 word),
(forall (i : nat) (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r -> ew E (N + i)%nat = getr regs r) ->
ew E GA_SP1 = getr regs 2 -> ew E GA_SP = getr regs 8 -> ew E GA_SP1 = getr regs 9 ->
ew E 3%nat = getr regs 3 -> ew E 4%nat = getr regs 4 -> ew E GA_FSH = getr regs 22 ->
regs_ok E (gef_sr N) regs.
Proof.
intros E N regs Hat H2 H8 H9 H3 H4 H22.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 0%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 1%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 2%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 3%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 4%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 5%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 6%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 7%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 8%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 9%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 10%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 11%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 12%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 13%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 14%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 15%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 16%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 17%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 18%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 19%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 20%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 21%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 22%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 23%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 24%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 25%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 26%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 27%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 28%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 29%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 30%nat|].
destruct Hr as [<- | Hr]; [gef_case Hat H2 H8 H9 H3 H4 H22 31%nat|].
destruct Hr.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* The table is not a block of the caller: the blocks are disjoint position by position
   (AR_blocks_law), and the table's range is not empty. *)
Lemma gef_blk1_fresh : forall cx ly3 S3 W3 mem3 md3 t,
AR SEGS B ly3 S3 W3 mem3 md3 -> gblk1 B cx ly3 S3 t ->
~ In (t, 460) (ablocks B (c_ly cx) (c_S cx)).
Proof.
intros cx ly3 S3 W3 mem3 md3 t HAR Hg Hc.
apply in_split in Hc as (l1 & l2 & E1).
pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (t, 460) (t, 460) l1 l2 [] HAR) as Hd.
unfold gblk1 in Hg. rewrite Hg, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (Hr : req_size 460 = 460) by reflexivity. rewrite Hr in Hd. lia.
Qed.

(* Taking a block that is not in C out of C ++ [x] leaves C. *)
Lemma gef_remove_last_fresh : forall (C l1 l2 : list (Z * Z)) x,
~ In x C -> C ++ [x] = l1 ++ x :: l2 -> l1 ++ l2 = C.
Proof.
intros C l1 l2 x Hx E.
induction l2 as [|y l2' _] using rev_ind.
- rewrite app_nil_r. symmetry. exact (proj1 (app_inj_tail C l1 x x E)).
- exfalso.
  rewrite app_comm_cons, app_assoc in E.
  apply app_inj_tail in E as (E & ->).
  apply Hx. rewrite E. apply in_or_app. right. left. reflexivity.
Qed.

(* `ge_body` holds of a later machine state that keeps the bytes the body's facts read:
   the saved registers, the frame's shadow bytes, the frame's flag word and the input. *)
Lemma gef_body_keep : forall cx fp pc0 pc W ms W' ms' sh,
  ge_body cx fp pc0 W ms sh ->
  (forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) \/
             gSH cx fp <= a < gSH cx fp + Z.of_nat (length sh) \/
             gF cx fp + 1016 <= a < gF cx fp + 1024 \/
             c_p cx <= a < c_p cx + c_n cx ->
     aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_pc_val ms' = w64 (BASE + pc) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx ms' ->
  ge_body cx fp pc W' ms' sh.
Proof.
  intros cx fp pc0 pc W ms W' ms' sh HB HK Hpc Hrv Hsv Hrom Hfr Hfc Hrg.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & (Hra & Hs12) & Hsh & Hfl & Hlen & Hg).
  split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hfc|]. split; [exact Hrg|].
  split; [split|].
  { apply (gef_rdword_keep (aview SEGS (w_H W) (ms_mem ms))); [|exact Hra].
    intros i Hi. apply HK. left. lia. }
  { intros j Hj. apply (gef_rdword_keep (aview SEGS (w_H W) (ms_mem ms))); [|exact (Hs12 j Hj)].
    intros i Hi. apply HK. left. lia. }
  split.
  { intros i Hi. rewrite HK by (right; left; lia). exact (Hsh i Hi). }
  split.
  { apply (gef_rdword_keep (aview SEGS (w_H W) (ms_mem ms))); [|exact Hfl].
    intros i Hi. apply HK. right. right. left. lia. }
  split; [exact Hlen|].
  intros j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k0 Hk0. assert (k0 = 0)%nat by lia. subst k0.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
  rewrite length_map in Hj. unfold c_n in HK.
  assert (Hx : aview SEGS (w_H W') (ms_mem ms') (c_p cx + Z.of_nat j) =
               aview SEGS (w_H W) (ms_mem ms) (c_p cx + Z.of_nat j))
    by (apply HK; right; right; right; lia).
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') (ms_mem ms) (ms_mem ms') _ Hx).
  exact Hv0.
Qed.

(* The right to write the windows of this phase's regions: the spill slots on the
   machine stack, the frame, and the first 104 shadow bytes of the frame. *)
Lemma gef_awr : forall cx fp E sh scs fcs ly S lyc Sc,
  ew E GA_SP1 = Z_to_bv 64 (c_sp1 cx) -> ew E GA_F = Z_to_bv 64 (gF cx fp) ->
  ew E GA_FSH = Z_to_bv 64 (gSH cx fp) ->
  0 <= c_sp1 cx < 2 ^ 64 ->
  spZ (c_regs cx) - 319 <= c_sp1 cx <= spZ (c_regs cx) - 288 ->
  0 <= gF cx fp < 2 ^ 64 -> frame_addr lyc GE_CID fp = gF cx fp ->
  0 <= gSH cx fp < 2 ^ 64 -> gSH cx fp = shadow_addr (gF cx fp) ->
  awr_ok E (ge_regions cx fp sh scs fcs 0 104 []) GE_STK (spZ (c_regs cx)) []
    (ablocks B ly S) (ablocks B lyc Sc) lyc [(GE_CID, fp)].
Proof.
  intros cx fp E sh scs fcs ly S lyc Sc E60 E516 E529 Hsp1r Hsp1 HFr HFa HSr ESH.
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  unfold ge_regions, ge_regions0, ge_obj_regions. cbn [app].
  apply awr_ok_cons_ro; [unfold ge_saved_region; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ GA_SP1 (c_sp1 cx - spZ (c_regs cx)));
    [ unfold ge_spill_region; reflexivity
    | rewrite E60; rewrite unsigned_lit_small by lia; lia
    | unfold ge_spill_region; cbn [YP09.r_wlo]; unfold GE_STK; lia
    | unfold ge_spill_region; cbn [YP09.r_whi]; lia
    | ].
  apply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ GA_F (gF cx fp));
    [ unfold ge_frame_region, fframe_region; reflexivity
    | rewrite E516; apply unsigned_lit_small; lia
    | unfold ge_frame_region, fframe_region; cbn [YP09.r_wlo YP09.r_whi];
      intros a Ha; right; right; right; exists GE_CID, fp;
      split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
      rewrite HFa; rewrite Hfb in Ha |- *; lia
    | ].
  apply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ GA_FSH (gSH cx fp));
    [ unfold ge_shadow_region, fshadow_region; reflexivity
    | rewrite E529; apply unsigned_lit_small; lia
    | unfold ge_shadow_region, fshadow_region; cbn [YP09.r_wlo YP09.r_whi];
      intros a Ha; right; right; right; exists GE_CID, fp;
      split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
      rewrite HFa, Hfb; change (1024 / 8) with 128; rewrite <- ESH; lia
    | ].
  apply awr_ok_cons_ro; [unfold got_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold uar_got_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [unfold uar_cell_regionP; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
Qed.

(* 0x817c8 .. 0x818b4: the table is freed and the frame's objects are marked unusable
   again; the walk lands in the cut `GI_leave` at 0x818b8. *)
Theorem ge_end_free : forall POST, ge_from B MT POST (GI_leave B MT) -> ge_from B MT POST (GI_freeT B MT).
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HBASE HJ3 Hfrs3 HMLE HINV.
pose proof HBASE as (HPRE & Hp10 & Hp11 & Hpn & HPLc & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & Usp & E32c & HMOK & HTR & HNEED).
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & HpresW & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (PBASE : 0 <= BASE /\ BASE + 2 ^ 40 < 2 ^ 64 /\ BASE mod 4 = 0) by exact pa_B_ok.
assert (PBLO : 0x10000 <= BASE) by apply pa_base_lo.
assert (Hsegs : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd) by exact pa_segs_low.
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct HINV as (t & HBODY & Hk & Hacc & Hblk1 & Hn26 & R20 & R22 & HSLOTS).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HSHD & HFLW & Hlensh & HPLm).
pose proof HREGS as (Rsp & Rs0 & Rs1 & Rgp3 & Rtp3).
pose proof HSLOTS as (HSLmid & HSL8 & HSL32 & HSL40 & HSL72 & HSL80 & HSL104 & HSL112 & HSL128).
assert (Hfin3 : In (GE_CID, fp) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
pose proof (proj1 HJ3) as HAR3.
assert (HFF : 4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\
              in_app (gF cx fp) 1024 /\
              (gF cx fp + 1024 <= 0x10000 \/ 0x5fa000 <= gF cx fp) /\
              gSH cx fp = SHADOW_OFF + gF cx fp / 8)
  by (eapply ge_F_facts; eassumption).
pose proof HFF as (HF4096 & HFceil & HFinapp & HFimg & HSHeq).
assert (HSPF : spZ (c_regs cx) mod 16 = 0 /\
               alloc_ceiling + 32768 <= spZ (c_regs cx) /\
               spZ (c_regs cx) <= 2 ^ 47 /\
               spZ (c_regs cx) - 319 <= c_sp1 cx <= spZ (c_regs cx) - 288)
  by (eapply ge_sp_facts; eassumption).
pose proof HSPF as (Hspal & Hsplo & Hsphi & Hsp1b).
assert (EFAly3 : frame_addr ly3 GE_CID fp = gF cx fp)
  by (eapply ge_frame_addr_eq; eassumption).
assert (HFbv : 0 <= gF cx fp < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
assert (HSHbv : 0 <= gSH cx fp /\ gSH cx fp + 128 <= 2 ^ 64)
  by (eapply ge_sh_range; eassumption).
(* ---- the table: a block of its own, apart from the caller's blocks, the frame and
   the frame's shadow ---- *)
assert (ERQT : req_size 460 = 460) by reflexivity.
assert (FB : fs_frame_bytes GE_CID = 1024) by reflexivity.
assert (Hnotin : ~ In (t, 460) (ablocks B (c_ly cx) (c_S cx)))
  by exact (gef_blk1_fresh cx ly3 S3 W3 (ms_mem ms3) md3 t HAR3 Hblk1).
assert (Hint : In (t, 460) (ablocks B ly3 S3))
  by (unfold gblk1 in Hblk1; rewrite Hblk1; apply in_or_app; right; left; reflexivity).
destruct (al_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 t 460 HAR3 Hint)
  as (Ht16 & Ht4096 & Htceil & Htapp & _).
rewrite ERQT in Htceil, Htapp.
assert (DFt : gF cx fp + 1024 <= t \/ t + 460 <= gF cx fp).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 t 460 GE_CID fp HAR3 Hint Hfin3) as D.
  rewrite EFAly3, FB, ERQT in D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (ESH : gSH cx fp = shadow_addr (gF cx fp)) by (rewrite HSHeq; reflexivity).
pose proof (YCbq.shadow_addr_bounds (gF cx fp) ltac:(lia)) as (Hsb1 & _).
pose proof (YCbq.shadow_addr_bounds (gF cx fp + 1024) ltac:(lia)) as (_ & Hsb2).
pose proof (YCbq.shadow_range_end (gF cx fp) 1024 ltac:(lia)) as Hsre.
change (1024 / 8) with 128 in Hsre.
assert (DSHt : gSH cx fp + 128 <= t \/ t + 460 <= gSH cx fp).
{ rewrite ESH. destruct Htapp as (_ & [Hlo | (Hhi & _)]).
  - right. unfold kLowShadowBeg in Hlo. lia.
  - left. lia. }
assert (Dpt : c_n cx = 0 \/ c_p cx + c_n cx <= t \/ t + 460 <= c_p cx).
{ destruct Hpn as [(Hn0 & _) | (Hnpos & Hin0)]; [left; exact Hn0 | right].
  apply in_split in Hin0. destruct Hin0 as (m1 & m2 & Em).
  assert (Heq : ablocks B ly3 S3 = m1 ++ (c_p cx, c_n cx) :: m2 ++ (t, 460) :: []).
  { unfold gblk1 in Hblk1. rewrite Hblk1, Em, <- app_assoc. reflexivity. }
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx, c_n cx) (t, 460)
    m1 m2 [] HAR3 Heq) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite ERQT in D.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq). lia. }
(* ---- the mv at 0x817c8 ---- *)
assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_freeT)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
  destruct ms3 as [rg fr pcv svp rv fc mm rm];
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity. }
assert (Hslot0 : plookup (pl_tpi (L := grant_listing)) GP_freeT = Some (PW 656659))
  by (vm_compute; reflexivity).
rewrite <- (pl_tpi_eq (L := grant_listing)) in Hslot0.
pose proof (cert_slot gsym (clookup pa_tbl) VAL SIGMA grant_listing pa_cert _ _ Hslot0) as HCK0.
destruct HCK0 as (Hck0 & _ & _).
cbv beta iota zeta delta [pi_slot_check] in Hck0.
destruct (clookup pa_tbl (VAL A_TEXT + GP_freeT)) as [w0|] eqn:Hfw0; [|discriminate Hck0].
apply Z.eqb_eq in Hck0. subst w0.
destruct (decode_any (Z_to_bv 32 656659)) as [[i0 isz0]|] eqn:Hdec0.
2: { exfalso. vm_compute in Hdec0. discriminate. }
assert (Ei0 : i0 = OpImm ALU_ADD (Z_to_bv 5 10) (Z_to_bv 5 20) (Z_to_bv 12 0) /\ isz0 = 4%Z).
{ pose proof Hdec0 as H'. vm_compute in H'. injection H' as Ei Es. subst i0 isz0.
  split; [|reflexivity]. f_equal; apply bv_eq; vm_compute; reflexivity. }
destruct Ei0 as [-> ->].
assert (HSTEP0 : RiscvSemantics.step SEGS (restrict (w_H W3) ms3) =
  MachineOk (mkst (regupd (ms_regs ms3) (Z_to_bv 5 10) (getr (ms_regs ms3) (Z_to_bv 5 20)))
                  (Z_to_bv 64 (BASE + (GP_freeT + 4))) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
{ rewrite Ems3 at 1. rewrite restrict_mkst_fx.
  rewrite (step_addi_at SEGS (ms_regs ms3) (Z_to_bv 64 (BASE + GP_freeT)) (mrestrict (w_H W3) (ms_mem ms3))
    (seg_rom SEGS) (Z_to_bv 32 656659) (Z_to_bv 5 10) (Z_to_bv 5 20) (Z_to_bv 12 0)
    (getr (ms_regs ms3) (Z_to_bv 5 20)) (pa_fetch_ok _ _ Hfw0)
    (not_ecall_of_decode _ _ _ Hdec0 ltac:(discriminate)) Hdec0 ltac:(vm_compute; reflexivity)).
  2: { unfold v_addi. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite Z.add_0_r.
       apply Z_to_bv_bv_unsigned. }
  assert (Epc : v_addi (Z_to_bv 64 (BASE + GP_freeT)) 4 = Z_to_bv 64 (BASE + (GP_freeT + 4))).
  { unfold v_addi. rewrite unsigned_lit_small by (unfold GP_freeT; lia). f_equal. lia. }
  rewrite Epc. reflexivity. }
eapply (SRr_step SEGS pa_wx W3 ms3 _ md3); [exact Hsvc | exact HSTEP0 |].
intros model1 Hsame1.
rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb md3 model1 Hsame1).
(* ---- the jal at 0x817cc ---- *)
assert (Hslot1 : plookup (pl_tpi (L := grant_listing)) (GP_freeT + 4)
  = Some (PCall GS___interceptor_trampoline_free (1%bv : Prelude.reg))) by (vm_compute; reflexivity).
rewrite <- (pl_tpi_eq (L := grant_listing)) in Hslot1.
pose proof (cert_slot gsym (clookup pa_tbl) VAL SIGMA grant_listing pa_cert _ _ Hslot1) as HCK.
destruct HCK as (Hck & _ & _).
cbv beta iota zeta delta [pi_slot_check] in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + (GP_freeT + 4))) as [wz|] eqn:Hfw; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck. destruct Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck. destruct Hck as (Hck1 & Ht).
apply andb_prop in Hck1. destruct Hck1 as (Hrd & _).
apply reg_eqb_eq in Hrd. apply Z.eqb_eq in Ht. rewrite <- Hrd in Hdec.
assert (HSTEP1 : RiscvSemantics.step SEGS (restrict (w_H W3)
    (mkst (regupd (ms_regs ms3) (Z_to_bv 5 10) (getr (ms_regs ms3) (Z_to_bv 5 20)))
          (Z_to_bv 64 (BASE + (GP_freeT + 4))) (ms_mem ms3) (seg_rom SEGS))) =
  MachineOk (mkst (regupd (regupd (ms_regs ms3) (Z_to_bv 5 10) (getr (ms_regs ms3) (Z_to_bv 5 20)))
                     (1%bv : Prelude.reg) (Z_to_bv 64 (BASE + (GP_freeT + 8))))
                  (Z_to_bv 64 (pc_wrap_free (as_code B)))
                  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
{ rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS _ (Z_to_bv 64 (BASE + (GP_freeT + 4)))
    (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS) (Z_to_bv 32 wz) (1%bv : Prelude.reg) _
    (pa_fetch_ok _ _ Hfw) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  destruct (bv_eqb (1%bv : Prelude.reg) 0) eqn:Hx0; [vm_compute in Hx0; discriminate|].
  f_equal. f_equal.
  - f_equal. unfold v_addi. rewrite unsigned_lit_small by (unfold GP_freeT; lia).
    f_equal. unfold GP_freeT. lia.
  - unfold btgt, v_addi. rewrite unsigned_lit_small by (unfold GP_freeT; lia).
    rewrite <- (pal_free B TL), <- Ht. symmetry. apply lit_canon. }
eapply (SRr_step SEGS pa_wx W3 _ _ _); [reflexivity | exact HSTEP1 |].
intros model2 Hsame2.
rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb _ model2 Hsame2).
set (R2 := regupd (regupd (ms_regs ms3) (Z_to_bv 5 10) (getr (ms_regs ms3) (Z_to_bv 5 20)))
                  (1%bv : Prelude.reg) (Z_to_bv 64 (BASE + (GP_freeT + 8)))).
assert (RUPD : forall r : bv 5, r <> (1%bv : bv 5) -> r <> Z_to_bv 5 10 ->
  getr R2 r = getr (ms_regs ms3) r).
{ intros r H1 H10. unfold R2. rewrite gef_reg_other by exact H1.
  rewrite gef_reg_other by exact H10. reflexivity. }
assert (RRA : getr R2 (1%bv : bv 5) = Z_to_bv 64 (BASE + (GP_freeT + 8)))
  by (unfold R2; apply gef_reg_same; vm_compute; reflexivity).
assert (RA0 : getr R2 (Z_to_bv 5 10) = w64 t).
{ unfold R2. rewrite gef_reg_other by bvne.
  rewrite gef_reg_same by (vm_compute; reflexivity). exact R20. }
assert (RSP1 : spZ R2 = c_sp1 cx).
{ unfold spZ. rewrite (RUPD (2%bv : Prelude.reg) ltac:(bvne) ltac:(bvne)), Rsp. unfold w64.
  apply unsigned_lit_small. lia. }
assert (HJ2 : ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
   [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3)
   (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) (m_vm_materialized model1) md3))
      (m_vm_materialized model2) (with_vm_backing (m_vm_lazy md3) (m_vm_materialized model1) md3)) k).
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ3. }
assert (Hsp132 : c_sp1 cx mod 32 = 0).
{ rewrite Esp1. first [apply Z_mod_mult | rewrite Z.mul_comm; apply Z_mod_mult]. }
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ pose proof (proj1 (Z.mod_divide _ 32 ltac:(lia)) Hsp132) as (q & Hq).
  pose proof (proj1 (Z.mod_divide _ 16 ltac:(lia)) Hspal) as (r & Hr).
  rewrite Hq, Hr. replace (q * 32 - r * 16) with ((2 * q - r) * 16) by lia. apply Z_mod_mult. }
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
{ pose proof HJ3 as (_ & Hly3 & _).
  apply (achain_ly_top (c_ly cx) ly3);
    [destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et|].
  pose proof HSAVED as (Hra_sv & Hsv).
  eapply ge_achain.
  all: first
    [ exact HBASE
    | intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 a Ha)
    | exact Hra_sv
    | replace (spZ (c_regs cx) - 16) with (spZ (c_regs cx) - 16 - 8 * 0) by lia; exact (Hsv 0 ltac:(lia))
    | lia
    | eassumption ]. }
(* ---- the call of the wrapper for free: its contract asks that the table is a live
   block (`Hint`), that the call site is one the call trace allows (the third site of
   `GE_FSITES`), and that the table is not one of the caller's blocks (`Hnotin`); its
   own error path (an invalid or double free) is therefore not reached ---- *)
eapply SRr_bind.
{ eapply (AFREE4 W3 R2 (ms_mem ms3) GE_STK (spZ (c_regs cx)) (@nil (Z * Z))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k t 460
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + (GP_freeT + 8))) (gch cx) HJ2 Hint).
  - exact RA0.
  - rewrite RSP1. lia.
  - exact Ho16.
  - lia.
  - assert (Has : ASTACK = 16384) by reflexivity. rewrite Has, FFS. lia.
  - rewrite (RUPD (3%bv : Prelude.reg) ltac:(bvne) ltac:(bvne)), Rgp3. exact Hgp.
  - rewrite (RUPD (4%bv : Prelude.reg) ltac:(bvne) ltac:(bvne)), Rtp3. exact Htp.
  - exact RRA.
  - apply ret_ok_codeptr_v; [unfold GP_freeT; lia | reflexivity].
  - pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & Hk0 & _). unfold GE_EV in Hev. lia.
  - apply (achain_chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx) (spZ (c_regs cx))
      (gch cx) _ HCH).
    + rewrite RSP1. lia.
    + unfold s0Z. rewrite (RUPD (8%bv : Prelude.reg) ltac:(bvne) ltac:(bvne)), Rs0. unfold w64.
      apply unsigned_lit_small. lia.
    + unfold raZ. rewrite RRA, unsigned_lit_small by (unfold GP_freeT; lia). unfold GP_freeT. lia.
  - apply HTR. right. split; [reflexivity|].
    unfold raZ. rewrite RRA, unsigned_lit_small by (unfold GP_freeT; lia).
    replace (BASE + (GP_freeT + 8) - BASE) with (GP_freeT + 8) by lia.
    unfold GE_FSITES, GP_freeT. cbn [In]. right. right. left. reflexivity.
  - intros Hcon i Hi. exfalso. exact (Hnotin Hcon).
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL HMOK HMLE).
    + apply (mo_free_nonneg MT MTL).
    + unfold GE_NEED in HNEED. lia. }
cbv beta. intros W4 c4 Hwle4 Hpost.
destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hsplit & Hfrs4 & HK4 & MLE4).
(* ---- the blocks after the free: the caller's ---- *)
destruct Hsplit as (l1 & l2 & Eb3 & Eb4).
assert (Eab4 : ablocks B ly4 S4 = ablocks B (c_ly cx) (c_S cx)).
{ rewrite Eb4. apply (gef_remove_last_fresh _ _ _ (t, 460) Hnotin).
  unfold gblk1 in Hblk1. rewrite <- Hblk1. exact Eb3. }
assert (HFR4 : frames S4 = [(GE_CID, fp)]) by (rewrite Hfrs4; exact Hfrs3).
(* ---- the bytes the call kept ---- *)
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK4 by lia.
destruct HK4 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KEEP : forall a : Z,
  c_sp1 cx <= a < 2 ^ 64 \/ c_p cx <= a < c_p cx + c_n cx \/
  gF cx fp <= a < gF cx fp + 1024 \/ gSH cx fp <= a < gSH cx fp + 128 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - apply K1; lia.
  - destruct Hpn as [(Hn0 & _) | (Hnpos & Hin0)]; [exfalso; lia|].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (unfold gblk1 in Hblk1; rewrite Hblk1; apply in_or_app; left; exact Hin0).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq).
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hin3); [lia|]. rewrite ERQT. lia.
  - apply (K4 GE_CID fp a Hfin3).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFAly3, FB. lia.
    + rewrite ERQT. lia.
  - apply (K4 GE_CID fp a Hfin3).
    + right. unfold in_zr. cbn [fst snd]. rewrite EFAly3, FB.
      change (1024 / 8) with 128. rewrite <- ESH. lia.
    + rewrite ERQT. lia. }
(* ---- the registers the call kept ---- *)
assert (QP : forall r : Z, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP4 r Hr). apply RUPD.
  - intros Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite Z_to_bv_unsigned in Hq. unfold bv_wrap in Hq.
    change (bv_modulus 5) with 32 in Hq.
    rewrite Z.mod_small in Hq by (unfold acallee_saved in Hr; lia).
    vm_compute in Hq. unfold acallee_saved in Hr. lia.
  - intros Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite !Z_to_bv_unsigned in Hq. unfold bv_wrap in Hq.
    change (bv_modulus 5) with 32 in Hq.
    rewrite !Z.mod_small in Hq by (unfold acallee_saved in Hr; lia).
    unfold acallee_saved in Hr. lia. }
set (ms4 := mkst regs4 (Z_to_bv 64 (BASE + (GP_freeT + 8))) mem4 (seg_rom SEGS)).
assert (HJ4s : ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
   [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 (k + 1)) by exact HJ4.
assert (HGR4 : gregs cx ms4).
{ unfold gregs. cbn [ms4 ms_regs mkst].
  split; [etransitivity; [exact (QP 2 ltac:(unfold acallee_saved; lia)) | exact Rsp]|].
  split; [etransitivity; [exact (QP 8 ltac:(unfold acallee_saved; lia)) | exact Rs0]|].
  split; [etransitivity; [exact (QP 9 ltac:(unfold acallee_saved; lia)) | exact Rs1]|].
  split; [etransitivity; [exact (QP 3 ltac:(unfold acallee_saved; lia)) | exact Rgp3]|].
  etransitivity; [exact (QP 4 ltac:(unfold acallee_saved; lia)) | exact Rtp3]. }
assert (HBODY4 : ge_body cx fp (GP_freeT + 8) W4 ms4 GSH_sched).
{ apply (gef_body_keep cx fp GP_freeT (GP_freeT + 8) W3 ms3 W4 ms4 GSH_sched HBODY).
  - intros a Ha. cbn [ms4 ms_mem mkst]. apply KEEP.
    rewrite Hlensh in Ha. unfold GE_NSH in Ha.
    destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    + left. lia.
    + right. right. right. lia.
    + right. right. left. lia.
    + right. left. exact Ha.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact HGR4. }
pose proof HBODY4 as (_ & _ & _ & _ & _ & _ & _ & HSV4 & _ & HFLW4 & _ & _).
assert (HSL4 : forall off, off = 32 \/ off = 40 -> gslot cx W4 ms4 off (gF cx fp)).
{ intros off Hoff. unfold gslot. cbn [ms4 ms_mem mkst].
  apply (gef_rdword_keep (aview SEGS (w_H W3) (ms_mem ms3))).
  - intros i Hi. apply KEEP. left. lia.
  - destruct Hoff as [-> | ->]; [exact HSL32 | exact HSL40]. }
(* ---- the environment after the call ---- *)
remember (havoc (havoc (havoc (havoc (Eimg (c_E0 cx)) GA_SP1 [w64 (c_sp1 cx)])
                              GA_F [w64 (gF cx fp)])
                       GA_FL [w64 (gFL cx fp); w64 (gSH cx fp)])
                530 [getr regs4 0; getr regs4 1; getr regs4 2; getr regs4 3; getr regs4 4;
                     getr regs4 5; getr regs4 6; getr regs4 7; getr regs4 8; getr regs4 9;
                     getr regs4 10; getr regs4 11; getr regs4 12; getr regs4 13; getr regs4 14;
                     getr regs4 15; getr regs4 16; getr regs4 17; getr regs4 18; getr regs4 19;
                     getr regs4 20; getr regs4 21; getr regs4 22; getr regs4 23; getr regs4 24;
                     getr regs4 25; getr regs4 26; getr regs4 27; getr regs4 28; getr regs4 29;
                     getr regs4 30; getr regs4 31]) as E eqn:HE.
assert (EWk : forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n).
{ intros n Hn. rewrite HE. rewrite !ew_havoc_old by (unfold GA_SP1, GA_F, GA_FL; lia).
  apply Eimg_low. unfold A_TEXT. lia. }
assert (E60 : ew E GA_SP1 = w64 (c_sp1 cx))
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E516 : ew E GA_F = w64 (gF cx fp))
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E528 : ew E GA_FL = w64 (gFL cx fp))
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E529 : ew E GA_FSH = w64 (gSH cx fp))
  by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (EAT : forall (i : nat) (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  ew E (530 + i)%nat = getr regs4 r).
{ intros i r Hi Hr.
  assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
               i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/
               i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/
               i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31)%nat)
    by lia.
  repeat (destruct Hc as [-> | Hc];
    [ rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub Nat.add];
      first [ f_equal; apply bv_eq; rewrite <- Hr; vm_compute; reflexivity
            | match goal with |- ?g => idtac "EAT-CASE:" g end; fail ] | ]).
  subst i; rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub Nat.add];
  f_equal; apply bv_eq; rewrite <- Hr; vm_compute; reflexivity. }
assert (HEge : ge_E cx fp E).
{ split; [exact EWk|].
  split; [rewrite (EWk GA_SB ltac:(unfold GA_SB; lia)); exact E32c|].
  split; [exact E60|]. split; [exact E516|]. split; [exact E528 | exact E529]. }
assert (HEI : img_env VAL A_LIM E).
{ rewrite HE. apply img_env_havoc_hi; [|unfold A_LIM; lia].
  apply img_env_havoc_hi; [|unfold A_LIM, GA_FL; lia].
  apply img_env_havoc_hi; [|unfold A_LIM, GA_F; lia].
  apply img_env_havoc; [|unfold GA_SP1, A_TEXT; cbn [length]; lia].
  apply Eimg_env. }
pose proof HGR4 as (G2 & G8 & G9 & G3 & G4).
assert (G22 : getr regs4 (Z_to_bv 5 22) = w64 (gSH cx fp))
  by (etransitivity; [exact (QP 22 ltac:(unfold acallee_saved; lia)) | exact R22]).
assert (HRO : regs_ok E (gef_sr 530) (ms_regs ms4)).
{ apply gef_regs_ok.
  - exact EAT.
  - rewrite E60. symmetry. exact G2.
  - rewrite (EWk GA_SP ltac:(unfold GA_SP; lia)), (EE GA_SP (2%bv : bv 5) ltac:(vm_compute; reflexivity)).
    cbn [ms4 ms_regs mkst] in G8 |- *. rewrite G8.
    unfold w64, spZ. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite E60. symmetry. exact G9.
  - rewrite (EWk 3%nat ltac:(lia)), (EE 3%nat (3%bv : bv 5) ltac:(vm_compute; reflexivity)).
    symmetry. exact G3.
  - rewrite (EWk 4%nat ltac:(lia)), (EE 4%nat (4%bv : bv 5) ltac:(vm_compute; reflexivity)).
    symmetry. exact G4.
  - rewrite E529. symmetry. exact G22. }
(* ---- the seat at 0x817d0: the shadow region keeps its window [0, 104) and no chunk;
   the spill slots 32 and 40 hold the frame's address as the atom GA_F ---- *)
assert (HCS : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W4) (ms_mem ms4)) (c_sp1 cx))
   [YP09.mkChunk 32 (CVal 8 (SOff GA_F 0)); YP09.mkChunk 40 (CVal 8 (SOff GA_F 0))]).
{ assert (UF : bv_unsigned (ew E GA_F) = gF cx fp)
    by (rewrite E516; unfold w64; apply unsigned_lit_small; lia).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (gef_chunk E (w_H W4) (ms_mem ms4) GA_F (c_sp1 cx) 32 (gF cx fp) UF HFbv).
    exact (HSL4 32 (or_introl eq_refl)).
  - apply (gef_chunk E (w_H W4) (ms_mem ms4) GA_F (c_sp1 cx) 40 (gF cx fp) UF HFbv).
    exact (HSL4 40 (or_intror eq_refl)). }
assert (HSH0 : gshadow cx fp W4 ms4 []) by (intros i Hi; cbn [length] in Hi; lia).
assert (HS : st_ok_pi SEGS VAL E
  (ge_ss cx fp (GP_freeT + 8) (gef_sr 530) []
     [YP09.mkChunk 32 (CVal 8 (SOff GA_F 0)); YP09.mkChunk 40 (CVal 8 (SOff GA_F 0))] [] 0 104 []
     (mkFacts [] [] []))
  (restrict (w_H W4) ms4)).
{ change (restrict (w_H W4) ms4) with
    (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + (GP_freeT + 8))) (mrestrict (w_H W4) (ms_mem ms4)) (seg_rom SEGS)).
  unfold ge_ss, ge_regions.
  apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute; reflexivity.
  - apply Forall_app. split; [|apply Forall_nil].
    unfold ge_regions0.
    apply Forall_cons; [eapply ge_region_saved with (W3 := W4) (ms3 := ms4); eassumption|].
    apply Forall_cons; [eapply ge_region_spill with (W3 := W4) (ms3 := ms4); eassumption|].
    apply Forall_cons; [eapply ge_region_frame with (W3 := W4) (ms3 := ms4);
                        first [eassumption | apply Forall_nil]|].
    apply Forall_cons; [eapply ge_region_shadow with (W3 := W4) (ms3 := ms4);
                        first [eassumption | lia]|].
    eapply ge_region_objs with (W3 := W4) (ms3 := ms4); eassumption.
  - apply ge_pwd_app.
    + eapply ge_disj with (W3 := W4) (ms3 := ms4); eassumption.
    + exact I.
    + unfold ge_regions0, ge_obj_regions. repeat (apply Forall_cons; [exact I|]). apply Forall_nil.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [exact I | split; [exact I | exact I]]. }
(* ---- 0x817d0 .. 0x818b4: `li a0,-8`, the 55 stores of 0xf8 through s6 into the frame's
   shadow bytes 4 .. 89, and the loads of s3 and s5 from the spill slots 40 and 32 ---- *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
  let r := eval vm_compute in (sym_run_toN_pi (pl_tpi (L := grant_listing)) 64%N GP_leave ssx) in
  lazymatch r with
  | (?ss', ?st) =>
    assert (Hrun : sym_run_toN_pi (pl_tpi (L := grant_listing)) 64%N GP_leave ssx = (ss', st))
      by (vm_compute; reflexivity);
    eapply (RUNTOP W4 64%N GP_leave Ev ssx ss' st ms4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ4s);
    [ clear Hrun | clear Hrun HS HJ4s; intros ms5 mat5 HS HJ5 HF5 HFr5 HG5 ]
  end
end.
{ apply (gef_awr cx fp E _ _ _ _ _ _ _ E60 E516 E529); try lia.
  all: first [ exact ESH | eapply ge_frame_addr_eq; eassumption ]. }
(* ---- the cut at 0x818b8 ---- *)
prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
lazymatch type of HS with
| st_ok_pi ?sg ?vl ?Ex (mkSST ?pc ?sr _ (_ :: YP09.mkRegion _ _ _ _ _ ?scs :: _
                                         :: YP09.mkRegion _ _ _ ?wlo ?whi ?cs :: _) None ?G) ?msx =>
  change (st_ok_pi sg vl Ex (ge_ss_c cx fp pc sr scs [] wlo whi cs [] G) msx) in HS
| _ => fail "ge_end_free: the state at 0x818b8 has an unexpected shape"
end.
assert (HIN5 : garr8 SEGS (mrestrict (w_H W4) (ms_mem ms5)) (c_p cx)
                 (map (fun b : byte => bv_unsigned b) (c_pl cx))).
{ apply (gef_garr8 (w_H (c_W cx)) (w_H W4) (c_mem cx) (ms_mem ms5)); [|exact HPLc].
  intros j Hj. rewrite length_map in Hj.
  destruct Hpn as [(Hn0 & _) | (Hnpos & Hin0)]; [unfold c_n in Hn0; lia|].
  pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FF2 & _).
  apply (FF2 (c_p cx) (c_n cx) (Z.of_nat j) Hin0).
  - rewrite Eab4. exact Hin0.
  - unfold req_size. destruct (Z.eqb_spec (c_n cx) 0) as [Heq0|Hne0]; [exfalso; lia|].
    unfold c_n. lia.
  - intros (r & Hin & _). destruct Hin. }
destruct (ge_land_ex B MT LAWS cx fp W4 ms5 ly4 S4 _ (k + 1) HBASE HJ5 HFR4 E _ _ _ _ _ _ _ _ _ HEge HS
            eq_refl eq_refl eq_refl eq_refl eq_refl HIN5) as (sh5 & HBODY5).
apply (HNEXT cx fp (k + 1) (acc + mo_free MT) ly4 S4 W4 ms5 _ HBASE HJ5 HFR4
         (mle_station MT (c_S cx) S3 S4 acc (mo_free MT) MTL HMLE MLE4)).
unfold GI_leave.
split; [exists sh5; exact HBODY5|].
split; [lia|]. split; [unfold GE_NEED; lia|]. split; [exact Eab4|].
split; [etransitivity; [exact Q19 | exact E516]|].
split; [etransitivity; [exact Q21 | exact E516] | etransitivity; [exact Q22 | exact E529]].
Qed.
End c.
End b.
End a.
