(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, the fuzz_reply.asan-ubsan twin of lib/A/AD1r_fp.v (RelocA-2,
   a working branch 50f0c528115): the footprint lemmas of target_run's loop for the cf program
   contract over YCbqG's ajournal_x (lib/B/YCbqG.v) with the program globals G_fr_c B as its PST and the footprint
   sink_token :: fr_FP_b (lib/B/YCfn_cf.v). Text adapted from B/YD1r.v and B/YE22.v as AD1r_fp adapts their A twins.
   Image-B values: the G_fr_c ranges (0xa2520 .. 0xa2564, 0x5d8cc0 .. 0x5d90c8 = A's + 0x580, and errno 0x5d994c ..
   0x5d9950, B/W_LLVMFuzzerTestOneInput_G.v TFIB_ERRNO_B), the atexit table finished_atexit 0x5f9a40 .. 0x5f9b70 (B's
   symtab; A's 0x5f94c0 + 0x580), the image end 0x5fc000, and B's globals fr_globals_b (B/W_rep.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK0k YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t YD20 YD1v YD1y YD26 YD24 YE22 YCeg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD21 YD25 YD23 YD2h YD1w YD2f YD2b YD2g YD1s YD2c YD2d YD29 YD2e YD1r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2f_fp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- 1. the donor's two spares lemmas for any footprint tail (AD1r.v:209-215) ---- *)
Lemma spares_ro_FP : forall FP a, in_ro_tfa a -> YCbq.fp_spares (SK := tfib_sink_head) (YI16.sink_token :: FP) a.
Proof. intros FP a Ha. apply YCbq.fp_spares_below. pose proof (in_ro_range a Ha). cbn [YCbq.AOFL_HEAD YI16.sk_ofl_head tfib_sink_head]. unfold A_ofl_head. lia. Qed.
Lemma spares_stdout_FP : forall FP a, STDOUT_MUT a -> YCbq.fp_spares (SK := tfib_sink_head) (YI16.sink_token :: FP) a.
Proof.
intros FP a Ha. apply YCbq.fp_spares_off. cbn [YCbq.AOFL_HEAD YI16.sk_ofl_head tfib_sink_head]. unfold A_ofl_head.
unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
Qed.

(* ---- 2. the program globals G_fr_c ---- *)
Lemma G_fr_c_eq : forall B, as_errno B = TFIB_ERRNO_B -> G_fr_c B = GF_RANGES.
Proof. intros B HEV. unfold G_fr_c. rewrite HEV. reflexivity. Qed.
Lemma G_fr_c_TfibB : forall B, TfibSyms B -> G_fr_c B = GF_RANGES.
Proof. intros B HB. apply G_fr_c_eq. rewrite (ts_errno B HB). reflexivity. Qed.
(* the cells the driver and the exit read, none of them a G_fr_c byte *)
Definition A_ATEXIT_LO : Z := 0x5f9a40.  Definition A_ATEXIT_HI : Z := 0x5f9b70.
Lemma gf_range : forall a, Exists (in_zr a) GF_RANGES ->
  (0xa2520 <= a < 0xa2564) \/ (0x5d8cc0 <= a < 0x5d90c8) \/ (0x5d994c <= a < 0x5d9950).
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Hz). unfold GF_RANGES in Hr. unfold in_zr in Hz.
repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hz; lia|]). destruct Hr.
Qed.
Lemma gf_avoids : forall a, Exists (in_zr a) GF_RANGES ->
  ~ in_ro_tfa a /\ ~ STDOUT_MUT a /\ ~ (A_ofl_head <= a < A_ofl_head + 8) /\
  a <> A_INITFLAG /\ a <> A_INITFLAG + 4 /\ ~ (A_ATEXIT_LO <= a < A_ATEXIT_HI) /\
  in_img tfibsegs a /\ 0x9f000 <= a < 0x5fc000.
Proof.
intros a Ha. pose proof (gf_range a Ha) as Hr.
assert (Himg : 0x9f000 <= a < 0x5fc000) by lia.
split; [intros Hro; pose proof (in_ro_range a Hro); lia|].
split; [unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI; lia|].
split; [unfold A_ofl_head; lia|].
split; [unfold A_INITFLAG; lia|]. split; [unfold A_INITFLAG; lia|].
split; [unfold A_ATEXIT_LO, A_ATEXIT_HI; lia|].
split; [|exact Himg]. apply in_img_hull. lia.
Qed.

(* ---- 3. the footprint tail fr_FP_b lies in live blocks, hence off the image ---- *)
Section fp.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {hl : Z}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x tfibsegs B ARx hl.
Lemma blk_bounds_x : forall ly S Hp (W : world tfibsegs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 4096 <= p /\ p + req_size n <= alloc_ceiling.
Proof.
intros ly S Hp W mem md p n HAR HIN.
pose proof (alx_blocks tfibsegs B ARx LAWS ly S Hp W mem md p n HAR HIN) as (_ & H1 & H2 & _).
split; [exact H1 | exact H2].
Qed.
Lemma fr_FP_blocks : forall regs ly S Hp (W : world tfibsegs) mem md a,
  ARx ly S Hp W mem md -> fr_gi B (G_fr_c B) ly S W mem -> inFP (fr_FP_b regs ly S W mem) a ->
  exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n.
Proof.
intros regs ly S Hp W mem md a HAR HGI (r & Hr & Ha). unfold fr_FP_b in Hr. apply in_app_or in Hr as [Hr|Hr].
- destruct HGI as (_ & _ & (T & HRA) & _).
  destruct (rdword (aview tfibsegs (w_H W) mem) (rg_src fr_globals_b)) as [G|] eqn:HG; [|destruct Hr].
  destruct (Z.eqb_spec G 0) as [_|HG0]; [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
  destruct HRA as [(-> & _ & (H1 & _)) | (H1 & _ & _ & _ & _ & _ & _ & HIN & _)].
  + exfalso. apply HG0. assert (X : rdword (aview tfibsegs (w_H W) mem) (rg_src fr_globals_b) = Some 0) by exact (rdword_of_val_mem tfibsegs (w_H W) mem _ 0 H1 ltac:(lia)).
    rewrite X in HG. injection HG as <-. reflexivity.
  + exists T, ATABLE. split; [exact HIN|].
    pose proof (blk_bounds_x ly S Hp W mem md T ATABLE HAR HIN) as (T1 & T2). pose proof YM05.alloc_ceiling_lt as ACL.
    assert (RqT : req_size ATABLE = 896) by reflexivity. rewrite RqT in T2 |- *.
    assert (TB : 0 <= T < 2 ^ 64) by lia.
    assert (X : rdword (aview tfibsegs (w_H W) mem) (rg_src fr_globals_b) = Some T) by exact (rdword_of_val_mem tfibsegs (w_H W) mem _ T H1 TB).
    rewrite X in HG. injection HG as <-.
    unfold ATABLE in *. lia.
- destruct HGI as (_ & _ & _ & (c & O & mx & cap & out & HAO) & _).
  destruct (rdword (aview tfibsegs (w_H W) mem) (rg_out fr_globals_b)) as [o|] eqn:Ho; [|destruct Hr].
  destruct (rdword (aview tfibsegs (w_H W) mem) (rg_capout fr_globals_b)) as [cp|] eqn:Hc; [|destruct Hr].
  destruct (Z.eqb_spec cp 0) as [_|Hc0]; [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
  destruct HAO as (_ & _ & _ & _ & HC & _ & HO & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB).
  destruct HB as [(-> & -> & _) | (Hcap & _ & HIN & _)].
  + exfalso. apply Hc0. assert (X : rdword (aview tfibsegs (w_H W) mem) (rg_capout fr_globals_b) = Some 0) by exact (rdword_of_val_mem tfibsegs (w_H W) mem _ 0 HC ltac:(lia)).
    rewrite X in Hc. injection Hc as <-. reflexivity.
  + exists out, cap. split; [exact HIN|].
    pose proof (blk_bounds_x ly S Hp W mem md out cap HAR HIN) as (O1 & O3). pose proof YM05.alloc_ceiling_lt as ACL.
    assert (Hrq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia). rewrite Hrq in O3 |- *.
    assert (OB : 0 <= out < 2 ^ 64) by lia.
    assert (CB : 0 <= cap < 2 ^ 64) by lia.
    assert (X1 : rdword (aview tfibsegs (w_H W) mem) (rg_out fr_globals_b) = Some out) by exact (rdword_of_val_mem tfibsegs (w_H W) mem _ out HO OB).
    assert (X2 : rdword (aview tfibsegs (w_H W) mem) (rg_capout fr_globals_b) = Some cap) by exact (rdword_of_val_mem tfibsegs (w_H W) mem _ cap HC CB).
    rewrite X1 in Ho. injection Ho as <-. rewrite X2 in Hc. injection Hc as <-. lia.
Qed.
(* so no byte of the tail is an image byte, and none is a G_fr_c byte *)
Lemma fr_FP_off_img : forall regs ly S Hp (W : world tfibsegs) mem md a,
  ARx ly S Hp W mem md -> fr_gi B (G_fr_c B) ly S W mem -> inFP (fr_FP_b regs ly S W mem) a -> ~ in_img tfibsegs a.
Proof.
intros regs ly S Hp W mem md a HAR HGI Ha.
pose proof (fr_FP_blocks regs ly S Hp W mem md a HAR HGI Ha) as (p & n & HIN & Hr).
exact (proj2 (alx_client_img tfibsegs B ARx LAWS ly S Hp W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj HIN Hr)))))).
Qed.
Lemma fr_FP_not_gf : forall regs ly S Hp (W : world tfibsegs) mem md a,
  ARx ly S Hp W mem md -> fr_gi B (G_fr_c B) ly S W mem -> inFP (fr_FP_b regs ly S W mem) a -> ~ Exists (in_zr a) GF_RANGES.
Proof.
intros regs ly S Hp W mem md a HAR HGI Ha Hg.
exact (fr_FP_off_img regs ly S Hp W mem md a HAR HGI Ha (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (gf_avoids a Hg))))))))).
Qed.
End fp.

(* ---- 4. the driver's image regions are kept across the call (AD1r.v:226-290 over ajournal_x) ---- *)
Section jr.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {hl : Z}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x tfibsegs B ARx hl.
(* AE22.v:39 from the const-cell law *)
Lemma canary_got_kept_x : forall ly S Hp (W : world tfibsegs) mem md ly' S' Hp' (W' : world tfibsegs) mem' md' i,
  ARx ly S Hp W mem md -> ARx ly' S' Hp' W' mem' md' -> 0 <= i < 8 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') (A_GOT_CANARY + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + i).
Proof.
intros ly S Hp W mem md ly' S' Hp' W' mem' md' i HAR HAR' Hi.
pose proof (proj1 (Forall_forall _ _) (alx_const_cells tfibsegs B ARx LAWS ly S Hp W mem md HAR) _ (canary_cell_in B HB ly)) as C.
pose proof (proj1 (Forall_forall _ _) (alx_const_cells tfibsegs B ARx LAWS ly' S' Hp' W' mem' md' HAR') _ (canary_cell_in B HB ly')) as C'.
unfold cell_holds in C, C'. cbn [c_at c_val c_w z8 c8 aeval] in C, C'.
apply mbyte_of_aview. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (C (Z.to_nat i) ltac:(lia)), (C' (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.
Variable sp : word.
Hypothesis Hsp : valid_sp sp.
#[local] Notation usp := (bv_unsigned sp).
(* ROUTE R: at any world relation R of the call's journal (ajournal_xR; the proof reads its post AR and frame clauses F1
   / F3, never the world conjunct); the strict journal ajournal_x is the instance R := wle, by conversion *)
Lemma journal_regions_kept_x : forall (R : world tfibsegs -> world tfibsegs -> Prop) E rs ly S Hp (W : world tfibsegs)
  mem md ly' S' Hp' (W' : world tfibsegs) mem' md' k sp0 FP,
  YCbqG.ajournal_xR (SK := tfib_sink_head) tfibsegs B (G_fr_c B) ARx R LLVMF_STK sp0 (YI16.sink_token :: FP)
    ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
  val_mem tfibsegs (mrestrict (w_H W) mem) A_ofl_head 8 0 -> val_mem tfibsegs (mrestrict (w_H W') mem') A_ofl_head 8 0 ->
  ARx ly S Hp W mem md ->
  regions_wf rs = true ->
  Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) rs ->
  forallb (drv_keep_ok (-208)) rs = true -> forallb region_gf_ok rs = true ->
  bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> sp0 = usp - 208 -> YM05.ceil_of_top (usp - stack_max_size) ->
  Forall (region_ok tfibsegs E (mrestrict (w_H W') mem')) rs.
Proof.
intros R E rs ly S Hp W mem md ly' S' Hp' W' mem' md' k sp0 FP HJ Hh0 Hh1 HAR Hwf Hok Hchk Hgf E0 E6 Hsp0 HCT.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. unfold sp_window_lo in Ulo.
pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
pose proof (ts_errno B HB) as Eerr.
pose proof (G_fr_c_TfibB B HB) as EGF.
apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hok r Hr) as HR. pose proof HR as (B1 & B2 & RW & _).
pose proof (chunk_inside_In r) as CI. specialize (CI) with (1 := regions_wf_In rs r Hwf Hr).
pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (forallb_forall _ _) Hgf r Hr) as Hg. unfold region_gf_ok in Hg.
assert (HIGH : forall a, usp - 208 <= a < 2 ^ 64 ->
mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a
/\ (writable_at tfibsegs (mrestrict (w_H W) mem) a -> writable_at tfibsegs (mrestrict (w_H W') mem') a)).
{ intros a Ha.
assert (EQA : aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ apply F1; [lia | unfold LLVMF_STK; lia]. }
assert (EQ : mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a) by (apply (mbyte_of_aview tfibsegs); exact EQA).
split; [exact EQ|]. intros Hw. apply (apresent_writable tfibsegs).
apply (apresent_transfer tfibsegs (w_H W) (w_H W') mem mem' a);
[lia | apply not_in_img_high; lia | exact EQA | apply apresent_of_writable; [lia | exact Hw]]. }
apply (region_ok_kept_chunks E (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') r HR).
- intros c i Hcin Hi. pose proof (CI c Hcin) as [L1 L2].
destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|] eqn:Hb; try discriminate Hc; cbn [base_val] in B1, B2, RW |- *.
+   apply andb_prop in Hc as [Hc Hcw]. apply Z.leb_le in Hc. rewrite E0 in *. apply (proj1 (HIGH (usp + YP09.c_off c + i) ltac:(lia))).
+   apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply (proj1 (HIGH (bv_unsigned (ew E 6) + YP09.c_off c + i) ltac:(lia))).
+   apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [Hc Hav]. apply andb_prop in Hc as [Hilo Hihi].
apply Z.leb_le in Hilo. apply Z.leb_le in Hihi.
apply andb_prop in Hav as [Herr Hav]. unfold ext_avoids in Herr. cbn [fst snd] in Herr.
pose proof (proj1 (forallb_forall _ _) Hav c Hcin) as Havc. unfold chunk_avoids in Havc.
apply orb_prop in Havc as [Hsh|Havc].
{
destruct (shared_const_chunk_sound c Hsh) as [Hoff Hlen]. rewrite !Z.add_0_l, Hoff.
apply (canary_got_kept_x _ _ _ _ _ _ _ _ _ _ _ _ i HAR HAR'). lia. }
pose proof (ext_avoids_sound _ _ _ (YP09.c_off c + i) Havc ltac:(lia)) as Hno.
assert (Hne : ~ (TFIB_ERRNO <= YP09.c_off c + i < TFIB_ERRNO + 4)) by (apply orb_prop in Herr as [Herr|Herr]; apply Z.leb_le in Herr; lia).
assert (Hngf : ~ Exists (in_zr (YP09.c_off c + i)) GF_RANGES).
{ apply orb_prop in Hg as [Hg|Hg]; [apply Z.leb_le in Hg; lia|]. exact (gf_avoid_sound _ _ (YP09.c_off c + i) Hg ltac:(lia)). }
pose proof (in_img_hull (YP09.c_off c + i) ltac:(lia)) as Himg.
rewrite !Z.add_0_l.
destruct (Sumbool.sumbool_of_bool ((A_ofl_head <=? YP09.c_off c + i) && (YP09.c_off c + i <? A_ofl_head + 8))%bool) as [Hofl|Hofl].
{
apply andb_prop in Hofl as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.ltb_lt in Ho2.
pose proof (Hh1 (Z.to_nat (YP09.c_off c + i - A_ofl_head)) ltac:(lia)) as X1. pose proof (Hh0 (Z.to_nat (YP09.c_off c + i - A_ofl_head)) ltac:(lia)) as X0.
rewrite Z2Nat.id in X1, X0 by lia. replace (A_ofl_head + (YP09.c_off c + i - A_ofl_head)) with (YP09.c_off c + i) in X1, X0 by lia.
rewrite X1, X0. reflexivity. }
apply (mbyte_of_aview tfibsegs). apply F3; [exact Himg | rewrite (ts_owned B HB); exact Hno | rewrite Eerr; exact Hne | rewrite EGF; exact Hngf |].
apply YCbq.fp_spares_off. cbn [YCbq.AOFL_HEAD YI16.sk_ofl_head tfib_sink_head]. unfold A_ofl_head in *.
apply Bool.andb_false_iff in Hofl. destruct Hofl as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; lia.
- intros o Ho.
destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|] eqn:Hb; try discriminate Hc; cbn [base_val] in B1, B2, RW |- *.
+ apply andb_prop in Hc as [Hc Hcw]. apply Z.leb_le in Hc. rewrite E0 in *.
apply orb_prop in Hcw as [Hcw|Hcw]; [apply Z.leb_le in Hcw; lia|]. apply andb_prop in Hcw as [Hw1 Hw2].
apply Z.leb_le in Hw1. apply Z.leb_le in Hw2. apply (proj2 (HIGH (usp + o) ltac:(lia))). apply RW. exact Ho.
+ apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc2. lia.
+ apply andb_prop in Hc as [Hc Hw]. apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
unfold writable_at. rewrite Z.add_0_l. apply tfib_rw_window. rewrite u64_lit by lia. lia.
Qed.
End jr.

(* ---- 5. rom_view at a call site, from what the driver already has there (arodata_ok) and the const-cell law ----
   The cf pre (A/AD1w_cf.v:106) asks rom_view: EVERY read-only image byte reads its image byte.  The donor's driver
   gives arodata_ok at each call site (A/AD2d.v sPE_img_facts), which leaves out the owned statics and errno.  errno
   is not read-only; each owned read-only byte is pinned by a Tfib_const_abs cell equal to the image byte
   (A/YF0mFacts.v tfib_rom_owned_pinned, in its shift-and-mask form; le_byte_land below is the bridge), and the
   const-cell law of the allocator invariant makes that cell hold. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0mFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YE01.
Lemma le_byte_land : forall v w k, (k < w)%nat -> le_byte v w k = Z.land (Z.shiftr v (8 * Z.of_nat k)) 255.
Proof.
intros v w k Hk. unfold le_byte.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
rewrite !Z.shiftr_div_pow2 by lia.
change 256 with (2 ^ 8).
set (n := 8 * Z.of_nat k). set (m := 8 * Z.of_nat w).
assert (Hnm : n + 8 <= m) by (unfold n, m; lia).
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (Hm : 2 ^ m = 2 ^ (m - n) * 2 ^ n) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (Hmn : 2 ^ (m - n) = 2 ^ (m - n - 8) * 2 ^ 8) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
set (R := v mod 2 ^ m). set (Q := v / 2 ^ m).
assert (Hv : v = R + (Q * 2 ^ (m - n)) * 2 ^ n).
{ pose proof (Z.div_mod v (2 ^ m) ltac:(apply Z.pow_nonzero; lia)) as D. fold R Q in D. rewrite D at 1. rewrite Hm. ring. }
rewrite Hv at 1. rewrite Z.div_add by (apply Z.pow_nonzero; lia).
rewrite Hmn. replace (Q * (2 ^ (m - n - 8) * 2 ^ 8)) with ((Q * 2 ^ (m - n - 8)) * 2 ^ 8) by ring.
rewrite Z.mod_add by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
Section rv.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {hl : Z}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x tfibsegs B ARx hl.
Lemma const_abs_in : forall ly c, In c Tfib_const_abs -> In c (as_const B ly).
Proof. intros ly c Hc. rewrite (ts_const B HB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. left. exact Hc. Qed.
Lemma rom_owned_view : forall ly S Hq (W : world tfibsegs) mem md a,
  ARx ly S Hq W mem md -> in_rom tfibsegs a -> Exists (in_zr a) (as_owned_static B) ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
intros ly S Hq W mem md a HAR Hrom Hown. rewrite (ts_owned B HB) in Hown.
pose proof (tfib_rom_owned_pinned a Hrom Hown) as (c & Hc & Hne & Heq).
pose proof (proj1 (Forall_forall _ _) (alx_const_cells tfibsegs B ARx LAWS ly S Hq W mem md HAR) c (const_abs_in ly c Hc)) as HCH.
unfold cell_holds in HCH. unfold tfib_cell_byte, tfib_cell_lit in Hne, Heq.
destruct (c_at c) eqn:Eat; try (exfalso; apply Hne; reflexivity).
destruct (c_val c) as [e|mask v] eqn:Ev; [|exfalso; apply Hne; reflexivity].
destruct e eqn:Ee; try (exfalso; apply Hne; reflexivity).
cbn [aeval] in HCH.
match type of Heq with context [if ?b then _ else _] => destruct b eqn:Hb end; [|exfalso; apply Hne; reflexivity].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
match type of HCH with forall k, _ -> ?rd (?A0 + Z.of_nat k) = _ =>
  assert (Hk : (Z.to_nat (a - A0) < c_w c)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia);
  specialize (HCH (Z.to_nat (a - A0)) Hk); rewrite (le_byte_land _ _ _ Hk) in HCH; rewrite Z2Nat.id in HCH by lia;
  replace (A0 + (a - A0)) with a in HCH by lia end.
rewrite HCH, Heq. unfold tfib_img_byte. reflexivity.
Qed.
(* rom_view from arodata_ok (what the donor's driver gives at every call site) and the allocator invariant *)
Lemma rom_view_of_arodata : forall ly S Hq (W : world tfibsegs) mem md,
  ARx ly S Hq W mem md -> arodata_ok B (aview tfibsegs (w_H W) mem) -> rom_view tfibsegs W mem.
Proof.
intros ly S Hq W mem md HAR HRO a Hrom.
assert (Hro : in_ro_tfa a) by (left; exact Hrom).
destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Hno].
{ intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r)); [left; lia | right; lia | right; lia | right; lia]. }
- exact (rom_owned_view ly S Hq W mem md a HAR Hrom Ho).
- apply HRO; [exact Hro | exact Hno |]. rewrite (ts_errno B HB). pose proof (in_ro_range a Hro). unfold TFIB_ERRNO. lia.
Qed.
(* the same from the cf pre's own read-only clause (YE01 arodata_okS at any RLO / RHI) *)
Lemma rom_view_of_arodataS : forall RLO RHI ly S Hq (W : world tfibsegs) mem md,
  ARx ly S Hq W mem md -> YE01.arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) mem) -> rom_view tfibsegs W mem.
Proof.
intros RLO RHI ly S Hq W mem md HAR HRO a Hrom.
assert (Hro : in_ro_tfa a) by (left; exact Hrom).
destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Hno].
{ intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r)); [left; lia | right; lia | right; lia | right; lia]. }
- exact (rom_owned_view ly S Hq W mem md a HAR Hrom Ho).
- apply HRO; [left; exact Hrom | exact Hno |]. rewrite (ts_errno B HB). pose proof (in_ro_range a Hro). unfold TFIB_ERRNO. lia.
Qed.
End rv.
