(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 1d255703e88 (m2_stack,
   m2_pre_call, m2_core_step, m2_core_call) and proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v at 1d255703e88
   (m2t_garr8_kept, the run-to-call / contract / return pattern of tl_s4 .. tl_s6) for reac-pw/fuzz_rate's image-A
   list segment M03: rate's cut vocabulary (lib/A/RtPgSeg.v, rt_ / q_ names); the seam is generic in the segment's
   write set and carries rt_cpost_g's O conjunct; the walk of C6 -> C7 (memset, reac_rate_drivable_csv, check_csv)
   is new. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, the same loaded bytes): THE LIST SEGMENT M03 of the
   walk of LLVMFuzzerTestOneInput (0x80714), C6 = 0x82e98 -> C7 = 0x82ed4, i.e. lib/A/RtPgSeg.v's
   rs_piece_W14_csv_stmt at the image's own segments. Proves no function (kind: segment lemma); nothing here
   restates a cut or a contract.

   THE CODE (15 words, w14c_tbl):
     0x82e98 beqz a0 -> 0x83050 (a0 = buf >= 4096: not taken); mv s5,a0; addi a1,zero,0x5a; mv a2,s7 (s7 = bl);
     0x82ea8 jal 0x51cfc (__asan_memset), ra = 0x82eac;
     0x82eac ld s2,0x120(s1) (the mask cell); mv a0,s2; mv a1,s5; mv a2,s3 (s3 = buflen);
     0x82ebc jal 0x84074 (reac_rate_drivable_csv), ra = 0x82ec0;
     0x82ec0 mv a2,a0; mv a0,s5; mv a1,s3; mv a3,s2;
     0x82ed0 jal 0x838e0 (check_csv), ra = 0x82ed4 = C7.
   No instrumented check lies in the segment; its only memory access is the load of R+0x120.

   THE ROUTE.
   1. One run of the kit's token engine from C6 (every register an atom; the fact 4096 <= a0, from the allocator's
      block law, decides the `beqz`) to the memset entry; the call by RtPgSteps.rts_intrin_at (OSet) at the
      harness's journal: buf's bl bytes are the journal's own (a block made since the journal's start,
      RtPgBase.rt_fresh_awr_n), its shadow is the block's (RtPgMem.rtm_blk_ra), its window [R - ESTACK, R) lies in
      the journal's stack window.
   2. One run from 0x82eac (the real-frame cell R+0x120 as a read-only region, its value the mask) to the entry of
      reac_rate_drivable_csv; its contract at fy = the segment's float state (the first call, frm_zero from
      rs_start_M03), with rt_cpre from the segment's frame (w14c_pre_call); the format, the two separators and the
      table ordered from rs_pre's strings and tables at the segment's start, rebuilt at the call by
      RtPgSiteA.rate_A_cstr_at / rate_A_i32tab_at from the symbol record's invariant rate_A_img_facts
      (w14c_statics): their bytes are the start's, being image bytes that are no owned static (w14c_img_kept: not in
      the callees' stack, not in buf, owned in no AR state by RtPgBase.rt_img_unowned); the read-only image kept
      (rt_rom_kept, w14c_rom_kept) by the same argument.
   3. At drivable_csv's float state fx3 (w14c_s3): one run from 0x82ec0 to the entry of check_csv and its contract
      at fy = fx3; buf holds 0x5a when buflen = 0 (memset's byte, kept: no byte of a live block is runtime-owned)
      and drivable_csv's list otherwise; buf is a live block (rs_core's block permutation); closed_list (0x21520)
      rebuilt at the call as in 2 (its shadow bytes are runtime-owned, so drivable_csv's post may change them: the
      shadow comes from rate_A_img_facts); check_csv's write set is the owned set at its call, which drivable_csv's O
      clause puts inside the owned set at C6.
   4. The C7 cut (w14c_cut_C7): the segment's frame with the write set rs_E3 (each callee's post through
      w14c_core_call, with its own write set inside rs_E3), rt_fxk [10] (drivable_csv's), the four registers
      (callee-saved, never written after 0x82e9c), the four real-frame cells and the frame's shadow (no callee and
      no run writes them: the stack cells and the frame's shadow are neither in a callee's stack, in buf, nor
      runtime-owned, by the journal's write rights and AR_frames_law).

   SECTION HYPOTHESES of rt_w14_csv_A (Section m): MTL : ameter_laws MT; AMEMSET : aintrin_realizes rsegs B OSet
   0x51cfc; DCSV : the contract of reac_rate_drivable_csv at every float state; CCSV : the contract of check_csv at
   every float state; IMGF : rate_A_img_facts rsegs B, the symbol record's invariant over image A's read ranges,
   registered globals and image range (RtPgSiteA.v). AR_laws is the kernel's YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Layout RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgMem RtPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSiteA.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ======================================== the code ======================================== *)
(* the 15 words 0x82e98 .. 0x82ed0 *)
Definition w14c_tbl : ctable := build_table rsegs 0x82e98 15 TEmpty.
Lemma w14c_tbl_ok : table_ok rsegs w14c_tbl.
Proof. apply build_table_ok0. lia. Qed.
(* env slot 32 is the runtime's shadow offset (no shadow entry is used) *)
Definition w14c_Bx : sv := SOff 32 0.
Definition w14c_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the fact of the first run: a0 (buf) is at least 4096 and below the allocator's highest ceiling *)
Definition w14c_G1 : facts := mkFacts [(10%nat, mkAF 4096 0x7fffff800000 0)] [] [].
(* the mask cell R+0x120 (s1 = atom 9) as a read-only region, its value env slot 33 *)
Definition w14c_r120 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x120 0x128 0 0 [YP09.mkChunk 0x120 (CVal 8 (SOff 33 0))].

(* buf's block: buflen + (buflen == 0) bytes, 1 .. 23 of them *)
Lemma w14c_bl : forall n, 0 <= n < 24 -> rt_bl n = Z.max n 1 /\ 1 <= rt_bl n <= 23 /\ req_size (rt_bl n) = rt_bl n.
Proof.
intros n Hn. unfold rt_bl, req_size. destruct (Z.eqb_spec n 0) as [->|H0].
- split; [reflexivity | split; [lia | reflexivity]].
- rewrite Z.add_0_r. destruct (Z.eqb_spec n 0); lia.
Qed.

(* a register not on a list of literal registers *)
Ltac w14_notin := let X := fresh "X" in intros X; cbn [In] in X;
  repeat (destruct X as [X|X]; [apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X|]);
  destruct X.
Ltac w14_nz := let X := fresh "X" in intros X; vm_compute in X; discriminate X.
(* a register a run kept, through regs_kept_of_st_ok *)
Ltac w14_rk RK := apply RK; [w14_nz | w14_notin].

(* ======================================== engine helpers ======================================== *)
Section gen. Context {fx : YK11.FPState}.
Lemma w14c_entry : forall pc sr regs extra E (rs : smem) (G : facts) mem, E = Ereg regs extra ->
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok rsegs E mem) rs -> pairwise_disjoint E rs ->
facts_ok E G -> st_ok rsegs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs)).
Proof. intros pc sr regs extra E rs G mem -> Hr Hw Hrs Hpd HG. apply entry_st_ok_full; assumption. Qed.
(* the bytes a run keeps: every address outside the write windows of its start regions *)
Lemma w14c_kept_run : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' a HF Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
Lemma w14c_garr8_kept : forall H H' (m m' : word -> option byte) a l,
garr8 rsegs (mrestrict H m) a l ->
(forall j, (j < length l)%nat -> aview rsegs H' m' (a + Z.of_nat j) = aview rsegs H m (a + Z.of_nat j)) ->
garr8 rsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l G K j Hj. destruct (G j Hj) as (Hv & Hr). split; [|exact Hr].
eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 1) with 1 in Hk.
replace k with 0 by lia. rewrite Z.add_0_r. exact (K j Hj).
Qed.
End gen.

(* ======================================== the seam ========================================
   The segment's frame rs_core (RtPgSeg) at a call state gives a callee contract's rt_cpre; a run that keeps sp /
   gp / tp, the frames, blocks, I/O state and meter keeps rs_core; a callee's post (RtPgCSpec.rt_cpost_g, for any
   O clause) whose write set lies in the segment's gives rs_core at the returned state. [role's
   lib/A/RPgM02Base.v m2_stack / m2_pre_call / m2_core_step / m2_core_call, generic in the write set and with
   rt_cpost_g's O conjunct] *)
Section seam. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMGF : rate_A_img_facts rsegs B.

Lemma w14c_stack : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
spZ (x_regs cx) = q_R (x_e cx) /\ q_R (x_e cx) mod 16 = 0 /\ q_R (x_e cx) + 0x1e0 <= x_sp0 cx /\
x_sp0 cx - x_STK cx <= q_R (x_e cx) - T_SEG_STK /\ alloc_ceiling + T_SEG_STK <= q_R (x_e cx) /\
x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\ st_nev (x_S cx) + x_k cx <= EV_MAX /\
getr (x_regs cx) 3 = w64 (as_gp B) /\ getr (x_regs cx) 4 = w64 (as_tp B).
Proof.
intros cx Hpre. unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
cbn [hi_rsz rate_himg_A] in Hrsz. rewrite HS in Hrsz.
unfold T_SEG_STK, ASTACK in *.
assert (HR : spZ (x_regs cx) = q_R (x_e cx))
by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
repeat split; first [assumption | lia].
Qed.

Lemma w14c_pre_call : forall (cx : rs_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regsT memT mdT T,
rs_pre rsegs B cx -> rs_core rsegs B MT cx E ly2 S2 W2 regsT memT mdT ->
YK0s.ret_ok (getr regsT 1) -> 4096 <= raZ regsT -> spZ regsT = q_R (x_e cx) -> 0 <= T <= T_SEG_STK ->
rt_cpre rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx)
(x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx) T regsT ly2 S2 W2 memT mdT.
Proof.
intros cx E ly2 S2 W2 regsT memT mdT T Hpre (HJ & Hr & _) Hra Hra4 HspT HT.
pose proof (w14c_stack cx Hpre) as (HR & Hal & Hrsz & Hwin & _ & _ & _ & Hev & Hgp & Htp).
unfold rt_cpre. split; [exact HJ|]. split; [exact Hra|]. split; [exact Hra4|].
split; [transitivity (getr (x_regs cx) (Z_to_bv 5 3)); [exact (Hr 3 ltac:(lia)) | exact Hgp]|].
split; [transitivity (getr (x_regs cx) (Z_to_bv 5 4)); [exact (Hr 4 ltac:(lia)) | exact Htp]|].
rewrite HspT. split; [exact Hal|]. split; [lia|]. split; [lia | exact Hev].
Qed.

Lemma w14c_core_step : forall (cx : rs_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx)
(x_mem0 cx) (x_md0 cx) (x_own cx) ly3 S3 W3 mem3 md3 (x_k cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (x_regs cx) - T_SEG_STK <= a < spZ (x_regs cx)) -> ~ E a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & Hr & Hfr & Hperm & Hio & Hmo & HK)
HJ3 Hr3 Hfr3 Hperm3 Hio3 Hmo3 HK3.
split; [exact HJ3|].
split; [intros r Hrr; rewrite (Hr3 r Hrr); exact (Hr r Hrr)|].
split; [rewrite Hfr3; exact Hfr|].
split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm]|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3)|].
intros a Ha Hs He. rewrite (HK3 a Ha Hs He). exact (HK a Ha Hs He).
Qed.

Lemma w14c_core_call : forall (cx : rs_scx rsegs) (E Ec : Z -> Prop) T ly2 S2 W2 regsT memT mdT
(O : alayout -> astate -> Prop) (FX : YK11.FPState -> Prop)
(Rc : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) W3 c3,
rs_pre rsegs B cx -> rs_core rsegs B MT cx E ly2 S2 W2 regsT memT mdT ->
spZ regsT = q_R (x_e cx) -> 0 <= T <= T_SEG_STK -> (forall a, Ec a -> E a) ->
rt_cpost_g rsegs B MT (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx)
(x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx) T regsT ly2 S2 W2 memT mdT O FX Ec Rc W3 c3 ->
exists (fx3 : YK11.FPState) ly3 S3 regs3 mem3 md3,
c3 = mkCfg (@mkst fx3 regs3 (getr regsT 1) mem3 (seg_rom rsegs)) md3 /\ FX fx3 /\
rs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3 /\ aregs_preserved regsT regs3 /\ O ly3 S3 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e cx) - T <= a < q_R (x_e cx)) -> ~ Ec a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) memT a) /\
Rc W3 regs3 mem3.
Proof.
intros cx E Ec T ly2 S2 W2 regsT memT mdT O FX Rc W3 c3 Hpre Hcore HspT HT HEc
(fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HFX & HJ3 & Hpres & Hfr3 & HO & Hperm3 & Hio3 & Hmo3 & HK3 & HR3).
pose proof (w14c_stack cx Hpre) as (HR & _).
exists fx3, ly3, S3, regs3, mem3, md3.
split; [exact Hc3|]. split; [exact HFX|].
split.
{ apply (w14c_core_step cx E ly2 S2 W2 regsT memT mdT ly3 S3 W3 regs3 mem3 md3 Hcore HJ3);
  [intros r Hr; apply Hpres; unfold acallee_saved; lia | exact Hfr3 | exact Hperm3 | exact Hio3 | exact Hmo3 |].
  intros a Ha Hs He. apply HK3; [exact Ha | rewrite HspT; rewrite HR in Hs; unfold T_SEG_STK in *; lia |].
  intros Hc. exact (He (HEc a Hc)). }
split; [exact Hpres|]. split; [exact HO|].
split; [intros a Ha Hs He; apply HK3; [exact Ha | rewrite HspT; exact Hs | exact He] | exact HR3].
Qed.

(* a sub-range of a live block lies in the application memory below the shadow [YCbq amem_range_of_block] *)
Lemma w14c_amem : forall ly S W mem md p m a n,
AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m -> 0 <= n ->
amem_range a n.
Proof.
intros ly S W mem md p m a n HAR Hin H1 H2 H0.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & _ & Hc & [Hh Hh2] & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). zlia.
Qed.

(* an image byte that is no owned static, at a state of the segment (the write set rs_E3), is the start's: it is
   not in the callees' stack (below the low shadow), not in buf (client memory is no image byte), and owned in no
   AR state (RtPgBase.rt_img_unowned) *)
Lemma w14c_img_kept : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B (x_lyc cx) (x_Sc cx)) ->
rs_core rsegs B MT cx (rs_E3 rsegs B cx) ly2 S2 W2 regs2 mem2 md2 ->
forall a, in_img rsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hbin Hcore a Himg Ho.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof (w14c_stack cx Hpre) as (HR & _ & _ & _ & Hceil & _).
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp. destruct Hp as (HJ & _).
pose proof HJ as (HAR & _).
destruct Hcore as (_ & _ & _ & _ & _ & _ & HK).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (rts_segs_low a Himg) as Hlow.
apply HK.
- unfold kLowMemEnd in Hlow. lia.
- rewrite HR. unfold T_SEG_STK, ASTACK, kLowMemEnd in *. lia.
- unfold rs_E3. intros [Hw | [Hb | Hown]].
  + unfold rt_inw in Hw. cbn [hi_w3 rate_himg_A] in Hw. inversion Hw.
  + assert (Hc : (exists p n, In (p, n) (ablocks B (x_lyc cx) (x_Sc cx)) /\ p <= a < p + req_size n) \/
      (exists cid pos, In (cid, pos) (frames (x_Sc cx)) /\
        frame_addr (x_lyc cx) cid pos <= a < frame_addr (x_lyc cx) cid pos + fs_frame_bytes cid) \/
      (exists cid pos, In (cid, pos) (frames (x_Sc cx)) /\ a = flag_addr (x_lyc cx) cid pos)).
    { left. exists (q_buf (x_e cx)), (rt_bl (q_buflen (x_e cx))). split; [exact Hbin|].
      unfold req_size. destruct (Z.eqb_spec (rt_bl (q_buflen (x_e cx))) 0); lia. }
    destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR Hc) as [_ Hni]. exact (Hni Himg).
  + exact (rt_img_unowned rsegs B LAWS _ _ _ _ _ a HAR Himg Ho Hown).
Qed.

(* the read-only image, at a state of the segment: the start's rom_view on the bytes w14c_img_kept keeps *)
Lemma w14c_rom_kept : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B (x_lyc cx) (x_Sc cx)) ->
rs_core rsegs B MT cx (rs_E3 rsegs B cx) ly2 S2 W2 regs2 mem2 md2 ->
rt_rom_kept rsegs B W2 mem2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hbin Hcore a Ha Ho He.
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrom & _).
assert (Himg : in_img rsegs a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
rewrite (w14c_img_kept cx ly2 S2 W2 regs2 mem2 md2 Hpre Hbin Hcore a Himg Ho). exact (Hrom a Ha).
Qed.

(* the strings and the two tables the list's callees read, at a state of the segment: rs_pre's facts at the start,
   rebuilt there by RtPgSiteA.rate_A_cstr_at / rate_A_i32tab_at (their bytes kept by w14c_img_kept, being image bytes
   that are no owned static, rate_A_str_unowned / rate_A_i32_unowned; their shadow from rate_A_img_facts) *)
Lemma w14c_statics : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B (x_lyc cx) (x_Sc cx)) ->
rs_core rsegs B MT cx (rs_E3 rsegs B cx) ly2 S2 W2 regs2 mem2 md2 ->
rt_cstr rsegs (w_H W2) mem2 0x216c0 STR_FMT_SD /\ rt_cstr rsegs (w_H W2) mem2 0x216e0 STR_COMMA /\
rt_cstr rsegs (w_H W2) mem2 0x21700 STR_EMPTY /\
rt_i32tab rsegs (w_H W2) mem2 0x216a0 RateCfg.closed_list /\
rt_i32tab rsegs (w_H W2) mem2 0x21520 RateCfg.closed_list.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hbin Hcore.
pose proof (w14c_img_kept cx ly2 S2 W2 regs2 mem2 md2 Hpre Hbin Hcore) as K.
pose proof (proj1 (proj1 Hcore)) as HAR2.
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstrs & _ & _ & _ & Hi32 & _).
rewrite Forall_forall in Hstrs, Hi32. cbn [hi_strs hi_i32 rate_himg_A] in Hstrs, Hi32.
assert (KS : forall a s, In (a, s) rate_A_strs -> rt_cstr rsegs (w_H W2) mem2 a s).
{ intros a s Hin. pose proof (Hstrs (a, s) Hin) as Hc. cbn [fst snd] in Hc.
  pose proof Hc as (_ & _ & _ & _ & _ & Himg & _).
  pose proof (rate_A_str_unowned rsegs B a s IMGF Hin) as HU.
  apply (rate_A_cstr_at rsegs B a s ly2 S2 W2 mem2 md2 (w_H (x_W cx)) (x_memc cx) IMGF Hin HAR2 Hc).
  intros i Hi. apply K; [exact (Himg i Hi) | exact (proj1 (HU (a + i) ltac:(lia)))]. }
assert (KT : forall t vs, In (t, vs) rate_A_i32 -> rt_i32tab rsegs (w_H W2) mem2 t vs).
{ intros t vs Hin. pose proof (Hi32 (t, vs) Hin) as Ht. cbn [fst snd] in Ht.
  pose proof Ht as (Himg & _).
  pose proof (rate_A_i32_unowned rsegs B t vs IMGF Hin) as HU.
  apply (rate_A_i32tab_at rsegs B t vs ly2 S2 W2 mem2 md2 (w_H (x_W cx)) (x_memc cx) IMGF Hin HAR2 Ht).
  intros i Hi. apply K; [exact (Himg i Hi) | exact (proj1 (HU (t + i) ltac:(lia)))]. }
split; [apply KS; unfold rate_A_strs; repeat (first [left; reflexivity | right])|].
split; [apply KS; unfold rate_A_strs; repeat (first [left; reflexivity | right])|].
split; [apply KS; unfold rate_A_strs; repeat (first [left; reflexivity | right])|].
split; [apply KT; unfold rate_A_i32; right; left; reflexivity|].
apply KT. unfold rate_A_i32. left. reflexivity.
Qed.
End seam.

(* ======================================== the third run and check_csv ========================================
   At the float state the drivable_csv call returned at (the Context fx of this Section): from 0x82ec0 (a0 = the
   list's length, s5 = buf, s3 = buflen, s2 = mask) one run to check_csv's entry, then its contract; the continuation
   gets rs_core at the return pc 0x82ed4 with every callee-saved register as at 0x82ec0. *)
Section s3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis CCSV : rt_check_csv_specX rsegs B MT 0x838e0 2 T_csv_STK 0x21520.
Hypothesis IMGF : rate_A_img_facts rsegs B.

Lemma w14c_s3 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx ->
frames (x_Sc cx) = [(hi_cid rate_himg_A, x_pos cx)] ->
In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B (x_lyc cx) (x_Sc cx)) ->
rs_core rsegs B MT cx (rs_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3 ->
spZ regs3 = q_R (x_e cx) ->
getr regs3 (Z_to_bv 5 10) = w64 (Z.of_nat (length (RateCsv.csv_list (q_mask (x_e cx))))) ->
getr regs3 (Z_to_bv 5 21) = w64 (q_buf (x_e cx)) ->
getr regs3 (Z_to_bv 5 19) = w64 (q_buflen (x_e cx)) ->
getr regs3 (Z_to_bv 5 18) = w64 (q_mask (x_e cx)) ->
(q_buflen (x_e cx) = 0 -> garr8 rsegs (mrestrict (w_H W3) mem3) (q_buf (x_e cx)) [0x5a]) ->
(0 < q_buflen (x_e cx) -> garr8 rsegs (mrestrict (w_H W3) mem3) (q_buf (x_e cx))
  (RateCsv.csv_cut (RateCsv.csv_list (q_mask (x_e cx))) (q_buflen (x_e cx)) ++ [0])) ->
(forall a, aowned B ly3 S3 a -> aowned B (x_lyc cx) (x_Sc cx) a) ->
(forall ly4 S4 W4 regs4 mem4 md4, rs_core rsegs B MT cx (rs_E3 rsegs B cx) ly4 S4 W4 regs4 mem4 md4 ->
  aregs_preserved regs3 regs4 ->
  SRr rsegs W4 (cfg_at rsegs 0x82ed4 regs4 mem4 md4) POST) ->
SRr rsegs W3 (cfg_at rsegs 0x82ec0 regs3 mem3 md3) POST.
Proof.
intros cx POST ly3 S3 W3 regs3 mem3 md3 Hpre Hfr Hbin Hcore3 Hsp3 H10 H21 H19 H18 Hz Hnz HO K.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof (w14c_stack B cx Hpre) as (HR & HR16 & HRs & Hwin & Hceil & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhdr & _).
pose proof HJ0 as (HAR0 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
destruct Hhdr as (_ & Hmask & Hbln & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w14c_bl (q_buflen (x_e cx)) Hbln) as (Hblm & Hbl23 & Hblr).
rewrite Hblr in Hbceil, Hbapp.
pose proof (proj1 Hcore3) as HJ.
pose proof Hcore3 as (_ & _ & Hfr3 & Hperm3 & _).
assert (Hbin3 : In (q_buf (x_e cx), rt_bl (q_buflen (x_e cx))) (ablocks B ly3 S3))
by (apply (Permutation_in _ (Permutation_sym Hperm3)); exact Hbin).
(* the entry at 0x82ec0: every register an atom, no region, no fact *)
set (E := Ereg regs3 [w64 SHADOW_OFF]).
assert (E21 : ew E 21 = w64 (q_buf (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact H21).
assert (E19 : ew E 19 = w64 (q_buflen (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl); exact H19).
assert (E10 : ew E 10 = w64 (Z.of_nat (length (RateCsv.csv_list (q_mask (x_e cx))))))
by (subst E; rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = w64 (q_mask (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl); exact H18).
assert (HE : E = Ereg regs3 [w64 SHADOW_OFF]) by reflexivity. clearbody E.
assert (HS : st_ok rsegs E (mkSS 0x82ec0 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 0x82ec0) mem3 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (w14c_entry 0x82ec0 sr_atoms regs3 [w64 SHADOW_OFF] E);
  [exact HE | rewrite HE; apply regs_ok_Ereg | vm_compute; reflexivity | constructor | cbn; tauto |].
  split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs w14c_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (HAE : env_agree 32 (Ereg regs3 [w64 SHADOW_OFF]) E) by (rewrite HE; apply env_agree_refl).
unfold cfg_at. change (w64 0x82ec0) with (Z_to_bv 64 0x82ec0).
aj_run_tok w14c_tbl_ok HS HJ SHOK w14c_Bspan; [awr_ok_tac |].
rreg HS (10%bv : bv 5) Vr10. rreg HS (11%bv : bv 5) Vr11. rreg HS (12%bv : bv 5) Vr12.
rreg HS (13%bv : bv 5) Vr13. rreg HS (1%bv : bv 5) Vr1.
assert (HP3 : aregs_preserved regs3 (ms_regs ms))
by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) (ms_mem ms) a = aview rsegs (w_H W3) mem3 a).
{ intros a Ha. apply (w14c_kept_run E _ (w_H W3) mem3 (ms_mem ms) a HFr Ha).
  intros (r & Hr & _). cbn [ss_mem In] in Hr. destruct Hr. }
assert (Vr1' : getr (ms_regs ms) 1 = w64 0x82ed4) by exact Vr1.
assert (HspT : spZ (ms_regs ms) = q_R (x_e cx)).
{ rewrite <- Hsp3. unfold spZ. f_equal. exact (HP3 2 ltac:(unfold acallee_saved; lia)). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E3 rsegs B cx) ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
by (apply (w14c_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT Hcore3 HJ);
    [ intros r Hr; apply HP3; unfold acallee_saved; lia
    | reflexivity | apply Permutation_refl | apply same_io_wvb | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KM a Ha))
end.
lazymatch goal with HS' : st_ok _ _ ?ss (restrict _ ms) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H W3) E ss ms HS' eq_refl);
  replace (ss_pc ss) with 0x838e0 by (vm_compute; reflexivity)
end.
destruct (w14c_statics B MT IMGF cx _ _ _ _ _ _ Hpre Hbin HcoreT) as (_ & _ & _ & _ & Tcl).
destruct (rtm_blk_ra rsegs B _ _ _ _ _ (q_buf (x_e cx)) (rt_bl (q_buflen (x_e cx))) (q_buf (x_e cx))
  (Z.max (q_buflen (x_e cx)) 1) (proj1 HJ) Hbin3 ltac:(lia) ltac:(rewrite Hblr; lia)) as [Hra Hhv].
eapply SRr_bind.
{ apply (CCSV (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly3 S3 W3 (ms_mem ms) _ (x_k cx) (ms_regs ms) (q_buf (x_e cx)) (q_buflen (x_e cx)) (q_mask (x_e cx))).
  - apply (w14c_pre_call B MT cx _ _ _ _ _ _ _ T_csv_STK Hpre HcoreT);
    [ rewrite Vr1'; vm_compute; reflexivity
    | unfold raZ; rewrite Vr1'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_csv_STK, T_SEG_STK, ASTACK, ESTACK; lia ].
  - etransitivity; [exact Vr10 | exact E21].
  - etransitivity; [exact Vr11 | exact E19].
  - lia.
  - etransitivity; [exact Vr12 | exact E10].
  - etransitivity; [exact Vr13 | exact E18].
  - lia.
  - lia.
  - rewrite <- Hblm. lia.
  - exists (rt_bl (q_buflen (x_e cx))). split; [exact Hbin3 | lia].
  - exact Hra.
  - exact (Hhv ltac:(lia)).
  - apply (w14c_amem B _ _ _ _ _ _ _ _ _ (proj1 HJ) Hbin3); lia.
  - left. rewrite HspT. unfold T_csv_STK, T_SEG_STK, ASTACK, ESTACK in *. lia.
  - intros Hn0. apply (w14c_garr8_kept (w_H W3) (w_H W3) mem3 (ms_mem ms) _ _ (Hz Hn0)).
    intros j Hj. cbn [length] in Hj. apply KM. lia.
  - intros Hn0. apply (w14c_garr8_kept (w_H W3) (w_H W3) mem3 (ms_mem ms) _ _ (Hnz Hn0)).
    intros j Hj.
    rewrite length_app, (RateCsv.csv_cut_length (RateCsv.csv_list (q_mask (x_e cx))) (q_buflen (x_e cx))
      ltac:(lia)) in Hj.
    cbn [length] in Hj.
    apply KM. lia.
  - lia.
  - rewrite Hfr3, Hfr. vm_compute. reflexivity.
  - exact Tcl. }
intros W4 c4 _ Hpost.
destruct (w14c_core_call B MT MTL cx (rs_E3 rsegs B cx) (fun x => aowned B ly3 S3 x) T_csv_STK
  _ _ _ _ _ _ _ _ _ W4 c4 Hpre HcoreT HspT ltac:(unfold T_csv_STK, T_SEG_STK, ASTACK, ESTACK; lia)
  ltac:(intros a Ha; unfold rs_E3; right; right; exact (HO a Ha)) Hpost)
as (fx4 & ly4 & S4 & regs4 & mem4 & md4 & Hc4 & Hfx4 & Hcore4 & Hpres4 & _ & _ & _).
cbv beta in Hfx4. subst fx4 c4. rewrite Vr1'.
exact (K ly4 S4 W4 regs4 mem4 md4 Hcore4 (aregs_preserved_trans _ _ _ HP3 Hpres4)).
Qed.
End s3.

(* ======================================== the piece ======================================== *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x51cfc.
Hypothesis DCSV : forall fy : YK11.FPState,
  rt_drivable_csv_specX (fx := fy) rsegs B MT 0x84074 1 T_dcsv_STK 0x216c0 0x216e0 0x21700 0x216a0.
Hypothesis CCSV : forall fy : YK11.FPState, rt_check_csv_specX (fx := fy) rsegs B MT 0x838e0 2 T_csv_STK 0x21520.
Hypothesis IMGF : rate_A_img_facts rsegs B.

(* the C7 cut at a state the segment's frame reaches with the write set rs_E3, whose four registers hold
   S, R, the frame's shadow base and buf: the four real-frame cells and the frame's shadow are the start's *)
Lemma w14c_cut_C7 : forall (cx : rs_scx rsegs) fx4 ly4 S4 W4 regs4 mem4 md4,
rs_start_M03 (fx := fx) rsegs B cx ->
rs_core rsegs B MT cx (rs_E3 rsegs B cx) ly4 S4 W4 regs4 mem4 md4 ->
getr regs4 (Z_to_bv 5 8) = w64 (q_S (x_e cx)) -> getr regs4 (Z_to_bv 5 9) = w64 (q_R (x_e cx)) ->
getr regs4 (Z_to_bv 5 20) = w64 (shadow_addr (q_F (x_e cx))) -> getr regs4 (Z_to_bv 5 21) = w64 (q_buf (x_e cx)) ->
rt_fxk [10] fx fx4 ->
rs_cut_C7 (fx := fx) rsegs B MT cx fx4 ly4 S4 W4 regs4 mem4 md4.
Proof.
intros cx fx4 ly4 S4 W4 regs4 mem4 md4 Hst Hcore4 G8 G9 G20 G21 Hfx.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
destruct Hst as (Hpre & Hfsh & Hcut & Hfr & Hbuf0 & Hbin & Hbout & _).
pose proof (w14c_stack B cx Hpre) as (HR & HR16 & HRs & Hwin & Hceil & H47 & _).
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & _ & Hhdr & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
destruct Hhdr as (_ & _ & Hbln & _).
destruct (w14c_bl (q_buflen (x_e cx)) Hbln) as (Hblm & Hbl23 & Hblr).
rewrite Hblr in Hbceil, Hbapp.
assert (Hin3 : In (3, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (F32 & Fapp & _ & Fsh).
cbn [hi_cid rate_himg_A] in HF. rewrite <- HF in F32, Fapp, Fsh.
change (fs_frame_bytes 3) with 512 in Fapp, Fsh. change (512 / 8) with 64 in Fsh.
pose proof (rts_fbounds _ F32 Fapp) as (F4096 & Fceil & Fsh0 & Fshc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hcore4 as (_ & _ & _ & _ & _ & _ & HK).
rewrite HR in HK.
unfold T_SEG_STK, ASTACK in *.
(* the real frame's cells [R, R + 0x1e0): below S, in the journal's stack window, never runtime-owned *)
assert (Kstk : forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x1e0 ->
  aview rsegs (w_H W4) mem4 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha. apply HK; [lia | lia |]. unfold rs_E3. intros [Hw | [Hb | Hown']].
  - unfold rt_inw in Hw. cbn [hi_w3 rate_himg_A] in Hw. inversion Hw.
  - lia.
  - pose proof (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ
      ltac:(apply rts_awr_stk; lia)) as [_ Hno].
    exact (Hno Hown'). }
(* the frame's 64 shadow bytes: below the allocator's ceiling, apart from every block, never runtime-owned *)
assert (Ksh : forall i, 0 <= i < 64 ->
  aview rsegs (w_H W4) mem4 (shadow_addr (q_F (x_e cx)) + i) =
  aview rsegs (w_H (x_W cx)) (x_memc cx) (shadow_addr (q_F (x_e cx)) + i)).
{ intros i Hi. apply HK; [lia | lia |]. unfold rs_E3. intros [Hw | [Hb | Hown']].
  - unfold rt_inw in Hw. cbn [hi_w3 rate_himg_A] in Hw. inversion Hw.
  - pose proof (rts_fsh_of (q_F (x_e cx)) (8 * i) F32 ltac:(lia)) as E8.
    replace (8 * i / 8) with i in E8 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    apply (rtm_shadow_not_app (q_F (x_e cx) + 8 * i) (q_buf (x_e cx)) (rt_bl (q_buflen (x_e cx)))
      ltac:(lia) Hbapp).
    rewrite E8. exact Hb.
  - exact (proj2 (Fsh i Hi) Hown'). }
unfold rs_cut_C7.
split; [exact Hcore4|]. split; [exact Hfx|]. split.
- unfold rt_cut in Hcut |- *. cbn [hi_L6 hi_L7 rate_himg_A] in Hcut |- *.
  unfold rate_A_L56, rate_A_L56_tl in Hcut.
  rewrite !Forall_cons_iff in Hcut.
  destruct Hcut as (_ & _ & _ & _ & _ & _ & K18 & K78 & Kc0 & _ & K138 & _).
  cbn [fst snd rt_at rt_xv] in K18, K78, Kc0, K138.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rt_at rt_xv].
  + exact G8.
  + exact G9.
  + exact G20.
  + exact G21.
  + eapply (val_mem_kept rsegs); [|exact K18]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Kstk. lia.
  + eapply (val_mem_kept rsegs); [|exact K78]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Kstk. lia.
  + eapply (val_mem_kept rsegs); [|exact Kc0]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Kstk. lia.
  + eapply (val_mem_kept rsegs); [|exact K138]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Kstk. lia.
- unfold rs_fsh_at, rs_PB. cbn [hi_shB rate_himg_A] in Hfsh.
  apply (rtm_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi.
  pose proof rate_A_sh_len as (_ & LB). rewrite LB in Hi. change (Z.of_nat 56) with 56 in Hi.
  apply Ksh. lia.
Qed.

(* ---- W14 THE LIST: C6 0x82e98 -> C7 0x82ed4 ---- *)
Theorem rt_w14_csv_A : rs_piece_W14_csv_stmt rsegs B MT.
Proof using MTL AMEMSET DCSV CCSV IMGF.
unfold rs_piece_W14_csv_stmt. intros cx POST Hst HC7.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof Hst as (Hpre & Hfsh & Hcut & Hfr & Hbuf0 & Hbin & Hbout & Hfz).
pose proof (w14c_stack B cx Hpre) as (HR & HR16 & HRs & Hwin & Hceil & H47 & Hsp0al & Hev & Hgp & Htp).
assert (HR0 : 4096 <= q_R (x_e cx) < 2 ^ 47)
by (pose proof asan_consts as (Cc & _); unfold T_SEG_STK, ASTACK in *; lia).
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhdr & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
destruct Hhdr as (_ & Hmask & Hbln & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w14c_bl (q_buflen (x_e cx)) Hbln) as (Hblm & Hbl23 & Hblr).
rewrite Hblr in Hbceil, Hbapp, Hbpres.
unfold rt_cut in Hcut. cbn [hi_L6 rate_himg_A] in Hcut. unfold rate_A_L56, rate_A_L56_tl in Hcut.
rewrite !Forall_cons_iff in Hcut.
destruct Hcut as (C10 & C8 & C9 & C19 & C20 & C23 & _ & _ & _ & K120 & _ & _).
cbn [fst snd rt_at rt_xv] in C10, C8, C9, C19, C20, C23, K120.
rewrite Z.mod_small in K120 by lia.
(* ---- 1. C6 .. the memset entry 0x51cfc: beqz (not taken), mv s5,a0, a1 := 0x5a, a2 := s7, jal ---- *)
set (E1 := Ereg (x_regs cx) [w64 SHADOW_OFF]).
assert (E1_10 : ew E1 10 = w64 (q_buf (x_e cx)))
by (subst E1; rewrite (ew_Ereg_nat (x_regs cx) _ 10 10%bv eq_refl); exact C10).
assert (E1_23 : ew E1 23 = w64 (rt_bl (q_buflen (x_e cx))))
by (subst E1; rewrite (ew_Ereg_nat (x_regs cx) _ 23 23%bv eq_refl); exact C23).
assert (HE1 : E1 = Ereg (x_regs cx) [w64 SHADOW_OFF]) by reflexivity. clearbody E1.
assert (U10 : bv_unsigned (ew E1 10) = q_buf (x_e cx)) by (rewrite E1_10; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E1 (mkSS 0x82e98 sr_atoms [] None w14c_G1)
  (restrict (w_H (x_W cx)) (mkst (x_regs cx) (Z_to_bv 64 0x82e98) (x_memc cx) (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (w14c_entry 0x82e98 sr_atoms (x_regs cx) [w64 SHADOW_OFF] E1);
  [exact HE1 | rewrite HE1; apply regs_ok_Ereg | vm_compute; reflexivity | constructor | cbn; tauto |].
  split; [|split; [exact I | exact I]]. cbn [w14c_G1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10. repeat split; first [lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)]. }
assert (SHOK1 : sh_ok rsegs w14c_Bx [] E1 (mrestrict (w_H (x_W cx)) (x_memc cx))) by constructor.
assert (HAE1 : env_agree 32 (Ereg (x_regs cx) [w64 SHADOW_OFF]) E1) by (rewrite HE1; apply env_agree_refl).
change (hi_c6 rate_himg_A) with 0x82e98. unfold cfg_at. change (w64 0x82e98) with (Z_to_bv 64 0x82e98).
aj_run_tok w14c_tbl_ok HS HJ SHOK1 w14c_Bspan; [awr_ok_tac |].
rreg HS (10%bv : bv 5) Vr10. rreg HS (11%bv : bv 5) Vr11. rreg HS (12%bv : bv 5) Vr12.
rreg HS (21%bv : bv 5) Vr21. rreg HS (1%bv : bv 5) Vr1.
pose proof (regs_kept_of_st_ok rsegs E1 _ ms (x_regs cx) [w64 SHADOW_OFF] (w_H (x_W cx)) [1; 10; 11; 12; 21]%bv
  HS HAE1 ltac:(vm_compute; reflexivity)) as RK1.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 ->
  aview rsegs (w_H (x_W cx)) (ms_mem ms) a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha. apply (w14c_kept_run E1 _ (w_H (x_W cx)) (x_memc cx) (ms_mem ms) a HFr Ha).
  intros (r & Hr & _). cbn [ss_mem In] in Hr. destruct Hr. }
clear HF HFr HG.
assert (HspT1 : spZ (ms_regs ms) = q_R (x_e cx)) by (rewrite <- HR; unfold spZ; f_equal; w14_rk RK1).
pose proof (proj1 HJ) as HAR1.
destruct (rtm_blk_ra rsegs B _ _ _ _ _ (q_buf (x_e cx)) (rt_bl (q_buflen (x_e cx))) (q_buf (x_e cx))
  (rt_bl (q_buflen (x_e cx))) HAR1 Hbin ltac:(lia) ltac:(rewrite Hblr; lia)) as [Hra1 Hhv1].
rewrite (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E1 _ ms HS eq_refl).
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] => replace (ss_pc s) with 0x51cfc by (vm_compute; reflexivity) end.
eapply SRr_bind.
{ apply (rts_intrin_at B LAWS OSet 0x51cfc AMEMSET (x_W cx) (ms_regs ms) (ms_mem ms) (x_STK cx) (x_sp0 cx)
    (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_lyc cx) (x_Sc cx) _ (x_k cx)
    (q_buf (x_e cx)) 0x5a (rt_bl (q_buflen (x_e cx))) (q_R (x_e cx) - x_sp0 cx) (Z_to_bv 64 0x82eac) HJ).
  - etransitivity; [exact Vr10 | exact E1_10].
  - exact Vr11.
  - etransitivity; [exact Vr12 | exact E1_23].
  - lia.
  - lia.
  - lia.
  - rewrite HspT1. lia.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - transitivity (getr (x_regs cx) 3); [w14_rk RK1 | exact Hgp].
  - transitivity (getr (x_regs cx) 4); [w14_rk RK1 | exact Htp].
  - exact Vr1.
  - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (q_buf (x_e cx) + (a - q_buf (x_e cx))) by lia.
      apply (rt_fresh_awr_n _ _ _ _ _ _ _ _ _ Hbin Hbout ltac:(lia)). lia.
    + unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - apply (w14c_amem B _ _ _ _ _ _ _ _ _ HAR1 Hbin); rewrite ?Hblr; lia.
  - exact Hra1.
  - exact Hhv1.
  - exact I. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame2 & H102 & Heff2 & Hkeep2).
(* the registers after memset: callee-saved ones as at C6 (s5 = buf) *)
assert (P2 : getr regs2 (Z_to_bv 5 2) = getr (x_regs cx) (Z_to_bv 5 2))
by (rewrite (HP2 2 ltac:(unfold acallee_saved; lia)); w14_rk RK1).
assert (P3 : getr regs2 (Z_to_bv 5 3) = getr (x_regs cx) (Z_to_bv 5 3))
by (rewrite (HP2 3 ltac:(unfold acallee_saved; lia)); w14_rk RK1).
assert (P4 : getr regs2 (Z_to_bv 5 4) = getr (x_regs cx) (Z_to_bv 5 4))
by (rewrite (HP2 4 ltac:(unfold acallee_saved; lia)); w14_rk RK1).
assert (P8 : getr regs2 (Z_to_bv 5 8) = getr (x_regs cx) (Z_to_bv 5 8))
by (rewrite (HP2 8 ltac:(unfold acallee_saved; lia)); w14_rk RK1).
assert (P9 : getr regs2 (Z_to_bv 5 9) = getr (x_regs cx) (Z_to_bv 5 9))
by (rewrite (HP2 9 ltac:(unfold acallee_saved; lia)); w14_rk RK1).
assert (P19 : getr regs2 (Z_to_bv 5 19) = getr (x_regs cx) (Z_to_bv 5 19))
by (rewrite (HP2 19 ltac:(unfold acallee_saved; lia)); w14_rk RK1).
assert (P20 : getr regs2 (Z_to_bv 5 20) = getr (x_regs cx) (Z_to_bv 5 20))
by (rewrite (HP2 20 ltac:(unfold acallee_saved; lia)); w14_rk RK1).
assert (P21 : getr regs2 (Z_to_bv 5 21) = w64 (q_buf (x_e cx)))
by (rewrite (HP2 21 ltac:(unfold acallee_saved; lia)); etransitivity; [exact Vr21 | exact E1_10]).
(* the bytes after memset: every byte outside buf and the routine's window as at C6 *)
assert (KM12 : forall a, 0 <= a < 2 ^ 64 -> ~ (q_buf (x_e cx) <= a < q_buf (x_e cx) + rt_bl (q_buflen (x_e cx))) ->
  ~ (q_R (x_e cx) - ESTACK <= a < q_R (x_e cx)) ->
  aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha H1 H2. rewrite Hkeep2; [exact (KM1 a Ha) | exact Ha | exact H1 | lia]. }
assert (IO2 : same_io (x_mdc cx) md2)
by (eapply same_io_trans; [apply same_io_wvb | apply same_io_materialized; exact Hsame2]).
rename ms into ms1. rename mat into mat1.
(* ---- 2. 0x82eac .. the drivable_csv entry 0x84074: ld s2,0x120(s1); a0 := s2; a1 := s5; a2 := s3; jal ---- *)
set (E2 := Ereg regs2 [w64 SHADOW_OFF; w64 (q_mask (x_e cx))]).
assert (E2_9 : ew E2 9 = w64 (q_R (x_e cx)))
by (subst E2; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); etransitivity; [exact P9 | exact C9]).
assert (E2_19 : ew E2 19 = w64 (q_buflen (x_e cx)))
by (subst E2; rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl); etransitivity; [exact P19 | exact C19]).
assert (E2_21 : ew E2 21 = w64 (q_buf (x_e cx)))
by (subst E2; rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl); exact P21).
assert (E2_33 : ew E2 33 = w64 (q_mask (x_e cx))) by (subst E2; exact (ew_Ereg_extra regs2 _ 1)).
assert (HE2 : E2 = Ereg regs2 [w64 SHADOW_OFF; w64 (q_mask (x_e cx))]) by reflexivity. clearbody E2.
assert (U9 : bv_unsigned (ew E2 9) = q_R (x_e cx))
by (rewrite E2_9; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
assert (Hr120 : region_ok rsegs E2 (mrestrict (w_H (x_W cx)) mem2) w14c_r120).
{ unfold w14c_r120. apply (rtm_ro_region rsegs E2 (w_H (x_W cx)) mem2 9 (q_R (x_e cx)) 0x120 0x128);
  [exact U9 | lia | lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs E2 _ (q_R (x_e cx)) 0x120 8 (SOff 33 0) (q_mask (x_e cx))).
  - apply rts_den_atom; [exact E2_33 | lia].
  - change (8 * Z.of_N 8) with 64. lia.
  - cbn. lia.
  - change (N.to_nat 8) with 8%nat. eapply (val_mem_kept rsegs); [|exact K120].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
    apply KM12; unfold ESTACK, T_SEG_STK, ASTACK in *; lia. }
assert (HS2 : st_ok rsegs E2 (mkSS 0x82eac sr_atoms [w14c_r120] None (mkFacts [] [] []))
  (restrict (w_H (x_W cx)) (mkst regs2 (Z_to_bv 64 0x82eac) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (w14c_entry 0x82eac sr_atoms regs2 [w64 SHADOW_OFF; w64 (q_mask (x_e cx))] E2);
  [exact HE2 | rewrite HE2; apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact Hr120 | constructor]
  | cbn; tauto |].
  split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK2 : sh_ok rsegs w14c_Bx [] E2 (mrestrict (w_H (x_W cx)) mem2)) by constructor.
assert (HAE2 : env_agree 32 (Ereg regs2 [w64 SHADOW_OFF; w64 (q_mask (x_e cx))]) E2)
by (rewrite HE2; apply env_agree_refl).
aj_run_tok w14c_tbl_ok HS2 HJ2 SHOK2 w14c_Bspan; [awr_ok_tac |].
rreg HS2 (10%bv : bv 5) Vq10. rreg HS2 (11%bv : bv 5) Vq11. rreg HS2 (12%bv : bv 5) Vq12.
rreg HS2 (18%bv : bv 5) Vq18. rreg HS2 (1%bv : bv 5) Vq1.
pose proof (regs_kept_of_st_ok rsegs E2 _ ms regs2 [w64 SHADOW_OFF; w64 (q_mask (x_e cx))] (w_H (x_W cx))
  [1; 10; 11; 12; 18]%bv HS2 HAE2 ltac:(vm_compute; reflexivity)) as RK2.
assert (KM2 : forall a, 0 <= a < 2 ^ 64 ->
  aview rsegs (w_H (x_W cx)) (ms_mem ms) a = aview rsegs (w_H (x_W cx)) mem2 a).
{ intros a Ha. apply (w14c_kept_run E2 _ (w_H (x_W cx)) mem2 (ms_mem ms) a HFr Ha).
  intros (r & Hr & Hb). cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
  unfold w14c_r120 in Hb. cbn [YP09.r_wlo YP09.r_whi] in Hb. lia. }
assert (D10 : getr (ms_regs ms) 10 = w64 (q_mask (x_e cx))) by (etransitivity; [exact Vq10 | exact E2_33]).
assert (D11 : getr (ms_regs ms) 11 = w64 (q_buf (x_e cx))) by (etransitivity; [exact Vq11 | exact E2_21]).
assert (D12 : getr (ms_regs ms) 12 = w64 (q_buflen (x_e cx))) by (etransitivity; [exact Vq12 | exact E2_19]).
assert (D1 : getr (ms_regs ms) 1 = w64 0x82ec0) by exact Vq1.
assert (D18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (q_mask (x_e cx))) by (etransitivity; [exact Vq18 | exact E2_33]).
assert (D8 : getr (ms_regs ms) (Z_to_bv 5 8) = w64 (q_S (x_e cx)))
by (rewrite <- P8 in C8; rewrite <- C8; w14_rk RK2).
assert (D9 : getr (ms_regs ms) (Z_to_bv 5 9) = w64 (q_R (x_e cx)))
by (rewrite <- P9 in C9; rewrite <- C9; w14_rk RK2).
assert (D19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (q_buflen (x_e cx)))
by (rewrite <- P19 in C19; rewrite <- C19; w14_rk RK2).
assert (D20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (shadow_addr (q_F (x_e cx))))
by (rewrite <- P20 in C20; rewrite <- C20; w14_rk RK2).
assert (D21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 (q_buf (x_e cx))) by (rewrite <- P21; w14_rk RK2).
assert (KR : forall r : Z, r = 2 \/ r = 3 \/ r = 4 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)).
{ intros r [-> | [-> | ->]]; [rewrite <- P2 | rewrite <- P3 | rewrite <- P4]; w14_rk RK2. }
assert (HspD : spZ (ms_regs ms) = q_R (x_e cx)).
{ rewrite <- HR. unfold spZ. f_equal. exact (KR 2 ltac:(lia)). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreD : rs_core rsegs B MT cx (rs_E3 rsegs B cx) (x_lyc cx) (x_Sc cx) (x_W cx) (ms_regs ms) (ms_mem ms) mdT)
end.
{ split; [exact HJ2|]. split; [exact KR|]. split; [reflexivity|]. split; [apply Permutation_refl|].
  split; [eapply same_io_trans; [exact IO2 | apply same_io_wvb]|]. split; [apply (mo_le_refl MT MTL)|].
  intros a Ha Hs He. rewrite (KM2 a Ha). apply KM12; [exact Ha | |].
  - intros X. apply He. unfold rs_E3. right. left. exact X.
  - rewrite HR in Hs. unfold ESTACK, T_SEG_STK, ASTACK in *. lia. }
pose proof (w14c_rom_kept B MT cx _ _ _ _ _ _ Hpre Hbin HcoreD) as RKD.
pose proof (proj1 HJ2) as HARD.
destruct (w14c_statics B MT IMGF cx _ _ _ _ _ _ Hpre Hbin HcoreD) as (Sfmt & Scomma & Sempty & Tord & _).
destruct (rtm_blk_ra rsegs B _ _ _ _ _ (q_buf (x_e cx)) (rt_bl (q_buflen (x_e cx))) (q_buf (x_e cx))
  (q_buflen (x_e cx)) HARD Hbin ltac:(lia) ltac:(rewrite Hblr; lia)) as [HraD HhvD].
lazymatch goal with HS' : st_ok _ _ ?ss (restrict _ ms) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H (x_W cx)) E2 ss ms HS' eq_refl);
  replace (ss_pc ss) with 0x84074 by (vm_compute; reflexivity)
end.
eapply SRr_bind.
{ apply (DCSV fx (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    (x_lyc cx) (x_Sc cx) (x_W cx) (ms_mem ms) _ (x_k cx) (ms_regs ms)
    (q_mask (x_e cx)) (q_buf (x_e cx)) (q_buflen (x_e cx))).
  - apply (w14c_pre_call B MT cx _ _ _ _ _ _ _ T_dcsv_STK Hpre HcoreD);
    [ rewrite D1; vm_compute; reflexivity
    | unfold raZ; rewrite D1; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspD | unfold T_dcsv_STK, T_SEG_STK, ASTACK, ESTACK; lia ].
  - exact D10.
  - lia.
  - exact D11.
  - exact D12.
  - lia.
  - intros Hn. split; [lia|]. split; [lia|].
    split; [exists (rt_bl (q_buflen (x_e cx))); split; [exact Hbin|]; split; [exact Hbout | lia]|].
    split; [exact HraD|]. split; [exact (HhvD Hn)|].
    split; [apply (w14c_amem B _ _ _ _ _ _ _ _ _ HARD Hbin); rewrite ?Hblr; lia|].
    left. rewrite HspD. unfold T_dcsv_STK, T_SEG_STK, ASTACK, ESTACK in *. lia.
  - lia.
  - rewrite Hfr. vm_compute. reflexivity.
  - exact Sfmt.
  - exact Scomma.
  - exact Sempty.
  - exact Tord.
  - exact RKD.
  - exact Hfz. }
intros W3 c3 _ Hpost.
destruct (w14c_core_call B MT MTL cx (rs_E3 rsegs B cx)
  (fun x => aowned B (x_lyc cx) (x_Sc cx) x \/
            (0 < q_buflen (x_e cx) /\ q_buf (x_e cx) <= x < q_buf (x_e cx) + q_buflen (x_e cx)))
  T_dcsv_STK _ _ _ _ _ _ _ _ _ W3 c3 Hpre HcoreD HspD ltac:(unfold T_dcsv_STK, T_SEG_STK, ASTACK, ESTACK; lia)
  ltac:(intros a [Ha | (_ & Ha)]; unfold rs_E3; [right; right; exact Ha | right; left; lia]) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & HO3 & Hkept3 & HR3).
subst c3. rewrite D1.
(* ---- 3. at drivable_csv's float state: the third run and check_csv, then C7 ---- *)
apply (w14c_s3 (fx := fx3) B MT MTL (CCSV fx3) IMGF cx POST ly3 S3 W3 regs3 mem3 md3 Hpre Hfr Hbin Hcore3).
- rewrite <- HspD. unfold spZ. f_equal. exact (Hpres3 2 ltac:(unfold acallee_saved; lia)).
- exact (proj1 HR3).
- etransitivity; [exact (Hpres3 21 ltac:(unfold acallee_saved; lia)) | exact D21].
- etransitivity; [exact (Hpres3 19 ltac:(unfold acallee_saved; lia)) | exact D19].
- etransitivity; [exact (Hpres3 18 ltac:(unfold acallee_saved; lia)) | exact D18].
- intros Hn0 j Hj. cbn [length] in Hj. destruct j as [|j]; [|lia].
  cbn [nth]. split; [|lia].
  assert (Hav : aview rsegs (w_H W3) mem3 (q_buf (x_e cx) + Z.of_nat 0) = Some 0x5a).
  { change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    rewrite Hkept3.
    - rewrite (KM2 (q_buf (x_e cx)) ltac:(lia)). pose proof (Heff2 0 ltac:(lia)) as H0.
      rewrite Z.add_0_r in H0. exact H0.
    - lia.
    - unfold T_dcsv_STK, ESTACK, T_SEG_STK, ASTACK in *. lia.
    - intros [Ho | (Hn & _)]; [exact (proj2 (Hbpres (q_buf (x_e cx)) ltac:(lia)) Ho) | lia]. }
  exact (proj1 (rtm_aview_val1 rsegs (w_H W3) mem3 _ 0x5a Hav)).
- exact (proj2 HR3).
- exact HO3.
- intros ly4 S4 W4 regs4 mem4 md4 Hcore4 Hpres4.
  apply (HC7 fx3 ly4 S4 W4 regs4 mem4 md4).
  apply (w14c_cut_C7 cx fx3 ly4 S4 W4 regs4 mem4 md4 Hst Hcore4).
  + etransitivity; [exact (Hpres4 8 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact (Hpres3 8 ltac:(unfold acallee_saved; lia)) | exact D8].
  + etransitivity; [exact (Hpres4 9 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact (Hpres3 9 ltac:(unfold acallee_saved; lia)) | exact D9].
  + etransitivity; [exact (Hpres4 20 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact (Hpres3 20 ltac:(unfold acallee_saved; lia)) | exact D20].
  + etransitivity; [exact (Hpres4 21 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact (Hpres3 21 ltac:(unfold acallee_saved; lia)) | exact D21].
  + exact Hfx3.
Qed.
(* inside the Section: the kernel's axioms and the five Section hypotheses named in the header *)
Print Assumptions rt_w14_csv_A.
End m.
Print Assumptions rt_w14_csv_A.
