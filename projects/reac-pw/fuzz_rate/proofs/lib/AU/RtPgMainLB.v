(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are
   restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc from
   proofs/libreac/fuzz_knock/lib/A/APgCSpec.v (the Section form of its lines 32-164) and
   proofs/libreac/fuzz_knock/lib/A/ACfn.v (lines 27-71, the harness contract tfib_lib_pre_x / _post_x /
   _contract_x; its lines 72-73, tfib_lib_contract_x_all, are not carried here) at origin/ossv/recipes
   6ebe35ba632, with their module paths changed (h-small-a3). rule 24 (reuse): no function is proved here;
   this file states the three ASan-level contracts only.

   THE QDISC CHANGES, and why each one is there.
   - knock's three callees (reac_knock_init / _heard / _step) write a 40-byte struct in the caller's fake
     frame; qdisc's two callees (reac_qdisc_etf_catchup_slots, check_slots) are register-only leaves that
     write nothing but check_slots' own return-address slot. So kn_post_* 's object clause (obj_at) and
     its FOUR memory conjuncts -- the stack side above alloc_ceiling outside the callee's window, the live
     blocks, the frames and their shadow, and the image -- are replaced by ONE memory clause,
     `aview W2 mem2 a = aview W memc a` outside [sp - STK_f, sp), which implies all four and needs no
     object. Its proof needs no block, separation or frame law of AR either (knock's four conjuncts needed
     AR's block and separation facts to place the object): check_slots' walk takes from the caller's
     journal only its stack-presence clause (`forall a, sp0 - STK <= a < sp0 -> apresent ..`) and astk_ok
     (sp0's alignment and bounds), with the contract's two stack-window premises. Both posts state the
     clause in that same shape, so the text does not depend on
     the value of either STK_f. T_slots_STK is 0 (the leaf has no frame: `addi a2,zero,1` is its first
     instruction in both images, image A 0x7e94c and image B 0x7e984, no sp move; at 0 the excluded window
     is empty and the clause holds at every address), T_check_STK is 16 (image A 0x7e870 and image B
     0x7e8a4 `addi sp,sp,-0x10`, then `sd ra,8(sp)`).
   - both leaves divide by 10^6 with the 8-byte constant 0x431BDE82D7B634DB = ceil(2 ^ 82 / 10 ^ 6)
     (lib/Prog/qdisc_div.v:7-10). The load is NOT shadow-checked in either image (image A
     `auipc a1,0xfff92` 0x7e8b4 + `ld a1,-0x564(a1)` 0x7e8b8 -> 0x10350, and the same cell 0x10350 in the
     asan-ubsan image from 0x7e8e8 / -0x598; capstone 5.0.7 over the pinned bytes). The cell is .rodata, so
     its value is not derivable from an abstract `segs`: the contract takes its ADDRESS as a parameter `am`
     and its value as the premise `val_mem segs .. am 8 QD_MAGIC`. Each image discharges that premise from
     its own read-only-data fact. The constant is image-shared: the 8 bytes at 0x10350 are
     0x431BDE82D7B634DB in both fuzz_qdisc.asan (980e2b845852) and fuzz_qdisc.asan-ubsan (eb657d77bd4b),
     read out of the pinned files by this lane and checked independently by h-small-a3; only `am` could
     differ between images (here both load 0x10350).
   - the result: catchup's post pins a0 to slots_spec (lib/Prog/qdisc_spec.v:8-11, the C source's
     slots_of); check_slots returns void, and its contract's content is that it RETURNS -- its abort
     (the abort call at image A 0x7e8dc, reached only from `bne a0,a3` at 0x7e8cc) is
     unreachable when a0 is slots_spec of the same (lead, fps). That is the harness's property.
   - the harness contract is ACfn's text with knock's names changed and its read-only premise written over
     lib/A/QPgBase.v's image-independent in_roP / arodata_okP, so that image B instantiates the same text.

   IMAGE-INDEPENDENT: this file Requires no image module. `segs`, the symbol record `B`, the meter `MT`,
   the sink `K`, the entry addresses and the harness constants are all Section variables or parameters. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCSpec.v, with its module paths and module names changed; 6 of its 69 lines of code are new or changed and 64 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgMainC.v, with its module paths changed; 144 of its 166 lines of code are new or changed and 47 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgMainL.v at 3c7e900fc63 (its lines 1-232: the loop-head bounds and role_build_holds) for reac-pw/fuzz_headamp image A; module paths changed, the rs_ prefix renamed to hs_ (lib/A/HPgSeg.v), role_build_contract to headamp_build_contract, the bounds read by explicit patterns over HPgSeg's cuts; role's check half (lines 234-305) is not taken: headamp's checking segment is closed by lib/A/HPgSegM.v headamp_check_holds. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgMainL.v, with its module paths changed; 199 of its 285 lines of code are new or changed and 80 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgMainL.v at ad0e022f7af7 for reac-pw/fuzz_rate
   image A: role's two middle contracts and pieces become rate's three (lib/A/RtPgCSpec.v rate_build_contract,
   rate_check_contract, rate_csv_contract over lib/A/RtPgSeg.v's pieces); the build's latch has a third entry (from the
   Int-7 piece), the checks' tail becomes the asked[] set-up, the decide loop (closed by its two turns) and its tail,
   and the list segment is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgMainL.v at af0538adbf24 for image B
   (fuzz_rate.asan-ubsan): the pieces are lib/AU/RtPgSegB.v's (rs_ -> rsb_), the record is RtPgImgB.rate_himg_B, and the
   build's latch has two entries (from the Struct's close and, at LATCH7, from the shape-7 and the Int-7 pieces). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): THE THREE MIDDLE SEGMENTS of
   LLVMFuzzerTestOneInput (0x8076c), closed from their pieces.

     rate_build_holds : rate_build_contract segs B MT rate_himg_B RLO RHI   (M01, C1 0x80ae4 -> C2 0x82a2c)
     rate_check_holds : rate_check_contract segs B MT rate_himg_B RLO RHI   (M02, C3 0x82a30 -> C4 0x82f9c)
     rate_csv_holds   : rate_csv_contract segs B MT rate_himg_B RLO RHI     (M03, C6 0x82fb0 -> C7 0x82fec)

   Each takes the piece statements of lib/AU/RtPgSegB.v as Section hypotheses (one per piece) and adds no walk: it
   fixes the segment's data cx from the contract's quantifiers (RtPgSegB.rsb_scx), shows that the contract's premises
   are the pieces' common premise (rsb_start_M01 / rsb_start_M02 / rsb_start_M03), takes POST := the contract's own
   post, chains the pieces by application, and closes the loops by induction on the loop index, the index being an
   argument of the head's continuation (RtPgSegB.v section f):
   - the pod loop (head C 0x813a0): on 32 - k, k = |es| pods written; a head state has (|es| < 32)%nat
     (rsb_pod_base), so at fuel 0 the head is unreachable;
   - the property loop (head N 0x80fb4): on 3 - i, i = |ps|; a head state has |ps| < np <= 3 (rsb_cut_N);
   - the corruption loop (head R 0x82960): on 8 - kk; a head state has kk <= |bs| <= 7 (rsb_cut_R, rsb_corr_wf);
   - the expect_rate scan (outer head O 0x82b48, inner I 0x82b74): the outer on 33 - j, j <= |ents rec| <= 32
     (rsb_scan_inv, Model.ents_wf of the record's pod_rec_wf); the inner on 32 - m, m < |ents rec| (rsb_cut_I); a key
     found at m >= j hands the outer head the index m + 2 > j, and below j the key cut is unreachable (at0 <= m);
   - the decide loop (head DEC 0x82e44): exactly two turns; a head state has t < 2 (rsb_cut_DEC), so the turn after
     the second is unreachable and the two turns close by applying the turn's piece twice.
   The last cut of each segment (rsb_cut_C2 at hi_c2, rsb_cut_C4 at hi_c4, rsb_cut_C7 at hi_c7) is the contract's post,
   discharged by SRr_ret. Statement of no function here beyond the three contracts: their walks are the pieces'. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.

(* ================================ the loop heads' bounds ================================
   Each head state carries its index's bound among its conjuncts; rsb_split takes a cut apart (the cuts' own
   sub-predicates rsb_core, rsb_in, ... stay folded) and lia reads the bound. *)
Ltac rsb_split := repeat match goal with H : _ /\ _ |- _ => destruct H end.

Lemma rsb_cut_C_bound : forall cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2,
rsb_cut_C segs B MT cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 -> (length es < 32)%nat.
Proof.
intros cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 HC.
unfold rsb_cut_C, rsb_pod_base in HC. rsb_split. lia.
Qed.

Lemma rsb_cut_N_bound : forall cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2,
rsb_cut_N segs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 -> (length ps < 3)%nat.
Proof.
intros cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 HN.
unfold rsb_cut_N in HN. rsb_split. lia.
Qed.

Lemma rsb_cut_R_bound : forall cx sh ps rest r off bs cnt kk ly2 S2 W2 regs2 mem2 md2,
rsb_cut_R segs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 -> (kk <= 7)%nat.
Proof.
intros cx sh ps rest r off bs cnt kk ly2 S2 W2 regs2 mem2 md2 HR.
unfold rsb_cut_R, rsb_corr_wf in HR. rsb_split. lia.
Qed.

Lemma rsb_cut_O_bound : forall cx fx2 rec j ly2 S2 W2 regs2 mem2 md2,
rsb_cut_O (fx := fx) segs B MT cx fx2 rec j ly2 S2 W2 regs2 mem2 md2 -> (j <= 32)%nat.
Proof.
intros cx fx2 rec j ly2 S2 W2 regs2 mem2 md2 HO.
unfold rsb_cut_O, rsb_chk_base, rsb_scan_inv in HO. rsb_split.
match goal with H : pod_rec_wf rec |- _ => destruct (ents_wf rec H) end. lia.
Qed.

Lemma rsb_cut_I_bound : forall cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2,
rsb_cut_I (fx := fx) segs B MT cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2 -> (m < 32)%nat.
Proof.
intros cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2 HI.
unfold rsb_cut_I, rsb_chk_base in HI. rsb_split.
match goal with H : pod_rec_wf rec |- _ => destruct (ents_wf rec H) end. lia.
Qed.

Lemma rsb_cut_KM_from : forall cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2,
rsb_cut_KM (fx := fx) segs B MT cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2 -> (at0 <= m)%nat.
Proof.
intros cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2 HK.
unfold rsb_cut_KM in HK. rsb_split. lia.
Qed.

Lemma rsb_cut_DEC_bound : forall cx fx2 rec t ly2 S2 W2 regs2 mem2 md2,
rsb_cut_DEC (fx := fx) segs B MT cx fx2 rec t ly2 S2 W2 regs2 mem2 md2 -> (t < 2)%nat.
Proof.
intros cx fx2 rec t ly2 S2 W2 regs2 mem2 md2 HD.
unfold rsb_cut_DEC in HD. rsb_split. lia.
Qed.

(* ================================ M01, the build ================================ *)
Section build.
(* C1 -> the object's header *)
Hypothesis PW3a : rsb_piece_W3a_stmt segs B MT.
(* the two headers and the property loop's preheader *)
Hypothesis PW3b_hdr : rsb_piece_W3b_hdr_stmt segs B MT.
Hypothesis PW3b_b7 : rsb_piece_W3b_b7_stmt segs B MT.
Hypothesis PW3b_pre : rsb_piece_W3b_pre_stmt segs B MT.
(* one property's selector, its shape-7 body, its key, and the latch from its two entries *)
Hypothesis PW4_sel : rsb_piece_W4_sel_stmt segs B MT.
Hypothesis PW4_int7 : rsb_piece_W4_int7_stmt segs B MT.
Hypothesis PW4_key : rsb_piece_W4_key_stmt segs B MT.
Hypothesis PW4_latch : rsb_piece_W4_latch_stmt segs B MT.
(* the Int-7 value pod (it enters the latch at LATCH7), the params Struct's header and count, and its close *)
Hypothesis PW5_int : rsb_piece_W5_int_stmt segs B MT.
Hypothesis PW5_open : rsb_piece_W5_open_stmt segs B MT.
Hypothesis PW5_close : rsb_piece_W5_close_stmt segs B MT.
(* the switch's dispatch and its cases 1 .. 9 *)
Hypothesis PW6a_disp : rsb_piece_W6a_disp_stmt segs B MT.
Hypothesis PW6a_cases : rsb_piece_W6a_cases_stmt segs B MT.
Hypothesis PW6b : rsb_piece_W6b_stmt segs B MT.
Hypothesis PW6c : rsb_piece_W6c_stmt segs B MT.
(* case 0 *)
Hypothesis PW7a : rsb_piece_W7a_stmt segs B MT.
Hypothesis PW7b : rsb_piece_W7b_stmt segs B MT.
(* the call pod_write_ent(pp, e62) and the record copy *)
Hypothesis PW8 : rsb_piece_W8_stmt segs B MT.
(* the top size word, the corruption and the second request *)
Hypothesis PW10_post : rsb_piece_W10_post_stmt segs B MT.
Hypothesis PW10_corr : rsb_piece_W10_corr_stmt segs B MT.
Hypothesis PW10_req : rsb_piece_W10_req_stmt segs B MT.

(* every case entry of the switch, from the join: the ten values of kd mod 10 *)
Lemma rsb_cases_all : forall cx POST rest i k kd,
rsb_start_M01 segs B cx rest -> rsb_from_J segs B MT cx POST rest i k -> rsb_from_D segs B MT cx POST rest i k kd.
Proof.
intros cx POST rest i k kd HS HJ.
assert (Hm : 0 <= kd mod 10 < 10) by (apply Z.mod_pos_bound; lia).
assert (Hc : kd mod 10 = 0 \/ kd mod 10 = 1 \/ kd mod 10 = 2 \/ kd mod 10 = 3 \/ kd mod 10 = 4 \/
  kd mod 10 = 5 \/ kd mod 10 = 6 \/ kd mod 10 = 7 \/ kd mod 10 = 8 \/ kd mod 10 = 9) by lia.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]].
- exact (proj1 (PW7a cx POST rest i k kd HS E (PW7b cx POST rest i k HS HJ))).
- apply (PW6b cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
- apply (PW6a_cases cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
- apply (PW6a_cases cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
- apply (PW6b cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
- apply (PW6b cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
- apply (PW6c cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
- apply (PW6c cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
- apply (PW6c cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
- apply (PW6b cx POST rest i k kd HS); [rewrite E; cbn [In]; tauto | exact HJ].
Qed.

(* the pod loop, closed: from its head at any k, given the Struct's close *)
Lemma rsb_pods_closed : forall cx POST rest i,
rsb_start_M01 segs B cx rest -> rsb_from_CL segs B MT cx POST rest i ->
forall k, rsb_from_C segs B MT cx POST rest i k.
Proof.
intros cx POST rest i HS HCL.
assert (H : forall f k, (32 - k <= f)%nat -> rsb_from_C segs B MT cx POST rest i k).
{ induction f as [|f IH]; intros k Hk.
  - intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r Hps Hes HC. exfalso.
    pose proof (rsb_cut_C_bound cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 HC). lia.
  - assert (HJ : rsb_from_J segs B MT cx POST rest i k)
      by exact (PW8 cx POST rest i k HS (IH (S k) ltac:(lia)) HCL).
    apply (PW6a_disp cx POST rest i k HS).
    + intros kd. exact (rsb_cases_all cx POST rest i k kd HS HJ).
    + exact (proj2 (PW7a cx POST rest i k 0 HS eq_refl (PW7b cx POST rest i k HS HJ))). }
intros k. exact (H (32 - k)%nat k (le_n _)).
Qed.

(* the property loop, closed: from its head at any i, given the builder's end *)
Lemma rsb_props_closed : forall cx POST rest,
rsb_start_M01 segs B cx rest -> rsb_from_P1 segs B MT cx POST rest ->
forall i, rsb_from_N segs B MT cx POST rest i.
Proof.
intros cx POST rest HS HP1.
assert (H : forall f i, (3 - i <= f)%nat -> rsb_from_N segs B MT cx POST rest i).
{ induction f as [|f IH]; intros i Hi.
  - intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hps HN. exfalso.
    pose proof (rsb_cut_N_bound cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 HN). lia.
  - destruct (PW4_latch cx POST rest i HS (IH (S i) ltac:(lia)) HP1) as (HL & HL7).
    assert (HCL : rsb_from_CL segs B MT cx POST rest i) by exact (PW5_close cx POST rest i HS HL).
    apply (PW4_sel cx POST rest i HS).
    + exact (PW4_int7 cx POST rest i HS HL7).
    + apply (PW4_key cx POST rest i HS).
      * exact (PW5_open cx POST rest i HS (rsb_pods_closed cx POST rest i HS HCL 0%nat) HCL).
      * exact (PW5_int cx POST rest i HS HL7). }
intros i. exact (H (3 - i)%nat i (le_n _)).
Qed.

(* the corruption loop, closed: from its head at any kk, given its exit *)
Lemma rsb_corr_closed : forall cx POST rest,
rsb_start_M01 segs B cx rest -> rsb_from_RT segs B MT cx POST rest ->
forall kk, rsb_from_R segs B MT cx POST rest kk.
Proof.
intros cx POST rest HS HRT.
assert (H : forall f kk, (8 - kk <= f)%nat -> rsb_from_R segs B MT cx POST rest kk).
{ induction f as [|f IH]; intros kk Hk.
  - intros ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt HR. exfalso.
    pose proof (rsb_cut_R_bound cx sh ps rest r off bs cnt kk ly2 S2 W2 regs2 mem2 md2 HR). lia.
  - exact (PW10_corr cx POST rest kk HS (IH (S kk) ltac:(lia)) HRT). }
intros kk. exact (H (8 - kk)%nat kk (le_n _)).
Qed.

Theorem rate_build_holds : forall RLO RHI : Z, rate_build_contract segs B MT rate_himg_B RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos rest
  HPRE Hfsh HL1 Hleft Hlen Harr Hra Hsrc Hhi Hamem Hhull Hdis.
match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : rsb_scx segs).
assert (HS : rsb_start_M01 segs B cx rest).
{ exact (conj HPRE (conj Hfsh (conj HL1 (conj Hlen (conj Hleft (conj Harr (conj Hra (conj Hhull (conj Hamem
    (conj Hsrc (conj Hhi Hdis))))))))))). }
(* the contract's post, as the pieces' POST; the build's last cut is it *)
assert (HC2 : rsb_from_C2 segs B MT cx POST rest).
{ intros ly2 S2 W2 regs2 mem2 md2 (Hcore & HL2 & Hfsh2 & Hpp2 & _).
  destruct Hcore as (HJ & Hr & Hfr & Hperm & Hio & Hmo & Hkept).
  apply SRr_ret. exists fx, ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HJ|]. split; [exact Hr|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
  split; [exact Hkept|]. split; [exact HL2|]. split; [exact Hfsh2 | exact Hpp2]. }
assert (HRT := PW10_req cx POST rest HS HC2).
destruct (PW10_post cx POST rest HS (rsb_corr_closed cx POST rest HS HRT) HRT HC2) as [HP HP1].
assert (HPH := PW3b_pre cx POST rest HS (rsb_props_closed cx POST rest HS HP1 0%nat) HP).
exact (PW3a cx POST rest HS (PW3b_b7 cx POST rest HS HPH) (PW3b_hdr cx POST rest HS HPH)).
Qed.
End build.

(* ================================ M02, the checks ================================ *)
Section check.
(* the second block's fill, the parse, the record's tests and the two scan loops *)
Hypothesis PW11a_head : rsb_piece_W11a_head_stmt segs B MT.
Hypothesis PW11a_setup : rsb_piece_W11a_setup_stmt segs B MT.
Hypothesis PW11a_outer : rsb_piece_W11a_outer_stmt segs B MT.
Hypothesis PW11a_inner : rsb_piece_W11a_inner_stmt segs B MT.
(* the key compare, the value's readers and the three checks *)
Hypothesis PW11b_key : rsb_piece_W11b_key_stmt segs B MT.
Hypothesis PW11b_checks : rsb_piece_W11b_checks_stmt segs B MT.
(* one decide turn *)
Hypothesis PW13 : rsb_piece_W13_stmt segs B MT.
(* the asked[] set-up and the decide loop's tail *)
Hypothesis PW14_asked : rsb_piece_W14_asked_stmt segs B MT.
Hypothesis PW14_tail : rsb_piece_W14_tail_stmt segs B MT.

(* the inner scan, closed: from its head at any m, given the key cuts of this scan *)
Lemma rsb_inner_closed : forall cx POST inp at0,
rsb_start_M02 segs B cx inp -> rsb_from_ABS segs B MT cx POST ->
(forall m, rsb_from_KM segs B MT cx POST at0 m) -> forall m, rsb_from_I segs B MT cx POST at0 m.
Proof.
intros cx POST inp at0 HS HABS HKM.
assert (H : forall f m, (32 - m <= f)%nat -> rsb_from_I segs B MT cx POST at0 m).
{ induction f as [|f IH]; intros m Hm.
  - intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HI. exfalso.
    pose proof (rsb_cut_I_bound cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2 HI). lia.
  - exact (PW11a_inner cx POST inp at0 m HS (IH (S m) ltac:(lia)) (HKM m) HABS). }
intros m. exact (H (32 - m)%nat m (le_n _)).
Qed.

(* the outer scan, closed: from its head at any j *)
Lemma rsb_outer_closed : forall cx POST inp,
rsb_start_M02 segs B cx inp -> rsb_from_ABS segs B MT cx POST -> rsb_from_MAL segs B MT cx POST ->
rsb_from_A segs B MT cx POST -> forall j, rsb_from_O segs B MT cx POST j.
Proof.
intros cx POST inp HS HABS HMAL HA.
assert (H : forall f j, (33 - j <= f)%nat -> rsb_from_O segs B MT cx POST j).
{ induction f as [|f IH]; intros j Hj.
  - intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HO. exfalso.
    pose proof (rsb_cut_O_bound cx fx2 rec j ly2 S2 W2 regs2 mem2 md2 HO). lia.
  - apply (PW11a_outer cx POST inp j HS); [|exact HABS].
    apply (rsb_inner_closed cx POST inp j HS HABS). intros m.
    destruct (Nat.lt_ge_cases m j) as [Hlt|Hge].
    + intros fx2 ly2 S2 W2 regs2 mem2 md2 rec kb HK. exfalso.
      pose proof (rsb_cut_KM_from cx fx2 rec j m kb ly2 S2 W2 regs2 mem2 md2 HK). lia.
    + exact (PW11b_key cx POST inp j m HS (IH (S (S m)) ltac:(lia)) HABS HMAL HA). }
intros j. exact (H (33 - j)%nat j (le_n _)).
Qed.

(* the decide loop, closed: its two turns from the first, given its tail *)
Lemma rsb_decide_closed : forall cx POST inp,
rsb_start_M02 segs B cx inp -> rsb_from_T2 segs B MT cx POST -> rsb_from_DEC segs B MT cx POST 0.
Proof.
intros cx POST inp HS HT.
assert (H2 : rsb_from_DEC segs B MT cx POST 2).
{ intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HD. exfalso.
  pose proof (rsb_cut_DEC_bound cx fx2 rec 2 ly2 S2 W2 regs2 mem2 md2 HD). lia. }
exact (PW13 cx POST inp 0%nat HS (PW13 cx POST inp 1%nat HS H2 HT) HT).
Qed.

Theorem rate_check_holds : forall RLO RHI : Z, rate_check_contract segs B MT rate_himg_B RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos inp
  HPRE Hfsh HL3 Hlen Hpp Hpod Hin Hnin Hfrm.
match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : rsb_scx segs).
assert (HS : rsb_start_M02 segs B cx inp).
{ exact (conj HPRE (conj Hfsh (conj HL3 (conj Hlen (conj Hpp (conj Hpod (conj Hin (conj Hnin Hfrm)))))))). }
(* the contract's post, as the pieces' POST; the checks' last cut is it *)
assert (HC4 : rsb_from_C4 segs B MT cx POST).
{ intros fx2 ly2 S2 W2 regs2 mem2 md2 (Hcore & Hfxk & HL4 & Hfsh4).
  destruct Hcore as (HJ & Hr & Hfr & Hperm & Hio & Hmo & Hkept).
  apply SRr_ret. exists fx2, ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact Hfxk|]. split; [exact HJ|]. split; [exact Hr|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
  split; [exact Hkept|]. split; [exact HL4 | exact Hfsh4]. }
assert (HT := PW14_tail cx POST inp HS HC4).
assert (HA := PW14_asked cx POST inp HS (rsb_decide_closed cx POST inp HS HT)).
destruct (PW11b_checks cx POST inp HS HA) as [HABS HMAL].
assert (HE := PW11a_setup cx POST inp HS (rsb_outer_closed cx POST inp HS HABS HMAL HA 0%nat) HABS HMAL).
exact (PW11a_head cx POST inp HS HE HMAL HA).
Qed.
End check.

(* ================================ M03, the list ================================ *)
Section csv.
(* memset(buf, 0x5a, bl), reac_rate_drivable_csv and check_csv: C6 -> C7, no internal cut *)
Hypothesis PW14_csv : rsb_piece_W14_csv_stmt segs B MT.

Theorem rate_csv_holds : forall RLO RHI : Z, rate_csv_contract segs B MT rate_himg_B RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos
  HPRE Hfsh HL6 Hfr Hbuf Hin Hnin Hfrm.
match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : rsb_scx segs).
assert (HS : rsb_start_M03 segs B cx).
{ exact (conj HPRE (conj Hfsh (conj HL6 (conj Hfr (conj Hbuf (conj Hin (conj Hnin Hfrm))))))). }
(* the contract's post, as the piece's POST; the list's last cut is it *)
assert (HC7 : rsb_from_C7 segs B MT cx POST).
{ intros fx2 ly2 S2 W2 regs2 mem2 md2 (Hcore & Hfxk & HL7 & Hfsh7).
  destruct Hcore as (HJ & Hr & Hfr2 & Hperm & Hio & Hmo & Hkept).
  apply SRr_ret. exists fx2, ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact Hfxk|]. split; [exact HJ|]. split; [exact Hr|].
  split; [exact Hfr2|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
  split; [exact Hkept|]. split; [exact HL7 | exact Hfsh7]. }
exact (PW14_csv cx POST HS HC7).
Qed.
End csv.
End b.

Print Assumptions rate_build_holds.
Print Assumptions rate_check_holds.
Print Assumptions rate_csv_holds.
