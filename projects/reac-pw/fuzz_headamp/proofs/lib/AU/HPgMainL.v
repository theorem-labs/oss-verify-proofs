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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgMainC.v, with its module paths and module names changed; 130 of its 153 lines of code are new or changed and 46 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): THE BUILD SEGMENT M01 of
   LLVMFuzzerTestOneInput (0x80c40), closed from its pieces.

     headamp_build_holds : headamp_build_contract segs B MT I RLO RHI   (M01, C1 hi_c1 I -> C2 hi_c2 I)

   for any segments, symbols, meter, image record I and builder pcs BI; image B's walk takes it at Img0U.rsegs,
   headamp_himg_B (C1 0x80fcc, C2 0x82efc) and headamp_bld_B. It takes the 21 piece statements of
   lib/AU/HPgSeg.v as Section hypotheses (one per piece) and adds no walk: it fixes the segment's data cx from the
   contract's quantifiers (HPgSeg.hsu_scx), shows that the contract's premises are the pieces' common premise
   (hsu_start_M01), takes POST := the contract's own post, chains the pieces by application, and closes the loops
   by induction on the loop index, the index being an argument of the head's continuation (HPgSeg.v section f):
   - the pod loop (head C bi_C, 0x81888 in image B): on 32 - k, k = |es| pods written; a head state has
     (|es| < 32)%nat (hsu_pod_base), so at fuel 0 the head is unreachable;
   - the property loop (head N bi_N, 0x81494): on 3 - i, i = |ps|; a head state has |ps| < np <= 3 (hsu_cut_N);
     image B's latch (bi_LATCH, 0x82ae4) has one entry, which the shape-7 body, the Int-7 value pod and the
     params Struct's close all reach (image A's latch has two);
   - the corruption loop (head R bi_R, 0x82e2c): on 8 - kk; a head state has kk < cnt <= 7 (hsu_cut_R,
     hsu_corr_wf).
   The last cut of the segment (hsu_cut_C2 at hi_c2 I) is the contract's post, discharged by SRr_ret.
   Proves no function of its own (kind: segment lemma; the walks are the pieces'). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Variable I : hd_himg.
Variable BI : hsu_bld.

(* ================================ M01, the build ================================ *)
Section build.
(* C1 -> the object's header *)
Hypothesis PW3a : hsu_piece_W3a_stmt segs B MT I BI.
(* the two headers and the property loop's preheader *)
Hypothesis PW3b_hdr : hsu_piece_W3b_hdr_stmt segs B MT I BI.
Hypothesis PW3b_b7 : hsu_piece_W3b_b7_stmt segs B MT I BI.
Hypothesis PW3b_pre : hsu_piece_W3b_pre_stmt segs B MT I BI.
(* one property's selector, its shape-7 body, its key, and the latch *)
Hypothesis PW4_sel : hsu_piece_W4_sel_stmt segs B MT I BI.
Hypothesis PW4_int7 : hsu_piece_W4_int7_stmt segs B MT I BI.
Hypothesis PW4_key : hsu_piece_W4_key_stmt segs B MT I BI.
Hypothesis PW4_latch : hsu_piece_W4_latch_stmt segs B MT I BI.
(* the Int-7 value pod, the params Struct's header and count, and its close *)
Hypothesis PW5_int : hsu_piece_W5_int_stmt segs B MT I BI.
Hypothesis PW5_open : hsu_piece_W5_open_stmt segs B MT I BI.
Hypothesis PW5_close : hsu_piece_W5_close_stmt segs B MT I BI.
(* the switch's dispatch and its cases 1 .. 9 *)
Hypothesis PW6a_disp : hsu_piece_W6a_disp_stmt segs B MT I BI.
Hypothesis PW6a_cases : hsu_piece_W6a_cases_stmt segs B MT I BI.
Hypothesis PW6b : hsu_piece_W6b_stmt segs B MT I BI.
Hypothesis PW6c : hsu_piece_W6c_stmt segs B MT I BI.
(* case 0 *)
Hypothesis PW7a : hsu_piece_W7a_stmt segs B MT I BI.
Hypothesis PW7b : hsu_piece_W7b_stmt segs B MT I BI.
(* the call of pod_write_ent and the record copy *)
Hypothesis PW8 : hsu_piece_W8_stmt segs B MT I BI.
(* the top size word, the corruption and the second request *)
Hypothesis PW10_post : hsu_piece_W10_post_stmt segs B MT I BI.
Hypothesis PW10_corr : hsu_piece_W10_corr_stmt segs B MT I BI.
Hypothesis PW10_req : hsu_piece_W10_req_stmt segs B MT I BI.

(* every case entry of the switch, from the join: the ten values of kd mod 10 *)
Lemma hsu_cases_all : forall cx POST rest i k kd,
hsu_start_M01 segs B I cx rest -> hsu_from_J segs B MT I BI cx POST rest i k ->
hsu_from_D segs B MT I BI cx POST rest i k kd.
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

(* the pod loop, closed: from its head at any k, given the Struct's close. A head state's pod base carries
   (|es| < 32)%nat (hsu_pod_base, its 17th conjunct). *)
Lemma hsu_pods_closed : forall cx POST rest i,
hsu_start_M01 segs B I cx rest -> hsu_from_CL segs B MT I BI cx POST rest i ->
forall k, hsu_from_C segs B MT I BI cx POST rest i k.
Proof.
intros cx POST rest i HS HCL.
assert (H : forall f k, (32 - k <= f)%nat -> hsu_from_C segs B MT I BI cx POST rest i k).
{ induction f as [|f IH]; intros k Hk.
  - intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r Hps Hes HC. exfalso.
    destruct HC as (HB & _).
    destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlt & _).
    lia.
  - assert (HJ : hsu_from_J segs B MT I BI cx POST rest i k)
      by exact (PW8 cx POST rest i k HS (IH (S k) ltac:(lia)) HCL).
    apply (PW6a_disp cx POST rest i k HS).
    + intros kd. exact (hsu_cases_all cx POST rest i k kd HS HJ).
    + exact (proj2 (PW7a cx POST rest i k 0 HS eq_refl (PW7b cx POST rest i k HS HJ))). }
intros k. exact (H (32 - k)%nat k (le_n _)).
Qed.

(* the property loop, closed: from its head at any i, given the builder's end. A head state carries
   |ps| < np <= 3 (hsu_cut_N, its 10th and 11th conjuncts). *)
Lemma hsu_props_closed : forall cx POST rest,
hsu_start_M01 segs B I cx rest -> hsu_from_P1 segs B MT I BI cx POST rest ->
forall i, hsu_from_N segs B MT I BI cx POST rest i.
Proof.
intros cx POST rest HS HP1.
assert (H : forall f i, (3 - i <= f)%nat -> hsu_from_N segs B MT I BI cx POST rest i).
{ induction f as [|f IH]; intros i Hi.
  - intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hps HN. exfalso.
    destruct HN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlt & Hle & _).
    lia.
  - assert (HL : hsu_from_LATCH segs B MT I BI cx POST rest i)
      by exact (PW4_latch cx POST rest i HS (IH (S i) ltac:(lia)) HP1).
    assert (HCL : hsu_from_CL segs B MT I BI cx POST rest i) by exact (PW5_close cx POST rest i HS HL).
    apply (PW4_sel cx POST rest i HS).
    + exact (PW4_int7 cx POST rest i HS HL).
    + apply (PW4_key cx POST rest i HS).
      * exact (PW5_open cx POST rest i HS (hsu_pods_closed cx POST rest i HS HCL 0%nat) HCL).
      * exact (PW5_int cx POST rest i HS HL). }
intros i. exact (H (3 - i)%nat i (le_n _)).
Qed.

(* the corruption loop, closed: from its head at any kk, given its exit. A head state carries kk < cnt <= 7
   (hsu_cut_R's 11th conjunct and hsu_corr_wf's 4th). *)
Lemma hsu_corr_closed : forall cx POST rest,
hsu_start_M01 segs B I cx rest -> hsu_from_RT segs B MT I BI cx POST rest ->
forall kk, hsu_from_R segs B MT I BI cx POST rest kk.
Proof.
intros cx POST rest HS HRT.
assert (H : forall f kk, (8 - kk <= f)%nat -> hsu_from_R segs B MT I BI cx POST rest kk).
{ induction f as [|f IH]; intros kk Hk.
  - intros ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt HR. exfalso.
    destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hwf & Hkk & _).
    destruct Hwf as (_ & _ & _ & Hc & _).
    lia.
  - exact (PW10_corr cx POST rest kk HS (IH (S kk) ltac:(lia)) HRT). }
intros kk. exact (H (8 - kk)%nat kk (le_n _)).
Qed.

Theorem headamp_build_holds : forall RLO RHI : Z, headamp_build_contract segs B MT I RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos rest
  HPRE HL1 Hleft Hlen Harr Hra Hsrc Hhi Hamem Hhull Hdis.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : hsu_scx segs).
assert (HS : hsu_start_M01 segs B I cx rest).
{ exact (conj HPRE (conj HL1 (conj Hlen (conj Hleft (conj Harr (conj Hra (conj Hhull (conj Hamem
    (conj Hsrc (conj Hhi Hdis)))))))))). }
(* the contract's post, as the pieces' POST; the build's last cut is it *)
assert (HC2 : hsu_from_C2 segs B MT I cx
  (hd_seg_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c2 I)
   (fun f => f = fx) (fun a => hd_inw e (hi_w1 I) a \/ e_pp e <= a < e_pp e + Layout.PP_SIZE)
   (fun W2 regs2 mem2 => hd_cut segs (w_H W2) mem2 regs2 e (hi_L2 I) /\
    hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shA I) /\
    garr8 segs (mrestrict (w_H W2) mem2) (e_pp e)
    (hd_zbytes (Layout.pp_bytes (fst (Model.pod_build rest)))))) rest).
{ intros ly2 S2 W2 regs2 mem2 md2 (Hcore & HL2 & Hfsh & Hpp & _).
  destruct Hcore as (HJ & Hr & Hfr & Hperm & Hio & Hmo & Hkept).
  apply SRr_ret. exists fx, ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HJ|]. split; [exact Hr|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
  split; [exact Hkept|]. split; [exact HL2|]. split; [exact Hfsh | exact Hpp]. }
assert (HRT := PW10_req cx _ rest HS HC2).
destruct (PW10_post cx _ rest HS (hsu_corr_closed cx _ rest HS HRT) HRT HC2) as [HP HP1].
assert (HPH := PW3b_pre cx _ rest HS (hsu_props_closed cx _ rest HS HP1 0%nat) HP).
exact (PW3a cx _ rest HS (PW3b_b7 cx _ rest HS HPH) (PW3b_hdr cx _ rest HS HPH)).
Qed.
End build.
End b.

Print Assumptions headamp_build_holds.
