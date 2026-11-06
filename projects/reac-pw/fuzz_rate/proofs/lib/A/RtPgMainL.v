(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgMainL.v at ad0e022f7af7 for reac-pw/fuzz_rate
   image A: role's two middle contracts and pieces become rate's three (lib/A/RtPgCSpec.v rate_build_contract,
   rate_check_contract, rate_csv_contract over lib/A/RtPgSeg.v's pieces); the build's latch has a third entry (from the
   Int-7 piece), the checks' tail becomes the asked[] set-up, the decide loop (closed by its two turns) and its tail,
   and the list segment is new. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): THE THREE MIDDLE SEGMENTS of
   LLVMFuzzerTestOneInput (0x80714), closed from their pieces.

     rate_build_holds : rate_build_contract segs B MT rate_himg_A RLO RHI   (M01, C1 0x809e0 -> C2 0x828b4)
     rate_check_holds : rate_check_contract segs B MT rate_himg_A RLO RHI   (M02, C3 0x828b8 -> C4 0x82e84)
     rate_csv_holds   : rate_csv_contract segs B MT rate_himg_A RLO RHI     (M03, C6 0x82e98 -> C7 0x82ed4)

   Each takes the piece statements of lib/A/RtPgSeg.v as Section hypotheses (one per piece) and adds no walk: it fixes
   the segment's data cx from the contract's quantifiers (RtPgSeg.rs_scx), shows that the contract's premises are the
   pieces' common premise (rs_start_M01 / rs_start_M02 / rs_start_M03), takes POST := the contract's own post, chains
   the pieces by application, and closes the loops by induction on the loop index, the index being an argument of
   the head's continuation (RtPgSeg.v section f):
   - the pod loop (head C 0x8127c): on 32 - k, k = |es| pods written; a head state has (|es| < 32)%nat
     (rs_pod_base), so at fuel 0 the head is unreachable;
   - the property loop (head N 0x80e10): on 3 - i, i = |ps|; a head state has |ps| < np <= 3 (rs_cut_N);
   - the corruption loop (head R 0x82808): on 8 - kk; a head state has kk <= |bs| <= 7 (rs_cut_R, rs_corr_wf);
   - the expect_rate scan (outer head O 0x829c0, inner head I 0x829e4): the outer on 33 - j, j <= |ents rec| <= 32
     (rs_scan_inv, Model.ents_wf of the record's pod_rec_wf); the inner on 32 - m, m < |ents rec| (rs_cut_I); a key
     found at m >= j hands the outer head the index m + 2 > j, and below j the key cut is unreachable (at0 <= m);
   - the decide loop (head DEC 0x82d14): exactly two turns; a head state has t < 2 (rs_cut_DEC), so the turn after
     the second is unreachable and the two turns close by applying the turn's piece twice.
   The last cut of each segment (rs_cut_C2 at hi_c2, rs_cut_C4 at hi_c4, rs_cut_C7 at hi_c7) is the contract's post,
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg.
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
   Each head state carries its index's bound among its conjuncts; rs_split takes a cut apart (the cuts' own
   sub-predicates rs_core, rs_in, ... stay folded) and lia reads the bound. *)
Ltac rs_split := repeat match goal with H : _ /\ _ |- _ => destruct H end.

Lemma rs_cut_C_bound : forall cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2,
rs_cut_C segs B MT cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 -> (length es < 32)%nat.
Proof.
intros cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 HC.
unfold rs_cut_C, rs_pod_base in HC. rs_split. lia.
Qed.

Lemma rs_cut_N_bound : forall cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2,
rs_cut_N segs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 -> (length ps < 3)%nat.
Proof.
intros cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 HN.
unfold rs_cut_N in HN. rs_split. lia.
Qed.

Lemma rs_cut_R_bound : forall cx sh ps rest r off bs cnt kk ly2 S2 W2 regs2 mem2 md2,
rs_cut_R segs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 -> (kk <= 7)%nat.
Proof.
intros cx sh ps rest r off bs cnt kk ly2 S2 W2 regs2 mem2 md2 HR.
unfold rs_cut_R, rs_corr_wf in HR. rs_split. lia.
Qed.

Lemma rs_cut_O_bound : forall cx fx2 rec j ly2 S2 W2 regs2 mem2 md2,
rs_cut_O (fx := fx) segs B MT cx fx2 rec j ly2 S2 W2 regs2 mem2 md2 -> (j <= 32)%nat.
Proof.
intros cx fx2 rec j ly2 S2 W2 regs2 mem2 md2 HO.
unfold rs_cut_O, rs_chk_base, rs_scan_inv in HO. rs_split.
match goal with H : pod_rec_wf rec |- _ => destruct (ents_wf rec H) end. lia.
Qed.

Lemma rs_cut_I_bound : forall cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2,
rs_cut_I (fx := fx) segs B MT cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2 -> (m < 32)%nat.
Proof.
intros cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2 HI.
unfold rs_cut_I, rs_chk_base in HI. rs_split.
match goal with H : pod_rec_wf rec |- _ => destruct (ents_wf rec H) end. lia.
Qed.

Lemma rs_cut_KM_from : forall cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2,
rs_cut_KM (fx := fx) segs B MT cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2 -> (at0 <= m)%nat.
Proof.
intros cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2 HK.
unfold rs_cut_KM in HK. rs_split. lia.
Qed.

Lemma rs_cut_DEC_bound : forall cx fx2 rec t ly2 S2 W2 regs2 mem2 md2,
rs_cut_DEC (fx := fx) segs B MT cx fx2 rec t ly2 S2 W2 regs2 mem2 md2 -> (t < 2)%nat.
Proof.
intros cx fx2 rec t ly2 S2 W2 regs2 mem2 md2 HD.
unfold rs_cut_DEC in HD. rs_split. lia.
Qed.

(* ================================ M01, the build ================================ *)
Section build.
(* C1 -> the object's header *)
Hypothesis PW3a : rs_piece_W3a_stmt segs B MT.
(* the two headers and the property loop's preheader *)
Hypothesis PW3b_hdr : rs_piece_W3b_hdr_stmt segs B MT.
Hypothesis PW3b_b7 : rs_piece_W3b_b7_stmt segs B MT.
Hypothesis PW3b_pre : rs_piece_W3b_pre_stmt segs B MT.
(* one property's selector, its shape-7 body, its key, and the latch from its three entries *)
Hypothesis PW4_sel : rs_piece_W4_sel_stmt segs B MT.
Hypothesis PW4_int7 : rs_piece_W4_int7_stmt segs B MT.
Hypothesis PW4_key : rs_piece_W4_key_stmt segs B MT.
Hypothesis PW4_latch : rs_piece_W4_latch_stmt segs B MT.
(* the Int-7 value pod, the params Struct's header and count, and its close *)
Hypothesis PW5_int : rs_piece_W5_int_stmt segs B MT.
Hypothesis PW5_open : rs_piece_W5_open_stmt segs B MT.
Hypothesis PW5_close : rs_piece_W5_close_stmt segs B MT.
(* the switch's dispatch and its cases 1 .. 9 *)
Hypothesis PW6a_disp : rs_piece_W6a_disp_stmt segs B MT.
Hypothesis PW6a_cases : rs_piece_W6a_cases_stmt segs B MT.
Hypothesis PW6b : rs_piece_W6b_stmt segs B MT.
Hypothesis PW6c : rs_piece_W6c_stmt segs B MT.
(* case 0 *)
Hypothesis PW7a : rs_piece_W7a_stmt segs B MT.
Hypothesis PW7b : rs_piece_W7b_stmt segs B MT.
(* the inlined pod_write_ent and the record copy *)
Hypothesis PW8 : rs_piece_W8_stmt segs B MT.
(* the top size word, the corruption and the second request *)
Hypothesis PW10_post : rs_piece_W10_post_stmt segs B MT.
Hypothesis PW10_corr : rs_piece_W10_corr_stmt segs B MT.
Hypothesis PW10_req : rs_piece_W10_req_stmt segs B MT.

(* every case entry of the switch, from the join: the ten values of kd mod 10 *)
Lemma rs_cases_all : forall cx POST rest i k kd,
rs_start_M01 segs B cx rest -> rs_from_J segs B MT cx POST rest i k -> rs_from_D segs B MT cx POST rest i k kd.
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
Lemma rs_pods_closed : forall cx POST rest i,
rs_start_M01 segs B cx rest -> rs_from_CL segs B MT cx POST rest i ->
forall k, rs_from_C segs B MT cx POST rest i k.
Proof.
intros cx POST rest i HS HCL.
assert (H : forall f k, (32 - k <= f)%nat -> rs_from_C segs B MT cx POST rest i k).
{ induction f as [|f IH]; intros k Hk.
  - intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r Hps Hes HC. exfalso.
    pose proof (rs_cut_C_bound cx sh np ps cnt es rest r ly2 S2 W2 regs2 mem2 md2 HC). lia.
  - assert (HJ : rs_from_J segs B MT cx POST rest i k)
      by exact (PW8 cx POST rest i k HS (IH (S k) ltac:(lia)) HCL).
    apply (PW6a_disp cx POST rest i k HS).
    + intros kd. exact (rs_cases_all cx POST rest i k kd HS HJ).
    + exact (proj2 (PW7a cx POST rest i k 0 HS eq_refl (PW7b cx POST rest i k HS HJ))). }
intros k. exact (H (32 - k)%nat k (le_n _)).
Qed.

(* the property loop, closed: from its head at any i, given the builder's end *)
Lemma rs_props_closed : forall cx POST rest,
rs_start_M01 segs B cx rest -> rs_from_P1 segs B MT cx POST rest ->
forall i, rs_from_N segs B MT cx POST rest i.
Proof.
intros cx POST rest HS HP1.
assert (H : forall f i, (3 - i <= f)%nat -> rs_from_N segs B MT cx POST rest i).
{ induction f as [|f IH]; intros i Hi.
  - intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hps HN. exfalso.
    pose proof (rs_cut_N_bound cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 HN). lia.
  - destruct (PW4_latch cx POST rest i HS (IH (S i) ltac:(lia)) HP1) as (HL & HLI & HL7).
    assert (HCL : rs_from_CL segs B MT cx POST rest i) by exact (PW5_close cx POST rest i HS HL).
    apply (PW4_sel cx POST rest i HS).
    + exact (PW4_int7 cx POST rest i HS HL7).
    + apply (PW4_key cx POST rest i HS).
      * exact (PW5_open cx POST rest i HS (rs_pods_closed cx POST rest i HS HCL 0%nat) HCL).
      * exact (PW5_int cx POST rest i HS HLI). }
intros i. exact (H (3 - i)%nat i (le_n _)).
Qed.

(* the corruption loop, closed: from its head at any kk, given its exit *)
Lemma rs_corr_closed : forall cx POST rest,
rs_start_M01 segs B cx rest -> rs_from_RT segs B MT cx POST rest ->
forall kk, rs_from_R segs B MT cx POST rest kk.
Proof.
intros cx POST rest HS HRT.
assert (H : forall f kk, (8 - kk <= f)%nat -> rs_from_R segs B MT cx POST rest kk).
{ induction f as [|f IH]; intros kk Hk.
  - intros ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt HR. exfalso.
    pose proof (rs_cut_R_bound cx sh ps rest r off bs cnt kk ly2 S2 W2 regs2 mem2 md2 HR). lia.
  - exact (PW10_corr cx POST rest kk HS (IH (S kk) ltac:(lia)) HRT). }
intros kk. exact (H (8 - kk)%nat kk (le_n _)).
Qed.

Theorem rate_build_holds : forall RLO RHI : Z, rate_build_contract segs B MT rate_himg_A RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos rest
  HPRE Hfsh HL1 Hleft Hlen Harr Hra Hsrc Hhi Hamem Hhull Hdis.
match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : rs_scx segs).
assert (HS : rs_start_M01 segs B cx rest).
{ exact (conj HPRE (conj Hfsh (conj HL1 (conj Hlen (conj Hleft (conj Harr (conj Hra (conj Hhull (conj Hamem
    (conj Hsrc (conj Hhi Hdis))))))))))). }
(* the contract's post, as the pieces' POST; the build's last cut is it *)
assert (HC2 : rs_from_C2 segs B MT cx POST rest).
{ intros ly2 S2 W2 regs2 mem2 md2 (Hcore & HL2 & Hfsh2 & Hpp2 & _).
  destruct Hcore as (HJ & Hr & Hfr & Hperm & Hio & Hmo & Hkept).
  apply SRr_ret. exists fx, ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HJ|]. split; [exact Hr|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
  split; [exact Hkept|]. split; [exact HL2|]. split; [exact Hfsh2 | exact Hpp2]. }
assert (HRT := PW10_req cx POST rest HS HC2).
destruct (PW10_post cx POST rest HS (rs_corr_closed cx POST rest HS HRT) HRT HC2) as [HP HP1].
assert (HPH := PW3b_pre cx POST rest HS (rs_props_closed cx POST rest HS HP1 0%nat) HP).
exact (PW3a cx POST rest HS (PW3b_b7 cx POST rest HS HPH) (PW3b_hdr cx POST rest HS HPH)).
Qed.
End build.

(* ================================ M02, the checks ================================ *)
Section check.
(* the second block's fill, the parse, the record's tests and the two scan loops *)
Hypothesis PW11a_head : rs_piece_W11a_head_stmt segs B MT.
Hypothesis PW11a_setup : rs_piece_W11a_setup_stmt segs B MT.
Hypothesis PW11a_outer : rs_piece_W11a_outer_stmt segs B MT.
Hypothesis PW11a_inner : rs_piece_W11a_inner_stmt segs B MT.
(* the key compare, the value's readers and the three checks *)
Hypothesis PW11b_key : rs_piece_W11b_key_stmt segs B MT.
Hypothesis PW11b_checks : rs_piece_W11b_checks_stmt segs B MT.
(* one decide turn *)
Hypothesis PW13 : rs_piece_W13_stmt segs B MT.
(* the asked[] set-up and the decide loop's tail *)
Hypothesis PW14_asked : rs_piece_W14_asked_stmt segs B MT.
Hypothesis PW14_tail : rs_piece_W14_tail_stmt segs B MT.

(* the inner scan, closed: from its head at any m, given the key cuts of this scan *)
Lemma rs_inner_closed : forall cx POST inp at0,
rs_start_M02 segs B cx inp -> rs_from_ABS segs B MT cx POST ->
(forall m, rs_from_KM segs B MT cx POST at0 m) -> forall m, rs_from_I segs B MT cx POST at0 m.
Proof.
intros cx POST inp at0 HS HABS HKM.
assert (H : forall f m, (32 - m <= f)%nat -> rs_from_I segs B MT cx POST at0 m).
{ induction f as [|f IH]; intros m Hm.
  - intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HI. exfalso.
    pose proof (rs_cut_I_bound cx fx2 rec at0 m ly2 S2 W2 regs2 mem2 md2 HI). lia.
  - exact (PW11a_inner cx POST inp at0 m HS (IH (S m) ltac:(lia)) (HKM m) HABS). }
intros m. exact (H (32 - m)%nat m (le_n _)).
Qed.

(* the outer scan, closed: from its head at any j *)
Lemma rs_outer_closed : forall cx POST inp,
rs_start_M02 segs B cx inp -> rs_from_ABS segs B MT cx POST -> rs_from_MAL segs B MT cx POST ->
rs_from_A segs B MT cx POST -> forall j, rs_from_O segs B MT cx POST j.
Proof.
intros cx POST inp HS HABS HMAL HA.
assert (H : forall f j, (33 - j <= f)%nat -> rs_from_O segs B MT cx POST j).
{ induction f as [|f IH]; intros j Hj.
  - intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HO. exfalso.
    pose proof (rs_cut_O_bound cx fx2 rec j ly2 S2 W2 regs2 mem2 md2 HO). lia.
  - apply (PW11a_outer cx POST inp j HS); [|exact HABS].
    apply (rs_inner_closed cx POST inp j HS HABS). intros m.
    destruct (Nat.lt_ge_cases m j) as [Hlt|Hge].
    + intros fx2 ly2 S2 W2 regs2 mem2 md2 rec kb HK. exfalso.
      pose proof (rs_cut_KM_from cx fx2 rec j m kb ly2 S2 W2 regs2 mem2 md2 HK). lia.
    + exact (PW11b_key cx POST inp j m HS (IH (S (S m)) ltac:(lia)) HABS HMAL HA). }
intros j. exact (H (33 - j)%nat j (le_n _)).
Qed.

(* the decide loop, closed: its two turns from the first, given its tail *)
Lemma rs_decide_closed : forall cx POST inp,
rs_start_M02 segs B cx inp -> rs_from_T2 segs B MT cx POST -> rs_from_DEC segs B MT cx POST 0.
Proof.
intros cx POST inp HS HT.
assert (H2 : rs_from_DEC segs B MT cx POST 2).
{ intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HD. exfalso.
  pose proof (rs_cut_DEC_bound cx fx2 rec 2 ly2 S2 W2 regs2 mem2 md2 HD). lia. }
exact (PW13 cx POST inp 0%nat HS (PW13 cx POST inp 1%nat HS H2 HT) HT).
Qed.

Theorem rate_check_holds : forall RLO RHI : Z, rate_check_contract segs B MT rate_himg_A RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos inp
  HPRE Hfsh HL3 Hlen Hpp Hpod Hin Hnin Hfrm.
match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : rs_scx segs).
assert (HS : rs_start_M02 segs B cx inp).
{ exact (conj HPRE (conj Hfsh (conj HL3 (conj Hlen (conj Hpp (conj Hpod (conj Hin (conj Hnin Hfrm)))))))). }
(* the contract's post, as the pieces' POST; the checks' last cut is it *)
assert (HC4 : rs_from_C4 segs B MT cx POST).
{ intros fx2 ly2 S2 W2 regs2 mem2 md2 (Hcore & Hfxk & HL4 & Hfsh4).
  destruct Hcore as (HJ & Hr & Hfr & Hperm & Hio & Hmo & Hkept).
  apply SRr_ret. exists fx2, ly2, S2, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact Hfxk|]. split; [exact HJ|]. split; [exact Hr|].
  split; [exact Hfr|]. split; [exact Hperm|]. split; [exact Hio|]. split; [exact Hmo|].
  split; [exact Hkept|]. split; [exact HL4 | exact Hfsh4]. }
assert (HT := PW14_tail cx POST inp HS HC4).
assert (HA := PW14_asked cx POST inp HS (rs_decide_closed cx POST inp HS HT)).
destruct (PW11b_checks cx POST inp HS HA) as [HABS HMAL].
assert (HE := PW11a_setup cx POST inp HS (rs_outer_closed cx POST inp HS HABS HMAL HA 0%nat) HABS HMAL).
exact (PW11a_head cx POST inp HS HE HMAL HA).
Qed.
End check.

(* ================================ M03, the list ================================ *)
Section csv.
(* memset(buf, 0x5a, bl), reac_rate_drivable_csv and check_csv: C6 -> C7, no internal cut *)
Hypothesis PW14_csv : rs_piece_W14_csv_stmt segs B MT.

Theorem rate_csv_holds : forall RLO RHI : Z, rate_csv_contract segs B MT rate_himg_A RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos
  HPRE Hfsh HL6 Hfr Hbuf Hin Hnin Hfrm.
match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
set (cx := {| x_STK := STK; x_sp0 := sp0; x_FP := FP; x_ly := ly; x_S := S; x_W0 := W0; x_mem0 := mem0;
  x_md0 := md0; x_own := own; x_k := k; x_regs := regs; x_lyc := lyc; x_Sc := Sc; x_W := W; x_memc := memc;
  x_mdc := mdc; x_RLO := RLO; x_RHI := RHI; x_e := e; x_pos := pos |} : rs_scx segs).
assert (HS : rs_start_M03 segs B cx).
{ exact (conj HPRE (conj Hfsh (conj HL6 (conj Hfr (conj Hbuf (conj Hin (conj Hnin Hfrm))))))). }
(* the contract's post, as the piece's POST; the list's last cut is it *)
assert (HC7 : rs_from_C7 segs B MT cx POST).
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
