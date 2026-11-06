(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the facts the two pieces of the cell write and the last four checks of the walk of
   LLVMFuzzerTestOneInput (0x80bc0) share, over lib/A/HPgSegM.v's cuts of the checking segment M03. Proves no
   function (kind: segment lemma).

   WHAT IS HERE.
   - he_seg / he_blk: the geometry the segment's start facts give (HPgSeg.hs_pre, i.e. HPgCSpec.hd_seg_pre at image
     A's record): the frame for locals F is the class-4 frame the harness holds, 32-aligned, in application memory,
     below the allocator's ceiling and outside the image; R is a stack address at or above the ceiling plus the
     callees' stack; every block live at the segment's start lies below the ceiling, in application memory and
     apart from F (YG0d AR_sep_law).
   - he_hc_core: a cut's journal-and-frame part (HPgSeg.hs_core) gives the call adapters' frame of facts
     (HPgCalls.hc_core) at R; he_core_call and he_core_blk carry hs_core across a call (the adapters' post) and
     across a block of straight-line code (HPgSteps.hd_blk_postE's clauses).
   - he_base3_kept: what every cut inside M03 carries (HPgSegM.hq_base3) stays true when only the callees' stack
     [R - T_SEG_STK, R), the 136 bytes of the frame object x (F + 0x1a0) and x's 17 shadow granules (52 .. 68) may
     have changed, with the frame's new shadow pattern and the new float state given. The errno cell's place is
     the image's (YCbq.api_env), which keeps it apart from all three.
   - he_ans_exp: on an uncorrupted record the parse's answer is expect_of's (Pod/Headamp.v
     parse_model_encode_any), for either null flag.
   SECTION HYPOTHESES: MTL : ameter_laws MT (the meter's order is a preorder: the cut's meter clause across a call)
   and errno_low : api_env rsegs B (YCbq.v: the errno cell lies in the image, below kLowMemEnd). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem HPgCalls.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================= lists and the model ======================================= *)
Lemma he_pairwise_app : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) x y,
YG0f.pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|a l1 IH]; intros l2 x y HP Hx Hy; [destruct Hx|].
cbn [app YG0f.pairwise] in HP. destruct HP as [HF HP]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hy.
- exact (IH l2 x y HP Hx Hy).
Qed.

(* On an uncorrupted record the parse's answer is expect_of's, for either null flag (fuzz_headamp.c:333-340:
   the parse of NULL and expect_of with the null flag both give (-1, [], (0, 0, NONE))). *)
Lemma he_ans_exp : forall (cx : hs_scx rsegs) (r : Model.pod_rec),
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_null (x_e rsegs cx) <= 1 ->
hq_ans rsegs cx r = hq_exp rsegs cx r.
Proof.
intros cx r Hwf Hc Hn. unfold hq_ans, hq_exp, hd_props.
assert (Hb : Model.buf r = Model.pod_encode r).
{ unfold Model.corrupt in Hc. unfold Model.buf. destruct (Model.p_corr r); [discriminate Hc | reflexivity]. }
destruct (Z.eq_dec (e_null (x_e rsegs cx)) 0) as [H0|H0].
- rewrite H0. cbn [Z.eqb]. cbn [parse_props]. rewrite Hb. apply parse_model_encode_any. exact Hwf.
- assert (H1 : e_null (x_e rsegs cx) = 1) by lia. rewrite H1. reflexivity.
Qed.

(* the answer's parts (Spec/HeadBytes.v answer_ok_parts) and its cells' length *)
Lemma he_ans_ok : forall (cx : hs_scx rsegs) r, 0 <= e_cap (x_e rsegs cx) <= 9 ->
answer_ok (e_cap (x_e rsegs cx)) (hq_ans rsegs cx r) /\
(length (ans_cells (hq_ans rsegs cx r)) <= X_CELLS)%nat /\
Z.of_nat (length (ans_cells (hq_ans rsegs cx r))) <= e_cap (x_e rsegs cx).
Proof.
intros cx r Hc. pose proof (parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r)) (e_cap (x_e rsegs cx))
  ltac:(lia)) as HO. fold (hq_ans rsegs cx r) in HO.
split; [exact HO|].
apply answer_ok_parts in HO as [[(_ & E2 & _) | (E1 & E2 & _)] _].
- rewrite E2. cbn [length]. unfold X_CELLS. split; lia.
- unfold X_CELLS. split; lia.
Qed.

(* expect_of's answer: n is the number of cells, and so is rc unless the record is not a Props object (or the null
   flag is set), when rc = -1 with no cell *)
Lemma he_exp_n : forall (cx : hs_scx rsegs) r,
ans_n (hq_exp rsegs cx r) = Z.of_nat (length (ans_cells (hq_exp rsegs cx r))) /\
(ans_rc (hq_exp rsegs cx r) = -1 \/ ans_rc (hq_exp rsegs cx r) = Z.of_nat (length (ans_cells (hq_exp rsegs cx r)))).
Proof.
intros cx r. unfold hq_exp, expect_model.
destruct ((e_null (x_e rsegs cx) =? 1) || negb (Model.is_props r)); [cbn; split; [reflexivity | left; reflexivity]|].
destruct (negb (Model.params_struct r)); [cbn; split; [reflexivity | right; reflexivity]|].
destruct (ha_fold expect_cell (e_cap (x_e rsegs cx)) (Accessors.pairs (Model.ents r)) [] 0 REFUSE_NONE)
  as [[cells keys] rf].
cbn. split; [reflexivity | right; reflexivity].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.

(* ======================================= the segment's geometry ======================================= *)
Lemma he_seg : forall (cx : hs_scx rsegs) sh, hs_pre rsegs B cx sh ->
In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)) /\ In (4, x_pos rsegs cx) (x_own rsegs cx) /\
e_F (x_e rsegs cx) = frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) /\
e_F (x_e rsegs cx) mod 32 = 0 /\ 4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
in_app (e_F (x_e rsegs cx)) 1024 /\
(forall a, e_F (x_e rsegs cx) <= a < e_F (x_e rsegs cx) + 1024 -> ~ in_img rsegs a) /\
alloc_ceiling + T_SEG_STK <= e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) <= 2 ^ 47 /\
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx) /\
0 <= e_cap (x_e rsegs cx) <= 9 /\ 0 <= e_null (x_e rsegs cx) <= 1.
Proof.
intros cx sh HP.
pose proof HP as HP'. apply hc_core_of_seg_pre_A in HP'. apply hc_core_R in HP' as (HR1 & HR2 & HR3).
pose proof HP as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & Hcap & Hnull & _).
cbn [hi_cid headamp_himg_A] in Hown, HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H32 & Happ & _ & _).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin) as (H4096 & Hceil). cbn [fst snd] in H4096, Hceil.
change (fs_frame_bytes 4) with 1024 in Happ, Hceil.
rewrite <- HF in H32, Happ, H4096, Hceil.
split; [exact Hin|]. split; [exact Hown|]. split; [exact HF|]. split; [exact H32|]. split; [exact H4096|].
split; [exact Hceil|]. split; [exact Happ|].
split.
{ intros a Ha. refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR _)).
  right. left. exists 4, (x_pos rsegs cx). split; [exact Hin|]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. exact Ha. }
split; [exact HR1|]. split; [exact HR2|]. split; [exact HR3|]. split; [exact Hcap | exact Hnull].
Qed.

(* a block live at the segment's start: below the ceiling, in application memory, apart from F *)
Lemma he_blk : forall (cx : hs_scx rsegs) sh p n, hs_pre rsegs B cx sh ->
In (p, n) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(p + req_size n <= e_F (x_e rsegs cx) \/ e_F (x_e rsegs cx) + 1024 <= p).
Proof.
intros cx sh p n HP Hin.
destruct (he_seg cx sh HP) as (Hfin & _ & HF & _).
pose proof HP as (HJ & _).
pose proof HJ as (HAR & _).
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (Hpw & _).
pose proof (he_pairwise_app zdisjoint _ _ (p, req_size n) (e_F (x_e rsegs cx), 1024) Hpw) as HD.
assert (H1 : In (p, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx))))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (p, n)); exact Hin).
assert (H2 : In (e_F (x_e rsegs cx), 1024)
  (map (fun f => (frame_addr (x_lyc rsegs cx) (fst f) (snd f), fs_frame_bytes (fst f))) (frames (x_Sc rsegs cx)))).
{ rewrite HF. change 1024 with (fs_frame_bytes (fst (4, x_pos rsegs cx))).
  apply (in_map (fun f => (frame_addr (x_lyc rsegs cx) (fst f) (snd f), fs_frame_bytes (fst f))) _ (4, x_pos rsegs cx)).
  exact Hfin. }
specialize (HD H1 H2). unfold zdisjoint in HD. cbn [fst snd] in HD.
split; [exact H4096|]. split; [exact Hceil|]. split; [exact Happ | exact HD].
Qed.

(* ======================================= the frame of facts across a run and a call ======================================= *)
Lemma he_hc_core : forall (cx : hs_scx rsegs) sh E ly2 S2 W2 regs2 mem2 md2,
hs_pre rsegs B cx sh -> hs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)).
Proof.
intros cx sh E ly2 S2 W2 regs2 mem2 md2 HP Hcore.
pose proof HP as (_ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _).
destruct Hcore as (HJ & Hr234 & _).
cbn [hi_rsz headamp_himg_A] in Hrsz.
unfold hc_core. split; [exact HJ|]. split; [exact Hev|].
split; [rewrite <- H2; exact (Hr234 2 (or_introl eq_refl))|].
split; [rewrite <- H3; exact (Hr234 3 (or_intror (or_introl eq_refl)))|].
split; [rewrite <- H4; exact (Hr234 4 (or_intror (or_intror eq_refl)))|].
assert (Hal16 : e_R (x_e rsegs cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 32); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hal]]. }
split; [exact Hal16|]. split; [exact Hwin | lia].
Qed.

(* after a call of one of headamp's own functions (HPgCalls' adapters: the callee's stack is [R - T, R)) *)
Lemma he_core_call : forall (cx : hs_scx rsegs) sh E T ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hs_pre rsegs B cx sh -> hs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 -> 0 <= T <= T_SEG_STK ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly3 S3 W3 mem3 md3 regs3 (e_R (x_e rsegs cx)) ->
aregs_preserved regs2 regs3 -> frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T <= y < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 y = aview rsegs (w_H W2) mem2 y) ->
hs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx sh E T ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HP Hcore HT HC3 Hpres Hfr Hperm Hio Hmo Hkeep.
destruct (he_seg cx sh HP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _).
destruct Hcore as (HJ & Hr234 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hmem2).
destruct HC3 as (HJ3 & _).
split; [exact HJ3|].
split; [intros r0 Hr0; rewrite <- (Hr234 r0 Hr0); apply Hpres; unfold acallee_saved; lia|].
split; [rewrite Hfr; exact Hfr2|].
split; [exact (Permutation_trans Hperm Hperm2)|].
split; [exact (same_io_trans _ _ _ Hio2 Hio)|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo2 Hmo)|].
intros a Ha Hs He. rewrite Hsp in Hs.
rewrite (Hkeep a Ha ltac:(unfold T_SEG_STK, ASTACK in *; lia)). exact (Hmem2 a Ha ltac:(rewrite Hsp; exact Hs) He).
Qed.

(* after a block of straight-line code whose post has HPgSteps.hd_blk_postE's clauses, writing only inside E *)
Lemma he_core_blk : forall (cx : hs_scx rsegs) E (Wr : Z -> Prop) (clob : list (bv 5))
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs3 r = getr regs2 r) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> ~ In (Z_to_bv 5 r) clob) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Wr a -> E a) ->
hs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx E Wr clob ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hkr Hcl Hfr Hperm Hio Hmo Hkeep HWE.
destruct Hcore as (HJ & Hr234 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hmem2).
split; [exact HJ3|].
split.
{ intros r0 Hr0. rewrite <- (Hr234 r0 Hr0). apply Hkr; [|exact (Hcl r0 Hr0)].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  destruct Hr0 as [ -> | [ -> | -> ] ]; vm_compute; discriminate. }
split; [rewrite Hfr; exact Hfr2|].
split; [exact (Permutation_trans Hperm Hperm2)|].
split; [exact (same_io_trans _ _ _ Hio2 Hio)|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo2 Hmo)|].
intros a Ha Hs He. rewrite (Hkeep a Ha (fun HW => He (HWE a HW))). exact (Hmem2 a Ha Hs He).
Qed.

(* ======================================= what a cut carries, across writes to x ======================================= *)
(* the bytes the two pieces and the callees they call may write: the callees' stack, x, and x's shadow granules *)
Definition he_wz (cx : hs_scx rsegs) (a : Z) : Prop :=
(e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) \/
(e_F (x_e rsegs cx) + HQ_XO <= a < e_F (x_e rsegs cx) + HQ_XO + 136) \/
(shadow_addr (e_F (x_e rsegs cx)) + 52 <= a < shadow_addr (e_F (x_e rsegs cx)) + 69).

(* the shadow of an address below the ceiling lies in [kLowMemEnd, kHighMemBeg) *)
Lemma he_shadow_band : forall x, 0 <= x < kHighMemEnd ->
kLowMemEnd <= shadow_addr x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_addr. pose proof (hm_shadow_band x Hx) as H. unfold shadow_of_addr in H. exact H.
Qed.

(* F's shadow bytes lie in the shadow band, far below kHighMemBeg *)
Lemma he_fsh_rng : forall (cx : hs_scx rsegs) sh, hs_pre rsegs B cx sh ->
0x7fff8000 <= shadow_addr (e_F (x_e rsegs cx)) /\ shadow_addr (e_F (x_e rsegs cx)) + 128 <= 0x10007fef8080.
Proof.
intros cx sh HP.
destruct (he_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
assert (Hd1 : 0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
assert (Hd2 : e_F (x_e rsegs cx) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
assert (Hd3 : 0x7fffff800000 / 8 = 0xffffff00000) by reflexivity. rewrite Hd3 in Hd2.
unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* a range in application memory below the ceiling and apart from F avoids he_wz *)
Lemma he_wz_app : forall (cx : hs_scx rsegs) sh p n a, hs_pre rsegs B cx sh ->
in_app p n -> p + n <= alloc_ceiling -> (p + n <= e_F (x_e rsegs cx) \/ e_F (x_e rsegs cx) + 1024 <= p) ->
p <= a < p + n -> ~ he_wz cx a.
Proof.
intros cx sh p n a HP Happ Hc Hd Ha.
destruct (he_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & HFapp & _ & HR & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
pose proof (he_fsh_rng cx sh HP) as Hb.
unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold he_wz, HQ_XO. unfold T_SEG_STK, ASTACK in *.
intros [H|[H|H]]; lia.
Qed.

(* a byte of the image avoids he_wz *)
Lemma he_wz_img : forall (cx : hs_scx rsegs) sh a, hs_pre rsegs B cx sh -> in_img rsegs a -> ~ he_wz cx a.
Proof.
intros cx sh a HP Hi.
destruct (he_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & _ & HFimg & HR & _).
pose proof (HPgSteps.img_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
pose proof (he_fsh_rng cx sh HP) as Hb.
unfold he_wz, HQ_XO. unfold T_SEG_STK, ASTACK in *.
intros [H|[H|H]]; [lia | exact (HFimg a ltac:(lia) Hi) | lia].
Qed.

(* res, F + 0x180 .. F + 0x18c, avoids he_wz *)
Lemma he_wz_res : forall (cx : hs_scx rsegs) sh a, hs_pre rsegs B cx sh ->
e_F (x_e rsegs cx) + HQ_RES <= a < e_F (x_e rsegs cx) + HQ_RES + 12 -> ~ he_wz cx a.
Proof.
intros cx sh a HP Ha.
destruct (he_seg cx sh HP) as (_ & _ & _ & _ & HF4 & HFc & HFapp & _ & HR & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
pose proof (he_fsh_rng cx sh HP) as Hb.
unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold HQ_RES in Ha. unfold he_wz, HQ_XO. unfold T_SEG_STK, ASTACK in *.
intros [H|[H|H]]; lia.
Qed.

(* a garr8 fact over bytes that avoid he_wz, carried *)
Lemma he_garr8_kept : forall (cx : hs_scx rsegs) (W2 W3 : world rsegs) mem2 mem3 a (l : list byte),
garr8 rsegs (mrestrict (w_H W2) mem2) a (hd_zbytes l) ->
(forall y, 0 <= y < 2 ^ 64 -> ~ he_wz cx y -> aview rsegs (w_H W3) mem3 y = aview rsegs (w_H W2) mem2 y) ->
(forall y, a <= y < a + Z.of_nat (length l) -> 0 <= y < 2 ^ 64 /\ ~ he_wz cx y) ->
garr8 rsegs (mrestrict (w_H W3) mem3) a (hd_zbytes l).
Proof.
intros cx W2 W3 mem2 mem3 a l Hg Hk Hd.
apply (proj1 (hm_bytes_zbytes rsegs (w_H W3) mem3 a l)).
apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs (w_H W2) mem2 a l) Hg)|].
intros y Hy. destruct (Hd y Hy) as [Hr Hn]. exact (Hk y Hr Hn).
Qed.

Lemma he_base3_kept : forall (cx : hs_scx rsegs) (r : Model.pod_rec) ev (fx2 fx3 : YK11.FPState) sh sh'
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ he_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
hs_fsh_at rsegs cx W3 mem3 sh' -> @hq_fxk fx fx3 ->
@hq_base3 fx rc SK rsegs B MT cx fx3 r sh' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx r ev fx2 fx3 sh sh' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hb Hcore3 Hk Hfsh Hfx.
pose proof HS as (HP & _ & Hwf & Hlen & _ & _ & Hpodb & _ & _ & _ & _ & Houtb & _).
pose proof HP as HP0.
pose proof HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _ & _ & _ & _ & _ & _ & _ & _ & Hppb).
destruct Hb as (_ & _ & _ & Hrom & Hpp & Hpod & Hout & Hres & (ev2 & Herr)).
destruct Hppb as (_ & Hppin & _). destruct Hpodb as (_ & Hpodin & _). destruct Houtb as (_ & Houtin & _).
destruct (he_blk cx _ _ _ HP Hppin) as (Hpp4 & Hppc & Hppa & Hppd).
destruct (he_blk cx _ _ _ HP Hpodin) as (Hpod4 & Hpodc & Hpoda & Hpodd).
destruct (he_blk cx _ _ _ HP Houtin) as (Hout4 & Houtc & Houta & Houtd).
destruct (he_seg cx _ HP) as (_ & _ & _ & _ & HF4 & HFc & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
destruct (he_ans_ok cx r Hcap) as (_ & _ & Hlc).
assert (Hreq : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
split; [exact Hcore3|]. split; [exact Hfx|]. split; [exact Hfsh|].
split.
{ apply (hm_rom_kept rsegs W2 W3 mem2 mem3 Hrom).
  intros a (sg & Hin & _ & Hsb).
  assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hin | exact Hsb]).
  pose proof (HPgSteps.img_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
  exact (Hk a ltac:(lia) (he_wz_img cx _ a HP Himg)). }
split.
{ unfold hs_pp_at in *. apply (he_garr8_kept cx W2 W3 mem2 mem3 _ _ Hpp Hk).
  rewrite (Layout.length_pp_bytes r Hwf). intros y Hy.
  assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hppc, Hppa, Hppd.
  split; [lia|]. exact (he_wz_app cx _ _ _ y HP Hppa Hppc Hppd Hy). }
split.
{ apply (he_garr8_kept cx W2 W3 mem2 mem3 _ _ Hpod Hk). rewrite <- Hlen. intros y Hy.
  pose proof (Hreq (e_len (x_e rsegs cx)) ltac:(lia)) as Hq.
  split; [lia|]. exact (he_wz_app cx _ _ _ y HP Hpoda Hpodc Hpodd ltac:(lia)). }
split.
{ apply (he_garr8_kept cx W2 W3 mem2 mem3 _ _ Hout Hk). rewrite length_ha_cells_bytes. intros y Hy.
  pose proof (Hreq (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)) as Hq.
  split; [lia|]. exact (he_wz_app cx _ _ _ y HP Houta Houtc Houtd ltac:(lia)). }
split.
{ apply (he_garr8_kept cx W2 W3 mem2 mem3 _ _ Hres Hk). unfold ans_res_bytes. rewrite length_ha_res_bytes.
  intros y Hy. split; [unfold HQ_RES in *; lia|]. exact (he_wz_res cx _ y HP Hy). }
exists ev2. intros j Hj.
pose proof errno_low as ((He0 & He1) & Heimg & _). unfold kLowMemEnd in He1.
assert (Hj' : 0 <= Z.of_nat j < 4) by (split; [apply Nat2Z.is_nonneg | apply (Nat2Z.inj_lt j 4); exact Hj]).
assert (Hi : in_img rsegs (as_errno B + Z.of_nat j)) by (apply Heimg; lia).
assert (Hb : 0 <= as_errno B + Z.of_nat j < 2 ^ 64) by lia.
rewrite (Hk _ Hb (he_wz_img cx _ _ HP Hi)). exact (Herr j Hj).
Qed.

End d.
End b.
