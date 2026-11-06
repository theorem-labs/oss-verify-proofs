(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: plugin-hostd/fuzz_reply.asan, the cf allocator bridge (new file), part 4: the
   MALLOC, FREE and FREE(NULL) rules of the `_x` journal at top_x's instance, from the cf contracts amalloc_realizes_cf
   and afree_realizes_cf (AMA_x_room_of_cf, AFREE_x_room_of_cf, AFREEN_x_room_of_cf), and the REALLOC rule from the
   realloc contracts at image A (ARE_x_room_of_cf: the room form arealloc_realizes_cf_rp at ROOM_cf_k S RK_realloc,
   the unprimed end rule with the caller's room restated in this tree, and YGcfRealloc.arealloc_null_realizes_cf;
   through the CfRBridgeAjRealloc journal lemmas; the room comes from room_live_cf by room_live_room_k).  The free rules are stated the
   same way (W_journal_x.v afree_cf_rule_c_x / afree_null_cf_rule_c_x: :770-793 / :794-815 at this base, :880-907 /
   :908-933 in the landed text at commit 479fec81839: the count premise right after the RM line, a charge of 1 for a
   block and for NULL) and proved through YGcallx.aj_free_at_x_ct
   and CfRBridgeAjFreeN.aj_free_null_at_x_ct (the free(NULL) twin).  The malloc rule's text:
   The rule is stated here in the ruled text (ROOM-TEXTS.md v3 (sha256 767baa12f13c; internal record)
   sections 0.1-0.3, (a), and (h) for the stack line): W_journal_x.v amalloc_cf_rule_c_x (:749-769) at top_x's instance
   (A/W_LLVMFuzzerTestOneInput_top_x.v:109-110 ARX, PST := [], MMAX := fr_MMAX, CTX := CTX_AMALLOC) with
   - the binder (kr : nat) after ch;
   - the count premise right after the bytes premise (cb_cf: top_x's Psec := rl_sec_req, P24 := in_cls kBatchClass,
     Lsec := 1024, L24 := 2 ^ 15, Pcls := in_cls, LPRIM c := Z.to_nat (RL_PRIM c); acnt: CfRBridgePrim.v);
   - the stack line `ly_bot lyc + ACALL_PREFIX < spZ regsT` right after `ASTACK - o <= STK`, ACALL_PREFIX := 4096
     (commit a3e599d9f79e YG0d.v:21; written as its value until the kit carries the notation);
   - after the CTX premise `RM Sc (1 + kr)` (realloc: `2 + kr`), and after mo_le in the post `RM S2 kr`, over a
     PARAMETER RM with HRM : RM = fun S _ => room_live_cf S (R1); the count premise is ONE premise `CNT (ablocks ..)`
     over a parameter CNT with HCNT : CNT l -> cb_cf l, so at commit 479fec81839 the bridges apply at RM := rp_RM RPi,
     CNT := cnt_ok RPi (W_journal_x.v Record roomp, commit 479fec81839 :626-633, rules :855-964);
   - the meter MT generic (KF-COUNT); its instance is MT_sec (Section TOPK).
   When that text lands in W_journal_x.v, the rule at top_x's instance is this statement by conversion,
   provided top_x's LPRIM is ReplyCnt.LPRIM (Z.to_nat (ReplyCnt.RL_PRIM c); the class bound PresetRoom.room_ok is
   checked against it by rl_prim_room).  The stack line is a premise the proofs do
   not use (it weakens the rule); a call site gets it from the strengthened astk_ok (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (h)).
   The proof: YGcallx.aj_malloc_at_x_ct at ARxs (YGcallcf.v's ARcf /\ xs_placed_cf; top_x's ARX implies it by
   xs_placed_of_ARcf, and the post's ghost list is the call's, []), with QMm_cf from room_live_cf, the hull admission
   and ARX's arodata conjunct (room_live_room, QMm_cf_of_room), the trace from CfRBridgeCtx.cfr_ctx_amalloc, the NULL arm excluded by
   CfRBridgePrim.malloc_cf_granted_not_null (count block -> rl_prim_ok), the tick by CfRBridgeNev.malloc_cf_block_nev,
   the post room by YGcfRoomLive.room_live_call_keep, errno by the leaf's raw clause (the image is never hidden:
   w_Hoff), the image's presence by the leaf's raw frame (image bytes are not owned, not scratch, not the block, not
   an extra extent: the owned-image, layout, client-image and extents laws).
   The call's memory facts (QMm; the frame law's kept bytes, commit 1aba1a15346b; top_x's ARX, commit b27e847023f8):
   top_x's relation ARX carries arodata_ok_cf on the call memory as its LAST conjunct, so each rule projects it from
   ARX at the call into
   QMm_cf, and re-establishes it at the post from the callee leaf's raw frame (arodata_post_keep: the bytes
   arodata_ok_cf reads are not owned, not scratch, not a block and not an errbuf extent; YG0dcf.arodata_keep_cf over
   the unit rows relro_seg_t / errno_relro_t, Section hypotheses HRS / HER).  QMm_cf's hull conjunct cf_hull_ok comes
   from each rule's own count premise mo_ok (MO_OK_HULL_M / _F / _R; at MT_sec, Section TOPK, from MT_ok_hull).  The
   four rules at the trivial meter ameter_triv (the old Section TOP theorems AMA_x_cf / AFREE_x_cf / AFREEN_x_cf /
   ARE_x_cf) are deleted: ameter_triv's mo_ok bounds nothing, so it cannot give the hull admission.
   No function is proved (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YP09 YP03 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfXs YGcallcf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x CfParamsReply AD2l ACk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomKeep YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc ReallocP YG03cf YG03dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt ReplyLSCntL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgeCtx CfRBridgePrim CfRBridgeNev CfRBridgeAjFreeN.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfRBridgeAjRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s YG0scf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* An image address is in a segment. *)
Lemma find_segment_in_img_cfr : forall sgs a, in_img sgs a -> find_segment sgs a 1 <> None.
Proof.
intros sgs a (sg & Hsg & Hr). induction sgs as [|sg0 rest IH]; [destruct Hsg|]. cbn.
destruct (Z.leb (Z.of_N (seg_base sg0)) a && Z.leb (a + 1) (Z.of_N (seg_base sg0) + Z.of_N (seg_size sg0)))%bool eqn:E0;
  [discriminate|].
destruct Hsg as [<-|Hin]; [|exact (IH Hin)].
apply Bool.andb_false_iff in E0 as [E0|E0]; apply Z.leb_gt in E0; lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 0. The read-only data across a call (QMm W1): arodata_ok_cf at the callee's post memory, from the call memory's and *)
(*    the leaf's raw frame.  The bytes it reads are not owned at either state, not scratch, not an errbuf extent        *)
(*    (YG0dcf.arodata_keep_cf, relro_not_scratch_cf), and not in the leaf's other exceptions EX (the caller shows EX     *)
(*    misses the image of both layouts and both errbuf lists).                                                         *)
Section AK. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* A live block lies off the image (YG0scf.client_byte_not_img_cf). *)
Lemma ablock_not_img_cfr : forall B ly S Hp rd pa n a, ARmcf B ly S Hp rd -> In (pa, n) (ablocks B ly S) ->
  in_zr a (ly_img ly) -> ~ (pa <= a < pa + req_size n).
Proof.
intros B ly S Hp rd pa n a M Hin I Hb.
eapply YG0s.In_ablocks in Hin. destruct Hin as (k & Hk & Hst & Hu & Hq). subst pa n.
apply (YG0scf.client_byte_not_img_cf B ly S Hp rd a M); [|exact I].
left. exists k. split; [exact Hk|]. split; [exact Hst|]. unfold ck_n. split; lia.
Qed.

Lemma arodata_post_keep : forall segs (B : asyms) lyc Sc Hpc (W : world segs) (regsT : bvmap 5 word) memT mdc
  ly2 S2 Hp2 (W2 : world segs) mem2 md2 (EX : Z -> Prop),
  relro_seg_t segs -> errno_relro_t B ->
  ARcf segs B lyc Sc Hpc W memT mdc -> ARcf segs B ly2 S2 Hp2 W2 mem2 md2 ->
  ly_stk_lo lyc + ASTACK <= spZ regsT ->
  (forall a, in_zr a (ly_img lyc) -> in_zr a (ly_img ly2) -> ~ Exists (in_zr a) (xs_cf lyc Sc) ->
     ~ Exists (in_zr a) (xs_cf ly2 S2) -> ~ EX a) ->
  (forall x : word, ~ (aowned B lyc Sc (bv_unsigned x) \/ aowned B ly2 S2 (bv_unsigned x) \/
     ascratch B ASTACK regsT (bv_unsigned x) \/ EX (bv_unsigned x)) -> mem2 x = memT x) ->
  arodata_ok_cf segs B memT -> arodata_ok_cf segs B mem2.
Proof.
intros segs B lyc Sc Hpc W regsT memT mdc ly2 S2 Hp2 W2 mem2 md2 EX RS ER A1 A2 STK HEX RAW.
apply (arodata_keep_cf segs B lyc Sc Hpc W memT mdc ly2 S2 Hp2 W2 mem2 md2
  (fun a => aowned B lyc Sc a \/ aowned B ly2 S2 a \/ ascratch B ASTACK regsT a \/ EX a) A1 A2 RS); [|exact RAW].
intros a Hr Hns Hk Hi1 Hi2 Ho1 Ho2 Hx1 Hx2 [H|[H|[H|H]]].
- exact (Ho1 H).
- exact (Ho2 H).
- exact (relro_not_scratch_cf B lyc ASTACK regsT a (amc_layout _ _ _ _ _ (proj1 A1)) STK ER Hr Hk H).
- exact (HEX a Hi1 Hi2 Hx1 Hx2 H).
Qed.
End AK.

Section B. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {ci : CfImg}.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.

(* The count block of the cf instance (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.3 at top_x's fields): what the rules' count premise
   gives at RP's field values (cnt_ok RPi l is this, by conversion, when RPi carries top_x's fields). *)
Definition cb_cf (l : list (Z * Z)) : Prop :=
  (acnt rl_sec_req l <= 1024)%nat /\ (acnt (PresetRoom.in_cls kBatchClass) l <= 2 ^ 15)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (PresetRoom.in_cls c) l <= Z.to_nat (RL_PRIM c))%nat).
(* The room record's two fields the rules read (W_journal_x.v Record roomp at commit 479fec81839: rp_RM, and the count
   premise cnt_ok RP), as parameters: there the bridges apply at RM := rp_RM RPi and CNT := cnt_ok RPi.  R1 (the
   ruled placement): RM is room_live_cf with the budget ignored.  The count premise gives the cf count block. *)
Variable RM : astate -> nat -> Prop.
Variable CNT : list (Z * Z) -> Prop.
Hypothesis HRM : RM = fun S _ => room_live_cf S.
Hypothesis HCNT : forall l, CNT l -> cb_cf l.
(* The meter (KF-COUNT, step 1, row 3): MT is generic; the rules' mo_le post follows from the cf model's
   count of granted secondary entries nsec_cf (YGcfNsec.v, stated here as Section hypotheses with its
   exact names and texts) through three arithmetic facts of MT (MO_LE_M / MO_LE_F / MO_LE_R).  At MT_sec they
   follow from its defining equations (Section TOPK). *)
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
Hypothesis MO_LE_M : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n).
Hypothesis MO_LE_F : forall s s', nsec_cf s' <= nsec_cf s -> mo_le MT s s' (mo_free MT).
Hypothesis MO_LE_R : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n + mo_free MT).
(* The hull admission at the call (QMm_cf's cf_hull_ok), from the rule's own count premise: at a meter whose mo_ok bounds
   the count (MT_sec: nsec_cf s + m <= cf_kmax) with a nonnegative charge (Section TOPK derives both). *)
Hypothesis MO_OK_HULL_M : forall s n, 0 <= n -> mo_ok MT s (mo_malloc MT n) -> cf_hull_ok s.
Hypothesis MO_OK_HULL_F : forall s, mo_ok MT s (mo_free MT) -> cf_hull_ok s.
(* The unit's two image rows the read-only data keep reads (YG0ncf.v): the read-only data lie in a segment, and errno's
   cell is apart from them. *)
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.

(* top_x's relation (W_LLVMFuzzerTestOneInput_top_x.v:173-174 after W1: its last conjunct is arodata_ok_cf on the
   memory) and YGcallcf's (:218). *)
Local Abbreviation ARX := (fun ly S Hp (W : world segs) mem md =>
  ARcf segs TfibB ly S Hp W mem md /\ Hp = [] /\ arodata_ok_cf segs TfibB mem).
Local Abbreviation ARxs := (fun ly S Hp (W : world segs) mem md => ARcf segs TfibB ly S Hp W mem md /\ xs_placed_cf ly S).

(* ---------------------------------------------------------------------------- *)
(* 1. The image is never hidden; its bytes are read from memory.                   *)
Lemma img_visible : forall (W : world segs) a, in_img segs a -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Hi. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity].
pose proof (segs_low a Hi) as Ha. pose proof (w_Hoff W _ E) as F.
rewrite unsigned_lit_small in F by (unfold kLowMemEnd in Ha; lia).
exfalso. exact (find_segment_in_img_cfr segs a Hi F).
Qed.

Lemma aview_img_eq : forall (W W' : world segs) mem mem' a, in_img segs a ->
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
intros W W' mem mem' a Hi Hm. unfold aview, mbyte, mrestrict.
rewrite (img_visible W a Hi), (img_visible W' a Hi), Hm. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The journal at top_x's relation and at ARxs.                                 *)
Lemma aj_to_xs : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_x segs TfibB [] ARxs STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ. eapply ajournal_x_impl; [|exact HJ].
intros [H _]. exact (conj H (xs_placed_of_ARcf segs TfibB ly' S' Hp' W' mem' md' H)).
Qed.

Lemma aj_of_xs : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k, Hp' = [] ->
  arodata_ok_cf segs TfibB mem' ->
  ajournal_x segs TfibB [] ARxs STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k E AD HJ. eapply ajournal_x_impl; [|exact HJ].
intros [H _]. exact (conj H (conj E AD)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The malloc rule, in the ruled text at top_x's instance.                      *)
Definition AMA_x_room : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch (kr : nat),
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 n -> 0 <= n < fr_MMAX -> blocks_bytes Sc + n <= LIVE_MAX ->
CNT (ablocks TfibB lyc Sc) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + 4096 < spZ regsT ->
getr regsT 3 = w64 (as_gp TfibB) -> getr regsT 4 = w64 (as_tp TfibB) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AMALLOC ->
RM Sc (1 + kr) ->
mo_ok MT Sc (mo_malloc MT n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code TfibB))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks TfibB ly2 S2 = ablocks TfibB lyc Sc ++ [(res, n)] /\
acall_kept segs TfibB lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
mo_le MT Sc S2 (mo_malloc MT n) /\
RM S2 kr /\
(forall i, 0 <= i < 4 -> aview segs (w_H W2) mem2 (as_errno TfibB + i) = aview segs (w_H W) memT (as_errno TfibB + i)) /\
(forall a, in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ aowned TfibB ly2 S2 a ->
 ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
 ~ (res <= a < res + req_size n) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).

Theorem AMA_x_room_of_cf : amalloc_realizes_cf segs TfibB -> AMA_x_room.
Proof.
intros AM W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch kr
  HJ Ha0 Hn Hlive HCB Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch HCTX HRL HMO.
destruct (HCNT _ HCB) as (Hc1 & Hc2 & Hc3). rewrite HRM in HRL. cbv beta in HRL.
pose proof HJ as ([HARc [HHp HAD]] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
pose proof (proj1 (count_block_iff_cfr TfibB lyc Sc) (conj Hc1 (conj Hc2 Hc3))) as (HSEC & H24 & HB24 & HPRIM).
pose proof (room_live_room Sc HRL) as HROOM.
(* the call's QMm_cf: the room, the hull admission from the count premise, ARX's arodata *)
pose proof (MO_OK_HULL_M Sc n (proj1 Hn) HMO) as HHULL.
pose proof (QMm_cf_of_room segs TfibB lyc Sc Hpc W memT mdc HARc HQT HROOM HHULL HAD) as HQM.
pose proof (universe_ok_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc) as HU.
pose proof (amc_wf _ _ _ _ _ (proj1 HARc)) as HWF.
pose proof (cfr_ctx_amalloc lyc regsT ch Sc HCTX) as Htr. unfold cf_trace_ok, cf_tr_ok in Htr.
pose proof (aj_to_xs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJx.
assert (Hn' : 0 <= n < cf_malloc_max) by exact Hn.
assert (LAWSx : AR_laws_x segs TfibB ARxs cf_head) by exact (AR_laws_x_xs segs TfibB L).
assert (AMX : alloc_model_laws_x TfibB QM_cf malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe TfibB)))
  by exact (alloc_model_laws_x_cf TfibB HU).
assert (AMx : amalloc_realizes_x segs TfibB ARxs (QMm_cf segs TfibB) malloc_cf cf_malloc_max xs_cf)
  by exact (amalloc_realizes_x_xs segs TfibB AM).
pose proof (amx_malloc _ _ _ _ _ _ AMX Sc n _ HWF (QMQ_cf segs TfibB Sc memT HQM) Hn' Hlive (admits_fix _ _ Sc HU Htr))
  as (_ & _ & _ & HMP).
pose proof (aj_malloc_at_x_ct segs TfibB [] ARxs QM_cf (QMm_cf segs TfibB) malloc_cf cf_malloc_max free_cf
  (Wf_cf (as_universe TfibB)) xs_cf
  LAWSx segs_low errno_low (ARx_owned_low_law_xs segs TfibB L) (ARx_wf_law_xs segs TfibB) AMX (QMQ_cf segs TfibB)
  (ARx_xs_law_xs segs TfibB) HU AMx
  W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch HJx Ha0 Hn' Hlive Hsp Hal Hneg Hbud
  Hgp Htp Hra Hraw HQM Hch Htr) as HSR.
assert (HARxs : ARxs lyc Sc Hpc W memT mdc) by exact (conj HARc (xs_placed_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc)).
eapply SRr_mono; [exact HSR|].
intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2' & HJ2 & Hpres & Hres & Hfrs & HPRE & Htr2 &
  (p & trc & Hpath & Hgf & Hleaf & Hiff & Hres2) & Harms).
assert (Hpn : p <> PNull)
  by exact (malloc_cf_granted_not_null (as_universe TfibB) Sc n _ trc (p, S2) HWF HQT HPRIM Hpath Hgf).
destruct Harms as [(Hr0 & _) | (H4096 & Eab & Hkept)].
{ exfalso. apply Hpn. apply Hiff. exact Hr0. }
pose proof (malloc_cf_block_nev n _ Sc trc p S2 Hpath Hpn) as Hnev.
assert (Hin2 : In (p, n) (blocks S2)).
{ pose proof (HMP trc (p, S2) Hpath) as HMP2. unfold malloc_post_x in HMP2. destruct HMP2 as (_ & _ & _ & Hbl).
  destruct p as [|o1|r1 o1|c1 o1]; [exfalso; exact (Hpn eq_refl)| | |];
  rewrite Hbl; apply in_or_app; right; left; reflexivity. }
destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & HPOST & Hreg' & HQT2 & HNULL & HERR & HRAW).
cbn [fst snd] in HRAW.
assert (Emem : mem2 = mem') by (rewrite Hc2' in Hc'; unfold cfg_at in Hc'; injection Hc'; intros; congruence).
destruct HPOST as (HARxs2 & Hly' & Hwle' & Hpres' & Hio' & Hfr' & Hpres2').
pose proof HPRE as (_ & _ & _ & HSLO & _).
(* the post's arodata (ARX's last conjunct at the post), from the leaf's raw frame *)
assert (HAD2 : arodata_ok_cf segs TfibB mem2).
{ rewrite Emem.
  apply (arodata_post_keep segs TfibB lyc Sc Hpc W regsT memT mdc ly' S2 Hpc W2 mem' md'
    (fun a => (p <> PNull /\ sptr_addr TfibB ly' p <= a < sptr_addr TfibB ly' p + req_size n) \/
       Exists (in_zr a) (xs_cf lyc Sc ++ xs_cf ly' S2)) HRS HER HARc (proj1 HARxs2) HSLO); [| |exact HAD].
  - intros a I1 I2 X1 X2 [[_ Hb] | Hx].
    + exact (ablock_not_img_cfr TfibB ly' S2 Hpc _ (sptr_addr TfibB ly' p) n a (proj1 (proj1 HARxs2))
        (in_map (fun b0 => (sptr_addr TfibB ly' (fst b0), snd b0)) _ (p, n) Hin2) I2 Hb).
    + apply Exists_app in Hx as [Hx|Hx]; [exact (X1 Hx) | exact (X2 Hx)].
  - intros x NX. apply HRAW; intros H; apply NX; tauto. }
exists ly2, S2, Hpc, regs2, mem2, md2, res.
split; [exact Hc2'|].
split.
{ apply aj_of_xs; [exact HHp | exact HAD2 |]. replace (k + 1) with (k + (st_nev S2 - st_nev Sc)) by lia. exact HJ2. }
split; [exact Hpres|]. split; [exact Hres|]. split; [exact Hfrs|]. split; [exact H4096|]. split; [exact Eab|].
split; [exact Hkept|].
split; [exact (MO_LE_M Sc S2 n (proj1 Hn) (cfx_ipost_apath _ _ trc (p, S2) (nsec_malloc_cf n _ Sc) Hpath))|].
split.
{ rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
    (or_introl (ex_intro _ n (ex_intro _ _ (ex_intro _ trc (ex_intro _ p Hpath)))))). }
split.
{ intros i Hi. rewrite Emem. apply aview_img_eq.
  - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
  - exact (HERR Hpn i Hi). }
intros a Hi Ho1 Ho2 He Hb [Hh (b & Hm)].
pose proof (segs_low a Hi) as Ha.
split; [exact (img_visible W2 a Hi)|]. exists b. rewrite Emem. rewrite <- Hm.
assert (Eua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; unfold kLowMemEnd in Ha; lia).
apply HRAW; rewrite Eua.
- exact Ho1.
- intros Ho. apply Ho1.
  apply (proj2 (alx_owned_image _ _ _ LAWSx lyc Sc Hpc W memT mdc a HARxs Hi)).
  exact (proj1 (alx_owned_image _ _ _ LAWSx ly' S2 Hpc W2 mem' md' a HARxs2 Hi) Ho).
- intros [Hs | He']; [|exact (He He')].
  pose proof (lo_top _ (alx_layout_ok _ _ _ LAWSx lyc Sc Hpc W memT mdc HARxs)) as (_ & _ & _ & _ & _ & _ & Hbeg).
  destruct HPRE as (_ & _ & _ & Hslo & _).
  unfold kHighMemBeg, kLowMemEnd, ASTACK in *. lia.
- intros [[_ Hblk] | Hx].
  + assert (Hinab : In (sptr_addr TfibB ly' p, n) (ablocks TfibB ly' S2))
      by exact (in_map (fun b0 => (sptr_addr TfibB ly' (fst b0), snd b0)) _ (p, n) Hin2).
    destruct (alx_client_img _ _ _ LAWSx ly' S2 Hpc W2 mem' md' a HARxs2
      (or_introl (ex_intro _ _ (ex_intro _ n (conj Hinab Hblk))))) as (_ & Hni).
    exact (Hni Hi).
  + apply Exists_app in Hx as [Hx|Hx].
    * destruct (ARx_xs_law_xs segs TfibB lyc Sc Hpc W memT mdc a HARxs Hx) as (_ & _ & Hni & _). exact (Hni Hi).
    * destruct (ARx_xs_law_xs segs TfibB ly' S2 Hpc W2 mem' md' a HARxs2 Hx) as (_ & _ & Hni & _). exact (Hni Hi).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The free rule (a live block), in the ruled text at top_x's instance.         *)
Definition AFREE_x_room : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch (kr : nat),
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, n) (ablocks TfibB lyc Sc) ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + 4096 < spZ regsT ->
getr regsT 3 = w64 (as_gp TfibB) -> getr regsT 4 = w64 (as_tp TfibB) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
RM Sc (1 + kr) ->
CNT (ablocks TfibB lyc Sc) ->
(In (pa, n) (ablocks TfibB ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code TfibB))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks TfibB lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks TfibB ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_kept segs TfibB lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n) /\
mo_le MT Sc S2 (mo_free MT) /\
RM S2 kr /\
(forall i, 0 <= i < 4 -> aview segs (w_H W2) mem2 (as_errno TfibB + i) = aview segs (w_H W) memT (as_errno TfibB + i)) /\
(forall a, in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ aowned TfibB ly2 S2 a ->
 ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
 ~ (pa <= a < pa + req_size n) -> apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).

Theorem AFREE_x_room_of_cf : afree_realizes_cf segs TfibB -> AFREE_x_room.
Proof.
intros AF W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch kr
  HJ Hin Ha0 Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch HCTX HRL HCB HFP HMO.
destruct (HCNT _ HCB) as (Hc1 & Hc2 & Hc3). rewrite HRM in HRL. cbv beta in HRL.
pose proof HJ as ([HARc [HHp HAD]] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
pose proof (proj1 (count_block_iff_cfr TfibB lyc Sc) (conj Hc1 (conj Hc2 Hc3))) as (HSEC & H24 & HB24 & _).
pose proof (room_live_room Sc HRL) as HROOM.
pose proof (MO_OK_HULL_F Sc HMO) as HHULL.
pose proof (QMm_cf_of_room segs TfibB lyc Sc Hpc W memT mdc HARc HQT HROOM HHULL HAD) as HQM.
pose proof (universe_ok_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc) as HU.
pose proof (amc_wf _ _ _ _ _ (proj1 HARc)) as HWF.
pose proof (cfr_ctx_afree lyc regsT ch Sc HCTX) as Htr. unfold cf_trace_ok, cf_tr_ok in Htr.
pose proof (aj_to_xs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJx.
assert (Hnhp : ~ In pa Hpc) by (rewrite HHp; intros []).
assert (LAWSx : AR_laws_x segs TfibB ARxs cf_head) by exact (AR_laws_x_xs segs TfibB L).
assert (AMX : alloc_model_laws_x TfibB QM_cf malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe TfibB)))
  by exact (alloc_model_laws_x_cf TfibB HU).
assert (AFx : afree_realizes_x segs TfibB ARxs (QMm_cf segs TfibB) free_cf) by exact (afree_realizes_x_xs segs TfibB AF).
pose proof (aj_free_at_x_ct segs TfibB [] ARxs QM_cf (QMm_cf segs TfibB) malloc_cf cf_malloc_max free_cf
  (Wf_cf (as_universe TfibB))
  LAWSx segs_low errno_low (ARx_owned_low_law_xs segs TfibB L) (ARx_wf_law_xs segs TfibB) AMX (QMQ_cf segs TfibB) HU AFx
  W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch HJx Hin Hnhp Ha0 Hsp Hal Hneg Hbud
  Hgp Htp Hra Hraw HQM Hch Htr HFP) as HSR.
assert (HARxs : ARxs lyc Sc Hpc W memT mdc) by exact (conj HARc (xs_placed_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc)).
eapply SRr_mono; [exact HSR|].
intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & Hc2' & HJ2 & Hpres & Hsplit & Hfrs & HPRE & Htr2 &
  (q & trc & Hq & Hqin & Hpath & Hgf & Hleaf) & Hkept).
pose proof (free_cf_nev q _ Sc trc S2 Hpath) as Hnev.
destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & HPOST & HQT2 & HERR & HRAW).
cbn [fst snd] in HRAW.
assert (Emem : mem2 = mem') by (rewrite Hc2' in Hc'; unfold cfg_at in Hc'; injection Hc'; intros; congruence).
destruct HPOST as (HARxs2 & Hly' & Hwle' & Hpres' & Hio' & Hfr' & Hpres2').
pose proof HPRE as (_ & _ & _ & HSLO & _).
(* the post's arodata, from the leaf's raw frame: the freed block is a live block of the call state, off the image *)
assert (HAD2 : arodata_ok_cf segs TfibB mem2).
{ rewrite Emem.
  apply (arodata_post_keep segs TfibB lyc Sc Hpc W regsT memT mdc ly' S2 Hpc W2 mem' md'
    (fun a => q <> PNull /\ sptr_addr TfibB lyc q <= a < sptr_addr TfibB lyc q + req_size n)
    HRS HER HARc (proj1 HARxs2) HSLO); [| |exact HAD].
  - intros a I1 I2 X1 X2 [_ Hb]. rewrite Hq in Hb.
    exact (ablock_not_img_cfr TfibB lyc Sc Hpc _ pa n a (proj1 HARc) Hin I1 Hb).
  - intros x NX. apply HRAW; intros H; apply NX; tauto. }
exists ly2, S2, Hpc, regs2, mem2, md2.
split; [exact Hc2'|].
split.
{ apply aj_of_xs; [exact HHp | exact HAD2 |]. replace (k + 1) with (k + (st_nev S2 - st_nev Sc)) by lia. exact HJ2. }
split; [exact Hpres|]. split; [exact Hsplit|]. split; [exact Hfrs|].
split; [exact Hkept|].
split; [exact (MO_LE_F Sc S2 (cfx_ipost_apath _ _ trc (tt, S2) (nsec_free_cf q _ Sc) Hpath))|].
split.
{ rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
    (or_intror (or_introl (ex_intro _ q (ex_intro _ _ (ex_intro _ trc Hpath)))))). }
split.
{ intros i Hi. rewrite Emem. apply aview_img_eq.
  - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
  - exact (HERR i Hi). }
intros a Hi Ho1 Ho2 He Hb [Hh (b & Hm)].
pose proof (segs_low a Hi) as Ha.
split; [exact (img_visible W2 a Hi)|]. exists b. rewrite Emem. rewrite <- Hm.
assert (Eua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; unfold kLowMemEnd in Ha; lia).
apply HRAW; rewrite Eua.
- exact Ho1.
- intros Ho. apply Ho1.
  apply (proj2 (alx_owned_image _ _ _ LAWSx lyc Sc Hpc W memT mdc a HARxs Hi)).
  exact (proj1 (alx_owned_image _ _ _ LAWSx ly' S2 Hpc W2 mem' md' a HARxs2 Hi) Ho).
- intros [Hs | He']; [|exact (He He')].
  pose proof (lo_top _ (alx_layout_ok _ _ _ LAWSx lyc Sc Hpc W memT mdc HARxs)) as (_ & _ & _ & _ & _ & _ & Hbeg).
  destruct HPRE as (_ & _ & _ & Hslo & _).
  unfold kHighMemBeg, kLowMemEnd, ASTACK in *. lia.
- intros [_ Hblk]. apply Hb. rewrite <- Hq. exact Hblk.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The free(NULL) rule, in the ruled text at top_x's instance (RM Sc (1 + kr): a charge of 1).                   *)
Definition AFREEN_x_room : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw ch (kr : nat),
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 0 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + 4096 < spZ regsT ->
getr regsT 3 = w64 (as_gp TfibB) -> getr regsT 4 = w64 (as_tp TfibB) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
RM Sc (1 + kr) ->
CNT (ablocks TfibB lyc Sc) ->
mo_ok MT Sc (mo_free MT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code TfibB))) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks TfibB ly2 S2) (ablocks TfibB lyc Sc) /\
frames S2 = frames Sc /\
acall_kept segs TfibB lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
mo_le MT Sc S2 (mo_free MT) /\
RM S2 kr /\
(forall i, 0 <= i < 4 -> aview segs (w_H W2) mem2 (as_errno TfibB + i) = aview segs (w_H W) memT (as_errno TfibB + i)) /\
(forall a, in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ aowned TfibB ly2 S2 a ->
 ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
 apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).

Theorem AFREEN_x_room_of_cf : afree_realizes_cf segs TfibB -> AFREEN_x_room.
Proof.
intros AF W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch kr
  HJ Ha0 Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch HCTX HRL HCB HMO.
destruct (HCNT _ HCB) as (Hc1 & Hc2 & Hc3). rewrite HRM in HRL. cbv beta in HRL.
pose proof HJ as ([HARc [HHp HAD]] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
pose proof (proj1 (count_block_iff_cfr TfibB lyc Sc) (conj Hc1 (conj Hc2 Hc3))) as (HSEC & H24 & HB24 & _).
pose proof (room_live_room Sc HRL) as HROOM.
pose proof (MO_OK_HULL_F Sc HMO) as HHULL.
pose proof (QMm_cf_of_room segs TfibB lyc Sc Hpc W memT mdc HARc HQT HROOM HHULL HAD) as HQM.
pose proof (universe_ok_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc) as HU.
pose proof (amc_wf _ _ _ _ _ (proj1 HARc)) as HWF.
pose proof (cfr_ctx_afree lyc regsT ch Sc HCTX) as Htr. unfold cf_trace_ok, cf_tr_ok in Htr.
pose proof (aj_to_xs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJx.
assert (LAWSx : AR_laws_x segs TfibB ARxs cf_head) by exact (AR_laws_x_xs segs TfibB L).
pose proof (aj_free_null_at_x_ct segs TfibB [] L segs_low errno_low HU AF
  W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw ch HJx Ha0 Hsp Hal Hneg Hbud
  Hgp Htp Hra Hraw HQM Hch Htr) as HSR.
assert (HARxs : ARxs lyc Sc Hpc W memT mdc) by exact (conj HARc (xs_placed_of_ARcf segs TfibB lyc Sc Hpc W memT mdc HARc)).
eapply SRr_mono; [exact HSR|].
intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & Hc2' & HJ2 & Hpres & Hperm & Hfrs & HPRE &
  (trc & Hpath & Hgf & Hleaf) & Hkept).
pose proof (free_cf_nev PNull _ Sc trc S2 Hpath) as Hnev.
destruct Hleaf as (ly' & regs' & mem' & md' & Hc' & HPOST & HQT2 & HERR & HRAW).
cbn [fst snd] in HRAW.
assert (Emem : mem2 = mem') by (rewrite Hc2' in Hc'; unfold cfg_at in Hc'; injection Hc'; intros; congruence).
destruct HPOST as (HARxs2 & Hly' & Hwle' & Hpres' & Hio' & Hfr' & Hpres2').
pose proof HPRE as (_ & _ & _ & HSLO & _).
(* the post's arodata, from the leaf's raw frame: free(NULL) has no block exception *)
assert (HAD2 : arodata_ok_cf segs TfibB mem2).
{ rewrite Emem.
  apply (arodata_post_keep segs TfibB lyc Sc Hpc W regsT memT mdc ly' S2 Hpc W2 mem' md'
    (fun a => PNull <> PNull /\ sptr_addr TfibB lyc PNull <= a < sptr_addr TfibB lyc PNull + req_size 0)
    HRS HER HARc (proj1 HARxs2) HSLO); [| |exact HAD].
  - intros a I1 I2 X1 X2 [Hc _]. exact (Hc eq_refl).
  - intros x NX. apply HRAW; intros H; apply NX; tauto. }
exists ly2, S2, Hpc, regs2, mem2, md2.
split; [exact Hc2'|].
split.
{ apply aj_of_xs; [exact HHp | exact HAD2 |]. replace (k + 1) with (k + (st_nev S2 - st_nev Sc)) by lia. exact HJ2. }
split; [exact Hpres|]. split; [exact Hperm|]. split; [exact Hfrs|].
split; [exact Hkept|].
split; [exact (MO_LE_F Sc S2 (cfx_ipost_apath _ _ trc (tt, S2) (nsec_free_cf PNull _ Sc) Hpath))|].
split.
{ rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
    (or_intror (or_introl (ex_intro _ PNull (ex_intro _ _ (ex_intro _ trc Hpath)))))). }
split.
{ intros i Hi. rewrite Emem. apply aview_img_eq.
  - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
  - exact (HERR i Hi). }
intros a Hi Ho1 Ho2 He [Hh (b & Hm)].
pose proof (segs_low a Hi) as Ha.
split; [exact (img_visible W2 a Hi)|]. exists b. rewrite Emem. rewrite <- Hm.
assert (Eua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; unfold kLowMemEnd in Ha; lia).
apply HRAW; rewrite Eua.
- exact Ho1.
- intros Ho. apply Ho1.
  apply (proj2 (alx_owned_image _ _ _ LAWSx lyc Sc Hpc W memT mdc a HARxs Hi)).
  exact (proj1 (alx_owned_image _ _ _ LAWSx ly' S2 Hpc W2 mem' md' a HARxs2 Hi) Ho).
- intros [Hs | He']; [|exact (He He')].
  pose proof (lo_top _ (alx_layout_ok _ _ _ LAWSx lyc Sc Hpc W memT mdc HARxs)) as (_ & _ & _ & _ & _ & _ & Hbeg).
  destruct HPRE as (_ & _ & _ & Hslo & _).
  unfold kHighMemBeg, kLowMemEnd, ASTACK in *. lia.
- intros [Hc _]. exact (Hc eq_refl).
Qed.



End B.

(* ---------------------------------------------------------------------------- *)
(* 6. Generic journal / call facts used by the realloc rule.                      *)
Lemma aj_k_le : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} segs B PST
  (R : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k', k <= k' ->
  ajournal_x segs B PST R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_x segs B PST R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k'.
Proof.
intros fx rc SK segs B PST R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k k' Hk HJ.
unfold ajournal_x in *. destruct HJ as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
split; [exact A6|]. split; [lia|]. split; [lia|]. exact A9.
Qed.

Lemma kept_mono : forall {fx : YK11.FPState} {rc : YM05.RunCeil} segs B lyc Sc (W : world segs) memc W2 mem2 slo shi
  (E E' : Z -> Prop), (forall a, E a -> E' a) ->
  acall_kept segs B lyc Sc W memc W2 mem2 slo shi E -> acall_kept segs B lyc Sc W memc W2 mem2 slo shi E'.
Proof.
intros fx rc segs B lyc Sc W memc W2 mem2 slo shi E E' HE (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split; [intros b m i Hb Hi Hn; exact (K2 b m i Hb Hi (fun H => Hn (HE _ H)))|].
split; [exact K3|]. split; [intros cid pos a Hf Hr Hn; exact (K4 cid pos a Hf Hr (fun H => Hn (HE _ H)))|].
exact (conj K5 K6).
Qed.

(* free(NULL) keeps the chunks, so the live blocks. *)
Lemma free_null_chunks : forall {ci : CfImg} tr s, cfx_ipost (free_cf PNull tr s) (fun r => st_chunks (snd r) = st_chunks s).
Proof.
intros ci tr s. unfold free_cf, YG00.tick, YG00.bind, YG00.get, YG00.modify, YG00.ret. cbn.
destruct (st_internal_inited s); cbn; reflexivity.
Qed.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.
(* The room record's two fields the rules read (W_journal_x.v Record roomp at commit 479fec81839: rp_RM, and the count
   premise cnt_ok RP), as parameters: there the bridges apply at RM := rp_RM RPi and CNT := cnt_ok RPi.  R1 (the
   ruled placement): RM is room_live_cf with the budget ignored.  The count premise gives the cf count block. *)
Variable RM : astate -> nat -> Prop.
Variable CNT : list (Z * Z) -> Prop.
Hypothesis HRM : RM = fun S _ => room_live_cf S.
Hypothesis HCNT : forall l, CNT l -> cb_cf l.
(* The meter (KF-COUNT, step 1, row 3): MT is generic; the rules' mo_le post follows from the cf model's
   count of granted secondary entries nsec_cf (YGcfNsec.v, stated here as Section hypotheses with its
   exact names and texts) through three arithmetic facts of MT (MO_LE_M / MO_LE_F / MO_LE_R).  At MT_sec they
   follow from its defining equations (Section TOPK). *)
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
Hypothesis MO_LE_M : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n).
Hypothesis MO_LE_F : forall s s', nsec_cf s' <= nsec_cf s -> mo_le MT s s' (mo_free MT).
Hypothesis MO_LE_R : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n + mo_free MT).
(* As Section B's: the hull admission from the rule's count premise; the two image rows. *)
Hypothesis MO_OK_HULL_R : forall s n, 0 <= n -> mo_ok MT s (mo_malloc MT n + mo_free MT) -> cf_hull_ok s.
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.
Local Abbreviation ARX := (fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @arodata_ok_cf CfImg_A segs TfibB mem).
Local Abbreviation ARxs := (fun ly S Hp (W : world segs) mem md => ARcf segs TfibB ly S Hp W mem md /\ xs_placed_cf ly S).

(* The count across the realloc trees: free_cf PNull, malloc_cf n, then (on a block) free_cf of the old block. *)
Lemma nsec_realloc_tree : forall p n tr s, cfx_ipost (ReallocP.realloc_tree_with malloc_cf free_cf p n tr s)
  (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Proof.
intros p n tr s. unfold ReallocP.realloc_tree_with, YG00.bind at 1. apply cfx_ipost_ibind.
eapply cfx_ipost_mono; [|apply nsec_free_cf]. intros [u s1] E1. cbn [fst snd] in E1.
unfold YG00.bind at 1. apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|apply nsec_malloc_cf].
intros [q1 s2] E2. cbn [fst snd] in E2. destruct q1 as [| o | r o | c o]; cbn [fst snd];
  [unfold YG00.ret; cbn; lia | .. ].
all: unfold YG00.bind; apply cfx_ipost_ibind; eapply cfx_ipost_mono; [|apply nsec_free_cf];
     intros [u3 s3] E3; cbn [fst snd] in E3; unfold YG00.ret; cbn; lia.
Qed.

Lemma nsec_realloc_null_tree : forall n tr s, cfx_ipost (ReallocP.realloc_null_tree_with malloc_cf free_cf n tr s)
  (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Proof.
intros n tr s. unfold ReallocP.realloc_null_tree_with, YG00.bind. apply cfx_ipost_ibind.
eapply cfx_ipost_mono; [|apply nsec_free_cf]. intros [u s1] E1. cbn [fst snd] in *.
eapply cfx_ipost_mono; [|apply nsec_malloc_cf]. intros [q1 s2] E2. cbn [fst snd] in *. lia.
Qed.

(* A refused malloc after free(NULL) is impossible at Wf_cf + qtight + rl_prim_ok + the batch room. *)
Lemma refused_impossible : forall n tr S S2, universe_ok (as_universe TfibB) -> Wf_cf (as_universe TfibB) S -> qtight S ->
  rl_prim_ok S -> batch_room_cf S -> In tr (as_universe TfibB) ->
  ReallocP.mt_refused malloc_cf free_cf n tr S S2 -> False.
Proof.
intros n tr S S2 HU HW HQ HP HB Htr (S1 & trc1 & trc2 & Hp1 & Hg1 & Hp2 & Hg2).
destruct (atok_cf_apath _ _ _ _ _ (YG03dcf.ml_free_cf (as_universe TfibB) HU S PNull 0 tr HW HB (or_introl eq_refl) (admits_fix _ _ S HU Htr)) Hp1)
  as (ns & HW1 & _ & _ & _ & _ & HQ1).
pose proof (cfx_ipost_apath _ _ trc1 (tt, S1) (free_null_chunks tr S) Hp1) as EC. cbn [snd] in EC.
assert (HP1 : rl_prim_ok S1) by (intros c Hc; unfold ccnt_c, blocks; rewrite EC; exact (HP c Hc)).
exact (malloc_cf_granted_not_null (as_universe TfibB) S1 n tr trc2 (PNull, S2) HW1 (HQ1 HQ) HP1 Hp2 Hg2 eq_refl).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 7. The realloc rule, in the ruled text at top_x's instance (count block after the bytes premise;               *)
(*    RM Sc (RK_realloc + kr) = room_live_cf Sc; RM S2 kr = room_live_cf S2).                                    *)
Definition ARE_x_room (pc : Z) : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k p n0 n (o : Z) raw ch (kr : nat),
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
(p = 0 \/ In (p, n0) (ablocks TfibB lyc Sc)) ->
getr regsT 10 = w64 p -> getr regsT 11 = w64 n ->
1 <= n < fr_MMAX -> blocks_bytes Sc + n <= LIVE_MAX ->
CNT (ablocks TfibB lyc Sc) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
ly_bot lyc + 4096 < spZ regsT ->
getr regsT 3 = w64 (as_gp TfibB) -> getr regsT 4 = w64 (as_tp TfibB) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AREALLOC ->
RM Sc (2 + kr) ->
(p <> 0 -> In (p, n0) (ablocks TfibB ly S) -> forall i, 0 <= i < req_size n0 -> inFP FP (p + i)) ->
mo_ok MT Sc (mo_malloc MT n + mo_free MT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x segs TfibB [] ARX STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 3) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\
(p = 0 -> Permutation (ablocks TfibB ly2 S2) ((res, n) :: ablocks TfibB lyc Sc)) /\
(p <> 0 -> exists l1 l2, ablocks TfibB lyc Sc = l1 ++ (p, n0) :: l2 /\
  Permutation (ablocks TfibB ly2 S2) ((res, n) :: l1 ++ l2)) /\
(p <> 0 -> forall i, 0 <= i < Z.min n0 n -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) memT (p + i)) /\
acall_kept segs TfibB lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o)
  (fun a => (res <= a < res + req_size n) \/ (p <> 0 /\ p <= a < p + req_size n0)) /\
mo_le MT Sc S2 (mo_malloc MT n + mo_free MT) /\
RM S2 kr /\
(forall i, 0 <= i < 4 -> aview segs (w_H W2) mem2 (as_errno TfibB + i) = aview segs (w_H W) memT (as_errno TfibB + i)) /\
(forall a, in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ aowned TfibB ly2 S2 a ->
 ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
 ~ ((res <= a < res + req_size n) \/ (p <> 0 /\ p <= a < p + req_size n0)) ->
 apresent (w_H W) memT a -> apresent (w_H W2) mem2 a)).

(* The image facts of the post: an image byte outside the call's exceptions keeps its presence. *)
Lemma img_present_keep : forall lyc Sc (W : world segs) regsT memT mdc ly2 S2 W2 mem2 md2 (EX : Z -> Prop) a,
  ARxs lyc Sc [] W memT mdc -> ARxs ly2 S2 [] W2 mem2 md2 ->
  ly_stk_lo lyc + ASTACK <= spZ regsT ->
  (forall x : word, ~ aowned TfibB lyc Sc (bv_unsigned x) -> ~ aowned TfibB ly2 S2 (bv_unsigned x) ->
    ~ ascratch TfibB ASTACK regsT (bv_unsigned x) ->
    ~ (EX (bv_unsigned x) \/ Exists (in_zr (bv_unsigned x)) (xs_cf lyc Sc ++ xs_cf ly2 S2)) -> mem2 x = memT x) ->
  (EX a -> ~ in_img segs a) ->
  in_img segs a -> ~ aowned TfibB lyc Sc a -> ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
  apresent (w_H W) memT a -> apresent (w_H W2) mem2 a.
Proof.
intros lyc Sc W regsT memT mdc ly2 S2 W2 mem2 md2 EX a HA1 HA2 Hslo HRAW HEX Hi Ho1 He [Hh (b & Hm)].
assert (LAWSx : AR_laws_x segs TfibB ARxs cf_head) by exact (AR_laws_x_xs segs TfibB L).
pose proof (segs_low a Hi) as Ha.
split; [exact (img_visible segs segs_low W2 a Hi)|]. exists b. rewrite <- Hm.
assert (Eua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; unfold kLowMemEnd in Ha; lia).
apply HRAW; rewrite Eua.
- exact Ho1.
- intros Ho. apply Ho1.
  apply (proj2 (alx_owned_image _ _ _ LAWSx lyc Sc [] W memT mdc a HA1 Hi)).
  exact (proj1 (alx_owned_image _ _ _ LAWSx ly2 S2 [] W2 mem2 md2 a HA2 Hi) Ho).
- intros [Hs | He']; [|exact (He He')].
  pose proof (lo_top _ (alx_layout_ok _ _ _ LAWSx lyc Sc [] W memT mdc HA1)) as (_ & _ & _ & _ & _ & _ & Hbeg).
  unfold kHighMemBeg, kLowMemEnd, ASTACK in *. lia.
- intros [Hx | Hx]; [exact (HEX Hx Hi)|].
  apply Exists_app in Hx as [Hx|Hx].
  + destruct (ARx_xs_law_xs segs TfibB lyc Sc [] W memT mdc a HA1 Hx) as (_ & _ & Hni & _). exact (Hni Hi).
  + destruct (ARx_xs_law_xs segs TfibB ly2 S2 [] W2 mem2 md2 a HA2 Hx) as (_ & _ & Hni & _). exact (Hni Hi).
Qed.

Theorem ARE_x_room_of_cf : forall pc,
  arealloc_realizes_cf_rp segs TfibB (fun S => ROOM_cf_k S RK_realloc) [] pc ->
  YGcfRealloc.arealloc_null_realizes_cf segs TfibB [] pc ->
  ARE_x_room pc.
Proof.
intros pc AR ARN W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k p n0 n o raw ch kr
  HJ Hp0 Ha0 Ha1 Hn Hlive HCB Hsp Hal Hneg Hbud Hpfx Hgp Htp Hra Hraw Hch HCTX HRL HFP HMO.
destruct (HCNT _ HCB) as (Hc1 & Hc2 & Hc3). rewrite HRM in HRL. cbv beta in HRL.
pose proof HJ as ([HARc [HHp HAD]] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
subst Hpc.
pose proof (proj1 (count_block_iff_cfr TfibB lyc Sc) (conj Hc1 (conj Hc2 Hc3))) as (HSEC & H24 & HB24 & HPRIM).
pose proof (room_live_room Sc HRL) as HROOM.
pose proof (MO_OK_HULL_R Sc n ltac:(lia) HMO) as HHULL.
pose proof (QMm_cf_of_room segs TfibB lyc Sc [] W memT mdc HARc HQT HROOM HHULL HAD) as HQM.
pose proof HQM as (_ & _ & _ & _ & HBR & _).
pose proof (universe_ok_of_ARcf segs TfibB lyc Sc [] W memT mdc HARc) as HU.
pose proof (amc_wf _ _ _ _ _ (proj1 HARc)) as HWF.
pose proof (cfr_ctx_arealloc lyc regsT ch Sc HCTX) as Htr. unfold cf_trace_ok, cf_tr_ok in Htr.
pose proof (aj_to_xs segs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJx.
assert (Hn' : 1 <= n < cf_malloc_max) by exact Hn.
assert (HARxs : ARxs lyc Sc [] W memT mdc) by exact (conj HARc (xs_placed_of_ARcf segs TfibB lyc Sc [] W memT mdc HARc)).
destruct (Z.eq_dec p 0) as [-> | Hpn].
- (* realloc(NULL, n) *)
  pose proof (aj_realloc_null_at_x_ct segs TfibB [] L segs_low errno_low HU pc
    W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc [] mdc k n o raw ch ARN HJx Ha0 Ha1 Hn' Hlive
    Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr) as HSR.
  eapply SRr_mono; [exact HSR|].
  intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2' & HJ2 & Hpres & Hres & Hfrs & HPRE &
    (q & trc & Hpath & Hgf & Hleaf & Href & Hiff & Hres2 & Herrno & Hrawf) & Harms).
  assert (Hqn : q <> PNull)
    by (intros E; exact (refused_impossible n _ Sc S2 HU HWF HQT HPRIM HBR Htr (Href E))).
  destruct Harms as [(Hr0 & _) | (H4096 & Eab & Hkept)]; [exfalso; apply Hqn; apply Hiff; exact Hr0|].
  pose proof (realloc_null_tree_nev n _ Sc trc q S2 Hpath Hqn) as Hnev.
  pose proof HJ2 as (HA2 & _).
  pose proof HPRE as (_ & _ & _ & Hslo & _).
  (* the post's arodata, from the raw frame: the new block is a live block of the post, off the image *)
  assert (HAD2 : arodata_ok_cf segs TfibB mem2).
  { apply (arodata_post_keep segs TfibB lyc Sc [] W regsT memT mdc ly2 S2 [] W2 mem2 md2
      (fun x => (q <> PNull /\ res <= x < res + req_size n) \/ Exists (in_zr x) (xs_cf lyc Sc ++ xs_cf ly2 S2))
      HRS HER HARc (proj1 HA2) Hslo); [| |exact HAD].
    - intros a I1 I2 X1 X2 [[_ Hb] | Hx].
      + assert (Hinab : In (res, n) (ablocks TfibB ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
        exact (ablock_not_img_cfr TfibB ly2 S2 [] _ res n a (proj1 (proj1 HA2)) Hinab I2 Hb).
      + apply Exists_app in Hx as [Hx|Hx]; [exact (X1 Hx) | exact (X2 Hx)].
    - intros x NX. apply Hrawf; intros H; apply NX; tauto. }
  exists ly2, S2, [], regs2, mem2, md2, res.
  split; [exact Hc2'|].
  split.
  { apply (aj_of_xs segs); [reflexivity | exact HAD2 |]. eapply aj_k_le; [|exact HJ2]; lia. }
  split; [exact Hpres|]. split; [exact Hres|]. split; [exact Hfrs|]. split; [exact H4096|].
  split; [intros _; rewrite Eab; apply Permutation_sym; apply Permutation_cons_append|].
  split; [intros Hc; exfalso; exact (Hc eq_refl)|].
  split; [intros Hc; exfalso; exact (Hc eq_refl)|].
  split; [eapply kept_mono; [|exact Hkept]; intros a Ha; left; exact Ha|].
  split; [exact (MO_LE_R Sc S2 n ltac:(lia) (cfx_ipost_apath _ _ trc (q, S2) (nsec_realloc_null_tree n _ Sc) Hpath))|].
  split.
  { rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
      (or_intror (or_intror (or_intror (ex_intro _ n (ex_intro _ _ (ex_intro _ trc (ex_intro _ q Hpath)))))))). }
  split.
  { intros i Hi. apply (aview_img_eq segs segs_low).
    - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
    - exact (Herrno Hqn i Hi). }
  intros a Hi Ho1 Ho2 He Hb.
  apply (img_present_keep lyc Sc W regsT memT mdc ly2 S2 W2 mem2 md2 (fun x => q <> PNull /\ res <= x < res + req_size n) a
    HARxs HA2 Hslo); [| | exact Hi | exact Ho1 | exact He].
  + intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
    intros [Hx | Hx]; apply H4; [left; exact Hx | right; exact Hx].
  + intros [_ Hblk] Hi'.
    assert (Hinab : In (res, n) (ablocks TfibB ly2 S2)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
    assert (LAWSx : AR_laws_x segs TfibB ARxs cf_head) by exact (AR_laws_x_xs segs TfibB L).
    destruct (alx_client_img _ _ _ LAWSx ly2 S2 [] W2 mem2 md2 a HA2
      (or_introl (ex_intro _ res (ex_intro _ n (conj Hinab Hblk))))) as (_ & Hni).
    exact (Hni Hi').
- (* realloc(p, n) of a live block *)
  destruct Hp0 as [E | Hin]; [exfalso; exact (Hpn E)|].
  pose proof (aj_realloc_at_x_ct segs TfibB [] L segs_low errno_low HU (fun S => ROOM_cf_k S RK_realloc) pc
    (amx_realloc_rp_room TfibB HU)
    W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc [] mdc k p n0 n o raw ch AR HJx Hin (fun H => H) Ha0 Ha1 Hn' Hlive
    Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HQM (room_live_room_k Sc HRL) Hch Htr (HFP Hpn)) as HSR.
  eapply SRr_mono; [exact HSR|].
  intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & res & Hc2' & HJ2 & Hpres & Hres & Hfrs & HPRE &
    (q & p' & trc & Hpq & Hpin & Hpath & Hgf & Hleaf & Href & EHp & Hiff & Hres2 & Hcopy & Herrno & Hrawf) & Harms).
  assert (Hqn : q <> PNull)
    by (intros E; exact (refused_impossible n _ Sc S2 HU HWF HQT HPRIM HBR Htr (Href E))).
  destruct Harms as [(Hr0 & _) | (H4096 & Hsplit & Hkept)]; [exfalso; apply Hqn; apply Hiff; exact Hr0|].
  pose proof (realloc_tree_nev p' n _ Sc trc q S2 Hpath Hqn) as Hnev.
  assert (Hn0 : 0 <= n < cf_malloc_max) by (destruct Hn' as [Hn1 Hn2]; split; [lia | exact Hn2]).
  pose proof HJ2 as (HA2 & _).
  pose proof HPRE as (_ & _ & _ & Hslo & _).
  (* the post's arodata, from the raw frame: the new block (live at the post) and the old one (live at the call) are
     off the image *)
  assert (HAD2 : arodata_ok_cf segs TfibB mem2).
  { apply (arodata_post_keep segs TfibB lyc Sc [] W regsT memT mdc ly2 S2 [] W2 mem2 md2
      (fun x => (q <> PNull /\ res <= x < res + req_size n) \/ (q <> PNull /\ p <= x < p + req_size n0) \/
         Exists (in_zr x) (xs_cf lyc Sc ++ xs_cf ly2 S2))
      HRS HER HARc (proj1 HA2) Hslo); [| |exact HAD].
    - intros a I1 I2 X1 X2 [[_ Hb] | [[_ Hb] | Hx]].
      + destruct Hsplit as (l1 & l2 & _ & Hperm2).
        assert (Hinab : In (res, n) (ablocks TfibB ly2 S2))
          by (apply (Permutation_in _ (Permutation_sym Hperm2)); left; reflexivity).
        exact (ablock_not_img_cfr TfibB ly2 S2 [] _ res n a (proj1 (proj1 HA2)) Hinab I2 Hb).
      + exact (ablock_not_img_cfr TfibB lyc Sc [] _ p n0 a (proj1 HARc) Hin I1 Hb).
      + apply Exists_app in Hx as [Hx|Hx]; [exact (X1 Hx) | exact (X2 Hx)].
    - intros x NX. apply Hrawf; intros H; apply NX; tauto. }
  exists ly2, S2, [], regs2, mem2, md2, res.
  split; [exact Hc2'|].
  split.
  { apply (aj_of_xs segs); [reflexivity | exact HAD2 |]. replace (k + 3) with (k + (st_nev S2 - st_nev Sc)) by lia. exact HJ2. }
  split; [exact Hpres|]. split; [exact Hres|]. split; [exact Hfrs|]. split; [exact H4096|].
  split; [intros Hc; exfalso; exact (Hpn Hc)|].
  split; [intros _; exact Hsplit|].
  split; [intros _; exact (Hcopy Hqn)|].
  split; [eapply kept_mono; [|exact Hkept]; intros a [Ha | Ha]; [left; exact Ha | right; exact (conj Hpn Ha)]|].
  split; [exact (MO_LE_R Sc S2 n ltac:(lia) (cfx_ipost_apath _ _ trc (q, S2) (nsec_realloc_tree p' n _ Sc) Hpath))|].
  split.
  { rewrite HRM. exact (room_live_call_keep (as_universe TfibB) 1024 (2 ^ 15) Sc S2 HWF HQT HSEC H24 HB24 HRL
      (or_intror (or_intror (or_introl (ex_intro _ p' (ex_intro _ n (ex_intro _ _ (ex_intro _ trc (ex_intro _ q
        (conj HU (conj (admits_fix _ _ Sc HU Htr) (conj Hn0 (conj Hlive Hpath))))))))))))). }
  split.
  { intros i Hi. apply (aview_img_eq segs segs_low).
    - exact (proj1 (proj2 errno_low) (as_errno TfibB + i) ltac:(lia)).
    - exact (Herrno Hqn i Hi). }
  intros a Hi Ho1 Ho2 He Hb.
  apply (img_present_keep lyc Sc W regsT memT mdc ly2 S2 W2 mem2 md2
    (fun x => (q <> PNull /\ res <= x < res + req_size n) \/ (q <> PNull /\ p <= x < p + req_size n0)) a
    HARxs HA2 Hslo); [| | exact Hi | exact Ho1 | exact He].
  + intros x H1 H2 H3 H4. apply Hrawf; [exact H1 | exact H2 | exact H3 |].
    intros [Hx | [Hx | Hx]]; apply H4; [left; left; exact Hx | left; right; exact Hx | right; exact Hx].
  + intros [[_ Hblk] | [_ Hblk]] Hi'.
    * apply Hb. left. exact Hblk.
    * apply Hb. right. exact (conj Hpn Hblk).
Qed.


End R.

(* ---------------------------------------------------------------------------- *)
(* 8. top_x's INSTANCE OF THE ROOM RECORD: RP_cf is the cf instance: RM := room_live_cf with the budget ignored (R1),  *)
(*    the counts at top_x's fields (Lsec 1024, L24 2 ^ 15, LPRIM := RL_PRIM), the two laws by NAMED terms: rp_RMM by   *)
(*    HRM's form (fun S k k' _ H => H), rp_RPF := YGcfRoomLive.room_live_set_fs.  The count premise gives cb_cf by the  *)
(*    NAMED lemma cnt_ok_cb_cf (cnt_ok adds `+ 0`, which does not reduce).  The four rules at RP_cf are Section TOPK's  *)
(*    (the rules at the trivial meter ameter_triv are deleted: its mo_ok cannot give the hull admission).               *)
Section TOP. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.

(* The count fields are ReplyCnt.v's top_x instance names (one definition each): Psec, P24, Lsec (1024), L24
   (2 ^ 15), Pcls, LPRIM (Z.to_nat (RL_PRIM c)). *)
Definition RP_cf : roomp :=
  {| rp_RM := fun S _ => room_live_cf S; rp_Psec := ReplyCnt.Psec; rp_P24 := ReplyCnt.P24;
     rp_Lsec := ReplyCnt.Lsec; rp_L24 := ReplyCnt.L24; rp_Pcls := ReplyCnt.Pcls; rp_LPRIM := ReplyCnt.LPRIM;
     rp_RMM := fun S k k' _ H => H; rp_RPF := fun S f k => room_live_set_fs S f |}.

Lemma cnt_ok_cb_cf : forall l, cnt_ok RP_cf l -> cb_cf l.
Proof.
intros l H. unfold cnt_ok, cnt_ok_pk in H. destruct H as (A & Bq & C).
change (acnt rl_sec_req l + 0 <= 1024)%nat in A.
change (acnt (PresetRoom.in_cls kBatchClass) l + 0 <= Z.to_nat (2 ^ 15))%nat in Bq.
assert (E24 : Z.to_nat (2 ^ 15) = 32768%nat) by (vm_compute; reflexivity). rewrite E24 in Bq.
unfold cb_cf. change (2 ^ 15)%nat with 32768%nat.
split; [lia|]. split; [lia|]. intros c Hc. specialize (C c Hc).
change (acnt (PresetRoom.in_cls c) l + 0 <= Z.to_nat (RL_PRIM c))%nat in C. lia.
Qed.
End TOP.

(* ---------------------------------------------------------------------------- *)
(* 9. KF-COUNT: the same four rules at a meter MT given by MT_sec's defining equations (ReplyKfMeter.v;             *)
(*    the count nsec_cf and its two step facts are YGcfNsec.v's, as Section hypotheses with its exact                *)
(*    names).  When both land, ONE lemma instantiates MT := MT_sec and nsec_cf := YGcfNsec's.                          *)
Section TOPK. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.
Variable segs : list Segment.
Hypothesis L : AR_laws_cf segs TfibB.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs TfibB.
Local Abbreviation ARX := (fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @arodata_ok_cf CfImg_A segs TfibB mem).
(* FIT CHECK of the relation: the rules' ARX is top_x's relation after W1, whose text is quoted
   here VERBATIM from commit b27e847023f8, lib/A/W_LLVMFuzzerTestOneInput_top_x.v:171-172
   (Definition ARX's body); it closes by reflexivity only if the two are the same term. *)
Goal ARX = (
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_A segs TfibB mem).
Proof. reflexivity. Qed.
Variable MT : ameter_ops.
Variable nsec_cf : astate -> Z.
Hypothesis nsec_malloc_cf : forall n tr s,
  cfx_ipost (malloc_cf n tr s) (fun r => nsec_cf (snd r) <= nsec_cf s + (if from_primary n then 0 else 1)).
Hypothesis nsec_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun r => nsec_cf (snd r) <= nsec_cf s).
(* MT_sec's defining equations, its literal text (ReplyKfMeter.v at a968c6e24aec: mkAMeter (fun s m => nsec s + m <= KMAX)
   (fun s s' m => nsec s' <= nsec s + m) (fun n => if 64512 <? n then 1 else 0) 0); each holds by reflexivity at
   MT := MT_sec nsec_cf cf_kmax.  mo_ok is not used by these rules' posts. *)
Hypothesis MT_malloc : forall n, mo_malloc MT n = if 64512 <? n then 1 else 0.
Hypothesis MT_free : mo_free MT = 0.
Hypothesis MT_le : forall s s' m, mo_le MT s s' m <-> nsec_cf s' <= nsec_cf s + m.
(* MT_sec's fourth defining equation, its mo_ok (MT_ok, the same text route R's TOPK_rh takes, commit
   07260ccc92a1 lib/A/CfRBridgeRulesRhTop.v:267): at MT := MT_sec YGcfNames.nsec_cf cf_kmax it holds by iff_refl. *)
Hypothesis MT_ok : forall s m, mo_ok MT s m <-> YGcfNames.nsec_cf s + m <= cf_kmax.
(* The unit's two image rows (Section B's HRS / HER). *)
Hypothesis HRS : relro_seg_t segs.
Hypothesis HER : errno_relro_t TfibB.

(* The primary cutoff: for n >= 0, a secondary request (from_primary n = false) is exactly n > 64,512
   (YGcfRoom.is_primary_eq, ReplyLSCntL.is_sec_iff over ReplyCnt.Psec). *)
Lemma sec_cost_cut : forall n, 0 <= n -> (if from_primary n then 0 else 1) = (if 64512 <? n then 1 else 0).
Proof.
intros n Hn. pose proof (ReplyLSCntL.is_sec_iff n Hn) as E. unfold ReplyCnt.Psec in E.
rewrite YGcfRoom.is_primary_eq in E.
destruct (from_primary n) eqn:F; cbn in E; destruct (64512 <? n) eqn:G; try reflexivity.
- apply Z.ltb_lt in G. symmetry in E. apply Z.leb_gt in E. lia.
- apply Z.ltb_ge in G. symmetry in E. apply Z.leb_le in E. lia.
Qed.

Lemma kf_MO_LE_M : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n).
Proof. intros s s' n Hn H. apply MT_le. rewrite MT_malloc, <- (sec_cost_cut n Hn). exact H. Qed.
Lemma kf_MO_LE_F : forall s s', nsec_cf s' <= nsec_cf s -> mo_le MT s s' (mo_free MT).
Proof. intros s s' H. apply MT_le. rewrite MT_free. lia. Qed.
Lemma kf_MO_LE_R : forall s s' n, 0 <= n -> nsec_cf s' <= nsec_cf s + (if from_primary n then 0 else 1) ->
  mo_le MT s s' (mo_malloc MT n + mo_free MT).
Proof. intros s s' n Hn H. apply MT_le. rewrite MT_malloc, MT_free, <- (sec_cost_cut n Hn). lia. Qed.

(* The hull admission from the meter (QMm): CfParams_reply's cf_hull_ok s is YGcfNames.nsec_cf s <= cf_kmax, and a
   nonnegative charge m under mo_ok bounds it. *)
Lemma MT_ok_hull : forall s m, 0 <= m -> mo_ok MT s m -> cf_hull_ok s.
Proof. intros s m Hm H. apply MT_ok in H. cbn [cf_hull_ok cf_kmax CfParams_reply]. cbn [cf_kmax CfParams_reply] in H. lia. Qed.
Lemma kf_MO_OK_HULL_M : forall s n, 0 <= n -> mo_ok MT s (mo_malloc MT n) -> cf_hull_ok s.
Proof. intros s n _ H. apply (MT_ok_hull s (mo_malloc MT n)); [rewrite MT_malloc; destruct (64512 <? n); lia | exact H]. Qed.
Lemma kf_MO_OK_HULL_F : forall s, mo_ok MT s (mo_free MT) -> cf_hull_ok s.
Proof. intros s H. apply (MT_ok_hull s (mo_free MT)); [rewrite MT_free; lia | exact H]. Qed.
Lemma kf_MO_OK_HULL_R : forall s n, 0 <= n -> mo_ok MT s (mo_malloc MT n + mo_free MT) -> cf_hull_ok s.
Proof.
intros s n _ H. apply (MT_ok_hull s (mo_malloc MT n + mo_free MT)); [|exact H].
rewrite MT_malloc, MT_free. destruct (64512 <? n); lia.
Qed.

Ltac kf_meter := first [ exact nsec_malloc_cf | exact nsec_free_cf | exact kf_MO_LE_M | exact kf_MO_LE_F | exact kf_MO_LE_R
  | exact kf_MO_OK_HULL_M | exact kf_MO_OK_HULL_F | exact kf_MO_OK_HULL_R | exact HRS | exact HER ].

Theorem AMA_x_kf : amalloc_realizes_cf segs TfibB ->
  amalloc_cf_rule_c_x segs TfibB [] ARX MT fr_MMAX RP_cf CTX_AMALLOC.
Proof.
intros AM. eapply (AMA_x_room_of_cf segs L segs_low errno_low (rp_RM RP_cf) (cnt_ok RP_cf) eq_refl cnt_ok_cb_cf
  MT nsec_cf); first [exact AM | kf_meter].
Qed.

Theorem AFREE_x_kf : afree_realizes_cf segs TfibB ->
  afree_cf_rule_c_x segs TfibB [] ARX MT RP_cf CTX_AFREE.
Proof.
intros AF. eapply (AFREE_x_room_of_cf segs L segs_low errno_low (rp_RM RP_cf) (cnt_ok RP_cf) eq_refl cnt_ok_cb_cf
  MT nsec_cf); first [exact AF | kf_meter].
Qed.

Theorem AFREEN_x_kf : afree_realizes_cf segs TfibB ->
  afree_null_cf_rule_c_x segs TfibB [] ARX MT RP_cf CTX_AFREE.
Proof.
intros AF. eapply (AFREEN_x_room_of_cf segs L segs_low errno_low (rp_RM RP_cf) (cnt_ok RP_cf) eq_refl cnt_ok_cb_cf
  MT nsec_cf); first [exact AF | kf_meter].
Qed.

Theorem ARE_x_kf : forall pc,
  arealloc_realizes_cf_rp segs TfibB (fun S => ROOM_cf_k S RK_realloc) [] pc ->
  YGcfRealloc.arealloc_null_realizes_cf segs TfibB [] pc ->
  arealloc_cf_rule_c_x segs TfibB [] ARX MT fr_MMAX RP_cf CTX_AREALLOC pc.
Proof.
intros pc AR ARN. eapply (ARE_x_room_of_cf segs L segs_low errno_low (rp_RM RP_cf) (cnt_ok RP_cf) eq_refl cnt_ok_cb_cf
  MT nsec_cf); first [exact AR | exact ARN | kf_meter].
Qed.
End TOPK.

Print Assumptions AMA_x_room_of_cf.
Print Assumptions AFREE_x_room_of_cf.
Print Assumptions AFREEN_x_room_of_cf.
Print Assumptions ARE_x_room_of_cf.
Print Assumptions AMA_x_kf.
Print Assumptions AFREE_x_kf.
Print Assumptions AFREEN_x_kf.
Print Assumptions ARE_x_kf.
