(* LLVMFuzzerTestOneInput_segX_up_d: the state the image-B up segment of LLVMFuzzerTestOneInput carries from
   malloc #3 to its end (up_inv: the frame invariant at the event count after the malloc, the two blocks, the
   meter, the memory clauses and the registers the post reads), and the three calls after malloc #3 in that
   form: __asan_memset of the upstream buffer (lib/A/Prog/YC85.v aj_intrin_atS through lib/Reusable/YCbq.v:1955
   aj_intrin_at, as lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_calls.v c1e_memset_call calls it for the decode
   buffer) and reac_upstream_decode (lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_leaf.v dec_leafb_upstream_decode).
   The bytes a call keeps carry the invariant over through lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_kit.v
   up_win_kept. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC85 DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBPa DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr DecodeBImg check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs reac_upstream_channels_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_exit_defs
  LLVMFuzzerTestOneInput_segX_up_kit LLVMFuzzerTestOneInput_segX_up_b LLVMFuzzerTestOneInput_segX_crt1_calls
  LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_upstream_decode_c reac_decode_c LeafCgKit
  reac_upstream_decode_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_up_arith.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the originals
   (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws decodesegsB0 B.
Local Abbreviation segs := decodesegsB0.

(* ---- the invariant after malloc #3 ---- *)
Definition up_inv (cx : dctx) (res mode nch ns upb : Z) (ly : alayout) (S : astate) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  dec_b_core B cx ly S W regs mem md dec_ev_96c /\
  Permutation (ablocks B ly S) (ablocks B (d_ly cx) (d_S cx) ++ [(res, up_len cx)] ++ [(upb, up_uo cx)]) /\
  4096 <= res /\ 4096 <= upb /\
  mo_le MT (d_S cx) S (dec_spent_96c MT (d_n cx)) /\ mo_ok MT S (dec_rest_96c MT) /\
  up_mem cx W mem res mode nch ns /\
  YK11.getr regs 18 = w64 SHADOW_OFF /\ YK11.getr regs 21 = w64 (up_r cx) /\
  YK11.getr regs 22 = w64 (up_len cx) /\ YK11.getr regs 24 = w64 (up_uo cx) /\ YK11.getr regs 27 = w64 res.

Definition up_keepI : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 22%bv; 24%bv; 27%bv].

(* A run that writes nothing: other registers, another model, the same memory. *)
Lemma up_inv_run : forall cx res mode nch ns upb ly S W regs mem md regs' md',
  up_inv cx res mode nch ns upb ly S W regs mem md ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem md' dec_ev_96c ->
  (forall x, In x up_keepI -> YK11.getr regs' x = YK11.getr regs x) ->
  up_inv cx res mode nch ns upb ly S W regs' mem md'.
Proof.
intros cx res mode nch ns upb ly S W regs mem md regs' md'
  (Hcore & Hperm & Hres & Hupb & Hmle & Hmok & Hmem & H18 & H21 & H22 & H24 & H27) HJ' HK.
pose proof Hcore as (_ & Hfrs & _).
assert (K : forall x, In x up_keepI -> YK11.getr regs' x = YK11.getr regs x) by exact HK.
split.
{ apply (ex_core_kept B cx ly S W regs mem md dec_ev_96c ly S W regs' mem md' dec_ev_96c Hcore HJ' Hfrs);
    try (apply K; cbn; tauto); try (intros; reflexivity); try (intros; split; reflexivity).
  - unfold spZ. f_equal. apply K. cbn; tauto.
  - intros a Ha. pose proof Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFp & _). exact (HFp a Ha).
  - pose proof Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpay & _). exact Hpay. }
repeat (split; [assumption|]).
rewrite (K 18%bv), (K 21%bv), (K 22%bv), (K 24%bv), (K 27%bv) by (cbn; tauto).
repeat split; assumption.
Qed.
(* Two entries of the block list are disjoint blocks. *)
Lemma up_perm_disj : forall ly S W mem md L x y,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (L ++ [x]) -> In y L ->
  zdisjoint (block_rng y) (block_rng x).
Proof.
intros ly S W mem md L x y HAR Hp Hy. apply in_split in Hy as (l1 & l2 & ->).
apply (sep_blocks_perm segs B LAWS ly S W mem md y x (l1 ++ l2) HAR).
eapply Permutation_trans; [exact Hp|]. rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
rewrite app_assoc. apply Permutation_sym. apply Permutation_cons_append.
Qed.

Lemma up_req_uo : forall cx, 1 <= up_uo cx -> req_size (up_uo cx) = up_uo cx.
Proof. intros cx H. unfold req_size. destruct (Z.eqb_spec (up_uo cx) 0); lia. Qed.

(* The facts about the upstream buffer the steps after malloc #3 use. *)
Lemma up_inv_blocks : forall cx res mode nch ns upb ly S W regs mem md,
  0 <= d_n cx < 67108864 ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  up_inv cx res mode nch ns upb ly S W regs mem md ->
  In (upb, up_uo cx) (ablocks B ly S) /\ ~ In (upb, up_uo cx) (ablocks B (d_ly cx) (d_S cx)) /\
  In (res, up_len cx) (ablocks B ly S) /\
  zdisjoint (block_rng (res, up_len cx)) (block_rng (upb, up_uo cx)) /\
  (0 < d_n cx -> zdisjoint (block_rng (d_p cx, d_n cx)) (block_rng (upb, up_uo cx))) /\
  1 <= up_uo cx <= 1440 /\ upb + up_uo cx <= alloc_ceiling.
Proof.
intros cx res mode nch ns upb ly S W regs mem md Hn Hpay0
  (Hcore & Hperm & Hres & Hupb & Hmle & Hmok & Hmem & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpay & _).
pose proof (proj1 HJ) as HAR.
pose proof (up_uo_bounds cx Hn) as Huo.
assert (Hin : In (upb, up_uo cx) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_app_iff; right; right; left; reflexivity).
assert (Hres_in : In (res, up_len cx) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_app_iff; right; left; reflexivity).
assert (Hp2 : Permutation (ablocks B ly S) ((ablocks B (d_ly cx) (d_S cx) ++ [(res, up_len cx)]) ++ [(upb, up_uo cx)]))
  by (rewrite <- app_assoc; exact Hperm).
destruct (al_blocks _ _ LAWS ly S W mem md upb _ HAR Hin) as (_ & _ & Hc & _).
rewrite (up_req_uo cx ltac:(lia)) in Hc.
split; [exact Hin|]. split.
{ intros Hb. apply (ex_perm_twice B LAWS ly S W mem md (ablocks B (d_ly cx) (d_S cx)) ([(res, up_len cx)] ++ [(upb, up_uo cx)])
    (upb, up_uo cx) HAR Hperm Hb). apply in_app_iff. right. left. reflexivity. }
split; [exact Hres_in|]. split.
{ apply (up_perm_disj ly S W mem md _ _ _ HAR Hp2). apply in_app_iff. right. left. reflexivity. }
split.
{ intros Hn0. apply (up_perm_disj ly S W mem md _ _ _ HAR Hp2). apply in_app_iff. left. exact (Hpay0 Hn0). }
split; [exact Huo | exact Hc].
Qed.
(* A call that writes only inside the upstream buffer (and its own stack window) keeps the invariant. *)
Lemma up_inv_call : forall cx res mode nch ns upb ly S W regs mem md regs2 mem2 md2 (Wr : Z -> Prop),
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> rom_view segs (d_W cx) (d_mem cx) ->
  0 <= d_n cx < 67108864 -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  up_inv cx res mode nch ns upb ly S W regs mem md ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 dec_ev_96c ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx) -> ~ Wr a ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  (forall a, Wr a -> upb <= a < upb + up_uo cx) ->
  up_inv cx res mode nch ns upb ly S W regs2 mem2 md2.
Proof.
intros cx res mode nch ns upb ly S W regs mem md regs2 mem2 md2 Wr HC HO HE HR Hn Hnlen Hpay0 Hinv HJ2 HP Heff Hpres
  HWr.
destruct (up_inv_blocks cx res mode nch ns upb ly S W regs mem md Hn Hpay0 Hinv)
  as (Hin & Hnin & Hres_in & Hdres & Hdpay & Huo & Hc).
pose proof Hinv as (Hcore & Hperm & Hres & Hupb & Hmle & Hmok & Hmem & H18 & H21 & H22 & H24 & H27).
pose proof Hcore as (HJ & Hfrs & _ & _ & _ & Hsp1r & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
unfold block_rng in Hdres, Hdpay. cbn [fst snd] in Hdres, Hdpay.
rewrite (up_req_uo cx ltac:(lia)) in Hdres, Hdpay.
destruct (al_blocks _ _ LAWS ly S W mem md upb _ HAR Hin) as (_ & H4096 & _ & Happ & _).
rewrite (up_req_uo cx ltac:(lia)) in Happ.
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
pose proof (sep_block_frame segs B LAWS ly S W mem md upb (up_uo cx) DEC_FCLASS (d_fpos cx) HAR Hin Hin0) as HdF.
rewrite (up_req_uo cx ltac:(lia)) in HdF.
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
rewrite EFA in HdF. change (fs_frame_bytes DEC_FCLASS) with 64 in HdF.
destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (Hb1 & Hb2 & _).
rewrite EFA in Hb1, Hb2. change (fs_frame_bytes DEC_FCLASS) with 64 in Hb2.
destruct (up_win_kept B cx ly S W regs mem md dec_ev_96c regs2 mem2 md2 res mode nch ns Wr LAWS HC HO HE HR Hnlen
  Hcore HJ2 HP Heff Hpres) as [Hcore2 Hmem2].
- intros a Ha Hw. apply HWr in Hw. lia.
- intros a Ha Hw. apply HWr in Hw. unfold zdisjoint in HdF. cbn [fst snd] in HdF. lia.
- intros a Ha Hw. apply HWr in Hw. unfold d_SH, shadow_addr in Ha.
  assert (HF8 : 0 <= d_F cx / 8 <= 0x7fffff800000 / 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
  change (0x7fffff800000 / 8) with 17592184995840 in HF8.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF in *. lia.
- intros i Hi Hw. apply HWr in Hw. destruct (Z.lt_ge_cases 0 (d_n cx)) as [Hn0 | Hn0]; [|lia].
  pose proof (Hdpay Hn0) as Hd. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos (d_n cx) ltac:(lia)). lia.
- exact Hres_in.
- intros i Hi Hw. apply HWr in Hw. unfold zdisjoint, block_rng in Hdres. cbn [fst snd] in Hdres.
  unfold up_len in Hdres. lia.
- exact Hmem.
- split; [exact Hcore2|]. split; [exact Hperm|]. split; [exact Hres|]. split; [exact Hupb|].
  split; [exact Hmle|]. split; [exact Hmok|]. split; [exact Hmem2|].
  assert (K : forall r : Z, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
    by exact HP.
  split; [transitivity (YK11.getr regs 18); [exact (K 18 ltac:(unfold acallee_saved; lia)) | exact H18]|].
  split; [transitivity (YK11.getr regs 21); [exact (K 21 ltac:(unfold acallee_saved; lia)) | exact H21]|].
  split; [transitivity (YK11.getr regs 22); [exact (K 22 ltac:(unfold acallee_saved; lia)) | exact H22]|].
  split; [transitivity (YK11.getr regs 24); [exact (K 24 ltac:(unfold acallee_saved; lia)) | exact H24]|].
  transitivity (YK11.getr regs 27); [exact (K 27 ltac:(unfold acallee_saved; lia)) | exact H27].
Qed.

(* The fill survives a call that writes nothing of the upstream buffer. *)
Lemma up_filled_kept : forall cx res mode nch ns upb ly S W regs mem md mem2 (Wr : Z -> Prop),
  0 <= d_n cx < 67108864 -> (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  up_inv cx res mode nch ns upb ly S W regs mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx) -> ~ Wr a ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, ~ Wr a) ->
  dec_b_filled W mem upb (up_uo cx) -> dec_b_filled W mem2 upb (up_uo cx).
Proof.
intros cx res mode nch ns upb ly S W regs mem md mem2 Wr Hn Hpay0 Hinv Heff HnW Hf i Hi.
destruct (up_inv_blocks cx res mode nch ns upb ly S W regs mem md Hn Hpay0 Hinv)
  as (_ & _ & _ & _ & _ & Huo & Hc).
pose proof Hinv as (Hcore & _ & _ & Hupb & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hsp1r & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & _).
rewrite Heff; [exact (Hf i Hi) | lia | lia | exact (HnW _)].
Qed.
Lemma up_body_len : forall cx, d_n cx = Z.of_nat (length (d_pl cx)) ->
  length (d_body cx) = Z.to_nat (up_len cx).
Proof. intros cx Hnlen. unfold d_body, up_len, dec_b_len, dec_b_u. rewrite length_skipn. lia. Qed.

(* __asan_memset(upb, 0xa5, olen) at +0x8d8. *)
Lemma up_memset_step : forall cx res mode nch ns upb ly S (W : world segs) regs mem md
    (Q : world segs -> config -> Prop),
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (decodeb_sigma DB___asan_memset)) ->
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> rom_view segs (d_W cx) (d_mem cx) ->
  0 <= d_n cx < 67108864 -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  up_inv cx res mode nch ns upb ly S W regs mem md ->
  YK11.getr regs 10 = w64 upb -> YK11.getr regs 11 = w64 165 -> YK11.getr regs 12 = w64 (up_uo cx) ->
  YK11.getr regs 1 = Z_to_bv 64 (decodeb_text + 0x8dc) ->
  (forall regs2 mem2 md2, up_inv cx res mode nch ns upb ly S W regs2 mem2 md2 -> aregs_preserved regs regs2 ->
     dec_b_filled W mem2 upb (up_uo cx) ->
     SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (decodeb_text + 0x8dc)) mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (decodeb_sigma DB___asan_memset)) mem (YK11.seg_rom segs)) md) Q.
Proof.
intros cx res mode nch ns upb ly S W regs mem md Q AMS HC HO HE HR Hn Hnlen Hpay0 Hinv R10 R11 R12 Rra HK.
destruct (up_inv_blocks cx res mode nch ns upb ly S W regs mem md Hn Hpay0 Hinv)
  as (Hin & Hnin & _ & _ & _ & Huo & Hc).
pose proof Hinv as (Hcore & _).
pose proof Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Ho16 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp1al; [|lia]. apply Z.mod_divide in Hsp0al; [|lia].
  destruct Hsp1al as [q1 Hq1]. destruct Hsp0al as [q0 Hq0]. exists (2 * q1 - q0). lia. }
pose proof (up_req_uo cx ltac:(lia)) as Hrq.
eapply SRr_bind.
{ apply (c1e_memset_call B LAWS AMS fx DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem md dec_ev_96c regs (d_sp1 cx - d_sp0 cx) upb (up_uo cx) (YK11.getr regs 1)
    HJ Hin Hnin).
  - rewrite Hrq. lia.
  - exact R10.
  - exact R11.
  - rewrite Hrq. exact R12.
  - rewrite Hsp. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK. lia.
  - exact Hgp.
  - exact Htp.
  - reflexivity.
  - rewrite Rra. change (decodeb_text + 0x8dc) with (@pa_val _ decodeb_listing PI_decodeb A_TEXT + 0x8dc).
    apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & H10' & Hfill & Heff & Hpres).
rewrite Rra. apply HK.
- apply (up_inv_call cx res mode nch ns upb ly S W regs mem md regs2 mem2 md2
    (fun a => upb <= a < upb + req_size (up_uo cx)) HC HO HE HR Hn Hnlen Hpay0 Hinv HJ2 HP).
  + intros a Ha Hw Hr. apply Heff; [exact Ha | exact Hr | unfold ESTACK; lia].
  + exact Hpres.
  + intros a Ha. rewrite Hrq in Ha. exact Ha.
- exact HP.
- intros i Hi. rewrite (Hfill i ltac:(rewrite Hrq; lia)). reflexivity.
Qed.

(* reac_upstream_decode(raw, len, out) at +0x8e8 / +0x8fc / +0x968, raw the copy or NULL, out the upstream
   buffer or NULL. *)
Lemma up_ud_step : forall cx res mode nch ns upb ly S (W : world segs) regs mem md raw out X
    (Q : world segs -> config -> Prop),
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@reac_upstream_decode_cg.dec_reac_upstream_decode_cg) fx') ->
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> rom_view segs (d_W cx) (d_mem cx) ->
  0 <= d_n cx < 67108864 -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  up_inv cx res mode nch ns upb ly S W regs mem md ->
  (raw = 0 \/ raw = res) -> (out = 0 \/ out = upb) ->
  YK11.getr regs 10 = w64 raw -> YK11.getr regs 11 = w64 (up_len cx) -> YK11.getr regs 12 = w64 out ->
  YK11.getr regs 1 = Z_to_bv 64 (decodeb_text + X) -> 0 <= X < 4096 -> X mod 2 = 0 ->
  (forall regs2 mem2 md2, up_inv cx res mode nch ns upb ly S W regs2 mem2 md2 -> aregs_preserved regs regs2 ->
     YK11.getr regs2 10 = w64 (if reac_upstream_decode_c.up_ok raw out (up_len cx) (d_body cx) then 12 else -1) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx) ->
        ~ LeafCgKit.in_wr (if reac_upstream_decode_c.up_ok raw out (up_len cx) (d_body cx)
                           then [(out, out + 36 * reac_upstream_decode_c.up_nch (up_len cx))] else []) a ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
     (reac_upstream_decode_c.up_ok raw out (up_len cx) (d_body cx) = true ->
        garr8 segs (mrestrict (w_H W) mem2) out
          (map (fun b : byte => bv_unsigned b)
             (reac_decode_c.braid_out (d_body cx) (reac_upstream_decode_c.up_nch (up_len cx)) 12))) ->
     SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (decodeb_text + X)) mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (decodeb_sigma DB_reac_upstream_decode)) mem (YK11.seg_rom segs)) md) Q.
Proof.
intros cx res mode nch ns upb ly S W regs mem md raw out X Q HLEAF HC HO HE HR Hn Hnlen Hpay0 Hinv Hraw Hout
  R10 R11 R12 Rra HX HX2 HK.
destruct (up_inv_blocks cx res mode nch ns upb ly S W regs mem md Hn Hpay0 Hinv)
  as (Hin & Hnin & Hres_in & Hdres & _ & Huo & Hc).
pose proof Hinv as (Hcore & _ & Hres & Hupb & _ & _ & Hmem & _).
pose proof Hmem as (_ & _ & _ & Hgarr & _).
pose proof Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Ho16 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp1al; [|lia]. apply Z.mod_divide in Hsp0al; [|lia].
  destruct Hsp1al as [q1 Hq1]. destruct Hsp0al as [q0 Hq0]. exists (2 * q1 - q0). lia. }
pose proof (up_req_uo cx ltac:(lia)) as Hrq.
unfold zdisjoint, block_rng in Hdres. cbn [fst snd] in Hdres. rewrite Hrq in Hdres.
destruct (al_blocks _ _ LAWS ly S W mem md res _ HAR Hres_in) as (_ & Hr4096 & Hrc & _).
assert (Hlen : 0 <= up_len cx < 67108864) by (unfold up_len, dec_b_len; lia).
pose proof (req_size_pos (up_len cx) ltac:(lia)) as [Hrq1 Hrql].
assert (Hnch : 36 * reac_upstream_decode_c.up_nch (up_len cx) <= up_uo cx).
{ rewrite (up_nch_result (up_len cx) ltac:(unfold UP_NMAX; lia)). unfold up_uo, up_r, dec_b_uolen.
  destruct (Z.ltb_spec 0 (upstream_result (up_len cx))); lia. }
eapply SRr_bind.
{ apply (dec_leafb_upstream_decode B LAWS HC HLEAF W regs mem DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
    (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S md dec_ev_96c (d_sp1 cx - d_sp0 cx) raw
    (up_len cx) out (up_uo cx) (d_body cx) HJ).
  - rewrite Hsp. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK. lia.
  - rewrite Rra. change (decodeb_text + X) with (@pa_val _ decodeb_listing PI_decodeb A_TEXT + X).
    apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | exact HX2].
  - exact Hgp.
  - exact Htp.
  - exact R10.
  - exact R11.
  - exact R12.
  - lia.
  - intros Hr. destruct Hraw as [-> | ->]; [contradiction|].
    split; [exact Hres_in|]. split; [exact (up_body_len cx Hnlen) | exact Hgarr].
  - intros Ho. destruct Hout as [-> | ->]; [contradiction|].
    split; [exact Hin|]. split; [exact Hnch|]. split.
    + destruct Hraw as [-> | ->]; lia.
    + intros a Ha. right. right. left. exists upb, (up_uo cx). split; [exact Hin|]. split; [exact Hnin|].
      rewrite Hrq. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & HP & H10' & Heff & Hpres & HXm).
rewrite Hc2, Rra. apply HK.
- apply (up_inv_call cx res mode nch ns upb ly S W regs mem md regs2 mem2 md2
    (LeafCgKit.in_wr (if reac_upstream_decode_c.up_ok raw out (up_len cx) (d_body cx)
                      then [(out, out + 36 * reac_upstream_decode_c.up_nch (up_len cx))] else []))
    HC HO HE HR Hn Hnlen Hpay0 Hinv HJ2 HP).
  + intros a Ha Hw Hr. apply Heff; [exact Ha | rewrite Hsp; unfold ESTACK; lia | exact Hr].
  + exact Hpres.
  + intros a Ha. destruct (reac_upstream_decode_c.up_ok raw out (up_len cx) (d_body cx)) eqn:Hok;
      [|apply Exists_nil in Ha; destruct Ha].
    apply Exists_cons in Ha as [Ha | Ha]; [cbn [fst snd] in Ha | apply Exists_nil in Ha; destruct Ha].
    assert (Ho0 : out <> 0).
    { intros ->.
      assert (F : reac_upstream_decode_c.up_ok raw 0 (up_len cx) (d_body cx) = false)
        by (unfold reac_upstream_decode_c.up_ok; destruct (negb (raw =? 0)); reflexivity).
      congruence. }
    destruct Hout as [-> | ->]; [contradiction|]. lia.
- exact HP.
- exact H10'.
- intros a Ha Hw Hr. apply Heff; [exact Ha | rewrite Hsp; unfold ESTACK; lia | exact Hr].
- exact HXm.
Qed.
End d.
