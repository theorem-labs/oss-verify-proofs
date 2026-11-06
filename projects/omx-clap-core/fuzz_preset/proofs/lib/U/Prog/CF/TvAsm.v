(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1050 of its 1065 lines of code are new or changed and 32 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/tx_put.v, with its module paths and module names changed; 14 of its 33 lines of code are new or changed and 1046 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/tx_value.v; 1452 of its 1476 lines of code are new or changed and 9 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct WriterSpec WriterValue TvSpec TvPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger GIInit strlen_c TvSeg TvSegL.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import tx_put_c TxRet TxGlue TxCompose TxTree TsHelp tx_line_c tx_string_c tx_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tv_geq : forall R1 R : bvmap 5 word, (forall r : reg, is_x0 r = false -> reg_get R1 r = reg_get R r) ->
  forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 k = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R k.
Proof.
  intros R1 R H k. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr. destruct (bv_eqb k 0) eqn:E; [reflexivity|]. apply H. exact E.
Qed.

Ltac rpx RP := lazymatch goal with |- OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr _ ?k = _ =>
  let kz := eval vm_compute in (bv_unsigned k) in
  etransitivity; [exact (RP kz ltac:(unfold callee_saved; lia)) |] end.

Lemma tv_lr_p : forall R R1 gp tp S t v d pretty i, tv_lr R gp tp S t v d pretty i -> regs_preserved R R1 ->
  tv_lr R1 gp tp S t v d pretty i.
Proof.
  intros R R1 gp tp S t v d pretty i H RP. unfold tv_lr, tv_lr0 in *. decompose [and] H.
  repeat split; rpx RP; assumption.
Qed.

Lemma tv_lr0_p : forall R R1 gp tp S t v d pretty, tv_lr0 R gp tp S t v d pretty -> regs_preserved R R1 ->
  tv_lr0 R1 gp tp S t v d pretty.
Proof.
  intros R R1 gp tp S t v d pretty H RP. unfold tv_lr0 in *. decompose [and] H.
  repeat split; rpx RP; assumption.
Qed.

Lemma tv_lr_g : forall R R1 gp tp S t v d pretty i, tv_lr R gp tp S t v d pretty i ->
  (forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 k = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R k) -> tv_lr R1 gp tp S t v d pretty i.
Proof.
  intros R R1 gp tp S t v d pretty i H G. unfold tv_lr, tv_lr0 in *. decompose [and] H.
  repeat split; rewrite G; assumption.
Qed.

Lemma tv_lr0_g : forall R R1 gp tp S t v d pretty, tv_lr0 R gp tp S t v d pretty ->
  (forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 k = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R k) -> tv_lr0 R1 gp tp S t v d pretty.
Proof.
  intros R R1 gp tp S t v d pretty H G. unfold tv_lr0 in *. decompose [and] H.
  repeat split; rewrite G; assumption.
Qed.

Lemma tv_lr_sp : forall R gp tp S t v d pretty, tv_lr0 R gp tp S t v d pretty -> 0 <= S + -128 < 2 ^ 64 ->
  spZ R = S + -128.
Proof.
  intros R gp tp S t v d pretty (E2 & _) H. unfold spZ. rewrite E2. apply unsigned_lit. exact H.
Qed.

Definition img_chk (a : Z) (l : list Z) : bool :=
  forallb (fun k => Mem.ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat k)) &&
    match OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat k)) with
    | Some b => bv_eqb b (Z_to_bv 8 (nth k l 0))
    | None => false
    end) (seq 0 (length l)).

Lemma tv_img_chk : forall a l, img_chk a l = true -> forall k, (k < length l)%nat ->
  Mem.ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat k)) = true /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (nth k l 0)).
Proof.
  intros a l H k Hk. unfold img_chk in H. rewrite forallb_forall in H.
  assert (Hin : In k (seq 0 (length l))) by (apply in_seq; lia).
  specialize (H k Hin). apply andb_true_iff in H. destruct H as [H1 H2]. split; [exact H1|].
  destruct (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [|discriminate H2].
  f_equal. apply bv_eq. unfold bv_eqb in H2. apply Z.eqb_eq in H2. exact H2.
Qed.

Lemma tv_img_ro : forall a l, img_chk a l = true -> forall i, 0 <= i < Z.of_nat (length l) ->
  Mem.ro_addr rsegs (Z_to_bv 64 (a + i)) = true.
Proof.
  intros a l H i Hi. destruct (tv_img_chk a l H (Z.to_nat i) ltac:(lia)) as [RO _].
  rewrite Z2Nat.id in RO by lia. exact RO.
Qed.

Definition a0q (tv : jv) (p : bool) (d : Z) (i : nat) : list (list Z) := [oc tv] :: prefq tv p d i.

Lemma a0q_succ : forall tv p d i, (i < length (kids tv))%nat -> a0q tv p d (S i) = a0q tv p d i ++ ipcq tv p d i.
Proof. intros tv p d i Hi. unfold a0q. rewrite prefq_succ by exact Hi. reflexivity. Qed.

Lemma a0q_0 : forall tv p d, a0q tv p d 0 = [[oc tv]].
Proof. intros. unfold a0q. rewrite prefq_0. reflexivity. Qed.

Lemma a0q_close : forall tv p d, tag tv = 5 \/ tag tv = 6 ->
  a0q tv p d (length (kids tv)) ++ (if Nat.eqb (length (kids tv)) 0 then [] else wind p d) ++ [[cc tv]] = tvp tv p d.
Proof. intros tv p d Ht. rewrite tvp_total by exact Ht. reflexivity. Qed.

Lemma a0q_le : forall tv p d i, tag tv = 5 \/ tag tv = 6 -> (i <= length (kids tv))%nat ->
  exists rest, tvp tv p d = a0q tv p d i ++ rest.
Proof.
  intros tv p d i Ht Hi. destruct (prefq_le tv p d i Hi) as [rest E].
  exists (rest ++ (if Nat.eqb (length (kids tv)) 0 then [] else wind p d) ++ [[cc tv]]).
  rewrite <- (a0q_close tv p d Ht). unfold a0q. rewrite E. cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma tv_pfxq : forall tv p d i Pc Yp Z0, tag tv = 5 \/ tag tv = 6 -> (i < length (kids tv))%nat ->
  Pc ++ Yp ++ Z0 = a0q tv p d (S i) ->
  Z.of_nat (length (concat (Pc ++ Yp))) <= Z.of_nat (length (concat (wvpieces tv p d))) /\
  exists rest, tvp tv p d = Pc ++ Yp ++ rest.
Proof.
  intros tv p d i Pc Yp Z0 Ht Hi E. destruct (a0q_le tv p d (S i) Ht ltac:(lia)) as [rest ER].
  split.
  - rewrite <- tvp_concat, ER, <- E, !concat_app, !length_app. lia.
  - exists (Z0 ++ rest). rewrite ER, <- E, <- !app_assoc. reflexivity.
Qed.

Lemma tv_depth1 : forall tv, tag tv = 5 \/ tag tv = 6 -> (1 <= depth tv)%nat.
Proof. intros [| | | | | |] H; cbn [tag] in H; cbn [depth]; lia. Qed.

Lemma tag5 : forall tv, tag tv = 5 -> exists items, tv = JArr items.
Proof. intros [| | | | | items |] H; cbn [tag] in H; try lia. exists items. reflexivity. Qed.

Lemma tag6 : forall tv, tag tv = 6 -> exists ms, tv = JObj ms.
Proof. intros [| | | | | | ms] H; cbn [tag] in H; try lia. exists ms. reflexivity. Qed.

Lemma concat_rep_snoc2 : forall n, concat (repeat [32; 32] n) ++ [32; 32] = concat (repeat [32; 32] (S n)).
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [repeat concat] in *. rewrite <- app_assoc. rewrite IH. reflexivity.
Qed.

Lemma wind_len : forall k, 0 <= k -> Z.of_nat (length (map (Z_to_bv 8) (concat (wind true k)))) = 1 + 2 * k.
Proof.
  intros k Hk. unfold wind. rewrite length_map. cbn [concat length app].
  assert (E : forall n, length (concat (repeat [32; 32] n)) = (2 * n)%nat).
  { induction n as [|n IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, IH. cbn [length]. lia. }
  rewrite E. lia.
Qed.

Lemma pj_node_hdr : forall segs m lb p t D, pj_node segs m lb p t D ->
  NoDup D /\ pj_apart D p /\ exists num str kids keys n cap, pj_hdr segs m p (tag t) num str kids keys n cap.
Proof.
  intros segs m lb p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (H1 & H2 & num & str & kp & yp & n & cap & Hh & _);
    (split; [exact H1|]); (split; [exact H2|]); exists num, str, kp, yp, n, cap; exact Hh.
Qed.

Lemma tv_cb : forall m a n junk, rw_cells rsegs m a [CB n junk] -> bytes_at rsegs m a junk /\ length junk = n.
Proof.
  intros m a n junk [[Hwf Hb] _]. cbn in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. split; [exact Hb | exact Hl].
Qed.

Lemma tvk_eq : forall tv, TV_K tv = 128 * Z.of_nat (depth tv) + 240 + TX_STACK.
Proof. intros. unfold TV_K, TV_F, TS_STACK. lia. Qed.

Lemma txs_val : TX_STACK = 8288.
Proof. reflexivity. Qed.

Lemma tv_f10 : forall m A (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) d jf,
  rw_cells rsegs m A (tv_frame1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d jf) ->
  rw_cells rsegs m A (tv_frame0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d (le8 (Z_to_bv 64 0x102aa)) jf).
Proof.
  intros m A ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d jf [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf tv_frame0 tv_frame1] in Hwf |- *. rewrite length_le8. tauto.
  - exact Hb.
  - exact Hw.
Qed.

Section G.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.
Hypothesis AX : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YL01.AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Variable F : ResForm.
#[local] Set Default Proof Using "All".

Lemma tv_imgs : forall m a l, ro_agree (ms_segs B) m -> img_chk a l = true -> mbytes B m a (map (Z_to_bv 8) l).
Proof.
  intros m a l RA H i Hi. rewrite length_map in Hi.
  destruct (tv_img_chk a l H (Z.to_nat i) ltac:(lia)) as [RO E].
  rewrite Z2Nat.id in RO, E by lia. rewrite SEGS in RA |- *.
  rewrite nth_error_map, (nth_error_nth' l 0) by lia. cbn [option_map].
  transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (a + i))); [exact (RA _ RO) | exact E].
Qed.

Lemma tv_img_ok : forall stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 regs1 s n,
  tx_relx B API F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= spZ regs1 - TX_STACK -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= t -> 0 <= s -> s + n <= 2 ^ 40 ->
  (forall i, 0 <= i < n -> Mem.ro_addr rsegs (Z_to_bv 64 (s + i)) = true) ->
  forall i, 0 <= i < n ->
    ~ (t <= s + i < t + 24) /\ ~ (spZ regs1 - TX_STACK <= s + i < spZ regs1) /\ ~ (b1 <= s + i < b1 + cap1) /\
    (len0 + Z.of_nat (length acc) + n + 1 <= cap1 \/ spZ regs1 <= s + i \/
     Mem.ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true \/
     exists a k, In (a, k) (blocks L1 A1) /\ a <> b1 /\ a <= s + i < a + k).
Proof.
  intros stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 regs1 s n R AC1 ACT Hs Hsn RO i Hi.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  destruct R as ((M1 & _) & _ & _ & _ & _ & _ & _ & INV1 & _).
  split; [lia|]. split; [lia|]. split.
  - intros X. destruct (inv_low B API SEGS ERRB AX CTX _ _ _ _ _ _ _ _ _ M1 INV1 X) as [_ NI].
    apply NI. apply (ro_img B SEGS); [lia | exact (RO i Hi)].
  - right. right. left. rewrite SEGS. exact (RO i Hi).
Qed.

Lemma tv_call : forall stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1
    stk1 regs1 pc1 add ks2 rest (Q1 : layout -> astate -> (word -> option byte) -> Prop) (P : config -> Prop),
  tx_start B API F stk L A regs mem md t b0 len0 cap0 txt bnd ns need ->
  tx_relx B API F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  ns = j1 ++ ks2 ++ rest ->
  spZ regs - stk <= spZ regs1 - stk1 -> spZ regs1 <= spZ regs -> spZ regs1 mod 16 = 0 -> 0 <= stk1 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 1) -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 10 = Z_to_bv 64 t ->
  len0 + Z.of_nat (length acc) + Z.of_nat (length add) + 1 <= need ->
  (tx_start B API F stk1 L1 A1 regs1 mem1 md1 t b1 (len0 + Z.of_nat (length acc)) cap1 (txt ++ acc)
     (tx_fold F bnd len0 cap0 j1) ks2 (len0 + Z.of_nat (length acc) + Z.of_nat (length add) + 1) ->
   SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs1 pc1 mem1 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md1)
     (tx_ret B API F stk1 L1 A1 regs1 mem1 md1 t b1 (len0 + Z.of_nat (length acc)) cap1 (txt ++ acc) add ks2
        (tx_fold F bnd len0 cap0 j1) Q1)) ->
  (forall L2 A2 regs2 mem2 md2, regs_preserved regs1 regs2 ->
     tx_rel B API F stk regs t b0 len0 cap0 txt (acc ++ add) (j1 ++ ks2) bnd L A mem md L2 A2 mem2 md2 ->
     (forall a, spZ regs1 <= a < 2 ^ 64 -> ~ (t <= a < t + 24) ->
        mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
        (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 1) mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs1 pc1 mem1 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md1) P.
Proof.
  intros stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1 stk1 regs1 pc1 add ks2 rest Q1 P
    ST R ENS S1 S2 AL HS RET TP R10 HN CALLEE K.
  pose proof (tx_start_facts B API SEGS ERRB AX CTX F _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (M0 & W0 & BD0 & SPK & SPT & WIN & INV0).
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hl0 & _).
  pose proof (tx_start_next B API SEGS ERRB AX CTX F stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1
                b1 cap1 j1 stk1 regs1 ks2 rest (len0 + Z.of_nat (length acc) + Z.of_nat (length add) + 1) ST R ENS S1 S2 AL RET
                TP R10 ltac:(lia)) as ST1.
  pose proof ST1 as ((_ & _ & _ & _ & _ & SPK1 & _) & _).
  eapply (tx_call B API SEGS ERRB AX CTX F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1
            stk1 regs1 pc1 add ks2 Q1 P M0 INV0 SPK SPT WIN R).
  - lia.
  - intros a [X|X]; [left; unfold spZ in *; lia | right; exact X].
  - exact (CALLEE ST1).
  - intros L2 A2 regs2 mem2 md2 RP REL _ KEEP. exact (K L2 A2 regs2 mem2 md2 RP REL KEEP).
Qed.

Lemma tv_run : forall regs2 pc mem2 md2 pc' (Pr : bvmap 5 word -> Prop) (P : config -> Prop),
  m_halted md2 = None -> m_vm_lazy md2 = [] ->
  evt rsegs (tv_out pc' mem2 fp_regs fp_csr Pr) (MS (rmk regs2) fp_regs (Z_to_bv 64 pc) fp_csr None mem2 (seg_rom rsegs)) ->
  (forall R1 R', Pr R' -> (forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 k = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' k) ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst R1 (Z_to_bv 64 pc') mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 pc) mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) P.
Proof.
  intros regs2 pc mem2 md2 pc' Pr P Hh Hl HE K.
  apply (sr_evt B SEGS regs2 (Z_to_bv 64 pc) mem2 md2 _ P Hh Hl HE).
  intros ms' (can & (R' & -> & HP) & EQV).
  destruct (eqv_final _ _ _ _ _ _ _ EQV eq_refl eq_refl) as (EMS & HR).
  rewrite EMS. replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  exact (K (ms_regs ms') R' HP (tv_geq _ _ HR)).
Qed.

Lemma tv_keep : forall lo cs t R1 mem1 mem2, spZ R1 <= lo -> lo + Z.of_nat (cells_size cs) <= t ->
  rw_cells rsegs mem1 lo cs ->
  (forall a, spZ R1 <= a < 2 ^ 64 -> ~ (t <= a < t + 24) ->
     mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
     (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
  rw_cells rsegs mem2 lo cs.
Proof.
  intros lo cs t R1 mem1 mem2 H1 H2 FR KEEP.
  pose proof (rw_cells_bound rsegs mem1 lo cs FR) as HB.
  apply (rw_cells_same mem1); [exact FR|]. intros a Ha.
  rewrite <- SEGS. destruct (KEEP a) as [E Wr]; [lia | lia |].
  split; [exact E | intros Wa; apply Wr; exact Wa].
Qed.

Lemma tv_run_m : forall regs2 pc mem2 md2 pc' lo hi (Pr : bvmap 5 word -> (word -> option byte) -> Prop)
    (P : config -> Prop),
  m_halted md2 = None -> m_vm_lazy md2 = [] ->
  evt rsegs (tv_out_m pc' mem2 fp_regs fp_csr lo hi Pr)
    (MS (rmk regs2) fp_regs (Z_to_bv 64 pc) fp_csr None mem2 (seg_rom rsegs)) ->
  (forall R1 R' m', Pr R' m' -> (forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 k = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' k) -> munch [(lo, hi)] mem2 m' ->
     wmono rsegs mem2 m' ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst R1 (Z_to_bv 64 pc') m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 pc) mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) P.
Proof.
  intros regs2 pc mem2 md2 pc' lo hi Pr P Hh Hl HE K.
  apply (sr_evt B SEGS regs2 (Z_to_bv 64 pc) mem2 md2 _ P Hh Hl HE).
  intros ms' (can & (R' & m' & -> & MU & WM & HP) & EQV).
  destruct (eqv_final _ _ _ _ _ _ _ EQV eq_refl eq_refl) as (EMS & HR).
  rewrite EMS. replace (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  exact (K (ms_regs ms') R' m' HP (tv_geq _ _ HR) MU WM).
Qed.

Lemma tv_ro_munch : forall m m' lo hi, ro_agree (ms_segs B) m -> munch [(lo, hi)] m m' -> 0 <= lo -> hi <= 2 ^ 64 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= lo -> ro_agree (ms_segs B) m'.
Proof.
  intros m m' lo hi RA MU H0 H1 H2 a Ha. rewrite SEGS in RA, Ha |- *.
  destruct (kb_outside_dec [(lo, hi)] (bv_unsigned a)) as [Ho|Ho].
  - unfold mrd. rewrite (MU a Ho). exact (RA a Ha).
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. unfold bv_modulus in Hr. cbn in Hr.
    assert (Hin : lo <= bv_unsigned a < hi).
    { destruct (Z_le_gt_dec lo (bv_unsigned a)) as [Q1|Q1];
        [destruct (Z_lt_ge_dec (bv_unsigned a) hi) as [Q2|Q2]; [lia|] |];
        exfalso; apply Ho; cbn [Frame.outside]; (split; [lia | exact I]). }
    assert (E : ro_addr rsegs (Z_to_bv 64 (bv_unsigned a)) = false) by (apply (ro_false B SEGS); [lia | left; lia]).
    rewrite Z_to_bv_bv_unsigned in E. congruence.
Qed.

Lemma lam_al : forall L A mem md Lam peak cnt fail a k, aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail ->
  In (a, k) Lam -> a mod 16 = 0.
Proof.
  intros L A mem md Lam peak cnt fail a k HM HL Hin. destruct HL as (_ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. specialize (HF _ Hin). cbn [fst snd] in HF.
  destruct (lblock_user B L A mem a k HF) as (q & Hq & Ep).
  pose proof (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ q (k + 16) HM Hq) as H. rewrite Ep in H.
  Z.div_mod_to_equations. lia.
Qed.

End G.

Section TF.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.

Definition tv_for (tv : jv) : Prop :=
  forall L A regs mem md (t v pretty d b0 len0 cap0 : Z) (D : list (Z * Z)) (txt : list byte)
         (bnd : rf_R F) (Lam : list (Z * Z)) (peak cnt fail : Z),
    tx_start B API F (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd (tv_calls tv (negb (pretty =? 0)) d)
      (len0 + Z.of_nat (length (map (Z_to_bv 8) (concat (wvpieces tv (negb (pretty =? 0)) d)))) + 1) ->
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 v -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12 = Z_to_bv 64 pretty -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 13 = Z_to_bv 64 d ->
    - 2 ^ 31 <= pretty < 2 ^ 31 -> 0 <= d -> d + Z.of_nat (depth tv) <= 2 ^ 31 - 1 ->
    ledger B L A mem Lam peak cnt fail ->
    pj_node (ms_segs B) mem (fun a n => In (a, n) Lam) v tv D ->
    (forall b, In b D -> In b Lam) ->
    (spZ regs <= v \/ exists a n, In (a, n) Lam /\ a <= v /\ v + 56 <= a + n) ->
    v + 56 <= 2 ^ 64 -> (v + 56 <= t \/ t + 24 <= v) ->
    (forall a n, In (a, n) Lam -> a - 16 <> b0) ->
    SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 TX_VALUE) mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md)
      (tx_ret B API F (TV_K tv) L A regs mem md t b0 len0 cap0 txt
         (map (Z_to_bv 8) (concat (wvpieces tv (negb (pretty =? 0)) d))) (tv_calls tv (negb (pretty =? 0)) d) bnd
         (fun L' A' mem' => ledger B L' A' mem' Lam peak cnt fail /\
            pj_node (ms_segs B) mem' (fun a n => In (a, n) Lam) v tv D /\
            forall x, pj_foot v D x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x)).

Lemma tv_for_all : (forall tv, tv_for tv) -> tx_value_contract B API F.
Proof.
  intros H. unfold tx_value_contract. intros L A regs mem md t v pretty d b0 len0 cap0 tv. apply H.
Qed.

Lemma tx_ret_tt : forall stk L A regs mem md t b0 len0 cap0 txt add ks bnd
    (Q : layout -> astate -> (word -> option byte) -> Prop) c,
  tx_ret B API F stk L A regs mem md t b0 len0 cap0 txt add ks bnd Q c ->
  tx_ret B API F stk L A regs mem md t b0 len0 cap0 txt add ks bnd (fun _ _ _ => True) c.
Proof.
  intros stk L A regs mem md t b0 len0 cap0 txt add ks bnd Q c (L' & A' & regs' & mem' & md' & E & RP & R & _).
  exists L', A', regs', mem', md'. split; [exact E|]. split; [exact RP|]. split; [exact R | exact I].
Qed.

Lemma tx_start_need : forall stk L A regs mem md t b len cap txt bnd ns n1 n2, n1 = n2 ->
  tx_start B API F stk L A regs mem md t b len cap txt bnd ns n1 ->
  tx_start B API F stk L A regs mem md t b len cap txt bnd ns n2.
Proof. intros stk L A regs mem md t b len cap txt bnd ns n1 n2 -> H. exact H. Qed.

End TF.

Ltac tv_g1 := lazymatch goal with |- OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr ?X ?k = _ => change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr X k) with (reg_get X k) end; simp_regs.

Section KB.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.
Hypothesis AX : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.YL01.AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Variable F : ResForm.
Hypothesis HG : globals_free B API omx_G.
Hypothesis SLK : block_slack_present B API.
Hypothesis TXP : tx_put_contract B API F.
Hypothesis TXL : tx_line_contract B API F.
Hypothesis TXS : tx_string_contract B API F.
Hypothesis STR : strlen_contract.
#[local] Set Default Proof Using "All".

Section Node.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (t v pretty d b0 len0 cap0 : Z) (tv : jv) (D : list (Z * Z)) (txt : list byte) (bnd : rf_R F)
  (Lam : list (Z * Z)) (peak cnt fail : Z).
Local Notation PBo := (negb (pretty =? 0)).
Local Notation WHo := (concat (wvpieces tv (negb (pretty =? 0)) d)).
Local Notation ADDo := (map (Z_to_bv 8) (concat (wvpieces tv (negb (pretty =? 0)) d))).
Local Notation LBo := (fun a n => In (a, n) Lam).
Hypothesis ST : tx_start B API F (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd (tv_calls tv PBo d)
  (len0 + Z.of_nat (length ADDo) + 1).
Hypothesis R11 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 v.
Hypothesis R12 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12 = Z_to_bv 64 pretty.
Hypothesis R13 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 13 = Z_to_bv 64 d.
Hypothesis HPR : - 2 ^ 31 <= pretty < 2 ^ 31.
Hypothesis HD0 : 0 <= d.
Hypothesis HDD : d + Z.of_nat (depth tv) <= 2 ^ 31 - 1.
Hypothesis LED : ledger B L A mem Lam peak cnt fail.
Hypothesis PJ : pj_node (ms_segs B) mem LBo v tv D.
Hypothesis DL : forall b, In b D -> In b Lam.
Hypothesis VP : spZ regs <= v \/ exists a n, In (a, n) Lam /\ a <= v /\ v + 56 <= a + n.
Hypothesis V64 : v + 56 <= 2 ^ 64.
Hypothesis VT : v + 56 <= t \/ t + 24 <= v.
Hypothesis NB : forall a n, In (a, n) Lam -> a - 16 <> b0.
Local Notation QQo := (fun L' A' mem' => ledger B L' A' mem' Lam peak cnt fail /\
  pj_node (ms_segs B) mem' (fun a n => In (a, n) Lam) v tv D /\
  forall x, pj_foot v D x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x).
Local Notation PPo := (tx_ret B API F (TV_K tv) L A regs mem md t b0 len0 cap0 txt ADDo (tv_calls tv PBo d) bnd QQo).

Lemma tv_nums : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling + TV_K tv <= spZ regs /\ spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0 /\
  spZ regs <= t /\ t + 24 <= 2 ^ 64 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 t /\
  aa_MR API L A mem md /\ tx_inv B L A mem b0 len0 cap0 txt /\ 0 <= v.
Proof.
  pose proof ST as ((M & _ & _ & RET & SPal & SPK & SP63 & _) & _ & _ & R10 & SPT & Thi & _ & _ & _ & _ & _ & _ & INV & _).
  destruct (pj_node_hdr _ _ _ _ _ _ PJ) as (_ & _ & num & str & kp & yp & n & cap & Hh).
  destruct Hh as (_ & (_ & (V0 & _)) & _).
  split; [exact SPK|]. split; [exact SP63|]. split; [exact SPal|]. split; [exact SPT|]. split; [exact Thi|].
  split; [exact RET|]. split; [exact R10|]. split; [exact M|]. split; [exact INV | exact V0].
Qed.

Lemma tv_vpos : v + 56 <= spZ regs + -128 \/ spZ regs <= v.
Proof.
  destruct tv_nums as (SPK & _ & _ & _ & _ & _ & _ & M0 & _).
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  assert (K0 : 128 <= TV_K tv) by (rewrite tvk_eq, txs_val; lia).
  destruct VP as [H|(a & n & Hin & H1 & H2)]; [right; exact H|left].
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail a n M0 LED Hin) as (_ & H3 & _). lia.
Qed.

Lemma tv_v8 : 0 < v /\ v mod 8 = 0.
Proof.
  destruct tv_nums as (SPK & _ & _ & _ & _ & _ & _ & M0 & _).
  pose proof (tvk_eq tv). pose proof txs_val. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value.
  destruct (pj_node_hdr _ _ _ _ _ _ PJ) as (_ & _ & num & str & kp & yp & n & cap & Hh).
  destruct Hh as ((H8 & _) & _). split; [|exact H8].
  destruct VP as [Hv|(a & n' & Hin & Ha1 & Ha2)]; [lia|].
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail a n' M0 LED Hin) as (Ha3 & _). lia.
Qed.

Lemma tv_whole : forall acc L2 A2 mem2 md2 b2 cap2 j2,
  tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt acc bnd L A mem md L2 A2 mem2 md2 b2 cap2 j2 ->
  ledger B L2 A2 mem2 Lam peak cnt fail /\ (forall a n, In (a, n) Lam -> a - 16 <> b2) /\
  pj_node (ms_segs B) mem2 LBo v tv D /\ (forall x, pj_foot v D x -> mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem x).
Proof.
  intros acc L2 A2 mem2 md2 b2 cap2 j2 R.
  destruct tv_nums as (SPK & _ & _ & SPT & _ & _ & _ & M0 & INV0 & _).
  assert (K0 : 0 <= TV_K tv) by (rewrite tvk_eq, txs_val; lia).
  destruct (tx_rel_ledger B API F (ts_gst B API SEGS ERRB AX CTX HG) (TV_K tv) regs t b0 len0 cap0 txt acc bnd
              L A mem md L2 A2 mem2 md2 b2 cap2 j2 Lam peak cnt fail R M0 K0 SPK SPT INV0 LED NB) as (LED2 & NB2 & _).
  destruct (tx_rel_node B API F ERRB (TV_K tv) regs t b0 len0 cap0 txt acc bnd L A mem md L2 A2 mem2 md2 b2 cap2 j2
              Lam peak cnt fail v tv D R M0 K0 SPK INV0 LED NB PJ DL VP V64 VT) as (PJ2 & FT2).
  split; [exact LED2|]. split; [exact NB2|]. split; [exact PJ2 | exact FT2].
Qed.

Lemma tv_fin : forall X K L2 A2 regs2 mem2 md2, X = WHo -> K = tv_calls tv PBo d -> regs_preserved regs regs2 ->
  tx_rel B API F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) X) K bnd L A mem md L2 A2 mem2 md2 ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) PPo.
Proof.
  intros X K L2 A2 regs2 mem2 md2 -> -> RP (b2 & cap2 & R).
  apply SR_ret. exists L2, A2, regs2, mem2, md2. split; [reflexivity|]. split; [exact RP|].
  split; [exists b2, cap2; exact R|].
  destruct (tv_whole _ _ _ _ _ _ _ _ R) as (H1 & _ & H3 & H4). split; [exact H1|]. split; [exact H3 | exact H4].
Qed.

Definition tv_saved (R : bvmap 5 word) : Prop :=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 1 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 2 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3 /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 8 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 9 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9 /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 18 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 19 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 20 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20 /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 21 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 22 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 23 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23 /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 24 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 25 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 26 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26 /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 27 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27.

Lemma tv_saved_rp : forall R, tv_saved R -> regs_preserved regs R.
Proof.
  intros R (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) r Hr.
  unfold callee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat destruct Hc as [Hc|Hc]; subst r; assumption.
Qed.

Lemma tv_saved_g : forall R R1, tv_saved R -> (forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 k = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R k) -> tv_saved R1.
Proof.
  intros R R1 (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) G.
  unfold tv_saved. rewrite !G. repeat split; assumption.
Qed.

Lemma tv_sp2 : Z_to_bv 64 (spZ regs) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2.
Proof. unfold spZ. apply Z_to_bv_bv_unsigned. Qed.

Lemma tv_tail_put : forall Pc Y s R1 L1 A1 mem1 md1 b1 cap1,
  tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) (concat Pc)) bnd L A mem md L1 A1 mem1 md1 b1 cap1
    (plen Pc) ->
  Pc ++ [Y] = tvp tv PBo d -> tv_saved R1 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 10 = Z_to_bv 64 t -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 11 = Z_to_bv 64 s ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 12 = Z_to_bv 64 (Z.of_nat (length Y)) ->
  0 <= s < 2 ^ 64 -> s + Z.of_nat (length Y) <= 2 ^ 64 -> mbytes B mem1 s (map (Z_to_bv 8) Y) ->
  (forall i, 0 <= i < Z.of_nat (length Y) ->
     ~ (t <= s + i < t + 24) /\ ~ (spZ R1 - TX_STACK <= s + i < spZ R1) /\ ~ (b1 <= s + i < b1 + cap1) /\
     (len0 + Z.of_nat (length (map (Z_to_bv 8) (concat Pc))) + Z.of_nat (length Y) + 1 <= cap1 \/ spZ R1 <= s + i \/
      Mem.ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true \/
      exists a k, In (a, k) (blocks L1 A1) /\ a <> b1 /\ a <= s + i < a + k)) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst R1 (Z_to_bv 64 TX_PUT) mem1 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md1) PPo.
Proof.
  intros Pc Y s R1 L1 A1 mem1 md1 b1 cap1 R HXY SV G10 G11 G12 Hs Hs2 SRC OK.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & _).
  pose proof SV as (G1 & G2 & _ & G4 & _).
  assert (Sp1 : spZ R1 = spZ regs) by (unfold spZ; rewrite G2; reflexivity).
  assert (K0 : TX_STACK <= TV_K tv) by (rewrite tvk_eq; lia).
  assert (EW : concat Pc ++ Y = WHo).
  { rewrite <- tvp_concat, <- HXY, concat_app. cbn [concat]. rewrite app_nil_r. reflexivity. }
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd _ _
            (map (Z_to_bv 8) (concat Pc)) L1 A1 mem1 md1 b1 cap1 (plen Pc) R1 s (Z.of_nat (length Y)) (map (Z_to_bv 8) Y)
            [] _ ST R).
  - unfold tv_calls. rewrite <- HXY, plen_app. reflexivity.
  - rewrite Sp1. lia.
  - lia.
  - rewrite Sp1. exact SPal.
  - rewrite G1. exact RET.
  - exact G4.
  - exact G10.
  - exact G11.
  - exact G12.
  - exact Hs.
  - lia.
  - exact Hs2.
  - exact SRC.
  - rewrite length_map. reflexivity.
  - exact OK.
  - rewrite <- EW, !length_map, length_app. lia.
  - intros L2 A2 regs2 mem2 md2 RP REL _. rewrite G1.
    apply (tv_fin (concat Pc ++ Y) (plen Pc ++ [Z.of_nat (length Y)]) L2 A2);
      [exact EW | unfold tv_calls; rewrite <- HXY, plen_app; reflexivity
      | eapply kb_preserved_trans; [apply tv_saved_rp; exact SV | exact RP] |].
    rewrite map_app. exact REL.
Qed.

Lemma tv_blk_ok : forall acc L1 A1 mem1 md1 b1 cap1 j1 R1 s k nn,
  tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  In (s, k) Lam -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= spZ R1 - TX_STACK ->
  forall i, 0 <= i < k ->
    ~ (t <= s + i < t + 24) /\ ~ (spZ R1 - TX_STACK <= s + i < spZ R1) /\ ~ (b1 <= s + i < b1 + cap1) /\
    (len0 + Z.of_nat (length acc) + nn + 1 <= cap1 \/ spZ R1 <= s + i \/
     Mem.ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true \/
     exists a k', In (a, k') (blocks L1 A1) /\ a <> b1 /\ a <= s + i < a + k').
Proof.
  intros acc L1 A1 mem1 md1 b1 cap1 j1 R1 s k nn R Hin AC1 i Hi.
  destruct tv_nums as (SPK & _ & _ & SPT & _ & _ & _ & M0 & _).
  pose proof (spZ_range regs) as SPR.
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail s k M0 LED Hin) as (S1 & S2 & S3).
  destruct (tx_rel_lam B API F (TV_K tv) regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1
              Lam peak cnt fail R LED NB) as (HQ & _).
  destruct (HQ s k Hin) as (Hb & Hne).
  pose proof R as ((M1 & _) & _ & _ & _ & _ & _ & _ & INV1 & _).
  assert (K0 : 0 <= TV_K tv) by (rewrite tvk_eq, txs_val; lia).
  split; [lia|]. split; [lia|]. split.
  - intros X. destruct INV1 as (_ & [(C & _)|(Cp & Hb1 & _)]); [lia|].
    destruct (pairwise_in _ _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1) Hb Hb1
                ltac:(intros E; inversion E; congruence)) as [Dj|Dj];
      unfold ranges_disjoint in Dj; cbn [fst snd] in Dj; lia.
  - right. right. right. exists (s - 16), (k + 16). split; [exact Hb|]. split; [exact Hne | lia].
Qed.

Lemma tv_entry : forall (Zp : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  (forall junk, rw_cells rsegs (normalize rsegs mem) (spZ regs + -128) [CB 128 junk] ->
     evt rsegs (fun ms => exists R pc m', ms = MS R fp_regs pc fp_csr None m' (seg_rom rsegs) /\
                   munch [(spZ regs + -128, spZ regs)] (normalize rsegs mem) m' /\
                   wmono rsegs (normalize rsegs mem) m' /\ Zp R pc m')
       (MS (mkR (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (Z_to_bv 64 (spZ regs)) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 5)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 6) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 7) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (Z_to_bv 64 t)
          (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 d) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 14) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 15)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 16) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 17) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 28) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 29) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 30)
          (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 31)) fp_regs (Z_to_bv 64 0x155ac) fp_csr None (normalize rsegs mem) (seg_rom rsegs))) ->
  (forall R pc m' R1 mem1, Zp R pc m' -> (forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 k = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R k) -> mem_rel rsegs mem1 m' ->
     tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt [] bnd L A mem md L A mem1 md b0 cap0 [] ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst R1 pc mem1 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 TX_VALUE) mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros Zp P HE K.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M & INV & _).
  pose proof ST as ((_ & W & BD & _ & _ & _ & _ & SWR & _ & _ & _) & IN & RA & _ & _ & _ & _ & TW & _ & _ & _ & REC &
                    _ & _ & RES & _).
  destruct (tx_start_facts B API SEGS ERRB AX CTX F _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (_ & _ & _ & _ & _ & WIN & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M) as (Hh & Hlz & _).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  assert (KK : 128 <= TV_K tv) by (rewrite tvk_eq, txs_val; lia).
  assert (RAr : ro_agree rsegs mem) by (rewrite <- SEGS; exact RA).
  assert (FRP : forall i, 0 <= i < 128 -> present mem (spZ regs + -128 + i)).
  { intros i Hi. apply (present_of_writable B SEGS); [lia | left; lia | apply SWR; lia]. }
  edestruct (rw_of_present mem (spZ regs + -128) 128) as [j FRJ]; [lia | lia | lia | exact FRP |].
  change (Z.to_nat 128) with 128%nat in FRJ.
  assert (FRN : rw_cells rsegs (normalize rsegs mem) (spZ regs + -128) [CB 128 j]).
  { apply rw_cells_norm; [exact RAr | exact FRJ |]. intros i Hi. cbn in Hi.
    apply (ro_false B SEGS); [lia | left; lia]. }
  eapply (sr_evt_n B SEGS regs _ mem md); [exact Hh | exact Hlz | exact RAr | |].
  { unfold TX_VALUE. rewrite <- tv_sp2, R10, R11, R12, R13. exact (HE j FRN). }
  intros ms' (can & s0 & HQ & HREL & RS & EQV).
  destruct HQ as (R & pc & m' & -> & MU & WM & HZ).
  destruct (final_n _ _ _ _ _ _ _ _ HREL EQV eq_refl eq_refl) as (EMS & HR & MRL & EM).
  rewrite <- EM in RS.
  pose proof (munch_rel rsegs _ mem (normalize rsegs mem) (ms_mem ms') m' (mem_rel_normalize rsegs mem RAr) MRL RS MU)
    as MU'.
  pose proof (wmono_rel rsegs mem (normalize rsegs mem) (ms_mem ms') m' (mem_rel_normalize rsegs mem RAr) MRL RS WM)
    as WM'.
  pose proof (ro_agree_same rsegs mem (ms_mem ms') RAr RS) as RA1.
  assert (R0 : tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt [] bnd L A mem md L A (ms_mem ms') md b0 cap0 []).
  { apply (tx_rel_frame B API SEGS ERRB AX CTX F (TV_K tv) regs t b0 len0 cap0 txt bnd L A mem md (ms_mem ms')
             (spZ regs + -128) (spZ regs)); try assumption.
    - rewrite SEGS. exact RA1.
    - intros a Ha. lia. }
  rewrite EMS. replace (seg_rom rsegs) with (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  exact (K R pc m' (ms_regs ms') (ms_mem ms') HZ (tv_geq _ _ HR) MRL R0).
Qed.

Lemma tv_saved_sp : forall R, tv_saved R -> spZ R = spZ regs.
Proof. intros R (_ & G2 & _). unfold spZ. rewrite G2. reflexivity. Qed.

Lemma st_lit : tv = JNull \/ tv = JFalse \/ tv = JTrue ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 TX_VALUE) mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) PPo.
Proof.
  intros Htv.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  assert (KK : 240 + TX_STACK <= TV_K tv) by (rewrite tvk_eq; lia).
  pose proof txs_val as TXV.
  pose proof ST as (_ & _ & RA & _).
  assert (RAr : ro_agree rsegs mem) by (rewrite <- SEGS; exact RA).
  pose proof tv_vpos as VPS. destruct tv_v8 as (VP0 & V8).
  assert (HC : exists k lit, ((k = 0 /\ lit = 0x102ed /\ Z.of_nat (length WHo) = 4) \/
                             (k = 1 /\ lit = 0x10298 /\ Z.of_nat (length WHo) = 5) \/
                             (k = 2 /\ lit = 0x10349 /\ Z.of_nat (length WHo) = 4)) /\
                   tag tv = k /\ img_chk lit WHo = true).
  { destruct Htv as [E|[E|E]]; rewrite E; cbn [wvpieces concat app tag];
      [exists 0, 0x102ed | exists 1, 0x10298 | exists 2, 0x10349];
      (split; [cbn [length Z.of_nat]; lia|]); (split; [reflexivity | vm_compute; reflexivity]). }
  destruct HC as (k & lit & Hk & Htag & HI).
  destruct (pj_node_hdr _ _ _ _ _ _ PJ) as (_ & _ & num & str & kp & yp & n & cap & Hh).
  destruct Hh as (_ & (_ & TY) & _). rewrite Htag, SEGS in TY.
  apply (tv_entry (fun R pc m' => pc = Z_to_bv 64 0x154b8 /\ tv_saved R /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 t /\
          OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 11 = Z_to_bv 64 lit /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 12 = Z_to_bv 64 (Z.of_nat (length WHo)))).
  - intros junk FRN. eapply evt_mono.
    + eapply ub_seg_lit with (k := k) (lit := lit) (n := Z.of_nat (length WHo)).
      * exact Hk.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact V8.
      * lia.
      * exact VPS.
      * lia.
      * exact FRN.
      * apply bytes_at_normalize; [exact RAr | exact TY].
      * apply mem_inv_normalize.
    + intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & A1 & A2).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split.
      { unfold tv_saved. repeat split; tv_g1; first [reflexivity | exact tv_sp2]. }
      split; [tv_g1; reflexivity|]. split; tv_g1; assumption.
  - intros R pc m' R1 mem1 (-> & SVr & G10 & G11 & G12) G MRL R0.
    pose proof R0 as (_ & _ & _ & _ & _ & _ & _ & _ & RA1 & _).
    pose proof (tv_saved_g R R1 SVr G) as SV1.
    pose proof (tv_saved_sp R1 SV1) as Sp1.
    assert (HXY : [] ++ [WHo] = tvp tv PBo d) by (destruct Htv as [E|[E|E]]; rewrite E; reflexivity).
    apply (tv_tail_put [] WHo lit R1 L A mem1 md b0 cap0 R0 HXY SV1).
    + rewrite G. exact G10.
    + rewrite G. exact G11.
    + rewrite G. exact G12.
    + lia.
    + lia.
    + exact (tv_imgs B API SEGS ERRB AX CTX F mem1 lit WHo RA1 HI).
    + intros i Hi.
      apply (tv_img_ok B API SEGS ERRB AX CTX F (TV_K tv) regs t b0 len0 cap0 txt [] bnd L A mem md L A mem1 md b0 cap0 []
               R1 lit (Z.of_nat (length WHo)) R0); [lia | lia | lia | lia | exact (tv_img_ro lit WHo HI) | exact Hi].
Qed.

Lemma st_num : forall txt0 bits, tv = JNum txt0 bits ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 TX_VALUE) mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) PPo.
Proof.
  intros txt0 bits E.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  assert (KK : 240 + TX_STACK <= TV_K tv) by (rewrite tvk_eq; lia).
  pose proof txs_val as TXV.
  pose proof ST as (_ & _ & RA & _).
  assert (RAr : ro_agree rsegs mem) by (rewrite <- SEGS; exact RA).
  pose proof tv_vpos as VPS. destruct tv_v8 as (VP0 & V8).
  pose proof PJ as PJ'. rewrite E in PJ'. cbn [pj_node tag] in PJ'.
  destruct PJ' as (_ & _ & num & str & kp & yp & n & cap & Hh & _ & _ & _ & _ & _ & k & CS & ED).
  destruct Hh as (_ & (_ & TY) & _ & (_ & SV0) & _). rewrite SEGS in TY, SV0.
  pose proof CS as (Hin & Hk & HF & HB). rewrite map_app, SEGS in HB.
  pose proof (proj1 (proj1 (bytes_at_app _ _ _ _ _) HB)) as HBr.
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail str k M0 LED Hin) as (S1 & S2 & S3).
  pose proof LED as (_ & _ & _ & _ & _ & HLF). rewrite Forall_forall in HLF.
  destruct (HLF (str, k) Hin) as (_ & HBK & _). cbn [fst snd] in HBK.
  pose proof (Z.mod_pos_bound (- (str + Z.of_nat (length txt0) + 1)) 8 ltac:(lia)) as EM.
  assert (SLp : forall i, 0 <= i < (- (str + Z.of_nat (length txt0) + 1)) mod 8 ->
            present mem (str + Z.of_nat (length txt0) + 1 + i)).
  { intros i Hi. destruct (Z_lt_ge_dec (str + Z.of_nat (length txt0) + 1 + i) (str + k)) as [Hlt|Hge].
    - replace (str + Z.of_nat (length txt0) + 1 + i) with (str + (Z.of_nat (length txt0) + 1 + i)) by lia.
      apply (ledger_block_present B API L A mem md Lam peak cnt fail str k); [exact M0 | exact LED | exact Hin | lia].
    - apply (SLK L A mem md (str - 16) (k + 16) _ M0 HBK). Z.div_mod_to_equations. lia. }
  edestruct (rw_of_present mem (str + Z.of_nat (length txt0) + 1) ((- (str + Z.of_nat (length txt0) + 1)) mod 8))
    as [sl FSL]; [lia | lia | lia | exact SLp |].
  destruct (tv_cb _ _ _ _ FSL) as (BSL & LSL).
  assert (HBN : bytes_at rsegs (normalize rsegs mem) str (map (Z_to_bv 8) txt0 ++ Z_to_bv 8 0 :: sl)).
  { apply bytes_at_normalize; [exact RAr|].
    change (Z_to_bv 8 0 :: sl) with ([Z_to_bv 8 0] ++ sl). rewrite app_assoc. apply bytes_at_app. split.
    - exact HB.
    - rewrite length_app, length_map. cbn [length].
      replace (str + Z.of_nat (length txt0 + 1)) with (str + Z.of_nat (length txt0) + 1) by lia. exact BSL. }
  apply (tv_entry (fun R pc m' => pc = Z_to_bv 64 0x154b8 /\ tv_saved R /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 t /\
          OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 11 = Z_to_bv 64 str /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 12 = Z_to_bv 64 (Z.of_nat (length (map (Z_to_bv 8) txt0))))).
  - intros junk FRN. eapply evt_mono.
    + eapply ub_seg_num with (s := str) (cs := map (Z_to_bv 8) txt0) (sl := sl).
      * exact STR.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact V8.
      * lia.
      * exact VPS.
      * lia.
      * lia.
      * exact FRN.
      * apply bytes_at_normalize; [exact RAr | exact TY].
      * apply bytes_at_normalize; [exact RAr | exact SV0].
      * exact HBN.
      * intros Hin0. apply in_map_iff in Hin0. destruct Hin0 as (c & Ec & Hc). rewrite Forall_forall in HF.
        specialize (HF c Hc). apply (f_equal bv_unsigned) in Ec. rewrite !Z_to_bv_unsigned in Ec.
        unfold bv_wrap, bv_modulus in Ec. change (2 ^ Z.of_N 8) with 256 in Ec.
        rewrite !Z.mod_small in Ec by lia. lia.
      * rewrite length_map, LSL, Z2Nat.id by lia. lia.
      * rewrite length_map, LSL, Z2Nat.id by lia. lia.
      * apply mem_inv_normalize.
    + intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & A1 & A2).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split.
      { unfold tv_saved. repeat split; tv_g1; first [reflexivity | exact tv_sp2]. }
      split; [tv_g1; reflexivity|]. split; tv_g1; assumption.
  - intros R pc m' R1 mem1 (-> & SVr & G10 & G11 & G12) G MRL R0.
    destruct (tv_whole _ _ _ _ _ _ _ _ R0) as (_ & _ & _ & FT1).
    pose proof (tv_saved_g R R1 SVr G) as SV1.
    pose proof (tv_saved_sp R1 SV1) as Sp1.
    apply (tv_tail_put [] txt0 str R1 L A mem1 md b0 cap0 R0).
    + rewrite E. reflexivity.
    + exact SV1.
    + rewrite G. exact G10.
    + rewrite G. exact G11.
    + rewrite G, G12, length_map. reflexivity.
    + lia.
    + lia.
    + apply (mbytes_same B mem mem1).
      * exact (bytes_at_mbytes B SEGS _ _ _ HBr).
      * intros i Hi. rewrite length_map in Hi. apply FT1. right. exists (str, k).
        split; [rewrite ED; left; reflexivity | unfold pj_holds; cbn [fst snd]; lia].
    + intros i Hi.
      apply (tv_blk_ok (map (Z_to_bv 8) []) L A mem1 md b0 cap0 [] R1 str k _ R0 Hin); [rewrite Sp1; lia | lia].
Qed.

Lemma st_str : forall s0, tv = JStr s0 ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 TX_VALUE) mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) PPo.
Proof.
  intros s0 E.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  assert (KK : 240 + TX_STACK <= TV_K tv) by (rewrite tvk_eq; lia).
  pose proof txs_val as TXV.
  pose proof ST as (_ & _ & RA & _).
  assert (RAr : ro_agree rsegs mem) by (rewrite <- SEGS; exact RA).
  pose proof tv_vpos as VPS. destruct tv_v8 as (VP0 & V8).
  pose proof PJ as PJ'. rewrite E in PJ'. cbn [pj_node tag] in PJ'.
  destruct PJ' as (_ & _ & num & str & kp & yp & n & cap & Hh & _ & _ & _ & _ & k & CS & ED).
  destruct Hh as (_ & (_ & TY) & _ & (SR0 & SV0) & _). rewrite SEGS in TY, SV0.
  apply (tv_entry (fun R pc m' => pc = Z_to_bv 64 0x158d4 /\ tv_saved R /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 t /\
          OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 11 = Z_to_bv 64 str)).
  - intros junk FRN. eapply evt_mono.
    + eapply ub_seg_str with (s := str).
      * lia.
      * lia.
      * lia.
      * lia.
      * exact V8.
      * lia.
      * exact VPS.
      * lia.
      * lia.
      * exact FRN.
      * apply bytes_at_normalize; [exact RAr | exact TY].
      * apply bytes_at_normalize; [exact RAr | exact SV0].
      * apply mem_inv_normalize.
    + intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & A1 & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split.
      { unfold tv_saved. repeat split; tv_g1; first [reflexivity | exact tv_sp2]. }
      split; [tv_g1; reflexivity | tv_g1; assumption].
  - intros R pc m' R1 mem1 (-> & SVr & G10 & G11) G MRL R0.
    destruct (tv_whole _ _ _ _ _ _ _ _ R0) as (LED1 & NB1 & _ & FT1).
    pose proof (tv_saved_g R R1 SVr G) as SV1. pose proof SV1 as (G1 & _ & _ & G4 & _).
    pose proof (tv_saved_sp R1 SV1) as Sp1.
    assert (CS1 : pj_cstr (ms_segs B) mem1 LBo str k s0).
    { apply (pj_cstr_mframe (ms_segs B) mem mem1); [exact CS|]. intros x Hx. apply FT1. right. exists (str, k).
      split; [rewrite ED; left; reflexivity | exact Hx]. }
    eapply (tv_call B API SEGS ERRB AX CTX F (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd _ _ [] L A mem1 md b0 cap0 []
              TS_STACK R1 (Z_to_bv 64 TX_STRING) (map (Z_to_bv 8) (wstr s0)) (plen (strp s0)) [] _ _ ST R0).
    + unfold tv_calls. rewrite E. cbn [tvp]. rewrite app_nil_r. reflexivity.
    + rewrite Sp1, tvk_eq. unfold TS_STACK. lia.
    + lia.
    + rewrite Sp1. exact SPal.
    + unfold TS_STACK. lia.
    + rewrite G1. exact RET.
    + exact G4.
    + rewrite G. exact G10.
    + rewrite E. cbn [wvpieces length Z.of_nat]. unfold wstr. lia.
    + intros ST1. exact (TXS L A R1 mem1 md t str k b0 _ cap0 s0 _ _ Lam peak cnt fail ST1
                           (eq_trans (G _) G11) LED1 CS1 NB1).
    + intros L2 A2 regs2 mem2 md2 RP REL _. rewrite G1.
      apply (tv_fin (wstr s0) (plen (strp s0)) L2 A2); [rewrite E; reflexivity | unfold tv_calls; rewrite E; reflexivity | |
        exact REL].
      eapply kb_preserved_trans; [apply tv_saved_rp; exact SV1 | exact RP].
Qed.

Section Coll.
Hypothesis IHC : forall tv', (depth tv' < depth tv)%nat -> tv_for B API F tv'.
Hypothesis CT : tag tv = 5 \/ tag tv = 6.

Definition tv_frm (jf : list byte) : list cell :=
  tv_frame1 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19)
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24)
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) d jf.

Definition tv_frm0 (x16 jf : list byte) : list cell :=
  tv_frame0 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19)
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24)
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) d x16 jf.

Definition tv_at (pc : Z) (i : nat) (Pc : list (list Z)) : Prop :=
  forall regs2 mem2 md2 L2 A2 b2 cap2 jf,
    tv_lr regs2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty (Z.of_nat i) ->
    tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) (concat Pc)) bnd L A mem md L2 A2 mem2 md2
      b2 cap2 (plen Pc) ->
    rw_cells rsegs mem2 (spZ regs + -128) (tv_frm jf) ->
    SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 pc) mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) PPo.

Lemma tv_cf : forall acc L2 A2 mem2 md2 b2 cap2 j2,
  tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt acc bnd L A mem md L2 A2 mem2 md2 b2 cap2 j2 ->
  exists kp yp, coll_facts (ms_segs B) mem2 LBo v tv D kp yp (Z.of_nat (length (kids tv))) /\
    ledger B L2 A2 mem2 Lam peak cnt fail /\ (forall a n, In (a, n) Lam -> a - 16 <> b2) /\
    aa_MR API L2 A2 mem2 md2 /\ ro_agree (ms_segs B) mem2 /\ m_halted md2 = None /\ m_vm_lazy md2 = [].
Proof.
  intros acc L2 A2 mem2 md2 b2 cap2 j2 R.
  destruct (tv_whole _ _ _ _ _ _ _ _ R) as (LED2 & NB2 & PJ2 & _).
  destruct (pj_coll (ms_segs B) mem2 LBo v tv D PJ2 CT) as (kp & yp & n & CF).
  pose proof CF as (_ & _ & _ & _ & En & _). subst n.
  pose proof R as ((M2 & _) & _ & _ & _ & _ & _ & _ & _ & RA2 & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh & Hlz & _).
  exists kp, yp. split; [exact CF|]. split; [exact LED2|]. split; [exact NB2|]. split; [exact M2|].
  split; [exact RA2|]. split; [exact Hh | exact Hlz].
Qed.

Lemma tv_nk : Z.of_nat (length (kids tv)) < 2 ^ 42.
Proof.
  destruct tv_nums as (_ & _ & _ & _ & _ & _ & _ & M0 & _).
  destruct (pj_coll (ms_segs B) mem LBo v tv D PJ CT) as (kp & yp & n & CF).
  destruct CF as (_ & _ & _ & _ & En & Hcap & _).
  destruct (Z_lt_ge_dec 0 n) as [Hn|Hn]; [|lia].
  destruct (Hcap Hn) as (cap & Hc & Hl & _).
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail kp (56 * cap) M0 LED Hl) as (H1 & _ & H3). lia.
Qed.

Lemma tv_rngi : forall z, 0 <= z < 2 ^ 54 -> tv_rng (spZ regs) t v d pretty z.
Proof.
  intros z Hz. destruct tv_nums as (SPK & SP63 & _ & SPT & Thi & _ & _ & _ & _ & V0).
  pose proof (spZ_range regs). pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value. pose proof (tv_depth1 tv CT).
  pose proof (tvk_eq tv). pose proof txs_val.
  unfold tv_rng. repeat split; lia.
Qed.

Lemma tv_restored_saved : forall R, tv_restored R (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4)
  (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20)
  (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25)
  (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) (spZ regs) -> tv_saved R.
Proof.
  intros R (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  unfold tv_saved. rewrite E2, tv_sp2. repeat split; assumption.
Qed.

Lemma pq_app : forall (Pc Yp : list (list Z)) Y, concat Yp = Y ->
  map (Z_to_bv 8) (concat (Pc ++ Yp)) = map (Z_to_bv 8) (concat Pc) ++ map (Z_to_bv 8) Y /\
  plen (Pc ++ Yp) = plen Pc ++ plen Yp.
Proof. intros Pc Yp Y E. rewrite concat_app, E, map_app, plen_app. split; reflexivity. Qed.

Lemma st_mv : forall i Pc pc pc',
  (forall R2 m, tv_lr R2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty (Z.of_nat i) ->
     evt rsegs (tv_out pc' m fp_regs fp_csr
                  (fun R' => tv_lr R' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty (Z.of_nat i)))
       (MS (rmk R2) fp_regs (Z_to_bv 64 pc) fp_csr None m (seg_rom rsegs))) ->
  tv_at pc' i Pc -> tv_at pc i Pc.
Proof.
  intros i Pc pc pc' SEG K regs2 mem2 md2 L2 A2 b2 cap2 jf LR R2 FR.
  pose proof R2 as ((M2 & _) & _). destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh & Hlz & _).
  apply (tv_run B API SEGS ERRB AX CTX F regs2 pc mem2 md2 pc' _ PPo Hh Hlz (SEG regs2 mem2 LR)).
  intros R1 R' LR' G. exact (K R1 mem2 md2 L2 A2 b2 cap2 jf (tv_lr_g _ _ _ _ _ _ _ _ _ _ LR' G) R2 FR).
Qed.

Lemma st_put : forall i Pc Y pc ret s nY,
  (i < length (kids tv))%nat -> (exists Z0, Pc ++ [Y] ++ Z0 = a0q tv PBo d (S i)) ->
  img_chk s Y = true -> 0 <= s -> s + Z.of_nat (length Y) <= 2 ^ 40 -> Z.of_nat (length Y) = nY ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (Z_to_bv 64 ret) ->
  (forall R2 m jf, tv_lr R2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty (Z.of_nat i) ->
     rw_cells rsegs m (spZ regs + -128) (tv_frm jf) ->
     evt rsegs (tv_out 0x154b8 m fp_regs fp_csr
                  (fun R' => tv_lr R' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty (Z.of_nat i) /\
                     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 1 = Z_to_bv 64 ret /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 10 = Z_to_bv 64 t /\
                     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 11 = Z_to_bv 64 s /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 12 = Z_to_bv 64 nY))
       (MS (rmk R2) fp_regs (Z_to_bv 64 pc) fp_csr None m (seg_rom rsegs))) ->
  tv_at ret i (Pc ++ [Y]) -> tv_at pc i Pc.
Proof.
  intros i Pc Y pc ret s nY Hi (Z0 & HXY) HI Hs Hs2 HnY RETo SEG K regs2 mem2 md2 L2 A2 b2 cap2 jf LR R2 FR.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof (tvk_eq tv) as TK. pose proof txs_val as TXV. pose proof (tv_depth1 tv CT) as DP.
  pose proof R2 as ((M2 & _) & _ & _ & _ & _ & _ & _ & _ & RA2 & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh & Hlz & _).
  destruct (tv_pfxq tv PBo d i Pc [Y] Z0 CT Hi HXY) as (HB & rest & ER).
  apply (tv_run B API SEGS ERRB AX CTX F regs2 pc mem2 md2 0x154b8 _ PPo Hh Hlz (SEG regs2 mem2 jf LR FR)).
  intros R1 R' (LR' & G1 & G10 & G11 & G12) G.
  pose proof (tv_lr_g _ _ _ _ _ _ _ _ _ _ LR' G) as LR1.
  pose proof (tv_lr_sp R1 _ _ _ _ _ _ _ (proj1 LR1) ltac:(lia)) as S1.
  pose proof LR' as ((_ & _ & E4 & _) & _).
  change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
  eapply (tx_put_call B API SEGS ERRB AX CTX F TXP (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd _ _
            (map (Z_to_bv 8) (concat Pc)) L2 A2 mem2 md2 b2 cap2 (plen Pc) R1 s (Z.of_nat (length Y))
            (map (Z_to_bv 8) Y) (plen rest) _ ST R2).
  - unfold tv_calls. rewrite ER, !plen_app. reflexivity.
  - rewrite S1. lia.
  - rewrite S1. lia.
  - rewrite S1. Z.div_mod_to_equations. lia.
  - rewrite G, G1. exact RETo.
  - rewrite G. exact E4.
  - rewrite G. exact G10.
  - rewrite G. exact G11.
  - rewrite G, G12, HnY. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact (tv_imgs B API SEGS ERRB AX CTX F mem2 s Y RA2 HI).
  - rewrite length_map. reflexivity.
  - intros k Hk.
    apply (tv_img_ok B API SEGS ERRB AX CTX F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) (concat Pc)) bnd
             L A mem md L2 A2 mem2 md2 b2 cap2 (plen Pc) R1 s (Z.of_nat (length Y)) R2);
      [rewrite S1; lia | lia | lia | lia | exact (tv_img_ro s Y HI) | exact Hk].
  - rewrite !length_map. rewrite concat_app, length_app in HB. cbn [concat] in HB. rewrite app_nil_r in HB. lia.
  - intros L3 A3 regs3 mem3 md3 RP (b3 & cap3 & R3) KEEP.
    rewrite G, G1. apply (K regs3 mem3 md3 L3 A3 b3 cap3 jf).
    + exact (tv_lr_p _ _ _ _ _ _ _ _ _ _ LR1 RP).
    + destruct (pq_app Pc [Y] Y ltac:(cbn [concat]; apply app_nil_r)) as [E1 E2]. rewrite E1, E2. exact R3.
    + apply (tv_keep B API SEGS ERRB AX CTX F (spZ regs + -128) (tv_frm jf) t R1 mem2 mem3);
        [lia | unfold tv_frm, tv_frame1; cbn [cells_size csize]; lia | exact FR | exact KEEP].
Qed.

Lemma st_sub : forall i Pc Yp Y pc pcC ret stk1 (Pr : (word -> option byte) -> bvmap 5 word -> Prop),
  (i < length (kids tv))%nat -> (exists Z0, Pc ++ Yp ++ Z0 = a0q tv PBo d (S i)) -> concat Yp = Y ->
  0 <= stk1 -> 128 + stk1 <= TV_K tv -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (Z_to_bv 64 ret) ->
  (forall R2 L2 A2 mem2 md2 b2 cap2,
     tv_lr R2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty (Z.of_nat i) ->
     tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) (concat Pc)) bnd L A mem md L2 A2 mem2 md2
       b2 cap2 (plen Pc) ->
     evt rsegs (tv_out pcC mem2 fp_regs fp_csr
                  (fun R' => tv_lr R' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty (Z.of_nat i) /\
                     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 1 = Z_to_bv 64 ret /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 10 = Z_to_bv 64 t /\ Pr mem2 R'))
       (MS (rmk R2) fp_regs (Z_to_bv 64 pc) fp_csr None mem2 (seg_rom rsegs))) ->
  (forall R1 R' L2 A2 mem2 md2 b2 cap2, Pr mem2 R' -> (forall k, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 k = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' k) ->
     spZ R1 = spZ regs + -128 ->
     tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) (concat Pc)) bnd L A mem md L2 A2 mem2 md2
       b2 cap2 (plen Pc) ->
     tx_start B API F stk1 L2 A2 R1 mem2 md2 t b2 (len0 + Z.of_nat (length (map (Z_to_bv 8) (concat Pc)))) cap2
       (txt ++ map (Z_to_bv 8) (concat Pc)) (tx_fold F bnd len0 cap0 (plen Pc)) (plen Yp)
       (len0 + Z.of_nat (length (map (Z_to_bv 8) (concat Pc))) + Z.of_nat (length (map (Z_to_bv 8) Y)) + 1) ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst R1 (Z_to_bv 64 pcC) mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2)
       (tx_ret B API F stk1 L2 A2 R1 mem2 md2 t b2 (len0 + Z.of_nat (length (map (Z_to_bv 8) (concat Pc)))) cap2
          (txt ++ map (Z_to_bv 8) (concat Pc)) (map (Z_to_bv 8) Y) (plen Yp) (tx_fold F bnd len0 cap0 (plen Pc))
          (fun _ _ _ => True))) ->
  tv_at ret i (Pc ++ Yp) -> tv_at pc i Pc.
Proof.
  intros i Pc Yp Y pc pcC ret stk1 Pr Hi (Z0 & HXY) EY Hk0 Hk1 RETo SEG CAL K regs2 mem2 md2 L2 A2 b2 cap2 jf LR R2 FR.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof (tvk_eq tv) as TK. pose proof txs_val as TXV. pose proof (tv_depth1 tv CT) as DP.
  pose proof R2 as ((M2 & _) & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh & Hlz & _).
  destruct (tv_pfxq tv PBo d i Pc Yp Z0 CT Hi HXY) as (HB & rest & ER).
  apply (tv_run B API SEGS ERRB AX CTX F regs2 pc mem2 md2 pcC _ PPo Hh Hlz (SEG regs2 L2 A2 mem2 md2 b2 cap2 LR R2)).
  intros R1 R' (LR' & G1 & G10 & HPr) G.
  pose proof (tv_lr_g _ _ _ _ _ _ _ _ _ _ LR' G) as LR1.
  pose proof (tv_lr_sp R1 _ _ _ _ _ _ _ (proj1 LR1) ltac:(lia)) as S1.
  pose proof LR' as ((_ & _ & E4 & _) & _).
  eapply (tv_call B API SEGS ERRB AX CTX F (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd _ _
            (map (Z_to_bv 8) (concat Pc)) L2 A2 mem2 md2 b2 cap2 (plen Pc) stk1 R1 (Z_to_bv 64 pcC) (map (Z_to_bv 8) Y)
            (plen Yp) (plen rest) (fun _ _ _ => True) _ ST R2).
  - unfold tv_calls. rewrite ER, !plen_app. reflexivity.
  - rewrite S1. lia.
  - rewrite S1. lia.
  - rewrite S1. Z.div_mod_to_equations. lia.
  - exact Hk0.
  - rewrite G, G1. exact RETo.
  - rewrite G. exact E4.
  - rewrite G. exact G10.
  - rewrite !length_map. rewrite <- EY. rewrite concat_app, length_app in HB. lia.
  - intros ST1. exact (CAL R1 R' L2 A2 mem2 md2 b2 cap2 HPr G S1 R2 ST1).
  - intros L3 A3 regs3 mem3 md3 RP (b3 & cap3 & R3) KEEP.
    rewrite G, G1. apply (K regs3 mem3 md3 L3 A3 b3 cap3 jf).
    + exact (tv_lr_p _ _ _ _ _ _ _ _ _ _ LR1 RP).
    + destruct (pq_app Pc Yp Y EY) as [E1 E2]. rewrite E1, E2. exact R3.
    + apply (tv_keep B API SEGS ERRB AX CTX F (spZ regs + -128) (tv_frm jf) t R1 mem2 mem3);
        [lia | unfold tv_frm, tv_frame1; cbn [cells_size csize]; lia | exact FR | exact KEEP].
Qed.

Lemma st_kid : forall i Pc pc0, (i < length (kids tv))%nat ->
  Pc ++ tvp (nth i (kids tv) JNull) PBo (d + 1) = a0q tv PBo d (S i) ->
  pc0 = 0x15728 \/ (pc0 = 0x15714 /\ pretty = 0) \/ (pc0 = 0x156c0 /\ tag tv = 5) \/
    (pc0 = 0x156ac /\ pretty = 0 /\ tag tv = 5) ->
  tv_at 0x15778 i (a0q tv PBo d (S i)) -> tv_at pc0 i Pc.
Proof.
  intros i Pc pc0 Hi HX Hpc K.
  pose proof (kids_depth tv i Hi) as KD.
  pose proof tv_nk as NK. pose proof (tvk_eq tv) as TK. pose proof (tvk_eq (nth i (kids tv) JNull)) as TKc.
  pose proof txs_val as TXV.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  eapply (st_sub i Pc (tvp (nth i (kids tv) JNull) PBo (d + 1)) (concat (wvpieces (nth i (kids tv) JNull) PBo (d + 1)))
          pc0 0x155ac 0x15778 (TV_K (nth i (kids tv) JNull))
          (fun m R' => exists kp, pj_u64 (ms_segs B) m (v + 24) kp /\
             OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 11 = Z_to_bv 64 (kp + 56 * Z.of_nat i) /\
             OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 12 = Z_to_bv 64 pretty /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 13 = Z_to_bv 64 (d + 1)) Hi).
  - exists []. rewrite app_nil_r. exact HX.
  - apply tvp_concat.
  - rewrite TKc. lia.
  - rewrite TK, TKc. lia.
  - unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - intros R2 L2 A2 mem2 md2 b2 cap2 LR R2r.
    destruct (tv_cf _ _ _ _ _ _ _ _ R2r) as (kp & yp & CF & LED2 & _ & M2 & _).
    pose proof CF as (TYc & KPc & _ & _ & _ & Hcap & _).
    destruct (Hcap ltac:(lia)) as (cap & Hc & Hl & _).
    destruct (ledger_block_range B API L2 A2 mem2 md2 Lam peak cnt fail kp (56 * cap) M2 LED2 Hl) as (B1 & B2 & B3).
    eapply evt_mono.
    + apply (tv_seg_kid R2 _ _ fp_regs fp_csr mem2 (spZ regs) t v d pretty (Z.of_nat i) pc0 (tag tv) kp LR
               (tv_rngi (Z.of_nat i) ltac:(lia))).
      * exact Hpc.
      * lia.
      * lia.
      * lia.
      * rewrite <- SEGS. exact (proj2 TYc).
      * rewrite <- SEGS. exact (proj2 KPc).
    + intros ms (R' & -> & LR' & G1 & G10 & G11 & G12 & G13). exists R'. split; [reflexivity|].
      split; [exact LR'|]. split; [exact G1|]. split; [exact G10|]. exists kp.
      split; [exact KPc|]. split; [exact G11|]. split; [exact G12 | exact G13].
  - intros R1 R' L2 A2 mem2 md2 b2 cap2 (kp & KPc & G11 & G12 & G13) G S1 R2r ST1.
    destruct (tv_cf _ _ _ _ _ _ _ _ R2r) as (kp' & yp & CF & LED2 & NB2 & M2 & _).
    pose proof CF as (_ & KPc' & _ & _ & _ & Hcap & HKD & _).
    pose proof (pj_u64_uniq (ms_segs B) mem2 (v + 24) kp kp' KPc KPc') as <-.
    destruct (Hcap ltac:(lia)) as (cap & Hc & Hl & _).
    destruct (ledger_block_range B API L2 A2 mem2 md2 Lam peak cnt fail kp (56 * cap) M2 LED2 Hl) as (B1 & B2 & B3).
    destruct (HKD i Hi) as (Dx & Hinc & PJc).
    pose proof (IHC (nth i (kids tv) JNull) KD) as IH.
    eapply SR_mono.
    + apply (IH L2 A2 R1 mem2 md2 t (kp + 56 * Z.of_nat i) pretty (d + 1) b2 _ cap2 Dx _ _ Lam peak cnt fail ST1).
      * rewrite G. exact G11.
      * rewrite G. exact G12.
      * rewrite G. exact G13.
      * exact HPR.
      * lia.
      * lia.
      * exact LED2.
      * exact PJc.
      * intros b Hb. apply DL. apply Hinc. exact Hb.
      * right. exists kp, (56 * cap). split; [exact Hl | lia].
      * lia.
      * left. lia.
      * exact NB2.
    + intros c' Hc'. exact (tx_ret_tt B API F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc').
  - rewrite HX. exact K.
Qed.

Lemma st_key : forall i Pc ms pc0, (i < length (kids tv))%nat -> tv = JObj ms ->
  (exists Z0, Pc ++ strp (fst (nth i ms ([], JNull))) ++ Z0 = a0q tv PBo d (S i)) ->
  pc0 = 0x156c0 \/ (pc0 = 0x156ac /\ pretty = 0) ->
  tv_at 0x15704 i (Pc ++ strp (fst (nth i ms ([], JNull)))) -> tv_at pc0 i Pc.
Proof.
  intros i Pc ms pc0 Hi E HX Hpc K.
  pose proof tv_nk as NK. pose proof (tvk_eq tv) as TK. pose proof txs_val as TXV.
  pose proof (tv_depth1 tv CT) as DP.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  assert (Hims : (i < length ms)%nat) by (rewrite E in Hi; cbn [kids] in Hi; rewrite length_map in Hi; exact Hi).
  eapply (st_sub i Pc (strp (fst (nth i ms ([], JNull)))) (wstr (fst (nth i ms ([], JNull)))) pc0 0x158d4 0x15704 TS_STACK
          (fun m R' => exists yp x, pj_u64 (ms_segs B) m (v + 32) yp /\ pj_u64 (ms_segs B) m (yp + 8 * Z.of_nat i) x /\
             OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 11 = Z_to_bv 64 x) Hi HX).
  - apply concat_strp.
  - unfold TS_STACK. lia.
  - rewrite TK. unfold TS_STACK. lia.
  - unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - intros R2 L2 A2 mem2 md2 b2 cap2 LR R2r.
    destruct (tv_cf _ _ _ _ _ _ _ _ R2r) as (kp & yp & CF & LED2 & _ & M2 & _).
    pose proof CF as (TYc & _ & YPc & _ & _ & _ & _ & HKY).
    destruct (HKY ms i E Hims) as (x & k & Hxk & XPc & _ & (cap & Hc & Hl & _)).
    destruct (ledger_block_range B API L2 A2 mem2 md2 Lam peak cnt fail yp (8 * cap) M2 LED2 Hl) as (B1 & B2 & B3).
    rewrite E in TYc. cbn [tag] in TYc.
    eapply evt_mono.
    + apply (tv_seg_key R2 _ _ fp_regs fp_csr mem2 (spZ regs) t v d pretty (Z.of_nat i) pc0 yp x LR
               (tv_rngi (Z.of_nat i) ltac:(lia))).
      * exact Hpc.
      * lia.
      * pose proof (lam_al B API SEGS ERRB AX CTX F L2 A2 mem2 md2 Lam peak cnt fail yp (8 * cap) M2 LED2 Hl) as Al.
        Z.div_mod_to_equations. lia.
      * lia.
      * rewrite <- SEGS. exact (proj2 TYc).
      * rewrite <- SEGS. exact (proj2 YPc).
      * rewrite <- SEGS. exact (proj2 XPc).
    + intros ms' (R' & -> & LR' & G1 & G10 & G11). exists R'. split; [reflexivity|].
      split; [exact LR'|]. split; [exact G1|]. split; [exact G10|]. exists yp, x.
      split; [exact YPc|]. split; [exact XPc | exact G11].
  - intros R1 R' L2 A2 mem2 md2 b2 cap2 (yp & x & YPc & XPc & G11) G S1 R2r ST1.
    destruct (tv_cf _ _ _ _ _ _ _ _ R2r) as (kp & yp' & CF & LED2 & NB2 & M2 & _).
    pose proof CF as (_ & _ & YPc' & _ & _ & _ & _ & HKY).
    pose proof (pj_u64_uniq (ms_segs B) mem2 (v + 32) yp yp' YPc YPc') as <-.
    destruct (HKY ms i E Hims) as (x' & k & Hxk & XPc' & CSk & _).
    pose proof (pj_u64_uniq (ms_segs B) mem2 (yp + 8 * Z.of_nat i) x x' XPc XPc') as <-.
    eapply SR_mono.
    + exact (TXS L2 A2 R1 mem2 md2 t x k b2 _ cap2 (fst (nth i ms ([], JNull))) _ _ Lam peak cnt fail ST1
               (eq_trans (G _) G11) LED2 CSk NB2).
    + intros c' Hc'. exact (tx_ret_tt B API F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc').
  - exact K.
Qed.

Lemma st_line : forall i Pc, (i < length (kids tv))%nat -> pretty <> 0 ->
  (exists Z0, Pc ++ wind PBo (d + 1) ++ Z0 = a0q tv PBo d (S i)) ->
  tv_at 0x156c0 i (Pc ++ wind PBo (d + 1)) -> tv_at 0x156ac i Pc.
Proof.
  intros i Pc Hi Hp HX K.
  pose proof tv_nk as NK. pose proof (tvk_eq tv) as TK. pose proof txs_val as TXV.
  pose proof (tv_depth1 tv CT) as DP.
  assert (WT : wind PBo (d + 1) = wind true (d + 1)) by (rewrite (proj2 (Z.eqb_neq _ _) Hp); reflexivity).
  eapply (st_sub i Pc (wind PBo (d + 1)) (concat (wind PBo (d + 1))) 0x156ac 0x15a70 0x156c0 TL_STACK
          (fun m R' => OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' 11 = Z_to_bv 64 (d + 1)) Hi HX).
  - reflexivity.
  - unfold TL_STACK. lia.
  - rewrite TK. unfold TL_STACK. lia.
  - unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
  - intros R2 L2 A2 mem2 md2 b2 cap2 LR R2r. eapply evt_mono.
    + exact (tv_seg_line R2 _ _ fp_regs fp_csr mem2 (spZ regs) t v d pretty (Z.of_nat i) LR
               (tv_rngi (Z.of_nat i) ltac:(lia)) Hp).
    + intros ms (R' & -> & LR' & G1 & G10 & G11). exists R'. split; [reflexivity|].
      split; [exact LR'|]. split; [exact G1|]. split; [exact G10 | exact G11].
  - intros R1 R' L2 A2 mem2 md2 b2 cap2 G11 G S1 R2r ST1.
    rewrite WT in ST1 |- *.
    assert (EQ : len0 + Z.of_nat (length (map (Z_to_bv 8) (concat Pc))) +
                 Z.of_nat (length (map (Z_to_bv 8) (concat (wind true (d + 1))))) + 1 =
                 len0 + Z.of_nat (length (map (Z_to_bv 8) (concat Pc))) + 1 + 2 * (d + 1) + 1)
      by (rewrite wind_len by lia; lia).
    exact (TXL L2 A2 R1 mem2 md2 t (d + 1) b2 _ cap2 _ _ (tx_start_need B API F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ ST1)
             (eq_trans (G _) G11) ltac:(lia)).
  - exact K.
Qed.

Lemma st_close : forall pc0 Pc regs2 mem2 md2 L2 A2 b2 cap2 x16 jf,
  Pc ++ [[cc tv]] = tvp tv PBo d ->
  pc0 = 0x157a4 \/ (pc0 = 0x15654 /\ length (kids tv) = 0%nat /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 18 = Z_to_bv 64 1) \/
    (pc0 = 0x15778 /\ pretty = 0 /\ (0 < length (kids tv))%nat /\
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 26 = Z_to_bv 64 (Z.of_nat (length (kids tv)) - 1) /\
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 24 = Z_to_bv 64 (56 * (Z.of_nat (length (kids tv)) - 1)) /\
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 25 = Z_to_bv 64 (8 * (Z.of_nat (length (kids tv)) - 1))) ->
  tv_lr0 regs2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty ->
  tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) (concat Pc)) bnd L A mem md L2 A2 mem2 md2 b2 cap2
    (plen Pc) ->
  rw_cells rsegs mem2 (spZ regs + -128) (tv_frm0 x16 jf) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 pc0) mem2 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md2) PPo.
Proof.
  intros pc0 Pc regs2 mem2 md2 L2 A2 b2 cap2 x16 jf HX Hpc L0 R2 FR.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof (tvk_eq tv) as TK. pose proof txs_val as TXV. pose proof tv_nk as NK.
  destruct (tv_cf _ _ _ _ _ _ _ _ R2) as (kp & yp & CF & LED2 & NB2 & M2 & RA2 & Hh & Hlz).
  pose proof CF as (TYc & _ & _ & NNc & _).
  assert (HCC : exists lit, (lit = 0x102a8 \/ lit = 0x10390) /\ (if tag tv =? 6 then 0x102a8 else 0x10390) = lit /\
                  img_chk lit [cc tv] = true).
  { destruct CT as [C|C]; [destruct (tag5 tv C) as (it & E) | destruct (tag6 tv C) as (it & E)]; rewrite E;
      eexists; (split; [|split; [reflexivity | vm_compute; reflexivity]]); cbn; lia. }
  destruct HCC as (lit & Hlit & Elit & HI).
  eapply (tv_run B API SEGS ERRB AX CTX F regs2 pc0 mem2 md2 0x154b8 _ PPo Hh Hlz).
  { apply (tv_seg_close regs2 _ _ fp_regs fp_csr mem2 (spZ regs) t v d pretty pc0 (tag tv) (Z.of_nat (length (kids tv)))
             (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19)
             (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24)
             (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) x16 jf L0 (tv_rngi 0 ltac:(lia))).
    - destruct Hpc as [->|[(-> & Hn & E18)|(-> & Hp & Hn & E26 & E24 & E25)]].
      + left. reflexivity.
      + right. left. split; [reflexivity|]. split; [rewrite Hn; reflexivity | exact E18].
      + right. right. split; [reflexivity|]. split; [exact Hp|]. split; [lia|].
        split; [exact E26|]. split; [exact E24 | exact E25].
    - exact CT.
    - lia.
    - rewrite <- SEGS. exact (proj2 TYc).
    - rewrite <- SEGS. exact (proj2 NNc).
    - exact (proj1 FR). }
  intros R1 R' (RS & G10 & G11 & G12) G.
  pose proof (tv_saved_g R' R1 (tv_restored_saved R' RS) G) as SV1.
  pose proof (tv_saved_sp R1 SV1) as Sp1.
  apply (tv_tail_put Pc [cc tv] lit R1 L2 A2 mem2 md2 b2 cap2 R2 HX SV1).
  - rewrite G. exact G10.
  - rewrite G, G11, Elit. reflexivity.
  - rewrite G, G12. reflexivity.
  - lia.
  - cbn [length Z.of_nat]. lia.
  - exact (tv_imgs B API SEGS ERRB AX CTX F mem2 lit [cc tv] RA2 HI).
  - intros i Hi.
    apply (tv_img_ok B API SEGS ERRB AX CTX F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) (concat Pc)) bnd
             L A mem md L2 A2 mem2 md2 b2 cap2 (plen Pc) R1 lit (Z.of_nat (length [cc tv])) R2);
      [rewrite Sp1; lia | lia | lia | cbn [length Z.of_nat]; lia | exact (tv_img_ro lit [cc tv] HI) | exact Hi].
Qed.

Lemma st_end : forall i, (i < length (kids tv))%nat ->
  ((S i < length (kids tv))%nat -> tv_at 0x15698 (S i) (a0q tv PBo d (S i))) ->
  tv_at 0x15778 i (a0q tv PBo d (S i)).
Proof.
  intros i Hi IH regs2 mem2 md2 L2 A2 b2 cap2 jf LR R2 FR.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof (tvk_eq tv) as TK. pose proof txs_val as TXV. pose proof tv_nk as NK.
  pose proof (tv_depth1 tv CT) as DP.
  destruct (tv_cf _ _ _ _ _ _ _ _ R2) as (kp & yp & CF & LED2 & NB2 & M2 & RA2 & Hh & Hlz).
  pose proof CF as (_ & _ & _ & NNc & _).
  destruct (Nat.lt_ge_cases (S i) (length (kids tv))) as [Hn|Hn].
  - eapply (tv_run B API SEGS ERRB AX CTX F regs2 0x15778 mem2 md2 0x15698 _ PPo Hh Hlz).
    + apply (tv_seg_next regs2 _ _ fp_regs fp_csr mem2 (spZ regs) t v d pretty (Z.of_nat i)
               (Z.of_nat (length (kids tv))) LR (tv_rngi (Z.of_nat i) ltac:(lia)) ltac:(lia)).
      rewrite <- SEGS. exact (proj2 NNc).
    + intros R1 R' LR' G. apply (IH Hn R1 mem2 md2 L2 A2 b2 cap2 jf); [| exact R2 | exact FR].
      replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia. exact (tv_lr_g _ _ _ _ _ _ _ _ _ _ LR' G).
  - assert (EN : length (kids tv) = S i) by lia.
    destruct (Z.eq_dec pretty 0) as [Hp|Hp].
    + apply (st_close 0x15778 (a0q tv PBo d (S i)) regs2 mem2 md2 L2 A2 b2 cap2 (le8 (Z_to_bv 64 0x102aa)) jf).
      * assert (WD : wind PBo d = []) by (rewrite (proj2 (Z.eqb_eq _ _) Hp); reflexivity).
        rewrite <- (a0q_close tv PBo d CT). rewrite EN. cbn [Nat.eqb]. rewrite WD. reflexivity.
      * destruct LR as (_ & _ & _ & _ & _ & _ & E24 & E25 & E26 & _).
        right. right. split; [reflexivity|]. split; [exact Hp|]. split; [lia|].
        replace (Z.of_nat (length (kids tv)) - 1) with (Z.of_nat i) by lia.
        split; [exact E26|]. split; [exact E24 | exact E25].
      * exact (proj1 LR).
      * exact R2.
      * exact (tv_f10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR).
    + eapply (tv_run B API SEGS ERRB AX CTX F regs2 0x15778 mem2 md2 0x15a70 _ PPo Hh Hlz).
      * eapply (tv_seg_endl regs2 _ _ fp_regs fp_csr mem2 (spZ regs) t v d pretty (Z.of_nat i)
                 (Z.of_nat (length (kids tv))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ LR (tv_rngi (Z.of_nat i) ltac:(lia))
                 ltac:(lia) ltac:(lia) Hp).
        -- rewrite <- SEGS. exact (proj2 NNc).
        -- exact (proj1 FR).
      * intros R1 R' (L0' & G1 & G10 & G11) G.
        pose proof (tv_lr0_g _ _ _ _ _ _ _ _ _ L0' G) as L01.
        pose proof (tv_lr_sp R1 _ _ _ _ _ _ _ L01 ltac:(lia)) as S1.
        pose proof L0' as (_ & _ & E4 & _).
        assert (PB : PBo = true) by (rewrite (proj2 (Z.eqb_neq _ _) Hp); reflexivity).
        assert (HX : (a0q tv PBo d (S i) ++ wind true d) ++ [[cc tv]] = tvp tv PBo d).
        { rewrite <- (a0q_close tv PBo d CT). rewrite EN. cbn [Nat.eqb]. rewrite PB, <- app_assoc. reflexivity. }
        eapply (tv_call B API SEGS ERRB AX CTX F (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd _ _
                  (map (Z_to_bv 8) (concat (a0q tv PBo d (S i)))) L2 A2 mem2 md2 b2 cap2 (plen (a0q tv PBo d (S i)))
                  TL_STACK R1 (Z_to_bv 64 0x15a70) (map (Z_to_bv 8) (concat (wind true d))) (plen (wind true d)) [1]
                  (fun _ _ _ => True) _ ST R2).
        -- unfold tv_calls. rewrite <- HX, !plen_app. rewrite <- app_assoc. reflexivity.
        -- rewrite S1, TK. unfold TL_STACK. lia.
        -- rewrite S1. lia.
        -- rewrite S1. Z.div_mod_to_equations. lia.
        -- unfold TL_STACK. lia.
        -- rewrite G, G1. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
        -- rewrite G. exact E4.
        -- rewrite G. exact G10.
        -- rewrite !length_map, <- tvp_concat, <- HX, !concat_app, !length_app. cbn [concat length]. lia.
        -- intros ST1.
           assert (EQ : len0 + Z.of_nat (length (map (Z_to_bv 8) (concat (a0q tv PBo d (S i))))) +
                        Z.of_nat (length (map (Z_to_bv 8) (concat (wind true d)))) + 1 =
                        len0 + Z.of_nat (length (map (Z_to_bv 8) (concat (a0q tv PBo d (S i))))) + 1 + 2 * d + 1)
             by (rewrite wind_len by lia; lia).
           exact (TXL L2 A2 R1 mem2 md2 t d b2 _ cap2 _ _
                    (tx_start_need B API F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ ST1) (eq_trans (G _) G11) ltac:(lia)).
        -- intros L3 A3 regs3 mem3 md3 RP (b3 & cap3 & R3) KEEP. rewrite G, G1.
           apply (st_close 0x157a4 (a0q tv PBo d (S i) ++ wind true d) regs3 mem3 md3 L3 A3 b3 cap3
                    (le8 (Z_to_bv 64 0x102aa)) jf HX).
           ++ left. reflexivity.
           ++ exact (tv_lr0_p _ _ _ _ _ _ _ _ _ L01 RP).
           ++ destruct (pq_app (a0q tv PBo d (S i)) (wind true d) (concat (wind true d)) eq_refl) as [E1 E2].
              rewrite E1, E2. exact R3.
           ++ apply tv_f10. apply (tv_keep B API SEGS ERRB AX CTX F (spZ regs + -128) (tv_frm jf) t R1 mem2 mem3);
                [lia | unfold tv_frm, tv_frame1; cbn [cells_size csize]; lia | exact FR | exact KEEP].
Qed.

Lemma st_item : forall i, (i < length (kids tv))%nat ->
  tv_at 0x15778 i (a0q tv PBo d (S i)) -> tv_at 0x15698 i (a0q tv PBo d i).
Proof.
  intros i Hi K.
  pose proof tv_nk as NK.
  pose proof (a0q_succ tv PBo d i Hi) as AS. unfold ipcq in AS.
  assert (K1 : tv_at 0x156ac i (a0q tv PBo d i ++ wcomma i)).
  { destruct (Z.eq_dec pretty 0) as [Hp|Hp].
    - assert (WZ : wind PBo (d + 1) = []) by (rewrite (proj2 (Z.eqb_eq _ _) Hp); reflexivity).
      assert (SPZ : spq tv PBo = []) by (rewrite (proj2 (Z.eqb_eq _ _) Hp); reflexivity).
      destruct CT as [C5|C6].
      + destruct (tag5 tv C5) as (items & E).
        assert (KZ : keyq tv i = []) by (rewrite E; reflexivity).
        apply (st_kid i _ _ Hi); [| right; right; right; split; [reflexivity|]; split; [exact Hp | exact C5] | exact K].
        rewrite AS, WZ, KZ, SPZ. rewrite <- !app_assoc. reflexivity.
      + destruct (tag6 tv C6) as (ms & E).
        assert (KZ : keyq tv i = strp (fst (nth i ms ([], JNull))) ++ [[58]]) by (rewrite E; reflexivity).
        assert (K4 : tv_at 0x15714 i ((a0q tv PBo d i ++ wcomma i) ++ strp (fst (nth i ms ([], JNull))) ++ [[58]])).
        { apply (st_kid i _ _ Hi); [| right; left; split; [reflexivity | exact Hp] | exact K].
          rewrite AS, WZ, KZ, SPZ. rewrite <- !app_assoc. reflexivity. }
        assert (K3 : tv_at 0x15704 i ((a0q tv PBo d i ++ wcomma i) ++ strp (fst (nth i ms ([], JNull))))).
        { eapply (st_put i _ [58] 0x15704 0x15714 0x1035c 1 Hi).
          - exists (spq tv PBo ++ tvp (nth i (kids tv) JNull) PBo (d + 1)). rewrite AS, WZ, KZ.
            rewrite <- !app_assoc. reflexivity.
          - vm_compute. reflexivity.
          - lia.
          - cbn [length Z.of_nat]. lia.
          - reflexivity.
          - unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
          - intros R2 m jf LR _.
            exact (tv_seg_colon R2 _ _ fp_regs fp_csr m (spZ regs) t v d pretty (Z.of_nat i) LR
                     (tv_rngi (Z.of_nat i) ltac:(lia))).
          - rewrite <- ?app_assoc in K4. rewrite <- ?app_assoc. exact K4. }
        apply (st_key i _ ms _ Hi E).
        * exists ([[58]] ++ spq tv PBo ++ tvp (nth i (kids tv) JNull) PBo (d + 1)). rewrite AS, WZ, KZ.
          rewrite <- !app_assoc. reflexivity.
        * right. split; [reflexivity | exact Hp].
        * exact K3.
    - assert (K2 : tv_at 0x156c0 i ((a0q tv PBo d i ++ wcomma i) ++ wind PBo (d + 1))).
      { destruct CT as [C5|C6].
        + destruct (tag5 tv C5) as (items & E).
          assert (KZ : keyq tv i = [] /\ spq tv PBo = []) by (rewrite E; destruct (negb (pretty =? 0)); split; reflexivity).
          destruct KZ as [KZ1 KZ2].
          apply (st_kid i _ _ Hi); [| right; right; left; split; [reflexivity | exact C5] | exact K].
          rewrite AS, KZ1, KZ2. rewrite <- !app_assoc. reflexivity.
        + destruct (tag6 tv C6) as (ms & E).
          assert (KZ : keyq tv i = strp (fst (nth i ms ([], JNull))) ++ [[58]]) by (rewrite E; reflexivity).
          assert (SP1 : spq tv PBo = [[32]]) by (rewrite E, (proj2 (Z.eqb_neq _ _) Hp); reflexivity).
          assert (K5 : tv_at 0x15728 i ((((a0q tv PBo d i ++ wcomma i) ++ wind PBo (d + 1)) ++
                                          strp (fst (nth i ms ([], JNull))) ++ [[58]]) ++ [[32]])).
          { apply (st_kid i _ _ Hi); [| left; reflexivity | exact K].
            rewrite AS, KZ, SP1. rewrite <- !app_assoc. reflexivity. }
          assert (K4 : tv_at 0x15714 i (((a0q tv PBo d i ++ wcomma i) ++ wind PBo (d + 1)) ++
                                          strp (fst (nth i ms ([], JNull))) ++ [[58]])).
          { eapply (st_put i _ [32] 0x15714 0x15728 0x102aa 1 Hi).
            - exists (tvp (nth i (kids tv) JNull) PBo (d + 1)). rewrite AS, KZ, SP1. rewrite <- !app_assoc. reflexivity.
            - vm_compute. reflexivity.
            - lia.
            - cbn [length Z.of_nat]. lia.
            - reflexivity.
            - unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
            - intros R2 m jf LR FRm.
              exact (tv_seg_sp R2 _ _ fp_regs fp_csr m (spZ regs) t v d pretty (Z.of_nat i)
                       _ _ _ _ _ _ _ _ _ _ _ _ _ jf LR (tv_rngi (Z.of_nat i) ltac:(lia)) Hp (proj1 FRm)).
            - exact K5. }
          assert (K3 : tv_at 0x15704 i (((a0q tv PBo d i ++ wcomma i) ++ wind PBo (d + 1)) ++
                                          strp (fst (nth i ms ([], JNull))))).
          { eapply (st_put i _ [58] 0x15704 0x15714 0x1035c 1 Hi).
            - exists (spq tv PBo ++ tvp (nth i (kids tv) JNull) PBo (d + 1)). rewrite AS, KZ.
              rewrite <- !app_assoc. reflexivity.
            - vm_compute. reflexivity.
            - lia.
            - cbn [length Z.of_nat]. lia.
            - reflexivity.
            - unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
            - intros R2 m jf LR _.
              exact (tv_seg_colon R2 _ _ fp_regs fp_csr m (spZ regs) t v d pretty (Z.of_nat i) LR
                       (tv_rngi (Z.of_nat i) ltac:(lia))).
            - rewrite <- ?app_assoc in K4. rewrite <- ?app_assoc. exact K4. }
          apply (st_key i _ ms _ Hi E).
          * exists ([[58]] ++ spq tv PBo ++ tvp (nth i (kids tv) JNull) PBo (d + 1)). rewrite AS, KZ.
            rewrite <- !app_assoc. reflexivity.
          * left. reflexivity.
          * exact K3. }
      apply (st_line i _ Hi Hp); [| exact K2].
      exists (keyq tv i ++ spq tv PBo ++ tvp (nth i (kids tv) JNull) PBo (d + 1)). rewrite AS.
      rewrite <- !app_assoc. reflexivity. }
  destruct i as [|i'].
  - change (wcomma 0) with (@nil (list Z)) in K1. rewrite app_nil_r in K1.
    apply (st_mv 0 _ 0x15698 0x156ac); [| exact K1].
    intros R2 m LR. exact (tv_seg_h0 R2 _ _ fp_regs fp_csr m (spZ regs) t v d pretty LR (tv_rngi 0 ltac:(lia))).
  - eapply (st_put (S i') _ [44] 0x15698 0x156ac 0x10335 1 Hi).
    + exists (wind PBo (d + 1) ++ keyq tv (S i') ++ spq tv PBo ++ tvp (nth (S i') (kids tv) JNull) PBo (d + 1)).
      rewrite AS. reflexivity.
    + vm_compute. reflexivity.
    + lia.
    + cbn [length Z.of_nat]. lia.
    + reflexivity.
    + unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
    + intros R2 m jf LR _.
      exact (tv_seg_h1 R2 _ _ fp_regs fp_csr m (spZ regs) t v d pretty (Z.of_nat (S i')) LR
               (tv_rngi (Z.of_nat (S i')) ltac:(lia)) ltac:(lia)).
    + exact K1.
Qed.

Lemma st_loop : forall k i, (i + k = length (kids tv))%nat -> (i < length (kids tv))%nat ->
  tv_at 0x15698 i (a0q tv PBo d i).
Proof.
  induction k as [|k IH]; intros i Hk Hi; [lia|].
  apply st_item; [exact Hi|]. apply st_end; [exact Hi|]. intros Hs. apply IH; lia.
Qed.

Lemma st_open :
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 TX_VALUE) mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) PPo.
Proof.
  destruct tv_nums as (SPK & SP63 & SPal & SPT & Thi & RET & R10 & M0 & INV0 & V0).
  pose proof (spZ_range regs) as SPR. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as ACV.
  pose proof (tvk_eq tv) as TK. pose proof txs_val as TXV. pose proof (tv_depth1 tv CT) as DP.
  pose proof tv_nk as NK.
  pose proof ST as (_ & _ & RA & _).
  assert (RAr : ro_agree rsegs mem) by (rewrite <- SEGS; exact RA).
  pose proof tv_vpos as VPS. destruct tv_v8 as (VP0 & V8).
  destruct (pj_node_hdr _ _ _ _ _ _ PJ) as (_ & _ & num & str & kp & yp & n & cap & Hh).
  destruct Hh as (_ & (_ & TY) & _). rewrite SEGS in TY.
  destruct (a0q_le tv PBo d 0 CT ltac:(lia)) as [rst ER]. rewrite a0q_0 in ER.
  assert (HOC : exists lit, (lit = 0x10333 \/ lit = 0x1041a) /\ (if tag tv =? 6 then 0x1041a else 0x10333) = lit /\
                  img_chk lit [oc tv] = true).
  { destruct CT as [C|C]; [destruct (tag5 tv C) as (it & E) | destruct (tag6 tv C) as (it & E)]; rewrite E;
      eexists; (split; [|split; [reflexivity | vm_compute; reflexivity]]); cbn; lia. }
  destruct HOC as (lit & Hlit & Elit & HI).
  apply (tv_entry (fun R pc m' => pc = Z_to_bv 64 0x154b8 /\
           tv_lr0 R (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (spZ regs) t v d pretty /\
           OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 1 = Z_to_bv 64 0x15654 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 t /\
           OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 11 = Z_to_bv 64 lit /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 12 = Z_to_bv 64 1 /\
           OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 18 = Z_to_bv 64 1 /\ exists j0 j1, rw_cells rsegs m' (spZ regs + -128) (tv_frm0 j1 j0))).
  - intros junk FRN. eapply evt_mono.
    + eapply ub_seg_open with (k := tag tv).
      * exact CT.
      * lia.
      * lia.
      * lia.
      * lia.
      * exact V8.
      * lia.
      * exact VPS.
      * lia.
      * exact FRN.
      * apply bytes_at_normalize; [exact RAr | exact TY].
      * apply mem_inv_normalize.
    + intros ms (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & j0 & j1 & -> & MU & WM & FR).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|].
      split; [unfold tv_lr0; repeat split; tv_g1; reflexivity|].
      split; [tv_g1; reflexivity|]. split; [tv_g1; reflexivity|].
      split; [tv_g1; rewrite Elit; reflexivity|]. split; [tv_g1; reflexivity|].
      split; [tv_g1; reflexivity|]. exists j0, j1. exact FR.
  - intros R pc m' R1 mem1 (-> & L0 & G1 & G10 & G11 & G12 & G18 & (j0 & j1 & FR)) G MRL R0.
    pose proof (rw_cells_rel _ _ _ _ MRL FR) as FR1.
    pose proof (tv_lr0_g _ _ _ _ _ _ _ _ _ L0 G) as L01.
    pose proof (tv_lr_sp R1 _ _ _ _ _ _ _ L01 ltac:(lia)) as S1.
    pose proof L0 as (_ & _ & E4 & _).
    pose proof R0 as (_ & _ & _ & _ & _ & _ & _ & _ & RA1 & _).
    change (Z_to_bv 64 0x154b8) with (Z_to_bv 64 TX_PUT).
    eapply (tx_put_call B API SEGS ERRB AX CTX F TXP (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd _ _
              [] L A mem1 md b0 cap0 [] R1 lit 1 [Z_to_bv 8 (oc tv)] (plen rst) _ ST R0).
    + unfold tv_calls. rewrite ER. reflexivity.
    + rewrite S1. lia.
    + rewrite S1. lia.
    + rewrite S1. Z.div_mod_to_equations. lia.
    + rewrite G, G1. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok. vm_compute. reflexivity.
    + rewrite G. exact E4.
    + rewrite G. exact G10.
    + rewrite G. exact G11.
    + rewrite G. exact G12.
    + lia.
    + lia.
    + lia.
    + exact (tv_imgs B API SEGS ERRB AX CTX F mem1 lit [oc tv] RA1 HI).
    + reflexivity.
    + intros k Hk.
      apply (tv_img_ok B API SEGS ERRB AX CTX F (TV_K tv) regs t b0 len0 cap0 txt [] bnd L A mem md L A mem1 md
               b0 cap0 [] R1 lit 1 R0); [rewrite S1; lia | lia | lia | lia | exact (tv_img_ro lit [oc tv] HI) | exact Hk].
    + rewrite !length_map, <- tvp_concat, ER. cbn [concat app length]. lia.
    + intros L2 A2 regs2 mem2 md2 RP (b2 & cap2 & R2) KEEP.
      rewrite G, G1.
      pose proof (tv_lr0_p _ _ _ _ _ _ _ _ _ L01 RP) as L02.
      assert (FR2 : rw_cells rsegs mem2 (spZ regs + -128) (tv_frm0 j1 j0)).
      { apply (tv_keep B API SEGS ERRB AX CTX F (spZ regs + -128) (tv_frm0 j1 j0) t R1 mem1 mem2);
          [lia | unfold tv_frm0, tv_frame0; cbn [cells_size csize]; lia | exact FR1 | exact KEEP]. }
      assert (R2' : tx_relx B API F (TV_K tv) regs t b0 len0 cap0 txt (map (Z_to_bv 8) (concat (a0q tv PBo d 0))) bnd
                      L A mem md L2 A2 mem2 md2 b2 cap2 (plen (a0q tv PBo d 0))) by (rewrite a0q_0; exact R2).
      destruct (Nat.eq_dec (length (kids tv)) 0) as [E0|E0].
      * apply (st_close 0x15654 (a0q tv PBo d 0) regs2 mem2 md2 L2 A2 b2 cap2 j1 j0).
        -- rewrite <- (a0q_close tv PBo d CT). rewrite E0. reflexivity.
        -- right. left. split; [reflexivity|]. split; [exact E0|].
           transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R1 18); [exact (RP 18 ltac:(unfold callee_saved; lia)) | rewrite G; exact G18].
        -- exact L02.
        -- exact R2'.
        -- exact FR2.
      * destruct (tv_cf _ _ _ _ _ _ _ _ R2') as (kp' & yp' & CF & _ & _ & _ & _ & Hh2 & Hlz2).
        pose proof CF as (_ & _ & _ & NNc & _).
        eapply (tv_run_m B API SEGS ERRB AX CTX F regs2 0x15654 mem2 md2 0x15698 _ _ _ PPo Hh2 Hlz2).
        -- eapply (tv_seg_after_open regs2 _ _ fp_regs fp_csr mem2 (spZ regs) t v d pretty
                    (Z.of_nat (length (kids tv))) _ _ _ _ _ _ _ _ _ _ _ _ _ j1 j0 L02 (tv_rngi 0 ltac:(lia)) ltac:(lia)).
           ++ rewrite <- SEGS. exact (proj2 NNc).
           ++ exact FR2.
        -- intros R3 R' m3 (LR' & FR3) G' MU3 WM3.
           pose proof R2' as (_ & _ & _ & _ & _ & _ & _ & _ & RA2 & _).
           assert (RA3 : ro_agree (ms_segs B) m3).
           { apply (tv_ro_munch B API SEGS ERRB AX CTX F mem2 m3 (spZ regs + -112) (spZ regs + -104));
               [exact RA2 | exact MU3 | lia | lia | lia]. }
           pose proof (tx_relx_store B API SEGS ERRB AX CTX HG F (TV_K tv) L A regs mem md t b0 len0 cap0 txt bnd _ _ _
                         L2 A2 mem2 md2 b2 cap2 _ m3 (spZ regs + -112) (spZ regs + -104) ST R2' MU3 WM3 RA3
                         ltac:(intros a Ha; lia)) as R3'.
           apply (st_loop (length (kids tv)) 0 ltac:(lia) ltac:(lia) R3 m3 md2 L2 A2 b2 cap2 j0);
             [exact (tv_lr_g _ _ _ _ _ _ _ _ _ _ LR' G') | exact R3' | exact FR3].
Qed.

End Coll.

End Node.
Lemma tv_all : forall n tv, (depth tv < n)%nat -> tv_for B API F tv.
Proof.
  induction n as [|n IH]; intros tv Hd; [lia|].
  intros L A regs mem md t v pretty d b0 len0 cap0 D txt bnd Lam peak cnt fail
    ST R11 R12 R13 HPR HD0 HDD LED PJ DL VP V64 VT NB.
  assert (Hc : tv = JNull \/ tv = JFalse \/ tv = JTrue \/ (exists x b, tv = JNum x b) \/ (exists s, tv = JStr s) \/
               tag tv = 5 \/ tag tv = 6).
  { destruct tv as [| | | x b | s | items | ms].
    - left. reflexivity.
    - right. left. reflexivity.
    - right. right. left. reflexivity.
    - right. right. right. left. exists x, b. reflexivity.
    - right. right. right. right. left. exists s. reflexivity.
    - right. right. right. right. right. left. reflexivity.
    - right. right. right. right. right. right. reflexivity. }
  destruct Hc as [E|[E|[E|[(x & b & E)|[(s & E)|C]]]]].
  - exact (st_lit L A regs mem md t v pretty d b0 len0 cap0 tv D txt bnd Lam peak cnt fail
             ST R11 R12 R13 HPR HD0 HDD LED PJ DL VP V64 VT NB (or_introl E)).
  - exact (st_lit L A regs mem md t v pretty d b0 len0 cap0 tv D txt bnd Lam peak cnt fail
             ST R11 R12 R13 HPR HD0 HDD LED PJ DL VP V64 VT NB (or_intror (or_introl E))).
  - exact (st_lit L A regs mem md t v pretty d b0 len0 cap0 tv D txt bnd Lam peak cnt fail
             ST R11 R12 R13 HPR HD0 HDD LED PJ DL VP V64 VT NB (or_intror (or_intror E))).
  - exact (st_num L A regs mem md t v pretty d b0 len0 cap0 tv D txt bnd Lam peak cnt fail
             ST R11 R12 R13 HPR HD0 HDD LED PJ DL VP V64 VT NB x b E).
  - exact (st_str L A regs mem md t v pretty d b0 len0 cap0 tv D txt bnd Lam peak cnt fail
             ST R11 R12 R13 HPR HD0 HDD LED PJ DL VP V64 VT NB s E).
  - exact (st_open L A regs mem md t v pretty d b0 len0 cap0 tv D txt bnd Lam peak cnt fail
             ST R11 R12 R13 HPR HD0 HDD LED PJ DL VP V64 VT NB (fun tv' H => IH tv' ltac:(lia)) C).
Qed.

End KB.
