(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Mem Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition onum (L : layout) (o : option sptr) : Z := match o with Some p => loc_addr L (LMem p) | None => 0 end.

Lemma sval_optr : forall L o, sval_num L (optr o) = onum L o.
Proof. intros L [p|]; reflexivity. Qed.

(* [comment removed for export] *)
Definition nenv (m : word -> option byte) : Prop :=
  rdn SEGS m (wa 408992) 8 = Some (word_to_le_bytes 8 (wa 0x95e40)) /\
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) /\
  (exists can, 0 <= can <= 2^64 - 1 /\ rdn SEGS m (wa 613952) 8 = Some (word_to_le_bytes 8 (wa can))).

(* [comment removed for export] *)
Definition cplace (L : layout) (LIM : Z) (c : mcell) : Prop :=
  1 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= LIM /\
  ((0x95ed8 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x96278) \/
   loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x10000 \/ 0x97000 <= loc_addr L (mc_loc c)).

Lemma cplace_RS : forall L LIM s' s, RS L s' s -> (forall c, In c (image s) -> cplace L LIM c) -> forall c, In c (image s') -> cplace L LIM c.
Proof.
  intros L LIM s' s HRS H c Hc. destruct (RS_range L s' s c HRS Hc) as (c0 & H0 & E). pose proof (H c0 H0) as P.
  unfold cplace, cell_range in *. injection E as E1 E2. rewrite E1, E2 in P. exact P.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_frame_n : forall m m' (a : Z) n, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat n -> m' (wa x) = m (wa x)) -> rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n.
Proof.
  intros m m' a n Ha Hn H. revert a Ha Hn H. induction n as [|n IH]; intros a Ha Hn H; [reflexivity|].
  rewrite (Mem.rdn_unfold SEGS m' (wa a) (S n)), (Mem.rdn_unfold SEGS m (wa a) (S n)). unfold Mem.mrd. change (Mem.wa a) with (wa a) in *. rewrite (H a) by lia.
  replace (wa a + 1)%bv with (wa (a + 1)) by (rewrite wa_add1; reflexivity).
  rewrite (IH (a + 1)) by (try lia; intros x Hx; apply H; lia). reflexivity.
Qed.

Lemma bview_grow_n : forall m m' x, mem_grows m m' -> bview SEGS m x <> None -> bview SEGS m' x <> None.
Proof.
  intros m m' x Hg H. destruct (bview SEGS m x) as [z|] eqn:E; [|exfalso; exact (H eq_refl)]. clear H.
  destruct (bview_some SEGS m x z E) as (Hx & Hw & Hr). unfold bview.
  replace ((0 <=? x) && (x <? 2^64)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  assert (Hw' : wview SEGS m' (wa x) <> None) by (apply (Frame.wmono_wview SEGS m m'); [exact Hg | exact Hw]).
  destruct (wview SEGS m' (wa x)) as [w|]; [|exact (fun _ => Hw' eq_refl)].
  cbn [ov_read_bytes] in *. destruct (m (wa x)) as [b|] eqn:Em.
  - destruct (m' (wa x)) as [b'|] eqn:Em'; [cbn; discriminate|]. exfalso. apply (Hg (wa x)); [rewrite Em; discriminate | exact Em'].
  - destruct (m' (wa x)) as [b'|] eqn:Em'; [cbn; discriminate|].
    destruct (memory_read SEGS (wa x) 1) as [[|b0 t]|]; cbn in Hr |- *; discriminate.
Qed.

Lemma bview_ne_range : forall m m' a, bview SEGS m' a <> bview SEGS m a -> 0 <= a < 2^64.
Proof.
  intros m m' a H. unfold bview in H. destruct ((0 <=? a) && (a <? 2^64)) eqn:E; [apply andb_prop in E as [E1 E2]; lia | exfalso; apply H; reflexivity].
Qed.

Lemma stk_ok_mono' : forall m sp K K', stk_ok SEGS m sp K -> K' <= K -> stk_ok SEGS m sp K'.
Proof. intros m sp K K' H HK a n H1 H2. apply H; lia. Qed.

Lemma stk_ok_shift : forall m sp K d, stk_ok SEGS m (wa sp) K -> 0 <= d -> d <= sp -> sp < 2^64 -> stk_ok SEGS m (wa (sp - d)) (K - d).
Proof.
  intros m sp K d H Hd1 Hd2 Hsp a n H1 H2. rewrite u_wa_small in H1, H2 by lia. apply H; rewrite u_wa_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma holds_of_mem : forall L (m : word -> option byte) c,
  (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat -> 0 <= loc_addr L (mc_loc c) -> loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 2^64 ->
  (forall k, (k < mc_w c)%nat -> m (wa (loc_addr L (mc_loc c) + Z.of_nat k)) = Some (nth k (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))) (Z_to_bv 8 0))) ->
  cell_holds L (bview SEGS m) c.
Proof.
  intros L m [l w v] Hv Hw Ha1 Ha2 Hm. cbn [mc_loc mc_w mc_val] in *. unfold cell_holds. cbn [mc_loc mc_w mc_val].
  assert (G : forall k, (k < w)%nat -> bview SEGS m (loc_addr L l + Z.of_nat k) = Some (le_byte (sval_num L v) w k)).
  { intros k Hk. rewrite (bview_some_byte SEGS m (loc_addr L l + Z.of_nat k) _ ltac:(lia) (Hm k Hk)). f_equal.
    rewrite le_byte_Z_to_le_bytes by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    unfold le_byte. rewrite Z.mod_mod by lia. reflexivity. }
  destruct v as [z|p|z|]; [exact G | exact G | exfalso; exact (Hv z eq_refl) | exact G].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RX.
Variables (L : layout) (s : astate) (m : word -> option byte) (EXC : list loc).
Hypothesis HR : repr_x L s (bview SEGS m) EXC.
Hypothesis HEX : EXC_ok s EXC.

#[using="EXC HR HEX"] Lemma rx_front_holds : forall c, In c (ctx_cells s ++ areas_cells s (st_areas s)) -> cell_holds L (bview SEGS m) c.
Proof. LiaFast.lf_pins (fun (EXC HR HEX : LiaFast.U) => LiaFast.u0).
  intros c Hc. pose proof HR as (_ & HPW & _).
  apply (repr_x_holds L s _ EXC c HR); [rewrite image_parts, app_assoc; apply in_app_iff; left; exact Hc|].
  exact (not_exc_front L s EXC c HPW HEX Hc).
Qed.

#[using="EXC HR HEX"] Lemma rx_front_rd : forall c, In c (ctx_cells s ++ areas_cells s (st_areas s)) -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
  rdn SEGS m (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))).
Proof. LiaFast.lf_pins (fun (EXC HR HEX : LiaFast.U) => LiaFast.u0). intros c Hc Hv Hw. apply holds_rdn; [exact (rx_front_holds c Hc) | exact Hv | exact Hw]. Qed.

#[using="EXC HR HEX"] Lemma rx_front_wr : forall c, In c (ctx_cells s ++ areas_cells s (st_areas s)) -> (forall z, mc_val c <> VLo5 z) ->
  forall d k, 0 <= d -> d + Z.of_nat k <= Z.of_nat (mc_w c) -> store_ok SEGS m (wa (loc_addr L (mc_loc c) + d)) k = true.
Proof. LiaFast.lf_pins (fun (EXC HR HEX : LiaFast.U) => LiaFast.u0). intros c Hc Hv. apply holds_store_ok; [exact (rx_front_holds c Hc) | exact Hv]. Qed.

Hypothesis HK : KS s.

(* [comment removed for export] *)
#[using="EXC HR HEX HK"] Lemma rx_msc_rd : forall q x c, MT s q = Some x -> In c (meta_slot_cells q (Some x)) ->
  rdn SEGS m (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))).
Proof. LiaFast.lf_pins (fun (EXC HR HEX HK : LiaFast.U) => LiaFast.u0).
  intros q x c Hq Hc. apply rx_front_rd; [exact (msc_in_front s q x c HK Hq Hc) | |].
  - intros z E. destruct x as [pr nx| |a]; cbn [meta_slot_cells In] in Hc;
      repeat (destruct Hc as [<-|Hc]; [cbn [mc_val optr] in E; first [discriminate | destruct pr; discriminate | destruct nx; discriminate
                                                                       | destruct (am_prev a); discriminate | destruct (am_next a); discriminate] |]); destruct Hc.
  - destruct x as [pr nx| |a]; cbn [meta_slot_cells In] in Hc; repeat (destruct Hc as [<-|Hc]; [cbn; lia|]); destruct Hc.
Qed.

(* [comment removed for export] *)
#[using="EXC HR HEX HK"] Lemma rx_msc_wr : forall q x, MT s q = Some x -> forall d k, 0 <= d -> d + Z.of_nat k <= 40 ->
  store_ok SEGS m (wa (loc_addr L (LMem q) + d)) k = true.
Proof. LiaFast.lf_pins (fun (EXC HR HEX HK : LiaFast.U) => LiaFast.u0).
  intros q x Hq. apply (store_ok_of_bytes SEGS m (loc_addr L (LMem q)) 40). intros j Hj.
  assert (HW : forall c, In c (meta_slot_cells q (Some x)) -> forall j', 0 <= j' < Z.of_nat (mc_w c) ->
             wview SEGS m (wa (loc_addr L (mc_loc c) + j')) <> None).
  { intros c Hc j' Hj'. apply (holds_wview SEGS L m c j' (rx_front_holds c (msc_in_front s q x c HK Hq Hc))); [|exact Hj'].
    intros z E. destruct x as [pr nx| |a]; cbn [meta_slot_cells In] in Hc;
      repeat (destruct Hc as [<-|Hc]; [cbn [mc_val optr] in E; first [discriminate | destruct pr; discriminate | destruct nx; discriminate
                                                                       | destruct (am_prev a); discriminate | destruct (am_next a); discriminate] |]); destruct Hc. }
  assert (Cs : exists v1 v2 v3 v4 v5 v6, meta_slot_cells q (Some x) =
     [MCell (LMem (padd q 0)) 8 v1; MCell (LMem (padd q 8)) 8 v2; MCell (LMem (padd q 16)) 8 v3;
      MCell (LMem (padd q 24)) 4 v4; MCell (LMem (padd q 28)) 4 v5; MCell (LMem (padd q 32)) 8 v6]).
  { destruct x as [pr nx| |a]; eexists _, _, _, _, _, _; reflexivity. }
  destruct Cs as (v1 & v2 & v3 & v4 & v5 & v6 & Ec). rewrite Ec in HW.
  destruct (Z.ltb_spec j 8) as [A|A]; [pose proof (HW _ ltac:(left; reflexivity) j ltac:(cbn; lia)) as W; cbn [mc_loc] in W; rewrite loc_padd, Z.add_0_r in W; exact W|].
  destruct (Z.ltb_spec j 16) as [B|B]; [pose proof (HW _ ltac:(right; left; reflexivity) (j - 8) ltac:(cbn; lia)) as W; cbn [mc_loc] in W; rewrite loc_padd in W;
    replace (loc_addr L (LMem q) + j) with (loc_addr L (LMem q) + 8 + (j - 8)) by ring; exact W|].
  destruct (Z.ltb_spec j 24) as [C|C]; [pose proof (HW _ ltac:(right; right; left; reflexivity) (j - 16) ltac:(cbn; lia)) as W; cbn [mc_loc] in W; rewrite loc_padd in W;
    replace (loc_addr L (LMem q) + j) with (loc_addr L (LMem q) + 16 + (j - 16)) by ring; exact W|].
  destruct (Z.ltb_spec j 28) as [D|D]; [pose proof (HW _ ltac:(right; right; right; left; reflexivity) (j - 24) ltac:(cbn; lia)) as W; cbn [mc_loc] in W; rewrite loc_padd in W;
    replace (loc_addr L (LMem q) + j) with (loc_addr L (LMem q) + 24 + (j - 24)) by ring; exact W|].
  destruct (Z.ltb_spec j 32) as [F|F]; [pose proof (HW _ ltac:(right; right; right; right; left; reflexivity) (j - 28) ltac:(cbn; lia)) as W; cbn [mc_loc] in W; rewrite loc_padd in W;
    replace (loc_addr L (LMem q) + j) with (loc_addr L (LMem q) + 28 + (j - 28)) by ring; exact W|].
  pose proof (HW _ ltac:(right; right; right; right; right; left; reflexivity) (j - 32) ltac:(cbn; lia)) as W; cbn [mc_loc] in W; rewrite loc_padd in W.
  replace (loc_addr L (LMem q) + j) with (loc_addr L (LMem q) + 32 + (j - 32)) by ring. exact W.
Qed.

(* [comment removed for export] *)
Section Used.
Variables (q : sptr) (a : ameta).
Hypothesis Hq : MT s q = Some (MUsed a).

#[using="s EXC HR HEX HK Hq"] Lemma rx_prev : rdn SEGS m (wa (loc_addr L (LMem q) + 0)) 8 = Some (word_to_le_bytes 8 (wa (onum L (am_prev a)))).
Proof. LiaFast.lf_pins (fun (s EXC HR HEX HK Hq : LiaFast.U) => LiaFast.u0). pose proof (rx_msc_rd q _ _ Hq ltac:(left; reflexivity)) as H. cbn [mc_loc mc_w mc_val] in H. rewrite loc_padd, sval_optr in H. exact H. Qed.
#[using="s EXC HR HEX HK Hq"] Lemma rx_next : rdn SEGS m (wa (loc_addr L (LMem q) + 8)) 8 = Some (word_to_le_bytes 8 (wa (onum L (am_next a)))).
Proof. LiaFast.lf_pins (fun (s EXC HR HEX HK Hq : LiaFast.U) => LiaFast.u0). pose proof (rx_msc_rd q _ _ Hq ltac:(right; left; reflexivity)) as H. cbn [mc_loc mc_w mc_val] in H. rewrite loc_padd, sval_optr in H. exact H. Qed.
#[using="s EXC HR HEX HK Hq"] Lemma rx_mem : rdn SEGS m (wa (loc_addr L (LMem q) + 16)) 8 = Some (word_to_le_bytes 8 (wa (loc_addr L (LMem (am_mem a))))).
Proof. LiaFast.lf_pins (fun (s EXC HR HEX HK Hq : LiaFast.U) => LiaFast.u0). pose proof (rx_msc_rd q _ _ Hq ltac:(right; right; left; reflexivity)) as H. cbn [mc_loc mc_w mc_val sval_num] in H. rewrite loc_padd in H. exact H. Qed.
#[using="s EXC HR HEX HK Hq"] Lemma rx_avail : rdn SEGS m (wa (loc_addr L (LMem q) + 24)) 4 = Some (word_to_le_bytes 4 (wa (am_avail a))).
Proof. LiaFast.lf_pins (fun (s EXC HR HEX HK Hq : LiaFast.U) => LiaFast.u0). pose proof (rx_msc_rd q _ _ Hq ltac:(right; right; right; left; reflexivity)) as H. cbn [mc_loc mc_w mc_val sval_num] in H. rewrite loc_padd in H. exact H. Qed.
#[using="s EXC HR HEX HK Hq"] Lemma rx_freed : rdn SEGS m (wa (loc_addr L (LMem q) + 28)) 4 = Some (word_to_le_bytes 4 (wa (am_freed a))).
Proof. LiaFast.lf_pins (fun (s EXC HR HEX HK Hq : LiaFast.U) => LiaFast.u0). pose proof (rx_msc_rd q _ _ Hq ltac:(right; right; right; right; left; reflexivity)) as H. cbn [mc_loc mc_w mc_val sval_num] in H. rewrite loc_padd in H. exact H. Qed.
#[using="s EXC HR HEX HK Hq"] Lemma rx_bits : rdn SEGS m (wa (loc_addr L (LMem q) + 32)) 8 = Some (word_to_le_bytes 8 (wa (meta_bits a))).
Proof. LiaFast.lf_pins (fun (s EXC HR HEX HK Hq : LiaFast.U) => LiaFast.u0). pose proof (rx_msc_rd q _ _ Hq ltac:(right; right; right; right; right; left; reflexivity)) as H. cbn [mc_loc mc_w mc_val sval_num] in H. rewrite loc_padd in H. exact H. Qed.
End Used.

(* [comment removed for export] *)
Section Free.
Variables (q : sptr) (pr nx : option sptr).
Hypothesis Hq : MT s q = Some (MFree pr nx).

#[using="s EXC HR HEX HK nx Hq"] Lemma rx_fprev : rdn SEGS m (wa (loc_addr L (LMem q) + 0)) 8 = Some (word_to_le_bytes 8 (wa (onum L pr))).
Proof. LiaFast.lf_pins (fun (s EXC HR HEX HK nx Hq : LiaFast.U) => LiaFast.u0). pose proof (rx_msc_rd q _ _ Hq ltac:(left; reflexivity)) as H. cbn [mc_loc mc_w mc_val] in H. rewrite loc_padd, sval_optr in H. exact H. Qed.
#[using="s EXC HR HEX HK pr Hq"] Lemma rx_fnext : rdn SEGS m (wa (loc_addr L (LMem q) + 8)) 8 = Some (word_to_le_bytes 8 (wa (onum L nx))).
Proof. LiaFast.lf_pins (fun (s EXC HR HEX HK pr Hq : LiaFast.U) => LiaFast.u0). pose proof (rx_msc_rd q _ _ Hq ltac:(right; left; reflexivity)) as H. cbn [mc_loc mc_w mc_val] in H. rewrite loc_padd, sval_optr in H. exact H. Qed.
End Free.

(* [comment removed for export] *)
Hypothesis Hctx : ly_ctx L = 0x95ed8.

#[using="EXC HR HEX Hctx"] Lemma rx_act : forall k, (k < 48)%nat ->
  rdn SEGS m (wa (614184 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (wa (onum L (nth k (st_active s) None)))).
Proof. LiaFast.lf_pins (fun (EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  intros k Hk. pose proof (rx_front_rd _ (ctx_in_front s _ (act_in_ctx s k Hk)) ltac:(intros z E; cbn [act_cell mc_val optr] in E; destruct (nth k (st_active s) None); discriminate)
    ltac:(cbn; lia)) as H. cbn [act_cell mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, sval_optr in H. unfold CTX_active in H.
  replace (614184 + 8 * Z.of_nat k) with (0x95ed8 + (80 + 8 * Z.of_nat k)) by ring. exact H.
Qed.

#[using="L EXC HR HEX Hctx"] Lemma rx_usage : forall k, (k < 48)%nat ->
  rdn SEGS m (wa (614568 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (wa (nth k (st_usage s) 0))).
Proof. LiaFast.lf_pins (fun (L EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  intros k Hk. pose proof (rx_front_rd _ (ctx_in_front s _ (usage_in_ctx s k Hk)) ltac:(intros z E; discriminate) ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. unfold CTX_usage in H.
  replace (614568 + 8 * Z.of_nat k) with (0x95ed8 + (464 + 8 * Z.of_nat k)) by ring. exact H.
Qed.

#[using="L EXC HR HEX Hctx"] Lemma rx_seq : rdn SEGS m (wa 615016) 1 = Some (word_to_le_bytes 1 (wa (st_seq s))).
Proof. LiaFast.lf_pins (fun (L EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  pose proof (rx_front_rd _ (ctx_in_front s _ (seq_in_ctx s)) ltac:(intros z E; discriminate) ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. unfold CTX_seq in H. exact H.
Qed.

#[using="L EXC HR HEX Hctx"] Lemma rx_bounce : forall k, (k < 32)%nat ->
  rdn SEGS m (wa (614984 + Z.of_nat k)) 1 = Some (word_to_le_bytes 1 (wa (nth k (st_bounces s) 0))).
Proof. LiaFast.lf_pins (fun (L EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  intros k Hk. pose proof (rx_front_rd _ (ctx_in_front s _ (bounce_in_ctx s k Hk)) ltac:(intros z E; discriminate) ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. unfold CTX_bounces in H.
  replace (614984 + Z.of_nat k) with (0x95ed8 + (880 + Z.of_nat k)) by ring. exact H.
Qed.

#[using="EXC HR HEX Hctx"] Lemma rx_fmh : rdn SEGS m (wa 614120) 8 = Some (word_to_le_bytes 8 (wa (onum L (st_free_meta_head s)))).
Proof. LiaFast.lf_pins (fun (EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  pose proof (rx_front_rd _ (ctx_in_front s _ (fmh_in_ctx s)) ltac:(intros z E; cbn [mc_val optr] in E; destruct (st_free_meta_head s); discriminate) ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, sval_optr in H. unfold CTX_free_meta_head in H. exact H.
Qed.

(* [comment removed for export] *)
#[using="L s EXC HR HEX Hctx"] Lemma rx_act_wr : forall k, (k < 48)%nat -> forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (614184 + 8 * Z.of_nat k + d)) n = true.
Proof. LiaFast.lf_pins (fun (L s EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  intros k Hk d n Hd Hn. pose proof (rx_front_wr _ (ctx_in_front s _ (act_in_ctx s k Hk))
    ltac:(intros z E; cbn [act_cell mc_val optr] in E; destruct (nth k (st_active s) None); discriminate) d n Hd ltac:(cbn; lia)) as H.
  cbn [act_cell mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. unfold CTX_active in H.
  replace (614184 + 8 * Z.of_nat k + d) with (0x95ed8 + (80 + 8 * Z.of_nat k) + d) by ring. exact H.
Qed.

#[using="L s EXC HR HEX Hctx"] Lemma rx_usage_wr : forall k, (k < 48)%nat -> forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (614568 + 8 * Z.of_nat k + d)) n = true.
Proof. LiaFast.lf_pins (fun (L s EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  intros k Hk d n Hd Hn. pose proof (rx_front_wr _ (ctx_in_front s _ (usage_in_ctx s k Hk)) ltac:(intros z E; discriminate) d n Hd ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. unfold CTX_usage in H.
  replace (614568 + 8 * Z.of_nat k + d) with (0x95ed8 + (464 + 8 * Z.of_nat k) + d) by ring. exact H.
Qed.

#[using="L s EXC HR HEX Hctx"] Lemma rx_seq_wr : forall d n, 0 <= d -> d + Z.of_nat n <= 1 -> store_ok SEGS m (wa (615016 + d)) n = true.
Proof. LiaFast.lf_pins (fun (L s EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  intros d n Hd Hn. pose proof (rx_front_wr _ (ctx_in_front s _ (seq_in_ctx s)) ltac:(intros z E; discriminate) d n Hd ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. unfold CTX_seq in H. exact H.
Qed.

#[using="L s EXC HR HEX Hctx"] Lemma rx_unmap_wr : forall d n, 0 <= d -> d + Z.of_nat n <= 32 -> store_ok SEGS m (wa (614952 + d)) n = true.
Proof. LiaFast.lf_pins (fun (L s EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  intros d n. revert d. induction n as [|n IH]; intros d Hd Hn; [reflexivity|]. cbn [store_ok].
  assert (Hk : (Z.to_nat d < 32)%nat) by lia.
  pose proof (holds_wview SEGS L m _ 0 (rx_front_holds _ (ctx_in_front s _ (unmap_in_ctx s (Z.to_nat d) Hk))) ltac:(intros z E; discriminate) ltac:(cbn; lia)) as W.
  cbn [mc_loc loc_addr] in W. rewrite Hctx, Z2Nat.id in W by lia. unfold CTX_unmap_seq in W. rewrite Z.add_0_r in W.
  replace (0x95ed8 + (848 + d)) with (614952 + d) in W by ring.
  destruct (wview SEGS m (wa (614952 + d))) as [b|]; [|exfalso; exact (W eq_refl)].
  rewrite wa_add1. replace (614952 + d + 1) with (614952 + (d + 1)) by ring. apply IH; lia.
Qed.

#[using="L s EXC HR HEX Hctx"] Lemma rx_unmap_wr1 : forall k, (k < 32)%nat -> forall d n, 0 <= d -> d + Z.of_nat n <= 1 -> store_ok SEGS m (wa (614952 + Z.of_nat k + d)) n = true.
Proof. LiaFast.lf_pins (fun (L s EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0). intros k Hk d n Hd Hn. replace (614952 + Z.of_nat k + d) with (614952 + (Z.of_nat k + d)) by ring. apply rx_unmap_wr; lia. Qed.

#[using="L s EXC HR HEX Hctx"] Lemma rx_fmh_wr : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (614120 + d)) n = true.
Proof. LiaFast.lf_pins (fun (L s EXC HR HEX Hctx : LiaFast.U) => LiaFast.u0).
  intros d n Hd Hn. pose proof (rx_front_wr _ (ctx_in_front s _ (fmh_in_ctx s)) ltac:(intros z E; cbn [mc_val optr] in E; destruct (st_free_meta_head s); discriminate) d n Hd ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. unfold CTX_free_meta_head in H. exact H.
Qed.
End RX.

(* [comment removed for export] *)
Lemma rx_ctx_byte : forall L s m EXC o, repr_x L s (bview SEGS m) EXC -> ly_ctx L = 0x95ed8 -> 0 <= o < 928 ->
  exists z, 0 <= z <= 255 /\ rdn SEGS m (wa (614104 + o)) 1 = Some (word_to_le_bytes 1 (wa z)).
Proof.
  intros L s m EXC o (_ & _ & _ & HF) Hctx Ho.
  assert (Hin : In (LCtx 0, CTX_SIZE) (footprint s)) by (unfold footprint; left; reflexivity).
  pose proof (proj1 (Forall_forall _ _) HF _ Hin (614104 + o)) as Hm. cbn [fst snd loc_addr] in Hm. rewrite Hctx in Hm. unfold CTX_SIZE in Hm.
  specialize (Hm ltac:(lia)).
  destruct (bview SEGS m (614104 + o)) as [z|] eqn:Ez; [|exfalso; exact (Hm eq_refl)].
  assert (Rz : 0 <= z <= 255).
  { unfold bview in Ez. destruct ((0 <=? 614104 + o) && (614104 + o <? 2^64)); [|discriminate].
    destruct (wview SEGS m (wa (614104 + o))); [|discriminate]. destruct (ov_read_bytes SEGS m (wa (614104 + o)) 1) as [[|bb [|]]|]; try discriminate.
    injection Ez as <-. pose proof (bv_unsigned_in_range 8 bb) as R. change (bv_modulus 8) with 256 in R. lia. }
  exists z. split; [exact Rz|].
  assert (Hc : cell_holds L (bview SEGS m) (MCell (LCtx o) 1 (VZ z))).
  { unfold cell_holds. cbn [mc_loc mc_w mc_val sval_num loc_addr]. rewrite Hctx. intros k Hk. assert (k = 0%nat) as -> by lia.
    rewrite Z.add_0_r, Ez. f_equal. unfold le_byte. cbn. rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity. }
  pose proof (holds_rdn SEGS L m _ Hc ltac:(intros z0 E; discriminate) ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val sval_num loc_addr] in H. rewrite Hctx in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma rx_aidx : forall L s m EXC q a, repr_x L s (bview SEGS m) EXC -> EXC_ok s EXC -> KS s -> MT s q = Some (MUsed a) -> 0 <= am_aidx a <= 31 ->
  exists b, 0 <= b <= 255 /\ rdn SEGS m (wa (loc_addr L (LMem (am_mem a)) + 8)) 1 = Some (word_to_le_bytes 1 (wa b)) /\ Z.land b 31 = am_aidx a.
Proof.
  intros L s m EXC q a HR HEO HK Hq Ha. pose proof HR as (_ & HPW & _).
  set (c := if am_maplen a =? 0 then MCell (LMem (padd (am_mem a) 8)) 1 (VLo5 (am_aidx a)) else MCell (LMem (padd (am_mem a) 8)) 4 (VZ (am_aidx a))).
  assert (Hc : In c (gpart s)) by (apply (group_in_gpart s q a c Hq (proj1 HK)); right; left; reflexivity).
  assert (Hw : mc_w c <> 8%nat) by (unfold c; destruct (am_maplen a =? 0); cbn; lia).
  assert (Hci : In c (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact Hc).
  pose proof (repr_x_holds L s _ EXC c HR Hci (not_exc_group L s EXC c HPW HEO Hc Hw)) as Hh.
  assert (Hrd : forall b, bview SEGS m (loc_addr L (LMem (am_mem a)) + 8) = Some b -> 0 <= b <= 255 /\
                  rdn SEGS m (wa (loc_addr L (LMem (am_mem a)) + 8)) 1 = Some (word_to_le_bytes 1 (wa b))).
  { intros b E. destruct (bview_some SEGS m _ b E) as (Rx & _ & Hr).
    assert (Rb : 0 <= b <= 255).
    { unfold bview in E. destruct ((0 <=? loc_addr L (LMem (am_mem a)) + 8) && (loc_addr L (LMem (am_mem a)) + 8 <? 2^64)); [|discriminate].
      destruct (wview SEGS m (wa (loc_addr L (LMem (am_mem a)) + 8))); [|discriminate].
      destruct (ov_read_bytes SEGS m (wa (loc_addr L (LMem (am_mem a)) + 8)) 1) as [[|bb [|]]|]; try discriminate.
      injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as R. change (bv_modulus 8) with 256 in R. lia. }
    split; [exact Rb|]. rewrite <- ov_rdn. rewrite Hr. f_equal. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small b (2^64)) by lia. reflexivity. }
  unfold c in Hh. destruct (am_maplen a =? 0).
  - unfold cell_holds in Hh. cbn [mc_loc mc_w mc_val] in Hh. rewrite loc_padd in Hh. destruct Hh as (b & Eb & Hb).
    destruct (Hrd b Eb) as (Rb & R1). exists b. split; [exact Rb|]. split; [exact R1|].
    change 31 with (Z.ones 5). rewrite Z.land_ones by lia. exact Hb.
  - unfold cell_holds in Hh. cbn [mc_loc mc_w mc_val sval_num] in Hh. rewrite loc_padd in Hh.
    pose proof (Hh 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E. destruct (Hrd _ E) as (Rb & R1).
    exists (le_byte (am_aidx a) 4 0). split; [exact Rb|]. split; [exact R1|].
    unfold le_byte. cbn [Z.of_nat]. rewrite Z.shiftr_0_r, !Z.mod_small by (cbn; lia).
    change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma gpart_vs_msc : forall L s q x c, PW L s -> KS s -> MT s q = Some x -> In c (gpart s) -> (1 <= mc_w c)%nat ->
  loc_addr L (LMem q) + 40 <= loc_addr L (mc_loc c) \/ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= loc_addr L (LMem q).
Proof.
  intros L s q x c HPW HK Hq Hc Hw. unfold PW in HPW. rewrite image_parts, app_assoc in HPW.
  assert (D : forall c0, In c0 (meta_slot_cells q (Some x)) -> ranges_disjoint (cell_range L c0) (cell_range L c)).
  { intros c0 H0. apply (pw_cross L _ _ c0 c HPW); [exact (msc_in_front s q x c0 HK Hq H0) | exact Hc]. }
  assert (Cs : exists v1 v2 v3 v4 v5 v6, meta_slot_cells q (Some x) =
     [MCell (LMem (padd q 0)) 8 v1; MCell (LMem (padd q 8)) 8 v2; MCell (LMem (padd q 16)) 8 v3;
      MCell (LMem (padd q 24)) 4 v4; MCell (LMem (padd q 28)) 4 v5; MCell (LMem (padd q 32)) 8 v6]).
  { destruct x as [pr nx| |a]; eexists _, _, _, _, _, _; reflexivity. }
  destruct Cs as (v1 & v2 & v3 & v4 & v5 & v6 & Ec). rewrite Ec in D.
  pose proof (D _ ltac:(left; reflexivity)) as D1. pose proof (D _ ltac:(right; left; reflexivity)) as D2.
  pose proof (D _ ltac:(right; right; left; reflexivity)) as D3. pose proof (D _ ltac:(right; right; right; left; reflexivity)) as D4.
  pose proof (D _ ltac:(right; right; right; right; left; reflexivity)) as D5. pose proof (D _ ltac:(right; right; right; right; right; left; reflexivity)) as D6.
  clear D Ec HPW Hc Hq HK. unfold ranges_disjoint, cell_range in *. cbn [fst snd mc_loc mc_w] in *. rewrite !loc_padd in *.
  cbn [Z.of_nat Pos.of_succ_nat] in *. set (Q := loc_addr L (LMem q)) in *. set (A := loc_addr L (mc_loc c)) in *.
  set (W := Z.of_nat (mc_w c)) in *. assert (1 <= W) by (unfold W; lia). clearbody Q A W. lia.
Qed.

(* [comment removed for export] *)
Lemma ctx_vs_gpart : forall L s c1 c2, PW L s -> In c1 (ctx_cells s) -> In c2 (gpart s) -> ranges_disjoint (cell_range L c1) (cell_range L c2).
Proof.
  intros L s c1 c2 HPW H1 H2. unfold PW in HPW. rewrite image_parts, app_assoc in HPW.
  apply (pw_cross L _ _ c1 c2 HPW); [apply in_app_iff; left; exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma repr_x_wcell : forall L s s' m EXC (cn : mcell) (a : Z),
  repr_x L s (bview SEGS m) EXC -> st_areas s' = st_areas s -> st_regions s' = st_regions s -> RS L s' s ->
  (forall c, In c (image s') -> In c (image s) \/ c = cn) -> In cn (image s') ->
  (forall z, mc_val cn <> VLo5 z) -> (mc_w cn <= 8)%nat -> loc_addr L (mc_loc cn) = a -> 0 <= a -> a + Z.of_nat (mc_w cn) <= 2^64 ->
  repr_x L s' (bview SEGS (wbytes m (wa a) (word_to_le_bytes (mc_w cn) (wa (sval_num L (mc_val cn)))))) EXC.
Proof.
  intros L s s' m EXC cn a HR Ea Er HRS Hcov Hin Hv Hw Ea' Ha1 Ha2.
  set (m' := wbytes m (wa a) (word_to_le_bytes (mc_w cn) (wa (sval_num L (mc_val cn))))).
  assert (Hlen : length (word_to_le_bytes (mc_w cn) (wa (sval_num L (mc_val cn)))) = mc_w cn) by apply length_Z_to_le_bytes.
  assert (Hg : mem_grows m m') by apply wbytes_grows.
  pose proof (image_cell_width s' cn Hin) as Hw1.
  apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [cn] HR Ea Er HRS (fun x E => bview_grow_n m m' x Hg E)).
  - intros c Hc. destruct (Hcov c Hc) as [H|H]; [left; exact H | right; rewrite H; left; reflexivity].
  - intros c [<-|[]]. exact Hin.
  - constructor; [|constructor]. apply holds_of_mem; [exact Hv | exact Hw | rewrite Ea'; exact Ha1 | rewrite Ea'; exact Ha2 |].
    intros k Hk. rewrite Ea'. unfold m'. apply wbytes_at_wa; [exact Ha1 | rewrite Hlen; exact Ha2 | rewrite Hlen; exact Hk].
  - intros x Hx. left. exists cn. split; [left; reflexivity|]. pose proof (bview_ne_range m m' x Hx) as Rx.
    unfold in_rng, cell_range. rewrite Ea'. cbn [fst snd]. destruct (decide (a <= x < a + Z.of_nat (mc_w cn))) as [A|A]; [exact A|].
    exfalso. apply Hx. apply bview_ext. unfold m'. apply MngWb.wbytes_out; [rewrite u_wa_small by lia; rewrite Hlen; exact Ha2 | exact Rx |].
    rewrite u_wa_small by lia. rewrite Hlen. lia.
Qed.

(* [comment removed for export] *)
Lemma rx_ctx_wr : forall L s m EXC, repr_x L s (bview SEGS m) EXC -> ly_ctx L = 0x95ed8 ->
  forall o n, 0 <= o -> o + Z.of_nat n <= 928 -> store_ok SEGS m (wa (614104 + o)) n = true.
Proof.
  intros L s m EXC (_ & _ & _ & HF) Hctx o n Ho Hn.
  assert (Hin : In (LCtx 0, CTX_SIZE) (footprint s)) by (unfold footprint; left; reflexivity).
  apply (store_ok_of_bytes SEGS m 614104 928); [|exact Ho | exact Hn].
  intros j Hj. pose proof (proj1 (Forall_forall _ _) HF _ Hin (614104 + j)) as Hm. cbn [fst snd loc_addr] in Hm. rewrite Hctx in Hm. unfold CTX_SIZE in Hm.
  specialize (Hm ltac:(lia)). destruct (bview SEGS m (614104 + j)) as [z|] eqn:Ez; [|exfalso; exact (Hm eq_refl)].
  exact (proj1 (proj2 (bview_some SEGS m _ z Ez))).
Qed.
