(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMallocA AMallocI AMalmys AMal9l1 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeT AFreeHc AFreeDc AFreeH2c AFreeW2c ACoresk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeDc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeW2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AFreeB1 AFreeB2 ATransp AFreeB3 AFreeB4 AFreeB4c AFreeB5.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB5.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
(* [comment removed for export] *)
Lemma pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma u32s_entry : forall (mm : mem) a ws i w, bytes_at rsegs mm a (u32s ws) -> nth_error ws i = Some w ->
  bytes_at rsegs mm (a + 4 * Z.of_nat i) (le4 w).
Proof.
  intros mm a ws. revert a. induction ws as [|x ws IH]; intros a i w B E; [destruct i; discriminate|].
  cbn [u32s] in B. apply bytes_at_app in B as [B0 B1]. rewrite length_le4 in B1. destruct i as [|i].
  - injection E as ->. rewrite Z.mul_0_r, Z.add_0_r. exact B0.
  - cbn in E. replace (a + 4 * Z.of_nat (S i)) with (a + Z.of_nat 4 + 4 * Z.of_nat i) by lia. exact (IH _ i w B1 E).
Qed.
Lemma nth_error_removelast : forall (l : list Z) i x, nth_error (removelast l) i = Some x -> nth_error l i = Some x.
Proof.
  intros l i x E. destruct l as [|y l'] eqn:El; [destruct i; discriminate|]. rewrite <- El in *.
  assert (NE' : l <> []) by (subst l; discriminate).
  rewrite (removelast_app_last l 0 NE'). rewrite nth_error_app1; [exact E|]. apply nth_error_Some. rewrite E. discriminate.
Qed.
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma last_nth : forall {X} (l : list X) d, last l d = nth (length l - 1) l d.
Proof.
  induction l as [|x l IH]; intros d; [reflexivity|]. destruct l as [|y l']; [reflexivity|].
  change (last (x :: y :: l') d) with (last (y :: l') d). rewrite IH.
  change (length (x :: y :: l') - 1)%nat with (S (length l')). change (length (y :: l') - 1)%nat with (length l' - 0)%nat.
  rewrite Nat.sub_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma batches_repr_append : forall (mm mm' : mem) sb l bl b',
  batches_repr LPA mm sb (l ++ [bl]) ->
  (forall x, In x l \/ x = bl -> forall i, (i < length (ba_entries x))%nat -> Z.of_nat i < 1021) ->
  (forall x a', In x l -> batch_addr sb x <= a' < batch_addr sb x + kQuarantineBatchBytes -> mm' (Z_to_bv 64 a') = mm (Z_to_bv 64 a')) ->
  (forall a', batch_addr sb bl + 8 <= a' < batch_addr sb bl + kQuarantineBatchBytes -> mm' (Z_to_bv 64 a') = mm (Z_to_bv 64 a')) ->
  u64_at rsegs mm' (batch_addr sb bl + off_qb_next) (batch_addr sb b') ->
  mapped mm' (batch_addr sb bl) kQuarantineBatchBytes ->
  (let a := batch_addr sb b' in
   u64_at rsegs mm' (a + off_qb_next) 0 /\ u64_at rsegs mm' (a + off_qb_size) (batch_bytes b') /\
   u64_at rsegs mm' (a + off_qb_count) (Z.of_nat (length (ba_entries b'))) /\
   (forall i e, nth_error (ba_entries b') i = Some e -> u64_at rsegs mm' (a + off_qb_batch (Z.of_nat i)) (hdr_of sb (qe_chunk e) (qe_n e))) /\
   mapped mm' a kQuarantineBatchBytes) ->
  batches_repr LPA mm' sb (l ++ [bl; b']).
Proof.
  intros mm mm' sb l. induction l as [|x l IH]; intros bl b' H LEN AG AGL NX MB NEW.
  - cbn [batches_repr app] in H |- *. cbv zeta in NEW. (first [ dand6 H as Hn Hs Hc He Hm _ | destruct H as (Hn & Hs & Hc & He & Hm & _) ]). (first [ dand5 NEW as N1 N2 N3 N4 N5 | destruct NEW as (N1 & N2 & N3 & N4 & N5) ]).
    unfold off_qb_next, off_qb_size, off_qb_count, off_qb_batch, kQuarantineBatchBytes in *.
    split; [exact NX|]. split; [eapply u64_at_agree; [exact Hs|]; intros i Hi; apply AGL; lia|].
    split; [eapply u64_at_agree; [exact Hc|]; intros i Hi; apply AGL; lia|].
    split.
    { intros i e Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as IL. assert (Z.of_nat i < 1021) by (apply (LEN bl); [right; reflexivity| exact IL]).
      eapply u64_at_agree; [exact (He i e Hi)|]. intros j Hj. apply AGL. lia. }
    split; [exact MB|]. split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5| exact I].
  - cbn [batches_repr app] in H |- *. (first [ dand6 H as Hn Hs Hc He Hm Hr | destruct H as (Hn & Hs & Hc & He & Hm & Hr) ]).
    assert (AGx : forall a', batch_addr sb x <= a' < batch_addr sb x + 8192 -> mm' (Z_to_bv 64 a') = mm (Z_to_bv 64 a'))
      by (intros a' Ha'; apply (AG x); [left; reflexivity| unfold kQuarantineBatchBytes; exact Ha']).
    unfold off_qb_next, off_qb_size, off_qb_count, off_qb_batch in *.
    split; [| split; [| split; [| split; [| split]]]].
    + destruct l as [|y l']; cbn [app] in Hn |- *; eapply u64_at_agree; [exact Hn| | exact Hn|]; intros i Hi; apply AGx; lia.
    + eapply u64_at_agree; [exact Hs|]. intros i Hi. apply AGx. lia.
    + eapply u64_at_agree; [exact Hc|]. intros i Hi. apply AGx. lia.
    + intros i e Hi. eapply u64_at_agree; [exact (He i e Hi)|]. intros j Hj.
      pose proof (nth_error_Some_lt _ _ _ Hi) as IL. assert (Z.of_nat i < 1021) by (apply (LEN x); [left; left; reflexivity| exact IL]).
      apply AGx. lia.
    + eapply mapped_agree_gen; [exact Hm|]. intros i Hi. apply AGx. unfold kQuarantineBatchBytes in Hi. lia.
    + apply (IH bl b' Hr); [| | exact AGL| exact NX| exact MB| exact NEW].
      * intros y Hy. apply LEN. destruct Hy as [Hy| ->]; [left; right; exact Hy| right; reflexivity].
      * intros y a' Hy Ha'. apply (AG y); [right; exact Hy| exact Ha'].
Qed.

End CEIL.

Section FreeHitsCore.
Context {Clg : Ceiling}.
  Variables (rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet).
  (* [comment removed for export] *)
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis MI : mem_inv rsegs (aview_of (pa_hull A) m).
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis IAT : a_ia_inited A = true.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HISP : hi <= 2^47.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis RA2 : bv_unsigned rac mod 2 = 0.
  Hypothesis ST : stk rsegs (aview_of (pa_hull A) m) lo (bv_unsigned spd).
  Hypothesis SMH : mapped (aview_of (pa_hull A) m) (bv_unsigned spd) (hi - bv_unsigned spd).
  Hypothesis STLO : bv_unsigned spd <= stkobj.
  Hypothesis STHI : stkobj + 2064 <= hi.
  Hypothesis STO : ro_cells rsegs (aview_of (pa_hull A) m) stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRW : bytes_at rsegs (aview_of (pa_hull A) m) (stkobj + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  Hypothesis NQ : n0 <= 2^28.
  (* [comment removed for export] *)
  Hypothesis KK : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          a_pl A' = a_pl A ->
          as_live A' p = None -> (forall q, q <> p -> as_live A' q = as_live A q) ->
          as_livebytes A' = as_livebytes A - n0 -> as_tinycred A' = as_tinycred A -> as_seccred A' = as_seccred A -> as_primcred A' = as_primcred A (* [comment removed for export] *) ->
          as_nlive A' = as_nlive A - (if Z.eqb p 0 then 0 else 1) ->
          (forall c, c <> kQuarantineBatchClass -> a_virgin A c -> a_virgin A' c) ->
          (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) (aview_of (pa_hull A) m) (wz (cl_errno LPA + i))) ->
          frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) (newblk p n0) nowhere (aview_of (pa_hull A) m) v' ->
          (forall a, bv_unsigned spd <= a < hi -> v' (wz a) = aview_of (pa_hull A) m (wz a)) ->
          stk (cl_segs LPA) v' lo (bv_unsigned spd) ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR rac spd gp (cl_tp LPA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom (cl_segs LPA))) md') T.
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).

  (* [comment removed for export] *)
  Local Ltac prefix :=
    cbn [cl_segs cl_free_pc LPA] in MI, KK |- *;
    (cbn [cl_segs cl_free_pc LPA] in MI |- *);
    (pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0);
    (pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A (aview_of (pa_hull A) m)) as AR);
    (assert (SPH : uspd <= 2^47) by (clear -SPHI HISP; lia));
    (pose proof alloc_ceiling_val as CE);
    (pose proof (zr_word spd) as SPR; unfold inr64 in SPR);
    (pose proof (zr_word rac) as RAR; unfold inr64 in RAR);
    (destruct (free_li A p n0 HL) as (li & LU & LN));
    (destruct (free_n0 A m md p n0 AI HL) as [NR US]);
    (unfold REQ_MAX in NR);
    ((first [ pose proof ((free_geom A m md p n0 AI HL)) as dR_4; dand4 dR_4 as PAL PLO PCE PHI | destruct (free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]));
    (pose proof (GEO A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as Gx0);
    (assert (PNB : 0x60a000 <= p + -16) by (clear -Gx0; lia)); (clear Gx0);
    ((first [ pose proof ((free_HDR A m md p n0 AI HL)) as dR_5; dex2 dR_5 as b1 ido; dand6 dR_5 as B1R B1M3 B1M IDR HDR CTXID | pose proof ((free_HDR A m md p n0 AI HL)) as dR_5; dand8 dR_5 as b1 ido B1R B1M3 B1M IDR HDR CTXID | destruct (free_HDR A m md p n0 AI HL) as (b1 & ido & B1R & B1M3 & B1M & IDR & HDR & CTXID) ]));
    (destruct (free_CTX0 A m md p n0 AI HL) as (old & CTX0));
    (pose proof (free_SHC A m md p n0 AI HL) as SHC);
    (pose proof (free_FCo A m md AI) as FCo);
    ((first [ pose proof ((free_TST A m md AI)) as dR_6; dex2 dR_6 as fr fd; dand3 dR_6 as FRR FDR TST | pose proof ((free_TST A m md AI)) as dR_6; dand5 dR_6 as fr fd FRR FDR TST | destruct (free_TST A m md AI) as (fr & fd & FRR & FDR & TST) ]));
    (pose proof (free_sep A m md p n0 AI HL) as SEPp);
    (cbv zeta in SEPp);
    ((first [ dand4 SEPp as SEP_pc SEP_pt SEP_pn SEP_pf | destruct SEPp as (SEP_pc & SEP_pt & SEP_pn & SEP_pf) ]));
    ((first [ pose proof ((hit_sep A m md AI)) as dR_8; dand13 dR_8 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]));
    ((first [ pose proof ((hit_place A m md AI)) as dR_9; dand7 dR_9 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]));
    ((first [ pose proof ((hit_depot_wf A m md AI)) as dR_10; dand5 dR_10 as DND DLEN _ DKEY _ | pose proof (hit_depot_wf A m md AI) as (DND & DLEN & _ & DKEY & _) ]));
    (pose proof (hit_DR A m md AI) as DR0);
    (pose proof (hit_TC A m md AI) as TC);
    (pose proof (hit_tsd A m md AI) as [TSD1 TSD2]);
    (assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia));
    (assert (LO : alloc_ceiling <= lo /\ lo <= uspd - 704) by (clear -CEIL LOW; lia));
    (* [comment removed for export] *)
    (assert (KL : (1 <= length key <= 255)%nat /\ depot_total (a_depot A) + 256 < kStackStoreBlockFrames) by
      (destruct (wfD A WF0) as (INC & ND & NN); pose proof (wfP A WF0) as PL; pose proof (wf_place_dkeys _ _ PL) as DK;
       destruct DK as (DK1 & DK2 & DK3); clear PL;
       assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros k Hk; exact (proj1 (Forall_forall _ _) INC k Hk));
       pose proof (depot_universe_bounds _ _ DK1 DK3 ND INC') as (L1 & _ & L3);
       split; [exact (proj1 (Forall_forall _ _) DK1 key KEYU)| unfold kStackStoreBlockFrames; clear -L1 L3; lia]));
    (destruct KL as [KL DTOT]);
    (assert (STOR : uspd <= stkobj /\ stkobj + 2064 <= 2^47) by (clear -STLO STHI HISP; lia));
    (assert (TPE : cl_tp LPA = wz TP) by reflexivity);
    (pose proof (Z_div_mod_eq_full (n0 + 7) 8) as NDE);
    (pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)) as ER);
    (assert (R8 : 8 * ((n0 + 7) / 8) - 8 < n0 <= 8 * ((n0 + 7) / 8)) by lia);
    (assert (IDR' : 0 <= snd (depot_putC (a_depot A) key) < 2^32) by (pose proof (depot_putC_id_range (a_depot A) key); lia)).

  (* [comment removed for export] *)
  Definition tailQt (tk : ftail) (qt' : list batch) : list batch := match tk with TN => qt' | _ => [] end.
  Definition tailQg (tk : ftail) (qt' qg : list batch) : list batch := match tk with TN => qg | _ => qg ++ qt' end.

  Lemma tailQ_entries : forall tk qt' qg e, In e (q_entries (tailQt tk qt' ++ tailQg tk qt' qg)) <-> In e (q_entries (qt' ++ qg)).
  Proof.
    intros tk qt' qg e. unfold q_entries. destruct tk; cbn [tailQt tailQg app]; [tauto| |]; rewrite !flat_map_app, !in_app_iff; tauto.
  Qed.
  Lemma tailQ_batches : forall tk qt' qg b, In b (tailQt tk qt' ++ tailQg tk qt' qg) <-> In b (qt' ++ qg).
  Proof. intros tk qt' qg b. destruct tk; cbn [tailQt tailQg app]; [tauto| |]; rewrite !in_app_iff; tauto. Qed.

  #[using="KK NQ KR KEYU TRW STO STHI STLO SMH ST RA2 HISP SPHI LOW CEIL IAT HL MI AI key hi lo Clg"] Theorem dealloc_new0G : forall tk : ftail,
    a_qthread A = [] -> pk_chunks (a_cache A kQuarantineBatchClass) <> [] ->
    match tk with
    | TN => n0 + kQuarantineBatchBytes <= kQuarantineCacheSize
    | T0 => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A = [] /\ n0 + kQuarantineBatchBytes <= kQuarantineMaxSize
    | TA => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A <> [] /\ q_bytes (a_qglobal A) + (n0 + kQuarantineBatchBytes) <= kQuarantineMaxSize
    end ->
    srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.
  Proof.
    intros tk QTE NE24 TKC. unfold dealloc_entry_ms. prefix.
    pose proof (free_QC A m md AI) as QC. rewrite QTE in QC. cbn [length Z.of_nat qc_first qc_last q_bytes fold_right] in QC.
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    (first [ pose proof ((cl_kidx A m md kQuarantineBatchClass AI C24 NE24)) as dR_11; dand5 dR_11 as KE KIN KB CNT ND24 | destruct (cl_kidx A m md kQuarantineBatchClass AI C24 NE24) as (KE & KIN & KB & CNT & ND24) ]).
    (first [ pose proof ((cl_PC A m md kQuarantineBatchClass AI C24 NE24)) as dR_12; dex1 dR_12 as ks; dand5 dR_12 as LKS KW KSM KSF PC24 | pose proof ((cl_PC A m md kQuarantineBatchClass AI C24 NE24)) as dR_12; dand6 dR_12 as ks LKS KW KSM KSF PC24 | destruct (cl_PC A m md kQuarantineBatchClass AI C24 NE24) as (ks & LKS & KW & KSM & KSF & PC24) ]).
    pose proof (cl_ci A m md kQuarantineBatchClass AI C24 NE24) as CI.
    set (ks24 := pk_chunks (a_cache A kQuarantineBatchClass)) in *.
    set (kb := nth (length ks24 - 1) ks24 0) in *. set (cnt := Z.of_nat (length ks24)) in *.
    assert (KQ : kb * class_size kQuarantineBatchClass / kCompactPtrScale = kb * 512).
    { rewrite class_size_24. unfold kCompactPtrScale, kQuarantineBatchBytes. replace (kb * 8192) with ((kb * 512) * 16) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite KQ in KW. set (kw := Z_to_bv 64 (kb * 512)) in *.
    pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ (conj C24 KB)) as W24.
    assert (KWV : bv_unsigned kw = kb * 512).
    { subst kw. unfold chunk_addr in W24. rewrite class_size_24 in W24. unfold kQuarantineBatchBytes in W24. rewrite unsigned_lit; [reflexivity|]. clear -KB W24 CE; try pose proof alloc_ceiling_val. kung_all. lia. }
    set (b := chunk_addr (a_sb A) kQuarantineBatchClass kb).
    assert (BE : a_sb A + 24 * 2^32 + 16 * bv_unsigned kw = b) by (subst b; rewrite KWV; unfold chunk_addr; rewrite class_size_24; unfold kQuarantineBatchBytes, kQuarantineBatchClass, region_beg, kRegionSize; lia).
    pose proof (cached_carved A (aview_of (pa_hull A) m) AR kQuarantineBatchClass kb C24 KIN) as CKB.
    pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ CKB) as WB. fold b in WB.
    pose proof (KN A (aview_of (pa_hull A) m) p n0 li AR LU LN) as KNp. pose proof (known_carved A (aview_of (pa_hull A) m) AR _ _ KNp) as CVp.
    pose proof (GEO A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as G.
    (first [ pose proof ((sb_facts A WF0)) as dR_13; dand5 dR_13 as _ SBA HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & SBA & HB6 & RSB & SCE) ]).
    assert (Abt : apart b 8192 (p_thr (a_pl A)) 4096).
    { pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ CKB) as D. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in D. subst b. try (generalize alloc_ceiling_val); clear -D; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, kQuarantineBatchBytes in *. lia. }
    assert (Abc : apart b 8192 (p_ctx (a_pl A)) 0x10000).
    { pose proof (carved_apart_ctx A (aview_of (pa_hull A) m) AR _ CKB) as D. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in D. subst b. try (generalize alloc_ceiling_val); clear -D; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, kQuarantineBatchBytes in *. lia. }
    assert (Abn : apart b 8192 (p_nodes0 (a_pl A)) kDepotNodesBlock).
    { pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ CKB) as D. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in D. subst b. try (generalize alloc_ceiling_val); clear -D; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, kQuarantineBatchBytes in *. lia. }
    assert (Abf : apart b 8192 (p_frames0 (a_pl A)) kStackStoreBlockBytes).
    { pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ CKB) as D. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in D. subst b. try (generalize alloc_ceiling_val); clear -D; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, kQuarantineBatchBytes in *. lia. }
    assert (Abp : apart b 8192 (p + -16) (8 * ((n0 + 7) / 8) + 16)).
    { pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ CKB CVp ltac:(intros E; exact (live_not_cached A (aview_of (pa_hull A) m) AR p li kQuarantineBatchClass kb LU C24 KIN (eq_sym E)))) as D.
      rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in D. subst b. (first [ dand5 G as _ _ L1 L2 _ | destruct G as (_ & _ & L1 & L2 & _) ]). try (generalize alloc_ceiling_val); clear -D L1 L2; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, kQuarantineBatchBytes in *. lia. }
    assert (BLO : kHighMemBeg <= b) by (try (generalize alloc_ceiling_val); clear -WB; try pose proof alloc_ceiling_val; lia).
    assert (BHI : b + 8192 <= alloc_ceiling) by (try (generalize alloc_ceiling_val); clear -WB CE C24; try pose proof alloc_ceiling_val; rewrite class_size_24 in WB; unfold kQuarantineBatchBytes in WB; kung_all; lia).
    (* [comment removed for export] *)
    (first [ pose proof ((ar_cache _ _ _ _ _ (proj2 AR))) as dR_15; dand5 dR_15 as _ _ _ TM _ | destruct (ar_cache _ _ _ _ _ (proj2 AR)) as (_ & _ & _ & TM & _) ]).
    destruct (mapped_C8 (aview_of (pa_hull A) m) (p_thr (a_pl A) + 208 + 2576) ltac:(intros i Hi; replace (p_thr (a_pl A) + 208 + 2576 + i) with (p_thr (a_pl A) + (2784 + i)) by lia; apply TM; lia)
                ltac:(try (generalize alloc_ceiling_val); clear -TH1; apply aobj_facts in TH1; try pose proof alloc_ceiling_val; kung_all; lia) ltac:(try (generalize alloc_ceiling_val); clear -TH2; try pose proof alloc_ceiling_val; lia)) as [statv STA].
    (first [ pose proof ((ar_regions _ _ _ _ _ (proj2 AR) kQuarantineBatchClass C24)) as dR_16; dand13 dR_16 as _ _ _ _ _ _ _ _ _ _ _ _ RM24 | destruct (ar_regions _ _ _ _ _ (proj2 AR) kQuarantineBatchClass C24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RM24) ]). change (p_sb (a_pl A)) with (a_sb A) in RM24.
    assert (BM : mapped (aview_of (pa_hull A) m) b 8192).
    { intros i Hi. replace (b + i) with (region_beg (a_sb A) kQuarantineBatchClass + (b - region_beg (a_sb A) kQuarantineBatchClass + i)) by lia. apply RM24.
      try (generalize alloc_ceiling_val); clear -WB Hi C24; try pose proof alloc_ceiling_val. rewrite class_size_24 in WB. unfold kQuarantineBatchBytes in WB. lia. }
    destruct (mapped_C8 (aview_of (pa_hull A) m) b ltac:(intros i Hi; apply BM; lia) ltac:(try (generalize alloc_ceiling_val); clear -BLO; try pose proof alloc_ceiling_val; kung_all; lia) ltac:(try (generalize alloc_ceiling_val); clear -BHI; try pose proof alloc_ceiling_val; lia)) as [bj0 BC0].
    destruct (mapped_C8 (aview_of (pa_hull A) m) (b + 8) ltac:(intros i Hi; replace (b + 8 + i) with (b + (8 + i)) by lia; apply BM; lia) ltac:(try (generalize alloc_ceiling_val); clear -BLO; try pose proof alloc_ceiling_val; kung_all; lia) ltac:(try (generalize alloc_ceiling_val); clear -BHI; try pose proof alloc_ceiling_val; lia)) as [bj1 BC1].
    destruct (mapped_C8 (aview_of (pa_hull A) m) (b + 16) ltac:(intros i Hi; replace (b + 16 + i) with (b + (16 + i)) by lia; apply BM; lia) ltac:(try (generalize alloc_ceiling_val); clear -BLO; try pose proof alloc_ceiling_val; kung_all; lia) ltac:(try (generalize alloc_ceiling_val); clear -BHI; try pose proof alloc_ceiling_val; lia)) as [bj2 BC2].
    destruct (mapped_C8 (aview_of (pa_hull A) m) (b + 24) ltac:(intros i Hi; replace (b + 24 + i) with (b + (24 + i)) by lia; apply BM; lia) ltac:(try (generalize alloc_ceiling_val); clear -BLO; try pose proof alloc_ceiling_val; kung_all; lia) ltac:(try (generalize alloc_ceiling_val); clear -BHI; try pose proof alloc_ceiling_val; lia)) as [bj3 BC3].
    assert (BC : rw_cells rsegs (aview_of (pa_hull A) m) b [C8 bj0; C8 bj1; C8 bj2; C8 bj3]).
    { apply (rw_cells_app_join _ _ [C8 bj0] [C8 bj1; C8 bj2; C8 bj3]); [exact BC0|]. cbn [cells_size csize Nat.add]. replace (b + Z.of_nat 8) with (b + 8) by lia.
      apply (rw_cells_app_join _ _ [C8 bj1] [C8 bj2; C8 bj3]); [exact BC1|]. cbn [cells_size csize Nat.add]. replace (b + 8 + Z.of_nat 8) with (b + 16) by lia.
      apply (rw_cells_app_join _ _ [C8 bj2] [C8 bj3]); [exact BC2|]. cbn [cells_size csize Nat.add]. replace (b + 16 + Z.of_nat 8) with (b + 24) by lia. exact BC3. }
    assert (KSMW : bv_unsigned kw < 2^32) by (rewrite KWV; try (generalize alloc_ceiling_val); clear -KB W24 C24; try pose proof alloc_ceiling_val; unfold chunk_addr in W24; rewrite class_size_24 in W24; unfold kQuarantineBatchBytes in W24; kung_all; lia).
    assert (NR' : 1 <= n0 < 2^32) by (try (generalize alloc_ceiling_val); clear -NR; try pose proof alloc_ceiling_val; lia).
    assert (PHI' : p + 8 * ((n0 + 7) / 8) <= alloc_ceiling) by (try (generalize alloc_ceiling_val); clear -PHI CE; try pose proof alloc_ceiling_val; lia).
    assert (SB1 : a_sb A + 2^37 <= 2^47) by (try (generalize alloc_ceiling_val); clear -SCE CE; try pose proof alloc_ceiling_val; kung_all; lia).
    rewrite <- BE in BC.
    (* [comment removed for export] *)
    assert (QWF : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> 0 <= qe_n e).
    { intros e He. destruct (qentry_wf A (aview_of (pa_hull A) m) AR e He) as [N _]. lia. }
    assert (QBall : forall bs, (forall e, In e (q_entries bs) -> 0 <= qe_n e) -> Z.of_nat (length bs) * kQuarantineBatchBytes <= q_bytes bs).
    { clear. intros bs QW. induction bs as [|b0 r IH]; [cbn; lia|]. rewrite q_bytes_cons, batch_bytes_ebytes. cbn [length]. rewrite Nat2Z.inj_succ.
      assert (IHr : Z.of_nat (length r) * kQuarantineBatchBytes <= q_bytes r) by (apply IH; intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; right; exact He).
      assert (EW : forall e, In e (ba_entries b0) -> 0 <= qe_n e) by (intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; left; exact He).
      assert (0 <= ebytes (ba_entries b0)); [| lia].
      clear -EW. induction (ba_entries b0) as [|e es IHe]; [cbn; lia|].
      rewrite ebytes_cons. unfold qe_bytes. pose proof (user_size_pos (qe_n e) ltac:(apply EW; left; reflexivity)).
      assert (0 <= ebytes es) by (apply IHe; intros e' He'; apply EW; right; exact He'). lia. }
    assert (LENG : Z.of_nat (length (a_qglobal A)) * kQuarantineBatchBytes <= q_bytes (a_qglobal A)).
    { apply QBall. intros e He. apply QWF. unfold q_entries in He |- *. rewrite flat_map_app. apply in_or_app. right. exact He. }
    assert (GQ0 : 0 <= q_bytes (a_qglobal A)) by (clear -LENG; unfold kQuarantineBatchBytes in LENG; lia).
    pose proof (batches_nodup A (aview_of (pa_hull A) m) AR) as BND0. pose proof BND0 as BND. rewrite QTE in BND. cbn [app] in BND.
    (* [comment removed for export] *)
    set (gn := Z.of_nat (length (a_qglobal A))). set (gf := qc_first A (a_qglobal A)). set (gl := qc_last A (a_qglobal A)). set (gqb := q_bytes (a_qglobal A)) in *.
    assert (TPRE : tail_pre tk gn gf gl gqb (wz 0) (aview_of (pa_hull A) m)).
    { destruct tk; cbn [tail_pre]; [exact I| |].
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). split; [exact (q_lockword A _ AR)|]. pose proof (q_global_hdr A _ AR) as X. subst gn gf gl gqb. rewrite QGE in X |- *. exact X.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). split; [exact (q_lockword A _ AR)|]. split; [exact (q_global_hdr A _ AR)| exact (proj1 (q_gl_cell A _ AR QGN))]. }
    assert (TOK : tail_ok tk gn gqb (0 + (n0 + 8192))).
    { destruct tk; cbn [tail_ok].
      - unfold kQuarantineCacheSize, kQuarantineBatchBytes in TKC. clear -TKC. lia.
      - (first [ dand3 TKC as T1 QGE T3 | destruct TKC as (T1 & QGE & T3) ]). subst gqb. rewrite QGE, q_bytes_nil. unfold kQuarantineCacheSize, kQuarantineMaxSize, kQuarantineBatchBytes in *. clear -T1 T3. lia.
      - (first [ dand3 TKC as T1 QGN T3 | destruct TKC as (T1 & QGN & T3) ]). subst gn gqb. unfold kQuarantineCacheSize, kQuarantineMaxSize, kQuarantineBatchBytes in *.
        assert (Z.of_nat (length (a_qglobal A)) <> 0) by (destruct (a_qglobal A); [congruence| cbn; lia]). clear -T1 T3 LENG H GQ0 NR. lia. }
    set (glb := last (a_qglobal A) (BA 0 [])).
    assert (GLX : a_qglobal A <> [] ->
              gl = batch_addr (a_sb A) glb /\ In glb (a_qthread A ++ a_qglobal A) /\ kHighMemBeg <= gl /\ gl + kQuarantineBatchBytes <= alloc_ceiling /\
              carved A (ChP (CP kQuarantineBatchClass (ba_idx glb))) /\ ChP (CP kQuarantineBatchClass (ba_idx glb)) <> ChP (CP kQuarantineBatchClass kb) /\ In glb (a_qglobal A)).
    { intros QGN. (first [ pose proof ((q_gl_cell A _ AR QGN)) as dR_21; dand5 dR_21 as _ E INg R1 R2 | destruct (q_gl_cell A _ AR QGN) as (_ & E & INg & R1 & R2) ]).
      split; [exact E|]. split; [exact INg|]. split; [exact R1|]. split; [exact R2|]. split; [exact (batch_carved A (aview_of (pa_hull A) m) AR glb INg)|].
      assert (INg' : In glb (a_qglobal A)) by (subst glb; pattern (a_qglobal A) at 2; rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN); apply in_or_app; right; left; reflexivity).
      split; [exact (batch_not_cached A (aview_of (pa_hull A) m) AR glb kQuarantineBatchClass kb INg C24 KIN)| exact INg']. }
    assert (TAP : tail_apart tk gl (p_thr (a_pl A)) p ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) [b]).
    { destruct tk; cbn [tail_apart]; [exact I| exact I|]. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_23; dand7 dR_23 as E INg R1 R2 Cg NKb _ | destruct (GLX QGN) as (E & INg & R1 & R2 & Cg & NKb & _) ]).
      pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cg) as Dn.
      pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cg) as Df.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CVp ltac:(intros EE; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li glb LU INg (eq_sym EE)))) as Dp.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CKB NKb) as Dk.
      rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dt, Dn, Df, Dp, Dk. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in Dk.
      (first [ dand5 G as _ _ L1 L2 _ | destruct G as (_ & _ & L1 & L2 & _) ]).
      subst b. clear -E R1 R2 Dt Dn Df Dp Dk L1 L2 CE. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try lia. constructor; [lia| constructor]. }
    (* [comment removed for export] *)
    pose proof (free_chitG_new0 rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                  (aview_of (pa_hull A) m) lo p n0 b1 pa_tsd (p_ctx (a_pl A)) (p_thr (a_pl A))
                  ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) fr fd stkobj (a_depot A) key old (shpat n0)
                  MI ST LO SPH RA2 TPE PAL PLO PNB PHI' NR' NQ R8 B1R B1M3 HDR CTX0 SHC FCo
                  (hit_PCo A m md AI) TC (hit_TH0 A m md AI) (hit_CT8 A m md AI) TSDL
                  TST FRR FDR DR0 DND DLEN DTOT (conj DN01 DN02) (conj DF01 DF02) STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc
                  tk gn gf gl gqb (wz 0) 0 cnt (max_count kQuarantineBatchClass) (a_sb A) ks kw statv bj0 bj1 bj2 bj3) as EV0.
    cbv zeta in EV0. rewrite BE in EV0.
    specialize (EV0 TPRE TOK TAP ltac:(lia) THRA CNT LKS KW KSMW ltac:(try (generalize alloc_ceiling_val); clear -HB6 RSB; try pose proof alloc_ceiling_val; kung_all; lia) SB1 BLO BHI
                    Abt Abp Abc Abn Abf (hit_SBc A m md AI) QC ltac:(subst cnt; rewrite class_size_24 in PC24; exact PC24) STA ltac:(rewrite BE in BC; exact BC)).
    rename EV0 into EV.
    idtac "walk ok".
    (* [comment removed for export] *)
    destruct (asI_minv A m md AI) as [HMI HH].
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) _ _ md T HMI HH).
    { rewrite restrict_MS. exact EV. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex17 HQ as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' v'; dand14 HQ as -> MU WM' MI' ST' Ptst Phdr Pctx Psh Pdr Pl24c Pstat Pb TPOST | dand31 HQ as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' v' -> MU WM' MI' ST' Ptst Phdr Pctx Psh Pdr Pl24c Pstat Pb TPOST | destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & v' & -> & MU & WM' & MI' & ST' & Ptst & Phdr & Pctx & Psh & Pdr & Pl24c & Pstat & Pb & TPOST) ]).
    try rewrite BE in MU. try rewrite BE in Pb. try rewrite BE in TPOST.
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v') = v').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> aview_of (pa_hull A) m (wz a) <> None -> v' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NN _ _ a WM'); lia. }
    (* [comment removed for export] *)
    pose proof G as G'. (first [ dand18 G' as PM CL1 L1 L2 CL2 _ R8' PU T1 T2 N1 N2 F1 F2 S1 S2 CEQ _ | destruct G' as (PM & CL1 & L1 & L2 & CL2 & _ & R8' & PU & T1 & T2 & N1 & N2 & F1 & F2 & S1 & S2 & CEQ & _) ]).
    (first [ pose proof ((GEOP A (aview_of (pa_hull A) m) p n0 li AR LU LN)) as dR_27; dand4 dR_27 as Gc Gt Gn Gf | pose proof (GEOP A (aview_of (pa_hull A) m) p n0 li AR LU LN) as (Gc & Gt & Gn & Gf) ]). aobj_lin1 Gc. aobj_lin1 Gt. aobj_lin1 Gn. aobj_lin1 Gf.
    pose proof (GEOS A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as Gs. unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg in Gs.
    set (BX := fun a => (p_thr (a_pl A) + 2128 <= a < p_thr (a_pl A) + 2132) \/ (p_thr (a_pl A) + 2784 <= a < p_thr (a_pl A) + 2792) \/ (b <= a < b + 32)
                        \/ (tk <> TN /\ gq_blk a) \/ (tk = TA /\ gl <= a < gl + 8) \/ (a_ia_inited A = false /\ ia_blk a)).
    assert (BXW : forall a, BX a ->
         (exists b0, In b0 (a_qthread A ++ a_qglobal A) /\ batch_addr (a_sb A) b0 <= a < batch_addr (a_sb A) b0 + kQuarantineBatchBytes)
      \/ (p_thr (a_pl A) + 2128 <= a < p_thr (a_pl A) + 2208) \/ (p_thr (a_pl A) + 2784 <= a < p_thr (a_pl A) + 2792)
      \/ (exists k, p_cached_ (a_cache A) kQuarantineBatchClass k /\
                    chunk_addr (a_sb A) kQuarantineBatchClass k <= a < chunk_addr (a_sb A) kQuarantineBatchClass k + kQuarantineBatchBytes)
      \/ xblk a).
    { intros a Ha. subst BX. cbv beta in Ha. destruct Ha as [Ha|[Ha|[Ha|[[_ Ha]|[[Htk Ha]|[_ Ha]]]]]].
      - right; left. clear -Ha. lia.
      - right; right; left. exact Ha.
      - right; right; right; left. exists kb. split; [exact KIN|]. subst b. clear -Ha. unfold kQuarantineBatchBytes. lia.
      - do 4 right. right. exact Ha.
      - subst tk. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_29; dand3 dR_29 as E INg _ | destruct (GLX QGN) as (E & INg & _) ]). left. exists glb. split; [exact INg|]. rewrite <- E. clear -Ha. unfold kQuarantineBatchBytes. lia.
      - do 4 right. left. exact Ha. }
    assert (MU' : forall a, 0 <= a < 2^64 -> ~ W0 lo uspd (p_thr (a_pl A)) p ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) a ->
                   ~ BX a -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
    { intros a Ha NW NB. apply MU. rewrite unsigned_lit by lia. unfold free_chitG_new0_W, free_cprefix_W, free_coreG_new0_W. rewrite !outside_app.
      unfold W0 in NW. subst BX. cbv beta in NB.
      split; [| split].
      - cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NW; clear -X LO; lia.
      - cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; [apply NW| apply NB| apply NB| apply NB]; clear -X; lia.
      - destruct tk; cbn [ctail_W]; [exact I| |]; unfold free_cdtail_W, free_cdtail_WA, QINST; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X;
          first [apply NW; clear -X LO; lia | apply NB; right; right; right; first [left; split; [discriminate| unfold gq_blk; clear -X; lia] | right; left; split; [reflexivity| clear -X; lia]]]. }
    (* [comment removed for export] *)
    assert (Punw : rw_cells rsegs v' (p_thr (a_pl A) + off_th_unwinding) [C1 (Z_to_bv 8 0)]).
    { pose proof Abt as Dt. unfold apart, AMallocA.apart in Dt.
      assert (Dg : tk = TA -> gl + 24 <= p_thr (a_pl A) \/ p_thr (a_pl A) + 4096 <= gl).
      { intros ->. (first [ dand6 TAP as _ _ _ _ Agt _ | destruct TAP as (_ & _ & _ & _ & Agt & _) ]). clear -Agt. unfold apart, AMallocA.apart in Agt. lia. }
      eapply rw_cells_transport; [exact (hit_TUNW A m md AI)| exact MU| exact WM'|].
      unfold free_chitG_new0_W, free_cprefix_W, free_coreG_new0_W, off_th_unwinding.
      pose proof SEP_pt as Dp. pose proof SEP_n0t as Dn. pose proof SEP_f0t as Df. unfold apart, AMallocA.apart in Dp, Dn, Df.
      destruct tk; [| | specialize (Dg eq_refl)]; cbn [ctail_W free_cdtail_W free_cdtail_WA app disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; unfold QINST;
        clear -Dt Dp Dn Df Dg T1 T2 L1 L2 CL1 CE CEIL LOW N1 F1 S1 S2 Gc Gt Gn Gf Gs NR R8; kung_all; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    assert (NGQ : tk = TN -> forall a, BX a -> ~ gq_blk a).
    { intros -> a HB GQ. subst BX. cbv beta in HB. destruct HB as [X|[X|[X|[[X _]|[[X _]|[_ X]]]]]]; [| | | exact (X eq_refl)| discriminate|].
      - clear -X GQ Gt. unfold gq_blk in *. kung_all. lia.
      - clear -X GQ Gt. unfold gq_blk in *. kung_all. lia.
      - clear -X GQ BLO. unfold gq_blk, kHighMemBeg in *. lia.
      - clear -X GQ. unfold gq_blk, ia_blk in *. lia. }
    assert (NBXg : forall g a, In g (a_qglobal A) -> batch_addr (a_sb A) g <= a < batch_addr (a_sb A) g + kQuarantineBatchBytes -> tk = TN -> ~ BX a).
    { intros g a Hg Ha -> HB. assert (INg : In g (a_qthread A ++ a_qglobal A)) by (apply in_or_app; right; exact Hg).
      pose proof (batch_carved A (aview_of (pa_hull A) m) AR g INg) as Cg.
      pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as Dt.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CKB (batch_not_cached A (aview_of (pa_hull A) m) AR g kQuarantineBatchClass kb INg C24 KIN)) as Dk.
      rewrite (proj1 (c24_range A (ba_idx g))), (proj2 (c24_range A (ba_idx g))) in Dt, Dk. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in Dk.
      pose proof (batch_range A (aview_of (pa_hull A) m) AR g INg) as (Rg1 & _).
      subst BX b. cbv beta in HB. destruct HB as [X|[X|[X|[[X _]|[[X _]|[_ X]]]]]]; [| | | exact (X eq_refl)| discriminate|].
      - clear -Ha Dt X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
      - clear -Ha Dt X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
      - clear -Ha Dk X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
      - clear -Ha Rg1 X. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia. }
    (* [comment removed for export] *)
    set (fe := free_entry li). set (b' := BA kb [fe]). set (qt' := [b']). set (cache' := cache_set (a_cache A) kQuarantineBatchClass (removelast ks24)).
    assert (FE : fe = QE (li_chunk li) n0) by (subst fe; unfold free_entry; rewrite LN; reflexivity).
    assert (EB : batch_addr (a_sb A) b' = b) by reflexivity.
    assert (BB : batch_bytes b' = n0 + 8192).
    { subst b'. rewrite batch_bytes_ebytes. cbn [ba_entries]. rewrite ebytes_cons. cbn [ebytes fold_right]. subst fe. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. unfold kQuarantineBatchBytes. lia. }
    (first [ pose proof ((u64x4_of_rw v' _ _ _ _ _ Pb)) as dR_31; dand4 dR_31 as Yb0 Yb1 Yb2 Yb3 | destruct (u64x4_of_rw v' _ _ _ _ _ Pb) as (Yb0 & Yb1 & Yb2 & Yb3) ]).
    assert (Pbr : batches_repr LPA v' (a_sb A) qt').
    { subst qt'. cbn [batches_repr]. rewrite EB, BB. offs. split; [exact Yb0|]. split; [exact Yb1|]. split; [subst b'; cbn [ba_entries length Z.of_nat Pos.of_succ_nat]; exact Yb2|].
      split.
      { subst b'. cbn [ba_entries]. intros i e Hi. destruct i as [|i]; [| destruct i; discriminate]. cbn in Hi. injection Hi as <-. rewrite FE. cbn [qe_chunk qe_n Z.of_nat Z.mul Z.add].
        unfold hdr_of. rewrite <- PU. unfold kChunkHeaderSize. replace (b + (24 + 8 * 0)) with (b + 24) by lia. replace (p - 16) with (p + -16) by lia. exact Yb3. }
      split; [| exact I]. apply (mapped_N (aview_of (pa_hull A) m) v' NN); [try (generalize alloc_ceiling_val); clear -BLO; try pose proof alloc_ceiling_val; kung_all; lia|try (generalize alloc_ceiling_val); clear -BLO; try pose proof alloc_ceiling_val; kung_all; lia| try (generalize alloc_ceiling_val); clear -BHI; try pose proof alloc_ceiling_val; unfold kQuarantineBatchBytes; lia| exact BM]. }
    assert (Pl24 : let e := p_thr (a_pl A) + off_th_per_class kQuarantineBatchClass in let ks' := pk_chunks (cache' kQuarantineBatchClass) in
      Z.of_nat (length ks') <= 16 /\
      u32_at rsegs v' (e + off_pc_count) (Z.of_nat (length ks')) /\
      (if a_cache_inited A && negb (kQuarantineBatchClass =? 0) then u32_at rsegs v' (e + off_pc_max_count) (max_count kQuarantineBatchClass) /\ u64_at rsegs v' (e + off_pc_class_size) (class_size kQuarantineBatchClass)
       else u32_at rsegs v' (e + off_pc_max_count) 0 /\ u64_at rsegs v' (e + off_pc_class_size) 0) /\
      (forall i k, nth_error ks' i = Some k -> u32_at rsegs v' (e + off_pc_chunk (Z.of_nat i)) (k * class_size kQuarantineBatchClass / kCompactPtrScale)) /\
      junk_at rsegs v' (e + off_pc_chunk (Z.of_nat (length ks'))) (4 * (16 - Z.of_nat (length ks')))).
    { cbv zeta. subst cache'. unfold cache_set. rewrite Z.eqb_refl. cbn [pk_chunks]. rewrite CI. cbn [andb negb Z.eqb Pos.eqb kQuarantineBatchClass].
      rewrite removelast_length'. fold ks24.
      destruct Pl24c as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      apply bytes_at_app in B as [Bcnt B]. apply bytes_at_app in B as [Bmax B]. apply bytes_at_app in B as [Bsz Bks]. rewrite ?length_le4, ?length_le8 in Bmax; rewrite ?length_le4, ?length_le8 in Bsz; rewrite ?length_le4, ?length_le8 in Bks.
      assert (LNE : (1 <= length ks24)%nat) by (try (generalize alloc_ceiling_val); clear -CNT; try pose proof alloc_ceiling_val; subst cnt; lia).
      unfold u32_at, u64_at. offs. unfold kQuarantineBatchClass.
      split; [try (generalize alloc_ceiling_val); clear -CNT LNE; try pose proof alloc_ceiling_val; subst cnt; lia|]. split.
      { replace (Z.of_nat (length ks24 - 1)) with (cnt - 1) by (try (generalize alloc_ceiling_val); clear -LNE; try pose proof alloc_ceiling_val; subst cnt; lia).
        replace (p_thr (a_pl A) + (208 + 80 * 24) + 0) with (p_thr (a_pl A) + 208 + 1920) by lia. exact Bcnt. }
      split.
      { split; [replace (p_thr (a_pl A) + (208 + 80 * 24) + 4) with (p_thr (a_pl A) + 208 + 1920 + Z.of_nat 4) by lia; exact Bmax
              | replace (p_thr (a_pl A) + (208 + 80 * 24) + 8) with (p_thr (a_pl A) + 208 + 1920 + Z.of_nat 4 + Z.of_nat 4) by lia; replace (class_size 24) with 8192 by reflexivity; exact Bsz]. }
      split.
      { intros i k E. pose proof (nth_error_removelast _ _ _ E) as E'.
        assert (Hi : (i < length ks24)%nat) by (apply nth_error_Some; rewrite E'; discriminate).
        assert (EK : nth_error ks i = Some (Z_to_bv 64 (k * class_size 24 / 16))).
        { rewrite <- (firstn_skipn (length ks24) ks). rewrite nth_error_app1 by (rewrite firstn_length; lia). rewrite KSF. rewrite nth_error_map, E'. reflexivity. }
        pose proof (u32s_entry v' _ ks i _ Bks EK) as X. unfold kCompactPtrScale.
        replace (p_thr (a_pl A) + (208 + 80 * 24) + (16 + 4 * Z.of_nat i)) with (p_thr (a_pl A) + 208 + 1920 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + 4 * Z.of_nat i) by lia. exact X. }
      { apply junk_at_of_mapped; [try (generalize alloc_ceiling_val); clear -TH1; apply aobj_facts in TH1; try pose proof alloc_ceiling_val; kung_all; lia| try (generalize alloc_ceiling_val); clear -CNT; try pose proof alloc_ceiling_val; subst cnt; lia| try (generalize alloc_ceiling_val); clear -TH2 CNT CE; try pose proof alloc_ceiling_val; subst cnt; kung_all; lia|].
        pose proof (bytes_at_mapped_gen v' _ _ Bks ltac:(try (generalize alloc_ceiling_val); clear -TH1; apply aobj_facts in TH1; try pose proof alloc_ceiling_val; kung_all; lia) ltac:(rewrite u32s_length, LKS; try (generalize alloc_ceiling_val); clear -TH1; apply aobj_facts in TH1; try pose proof alloc_ceiling_val; kung_all; lia)) as MK. rewrite u32s_length, LKS in MK.
        intros j Hj. replace (p_thr (a_pl A) + (208 + 80 * 24) + (16 + 4 * Z.of_nat (length ks24 - 1)) + j)
          with (p_thr (a_pl A) + 208 + 1920 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + (4 * (Z.of_nat (length ks24) - 1) + j)) by lia. apply MK. clear -Hj LNE CNT; try pose proof alloc_ceiling_val. subst cnt. lia. } }
    assert (C'O : forall c, c <> kQuarantineBatchClass -> cache' c = a_cache A c).
    { intros c Hc. subst cache'. unfold cache_set. destruct (Z.eqb_spec c kQuarantineBatchClass); [contradiction| reflexivity]. }
    assert (C'S : forall k, p_cached_ cache' kQuarantineBatchClass k -> p_cached_ (a_cache A) kQuarantineBatchClass k).
    { intros k Hk. subst cache'. unfold p_cached_, cache_set in Hk |- *. rewrite Z.eqb_refl in Hk. cbn [pk_chunks] in Hk. exact (removelast_incl _ _ Hk). }
    assert (HQ2 : qc_first A qt' = b) by (subst qt'; unfold qc_first; exact EB).
    (* [comment removed for export] *)
    set (qt1 := tailQt tk qt'). set (qg1 := tailQg tk qt' (a_qglobal A)).
    set (A' := freeA A p qt1 qg1 cache' (fst (depot_putC (a_depot A) key)) true).
    assert (Pqc' : rw_cells rsegs v' (p_thr (a_pl A) + 80)
              [C8 (wz (Z.of_nat (length qt1))); C8 (wz (qc_first A qt1)); C8 (wz (qc_last A qt1)); C8 (wz (q_bytes qt1))]).
    { subst qt1. destruct tk; cbn [tailQt tail_post] in TPOST |- *.
      - unfold qc_first, qc_last. subst qt'. cbn [length last Z.of_nat Pos.of_succ_nat]. rewrite q_bytes_cons, q_bytes_nil, EB, BB.
        replace (n0 + 8192 + 0) with (0 + (n0 + 8192)) by lia. exact TPOST.
      - destruct TPOST as (X & _). exact X.
      - destruct TPOST as (X & _). exact X. }
    assert (Pbr' : batches_repr LPA v' (a_sb A) qt1) by (subst qt1; destruct tk; cbn [tailQt]; [exact Pbr| exact I| exact I]).
    assert (Pqcg : let I := al_instance AL_pboth + off_q_cache_list_size in
              u64_at rsegs v' (I + 0) (Z.of_nat (length qg1)) /\
              u64_at rsegs v' (I + 8) (match qg1 with [] => 0 | b0 :: _ => batch_addr (a_sb A) b0 end) /\
              u64_at rsegs v' (I + 16) (match qg1 with [] => 0 | _ => batch_addr (a_sb A) (last qg1 (BA 0 [])) end) /\
              u64_at rsegs v' (I + 24) (q_bytes qg1)).
    { subst qg1. destruct tk; cbn [tailQg tail_post] in TPOST |- *.
      - exact (proj1 (global_untouched A (aview_of (pa_hull A) m) p n0 li spd v' lo AR LU LN ltac:(clear -CEIL LOW; lia) BX MU' NN (NGQ eq_refl) ltac:(intros g a Hg Ha; exact (NBXg g a Hg Ha eq_refl)))).
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). (first [ dand3 TPOST as _ _ X | destruct TPOST as (_ & _ & X) ]). rewrite QGE. cbn [app]. change (al_instance AL_pboth + off_q_cache_list_size) with (QINST + 160).
        subst gqb. rewrite QGE in X. rewrite q_bytes_nil, Z.add_0_l in X.
        apply u64x4_of_rw. subst qt'. cbn [length last Z.of_nat Pos.of_succ_nat]. rewrite q_bytes_cons, q_bytes_nil, EB, BB.
        replace (n0 + 8192 + 0) with (0 + (n0 + 8192)) by lia. exact X.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ dand4 TPOST as _ _ X _ | destruct TPOST as (_ & _ & X & _) ]). change (al_instance AL_pboth + off_q_cache_list_size) with (QINST + 160).
        apply u64x4_of_rw. rewrite length_app, Nat2Z.inj_add, q_bytes_app.
        replace (match a_qglobal A ++ qt' with [] => 0 | b0 :: _ => batch_addr (a_sb A) b0 end) with gf by (subst gf; unfold qc_first; destruct (a_qglobal A); [congruence| reflexivity]).
        replace (match a_qglobal A ++ qt' with [] => 0 | _ :: _ => batch_addr (a_sb A) (last (a_qglobal A ++ qt') (BA 0 [])) end) with b.
        2:{ subst qt'. rewrite last_last. rewrite <- EB. destruct (a_qglobal A ++ [b']) eqn:EE; [| reflexivity]. apply app_eq_nil in EE. destruct EE; discriminate. }
        subst gn gqb qt'. cbn [length Z.of_nat Pos.of_succ_nat] in X |- *. rewrite q_bytes_cons, q_bytes_nil, BB. replace (q_bytes (a_qglobal A) + (n0 + 8192 + 0)) with (q_bytes (a_qglobal A) + (0 + (n0 + 8192))) by lia. exact X. }
    assert (Pbrg : batches_repr LPA v' (a_sb A) qg1).
    { subst qg1. destruct tk; cbn [tailQg tail_post] in TPOST |- *.
      - exact (proj2 (global_untouched A (aview_of (pa_hull A) m) p n0 li spd v' lo AR LU LN ltac:(clear -CEIL LOW; lia) BX MU' NN (NGQ eq_refl) ltac:(intros g a Hg Ha; exact (NBXg g a Hg Ha eq_refl)))).
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). rewrite QGE. exact Pbr.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ dand4 TPOST as _ _ _ Pgl | destruct TPOST as (_ & _ & _ & Pgl) ]). (first [ pose proof ((GLX QGN)) as dR_39; dand7 dR_39 as E INg R1 R2 Cg NKb INgg | destruct (GLX QGN) as (E & INg & R1 & R2 & Cg & NKb & INgg) ]).
        (first [ pose proof ((ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_40; dand3 dR_40 as _ QG0 _ | destruct (ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & QG0 & _) ]). (first [ dand5 QG0 as _ _ _ _ BRG0 | destruct QG0 as (_ & _ & _ & _ & BRG0) ]). change (p_sb (a_pl A)) with (a_sb A) in BRG0.
        apply breprN_cat; [| exact Pbr].
        replace (hd_addr (a_sb A) qt') with b by (subst qt'; unfold hd_addr; exact EB).
        pattern (a_qglobal A) at 1. rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN). fold glb.
        apply (breprN_relink (aview_of (pa_hull A) m) v' (a_sb A) (removelast (a_qglobal A)) glb 0).
        + apply breprN_0. unfold glb. rewrite (removelast_last_app (a_qglobal A) (BA 0 []) QGN). exact BRG0.
        + intros x Hx i Hi. assert (INx : In x (a_qthread A ++ a_qglobal A)).
          { apply in_or_app. right. destruct Hx as [Hx| ->]; [| exact INgg].
            pattern (a_qglobal A) at 1. rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN). apply in_or_app. left. exact Hx. }
          pose proof (batch_known A (aview_of (pa_hull A) m) AR x INx) as [_ LX]. unfold kQuarantineBatchCount in LX. lia.
        + (* [comment removed for export] *)
          intros x a' Hx Ha'.
          assert (INxg : In x (a_qglobal A)) by (pattern (a_qglobal A) at 1; rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN); apply in_or_app; left; exact Hx).
          assert (INx : In x (a_qthread A ++ a_qglobal A)) by (apply in_or_app; right; exact INxg).
          pose proof (batch_carved A (aview_of (pa_hull A) m) AR x INx) as Cx.
          pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cx) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cx) as Dn. pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cx) as Df.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx CVp ltac:(intros EE; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li x LU INx (eq_sym EE)))) as Dp.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx CKB (batch_not_cached A (aview_of (pa_hull A) m) AR x kQuarantineBatchClass kb INx C24 KIN)) as Dk.
          assert (NIg : ba_idx x <> ba_idx glb).
          { intros EE. pose proof BND0 as ND. rewrite map_app in ND. apply stdpp.list_relations.list.NoDup_app in ND as (_ & _ & NDg).
            pattern (a_qglobal A) at 1 in NDg. rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN), map_app in NDg. cbn [map] in NDg.
            exact (NoDup_app_In _ _ (ba_idx x) NDg ltac:(apply in_map; exact Hx) ltac:(rewrite EE; left; reflexivity)). }
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx Cg ltac:(intros EE; injection EE as EE; exact (NIg EE))) as Dgx.
          rewrite (proj1 (c24_range A (ba_idx x))), (proj2 (c24_range A (ba_idx x))) in Dt, Dn, Df, Dp, Dk, Dgx.
          rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in Dk. rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dgx.
          (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR x INx)) as dR_42; dand3 dR_42 as Rx1 Rx2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR x INx) as (Rx1 & Rx2 & _) ]).
          apply MU'; [clear -Ha' Rx1 Rx2 CE; unfold kQuarantineBatchBytes in *; kung_all; lia| |].
          * unfold W0. clear -Ha' Dt Dn Df Dp Rx1 Rx2 L1 L2 CE CEIL S2 NR Gc Gt Gn Gf Gs. unfold batch_addr, kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          * subst BX b. cbv beta. intros [X|[X|[X|[[_ X]|[[_ X]|[_ X]]]]]].
            -- clear -Ha' Dt X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dt X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dk X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Rx1 X. unfold gq_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
            -- clear -Ha' Dgx X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Rx1 X. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
        + (* [comment removed for export] *)
          intros a' Ha'.
          pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cg) as Dn. pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cg) as Df.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CVp ltac:(intros EE; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li glb LU INg (eq_sym EE)))) as Dp.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CKB NKb) as Dk.
          rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dt, Dn, Df, Dp, Dk. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in Dk.
          apply MU'; [clear -Ha' R1 R2 CE E; unfold batch_addr, kQuarantineBatchBytes in *; kung_all; lia| |].
          * unfold W0. subst b. clear -Ha' E Dt Dn Df Dp R1 R2 L1 L2 CE CEIL S2 NR Gc Gt Gn Gf Gs. unfold batch_addr, kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          * subst BX b. cbv beta. intros [X|[X|[X|[[_ X]|[[_ X]|[_ X]]]]]].
            -- clear -Ha' Dt X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dt X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dk X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' R1 X E. unfold gq_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
            -- clear -Ha' X E. unfold batch_addr in *. lia.
            -- clear -Ha' R1 X E. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
        + rewrite <- E. unfold off_qb_next. rewrite Z.add_0_r. destruct Pgl as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
        + rewrite <- E. (first [ pose proof ((batches_repr_last _ _ (removelast (a_qglobal A)) glb ltac:(unfold glb; rewrite (removelast_last_app (a_qglobal A) (BA 0 []) QGN); exact BRG0))) as dR_43; dand5 dR_43 as _ _ _ _ Mg | pose proof (batches_repr_last _ _ (removelast (a_qglobal A)) glb ltac:(unfold glb; rewrite (removelast_last_app (a_qglobal A) (BA 0 []) QGN); exact BRG0)) as (_ & _ & _ & _ & Mg) ]).
          rewrite <- E in Mg. apply (mapped_N (aview_of (pa_hull A) m) v' NN); [clear -R1; kung_all; lia| clear -R1; kung_all; lia| clear -R2 CE; unfold kQuarantineBatchBytes in *; lia| exact Mg]. }
    assert (QT'E : forall e, In e (q_entries (qt1 ++ qg1)) -> In e (q_entries (a_qthread A ++ a_qglobal A)) \/ e = QE (li_chunk li) n0).
    { intros e He. subst qt1 qg1. apply (proj1 (tailQ_entries tk qt' (a_qglobal A) e)) in He.
      subst qt' b'. cbn [q_entries flat_map ba_entries app] in He. destruct He as [E|He]; [right; rewrite <- E; exact FE|]. left. rewrite QTE. cbn [app]. exact He. }
    assert (QT'N : In (QE (li_chunk li) n0) (q_entries (qt1 ++ qg1))).
    { subst qt1 qg1. apply (proj2 (tailQ_entries tk qt' (a_qglobal A) _)). subst qt' b'. cbn [q_entries flat_map ba_entries app]. left. exact FE. }
    assert (QT'B : forall b0, In b0 (qt1 ++ qg1) -> In (ba_idx b0) (map ba_idx (a_qthread A ++ a_qglobal A)) \/ p_cached_ (a_cache A) kQuarantineBatchClass (ba_idx b0)).
    { intros b0 Hb0. subst qt1 qg1. apply (proj1 (tailQ_batches tk qt' (a_qglobal A) b0)) in Hb0.
      subst qt'. destruct Hb0 as [<-|Hb0]; [right; subst b'; cbn [ba_idx]; exact KIN|]. left. rewrite QTE. cbn [app]. apply in_map. exact Hb0. }
    (* [comment removed for export] *)
    assert (IAQ : ((true = a_ia_inited A /\ (forall a, iafoot a -> v' (wz a) = aview_of (pa_hull A) m (wz a))) \/ (true = true /\ ia_repr_ LPA AL_pboth true v'))
                  /\ u8_at rsegs v' 0x144649 0 /\ bytes_at rsegs v' 0x14464a [Z_to_bv 8 0; Z_to_bv 8 0]).
    { destruct (a_ia_inited A) eqn:EIA.
      - assert (IAW : forall a, 0xb5dc0 <= a < 0x14464c -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
        { intros a Ha. apply MU'; [clear -Ha; lia| |].
          - unfold W0. clear -Ha T1 L1 L2 CL1 CE CEIL N1 F1 S1 S2 Gc Gt Gn Gf Gs. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          - subst BX. cbv beta. intros [X|[X|[X|[[_ X]|[[Htk X]|[X _]]]]]]; [clear -Ha X Gt; kung_all; lia| clear -Ha X Gt; kung_all; lia| clear -Ha X BLO; unfold kHighMemBeg in BLO; lia| clear -Ha X; unfold gq_blk in X; lia| | discriminate].
            subst tk. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_45; dand4 dR_45 as _ _ R1 _ | destruct (GLX QGN) as (_ & _ & R1 & _) ]). clear -Ha X R1. kung_all. lia. }
        split; [| split].
        + left. split; [reflexivity|]. intros a Ha. apply IAW. unfold iafoot in Ha. cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pboth] in Ha. clear -Ha. lia.
        + pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK. unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ _ _ _ LK | destruct LK as (_ & _ & _ & _ & _ & LK) ]).
          change (al_internal_alloc_inited AL_pboth + 1) with 0x144649 in LK. rewrite lockb_nil in LK.
          eapply (bytes_at_agree_gen _ _ _ _ _ LK). intros i Hi. cbn in Hi. apply IAW. lia.
        + pose proof (consts_cell (aview_of (pa_hull A) m) 0x14464a [Z_to_bv 8 0; Z_to_bv 8 0] (proj1 (ar_consts _ _ _ _ _ (proj2 AR))) eq_refl) as PD.
          eapply (bytes_at_agree_gen _ _ _ _ _ PD). intros i Hi. cbn in Hi. apply IAW. lia.
      - exfalso. clear -EIA IAT. congruence. }
    (first [ dand3 IAQ as IAH IAL IAP | destruct IAQ as (IAH & IAL & IAP) ]).
    assert (QLX : u8_at rsegs v' 0xb18c8 0 /\ u8_at rsegs v' 0xb18c9 0 /\ bytes_at rsegs v' 0xb18ca [Z_to_bv 8 0; Z_to_bv 8 0]).
    { destruct tk; cbn [tail_post] in TPOST.
      - assert (QGW : forall a, 0xb18c8 <= a < 0xb18cc -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
        { intros a Ha. apply MU'; [clear -Ha; lia| |].
          - unfold W0. clear -Ha T1 L1 L2 CL1 CE CEIL N1 F1 S1 S2 Gc Gt Gn Gf Gs. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          - exact (fun HB => NGQ eq_refl a HB ltac:(unfold gq_blk; clear -Ha; lia)). }
        split; [| split].
        + pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK. unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ LKc _ _ _ | destruct LK as (_ & _ & LKc & _ & _ & _) ]).
          change (al_instance AL_pboth + off_q_cache_mutex) with 0xb18c8 in LKc. rewrite lockb_nil in LKc.
          eapply (bytes_at_agree_gen _ _ _ _ _ LKc). intros i Hi. cbn in Hi. apply QGW. lia.
        + pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK. unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ _ LKr _ _ | destruct LK as (_ & _ & _ & LKr & _ & _) ]).
          change (al_instance AL_pboth + off_q_recycle_mutex) with 0xb18c9 in LKr. rewrite lockb_nil in LKr.
          eapply (bytes_at_agree_gen _ _ _ _ _ LKr). intros i Hi. cbn in Hi. apply QGW. lia.
        + pose proof (consts_cell (aview_of (pa_hull A) m) 0xb18ca [Z_to_bv 8 0; Z_to_bv 8 0] (proj1 (ar_consts _ _ _ _ _ (proj2 AR))) eq_refl) as PD.
          eapply (bytes_at_agree_gen _ _ _ _ _ PD). intros i Hi. cbn in Hi. apply QGW. lia.
      - (first [ dand3 TPOST as _ LW _ | destruct TPOST as (_ & LW & _) ]). destruct LW as [[_ B] _]. cbn [cells_bytes cbytes app] in B. change (le2 (wz 0)) with [Z_to_bv 8 0; Z_to_bv 8 0] in B. change (QINST + 152) with 0xb18c8 in B.
        apply (bytes_at_app _ v' 0xb18c8 [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) in B as [B1 B]. apply (bytes_at_app _ v' _ [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0]) in B as [B2 B3].
        cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in B2, B3. exact (conj B1 (conj B2 B3)).
      - (first [ dand3 TPOST as _ LW _ | destruct TPOST as (_ & LW & _) ]). destruct LW as [[_ B] _]. cbn [cells_bytes cbytes app] in B. change (le2 (wz 0)) with [Z_to_bv 8 0; Z_to_bv 8 0] in B. change (QINST + 152) with 0xb18c8 in B.
        apply (bytes_at_app _ v' 0xb18c8 [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) in B as [B1 B]. apply (bytes_at_app _ v' _ [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0]) in B as [B2 B3].
        cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in B2, B3. exact (conj B1 (conj B2 B3)). }
    (first [ dand3 QLX as QLK QRL QPD | destruct QLX as (QLK & QRL & QPD) ]).
    assert (EQA : freeA_new A p li key = freeA A p qt' (a_qglobal A) cache' (fst (depot_putC (a_depot A) key)) (a_ia_inited A)).
    { rewrite freeA_new_eq. unfold qpush_new. rewrite QTE. cbn [app]. rewrite last_nth. reflexivity. }
    (* [comment removed for export] *)
    eapply (KK t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' (munrestrict (hidc (pa_hull A)) m v') md').
    - (* [comment removed for export] *)
      constructor.
      + subst A' qt1 qg1. destruct tk; cbn [tailQt tailQg].
        * rewrite <- (set_ia_freeA A p qt' (a_qglobal A) cache' _ (a_ia_inited A) true). apply WF_set_ia. rewrite <- EQA.
          apply (free_new_WF A m md p li key AI LU KEYU NE24); [left; exact QTE|].
          rewrite QTE. unfold free_entry, qe_bytes. cbn [qe_n q_bytes fold_right]. rewrite LN, US. clear -TKC. unfold kQuarantineBatchBytes, kQuarantineCacheSize in *. lia.
        * rewrite <- (set_ia_freeA A p [] (a_qglobal A ++ qt') cache' _ (a_ia_inited A) true). apply WF_set_ia. rewrite <- xferA_freeA. rewrite <- EQA.
          apply (xfer_WFB _ _ (free_new_WFB A m md p li key AI LU KEYU NE24 (or_introl QTE))).
          -- cbn [freeA_new a_qglobal a_qthread]. rewrite qpush_new_bytes, QTE, q_bytes_nil. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. destruct TKC as (TK1 & _). clear -TK1. unfold kQuarantineCacheSize, kQuarantineBatchBytes in *. lia.
          -- cbn [freeA_new a_qglobal a_qthread]. rewrite qpush_new_bytes, QTE, q_bytes_nil. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. (first [ dand3 TKC as _ QGE T3 | destruct TKC as (_ & QGE & T3) ]). rewrite QGE, q_bytes_nil. clear -T3. unfold kQuarantineMaxSize, kQuarantineBatchBytes in *. lia.
        * rewrite <- (set_ia_freeA A p [] (a_qglobal A ++ qt') cache' _ (a_ia_inited A) true). apply WF_set_ia. rewrite <- xferA_freeA. rewrite <- EQA.
          apply (xfer_WFB _ _ (free_new_WFB A m md p li key AI LU KEYU NE24 (or_introl QTE))).
          -- cbn [freeA_new a_qglobal a_qthread]. rewrite qpush_new_bytes, QTE, q_bytes_nil. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. destruct TKC as (TK1 & _). clear -TK1. unfold kQuarantineCacheSize, kQuarantineBatchBytes in *. lia.
          -- cbn [freeA_new a_qglobal a_qthread]. rewrite qpush_new_bytes, QTE, q_bytes_nil. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. (first [ dand3 TKC as _ _ T3 | destruct TKC as (_ & _ & T3) ]). clear -T3. unfold kQuarantineMaxSize, kQuarantineBatchBytes in *. lia.
      + change (ahull_of pa_image_ivs AL_pboth A') with (pa_hull A). rewrite VIEW. subst A'.
        eapply (free_arepr A (aview_of (pa_hull A) m) p n0 li spd v' lo AR LU LN ltac:(clear -CEIL LOW; lia) qt1 qg1 cache' _ true BX BXW MU' NN b1 _ B1R B1M IDR'
                  Punw Phdr Pctx Psh Pdr Pqc' Pbr' Pqcg Pbrg Pl24 IAH IAL IAP QLK QRL QPD QT'E QT'N QT'B C'O C'S).
      + subst A'. cbn [freeA a_pl a_reg a_sec]. apply (free_hiddenC A m md p n0 li spd v' lo AI LU LN CEIL BX BXW MU' WM').
        exact (ai_hidden _ _ _ _ _ _ _ AI).
      + subst A'. cbn [freeA a_pl]. exact (ai_extra _ _ _ _ _ _ _ AI).
      + subst A'. cbn [freeA a_pl a_sec]. exact (aledger_sbm _ _ _ _ md md' Hsame (ai_ledger _ _ _ _ _ _ _ AI)).
      + exact HI'.
      + (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _) ]). rewrite HLT. exact HH.
      + rewrite (same_but_materialized_vmmaps _ _ Hsame). subst A'. exact (ai_cover _ _ _ _ _ _ _ AI).
      + (* [comment removed for export] *) rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_ceil _ _ _ _ _ _ _ AI).
    - change (pa_hull A') with (pa_hull A). rewrite VIEW. exact MI'.
    - unfold amd_frame. (first [ dand18 FRM as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | destruct FRM as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
      rewrite X2, X17, HH. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption| reflexivity].
    - intros ff. reflexivity.
    - subst A'. reflexivity.
    - unfold as_live, as_live_. subst A'. cbn [freeA a_livemap]. unfold free_lm. rewrite lookup_delete_eq. reflexivity.
    - intros q Hq. unfold as_live, as_live_. subst A'. cbn [freeA a_livemap]. unfold free_lm. rewrite lookup_delete_ne by congruence. reflexivity.
    - unfold as_livebytes. subst A'. cbn [freeA a_livemap]. unfold free_lm. rewrite (as_livebytes_delete' _ _ _ LU), LN. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.   (* [comment removed for export] *)
    - unfold as_nlive. subst A'. cbn [freeA a_livemap]. unfold free_lm. rewrite (as_nlive_delete _ _ _ LU).
      destruct (Z.eqb_spec p 0) as [E0|_]; [exfalso; try (generalize alloc_ceiling_val); clear -E0 PNB; try pose proof alloc_ceiling_val; kung_all; lia| reflexivity].
    - (* [comment removed for export] *)
      intros c Hc [R0 K0]. subst A' cache'. split; [exact R0| cbn [freeA a_cache]; unfold cache_set; destruct (Z.eqb_spec c kQuarantineBatchClass) as [E|_]; [exfalso; exact (Hc E)| exact K0]].
    - intros i Hi. change (pa_hull A') with (pa_hull A). rewrite VIEW. cbn [cl_errno LPA]. unfold mrd.
      rewrite (AGimg A (aview_of (pa_hull A) m) p n0 li spd v' lo AR LU LN ltac:(clear -CEIL LOW; lia) BX BXW MU' (6191924 + i) ltac:(lia) ltac:(lia) ltac:(unfold xblk, ia_blk, gq_blk; lia)). reflexivity.
    - (* [comment removed for export] *)
      change (pa_hull A') with (pa_hull A). rewrite VIEW. apply (frame_ok_widen _ _ _ _ _ _ uspd lo hi SPHI); [| | exact SMH].
      + subst A'. apply (free_frame_okC A m md p n0 li spd v' lo AI LU LN CEIL qt1 qg1 cache' _ true BX BXW MU' WM').
        intros k Hk. destruct ST as (_ & _ & STx). destruct (STx (lo + k) ltac:(lia)) as [Wv _]. unfold wview, wa in Wv.
        rewrite unsigned_lit in Wv by (clear -Hk CEIL LOW CE SPR; lia). rewrite (pa_find_segment_none (lo + k) 1) in Wv by (clear -Hk CEIL LOW CE SPR; lia).
        destruct (aview_of (pa_hull A) m (wz (lo + k))); [discriminate| exact Wv].
      + intros a Ha. apply MU'; [clear -Ha SPR SPHI HISP; lia| |].
        * unfold W0. clear -Ha T1 T2 L1 L2 CL1 CL2 CE CEIL LOW N1 N2 F1 F2 S1 S2 Gc Gt Gn Gf Gs NR R8. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
        * intros HB. destruct (BXW a HB) as [(b0 & Hb & Rb)|[X|[X|[(k & Ck & Rk)|X]]]].
          -- (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR b0 Hb)) as dR_57; dand3 dR_57 as _ Rb2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR b0 Hb) as (_ & Rb2 & _) ]). clear -Ha Rb Rb2 CE CEIL LOW. unfold kQuarantineBatchBytes in *. lia.
          -- clear -Ha X T2 CEIL LOW. lia.
          -- clear -Ha X T2 CEIL LOW. lia.
          -- pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ (cached_carved A (aview_of (pa_hull A) m) AR kQuarantineBatchClass k ltac:(unfold kQuarantineBatchClass; lia) Ck)) as W.
             pose proof class_size_24 as CS24. clear -Ha Rk W CS24 CE CEIL LOW. unfold kQuarantineBatchBytes in *. kung_all. lia.
          -- clear -Ha X CEIL LOW CE. unfold xblk, ia_blk, gq_blk in X. lia.
    - (* [comment removed for export] *)
      intros a Ha. change (pa_hull A') with (pa_hull A). rewrite VIEW. apply MU'; [clear -Ha SPR SPHI HISP; lia| |].
      + unfold W0. clear -Ha T1 T2 L1 L2 CL1 CL2 CE CEIL LOW N1 N2 F1 F2 S1 S2 Gc Gt Gn Gf Gs NR R8. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
      + intros HB. destruct (BXW a HB) as [(b0 & Hb & Rb)|[X|[X|[(k & Ck & Rk)|X]]]].
        * (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR b0 Hb)) as dR_58; dand3 dR_58 as _ Rb2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR b0 Hb) as (_ & Rb2 & _) ]). clear -Ha Rb Rb2 CE CEIL LOW. unfold kQuarantineBatchBytes in *. lia.
        * clear -Ha X T2 CEIL LOW. lia.
        * clear -Ha X T2 CEIL LOW. lia.
        * pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ (cached_carved A (aview_of (pa_hull A) m) AR kQuarantineBatchClass k ltac:(unfold kQuarantineBatchClass; lia) Ck)) as W.
          pose proof class_size_24 as CS24. clear -Ha Rk W CS24 CE CEIL LOW. unfold kQuarantineBatchBytes in *. kung_all. lia.
        * clear -Ha X CEIL LOW CE. unfold xblk, ia_blk, gq_blk in X. lia.
    - (* [comment removed for export] *)
      change (pa_hull A') with (pa_hull A). rewrite VIEW. exact ST'.
  Qed.
End FreeHitsCore.
