(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 AMTac AMallocA AMallocI AMalmys AMal9l1 AMalkbe AMalzuh AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeT AFreeHc AFreeDc AFreeH2c AFreeW2c AFreeH4c AFrejxv AFrea6l AFrelij ACoresk ARtSnjd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalkbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalzuh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeDc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeW2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFrejxv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFrea6l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFrelij OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ATranspR AFreeRS AFreeRX AFreeRI AFreeRT AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRE AWrapKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE.AFreeRI1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE.AFreeRL OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE.AFreeRN OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeB1 AFreeB2 ATransp AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB4 AFreeB4c AFreeB5 AFreeFS AFreeB1F.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB4F.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB4F AFreeG2c.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4.AFreeB3R OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeFS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3.AFreeB2F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4F.AFreeB3F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeG2c.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Lemma freeA_refF {Clg : Ceiling} : forall A p qt qg c D ia, a_cache_inited A = true -> freeA (refF A) p qt qg c D ia = freeA3 A p qt qg c D ia (a_reg (refF A)).
Proof. intros A p qt qg c D ia CI. unfold freeA, freeA3, free_lm, AFreeB2.free_lm. cbn. rewrite CI. reflexivity. Qed.
(* [comment removed for export] *)
Lemma hidden_repr_extF {Clg : Ceiling} : forall P reg reg' sec (mm : mem),
  (forall c, 1 <= c <= 30 -> rg_mapped_user (reg' c) = rg_mapped_user (reg c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (reg c)) ->
  hidden_repr P reg sec mm -> hidden_repr P reg' sec mm.
Proof.
  intros P reg reg' sec mm E [H1 H2]. split; [| exact H2]. intros z Gz. destruct (H1 z Gz) as [X Y]. split; [exact X|].
  intros NH. apply Y. intros HS. apply NH. apply (proj2 (heap_shadow_extF (p_sb P) reg reg' sec z E)). exact HS.
Qed.

(* [comment removed for export] *)
Lemma ro_C8C8 : forall (mm : mem) a x y, u64_at rsegs mm a x -> u64_at rsegs mm (a + 8) y -> ro_cells rsegs mm a [C8 (wz x); C8 (wz y)].
Proof.
  intros mm a x y Bx By. unfold ro_cells, cells_at. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply length_le8|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_app. split; [exact Bx|]. rewrite length_le8. exact By.
Qed.

Section FreeHitsRF.
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
  #[warnings="-notation-for-abbreviation"] Local Notation T160 := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation xs2 := (Z_to_bv 64 n0 : word).
  #[warnings="-notation-for-abbreviation"] Local Notation xs5 := (Z_to_bv 64 (p + -16) : word).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation CUR := (CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A m md p n0 stkobj lo hi xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation it_cfg := (it_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation blk_cfg := (blk_cfgG spd gp s10 s11 F fc).
  Hypothesis VB : forall a, newblk p n0 a -> a < alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis STEP_PDM : forall (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (c k n : Z),
    CUR A1 m1 md1 (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChP (CP c k)) n) ->
    Z.of_nat (length (pk_chunks (a_cache A1 c))) = max_count c ->
    rg_mapped_fa (a_reg A1 c) < 4 * (Z.of_nat (length (rg_free (a_reg A1 c))) + max_count c / 2) ->
    KMORE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 b0 i more scr ->
    KDONE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 b0 i more scr ->
    srealizes rsegs (it_cfg A1 m1 md1 b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') T.
  Hypothesis STEP_SEC : forall (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (s : chunkS) (n : Z),
    CUR A1 m1 md1 (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChS s) n) ->
    KMORE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 b0 i more scr ->
    KDONE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 b0 i more scr ->
    srealizes rsegs (it_cfg A1 m1 md1 b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') T.
  Hypothesis STEP_BDM : forall (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word),
    CUR A1 m1 md1 (Some (b0, length (ba_entries b0))) more scr ->
    Z.of_nat (length (pk_chunks (a_cache A1 kQuarantineBatchClass))) = max_count kQuarantineBatchClass ->
    rg_mapped_fa (a_reg A1 kQuarantineBatchClass) < 4 * (Z.of_nat (length (rg_free (a_reg A1 kQuarantineBatchClass))) + max_count kQuarantineBatchClass / 2) ->
    KHEAD rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 more scr ->
    KEXIT rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 ->
    srealizes rsegs (blk_cfg A1 m1 md1 b0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9') T.

  (* [comment removed for export] *)
  Local Ltac prefix :=
    cbn [cl_segs cl_free_pc LPA] in MI, KK |- *;
    (cbn [cl_segs cl_free_pc LPA] in MI |- *);
    (pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0);
    (pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A (aview_of (pa_hull A) m)) as AR);
    (assert (SPH : uspd <= 2^47) by (clear -SPHI HISP; lia));
    (pose proof alloc_ceiling_val as CE);
    (pose proof (zr_word spd) as SPR; unfold inr64 in SPR);
    (pose proof (zr_word rac) as RAR; unfold inr64 in RAR);
    (destruct (free_li A p n0 HL) as (li & LU & LN));
    (destruct (free_n0 A m md p n0 AI HL) as [NR US]);
    (unfold REQ_MAX in NR);
    ((first [ pose proof ((free_geom A m md p n0 AI HL)) as dR_1; dand4 dR_1 as PAL PLO PCE PHI | destruct (free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]));
    (pose proof (GEO A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as Gx0);
    (assert (PNB : 0x60a000 <= p + -16) by (clear -Gx0; lia)); (clear Gx0);
    ((first [ pose proof ((free_HDR A m md p n0 AI HL)) as dR_2; dex2 dR_2 as b1 ido; dand6 dR_2 as B1R B1M3 B1M IDR HDR CTXID | pose proof ((free_HDR A m md p n0 AI HL)) as dR_2; dand8 dR_2 as b1 ido B1R B1M3 B1M IDR HDR CTXID | destruct (free_HDR A m md p n0 AI HL) as (b1 & ido & B1R & B1M3 & B1M & IDR & HDR & CTXID) ]));
    (destruct (free_CTX0 A m md p n0 AI HL) as (old & CTX0));
    (pose proof (free_SHC A m md p n0 AI HL) as SHC);
    (pose proof (free_FCo A m md AI) as FCo);
    ((first [ pose proof ((free_TST A m md AI)) as dR_3; dex2 dR_3 as fr fd; dand3 dR_3 as FRR FDR TST | pose proof ((free_TST A m md AI)) as dR_3; dand5 dR_3 as fr fd FRR FDR TST | destruct (free_TST A m md AI) as (fr & fd & FRR & FDR & TST) ]));
    (pose proof (free_sep A m md p n0 AI HL) as SEPp);
    (cbv zeta in SEPp);
    ((first [ dand4 SEPp as SEP_pc SEP_pt SEP_pn SEP_pf | destruct SEPp as (SEP_pc & SEP_pt & SEP_pn & SEP_pf) ]));
    ((first [ pose proof ((hit_sep A m md AI)) as dR_5; dand13 dR_5 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]));
    ((first [ pose proof ((hit_place A m md AI)) as dR_6; dand7 dR_6 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]));
    ((first [ pose proof ((hit_depot_wf A m md AI)) as dR_7; dand5 dR_7 as DND DLEN _ DKEY _ | pose proof (hit_depot_wf A m md AI) as (DND & DLEN & _ & DKEY & _) ]));
    (pose proof (hit_DR A m md AI) as DR0);
    (pose proof (hit_TC A m md AI) as TC);
    (pose proof (hit_tsd A m md AI) as [TSD1 TSD2]);
    (assert (TSDL : 0x5e8328 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia));
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
  #[using="STEP_BDM STEP_SEC STEP_PDM VB KK NQ KR KEYU TRW STO STHI STLO SMH ST RA2 SPA HISP SPHI LOW CEIL IAT HL MI AI hi"] Theorem dealloc_new0RX : forall (ms0 : machine_state),
    (forall (tk : ftail) (b1 : Z) (fr : Z) (fd : Z) (ks : list word) (na : word) (statv : word) (bj0 : word) (bj1 : word) (bj2 : word) (bj3 : word) (fr24 : list Z) (gf : Z) (gl : Z) (gn : Z) (gqb : Z) (kb : Z) (b : Z) (kw : word) (nf : Z),
      fr24 = (rg_free (a_reg A kQuarantineBatchClass)) ->
      gf = (qc_first A (a_qglobal A)) ->
      gl = (qc_last A (a_qglobal A)) ->
      gn = (Z.of_nat (length (a_qglobal A))) ->
      gqb = (q_bytes (a_qglobal A)) ->
      kb = (nth (length fr24 - 1) fr24 0) ->
      b = (chunk_addr (a_sb A) kQuarantineBatchClass kb) ->
      kw = (Z_to_bv 64 (kb * 512)) ->
      nf = (Z.of_nat (length fr24)) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 (size_hi n0)); C4 (Z_to_bv 64 n0)]) ->
      (0 <= b1 < 256) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) (p_thr (a_pl A) + 2824) [C8 (Z_to_bv 64 fr); C8 (Z_to_bv 64 fd)]) ->
      (0 <= fr < 2 ^ 64) ->
      (0 <= fd < 2 ^ 64) ->
      (AMallocA.apart (a_sb A + 24 * 2 ^ 32 + 3758096384) (4 * 2 ^ 27) (p + -16) (8 * ((n0 + 7) / 8) + 16)) ->
      (bv_unsigned kw < 2 ^ 32) ->
      (1 <= nf < 2 ^ 27) ->
      (kHighMemBeg <= b) ->
      (b + 8192 <= alloc_ceiling) ->
      (b + 8192 <= free_array_of (a_sb A) 24) ->
      (AMallocA.apart b 8192 (p_thr (a_pl A)) 4096) ->
      (AMallocA.apart b 8192 (p + -16) (8 * ((n0 + 7) / 8) + 16)) ->
      (AMallocA.apart b 8192 (p_nodes0 (a_pl A)) kDepotNodesBlock) ->
      (AMallocA.apart b 8192 (p_frames0 (a_pl A)) kStackStoreBlockBytes) ->
      (tail_pre tk gn gf gl gqb (Z_to_bv 64 0) (aview_of (pa_hull A) m)) ->
      (tail_okR tk gn gqb (0 + (n0 + 8192))) ->
      (tail_apart tk gl (p_thr (a_pl A)) p ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) [b]) ->
      (0 <= kQuarantineMinSize < 2 ^ 64) ->
      (ro_cells rsegs (aview_of (pa_hull A) m) (QINST + 64) [C8 (Z_to_bv 64 (2 ^ 28)); C8 (Z_to_bv 64 kQuarantineMinSize)]) ->
      (tk = TA → apart gl 24 (a_ri A) 4096 ∧ apart gl 24 (a_sb A + 24 * 2 ^ 32 + 3758096384) (4 * 2 ^ 27)) ->
      (p_thr (a_pl A) mod 16 = 0) ->
      (length ks = 16%nat) ->
      (ro_cells rsegs (aview_of (pa_hull A) m) 728440 [C8 (Z_to_bv 64 (a_sb A))]) ->
      (ro_cells rsegs (aview_of (pa_hull A) m) 728456 [C8 (Z_to_bv 64 (a_ri A))]) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) (p_thr (a_pl A) + 80) [C8 (Z_to_bv 64 (Z.of_nat 0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) (p_thr (a_pl A) + 208 + 1920) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2); C8 (Z_to_bv 64 8192); CB 64 (u32s ks)]) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) (p_thr (a_pl A) + 208 + 2576) [C8 statv]) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) (a_ri A + 3072) [C8 (Z_to_bv 64 0)]) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) (a_ri A + 3072 + 16) [C8 (Z_to_bv 64 nf)]) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) (a_ri A + 3072 + 72) [C8 na]) ->
      (u32arr rsegs (aview_of (pa_hull A) m) (free_array_of (a_sb A) 24 + 4 * (nf - 1)) [kw]) ->
      (rw_cells rsegs (aview_of (pa_hull A) m) b [C8 bj0; C8 bj1; C8 bj2; C8 bj3]) ->
      (evt rsegs (free_chitR_new0F_post rac spd gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aview_of (pa_hull A) m) lo p n0 b1 (p_thr (a_pl A)) ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) fr fd stkobj (a_depot A) key (a_sb A) (a_ri A) nf kw na tk gn gf gl gqb 0 kQuarantineMinSize ks) (MS (mkR rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 (Z_to_bv 64 AINST) (Z_to_bv 64 p) a2 a3 (Z_to_bv 64 stkobj) (Z_to_bv 64 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 dealloc_entry) fc None (aview_of (pa_hull A) m) (seg_rom rsegs))) ->
      (forall (msr' : machine_state) (md' : Model), (free_chitR_new0F_post rac spd gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aview_of (pa_hull A) m) lo p n0 b1 (p_thr (a_pl A)) ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) fr fd stkobj (a_depot A) key (a_sb A) (a_ri A) nf kw na tk gn gf gl gqb 0 kQuarantineMinSize ks) msr' -> MInv (pa_hull A) (pa_lhull A) (pa_eager A) md' -> same_but_materialized md md' -> hclean (hidc (pa_hull A)) msr' ->
         srealizes (cl_segs LPA) (mkCfg (unrestrict (hidc (pa_hull A)) m msr') md') T) ->
      srealizes (cl_segs LPA) (mkCfg ms0 md) T) ->
    forall tk : ftail,
    a_qthread A = [] -> a_cache_inited A = true -> pk_chunks (a_cache A kQuarantineBatchClass) = [] ->
    1 <= Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) ->
    match tk with
    | TN => False
    | T0 => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A = [] /\ kQuarantineMaxSize < n0 + kQuarantineBatchBytes
    | TA => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A <> [] /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + (n0 + kQuarantineBatchBytes)
    end ->
    srealizes (cl_segs LPA) (mkCfg ms0 md) T.
  Proof.
    intros ms0 WALKH. intros tk QTE CI E24 NF1 TKC. unfold dealloc_entry_ms. prefix.
    pose proof (free_QC A m md AI) as QC. rewrite QTE in QC. cbn [length Z.of_nat qc_first qc_last q_bytes fold_right] in QC.
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    (* [comment removed for export] *)
    (first [ pose proof ((f24_kidx A m md AI NF1)) as dR_8; dand4 dR_8 as KIN KB KLAST FNE | destruct (f24_kidx A m md AI NF1) as (KIN & KB & KLAST & FNE) ]).
    (first [ pose proof ((f24_PC A m md AI CI E24)) as dR_9; dex1 dR_9 as ks; destruct dR_9 as [LKS PC24] | pose proof ((f24_PC A m md AI CI E24)) as dR_9; dand3 dR_9 as ks LKS PC24 | destruct (f24_PC A m md AI CI E24) as (ks & LKS & PC24) ]).
    set (fr24 := rg_free (a_reg A kQuarantineBatchClass)) in *.
    set (kb := nth (length fr24 - 1) fr24 0) in *. set (nf := Z.of_nat (length fr24)) in *.
    pose proof (f24_geom A m md AI NF1) as GB. cbv zeta in GB. fold fr24 in GB. fold kb in GB. (first [ dand7 GB as BE KWR BLO BHI BFA RB1 RB2 | destruct GB as (BE & KWR & BLO & BHI & BFA & RB1 & RB2) ]).
    set (kw := Z_to_bv 64 (kb * 512)) in *.
    assert (KWV : bv_unsigned kw = kb * 512) by (subst kw; apply unsigned_lit; clear -KWR; lia).
    set (b := chunk_addr (a_sb A) kQuarantineBatchClass kb) in *.
    assert (BE' : a_sb A + 24 * 2^32 + 16 * bv_unsigned kw = b) by (rewrite KWV; symmetry; exact BE).
    pose proof (f24_carved A m md AI NF1) as CKB. fold fr24 in CKB. fold kb in CKB.
    pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ CKB) as WB. fold b in WB.
    pose proof (KN A (aview_of (pa_hull A) m) p n0 li AR LU LN) as KNp. pose proof (known_carved A (aview_of (pa_hull A) m) AR _ _ KNp) as CVp.
    pose proof (GEO A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as G.
    (first [ pose proof ((sb_facts A WF0)) as dR_11; dand5 dR_11 as _ SBA HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & SBA & HB6 & RSB & SCE) ]).
    pose proof (f24_bsep A m md AI NF1) as BS. cbv zeta in BS. fold fr24 in BS. fold kb in BS. fold b in BS. (first [ dand5 BS as Abt Abc Abn Abf Abr | destruct BS as (Abt & Abc & Abn & Abf & Abr) ]).
    pose proof (f24_psep A m md AI NF1 p n0 li LU LN) as PS. cbv zeta in PS. fold fr24 in PS. fold kb in PS. fold b in PS. (first [ dand3 PS as Abp SEP_rp Afap | destruct PS as (Abp & SEP_rp & Afap) ]).
    (first [ pose proof ((f24_sep A m md AI)) as dR_14; dand8 dR_14 as SEP_tr SEP_rs SEP_rc SEP_rn SEP_rf SEP_ts SEP_ns SEP_fs | pose proof (f24_sep A m md AI) as (SEP_tr & SEP_rs & SEP_rc & SEP_rn & SEP_rf & SEP_ts & SEP_ns & SEP_fs) ]).
    (first [ pose proof ((f24_ri A m md AI)) as dR_15; dand7 dR_15 as RIE RILO RIHI RIAL SBAL SBLO SBHI | pose proof (f24_ri A m md AI) as (RIE & RILO & RIHI & RIAL & SBAL & SBLO & SBHI) ]).
    pose proof (f24_nf A m md AI NF1) as [NFR _]. fold fr24 in NFR. fold nf in NFR.
    (first [ pose proof ((f24_region A m md AI NF1)) as dR_16; dex1 dR_16 as na; dand4 dR_16 as MXc NFCc NALc FARRc | pose proof ((f24_region A m md AI NF1)) as dR_16; dand5 dR_16 as na MXc NFCc NALc FARRc | destruct (f24_region A m md AI NF1) as (na & MXc & NFCc & NALc & FARRc) ]). fold fr24 in NFCc. fold nf in NFCc. fold fr24 in FARRc. fold kb in FARRc. fold nf in FARRc. fold kw in FARRc.
    destruct (f24_STA A m md AI) as [statv STA].
    (first [ pose proof ((f24_BC A m md AI NF1)) as dR_17; dex4 dR_17 as bj0 bj1 bj2 bj3; rename dR_17 into BC | pose proof ((f24_BC A m md AI NF1)) as dR_17; dand5 dR_17 as bj0 bj1 bj2 bj3 BC | destruct (f24_BC A m md AI NF1) as (bj0 & bj1 & bj2 & bj3 & BC) ]). fold fr24 in BC. fold kb in BC. fold b in BC.
    pose proof (f24_CRI A m md AI) as CRI. pose proof (f24_CSB A m md AI) as CSB.
    (first [ pose proof ((ar_regions _ _ _ _ _ (proj2 AR) kQuarantineBatchClass C24)) as dR_18; dand13 dR_18 as _ _ _ _ _ _ _ _ _ _ _ _ RM24 | destruct (ar_regions _ _ _ _ _ (proj2 AR) kQuarantineBatchClass C24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RM24) ]). change (p_sb (a_pl A)) with (a_sb A) in RM24.
    assert (BM : mapped (aview_of (pa_hull A) m) b 8192).
    { intros i Hi. replace (b + i) with (region_beg (a_sb A) kQuarantineBatchClass + (b - region_beg (a_sb A) kQuarantineBatchClass + i)) by lia. apply RM24.
      clear -RB1 RB2 Hi. lia. }
    assert (KSMW : bv_unsigned kw < 2^32) by (rewrite KWV; clear -KWR; lia).
    assert (NR' : 1 <= n0 < 2^32) by (try (generalize alloc_ceiling_val); clear -NR; try pose proof alloc_ceiling_val; lia).
    assert (PHI' : p + 8 * ((n0 + 7) / 8) <= alloc_ceiling) by (try (generalize alloc_ceiling_val); clear -PHI CE; try pose proof alloc_ceiling_val; lia).
    assert (SB1 : a_sb A + 2^37 <= 2^47) by (try (generalize alloc_ceiling_val); clear -SCE CE; try pose proof alloc_ceiling_val; kung_all; lia).
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
    pose proof (wfQ A WF0) as WQ0. (first [ dand6 WQ0 as _ _ _ _ QGB _ | destruct WQ0 as (_ & _ & _ & _ & QGB & _) ]). unfold kQuarantineMaxSize in QGB.
    pose proof (qall_count_bound rac spd key KL A [] (aview_of (pa_hull A) m) (conj (WFT_of_WF A WF0) (proj2 AR))) as [CNTq CAPq].
    rewrite !length_app in CNTq.
    assert (GNB : Z.of_nat (length (a_qglobal A)) < 2^40) by (clear -CNTq CAPq; lia).
    assert (TOK : tail_okR tk gn gqb (0 + (n0 + 8192))).
    { destruct tk; cbn [tail_okR].
      - exact TKC.
      - (first [ dand3 TKC as TK1 QGE TK3 | destruct TKC as (TK1 & QGE & TK3) ]). subst gqb. rewrite QGE, q_bytes_nil. unfold kQuarantineCacheSize, kQuarantineMaxSize, kQuarantineBatchBytes in *. clear -TK1 TK3 NQ NR. lia.
      - (first [ dand3 TKC as TK1 QGN TK3 | destruct TKC as (TK1 & QGN & TK3) ]). subst gn gqb. unfold kQuarantineCacheSize, kQuarantineMaxSize, kQuarantineBatchBytes in *.
        assert (Z.of_nat (length (a_qglobal A)) <> 0) by (destruct (a_qglobal A); [congruence| cbn; lia]). clear -TK1 TK3 LENG H GQ0 NR QGB NQ GNB. lia. }
    (* [comment removed for export] *)
    assert (QMM : ro_cells rsegs (aview_of (pa_hull A) m) (QINST + 64) [C8 (wz (2^28)); C8 (wz kQuarantineMinSize)]).
    { pose proof (ar_consts _ _ _ _ _ (proj2 AR)) as CC. unfold consts_repr_ in CC. cbv zeta in CC.
      assert (X1 : u64_at rsegs (aview_of (pa_hull A) m) (728408 + off_q_max_size) kQuarantineMaxSize) by tauto.
      assert (X2 : u64_at rsegs (aview_of (pa_hull A) m) (728408 + off_q_min_size) kQuarantineMinSize) by tauto.
      change (728408 + off_q_max_size) with (QINST + 64) in X1. change (728408 + off_q_min_size) with (QINST + 64 + 8) in X2. change kQuarantineMaxSize with (2^28) in X1.
      exact (ro_C8C8 _ _ _ _ X1 X2). }
    assert (QMR : 0 <= kQuarantineMinSize < 2^64) by (unfold kQuarantineMinSize; clear; lia).
    set (glb := last (a_qglobal A) (BA 0 [])).
    assert (GLX : a_qglobal A <> [] ->
              gl = batch_addr (a_sb A) glb /\ In glb (a_qthread A ++ a_qglobal A) /\ kHighMemBeg <= gl /\ gl + kQuarantineBatchBytes <= alloc_ceiling /\
              carved A (ChP (CP kQuarantineBatchClass (ba_idx glb))) /\ ChP (CP kQuarantineBatchClass (ba_idx glb)) <> ChP (CP kQuarantineBatchClass kb) /\ In glb (a_qglobal A)).
    { intros QGN. (first [ pose proof ((q_gl_cell A _ AR QGN)) as dR_24; dand5 dR_24 as _ E INg R1 R2 | destruct (q_gl_cell A _ AR QGN) as (_ & E & INg & R1 & R2) ]).
      split; [exact E|]. split; [exact INg|]. split; [exact R1|]. split; [exact R2|]. split; [exact (batch_carved A (aview_of (pa_hull A) m) AR glb INg)|].
      assert (INg' : In glb (a_qglobal A)) by (subst glb; pattern (a_qglobal A) at 2; rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN); apply in_or_app; right; left; reflexivity).
      split; [exact (batch_not_free A (aview_of (pa_hull A) m) AR glb kQuarantineBatchClass kb INg C24 KIN)| exact INg']. }
    assert (TAP : tail_apart tk gl (p_thr (a_pl A)) p ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) [b]).
    { destruct tk; cbn [tail_apart]; [exact I| exact I|]. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_26; dand7 dR_26 as E INg R1 R2 Cg NKb _ | destruct (GLX QGN) as (E & INg & R1 & R2 & Cg & NKb & _) ]).
      pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cg) as Dn.
      pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cg) as Df.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CVp ltac:(intros EE; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li glb LU INg (eq_sym EE)))) as Dp.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CKB NKb) as Dk.
      rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dt, Dn, Df, Dp, Dk. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in Dk.
      (first [ dand5 G as _ _ L1 L2 _ | destruct G as (_ & _ & L1 & L2 & _) ]).
      subst b. clear -E R1 R2 Dt Dn Df Dp Dk L1 L2 CE. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try lia. constructor; [lia| constructor]. }
    assert (TAPR : tk = TA -> apart gl 24 (a_ri A) 4096 /\ apart gl 24 (a_sb A + 24 * 2^32 + 3758096384) (4 * 2^27)).
    { intros ->. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_29; dand7 dR_29 as E INg R1 R2 Cg NKb _ | destruct (GLX QGN) as (E & INg & R1 & R2 & Cg & NKb & _) ]).
      pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ Cg) as Wg. rewrite E.
      unfold batch_addr, apart, AMallocA.apart. rewrite RIE. clear -Wg. pose proof class_size_24 as CS. unfold region_beg, kQuarantineBatchClass in *. kung_all. unfold kQuarantineBatchBytes in CS. lia. }
    (* [comment removed for export] *)
    pose proof (free_chitR_new0F rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                  (aview_of (pa_hull A) m) lo p n0 b1 pa_tsd (p_ctx (a_pl A)) (p_thr (a_pl A))
                  ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) fr fd stkobj (a_depot A) key old (shpat n0)
                  MI ST LO SPA SPH RA2 TPE PAL PLO PNB PHI' NR' NQ R8 B1R B1M3 HDR CTX0 SHC FCo
                  (hit_PCo A m md AI) TC (hit_TH0 A m md AI) (hit_CT8 A m md AI) TSDL
                  TST FRR FDR DR0 DND DLEN DTOT (conj DN01 DN02) (conj DF01 DF02) STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc
                  (a_sb A) (a_ri A) nf kw na SBLO SBHI SBAL RILO RIHI RIAL SEP_tr SEP_ts SEP_rs SEP_rp SEP_rn SEP_rf SEP_ns SEP_fs) as EV0.
    cbv zeta in EV0. rewrite BE' in EV0.
    specialize (EV0 Afap KSMW NFR BLO BHI BFA Abt Abp Abn Abf
                    tk gn gf gl gqb (wz 0) 0 ks statv bj0 bj1 bj2 bj3 kQuarantineMinSize TPRE TOK TAP QMR QMM TAPR ltac:(lia) THRA LKS CSB CRI QC PC24 STA MXc NFCc NALc FARRc BC).
    rename EV0 into EV.
    idtac "walk ok".
    (* [comment removed for export] *)
    destruct (asI_minv A m md AI) as [HMI HH].
    pose proof (WALKH tk b1 fr fd ks na statv bj0 bj1 bj2 bj3 fr24 gf gl gn gqb kb b kw nf eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HDR B1R TST FRR FDR Afap KSMW NFR BLO BHI BFA Abt Abp Abn Abf TPRE TOK TAP QMR QMM TAPR THRA LKS CSB CRI QC PC24 STA MXc NFCc NALc FARRc BC EV) as WK.
    apply WK; clear WK.
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex13 HQ as t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' statv' v'; dand19 HQ as -> MU WM' MI' ST' PFR' Ptst Phdr Pctx Psh Pdr Pl24c Pstat Pb PR PNF PNA PFA TPOST | dand32 HQ as t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' statv' v' -> MU WM' MI' ST' PFR' Ptst Phdr Pctx Psh Pdr Pl24c Pstat Pb PR PNF PNA PFA TPOST | destruct HQ as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & v' & -> & MU & WM' & MI' & ST' & PFR' & Ptst & Phdr & Pctx & Psh & Pdr & Pl24c & Pstat & Pb & PR & PNF & PNA & PFA & TPOST) ]).
    try rewrite BE' in MU. try rewrite BE' in Pb. try rewrite BE' in TPOST.
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v') = v').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> aview_of (pa_hull A) m (wz a) <> None -> v' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NN _ _ a WM'); lia. }
    (* [comment removed for export] *)
    pose proof G as G'. (first [ dand18 G' as PM CL1 L1 L2 CL2 _ R8' PU T1 T2 N1 N2 F1 F2 S1 S2 CEQ _ | destruct G' as (PM & CL1 & L1 & L2 & CL2 & _ & R8' & PU & T1 & T2 & N1 & N2 & F1 & F2 & S1 & S2 & CEQ & _) ]).
    (first [ pose proof ((GEOP A (aview_of (pa_hull A) m) p n0 li AR LU LN)) as dR_32; dand4 dR_32 as Gc Gt Gn Gf | pose proof (GEOP A (aview_of (pa_hull A) m) p n0 li AR LU LN) as (Gc & Gt & Gn & Gf) ]). aobj_lin1 Gc. aobj_lin1 Gt. aobj_lin1 Gn. aobj_lin1 Gf.
    pose proof (GEOS A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as Gs. unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg in Gs.
    set (BX := fun a => (p_thr (a_pl A) + 2128 <= a < p_thr (a_pl A) + 2208) \/ (p_thr (a_pl A) + 2784 <= a < p_thr (a_pl A) + 2792) \/ (b <= a < b + 32)
                        \/ (tk <> TN /\ gq_blk a) \/ (tk = TA /\ gl <= a < gl + 8) \/ (a_ia_inited A = false /\ ia_blk a) \/ rr24 (a_ri A) a).
    assert (BXW : forall a, BX a ->
         (exists b0, In b0 (a_qthread A ++ a_qglobal A) /\ batch_addr (a_sb A) b0 <= a < batch_addr (a_sb A) b0 + kQuarantineBatchBytes)
      \/ (p_thr (a_pl A) + 2128 <= a < p_thr (a_pl A) + 2208) \/ (p_thr (a_pl A) + 2784 <= a < p_thr (a_pl A) + 2792)
      \/ (exists k, cf24 A k /\
                    chunk_addr (a_sb A) kQuarantineBatchClass k <= a < chunk_addr (a_sb A) kQuarantineBatchClass k + kQuarantineBatchBytes)
      \/ xblk a
      \/ rr24 (a_ri A) a).
    { intros a Ha. subst BX. cbv beta in Ha. destruct Ha as [Ha|[Ha|[Ha|[[_ Ha]|[[Htk Ha]|[[_ Ha]|Ha]]]]]].
      - right; left. exact Ha.
      - right; right; left. exact Ha.
      - right; right; right; left. exists kb. split; [unfold cf24; right; exact KIN|]. subst b. clear -Ha. unfold kQuarantineBatchBytes. lia.
      - do 4 right. left. right. exact Ha.
      - subst tk. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_34; dand3 dR_34 as E INg _ | destruct (GLX QGN) as (E & INg & _) ]). left. exists glb. split; [exact INg|]. rewrite <- E. clear -Ha. unfold kQuarantineBatchBytes. lia.
      - do 4 right. left. left. exact Ha.
      - do 5 right. exact Ha. }
    assert (MU' : forall a, 0 <= a < 2^64 -> ~ W0 lo uspd (p_thr (a_pl A)) p ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) a ->
                   ~ BX a -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
    { intros a Ha NW NB. apply MU. rewrite unsigned_lit by lia. unfold free_chitR_new0F_W, free_cprefix_W, free_coreR_new0F_W. rewrite !outside_app.
      unfold W0 in NW. subst BX. cbv beta in NB.
      split; [| split].
      - cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NW; clear -X LO; lia.
      - cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia | apply NB; clear -X; unfold rr24; lia].
      - destruct tk; cbn [ctail_W]; [exact I| |]; unfold free_cdtail_W, free_cdtail_WA, QINST; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X;
          first [apply NW; clear -X LO; lia | apply NB; right; right; right; first [left; split; [discriminate| unfold gq_blk; clear -X; lia] | right; left; split; [reflexivity| clear -X; lia]]]. }
    (* [comment removed for export] *)
    assert (Punw : rw_cells rsegs v' (p_thr (a_pl A) + off_th_unwinding) [C1 (Z_to_bv 8 0)]).
    { pose proof Abt as Dt. unfold apart, AMallocA.apart in Dt.
      assert (Dg : tk = TA -> gl + 24 <= p_thr (a_pl A) \/ p_thr (a_pl A) + 4096 <= gl).
      { intros ->. (first [ dand6 TAP as _ _ _ _ Agt _ | destruct TAP as (_ & _ & _ & _ & Agt & _) ]). clear -Agt. unfold apart, AMallocA.apart in Agt. lia. }
      eapply rw_cells_transport; [exact (hit_TUNW A m md AI)| exact MU| exact WM'|].
      unfold free_chitR_new0F_W, free_cprefix_W, free_coreR_new0F_W, off_th_unwinding.
      pose proof SEP_pt as Dp. pose proof SEP_n0t as Dn. pose proof SEP_f0t as Df. pose proof SEP_tr as Dr. unfold apart, AMallocA.apart in Dp, Dn, Df, Dr.
      destruct tk; [| | specialize (Dg eq_refl)]; cbn [ctail_W free_cdtail_W free_cdtail_WA app disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; unfold QINST;
        clear -Dt Dp Dn Df Dr Dg T1 T2 L1 L2 CL1 CE CEIL LOW N1 F1 S1 S2 Gc Gt Gn Gf Gs NR R8; kung_all; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    assert (NGQ : tk = TN -> forall a, BX a -> ~ gq_blk a).
    { intros -> a HB GQ. subst BX. cbv beta in HB. destruct HB as [X|[X|[X|[[X _]|[[X _]|[[_ X]|X]]]]]]; [| | | exact (X eq_refl)| discriminate| |].
      - clear -X GQ Gt. unfold gq_blk in *. kung_all. lia.
      - clear -X GQ Gt. unfold gq_blk in *. kung_all. lia.
      - clear -X GQ BLO. unfold gq_blk, kHighMemBeg in *. lia.
      - clear -X GQ. unfold gq_blk, ia_blk in *. lia.
      - clear -X GQ RILO. unfold gq_blk, rr24, kHighMemBeg in *. lia. }
    assert (NBXg : forall g a, In g (a_qglobal A) -> batch_addr (a_sb A) g <= a < batch_addr (a_sb A) g + kQuarantineBatchBytes -> tk = TN -> ~ BX a).
    { intros g a Hg Ha -> HB. assert (INg : In g (a_qthread A ++ a_qglobal A)) by (apply in_or_app; right; exact Hg).
      pose proof (batch_carved A (aview_of (pa_hull A) m) AR g INg) as Cg.
      pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as Dt.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CKB (batch_not_free A (aview_of (pa_hull A) m) AR g kQuarantineBatchClass kb INg C24 KIN)) as Dk.
      pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ Cg) as Wg. rewrite class_size_24 in Wg.
      rewrite (proj1 (c24_range A (ba_idx g))), (proj2 (c24_range A (ba_idx g))) in Dt, Dk. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in Dk.
      pose proof (batch_range A (aview_of (pa_hull A) m) AR g INg) as (Rg1 & _).
      subst BX b. cbv beta in HB. destruct HB as [X|[X|[X|[[X _]|[[X _]|[[_ X]|X]]]]]]; [| | | exact (X eq_refl)| discriminate| |].
      - clear -Ha Dt X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
      - clear -Ha Dt X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
      - clear -Ha Dk X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
      - clear -Ha Rg1 X. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
      - clear -Ha Wg X RIE. unfold rr24, batch_addr, region_beg, kQuarantineBatchClass, kQuarantineBatchBytes in *. kung_all. lia. }
    (* [comment removed for export] *)
    set (A1 := refF A).
    assert (KS24E : pk_chunks (a_cache A1 kQuarantineBatchClass) = [kb]).
    { subst A1. rewrite refF_line. unfold ref_fetched. change (Z.to_nat 1) with 1%nat. fold fr24. rewrite (skipn_last1 fr24 FNE). reflexivity. }
    assert (RX : forall c, 1 <= c <= 30 -> rg_mapped_user (a_reg A1 c) = rg_mapped_user (a_reg A c) /\ rg_mapped_fa (a_reg A1 c) = rg_mapped_fa (a_reg A c)).
    { intros c _. subst A1. cbn [refF a_reg]. unfold ref_reg. destruct (Z.eqb c kQuarantineBatchClass) eqn:Ec; [apply Z.eqb_eq in Ec; subst c; cbn; split; reflexivity| split; reflexivity]. }
    set (fe := free_entry li). set (b' := BA kb [fe]). set (qt' := [b']). set (cache' := cache_set (a_cache A1) kQuarantineBatchClass (removelast (pk_chunks (a_cache A1 kQuarantineBatchClass)))).
    assert (C'E : cache' kQuarantineBatchClass = PCc []).
    { subst cache'. unfold cache_set. rewrite Z.eqb_refl, KS24E. reflexivity. }
    assert (FE : fe = QE (li_chunk li) n0) by (subst fe; unfold free_entry; rewrite LN; reflexivity).
    assert (EB : batch_addr (a_sb A) b' = b) by reflexivity.
    assert (BB : batch_bytes b' = n0 + 8192).
    { subst b'. rewrite batch_bytes_ebytes. cbn [ba_entries]. rewrite ebytes_cons. cbn [ebytes fold_right]. subst fe. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. unfold kQuarantineBatchBytes. lia. }
    (first [ pose proof ((u64x4_of_rw v' _ _ _ _ _ Pb)) as dR_36; dand4 dR_36 as Yb0 Yb1 Yb2 Yb3 | destruct (u64x4_of_rw v' _ _ _ _ _ Pb) as (Yb0 & Yb1 & Yb2 & Yb3) ]).
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
    { cbv zeta. rewrite C'E. cbn [pk_chunks length Z.of_nat]. rewrite CI. cbn [andb negb Z.eqb Pos.eqb kQuarantineBatchClass].
      destruct Pl24c as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      apply bytes_at_app in B as [Bcnt B]. apply bytes_at_app in B as [Bmax B]. apply bytes_at_app in B as [Bsz Bks]. rewrite ?length_le4, ?length_le8 in Bmax; rewrite ?length_le4, ?length_le8 in Bsz; rewrite ?length_le4, ?length_le8 in Bks.
      assert (LKS' : length ([kw] ++ skipn 1 ks) = 16%nat) by (cbn [length app]; rewrite length_skipn, LKS; reflexivity).
      unfold u32_at, u64_at. offs. unfold kQuarantineBatchClass.
      split; [clear; cbn; lia|]. split.
      { replace (p_thr (a_pl A) + (208 + 80 * 24) + 0) with (p_thr (a_pl A) + 208 + 1920) by lia. exact Bcnt. }
      split.
      { split; [replace (p_thr (a_pl A) + (208 + 80 * 24) + 4) with (p_thr (a_pl A) + 208 + 1920 + Z.of_nat 4) by lia; replace (max_count 24) with 2 by reflexivity; exact Bmax
              | replace (p_thr (a_pl A) + (208 + 80 * 24) + 8) with (p_thr (a_pl A) + 208 + 1920 + Z.of_nat 4 + Z.of_nat 4) by lia; replace (class_size 24) with 8192 by reflexivity; exact Bsz]. }
      split.
      { intros i k E. destruct i; discriminate. }
      { apply junk_at_of_mapped; [try (generalize alloc_ceiling_val); clear -TH1; apply aobj_facts in TH1; try pose proof alloc_ceiling_val; kung_all; lia| clear; cbn; lia| try (generalize alloc_ceiling_val); clear -TH2 CE; try pose proof alloc_ceiling_val; kung_all; lia|].
        pose proof (bytes_at_mapped_gen v' _ _ Bks ltac:(try (generalize alloc_ceiling_val); clear -TH1; apply aobj_facts in TH1; try pose proof alloc_ceiling_val; kung_all; lia) ltac:(rewrite u32s_length, LKS'; try (generalize alloc_ceiling_val); clear -TH1; apply aobj_facts in TH1; try pose proof alloc_ceiling_val; kung_all; lia)) as MK. rewrite u32s_length, LKS' in MK.
        intros j Hj. replace (p_thr (a_pl A) + (208 + 80 * 24) + (16 + 4 * Z.of_nat 0) + j)
          with (p_thr (a_pl A) + 208 + 1920 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + j) by lia. apply MK. clear -Hj. lia. } }
    assert (C'O : forall c, c <> kQuarantineBatchClass -> cache' c = a_cache A c).
    { intros c Hc. subst cache'. unfold cache_set. destruct (Z.eqb_spec c kQuarantineBatchClass); [contradiction|]. subst A1. cbn [refF a_cache]. unfold reff_cache.
      destruct (Z.eqb_spec c kQuarantineBatchClass); [contradiction| reflexivity]. }
    assert (C'S : forall k, p_cached_ cache' kQuarantineBatchClass k -> p_cached_ (a_cache A) kQuarantineBatchClass k \/ p_free_ (a_reg A) kQuarantineBatchClass k).
    { intros k Hk. unfold p_cached_ in Hk. rewrite C'E in Hk. cbn [pk_chunks] in Hk. destruct Hk. }
    (* [comment removed for export] *)
    assert (R'O : forall c, c <> kQuarantineBatchClass -> a_reg A1 c = a_reg A c) by (intros c Hc; subst A1; exact (refF_reg_other A c Hc)).
    assert (R'E : rg_mapped_user (a_reg A1 kQuarantineBatchClass) = rg_mapped_user (a_reg A kQuarantineBatchClass) /\
                  rg_allocated_user (a_reg A1 kQuarantineBatchClass) = rg_allocated_user (a_reg A kQuarantineBatchClass) /\
                  rg_mapped_fa (a_reg A1 kQuarantineBatchClass) = rg_mapped_fa (a_reg A kQuarantineBatchClass)).
    { subst A1. rewrite refF_reg_QB. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. }
    assert (R'F : forall k, p_free_ (a_reg A1) kQuarantineBatchClass k -> p_free_ (a_reg A) kQuarantineBatchClass k).
    { intros k Hk. unfold p_free_ in Hk |- *. subst A1. rewrite refF_reg_QB in Hk. cbn [rg_free] in Hk. unfold ref_rest in Hk. fold fr24 in Hk. fold fr24.
      rewrite <- (firstn_skipn (length fr24 - Z.to_nat 1) fr24). apply in_or_app. left. exact Hk. }
    assert (RG24 : exists n', rg_free (a_reg A1 kQuarantineBatchClass) = firstn n' (rg_free (a_reg A kQuarantineBatchClass))).
    { exists (length fr24 - Z.to_nat 1)%nat. subst A1. rewrite refF_reg_QB. reflexivity. }
    assert (Pmx24 : u64_at rsegs v' (a_ri A + 3072) 0).
    { destruct PR as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    assert (Pnf24 : u64_at rsegs v' (a_ri A + 3088) (Z.of_nat (length (rg_free (a_reg A1 kQuarantineBatchClass))))).
    { subst A1. rewrite refF_reg_QB. cbn [rg_free]. unfold ref_rest. rewrite firstn_length. fold fr24.
      replace (Z.of_nat ((length fr24 - Z.to_nat 1) `min` length fr24)) with (nf - 1) by (subst nf; clear -FNE NF1; lia).
      destruct PNF as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. replace (a_ri A + 3088) with (a_ri A + 3072 + 16) by (clear; lia). exact B. }
    assert (HQ2 : qc_first A qt' = b) by (subst qt'; unfold qc_first; exact EB).
    (* [comment removed for export] *)
    set (qt1 := tailQt tk qt'). set (qg1 := tailQg tk qt' (a_qglobal A)).
    set (A' := freeA A1 p qt1 qg1 cache' (fst (depot_putC (a_depot A) key)) true).
    assert (Pqc' : rw_cells rsegs v' (p_thr (a_pl A) + 80)
              [C8 (wz (Z.of_nat (length qt1))); C8 (wz (qc_first A qt1)); C8 (wz (qc_last A qt1)); C8 (wz (q_bytes qt1))]).
    { subst qt1. destruct tk; cbn [tailQt tail_postR] in TPOST |- *.
      - destruct TPOST.
      - destruct TPOST as (X & _). exact X.
      - destruct TPOST as (X & _). exact X. }
    assert (Pbr' : batches_repr LPA v' (a_sb A) qt1) by (subst qt1; destruct tk; cbn [tailQt]; [exact Pbr| exact I| exact I]).
    assert (Pqcg : let I := al_instance AL_pasan + off_q_cache_list_size in
              u64_at rsegs v' (I + 0) (Z.of_nat (length qg1)) /\
              u64_at rsegs v' (I + 8) (match qg1 with [] => 0 | b0 :: _ => batch_addr (a_sb A) b0 end) /\
              u64_at rsegs v' (I + 16) (match qg1 with [] => 0 | _ => batch_addr (a_sb A) (last qg1 (BA 0 [])) end) /\
              u64_at rsegs v' (I + 24) (q_bytes qg1)).
    { subst qg1. destruct tk; cbn [tailQg tail_postR] in TPOST |- *.
      - destruct TPOST.
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). (first [ dand4 TPOST as _ _ X _ | destruct TPOST as (_ & _ & X & _) ]). rewrite QGE. cbn [app]. change (al_instance AL_pasan + off_q_cache_list_size) with (QINST + 160).
        subst gqb. rewrite QGE in X. rewrite q_bytes_nil, Z.add_0_l in X.
        apply u64x4_of_rw. subst qt'. cbn [length last Z.of_nat Pos.of_succ_nat]. rewrite q_bytes_cons, q_bytes_nil, EB, BB.
        replace (n0 + 8192 + 0) with (0 + (n0 + 8192)) by lia. exact X.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ dand5 TPOST as _ _ X _ _ | destruct TPOST as (_ & _ & X & _ & _) ]). change (al_instance AL_pasan + off_q_cache_list_size) with (QINST + 160).
        apply u64x4_of_rw. rewrite length_app, Nat2Z.inj_add, q_bytes_app.
        replace (match a_qglobal A ++ qt' with [] => 0 | b0 :: _ => batch_addr (a_sb A) b0 end) with gf by (subst gf; unfold qc_first; destruct (a_qglobal A); [congruence| reflexivity]).
        replace (match a_qglobal A ++ qt' with [] => 0 | _ :: _ => batch_addr (a_sb A) (last (a_qglobal A ++ qt') (BA 0 [])) end) with b.
        2:{ subst qt'. rewrite last_last. rewrite <- EB. destruct (a_qglobal A ++ [b']) eqn:EE; [| reflexivity]. apply app_eq_nil in EE. destruct EE; discriminate. }
        subst gn gqb qt'. cbn [length Z.of_nat Pos.of_succ_nat] in X |- *. rewrite q_bytes_cons, q_bytes_nil, BB. replace (q_bytes (a_qglobal A) + (n0 + 8192 + 0)) with (q_bytes (a_qglobal A) + (0 + (n0 + 8192))) by lia. exact X. }
    assert (Pbrg : batches_repr LPA v' (a_sb A) qg1).
    { subst qg1. destruct tk; cbn [tailQg tail_postR] in TPOST |- *.
      - destruct TPOST.
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). rewrite QGE. exact Pbr.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ dand5 TPOST as _ _ _ Pgl _ | destruct TPOST as (_ & _ & _ & Pgl & _) ]). (first [ pose proof ((GLX QGN)) as dR_44; dand7 dR_44 as E INg R1 R2 Cg NKb INgg | destruct (GLX QGN) as (E & INg & R1 & R2 & Cg & NKb & INgg) ]).
        (first [ pose proof ((ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_45; dand3 dR_45 as _ QG0 _ | destruct (ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & QG0 & _) ]). (first [ dand5 QG0 as _ _ _ _ BRG0 | destruct QG0 as (_ & _ & _ & _ & BRG0) ]). change (p_sb (a_pl A)) with (a_sb A) in BRG0.
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
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx CKB (batch_not_free A (aview_of (pa_hull A) m) AR x kQuarantineBatchClass kb INx C24 KIN)) as Dk.
          assert (NIg : ba_idx x <> ba_idx glb).
          { intros EE. pose proof BND0 as ND. rewrite map_app in ND. apply stdpp.list_relations.list.NoDup_app in ND as (_ & _ & NDg).
            pattern (a_qglobal A) at 1 in NDg. rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN), map_app in NDg. cbn [map] in NDg.
            exact (NoDup_app_In _ _ (ba_idx x) NDg ltac:(apply in_map; exact Hx) ltac:(rewrite EE; left; reflexivity)). }
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx Cg ltac:(intros EE; injection EE as EE; exact (NIg EE))) as Dgx.
          rewrite (proj1 (c24_range A (ba_idx x))), (proj2 (c24_range A (ba_idx x))) in Dt, Dn, Df, Dp, Dk, Dgx.
          rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in Dk. rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dgx.
          (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR x INx)) as dR_47; dand3 dR_47 as Rx1 Rx2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR x INx) as (Rx1 & Rx2 & _) ]).
          apply MU'; [clear -Ha' Rx1 Rx2 CE; unfold kQuarantineBatchBytes in *; kung_all; lia| |].
          * unfold W0. clear -Ha' Dt Dn Df Dp Rx1 Rx2 L1 L2 CE CEIL S2 NR Gc Gt Gn Gf Gs. unfold batch_addr, kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          * pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ Cx) as Wx. rewrite class_size_24 in Wx.
            subst BX b. cbv beta. intros [X|[X|[X|[[_ X]|[[_ X]|[[_ X]|X]]]]]].
            -- clear -Ha' Dt X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dt X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dk X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Rx1 X. unfold gq_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
            -- clear -Ha' Dgx X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Rx1 X. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
            -- clear -Ha' Wx X RIE. unfold rr24, batch_addr, region_beg, kQuarantineBatchClass, kQuarantineBatchBytes in *. kung_all. lia.
        + (* [comment removed for export] *)
          intros a' Ha'.
          pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cg) as Dn. pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cg) as Df.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CVp ltac:(intros EE; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li glb LU INg (eq_sym EE)))) as Dp.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CKB NKb) as Dk.
          rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dt, Dn, Df, Dp, Dk. rewrite (proj1 (c24_range A kb)), (proj2 (c24_range A kb)) in Dk.
          apply MU'; [clear -Ha' R1 R2 CE E; unfold batch_addr, kQuarantineBatchBytes in *; kung_all; lia| |].
          * unfold W0. subst b. clear -Ha' E Dt Dn Df Dp R1 R2 L1 L2 CE CEIL S2 NR Gc Gt Gn Gf Gs. unfold batch_addr, kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          * pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ Cg) as Wg. rewrite class_size_24 in Wg.
            subst BX b. cbv beta. intros [X|[X|[X|[[_ X]|[[_ X]|[[_ X]|X]]]]]].
            -- clear -Ha' Dt X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dt X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dk X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' R1 X E. unfold gq_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
            -- clear -Ha' X E. unfold batch_addr in *. lia.
            -- clear -Ha' R1 X E. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
            -- clear -Ha' Wg X E RIE. unfold rr24, batch_addr, region_beg, kQuarantineBatchClass, kQuarantineBatchBytes in *. kung_all. lia.
        + rewrite <- E. unfold off_qb_next. rewrite Z.add_0_r. destruct Pgl as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
        + rewrite <- E. (first [ pose proof ((batches_repr_last _ _ (removelast (a_qglobal A)) glb ltac:(unfold glb; rewrite (removelast_last_app (a_qglobal A) (BA 0 []) QGN); exact BRG0))) as dR_48; dand5 dR_48 as _ _ _ _ Mg | pose proof (batches_repr_last _ _ (removelast (a_qglobal A)) glb ltac:(unfold glb; rewrite (removelast_last_app (a_qglobal A) (BA 0 []) QGN); exact BRG0)) as (_ & _ & _ & _ & Mg) ]).
          rewrite <- E in Mg. apply (mapped_N (aview_of (pa_hull A) m) v' NN); [clear -R1; kung_all; lia| clear -R1; kung_all; lia| clear -R2 CE; unfold kQuarantineBatchBytes in *; lia| exact Mg]. }
    assert (QT'E : forall e, In e (q_entries (qt1 ++ qg1)) -> In e (q_entries (a_qthread A ++ a_qglobal A)) \/ e = QE (li_chunk li) n0).
    { intros e He. subst qt1 qg1. apply (proj1 (tailQ_entries tk qt' (a_qglobal A) e)) in He.
      subst qt' b'. cbn [q_entries flat_map ba_entries app] in He. destruct He as [E|He]; [right; rewrite <- E; exact FE|]. left. rewrite QTE. cbn [app]. exact He. }
    assert (QT'N : In (QE (li_chunk li) n0) (q_entries (qt1 ++ qg1))).
    { subst qt1 qg1. apply (proj2 (tailQ_entries tk qt' (a_qglobal A) _)). subst qt' b'. cbn [q_entries flat_map ba_entries app]. left. exact FE. }
    assert (QT'B : forall b0, In b0 (qt1 ++ qg1) -> In (ba_idx b0) (map ba_idx (a_qthread A ++ a_qglobal A)) \/ cf24 A (ba_idx b0)).
    { intros b0 Hb0. subst qt1 qg1. apply (proj1 (tailQ_batches tk qt' (a_qglobal A) b0)) in Hb0.
      subst qt'. destruct Hb0 as [<-|Hb0]; [right; subst b'; cbn [ba_idx]; unfold cf24; right; exact KIN|]. left. rewrite QTE. cbn [app]. apply in_map. exact Hb0. }
    (* [comment removed for export] *)
    assert (IAQ : ((true = a_ia_inited A /\ (forall a, iafoot a -> v' (wz a) = aview_of (pa_hull A) m (wz a))) \/ (true = true /\ ia_repr_ LPA AL_pasan true v'))
                  /\ u8_at rsegs v' 0x144e49 0 /\ bytes_at rsegs v' 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0]).
    { destruct (a_ia_inited A) eqn:EIA.
      - assert (IAW : forall a, 0xb65c0 <= a < 0x144e4c -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
        { intros a Ha. apply MU'; [clear -Ha; lia| |].
          - unfold W0. clear -Ha T1 L1 L2 CL1 CE CEIL N1 F1 S1 S2 Gc Gt Gn Gf Gs. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          - subst BX. cbv beta. intros [X|[X|[X|[[_ X]|[[Htk X]|[[X _]|X]]]]]]; [clear -Ha X Gt; kung_all; lia| clear -Ha X Gt; kung_all; lia| clear -Ha X BLO; unfold kHighMemBeg in BLO; lia| clear -Ha X; unfold gq_blk in X; lia| | discriminate| clear -Ha X RILO; unfold rr24, kHighMemBeg in *; lia].
            subst tk. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_50; dand4 dR_50 as _ _ R1 _ | destruct (GLX QGN) as (_ & _ & R1 & _) ]). clear -Ha X R1. kung_all. lia. }
        split; [| split].
        + left. split; [reflexivity|]. intros a Ha. apply IAW. unfold iafoot in Ha. cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pasan] in Ha. clear -Ha. lia.
        + pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK. unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ _ _ _ LK | destruct LK as (_ & _ & _ & _ & _ & LK) ]).
          change (al_internal_alloc_inited AL_pasan + 1) with 0x144e49 in LK. rewrite lockb_nil in LK.
          eapply (bytes_at_agree_gen _ _ _ _ _ LK). intros i Hi. cbn in Hi. apply IAW. lia.
        + pose proof (consts_cell (aview_of (pa_hull A) m) 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0] (proj1 (ar_consts _ _ _ _ _ (proj2 AR))) eq_refl) as PD.
          eapply (bytes_at_agree_gen _ _ _ _ _ PD). intros i Hi. cbn in Hi. apply IAW. lia.
      - exfalso. clear -EIA IAT. congruence. }
    (first [ dand3 IAQ as IAH IAL IAP | destruct IAQ as (IAH & IAL & IAP) ]).
    (* [comment removed for export] *)
    assert (LW : rw_cells rsegs v' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz 0)]).
    { destruct tk; cbn [tail_postR] in TPOST; [destruct TPOST| exact (proj1 (proj2 TPOST))| exact (proj1 (proj2 TPOST))]. }
    assert (QLX : u8_at rsegs v' 0xb20c8 0 /\ u8_at rsegs v' 0xb20c9 1 /\ bytes_at rsegs v' 0xb20ca [Z_to_bv 8 0; Z_to_bv 8 0]).
    { destruct LW as [[_ B] _]. cbn [cells_bytes cbytes app] in B. change (le2 (wz 0)) with [Z_to_bv 8 0; Z_to_bv 8 0] in B. change (QINST + 152) with 0xb20c8 in B.
      apply (bytes_at_app _ v' 0xb20c8 [Z_to_bv 8 0] [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0]) in B as [B1 B]. apply (bytes_at_app _ v' _ [Z_to_bv 8 1] [Z_to_bv 8 0; Z_to_bv 8 0]) in B as [B2 B3].
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in B2, B3. exact (conj B1 (conj B2 B3)). }
    (first [ dand3 QLX as QLK QRL1 QPD | destruct QLX as (QLK & QRL1 & QPD) ]).
    assert (EQA : freeA_new A1 p li key = freeA A1 p qt' (a_qglobal A) cache' (fst (depot_putC (a_depot A) key)) (a_ia_inited A)).
    { rewrite freeA_new_eq. change (a_qthread A1) with (a_qthread A). change (a_qglobal A1) with (a_qglobal A). change (a_depot A1) with (a_depot A).
      change (a_ia_inited A1) with (a_ia_inited A). rewrite KS24E at 1. unfold qpush_new. rewrite QTE. cbn [app last]. reflexivity. }
    (* [comment removed for export] *)
    assert (HULL' : ahull_of pa_image_ivs AL_pasan A' = pa_hull A).
    { subst A' A1. unfold pa_hull, ahull_of, ahull_of_, aregions_, freeA, refF. cbn [a_pl a_reg a_sec a_deadsh]. rewrite ref_classes_regions. reflexivity. }
    assert (EAG' : aeager_of A' = pa_eager A).
    { subst A' A1. unfold pa_eager, aeager_of, aeager_of_, freeA, refF. cbn [a_pl a_reg a_sec]. rewrite ref_classes_eager. reflexivity. }
    pose proof (HULL' : pa_hull A' = pa_hull A) as HULLp.
    (* [comment removed for export] *)
    set (A1e := freeA A1 p qt' (a_qglobal A) cache' (fst (depot_putC (a_depot A) key)) true).
    assert (HULL1e' : ahull_of pa_image_ivs AL_pasan A1e = pa_hull A).
    { subst A1e A1. unfold pa_hull, ahull_of, ahull_of_, aregions_, freeA, refF. cbn [a_pl a_reg a_sec a_deadsh]. rewrite ref_classes_regions. reflexivity. }
    assert (EAG1e : aeager_of A1e = pa_eager A).
    { subst A1e A1. unfold pa_eager, aeager_of, aeager_of_, freeA, refF. cbn [a_pl a_reg a_sec]. rewrite ref_classes_eager. reflexivity. }
    pose proof (HULL1e' : pa_hull A1e = pa_hull A) as HULLp1e.
    pose proof (EAG1e : pa_eager A1e = pa_eager A) as EAGp1e.
    assert (LHULL1e' : alhull_of AL_pasan A1e = pa_lhull A).   (* [comment removed for export] *)
    { subst A1e A1. unfold pa_lhull, alhull_of, alhull_of_, alregions_, freeA, refF. cbn [a_pl a_reg a_sec a_deadsh]. rewrite ref_lclasses_regions. reflexivity. }
    pose proof (LHULL1e' : pa_lhull A1e = pa_lhull A) as LHULLp1e.
    assert (TKX : tk <> TN /\ kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + (n0 + kQuarantineBatchBytes)).
    { destruct tk; [destruct TKC| |].
      - (first [ dand3 TKC as TK1 QGE TK3 | destruct TKC as (TK1 & QGE & TK3) ]). split; [discriminate|]. split; [exact TK1|]. subst gqb. rewrite QGE, q_bytes_nil. clear -TK3. lia.
      - (first [ dand3 TKC as TK1 _ TK3 | destruct TKC as (TK1 & _ & TK3) ]). split; [discriminate|]. exact (conj TK1 TK3). }
    (first [ dand3 TKX as TKN DRN BIGN | destruct TKX as (TKN & DRN & BIGN) ]).
    assert (QG1 : qg1 = a_qglobal A ++ qt') by (subst qg1; destruct tk; [exfalso; exact (TKN eq_refl)| reflexivity| reflexivity]).
    assert (QT1 : qt1 = []) by (subst qt1; destruct tk; [exfalso; exact (TKN eq_refl)| reflexivity| reflexivity]).
    assert (XE : xferA A1e = A') by (subst A1e A'; rewrite xferA_freeA, QT1, QG1; reflexivity).
    assert (WB1 : WFB (q_bytes (a_qthread A1e)) A1e).
    { subst A1e. cbn [freeA a_qthread]. rewrite <- (set_ia_freeA A1 p qt' (a_qglobal A) cache' _ (a_ia_inited A) true), IAT.
      unfold set_ia. cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid freeA].
      pose proof (free_new_WFBW A1 p li key (refF_WF A WF0 E24 NF1) LU KEYU ltac:(rewrite KS24E; discriminate) (or_introl QTE)) as X. rewrite EQA, IAT in X. change (a_qthread A1) with (a_qthread A) in X. rewrite QTE, q_bytes_nil in X.
      replace (q_bytes qt') with (0 + kQuarantineBatchBytes + qe_bytes (free_entry li)); [exact X|].
      subst qt' b' fe. rewrite q_bytes_cons, q_bytes_nil, batch_bytes_ebytes. cbn [ba_entries]. rewrite ebytes_cons. cbn [ebytes foldr]. clear. lia. }
    assert (HDRX : rw_cells rsegs v' (728408 + off_q_cache_list_size)
               [C8 (wz (Z.of_nat (length (qtransfer qt' (a_qglobal A)))));
                C8 (wz (match qtransfer qt' (a_qglobal A) with [] => 0 | b0 :: _ => batch_addr (a_sb A) b0 end));
                C8 (wz (match qtransfer qt' (a_qglobal A) with [] => 0 | _ :: _ => batch_addr (a_sb A) (last (qtransfer qt' (a_qglobal A)) (BA 0 [])) end));
                C8 (wz (q_bytes (qtransfer qt' (a_qglobal A))))]).
    { change (728408 + off_q_cache_list_size) with (QINST + 160). unfold qtransfer. rewrite length_app, Nat2Z.inj_add, q_bytes_app.
      replace (match a_qglobal A ++ qt' with [] => 0 | _ :: _ => batch_addr (a_sb A) (last (a_qglobal A ++ qt') (BA 0 [])) end) with b.
      2:{ subst qt'. rewrite last_last. rewrite <- EB. destruct (a_qglobal A ++ [b']) eqn:EE; [| reflexivity]. apply app_eq_nil in EE. destruct EE; discriminate. }
      assert (QB' : q_bytes qt' = 0 + (n0 + 8192)) by (subst qt'; rewrite q_bytes_cons, q_bytes_nil, BB; clear; lia).
      rewrite QB'.
      destruct tk; cbn [tail_postR] in TPOST; [destruct TPOST| |].
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). (first [ dand4 TPOST as _ _ X _ | destruct TPOST as (_ & _ & X & _) ]). rewrite QGE. cbn [app length Z.of_nat Pos.of_succ_nat]. rewrite q_bytes_nil, Z.add_0_l.
        subst qt'. cbn [length Z.of_nat Pos.of_succ_nat]. rewrite EB. subst gqb. rewrite QGE, q_bytes_nil, Z.add_0_l in X. exact X.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ dand5 TPOST as _ _ X _ _ | destruct TPOST as (_ & _ & X & _ & _) ]).
        replace (match a_qglobal A ++ qt' with [] => 0 | b0 :: _ => batch_addr (a_sb A) b0 end) with gf by (subst gf; unfold qc_first; destruct (a_qglobal A); [congruence| reflexivity]).
        subst gn gqb qt'. cbn [length Z.of_nat Pos.of_succ_nat]. exact X. }
    assert (QMX : ro_cells rsegs v' (QINST + 64) [C8 (wz (2^28)); C8 (wz kQuarantineMinSize)]).
    { destruct tk; cbn [tail_postR] in TPOST; [destruct TPOST| exact (proj2 (proj2 (proj2 TPOST)))| exact (proj2 (proj2 (proj2 (proj2 TPOST))))]. }
    (* [comment removed for export] *)
    assert (FROK : frame_ok LPA (pa_owned A) (pa_owned A1e) uspd (uspd - lo) (newblk p n0) nowhere (aview_of (pa_hull A) m) v').
    { subst A1e. subst A1. rewrite (freeA_refF A p qt' (a_qglobal A) cache' _ true CI).
      apply (free_frame_okF A m md p n0 li spd v' lo AI LU LN CEIL qt' (a_qglobal A) cache' _ true (a_reg (refF A)) ltac:(intros c Hc; cbn [a_reg refF] in RX; exact (RX c Hc)) BX BXW MU' WM').
      intros k Hk. destruct ST as (_ & _ & STx). destruct (STx (lo + k) ltac:(lia)) as [Wv _]. unfold wview, wa in Wv.
      rewrite unsigned_lit in Wv by (clear -Hk CEIL LOW CE SPR; lia). rewrite (pa_find_segment_none (lo + k) 1) in Wv by (clear -Hk CEIL LOW CE SPR; lia).
      destruct (aview_of (pa_hull A) m (wz (lo + k))); [discriminate| exact Wv]. }
    assert (ABOVE : forall a, uspd <= a < hi -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
    { intros a Ha. apply MU'; [clear -Ha SPR SPHI HISP; lia| |].
      + unfold W0. clear -Ha T1 T2 L1 L2 CL1 CL2 CE CEIL LOW N1 N2 F1 F2 S1 S2 Gc Gt Gn Gf Gs NR R8. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
      + intros HB. destruct (BXW a HB) as [(b0 & Hb & Rb)|[X|[X|[(k & Ck & Rk)|[X|X]]]]].
        * (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR b0 Hb)) as dR_61; dand3 dR_61 as _ Rb2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR b0 Hb) as (_ & Rb2 & _) ]). clear -Ha Rb Rb2 CE CEIL LOW. unfold kQuarantineBatchBytes in *. lia.
        * clear -Ha X T2 CEIL LOW. lia.
        * clear -Ha X T2 CEIL LOW. lia.
        * pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ (cf_carved A (aview_of (pa_hull A) m) AR k Ck)) as W.
          pose proof class_size_24 as CS24. clear -Ha Rk W CS24 CE CEIL LOW. unfold kQuarantineBatchBytes in *. kung_all. lia.
        * clear -Ha X CEIL LOW CE. unfold xblk, ia_blk, gq_blk in X. lia.
        * clear -Ha X CEIL LOW CE RIHI. unfold rr24 in *. lia. }
    assert (ERRNO : forall i, 0 <= i < 4 -> v' (wz (cl_errno LPA + i)) = aview_of (pa_hull A) m (wz (cl_errno LPA + i))).
    { intros i Hi. cbn [cl_errno LPA].
      exact (AGimg A (aview_of (pa_hull A) m) p n0 li spd v' lo AR LU LN ltac:(clear -CEIL LOW; lia) BX BXW MU' (6193972 + i) ltac:(lia) ltac:(lia) ltac:(unfold xblk, ia_blk, gq_blk; lia)). }
    assert (RXC : RECX rac spd s0 s1 s2 s3 s4 s5 s6 A m md p n0 stkobj lo hi A1e (munrestrict (hidc (pa_hull A)) m v') md').
    { constructor; rewrite ?HULLp1e, ?LHULLp1e, ?EAGp1e, ?HULL1e', ?LHULL1e', ?EAG1e, ?VIEW.
      - exact WB1.
      - subst A1e A1. cbn [freeA a_cache_inited refF]. reflexivity.
      - subst A1e A1. cbn [freeA a_qthread refF]. subst qt' b' fe. rewrite q_bytes_cons, q_bytes_nil, batch_bytes_ebytes. cbn [ba_entries]. rewrite ebytes_cons. cbn [ebytes foldr].
        unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. clear -DRN. unfold kQuarantineBatchBytes in *. lia.
      - subst A1e A1. cbn [freeA a_qthread a_qglobal refF]. subst qt' b' fe. rewrite q_bytes_cons, q_bytes_nil, batch_bytes_ebytes. cbn [ba_entries]. rewrite ebytes_cons. cbn [ebytes foldr].
        unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. clear -BIGN. unfold kQuarantineBatchBytes in *. lia.
      - subst A1e A1. cbn [freeA a_qthread a_qglobal refF]. subst qt' b' fe. rewrite q_bytes_cons, q_bytes_nil, batch_bytes_ebytes. cbn [ba_entries]. rewrite ebytes_cons. cbn [ebytes foldr].
        unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. clear -QGB NQ NR. unfold kQuarantineBatchBytes in *. lia.
      - rewrite XE. subst A'. subst A1. rewrite (freeA_refF A p qt1 qg1 cache' _ true CI).
        eapply (free_arepr3R A (aview_of (pa_hull A) m) p n0 li spd v' lo AR LU LN ltac:(clear -CEIL LOW; lia) qt1 qg1 cache' _ true (a_reg (refF A)) BX BXW MU' NN b1 _ B1R B1M IDR'
                  Punw Phdr Pctx Psh Pdr Pqc' Pbr' Pqcg Pbrg Pl24 IAH IAL IAP QLK QPD QT'E QT'B C'O C'S R'O R'E R'F RG24 Pmx24 Pnf24 QRL1).
      - subst A1e. subst A1. cbn [freeA a_pl a_reg a_sec refF].
        apply (hidden_repr_extF (a_pl A) (a_reg A) _ (a_sec A)); [intros c Hc; cbn [a_reg] in RX; exact (RX c Hc)|].
        apply (free_hiddenF A m md p n0 li spd v' lo AI LU LN CEIL BX BXW MU' WM'). exact (ai_hidden _ _ _ _ _ _ _ AI).
      - subst A1e. subst A1. cbn [freeA a_pl refF]. exact (ai_extra _ _ _ _ _ _ _ AI).
      - subst A1e. subst A1. cbn [freeA a_pl a_reg a_sec refF]. apply aledger_ref. exact (aledger_sbm _ _ _ _ md md' Hsame (ai_ledger _ _ _ _ _ _ _ AI)).   (* [comment removed for export] *)
      - exact HI'.
      - (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _) ]). rewrite HLT. exact HH.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). subst A1e. subst A1. cbn [freeA refF a_pl a_sec]. exact (ai_cover _ _ _ _ _ _ _ AI).
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_ceil _ _ _ _ _ _ _ AI).
      - (* [comment removed for export] *)
        constructor; try reflexivity.
        + intros c Hc [R0 K0]. subst A1e cache'. split.
          * subst A1. cbn [freeA a_reg refF]. unfold ref_reg. destruct (Z.eqb_spec c kQuarantineBatchClass) as [E|_]; [exfalso; exact (Hc E)| exact R0].
          * subst A1. cbn [freeA a_cache]. unfold cache_set. destruct (Z.eqb_spec c kQuarantineBatchClass) as [E|_]; [exfalso; exact (Hc E)|]. cbn [refF a_cache]. unfold reff_cache.
            destruct (Z.eqb_spec c kQuarantineBatchClass) as [E|_]; [exfalso; exact (Hc E)| exact K0].
        + exact (wamd_sbm md md' Hsame HH).
        + exact ERRNO.
        + exact FROK.
        + exact ABOVE.
      - exact MI'.
      - exact ST'.
      - exact PFR'.
      - exact LW.
      - exact HDRX.
      - exact QMX. }
    (* [comment removed for export] *)
    apply (rec_to_loop rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 CEIL LOW SPHI HISP SPA VB key KL
             A1e (munrestrict (hidc (pa_hull A)) m v') md' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' RXC).
    intros A2 m2 md2 scr ra a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s4x s6x s7x s8x s9x more NEM CU2 PL2.
    apply (rloop rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 CEIL LOW SPHI HISP SPA VB STEP_PDM STEP_SEC STEP_BDM
             (length more) A2 m2 md2 more scr ra a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s4x s6x s7x s8x s9x (le_n _) NEM CU2).
    intros A3 m3 md3 t0y t1y t2y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y X3 PL3.
    apply (loop_exit rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 CEIL LOW SPHI HISP SPA VB key KL PNB SMH li LU LN
             A3 m3 md3 t0y t1y t2y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y X3).
    - rewrite PL3, PL2. subst A1e. subst A1. reflexivity.
    - unfold dealloc_core_K. cbv zeta. exact KK.
  Qed.

  (* [comment removed for export] *)
  #[using="STEP_BDM STEP_SEC STEP_PDM VB KK NQ KR KEYU TRW STO STHI STLO SMH ST RA2 SPA HISP SPHI LOW CEIL IAT HL MI AI key hi lo Clg"] Theorem dealloc_new0RF : forall tk : ftail,
    a_qthread A = [] -> a_cache_inited A = true -> pk_chunks (a_cache A kQuarantineBatchClass) = [] ->
    1 <= Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) ->
    match tk with
    | TN => False
    | T0 => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A = [] /\ kQuarantineMaxSize < n0 + kQuarantineBatchBytes
    | TA => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A <> [] /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + (n0 + kQuarantineBatchBytes)
    end ->
    srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.
  Proof.
    intros tk QTE CI E24 NF1 TKC.
    refine (dealloc_new0RX (dealloc_entry_ms rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) _ tk QTE CI E24 NF1 TKC).
    intros tk_w b1_w fr_w fd_w ks_w na_w statv_w bj0_w bj1_w bj2_w bj3_w fr24_w gf_w gl_w gn_w gqb_w kb_w b_w kw_w nf_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EV KC.
    unfold dealloc_entry_ms. destruct (asI_minv A m md AI) as [HMI HH].
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) _ _ md T HMI HH).
    { rewrite restrict_MS. exact EV. }
    exact KC.
  Qed.
End FreeHitsRF.
