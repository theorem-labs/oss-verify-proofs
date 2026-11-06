(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSnjd ARtSrgm AMalmys ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQWf2 AQPart ACover AFreeR AFreeR2 AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2 AFreeRP AFreeRQ AFreeRU AWrapKit ACoresk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRQ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve,
                        kQuarantineBatchBytes, kQuarantineBatchCount in *.

Lemma hull_segsR {Clg : Ceiling} : forall A, H_off_segments (cl_segs LPA) (hidc (pa_hull A)).
Proof. intros A. cbn [cl_segs LPA]. unfold pa_hull, ahull_of, ahull_of_. apply pa_hull_off_segments. Qed.
Lemma pa_wxR : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma wmono_NNR : forall (v v' : mem) a, wmono rsegs v v' -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 ->
  v (wz a) <> None -> v' (wz a) <> None.
Proof.
  intros v v' a WM Ha Hr Hv. specialize (WM (wz a)). unfold wview in WM.
  rewrite unsigned_lit in WM by lia. rewrite (pa_find_segment_none a 1 ltac:(lia) Ha) in WM.
  destruct (v (wz a)); [| congruence]. destruct (v' (wz a)); [congruence|]. exfalso. apply WM; [discriminate| reflexivity].
Qed.

Lemma rw_mapped_hi : forall (v : mem) a cs, rw_cells rsegs v a cs -> 0x60a000 <= a -> a + Z.of_nat (cells_size cs) <= 2^64 -> mapped v a (Z.of_nat (cells_size cs)).
Proof.
  intros v a cs [_ (W0 & W1 & W)] Ha Hn i Hi. specialize (W i Hi). unfold wview, wa in W. rewrite unsigned_lit in W by lia.
  rewrite (pa_find_segment_none (a + i) 1 ltac:(lia) ltac:(lia)) in W. destruct (v (wz (a + i))); [discriminate| exact W].
Qed.

Lemma skipn_cons_nth : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  induction l as [|y l IH]; intros [|i] x H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn. exact (IH i x H).
Qed.

(* [comment removed for export] *)
Lemma limbo_count_bound {Clg : Ceiling} : forall A, WFR A -> Z.of_nat (length (a_qlimbo A)) <= carved_count A kQuarantineBatchClass.
Proof.
  intros A W. (first [ pose proof ((wrL A W)) as dR_1; dand3 dR_1 as LB ND _ | destruct (wrL A W) as (LB & ND & _) ]). (first [ pose proof ((wrQ A W)) as dR_2; dand3 dR_2 as _ QG _ | destruct (wrQ A W) as (_ & QG & _) ]). unfold batch_indices_ in ND. cbn [app] in ND. rewrite map_app in ND.
  apply (proj1 (list.NoDup_app _ _)) in ND as (_ & _ & ND). apply NoDup_ListNoDup in ND.
  assert (RG : forall x, In x (map ba_idx (a_qlimbo A)) -> 0 <= x < carved_count A kQuarantineBatchClass).
  { intros x Hx. apply in_map_iff in Hx as (b & <- & Hb). (first [ pose proof ((proj1 (Forall_forall _ _) LB b Hb)) as dR_3; dand3 dR_3 as _ R _ | pose proof (proj1 (Forall_forall _ _) LB b Hb) as (_ & R & _) ]). exact R. }
  assert (C0' : 0 <= carved_count A kQuarantineBatchClass).
  { (first [ pose proof ((wrR A W)) as dR_4; dand3 dR_4 as WR _ _ | destruct (wrR A W) as (WR & _ & _) ]). destruct (WR kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (R1 & _).
    unfold carved_count, carved_count_. apply Z.div_pos; [lia|]. change (class_size kQuarantineBatchClass) with 8192. lia. }
  pose proof (NoDup_incl_length ND (l' := map Z.of_nat (seq 0 (Z.to_nat (carved_count A kQuarantineBatchClass))))) as X.
  rewrite !length_map, length_seq in X. rewrite <- (Z2Nat.id (carved_count A kQuarantineBatchClass)) by lia.
  apply inj_le. apply X. intros x Hx. apply in_map_iff. exists (Z.to_nat x). pose proof (RG x Hx). split; [lia|]. apply in_seq. lia.
Qed.

Section RC.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Variables (rac spd gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet).
  (* [comment removed for export] *)
  Variables (xs2 xs5 : word).
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation T := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation v0 := (aview_of (pa_hull A0) m0).

  (* [comment removed for export] *)
  Definition put_frameG (thr : Z) (v : mem) : Prop :=
    rw_cells rsegs v (uspd + -80) [C8 (wz (thr + 208)); C8 (wz stkobj); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac].
  Definition rec_frameG (thr : Z) (v : mem) : Prop :=
    rw_cells rsegs v (T + 32) [C8 (wz (thr + 208)); C8 (wz stkobj); C8 xs2; C8 (wz (thr + 80)); C8 (wz QINST); C8 (wz 0x3b664)].
  Definition dorec_frG (thr : Z) (scr : list byte) : list cell :=
    dorec_frame scr (wz (thr + 208)) (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret).

  (* [comment removed for export] *)
  Record CURG (A : AState) (m : mem) (md : Model) (cur : option (batch * nat)) (more : list batch) (scr : list byte) : Prop := {
    cu_rinv : RINV A m md T cur more;
    cu_hist : RHIST A0 v0 md0 p n0 uspd lo hi A (aview_of (pa_hull A) m) md;
    cu_mi : mem_inv rsegs (aview_of (pa_hull A) m);
    cu_stk : stk rsegs (aview_of (pa_hull A) m) lo dsp;
    cu_put : put_frameG (p_thr (a_pl A)) (aview_of (pa_hull A) m);
    cu_rec : rec_frameG (p_thr (a_pl A)) (aview_of (pa_hull A) m);
    cu_dorec : rw_cells rsegs (aview_of (pa_hull A) m) dsp (dorec_frG (p_thr (a_pl A)) scr);
    (* [comment removed for export] *)
    cu_len : match cur with None => True | Some (b0, i) => Z.of_nat (length (ba_entries b0)) <= kQuarantineBatchCount /\ (i <= length (ba_entries b0))%nat end;
    (* [comment removed for export] *)
    cu_qb : q_bytes (a_qlimbo A) <= 2^29 + 2^21 }.

  (* [comment removed for export] *)
  Definition it_cfgG (A : AState) (m : mem) (md : Model) (b0 : batch) (i : Z) (pc : Z)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) : config :=
    mkCfg (MS (it_regs (wz dsp) gp (cl_tp LPA) T (batch_addr (a_sb A) b0) (Z.of_nat (length (ba_entries b0))) s10 s11
                       ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' i)
              F (wz pc) fc None m (seg_rom rsegs)) md.

  (* [comment removed for export] *)
  Definition head_cfgG (A : AState) (m : mem) (md : Model) (more : list batch)
      (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' : word) : config :=
    mkCfg (MS (head_regs (wz dsp) gp (cl_tp LPA) T s10 s11 ra' (Z.of_nat (length more)) a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9')
              F (wz dorec_head) fc None m (seg_rom rsegs)) md.
  Definition blk_cfgG (A : AState) (m : mem) (md : Model) (b0 : batch)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word) : config :=
    mkCfg (MS (mkR ra' (wz dsp) gp (cl_tp LPA) t0' t1' t2' (wz T) (wz 0xb1d58) a0' a1' a2' a3' a4' a5' a6' a7'
                   (wz LMA_L) (wz LMA_STAT) (wz (batch_addr (a_sb A) b0)) (wz (2^37)) s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
              F (wz dorec_batchblk) fc None m (seg_rom rsegs)) md.

  (* [comment removed for export] *)
  Definition exit_cfgG (A : AState) (m : mem) (md : Model) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) : config :=
    mkCfg (MS (mkR (wz recycle_ret) (wz T) gp (cl_tp LPA) t0' t1' t2' (wz QINST) (wz (p_thr (a_pl A) + 80)) (wz 0) a1' a2' a3' a4' a5' a6' a7'
                   xs2 (wz stkobj) (wz (p_thr (a_pl A) + 208)) xs5 (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (ret_pc (wz recycle_ret)) fc None m (seg_rom rsegs)) md.
  (* [comment removed for export] *)
  Record XCURG (A : AState) (m : mem) (md : Model) : Prop := {
    xc_rinv : RINV A m md T None [];
    xc_hist : RHIST A0 v0 md0 p n0 uspd lo hi A (aview_of (pa_hull A) m) md;
    xc_mi : mem_inv rsegs (aview_of (pa_hull A) m);
    xc_stk : stk rsegs (aview_of (pa_hull A) m) lo T;
    xc_put : put_frameG (p_thr (a_pl A)) (aview_of (pa_hull A) m);
    xc_rec : rec_frameG (p_thr (a_pl A)) (aview_of (pa_hull A) m) }.

End RC.

(* [comment removed for export] *)
