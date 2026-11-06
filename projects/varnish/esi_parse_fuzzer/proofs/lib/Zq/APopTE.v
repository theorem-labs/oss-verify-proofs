(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d ARt_3ti ARt_fpo ARt_png.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_a0k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalq4j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalrrv AMaluvs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalq4j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaluvs.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 AMTac AMallocA AMallocH AMalmys AMal9l1 AMalgue AMaly5g AMal93m AMaldga AMalkbe AMal8cv AMalzuh AMallbq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallbq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecZ ATransp ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require APopG5.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalgue OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal93m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalkbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal8cv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalzuh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallbq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallbq.AMaljju OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecZ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.   (* [comment removed for export] *)
Local Ltac natz_kl :=
  repeat match goal with
  | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
      let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit za; natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz; clear H
  | H : (@length ?A ?l <= ?b)%nat |- _ =>
      let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz; clear H
  end.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Zifyk6b.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= natz_kl; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Zifyk6b.zon_hook.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.

(* [comment removed for export] *)
Lemma munch_sym : forall W (m m' : mem), munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. exact (H x Hx). Qed.

(* [comment removed for export] *)
Ltac xf H M WMH tac :=
  lazymatch type of M with munch ?Wm ?mi ?mc =>
  lazymatch type of H with
  | ro_cells _ _ ?A ?cs => apply (ro_cells_transport rsegs Wm mi mc A cs) in H; [| exact M| cbn [disjoint_from]; simpl_sizes; tac]
  | bytes_at _ _ ?A ?bs => apply (bytes_at_transport rsegs Wm mi mc A bs) in H; [| exact M| cbn [disjoint_from]; simpl_sizes; tac]
  | rw_cells _ _ ?A ?cs => apply (rw_cells_transport rsegs Wm mi mc A cs) in H; [| exact M| exact WMH| cbn [disjoint_from]; simpl_sizes; tac]
  | u32arr _ _ ?A ?xs => apply (u32arr_transport rsegs Wm mi mc A xs) in H; [| exact M| exact WMH| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; tac]
  | u64arr _ _ ?A ?xs => apply (u64arr_transport rsegs Wm mi mc A xs) in H; [| exact M| exact WMH| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; tac]
  | u8arr _ _ ?A ?xs => apply (u8arr_transport rsegs Wm mi mc A xs) in H; [| exact M| exact WMH| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; tac]
  end end.

Section End_.
Context {Clg : Ceiling}.
  Variables (rac spa gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T1 : TSet) (ums fam nc : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  #[warnings="-notation-for-abbreviation"] Local Notation c := (class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * class_of n).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) (class_of n)).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) (class_of n) + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A (class_of n))).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A (class_of n))))).
  #[warnings="-notation-for-abbreviation"] Local Notation Ag := (popg A (class_of n) ums fam nc).
  #[warnings="-notation-for-abbreviation"] Local Notation HS := (pa_hull (popg A (class_of n) ums fam nc)).
  #[warnings="-notation-for-abbreviation"] Local Notation HLS := (pa_lhull (popg A (class_of n) ums fam nc)).   (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation W := (pop_W (bv_unsigned spa - 1024) (bv_unsigned spa) thr E R fa nf nc rb mu ums mfa fam (a_cache_inited A)).
  #[warnings="-notation-for-abbreviation"] Local Notation kk := (refill_count (class_of n)).
  (* [comment removed for export] *)
  Hypothesis EMP : pk_chunks (a_cache A c) = [].
  Hypothesis TINY : n < 16 -> 1 <= as_tinycred A.
  Hypothesis PCRED : prim_cost n <= as_primcred A.   (* [comment removed for export] *)
  Hypothesis LIM : as_livebytes A + n <= LIVE_MAX.
  Hypothesis NLV : as_nlive A + 1 <= NLIVE_MAX.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOSA : lo <= sa - 4096.
  Hypothesis SAHI : sa <= hi.
  Hypothesis HI47 : hi <= 2^47.
  Hypothesis SPA : sa mod 16 = 0.
  Hypothesis RAC2 : bv_unsigned rac mod 2 = 0.
  Hypothesis SMW : mapped v lo (hi - lo).
  Hypothesis SOLO : sa <= stkobj.
  Hypothesis SOHI : stkobj + 2064 <= hi.
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  (* [comment removed for export] *)
  Hypothesis UMS : 0 <= ums /\ ums mod kUserMapSize = 0 /\ mu + ums < au + 9 * class_size (class_of n) + kUserMapSize /\
                   au <= class_size (class_of n) * (Z.of_nat (length (a_paid A (class_of n))) + 7) + class_slack (class_of n).   (* [comment removed for export] *)
  Hypothesis FAM : 0 <= fam /\ fam mod kFreeArrayMapSize = 0 /\ mfa + fam <= 4 * (au / class_size (class_of n)) + kFreeArrayMapSize /\ mfa + fam <= kFreeArraySize.
  Hypothesis NC : 0 <= nc /\ au + nc * class_size c <= mu + ums /\ 4 * (nf + nc) <= mfa + fam.
  Hypothesis POS : mu + ums = 0 -> fam = 0 /\ nc = 0.
  Hypothesis TAIL : mu + ums < au + nc * class_size c + 9 * class_size c + kUserMapSize.
  Hypothesis ENOUGH : kk <= nf + nc.
  (* [comment removed for export] *)
  Hypothesis VNEW : forall a, rb + mu <= a < rb + mu + ums -> v (wz a) = None.
  Hypothesis VNEWF : forall a, fa + mfa <= a < fa + mfa + fam -> v (wz a) = None.
  Hypothesis K1 : alloc_core_K1v rac spa gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1.
  (* [comment removed for export] *)
  Variables (mS : mem) (mdS md5' : Model) (v5 : mem) (a0g s10v s11v na : word) (ksc : list word) (junk0 pad scr : list byte).
  Hypothesis MSH : forall a, hidc HS a = true -> mS a = m a.
  Hypothesis VMS : vm5_same (m_vmmaps md) (m_vmmaps mdS).
  Hypothesis LEDS : aledger_ AL_pboth (a_pl A) (a_reg Ag) (a_sec A) mdS.   (* [comment removed for export] *)
  Hypothesis HHS : m_halted mdS = None.
  Hypothesis AMDS : amd_frame md mdS.
  Hypothesis HI5 : MInv HS HLS (pa_eager Ag) md5'.   (* [comment removed for export] *)
  Hypothesis SB5 : same_but_materialized mdS md5'.
  Hypothesis CL5 : forall a, hidc HS a = true -> v5 a = None.
  Hypothesis MU5 : munch W v v5.
  Hypothesis NN5 : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> v5 (wz a) <> None.
  Hypothesis ST5 : stk rsegs v5 lo (sa + -128 + -48 + -32 - 128).
  Hypothesis MI5 : mem_inv rsegs v5.
  Hypothesis LKS : length ksc = 16%nat.
  (* [comment removed for export] *)
  Hypothesis P_mxL : rw_cells rsegs v5 R [C8 (wz kMutexWriter)].
  Hypothesis P_nf : rw_cells rsegs v5 (R + 16) [C8 (wz (nf + nc))].
  Hypothesis P_mfa : rw_cells rsegs v5 (R + 24) [C8 (wz (mfa + fam))].
  Hypothesis P_au : rw_cells rsegs v5 (R + 32) [C8 (wz (au + nc * class_size c))].
  Hypothesis P_mu : rw_cells rsegs v5 (R + 48) [C8 (wz (mu + ums))].
  Hypothesis P_ex : rw_cells rsegs v5 (R + 68) [C1 (Z_to_bv 8 0)].
  Hypothesis P_na : rw_cells rsegs v5 (R + 72) [C8 na].
  Hypothesis P_fa : u32arr rsegs v5 (fa + 4 * nf) (map (fun k => wz (k * class_size c / kCompactPtrScale)) (newfree (au / class_size c) nc)).
  Hypothesis P_newU : mapped v5 (rb + mu) ums.
  Hypothesis P_newF : mapped v5 (fa + mfa) fam.
  Hypothesis P_shU : bytes_at rsegs v5 (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (ums / 8))).
  Hypothesis P_shF : bytes_at rsegs v5 (sh (fa + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (fam / 8))).
  Hypothesis P_line : rw_cells rsegs v5 E [C4 (wz 0); C4 (wz (max_count c)); C8 (wz (class_size c)); CB 64 (u32s ksc)].
  Hypothesis P_lines : a_cache_inited A = false -> forall i, 1 <= i <= 31 -> i <> c ->
    exists ks, length ks = 16%nat /\ rw_cells rsegs v5 (thr + 208 + 80 * i) [C4 (wz 0); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s ks)].
  (* [comment removed for export] *)
  Hypothesis P_s1a : rw_cells rsegs v5 (sa + -128) (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0).
  Hypothesis P_comb : rw_cells rsegs v5 (sa + -128 + -48) (comb_frameR n).
  Hypothesis P_ref : rw_cells rsegs v5 (sa + -128 + -48 + -32) (refill_frame pad (wz E) (wz c) (wz comb_refill_ret)).
  Hypothesis P_gfa : rw_cells rsegs v5 (sa + -128 + -48 + -32 + -128) (gfa_frameR scr thr stkobj n (thr + 208) kk E).
  (* [comment removed for export] *)
  Hypothesis TRC5 : ro_cells rsegs v5 stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRB5 : bytes_at rsegs v5 (stkobj + 16) (u64s (map (Z_to_bv 64) key)).
  (* [comment removed for export] *)
  Variables (tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 : word).

  (* [comment removed for export] *)
  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.
  Let CEIL : alloc_ceiling <= sa - 1024. Proof. clear - CLO LOSA. lia. Qed.
  Let SPR : 0 <= sa < 2^64. Proof. pose proof (zr_word spa) as X. unfold inr64 in X. exact X. Qed.
  Let GEOn := (GEO A m md c ums fam nc spa AI CR CEIL UMS FAM NC).
  Let SHGn := (SHG A m md c ums fam nc spa AI CR CEIL UMS FAM NC POS).

  (* [comment removed for export] *)
  #[using="GEOn CEIL CR P_mxL CL5 v5 NC FAM UMS LOSA CLO NR AI lo md m spa"] Lemma R_visible : forall i, 0 <= i < 8 -> hidc HS (wz (R + i)) = false.
  Proof.
    intros i Hi. destruct (hidc HS (wz (R + i))) eqn:Hz; [| reflexivity]. exfalso.
    destruct P_mxL as [_ (W0 & W1 & WW)]. cbn [cells_size csize Nat.add] in W1, WW. specialize (WW i ltac:(clear - Hi; lia)).
    apply WW. unfold wview, wa. rewrite (CL5 _ Hz). pose proof GEOn as G.
    rewrite unsigned_lit by (clear - Hi G CE; kung_all; lia). rewrite (pa_find_segment_none (R + i) 1); [reflexivity| clear - Hi G CE; kung_all; lia| right; clear - Hi G CE; kung_all; lia].
  Qed.

  (* [comment removed for export] *)
  Definition vp : mem := write_to_mem v5 (wa R) (le8 (wz 0)).

  #[using="GEOn SPR CEIL CR LKS ksc NC FAM UMS LOSA CLO NR AI nc fam ums lo md m spa rac Clg"] Lemma MU5p : munch [(R, R + 8)] v5 vp.
  Proof.
    unfold vp. apply munch_write; [apply munch_refl| | |]; pose proof GEOn as G; rewrite ?length_le8; [clear - G; kung_all; lia| clear - G CE; kung_all; lia| cbn; lia].
  Qed.
  #[using="GEOn SPR CEIL CR LKS ksc NC FAM UMS LOSA CLO NR AI nc fam ums lo md m spa rac Clg"] Lemma MUp5 : munch [(R, R + 8)] vp v5. Proof. exact (munch_sym _ _ _ MU5p). Qed.
  Lemma WM5p : wmono rsegs v5 vp. Proof. unfold vp. apply wmono_write. apply wmono_refl. Qed.
  #[using="GEOn SPR CEIL CR LKS ksc NC FAM UMS LOSA CLO NR AI nc fam ums lo md m spa rac Clg"] Lemma AGRw : forall x : word, ~ (R <= bv_unsigned x < R + 8) -> vp x = v5 x.
  Proof. intros x Hx. apply MU5p. cbn. clear - Hx. lia. Qed.
  #[using="GEOn SPR CEIL CR LKS ksc NC FAM UMS LOSA CLO NR AI nc fam ums lo md m spa rac Clg"] Lemma AGR : forall a, 0 <= a < 2^64 -> ~ (R <= a < R + 8) -> vp (wz a) = v5 (wz a).
  Proof. intros a Ha NRa. apply AGRw. rewrite unsigned_lit by exact Ha. exact NRa. Qed.
  #[using="GEOn SPR CEIL CR P_mxL LKS ksc NC FAM UMS LOSA CLO NR AI nc fam ums lo md m spa rac Clg"] Lemma WMp5 : wmono rsegs vp v5.
  Proof.
    intros x Hx. destruct P_mxL as [_ (W0 & W1 & WW)]. cbn [cells_size csize Nat.add] in W1, WW.
    pose proof (zr_word x) as XR; unfold inr64 in XR.
    destruct (classic (R <= bv_unsigned x < R + 8)) as [IN|OUT].
    - specialize (WW (bv_unsigned x - R) ltac:(clear - IN; lia)). replace (R + (bv_unsigned x - R)) with (bv_unsigned x) in WW by lia.
      unfold wa in WW. rewrite Z_to_bv_lit_self in WW. exact WW.
    - unfold wview in *. rewrite <- (AGRw x OUT). exact Hx.
  Qed.
  #[using="P_mxL"] Lemma P_mxp : rw_cells rsegs vp R [C8 (wz 0)].
  Proof.
    unfold vp. pose proof (rw_cells_write rsegs v5 R [C8 (wz kMutexWriter)] 0 (C8 (wz kMutexWriter)) (C8 (wz 0)) P_mxL eq_refl eq_refl I) as X.
    cbn [cell_upd firstn skipn app cbytes Z.of_nat] in X. rewrite Z.add_0_r in X. exact X.
  Qed.
  #[using="GEOn SPR CEIL CR P_mxL LKS CL5 ksc NC FAM UMS LOSA CLO NR AI lo md m spa rac"] Lemma CLp : forall a, hidc HS a = true -> vp a = None.
  Proof.
    intros a Ha. pose proof (zr_word a) as XR; unfold inr64 in XR.
    destruct (classic (R <= bv_unsigned a < R + 8)) as [IN|OUT].
    - exfalso. pose proof (R_visible (bv_unsigned a - R) ltac:(clear - IN; lia)) as X.
      replace (R + (bv_unsigned a - R)) with (bv_unsigned a) in X by lia. rewrite Z_to_bv_lit_self in X. congruence.
    - rewrite (AGRw a OUT). exact (CL5 a Ha).
  Qed.
  #[using="SHGn GEOn SPR CEIL CR CE LKS MU5 ksc POS NC FAM UMS LOSA CLO CF NR AI lo canfill md rac"] Lemma MUp : munch W v vp.
  Proof.
    eapply munch_trans; [exact MU5|]. eapply munch_weaken; [| exact MU5p]. unfold sub_fp. intros x Hx. unfold pop_W in Hx. cbn [outside app] in Hx |- *. tauto.
  Qed.
  #[using="GEOn SPR CEIL CR P_mxL LKS NN5 ksc NC FAM UMS LOSA CLO NR AI nc fam ums lo md spa rac"] Lemma NNp : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> vp (wz a) <> None.
  Proof.
    intros a H0 H1 H2 H3. pose proof (NN5 a H0 H1 H2 H3) as X. destruct (classic (R <= a < R + 8)) as [IN|OUT].
    - destruct P_mxp as [_ (W0 & W1 & WW)]. cbn [cells_size csize Nat.add] in W1, WW. specialize (WW (a - R) ltac:(clear - IN; lia)).
      replace (R + (a - R)) with a in WW by lia. unfold wview, wa in WW. intros EQ. apply WW. rewrite EQ.
      pose proof GEOn as G. rewrite unsigned_lit by (clear - H0 H2; lia).
      rewrite (pa_find_segment_none a 1); [reflexivity| clear - H0 H2; lia| right; clear - IN G; kung_all; lia].
    - rewrite (AGR a ltac:(clear - H0 H2; lia) OUT). exact X.
  Qed.

  #[warnings="-notation-for-abbreviation"] Local Notation mg := (munrestrict (hidc HS) mS vp).
  #[using="GEOn SPR CEIL CR P_mxL LKS CL5 ksc NC FAM UMS LOSA CLO NR AI lo md m spa rac"] Lemma VIEWp : aview_of HS mg = vp.
  Proof. unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CLp. Qed.
  #[using="CL5"] Lemma VIEW5 : aview_of HS (munrestrict (hidc HS) mS v5) = v5.
  Proof. unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CL5. Qed.

  (* [comment removed for export] *)
  #[using="CR WF0 TAIL POS NC FAM UMS NR AI md m"] Lemma WFg : WF Ag.
  Proof. exact (pop_WF A c ums fam nc WF0 CR UMS FAM NC POS TAIL). Qed.

  #[using="SHGn GEOn SPR CEIL CR CE P_lines P_line P_shF P_shU P_newF P_newU P_fa P_ex P_mu P_au P_mfa P_nf P_mxL LKS NN5 MU5 ksc POS NC FAM UMS LOSA CLO CF EMP NR AI lo canfill md m spa rac"] Lemma Rg : @arepr _ DepotRepL LPA AL_pboth [] Ag vp.
  Proof.
    pose proof GEOn as G. pose proof SHGn as SG. pose proof MU5p as M. pose proof WM5p as WM.
    pose proof P_nf as Xnf. pose proof P_mfa as Xmfa. pose proof P_au as Xau. pose proof P_mu as Xmu. pose proof P_ex as Xex. pose proof P_fa as Xfa.
    pose proof P_shU as XshU. pose proof P_shF as XshF. pose proof P_line as Xline. pose proof P_newU as XnewU. pose proof P_newF as XnewF.
    (first [ pose proof ((GEOP A m md AI)) as dR_1; dand3 dR_1 as Gt _ _ | pose proof (GEOP A m md AI) as (Gt & _ & _) ]). aobj_lin1 Gt.
    (first [ pose proof ((ref_sep A m md n AI)) as dR_2; dand5 dR_2 as SEP_tr SEP_rs SEP_cri SEP_n0r SEP_f0r | pose proof (ref_sep A m md n AI) as (SEP_tr & SEP_rs & SEP_cri & SEP_n0r & SEP_f0r) ]). unfold AMallocA.apart in SEP_tr, SEP_rs, SEP_cri, SEP_n0r, SEP_f0r.
    xf Xnf M WM ltac:(clear; lia).
    xf Xmfa M WM ltac:(clear; lia).
    xf Xau M WM ltac:(clear; lia).
    xf Xmu M WM ltac:(clear; lia).
    xf Xex M WM ltac:(clear; lia).
    xf Xline M WM ltac:(split; [| exact I]; clear - G CR SEP_tr; kung_all; lia).
    xf Xfa M WM ltac:(split; [| exact I]; rewrite ?map_length, ?newfree_length; clear - G CR NC; kung_all; unfold region_beg in *; lia).
    xf XshU M WM ltac:(split; [| exact I]; rewrite ?repeat_length; clear - G SG CR; kung_all; unfold region_beg in *; lia).
    xf XshF M WM ltac:(split; [| exact I]; rewrite ?repeat_length; clear - G SG CR; kung_all; unfold region_beg in *; lia).
    assert (XnewUp : mapped vp (rb + mu) ums).
    { intros i Hi. rewrite (AGR (rb + mu + i)); [exact (XnewU i Hi)| clear - Hi G CE; kung_all; unfold region_beg in *; lia| clear - Hi G CR; kung_all; unfold region_beg in *; lia]. }
    assert (XnewFp : mapped vp (fa + mfa) fam).
    { intros i Hi. rewrite (AGR (fa + mfa + i)); [exact (XnewF i Hi)| clear - Hi G CE; kung_all; unfold region_beg in *; lia| clear - Hi G CR; kung_all; unfold region_beg in *; lia]. }
    refine (pop_arepr A m md c ums fam nc spa vp AI CR CEIL UMS FAM NC POS MUp NNp ksc EMP LKS P_mxp Xnf Xmfa Xau Xmu Xex Xfa XnewUp XnewFp XshU XshF Xline _).
    intros CI0 i Hi Hic. (first [ pose proof ((P_lines CI0 i Hi Hic)) as dR_3; dex1 dR_3 as ks; destruct dR_3 as [Lks Xi] | pose proof ((P_lines CI0 i Hi Hic)) as dR_3; dand3 dR_3 as ks Lks Xi | destruct (P_lines CI0 i Hi Hic) as (ks & Lks & Xi) ]). exists ks. split; [exact Lks|].
    xf Xi M WM ltac:(split; [| exact I]; clear - G Hi SEP_tr; kung_all; lia). exact Xi.
  Qed.

  (* [comment removed for export] *)
  #[using="SHGn GEOn SPR CEIL CR CE WF0 P_shF P_shU P_mxL LKS NN5 MU5 MSH ksc POS NC FAM UMS LOSA CLO CF NR AI lo canfill md m spa rac"] Lemma HIDg : hidden_repr (a_pl A) (a_reg Ag) (a_sec A) mg.
  Proof.
    pose proof GEOn as G. pose proof SHGn as SG.
    apply (pop_hidden A c ums fam nc m mg UMS FAM (ai_hidden _ _ _ _ _ _ _ AI)).
    - intros z Gz. pose proof (ai_hidden _ _ _ _ _ _ _ AI) as [H1 _]. destruct (H1 z Gz) as [PZ ZZ]. pose proof Gz as [ISM _].
      unfold munrestrict. destruct (hidc HS (wz z)) eqn:Hz; [left; exact (MSH _ Hz)|].
      assert (Z64 : 0 <= z < 2^64) by (unfold in_shadow_maps in ISM; kung_all; lia).
      unfold hidc in Hz. apply negb_false_iff in Hz. rewrite unsigned_lit in Hz by exact Z64.
      destruct (pop_hull_cases A c ums fam nc WF0 CR UMS FAM z Hz) as [OLD|[NU|[NS|[NF|NFS]]]].
      + destruct (classic (heap_shadow Ag z)) as [HSz|NHS].
        * right. split; [exact HSz|]. apply NNp; [lia| unfold in_shadow_maps in ISM; kung_all; lia| lia|].
          unfold aview_of, mrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite OLD. cbn [negb]. exact PZ.
        * left. rewrite (AGW A m c ums fam nc spa vp MUp z Z64).
          { unfold aview_of, mrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite OLD. reflexivity. }
          (first [ pose proof ((GEOP A m md AI)) as dR_4; dand3 dR_4 as Gt _ _ | pose proof (GEOP A m md AI) as (Gt & _ & _) ]). aobj_lin1 Gt.
          assert (NS1 : ~ (sh (rb + mu) <= z < sh (rb + mu) + ums / 8)).
          { intros X. apply NHS. unfold heap_shadow, heap_shadow_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_sb]. left. exists c. split; [exact CR|].
            cbv zeta. unfold reg_upd. rewrite Z.eqb_refl. cbn [grow rg_mapped_user]. change (a_sb Ag) with sb. clear - X SG G. lia. }
          assert (NF1 : ~ (sh (fa + mfa) <= z < sh (fa + mfa) + fam / 8)).
          { intros X. apply NHS. unfold heap_shadow, heap_shadow_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_sb]. right. left. exists c. split; [exact CR|].
            cbv zeta. unfold reg_upd. rewrite Z.eqb_refl. cbn [grow rg_mapped_fa]. change (a_sb Ag) with sb. clear - X SG G. lia. }
          apply (W_shape A c ums fam nc spa); unfold in_shadow_maps in ISM;
            [ clear - ISM G | clear - ISM G | clear - ISM G | clear - ISM G | clear - ISM G | clear - ISM G | clear - ISM G Gt; destruct (a_cache_inited A) | clear - ISM G Gt
            | clear - ISM G | exact NS1 | clear - ISM G | exact NF1 | clear - ISM G ]; kung_all; lia.
      + exfalso. unfold in_shadow_maps in ISM. clear - ISM NU G. kung_all. lia.
      + right. split.
        * unfold heap_shadow, heap_shadow_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_sb]. left. exists c. split; [exact CR|].
          cbv zeta. unfold reg_upd. rewrite Z.eqb_refl. cbn [grow rg_mapped_user]. change (a_sb Ag) with sb. clear - NS SG G. lia.
        * pose proof (bytes_at_mapped_gen v5 (sh (rb + mu)) _ P_shU) as MK. rewrite repeat_length, Z2Nat.id in MK by (clear - G SG; lia).
          rewrite (AGR z Z64) by (clear - NS G SG CR; kung_all; unfold region_beg in *; lia).
          replace z with (sh (rb + mu) + (z - sh (rb + mu))) by lia. apply MK; [clear - SG G; kung_all; lia| right; clear - SG G; kung_all; lia| clear - NS; lia].
      + exfalso. unfold in_shadow_maps in ISM. clear - ISM NF G. kung_all. lia.
      + right. split.
        * unfold heap_shadow, heap_shadow_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_sb]. right. left. exists c. split; [exact CR|].
          cbv zeta. unfold reg_upd. rewrite Z.eqb_refl. cbn [grow rg_mapped_fa]. change (a_sb Ag) with sb. clear - NFS SG G. lia.
        * pose proof (bytes_at_mapped_gen v5 (sh (fa + mfa)) _ P_shF) as MK. rewrite repeat_length, Z2Nat.id in MK by (clear - G SG; lia).
          rewrite (AGR z Z64) by (clear - NFS G SG CR; kung_all; unfold region_beg in *; lia).
          replace z with (sh (fa + mfa) + (z - sh (fa + mfa))) by lia. apply MK; [clear - SG G; kung_all; lia| right; clear - SG G; kung_all; lia| clear - NFS; lia].
    - intros z Hz PZ. unfold munrestrict. destruct (hidc HS (wz z)) eqn:Vz; [rewrite (MSH _ Vz); exact PZ|].
      assert (Z64 : 0 <= z < 2^64) by (kung_all; lia).
      unfold hidc in Vz. apply negb_false_iff in Vz. rewrite unsigned_lit in Vz by exact Z64.
      destruct (pop_hull_cases A c ums fam nc WF0 CR UMS FAM z Vz) as [OLD|[NU|[NS|[NF|NFS]]]].
      + apply NNp; [lia| kung_all; lia| lia|]. unfold aview_of, mrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite OLD. exact PZ.
      + exfalso. clear - Hz NU G. kung_all. lia.
      + exfalso. clear - Hz NS G SG. kung_all. lia.
      + exfalso. clear - Hz NF G. kung_all. lia.
      + exfalso. clear - Hz NFS G SG. kung_all. lia.
  Qed.

  #[using="SHGn GEOn SPR CEIL CR CE WF0 P_lines P_line P_shF P_shU P_newF P_newU P_fa P_ex P_mu P_au P_mfa P_nf P_mxL LKS NN5 MU5 CL5 SB5 HI5 AMDS HHS LEDS VMS MSH ksc mdS TAIL POS NC FAM UMS LOSA CLO CF EMP NR AI lo canfill md m spa rac"] Lemma AIg : @pa_ainv _ DepotRepL Ag mg md5'.
  Proof.
    (first [ pose proof ((s_model A m md AI mdS md5' VMS LEDS HHS AMDS SB5)) as dR_5; dand6 dR_5 as V5 LED' COV' CEIL' AMD' HH' | destruct (s_model A m md AI mdS md5' VMS LEDS HHS AMDS SB5) as (V5 & LED' & COV' & CEIL' & AMD' & HH') ]).
    constructor.
    - exact WFg.
    - change (ahull_of pa_image_ivs AL_pboth Ag) with HS. rewrite VIEWp. exact Rg.
    - exact HIDg.
    - exact (ai_extra _ _ _ _ _ _ _ AI).
    - exact LED'.
    - exact HI5.
    - exact HH'.
    - exact COV'.
    - exact CEIL'.
  Qed.

  (* [comment removed for export] *)
  #[using="SHGn GEOn SPR CEIL CR CE WF0 TRB5 TRC5 P_gfa P_ref P_comb P_s1a P_lines P_line P_shF P_shU P_newF P_newU P_fa P_ex P_mu P_au P_mfa P_nf P_mxL LKS MI5 ST5 NN5 MU5 CL5 SB5 HI5 AMDS HHS LEDS VMS MSH scr pad junk0 ksc mdS K1 VNEWF VNEW ENOUGH TAIL POS NC FAM UMS KR KEYU SOHI SOLO SMW RAC2 SPA HI47 SAHI LOSA CLO CF NLV LIM TINY PCRED EMP NR AI key hi lo stkobj canfill md m s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Theorem pop_finishG :
    srealizes (cl_segs LPA)
      (mkCfg (MS (mkR (wz gfa_popret) (wz (sa + -128 + -48 + -32 + -128)) gp (cl_tp LPA) tq0 tq1 tq2 (wz R) (wz 0xb1558) (wz 1) aq1 aq2 aq3 aq4 aq5 aq6 aq7
                     a0g (wz 2305843009213693952) (wz (free_array_of sb c)) (wz (E + 16)) (wz kk)
                     (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10v s11v tq3 tq4 tq5 tq6)
                 F (wz gfa_popret) fc None (munrestrict (hidc HS) mS v5) (seg_rom (cl_segs LPA))) md5') T1.
  Proof.
    pose proof AIg as AIG. pose proof WFg as WFG. pose proof GEOn as G. pose proof SHGn as SG.
    set (AG := Ag) in *. set (MG := mg) in *.
    assert (VIEWG : aview_of (pa_hull AG) MG = vp) by (subst AG MG; exact VIEWp).
    assert (ENOUGHg : refill_count c <= Z.of_nat (length (rg_free (a_reg AG c)))).
    { subst AG. rewrite popg_reg_c. cbn [grow rg_free]. rewrite app_length, newfree_length by (clear - NC; lia). clear - ENOUGH NC. lia. }
    assert (CIg : a_cache_inited AG = true) by (subst AG; reflexivity).
    assert (EMPg : pk_chunks (a_cache AG c) = []) by (subst AG; exact EMP).
    assert (KEYUg : In key (p_dkeys (a_pl AG))) by (subst AG; exact KEYU).
    assert (LIMg : as_livebytes AG + n <= LIVE_MAX) by (subst AG; exact LIM).
    assert (NLVg : as_nlive AG + 1 <= NLIVE_MAX) by (subst AG; exact NLV).
    assert (TINYg : n < 16 -> 1 <= as_tinycred AG) by (subst AG; exact TINY).
    assert (PCREDg : prim_cost n <= as_primcred AG) by (subst AG; exact PCRED).   (* [comment removed for export] *)
    idtac "prelude ok".
    (* [comment removed for export] *)
    (first [ pose proof ((ref_kidx AG MG md5' n AIG NR ENOUGHg)) as dR_6; dand4 dR_6 as KIN KB KNE FNE | pose proof (ref_kidx AG MG md5' n AIG NR ENOUGHg) as (KIN & KB & KNE & FNE) ]).
    set (fr := rg_free (a_reg AG (class_of n))) in *.
    set (kidx := refK AG n).
    assert (KID : kidx = nth (length fr - 1) fr 0) by reflexivity.
    rewrite <- KID in KIN, KB.
    (first [ pose proof ((hit_class n NR)) as dR_7; dand5 dR_7 as CR' HC FIT CSR CM32 | pose proof (hit_class n NR) as (CR' & HC & FIT & CSR & CM32) ]).
    (first [ pose proof ((ref_k AG n NR)) as dR_8; dand4 dR_8 as MK2 KR2 KS MR | pose proof (ref_k AG n NR) as (MK2 & KR2 & KS & MR) ]).
    (first [ pose proof ((free_geom AG MG md5' n kidx AIG NR KIN)) as dR_9; dand16 dR_9 as ABE ABA ABQ ABR1 ABR2 RZ8 SB1 SB2 RB1 RB2 FIT2 _ _ _ KWR ABU | pose proof (free_geom AG MG md5' n kidx AIG NR KIN) as (ABE & ABA & ABQ & ABR1 & ABR2 & RZ8 & SB1 & SB2 & RB1 & RB2 & FIT2 & _ & _ & _ & KWR & ABU) ]).
    (first [ pose proof ((hit_place AG MG md5' AIG)) as dR_10; dand7 dR_10 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place AG MG md5' AIG) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    (first [ pose proof ((hit_sep AG MG md5' AIG)) as dR_11; dand13 dR_11 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep AG MG md5' AIG) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]).
    (first [ pose proof ((ref_sep AG MG md5' n AIG)) as dR_12; dand5 dR_12 as SEP_tr SEP_rs SEP_cri SEP_n0r SEP_f0r | pose proof (ref_sep AG MG md5' n AIG) as (SEP_tr & SEP_rs & SEP_cri & SEP_n0r & SEP_f0r) ]).
    (first [ pose proof ((ref_ri AG MG md5' n AIG)) as dR_13; dand7 dR_13 as RIE RIL RIH RIAL SBAL _ _ | pose proof (ref_ri AG MG md5' n AIG) as (RIE & RIL & RIH & RIAL & SBAL & _ & _) ]).
    (first [ pose proof ((ref_PC AG MG md5' n AIG NR CIg EMPg)) as dR_14; dex1 dR_14 as ks; destruct dR_14 as [LKS' PC] | pose proof ((ref_PC AG MG md5' n AIG NR CIg EMPg)) as dR_14; dand3 dR_14 as ks LKS' PC | destruct (ref_PC AG MG md5' n AIG NR CIg EMPg) as (ks & LKS' & PC) ]).
    (first [ pose proof ((ref_region AG MG md5' n AIG NR ENOUGHg)) as dR_15; dex1 dR_15 as na'; dand4 dR_15 as MX NFC NAL FARR | pose proof ((ref_region AG MG md5' n AIG NR ENOUGHg)) as dR_15; dand5 dR_15 as na' MX NFC NAL FARR | destruct (ref_region AG MG md5' n AIG NR ENOUGHg) as (na' & MX & NFC & NAL & FARR) ]). fold fr in NFC, FARR.
    pose proof (ref_ws_len AG n NR ENOUGHg) as LWS. pose proof LWS as WSL. pose proof (ref_ws_last AG MG md5' n AIG NR ENOUGHg) as KW. fold fr in LWS, WSL, KW. rewrite <- KID in KW.
    (first [ pose proof ((hit_stats AG MG md5' n AIG NR)) as dR_16; dex5 dR_16 as statv v0 v1 v2 vs; dand4 dR_16 as STA STS STA2 LVS | pose proof ((hit_stats AG MG md5' n AIG NR)) as dR_16; dand9 dR_16 as statv v0 v1 v2 vs STA STS STA2 LVS | destruct (hit_stats AG MG md5' n AIG NR) as (statv & v0 & v1 & v2 & vs & STA & STS & STA2 & LVS) ]).
    (first [ pose proof ((free_HDR AG MG md5' n kidx AIG NR KIN)) as dR_17; dex5 dR_17 as b0w b1w h2 w4 d8; rename dR_17 into HDR | pose proof ((free_HDR AG MG md5' n kidx AIG NR KIN)) as dR_17; dand6 dR_17 as b0w b1w h2 w4 d8 HDR | destruct (free_HDR AG MG md5' n kidx AIG NR KIN) as (b0w & b1w & h2 & w4 & d8 & HDR) ]).
    (first [ pose proof ((free_ABH AG MG md5' n kidx AIG NR KIN)) as dR_18; dex2 dR_18 as j0 j1; rename dR_18 into ABH | pose proof ((free_ABH AG MG md5' n kidx AIG NR KIN)) as dR_18; dand3 dR_18 as j0 j1 ABH | destruct (free_ABH AG MG md5' n kidx AIG NR KIN) as (j0 & j1 & ABH) ]).
    destruct (free_USR AG MG md5' n kidx AIG NR KIN) as (uj & USR).
    pose proof (Z_div_mod_eq_full n 8) as NDE. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as ER.
    (first [ pose proof ((free_SH AG MG md5' n kidx AIG NR KIN (n / 8) (n mod 8) NDE ER)) as dR_19; dex2 dR_19 as olds oldp; dand4 dR_19 as SHA SHU OL SHP | pose proof ((free_SH AG MG md5' n kidx AIG NR KIN (n / 8) (n mod 8) NDE ER)) as dR_19; dand6 dR_19 as olds oldp SHA SHU OL SHP | destruct (free_SH AG MG md5' n kidx AIG NR KIN (n / 8) (n mod 8) NDE ER) as (olds & oldp & SHA & SHU & OL & SHP) ]).
    (first [ pose proof ((hit_depot_wf AG MG md5' AIG)) as dR_20; dand5 dR_20 as DND DLEN DTOT3 DKEY _ | pose proof (hit_depot_wf AG MG md5' AIG) as (DND & DLEN & DTOT3 & DKEY & _) ]).
    pose proof (hit_DR AG MG md5' AIG) as DR0.
    pose proof (hit_TC AG MG md5' AIG) as TC. pose proof (hit_tsd AG MG md5' AIG) as [TSD1 TSD2].
    (first [ pose proof ((sec_dkeys AG WFG)) as dR_21; dand3 dR_21 as DK1 _ DK3 | pose proof (sec_dkeys AG WFG) as (DK1 & _ & DK3) ]).
    assert (KL : (1 <= length key <= 255)%nat) by exact (proj1 (Forall_forall _ _) DK1 key KEYUg).
    assert (DTOT : depot_total (a_depot AG) + 1 + Z.of_nat (length key) < kStackStoreBlockFrames).
    { (first [ pose proof ((wfD AG WFG)) as dR_22; dand3 dR_22 as INC NDd _ | destruct (wfD AG WFG) as (INC & NDd & _) ]).
      assert (INC' : incl (a_depot AG) (p_dkeys (a_pl AG))) by (intros k0 Hk; exact (proj1 (Forall_forall _ _) INC k0 Hk)).
      (first [ pose proof ((depot_universe_bounds _ _ DK1 DK3 NDd INC')) as dR_23; dand3 dR_23 as L1 _ L3 | pose proof (depot_universe_bounds _ _ DK1 DK3 NDd INC') as (L1 & _ & L3) ]). unfold kStackStoreBlockFrames. clear - L1 L3 KL. lia. }
    assert (LO : alloc_ceiling <= lo /\ lo <= bv_unsigned spa - 1024) by (clear - CLO LOSA; lia).
    assert (SPR' : bv_unsigned spa + 65536 < 2^64) by (clear - SAHI HI47; lia).
    assert (NR64 : 1 <= n <= 64512) by (clear - NR; unfold kMaxPrimaryUser in NR; lia).
    assert (NDE' : n = 8 * (n / 8) + n mod 8) by (clear - NDE; lia).
    assert (SOA : bv_unsigned spa <= stkobj /\ stkobj + 2064 <= 2^47) by (clear - SOLO SOHI HI47; lia).
    assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e7bd8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    assert (KWR' : bv_unsigned (wz (kidx * class_size (class_of n) / kCompactPtrScale)) < 2^32) by (rewrite unsigned_lit by lia; lia).
    assert (ABE' : chunk_addr (a_sb AG) (class_of n) kidx = a_sb AG + class_of n * 2^32 + 16 * bv_unsigned (wz (kidx * class_size (class_of n) / kCompactPtrScale))) by (rewrite unsigned_lit by lia; exact ABE).
    assert (DRF : forall D' (m1 m2 : mem), depot_repL AL_pboth rsegs D' (p_nodes0 (a_pl AG)) (p_frames0 (a_pl AG)) m1 ->
              (forall a, ACells.depot_foot AL_pboth (p_nodes0 (a_pl AG)) (p_frames0 (a_pl AG)) a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) ->
              depot_repL AL_pboth rsegs D' (p_nodes0 (a_pl AG)) (p_frames0 (a_pl AG)) m2).
    { intros D' m1 m2 H1 H2. exact (depot_repL_agree AL_pboth rsegs D' _ _ m1 m2 H1 H2). }
    pose proof (ref_nf AG MG md5' n AIG NR ENOUGHg) as ((_ & NFH) & _). fold fr in NFH.
    rewrite <- KS in FARR, LWS, KW.
    idtac "facts ok".
    (* [comment removed for export] *)
    change (a_pl AG) with (a_pl A) in *. change (a_ri AG) with (a_ri A) in *. change (a_sb AG) with sb in *. change (a_depot AG) with (a_depot A) in *.
    rewrite VIEWG in *.
    pose proof (hit_PCo AG MG md5' AIG) as PCo. pose proof (hit_AF1 AG MG md5' AIG) as AF1. pose proof (hit_AF2 AG MG md5' AIG) as AF2.
    pose proof (hit_AF44 AG MG md5' AIG) as AF44. pose proof (hit_AF52 AG MG md5' AIG) as AF52. pose proof (hit_LS1 AG MG md5' AIG) as LS1.
    pose proof (hit_LS2 AG MG md5' AIG) as LS2. pose proof (hit_HK AG MG md5' AIG) as HK. pose proof (hit_SBc AG MG md5' AIG) as SBc.
    pose proof (hit_TH0 AG MG md5' AIG) as TH0. pose proof (hit_CT8 AG MG md5' AIG) as CT8.
    rewrite VIEWG in PCo, AF1, AF2, AF44, AF52, LS1, LS2, HK, SBc, TH0, CT8.
    change (a_pl AG) with (a_pl A) in TH0, CT8. change (a_sb AG) with sb in SBc.
    pose proof MUp5 as M. pose proof WMp5 as WM. unfold AMallocA.apart in SEP_tr, SEP_cri, SEP_n0r, SEP_f0r, SEP_rs.
    rewrite TPL in LS2.
    xf AF1 M WM ltac:(clear - G CE; kung_all; lia). xf AF2 M WM ltac:(clear - G CE; kung_all; lia). xf AF44 M WM ltac:(clear - G CE; kung_all; lia).
    xf AF52 M WM ltac:(clear - G CE; kung_all; lia). xf LS1 M WM ltac:(clear - G CE; kung_all; lia). xf LS2 M WM ltac:(clear - G CE; kung_all; lia).
    xf HK M WM ltac:(clear - G CE; kung_all; lia). xf SBc M WM ltac:(clear - G CE; kung_all; lia).
    xf TH0 M WM ltac:(split; [| exact I]; clear - G CR SEP_tr; kung_all; lia). xf CT8 M WM ltac:(split; [| exact I]; clear - G CR SEP_cri; kung_all; lia).
    xf PC M WM ltac:(split; [| exact I]; clear - G CR SEP_tr; kung_all; lia).
    xf NFC M WM ltac:(clear; lia). xf NAL M WM ltac:(clear; lia).
    xf FARR M WM ltac:(split; [| exact I]; left; rewrite LWS, Z2Nat.id by (rewrite KS; clear - KR2; lia); unfold free_array_of; rewrite KS; clear - G CR KR2 NFH; kung_all; lia).
    xf STA M WM ltac:(split; [| exact I]; clear - G CR SEP_tr; kung_all; lia). xf STS M WM ltac:(split; [| exact I]; clear - G CR SEP_tr; kung_all; lia).
    xf STA2 M WM ltac:(split; [| exact I]; rewrite ?LVS; clear - G CR SEP_tr; kung_all; lia).
    xf HDR M WM ltac:(split; [| exact I]; left; clear - CR ABR2 RIE FIT2 NR; kung_all; lia).
    xf ABH M WM ltac:(split; [| exact I]; left; clear - CR ABR2 RIE CSR; kung_all; lia).
    xf USR M WM ltac:(split; [| exact I]; left; clear - CR ABR2 RIE FIT2 NR; kung_all; lia).
    xf SHA M WM ltac:(split; [| exact I]; left; clear - CR SB1 ABR2 ABQ RIE CE CSR; kung_all; lia).
    xf SHU M WM ltac:(split; [| exact I]; left; rewrite OL, Z2Nat.id by (apply Z.div_pos; [clear - NR; lia | lia]); clear - CR SB1 ABR2 ABQ RZ8 RIE CE NR FIT2 CSR NDE ER; kung_all; lia).
    assert (SHP5 : n mod 8 <> 0 -> rw_cells rsegs v5 (chunk_addr sb c kidx / 8 + rz_size n / 8 + n / 8 + kShadowOffset) [C1 oldp]).
    { intros He. specialize (SHP He). xf SHP M WM ltac:(split; [| exact I]; left; clear - CR SB1 ABR2 ABQ RZ8 RIE CE NR NDE FIT2 CSR; kung_all; lia). exact SHP. }
    idtac "xfer ok".
    (* [comment removed for export] *)
    assert (PCo5 : poison_consts v5).
    { (first [ dand13 PCo as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 | destruct PCo as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13) ]).
      xf Q1 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q2 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q3 M WM ltac:(clear - RIL CR; kung_all; lia).
      xf Q4 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q5 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q6 M WM ltac:(clear - RIL CR; kung_all; lia).
      xf Q7 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q8 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q9 M WM ltac:(clear - RIL CR; kung_all; lia).
      xf Q10 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q11 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q12 M WM ltac:(clear - RIL CR; kung_all; lia).
      xf Q13 M WM ltac:(clear - RIL CR; kung_all; lia).
      exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj Q10 (conj Q11 (conj Q12 Q13)))))))))))). }
    idtac "PCo5 ok".
    assert (TC5 : thread_cells v5 (cl_tp LPA) pa_tsd (p_ctx (a_pl A)) thr).
    { (first [ dand6 TC as Q1 Q2 Q3 Q4 Q5 QR | destruct TC as (Q1 & Q2 & Q3 & Q4 & Q5 & QR) ]).
      xf Q1 M WM ltac:(clear - RIL CR; kung_all; lia). xf Q2 M WM ltac:(clear - RIL CR; kung_all; lia).
      rewrite TPL in Q3. xf Q3 M WM ltac:(clear - RIL CR; kung_all; lia). rewrite <- TPL in Q3.
      xf Q4 M WM ltac:(clear - RIL CR TSDL; kung_all; lia).
      xf Q5 M WM ltac:(split; [| exact I]; clear - RIL CR SEP_cri; kung_all; lia).
      exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 QR))))). }
    idtac "TC5 ok".
    assert (DR5 : depot_repL AL_pboth rsegs (a_depot A) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) v5).
    { apply (DRF (a_depot A) vp v5 DR0). intros a Ha. apply M. cbn [outside]. split; [| exact I].
      rewrite unsigned_lit.
      - unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1 in Ha.
        clear - Ha RIL CR SEP_n0r SEP_f0r. kung_all. lia.
      - unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1 in Ha.
        assert (N0P : 4096 <= p_nodes0 (a_pl A)) by (clear - DN01; unfold aobj in DN01; kung_all; lia).
        assert (F0P : 4096 <= p_frames0 (a_pl A)) by (clear - DF01; unfold aobj in DF01; kung_all; lia).
        clear - Ha DN02 DF02 CE N0P F0P. kung_all. lia. }
    idtac "DR5 ok".
    (* [comment removed for export] *)
    destruct (asI_minv AG MG md5' AIG) as [HMIg HHg].
    eapply (srz_evt_restrict rsegs (pa_hull AG) (asI_hull_segs AG MG md5' AIG) pa_wx _ (pa_eager AG) _ _ md5' T1 HMIg HHg).
    { rewrite restrict_MS.
      change (mrestrict (hidc (pa_hull AG)) (munrestrict (hidc (pa_hull AG)) mS v5)) with (aview_of (pa_hull AG) (munrestrict (hidc (pa_hull AG)) mS v5)).
      replace (aview_of (pa_hull AG) (munrestrict (hidc (pa_hull AG)) mS v5)) with v5 by (symmetry; exact VIEW5).
      eapply evt_cut; [eapply (gfa_popok_ok _ gp (cl_tp LPA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v5 (sa + -128 + -48 + -32) lo R sb c (Z.of_nat (length fr)) kk E 0 (max_count c) (class_size c) 1 na' (ref_ws sb c fr kk) ks scr (wz 1) (wz thr) (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1558) (wz n) (wz 0xb1558) (wz (thr + 208)) (wz 8) (wz kk) (wz E) (wz refill_ret)) | ].
      { exact MI5. }
      { exact ST5. }
      { clear - LOSA. lia. }
      { exact CLO. }
      { clear - SAHI HI47. lia. }
      { replace (sa + -128 + -48 + -32) with (sa + (-13) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact SPA. }
      { clear - RIL CR. lia. }
      { clear - RIH CR. lia. }
      { replace R with (a_ri A + (16 * c) * 8) by (clear; lia). rewrite Z_mod_plus_full. clear - RIAL. pose proof (Z.mod_divide (a_ri A) 128 ltac:(lia)) as [X _]. destruct (X RIAL) as [q ->]. replace (q * 128) with ((q * 16) * 8) by lia. apply Z_mod_mult. }
      { apply (aobj_sub thr 4096); [exact TH1| clear - CR; lia| clear; lia| clear - CR; lia]. }
      { clear - TH2 CR. lia. }
      { replace E with (thr + (13 + 5 * c) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact THRA. }
      { exact SB1. }
      { exact SB2. }
      { exact SBAL. }
      { clear - CR. lia. }
      { exact KR2. }
      { exact ENOUGHg. }
      { exact NFH. }
      { rewrite <- KS. exact LWS. }
      { exact LKS'. }
      { clear. lia. }
      { clear - MR. lia. }
      { clear - CSR. kung_all. lia. }
      { clear. lia. }
      { clear. lia. }
      { clear - SEP_tr CR. lia. }
      { unfold AMallocA.apart in SEP_thr. clear - SEP_thr CR. lia. }
      { clear - SEP_rs CR. lia. }
      { exact P_gfa. }
      { exact P_mxL. }
      { exact NFC. }
      { exact NAL. }
      { rewrite <- KS. exact FARR. }
      { exact PC. }
      { unfold refill_ret. rewrite unsigned_lit by lia. reflexivity. }
      idtac "popok premises ok".
      intros ms1 HP1. rewrite <- KS in HP1.
      eapply (alloc_tail_ok rac spa gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v5
                lo n stkobj canfill pa_tsd (p_ctx (a_pl A)) thr c (max_count c) sb (chunk_addr sb c kidx)
                (chunk_addr sb c kidx / 8) (rz_size n / 8) (n / 8) (n mod 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) (a_ri A)
                (Z.of_nat (length fr) - Z.shiftr (max_count c) 1)
                ks (ref_ws sb c fr (Z.shiftr (max_count c) 1)) b0w b1w (wz (kidx * class_size c / kCompactPtrScale)) statv na' h2 w4 d8 j0 j1 v0 v1 v2 vs
                (a_depot A) key olds uj oldp junk0 pad depot_repL).
      1: exact LO.
      1: exact SPA.
      1: exact SPR'.
      1: exact RAC2.
      1: exact NR64.
      1: exact NDE'.
      1: exact ER.
      1: exact CF.
      1: exact SOA.
      1: exact get_thread_ok.
      1: exact thread_stats_ok.
      1: exact poison_ok.
      1: exact depot_put_ok.
      1: exact classid_blk2_ok.
      1: exact PCo5.
      1: exact AF1.
      1: exact AF2.
      1: exact AF44.
      1: exact AF52.
      1: exact LS1.
      1: exact LS2.
      1: exact HK.
      1: exact SBc.
      1: exact TC5.
      1: exact TH0.
      1: exact CT8.
      1: exact (conj TH1 TH2).
      1: exact THRA.
      1: exact (conj CT1 CT2).
      1: exact TSDL.
      1: exact TPL.
      1: exact (conj SB1 SB2).
      1: exact SEP_thr.
      1: exact SEP_ctx.
      1: exact SEP_tc.
      1: exact HC.
      1: exact LKS'.
      1: exact MR.
      1: exact (conj RIL RIH).
      1: exact RIAL.
      1: exact SBAL.
      1: exact SEP_tr.
      1: exact SEP_rs.
      1: exact SEP_cri.
      1: exact SEP_n0r.
      1: exact SEP_f0r.
      1: exact LWS.
      1: { rewrite KS. clear - ENOUGHg NFH KR2. lia. }
      1: exact KW.
      1: exact KWR'.
      1: exact ABU.
      1: exact STA.
      1: exact STS.
      1: exact STA2.
      1: exact LVS.
      1: exact ABE'.
      1: exact ABA.
      1: exact ABQ.
      1: exact (conj ABR1 ABR2).
      1: exact RZ8.
      1: exact HDR.
      1: exact (fun _ => ABH).
      1: exact SHA.
      1: exact SHU.
      1: exact OL.
      1: exact SHP5.
      1: exact USR.
      1: exact DR5.
      1: exact DND.
      1: exact DLEN.
      1: exact DTOT.
      1: exact (conj DN01 DN02).
      1: exact (conj DF01 DF02).
      1: exact SEP_n0.
      1: exact SEP_f0.
      1: exact SEP_n0t.
      1: exact SEP_f0t.
      1: exact SEP_n0c.
      1: exact SEP_f0c.
      1: exact DRF.
      1: exact KL.
      1: exact KR.
      1: exact TRC5.
      1: exact TRB5.
      1: exact P_s1a.
      1: exact P_comb.
      1: exact P_ref.
      exact HP1. }
    idtac "session evt ok".
    (* [comment removed for export] *)
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex21 HQ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' v' md0; dand22 HQ as -> MU WM' MI' ST' Ppc Psta Pmx Pnf Pna Pfa Psts Psta2 Phdr Plch Pshz Pshw Pshe Pusr Pdr Pmu2 WM2 | dand36 HQ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' v' md0 -> MU WM' MI' ST' Ppc Psta Pmx Pnf Pna Pfa Psts Psta2 Phdr dR_HQ_t0; dand8 dR_HQ_t0 as Plch Pshz Pshw Pshe Pusr Pdr Pmu2 WM2 | destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & vc' & v0' & v1' & v2' & v' & md0
                    & -> & MU & WM' & MI' & ST' & Ppc & Psta & Pmx & Pnf & Pna & Pfa & Psts & Psta2 & Phdr & Plch & Pshz & Pshw & Pshe & Pusr & Pdr & Pmu2 & WM2) ]).
    rewrite KS in Ppc, Pnf.
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl |- *.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    idtac "k1 intro ok".
    assert (MMU : forall (f m1 m2 : mem), munrestrict (hidc (pa_hull AG)) (munrestrict (hidc (pa_hull AG)) f m1) m2 = munrestrict (hidc (pa_hull AG)) f m2).
    { intros f m1 m2. apply FunctionalExtensionality.functional_extensionality. intros a. unfold munrestrict. destruct (hidc (pa_hull AG) a); reflexivity. }
    change (ms_mem (MS ?r ?fr0 ?p ?c0 ?sv ?mm ?ro)) with mm.
    rewrite MMU.
    assert (VIEW' : aview_of (pa_hull AG) (munrestrict (hidc (pa_hull AG)) mS v') = v').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (MGE : munrestrict (hidc (pa_hull AG)) MG v' = munrestrict (hidc (pa_hull AG)) mS v') by (subst MG; unfold mg; apply MMU).
    idtac "k2 ok".
    assert (MUv : munch (alloc_refill_W spa thr c (chunk_addr sb c kidx) n (chunk_addr sb c kidx / 8) (rz_size n / 8) (n / 8) (n mod 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) (a_ri A)) vp v').
    { eapply munch_trans; [| exact MU]. eapply munch_weaken; [| exact MUp5]. unfold sub_fp. intros x Hx. unfold alloc_refill_W in Hx. cbn [outside] in Hx |- *.
      (* [comment removed for export] *)
      split; [| exact I]. repeat (let X := fresh "X" in destruct Hx as [X Hx]). first [ assumption | tauto ]. }
    assert (WMv : wmono rsegs vp v') by (eapply wmono_trans; [exact WMp5| exact WM']).
    idtac "k3 ok".
    assert (NNv : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> vp (wz a) <> None -> v' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NN _ _ a WMv); clear - H0 H1 H2; lia. }
    pose proof (b1_final_ok (bv_unsigned b1w) ltac:(pose proof (bv_unsigned_in_range _ b1w); lia)) as [B1R B1M].
    pose proof (rf_u_fresh AG MG md5' n AIG NR ENOUGHg) as FRu. fold kidx in FRu. (first [ pose proof ((hit_u_range AG n kidx NR)) as dR_27; dand3 dR_27 as UR1 UR2 UE | pose proof (hit_u_range AG n kidx NR) as (UR1 & UR2 & UE) ]).
    assert (IDR : 0 <= snd (depot_putC (a_depot A) key) < 2^32) by (pose proof (depot_putC_id_range (a_depot A) key) as X; clear - X DLEN; lia).
    assert (SMWp : mapped vp lo (hi - lo)).
    { intros i Hi. apply NNp; [clear - Hi CLO CE; lia| right; clear - Hi CLO CE; lia| clear - Hi HI47; lia| apply SMW; exact Hi]. }
    idtac "k4 ok".
    change (a_sb AG) with sb in UE, UR1, UR2.
    rewrite <- UE.
    pose proof (ref_fetched_length fr kk ltac:(clear - KR2 ENOUGHg; lia)) as FL.
    set (fetched := ref_fetched fr kk) in FL.
    set (ks' := ref_ws sb c fr kk ++ skipn (Z.to_nat kk) ks) in Ppc.
    assert (LKS'' : length ks' = 16%nat) by (subst ks'; rewrite app_length, length_skipn, WSL; clear - LKS' KR2; lia).
    assert (KSF : firstn (length fetched) ks' = map (fun k => wz (k * class_size c / kCompactPtrScale)) fetched).
    { subst ks' fetched. rewrite FL. rewrite firstn_app, WSL, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite WSL; lia). reflexivity. }
    replace (kk - 1) with (Z.of_nat (length fetched) - 1) in Ppc by (rewrite FL; clear - KR2; lia).
    pose proof (AMal8cv.GEO AG MG md5' n spa AIG NR ENOUGHg CEIL) as GR. fold kidx in GR.
    idtac "k5 ok".
    pose proof MUv as MUg. rewrite <- VIEWG in MUg. pose proof NNv as NNg. rewrite <- VIEWG in NNg.
    pose proof WMv as WMg. rewrite <- VIEWG in WMg. pose proof SMWp as SMWg. rewrite <- VIEWG in SMWg.
    unfold alloc_core_K1v in K1. cbn [cl_segs cl_malloc_pc LPA] in K1 |- *.
    eapply (K1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (hit_user AG n kidx) (refA AG n key) (munrestrict (hidc (pa_hull AG)) mS v') md').
    - (* [comment removed for export] *)
      rewrite <- MGE. constructor.
      + exact (ref_WF AG MG md5' n key AIG NR CIg EMPg ENOUGHg KEYUg LIMg NLVg TINYg PCREDg).
      + change (ahull_of pa_image_ivs AL_pboth (refA AG n key)) with (pa_hull (refA AG n key)). rewrite ref_hull, MGE, VIEW'.
        exact (ref_arepr AG MG md5' n key spa v' AIG NR CIg ENOUGHg CEIL MUg NNg md0 ks' _ _ LKS'' KSF Ppc Pmx Pnf B1R B1M IDR Phdr Plch Pshz Pshe Pdr Pmu2).
      + cbn [refA a_pl a_reg a_sec]. rewrite MGE.
        rewrite <- MGE. apply (ref_hidden AG MG md5' n spa v' lo AIG NR ENOUGHg CLO (proj2 LO) MUg WMg). exact (ai_hidden _ _ _ _ _ _ _ AIG).
      + cbn [refA a_pl]. exact (ai_extra _ _ _ _ _ _ _ AIG).
      + cbn [refA a_pl a_reg a_sec]. apply aledger_ref. exact (aledger_sbm _ _ _ _ md5' md' Hsame (ai_ledger _ _ _ _ _ _ _ AIG)).   (* [comment removed for export] *)
      + change (ahull_of pa_image_ivs AL_pboth (refA AG n key)) with (pa_hull (refA AG n key)). change (aeager_of (refA AG n key)) with (pa_eager (refA AG n key)).
        change (alhull_of AL_pboth (refA AG n key)) with (pa_lhull (refA AG n key)).
        rewrite ref_hull, ref_lhull, ref_eager. exact HI'.
      + (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _) ]). rewrite HLT. exact HHg.
      + cbn [refA a_pl a_sec]. rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_cover _ _ _ _ _ _ _ AIG).
      + rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_ceil _ _ _ _ _ _ _ AIG).
    - rewrite ref_hull, VIEW'. exact MI'.
    - (first [ pose proof ((s_model A m md AI mdS md5' VMS LEDS HHS AMDS SB5)) as dR_29; dand6 dR_29 as _ _ _ _ AMD' _ | destruct (s_model A m md AI mdS md5' VMS LEDS HHS AMDS SB5) as (_ & _ & _ & _ & AMD' & _) ]).
      exact (amd_frame_sbm_r md md5' md' AMD' Hsame).
    - rewrite ref_hull. exact (popg_hull_le A c ums fam nc WF0 CR UMS FAM).
    - intros ff. reflexivity.
    - reflexivity.
    - reflexivity.
    - intros c0 V [X|X]; [exfalso; clear - X NR; lia|].
      pose proof (popg_virgin_other A c ums fam nc c0 X V) as [VR VC]. split.
      + cbn [refA a_reg]. unfold ref_reg. rewrite (proj2 (Z.eqb_neq c0 (class_of n)) X). exact VR.
      + cbn [refA a_cache]. unfold ref_cache. rewrite (proj2 (Z.eqb_neq c0 (class_of n)) X). exact VC.
    - rewrite UE. clear - GR ABR1 SB1. kung_all. lia.
    - unfold as_live, as_live_. change (a_livemap A) with (a_livemap AG). rewrite FRu. reflexivity.
    - unfold as_live, as_live_. cbn [refA a_livemap]. fold kidx. rewrite lookup_insert_eq. reflexivity.
    - intros q Hq. unfold as_live, as_live_. cbn [refA a_livemap]. fold kidx. rewrite lookup_insert_ne by congruence. reflexivity.
    - unfold as_livebytes. cbn [refA a_livemap]. fold kidx. rewrite (as_livebytes_insert _ _ _ FRu). cbn [li_n]. change (a_livemap AG) with (a_livemap A). lia.
    - unfold as_tinycred. cbn [refA a_tiny]. unfold is_tiny. reflexivity.
    - unfold as_nlive. cbn [refA a_livemap]. fold kidx. rewrite (as_nlive_insert _ _ _ FRu). reflexivity.
    - unfold as_seccred. cbn [refA a_scred]. destruct (Z.ltb_spec kMaxPrimaryUser n); [exfalso; clear - H NR; lia| change (a_scred AG) with (a_scred A); lia].
    - (* [comment removed for export] *) unfold as_primcred. cbn [refA a_pcred]. rewrite (prim_cost_primary n ltac:(clear - NR; lia)). change (a_pcred AG) with (a_pcred A). reflexivity.
    - intros _ X. exfalso. clear - X NR. lia.
    - split; [intros _| intros _; clear - NR; lia]. rewrite UE. change (p_sb (a_pl A)) with sb. clear - ABR1 ABR2 GR NR CSR. kung_all. lia.
    - (* [comment removed for export] *)
      rewrite ref_hull, VIEW'.
      pose proof (ref_frame_ok AG MG md5' n key spa v' lo hi AIG NR ENOUGHg CLO (proj2 LO) SAHI HI47 MUg WMg SMWg) as FRK. rewrite VIEWG in FRK.
      apply (frame_grow_refill (pa_owned A) (pa_owned AG) (pa_owned (refA AG n key)) (newblk (hit_user AG n kidx) n) hi (hi - lo) v vp v').
      + exact (popg_owned_mono A c ums fam nc UMS FAM).
      + intros a Ha Og NO. destruct (popg_owned_new A c ums fam nc CR UMS FAM NC a Og) as [X|[X|[X|[X|X]]]]; [exfalso; exact (NO X)| | | |].
        * split; [exact (VNEW a X)|]. unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA]. clear - X G. kung_all. lia.
        * split; [exact (VNEWF a X)|]. unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA]. clear - X G. kung_all. lia.
        * exfalso. apply NO. apply (newUsh_ownedA A c ums fam WF0 CR UMS FAM). clear - X SG. lia.
        * exfalso. apply NO. apply (newFsh_ownedA A c ums fam WF0 CR UMS FAM). clear - X SG. lia.
      + intros a Ha NOg NW. replace (hi - (hi - lo)) with lo in NW by lia. apply (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3.AGW A m c ums fam nc spa vp MUp a Ha).
        apply (W_owned A c ums fam nc WF0 CR UMS FAM NC); [clear - NW LOSA SAHI; lia| exact NOg].
      + intros a Ha NI. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. apply NNp; clear - Ha NI; lia.
      + exact FRK.
    - rewrite ref_hull, VIEW'. intros i Hi. cbn [cl_errno LPA]. unfold mrd.
      rewrite (AMal8cv.AGimg AG MG md5' n spa v' AIG NR ENOUGHg CEIL MUg (6191924 + i)); [| clear - Hi; lia| clear - Hi; lia].
      rewrite VIEWG.
      rewrite (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3.AGimg A m md c ums fam nc spa vp AI CR CEIL UMS FAM NC POS MUp (6191924 + i)); [reflexivity| clear - Hi; lia| clear - Hi; lia].
    - rewrite ref_hull, VIEW'. intros a Ha.
      (first [ pose proof ((AMal8cv.USH AG MG md5' n spa AIG NR ENOUGHg CEIL)) as dR_30; dand4 dR_30 as U1 U2 U3 _ | pose proof (AMal8cv.USH AG MG md5' n spa AIG NR ENOUGHg CEIL) as (U1 & U2 & U3 & _) ]). pose proof (div8_ceil n ltac:(clear - NR; lia)) as DC. pose proof (conj RIL RIH) as RI.
      fold kidx in U3.
      transitivity (vp (wz a)).
      + rewrite <- VIEWG. apply (AMal8cv.AGW AG MG n spa v' MUg); [clear - Ha HI47 SPR; lia|].
        apply (AMal8cv.W_shape AG MG md5' n spa AIG NR ENOUGHg CEIL); fold kidx; clear - Ha HI47 SPR GR U3 DC CE RI; kung_all; lia.
      + apply (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3.AGW A m c ums fam nc spa vp MUp a); [clear - Ha HI47 SPR; lia|].
        apply (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5.APopG3.W_shape A c ums fam nc spa); (clear - Ha G SG CE LOSA CLO; try destruct (a_cache_inited A); kung_all; lia).
    - rewrite ref_hull, VIEW'. exact ST'.
  Qed.
End End_.
