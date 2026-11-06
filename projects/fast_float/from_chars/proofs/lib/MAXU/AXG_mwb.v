(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfMalloc.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngCtx MngSurgery MngNtfPre.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits AxMalloc MngZ MngMalloc AXF_mb0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb2bz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb2bz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb2bz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb2bz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb2bz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb2bz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb2bz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mb2bz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_mwm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2a OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2az OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2b OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb0z.AXF_mbtz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mbz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mbzz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mwm.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition kb_keep : list nat := [1;2;3;4;21;22;23;24;25;26;27]%nat.

(* [comment removed for export] *)
Definition oaddr (L : layout) (o : option sptr) : Z := match o with Some g => loc_addr L (LMem g) | None => 0 end.

Lemma swrap32_nz : forall av, 0 <= av < 2^32 -> (bv_swrap 32 av mod 2^64 =? 0 mod 2^64) = (av =? 0).
Proof.
  intros av Ha. destruct (Z.eqb_spec av 0) as [->|Hne]; [reflexivity|]. apply Z.eqb_neq. intros E.
  assert (W : -2^31 <= bv_swrap 32 av < 2^31).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    pose proof (Z.mod_pos_bound (av + 2 ^ Z.of_N 32 / 2) (2 ^ Z.of_N 32) ltac:(cbn; lia)) as B.
    change (2 ^ Z.of_N 32) with (2^32) in *. change (2^32 / 2) with (2^31) in *. lia. }
  assert (Z0 : bv_swrap 32 av = 0).
  { destruct (Z_le_dec 0 (bv_swrap 32 av)) as [P|P].
    - rewrite Z.mod_small in E by lia. change (0 mod 2^64) with 0 in E. exact E.
    - exfalso. replace (bv_swrap 32 av) with ((bv_swrap 32 av + 2^64) + (-1) * 2^64) in E by ring.
      rewrite Z_mod_plus_full, Z.mod_small in E by lia. change (0 mod 2^64) with 0 in E. lia. }
  pose proof (swrap32_mod av) as M. rewrite Z0 in M. change (0 mod 2^32) with 0 in M. rewrite Z.mod_small in M by lia. lia.
Qed.

Section BD.
Context {fx : FPState}.
Variables (L : layout) (s : astate) (m rom : word -> option byte) (n : Z) (regs : bvmap 5 word).
Hypothesis HW : WF s.
Hypothesis HR : repr L s (bview SEGS m).
Hypothesis Hctx : ly_ctx L = 0x97c98.
Hypothesis HP : forall q, In q (keys s) -> 1 <= loc_addr L (LMem q) /\ loc_addr L (LMem q) + 40 <= 2^47 /\ loc_addr L (LMem q) mod 8 = 0.
Hypothesis HU : forall c, 0 <= c < 48 -> usage_of s c < 2^40.
Hypothesis Mnl : rdn SEGS m (wa 0x97c23) 1 = Some (word_to_le_bytes 1 (wa 0)).
Hypothesis Mdb : forall j, 0 <= j < 32 -> rdn SEGS m (wa (98952 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn))).
Hypothesis Hn : 1 <= n <= 131051.
Hypothesis R8 : getr regs 8 = wa n.
Hypothesis R9 : getr regs 9 = wa 621712.
Hypothesis R19 : getr regs 19 = wa 98952.
Hypothesis R20 : getr regs 20 = wa (size_to_class n).

#[using="Hn"] Lemma bd_sc0 : 0 <= size_to_class n <= 47.
Proof. LiaFast.lf_pins (fun (Hn : LiaFast.U) => LiaFast.u0). pose proof (size_to_class_range n ltac:(unfold MMAP_THRESHOLD; lia)) as [A _]. lia. Qed.

(* [comment removed for export] *)
#[using="HR Hctx"] Lemma bd_act : forall k, 0 <= k < 48 -> rdn SEGS m (wa (8 * k + 621800)) 8 = Some (word_to_le_bytes 8 (wa (oaddr L (active_hd s k)))).
Proof. LiaFast.lf_pins (fun (HR Hctx : LiaFast.U) => LiaFast.u0).
  intros k Hk. pose proof (act_in_ctx_img s (Z.to_nat k) ltac:(lia)) as C.
  pose proof (repr_rdn SEGS L s m _ HR C ltac:(unfold act_cell, optr; destruct (nth (Z.to_nat k) (st_active s) None); intros zz Hzz; discriminate)
                ltac:(cbn; lia)) as Rd.
  unfold act_cell in Rd. cbn [mc_loc mc_w mc_val] in Rd. cbn [loc_addr] in Rd. rewrite Hctx, Z2Nat.id in Rd by lia.
  unfold CTX_active in Rd. replace (8 * k + 621800) with (621720 + (80 + 8 * k)) by ring. rewrite Rd. unfold active_hd, oaddr, optr.
  destruct (nth (Z.to_nat k) (st_active s) None); reflexivity.
Qed.

#[using="L HR Hctx"] Lemma bd_usage : forall k, 0 <= k < 48 -> rdn SEGS m (wa (8 * k + 622184)) 8 = Some (word_to_le_bytes 8 (wa (usage_of s k))).
Proof. LiaFast.lf_pins (fun (L HR Hctx : LiaFast.U) => LiaFast.u0).
  intros k Hk. pose proof (usage_in_ctx s (Z.to_nat k) ltac:(lia)) as C.
  assert (C' : In (MCell (LCtx (CTX_usage + 8 * Z.of_nat (Z.to_nat k))) 8 (VZ (nth (Z.to_nat k) (st_usage s) 0))) (image s))
    by (unfold image; apply in_app_iff; left; exact C).
  pose proof (repr_rdn SEGS L s m _ HR C' ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as Rd.
  cbn [mc_loc mc_w mc_val loc_addr sval_num] in Rd. rewrite Hctx, Z2Nat.id in Rd by lia.
  unfold CTX_usage in Rd. replace (8 * k + 622184) with (621720 + (464 + 8 * k)) by ring. rewrite Rd. unfold usage_of, znth. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="HW HR"] Lemma bd_meta : forall g am, MT s g = Some (MUsed am) ->
  rdn SEGS m (wa (loc_addr L (LMem g) + 24)) 4 = Some (word_to_le_bytes 4 (wa (am_avail am))) /\
  rdn SEGS m (wa (loc_addr L (LMem g) + 28)) 4 = Some (word_to_le_bytes 4 (wa (am_freed am))) /\
  (forall d kk, 0 <= d -> d + Z.of_nat kk <= 4 -> store_ok SEGS m (wa (loc_addr L (LMem g) + 24 + d)) kk = true) /\
  0 <= am_avail am <= 2^32 - 1 /\ 0 <= am_freed am <= 2^32 - 1.
Proof. LiaFast.lf_pins (fun (HW HR : LiaFast.U) => LiaFast.u0).
  intros g am HMT. pose proof (KS_of_WF s HW) as KS.
  assert (MS : forall c, In c (meta_slot_cells g (Some (MUsed am))) -> In c (image s)).
  { intros c Hc. apply (In_image_used s g am c KS HMT). left. exact Hc. }
  pose proof (repr_rdn SEGS L s m (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am))) HR (MS _ ltac:(right; right; right; left; reflexivity))
                ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as MAV.
  pose proof (repr_rdn SEGS L s m (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))) HR (MS _ ltac:(right; right; right; right; left; reflexivity))
                ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as MFR.
  cbn [mc_loc mc_w mc_val sval_num] in MAV, MFR. rewrite loc_padd in MAV, MFR. unfold META_avail, META_freed in MAV, MFR.
  assert (Hux : usedX [] s g am) by (unfold usedX, MTX; cbn [memb]; exact HMT).
  pose proof (inv_groups HW g am Hux) as G. pose proof G as (Gm & _). destruct Gm as (Mlast & Maidx & Mlen & Mav0 & Mfr0 & Mdisj & Mabove & Mabove2 & _).
  assert (Rav : 0 <= am_avail am <= 2^32 - 1).
  { split; [exact Mav0|]. assert (am_avail am < 2^32); [|lia].
    apply (lt_pow2_of_testbit (am_avail am) 32 Mav0 ltac:(lia)). intros i Hi. apply (proj1 (Mabove i ltac:(lia))). }
  assert (Rfr : 0 <= am_freed am <= 2^32 - 1).
  { split; [exact Mfr0|]. assert (am_freed am < 2^32); [|lia].
    apply (lt_pow2_of_testbit (am_freed am) 32 Mfr0 ltac:(lia)). intros i Hi. apply (proj2 (Mabove i ltac:(lia))). }
  split; [exact MAV|]. split; [exact MFR|]. split; [|split; assumption].
  intros d kk Hd Hkk. apply (store_ok_of_bytes SEGS m (loc_addr L (LMem g) + 24) 4); [|lia|lia].
  intros j Hj. pose proof (holds_wview SEGS L m (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am))) j
                 (proj1 (Forall_forall _ _) (proj1 (proj2 HR)) _ (MS _ ltac:(right; right; right; left; reflexivity))) ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as Wv.
  cbn [mc_loc] in Wv. rewrite loc_padd in Wv. unfold META_avail in Wv. exact Wv.
Qed.

(* [comment removed for export] *)
#[using="Mdb"] Lemma bd_idx : forall avail, 0 < avail <= 2^32 - 1 ->
  0 <= db_mach (wa avail) <= 31 /\
  rdn SEGS m (wa (db_mach (wa avail) + 98952)) 1 = Some (word_to_le_bytes 1 (wa (ctz32 (lowbit avail)))) /\
  0 <= ctz32 (lowbit avail) <= 31.
Proof. LiaFast.lf_pins (fun (Mdb : LiaFast.U) => LiaFast.u0).
  intros avail Ha. destruct (lowbit_pow avail ltac:(lia)) as (LP & Rj).
  assert (Ec : ctz32 (lowbit avail) = ctz32 avail).
  { destruct (lowbit_spec avail ltac:(lia)) as (j & Hj & Hlb & _). rewrite Hlb, ctz32_bit by lia.
    unfold ctz32. rewrite Hlb. unfold bit. rewrite Z.log2_pow2 by lia. reflexivity. }
  rewrite Ec. rewrite db_mach_ok by lia. pose proof (db_table_ok (ctz32 avail) Rj) as (D1 & D2).
  split; [exact D1|]. split; [|lia].
  rewrite Z.add_comm, Mdb by lia. rewrite D2. reflexivity.
Qed.

(* [comment removed for export] *)
Definition b_fast (R : bvmap 5 word) (g : sptr) (am : ameta) : Prop :=
  active_hd s (mw_sc s n) = Some g /\ MT s g = Some (MUsed am) /\ am_avail am <> 0 /\
  getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 18 = wa (loc_addr L (LMem g)) /\ getr R 19 = wa (mf_idx am) /\
  getr R 20 = wa (mw_sc s n) /\
  (forall k, In k kb_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).

Definition b_slow (R : bvmap 5 word) : Prop :=
  (forall g, active_hd s (mw_sc s n) = Some g -> exists am, MT s g = Some (MUsed am) /\ am_avail am = 0) /\
  getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa (mw_sc s n) /\ getr R 11 = wa n /\ getr R 18 = wa (mw_sc s n) /\
  getr R 20 = wa (mw_sc s n) /\ (forall k, In k kb_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).

#[using="Type"] Lemma keep_sub : forall (R : bvmap 5 word) (l : list nat), (forall k, In k l -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
  (forall k, In k kb_keep -> In k l) -> forall k, In k kb_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0. intros R l H S k Hk. exact (H k (S k Hk)). Qed.

#[using="Type"] Lemma keep_trans : forall (R R1 : bvmap 5 word) (l1 l2 : list nat),
  (forall k, In k l1 -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
  (forall k, In k l2 -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr R1 (Z_to_bv 5 (Z.of_nat k))) ->
  (forall k, In k kb_keep -> In k l1 /\ In k l2) -> forall k, In k kb_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0. intros R R1 l1 l2 H1 H2 S k Hk. destruct (S k Hk) as [A B]. rewrite (H2 k B). exact (H1 k A). Qed.

Ltac lmemb := first [ AxSymRun3.memb_refl | repeat (first [left; reflexivity | right]) ].      (* [comment removed for export] *)
Ltac kb_in := let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; unfold kb_keep in Hk; cbn [In] in Hk;
  repeat (destruct Hk as [<-|Hk]; [lmemb|]); destruct Hk.
Ltac kb_in2 := let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; unfold kb_keep in Hk; cbn [In] in Hk;
  repeat (destruct Hk as [<-|Hk]; [split; lmemb|]); destruct Hk.

#[using="HW HR Hctx HP HU Mnl Mdb Hn R8 R9 R19 R20"] Theorem b_decide :
  (exists R g am, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x5405c) (mb0_mem m (loc_addr L (LMem g)) (am_avail am)) rom)
                  /\ b_fast R g am)
  \/ (exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x54044) m rom) /\ b_slow R).
Proof. LiaFast.lf_pins (fun (HW HR Hctx HP HU Mnl Mdb Hn R8 R9 R19 R20 : LiaFast.U) => LiaFast.u0).
  pose proof bd_sc0 as Hsc0. set (sc0 := size_to_class n) in *.
  assert (Eact : forall k, 0 <= k < 48 -> active_hd s k <> None -> exists g am, active_hd s k = Some g /\ MT s g = Some (MUsed am) /\ am_sc am = k /\
             1 <= loc_addr L (LMem g) <= 2^63 - 1 /\ loc_addr L (LMem g) mod 8 = 0).
  { intros k Hk Hne. destruct (active_hd s k) as [g|] eqn:Eg; [|contradiction].
    destruct (head_used [] None U0 s k g HW Hk Eg) as (am & Hux & Hsc). pose proof (usedX_MT _ _ _ _ Hux) as [HMT _].
    destruct (HP g ltac:(eapply MT_keys; exact HMT)) as (G1 & G2 & G3). exists g, am. repeat split; try assumption; lia. }
  destruct (active_hd s sc0) as [g0|] eqn:Eg0.
  - (* [comment removed for export] *)
    assert (Msc : mw_sc s n = sc0).
    { unfold mw_sc. fold sc0. unfold active_hd in Eg0. rewrite Eg0. reflexivity. }
    destruct (Eact sc0 ltac:(lia) ltac:(rewrite Eg0; discriminate)) as (g & am & Eg & HMT & Hsc & G1 & GAL).
    rewrite Eg0 in Eg. injection Eg as <-.
    destruct (bd_meta g0 am HMT) as (MAV & MFR & MW & Rav & Rfr).
    pose proof (bd_act sc0 ltac:(lia)) as MACT. rewrite Eg0 in MACT. cbn [oaddr] in MACT.
    destruct (Z.eq_dec (am_avail am) 0) as [A0|A1].
    + right.
      assert (P : mb0_pre regs m n sc0 (loc_addr L (LMem g0)) (am_avail am) (znth 0 debruijn)).
      { constructor.
        all: first [ assumption | lia | (replace (znth 0 debruijn) with 0 by reflexivity; lia)
                   | (rewrite A0; replace (db_mach (wa 0)) with 0 by (vm_compute; reflexivity); lia)
                   | (rewrite A0; replace (db_mach (wa 0) + 98952) with (98952 + 0) by (vm_compute; reflexivity); exact (Mdb 0 ltac:(lia)))
 ]. }
      destruct (mb0_slow regs m rom n sc0 _ _ _ P A0) as (R & Hms & B8 & B9 & B10 & B11 & B18 & B19 & B20 & K).
      exists R. split; [exact Hms|]. unfold b_slow. rewrite Msc. split; [|split; [exact B8|split; [exact B9|split; [exact B10|split; [exact B11|split; [exact B18|split; [exact B20|]]]]]]].
      * intros g Hg. rewrite Eg0 in Hg. injection Hg as <-. exists am. split; [exact HMT | exact A0].
      * exact K.
    + left. destruct (bd_idx (am_avail am) ltac:(lia)) as (Rdb & Mdb' & Ridx).
      assert (P : mb0_pre regs m n sc0 (loc_addr L (LMem g0)) (am_avail am) (ctz32 (lowbit (am_avail am)))).
      { constructor. all: first [ assumption | lia ]. }
      destruct (mb0_fast regs m rom n sc0 _ _ _ P A1) as (R & Hms & B8 & B9 & B18 & B19 & B20 & K).
      exists R, g0, am. split; [exact Hms|]. unfold b_fast. rewrite Msc.
      split; [exact Eg0|]. split; [exact HMT|]. split; [exact A1|]. split; [exact B8|]. split; [exact B9|]. split; [exact B18|].
      split; [exact B19|]. split; [exact B20|]. exact K.
  - (* [comment removed for export] *)
    pose proof (bd_act sc0 ltac:(lia)) as MACT. rewrite Eg0 in MACT. cbn [oaddr] in MACT.
    set (u := usage_of s sc0).
    pose proof (bd_usage sc0 ltac:(lia)) as MUSG. fold u in MUSG.
    assert (Ru : 0 <= u <= 2^40) by (pose proof (HU sc0 ltac:(lia)); pose proof (usage_of_nonneg s sc0 (inv_ctx HW)); unfold u; lia).
    assert (P1 : mb1_pre regs m n sc0 u).
    { constructor; try assumption. all: try lia. }
    assert (Z32 : bv_unsigned (ev (Ez regs (VALS_mb1 n sc0 u)) 32) = n) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Z33 : bv_unsigned (ev (Ez regs (VALS_mb1 n sc0 u)) 33) = sc0) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Z34 : bv_unsigned (ev (Ez regs (VALS_mb1 n sc0 u)) 34) = u) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Hnone : forall g, active_hd s sc0 = Some g -> exists am, MT s g = Some (MUsed am) /\ am_avail am = 0)
      by (intros g Hg; rewrite Eg0 in Hg; discriminate).
    (* [comment removed for export] *)
    assert (NC : forall R, getr R 8 = wa n -> getr R 9 = wa 621712 -> getr R 10 = wa sc0 -> getr R 11 = wa n -> getr R 18 = wa sc0 ->
               getr R 20 = wa sc0 -> (forall k, In k kb_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
               mw_sc s n = sc0 -> b_slow R).
    { intros R A8 A9 A10 A11 A18 A20 K E. unfold b_slow. rewrite E. split; [exact Hnone|]. repeat (split; [assumption|]). assumption. }
    assert (Msc0 : ~ (4 <= sc0 <= 31 /\ sc0 <> 6 /\ Z.even sc0 = true /\ u = 0) -> mw_sc s n = sc0).
    { intros H. unfold mw_sc. fold sc0. unfold active_hd in Eg0. rewrite Eg0. cbn [osptr_eqb andb].
      destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage_of s sc0 =? 0)) eqn:Ec; [|reflexivity].
      exfalso. apply H. apply andb_true_iff in Ec as [Ec E5]. apply andb_true_iff in Ec as [Ec E4]. apply andb_true_iff in Ec as [Ec E3].
      apply andb_true_iff in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply negb_true_iff, Z.eqb_neq in E3.
      apply Z.eqb_eq in E5. fold u in E5. repeat split; try lia; exact E4. }
    destruct (Z.eq_dec sc0 6) as [E6|N6].
    { right. destruct (mb1_pb1a regs m rom n sc0 u P1) as (R & Hms & A8 & A9 & A10 & A11 & _ & A18 & _ & A20 & K).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb1.RES_pb1a fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z33.
        rewrite br_eq_z. rewrite E6. reflexivity. }
      exists R. split; [exact Hms|]. apply NC; try assumption.
      - apply (keep_sub R _ K). kb_in.
      - apply Msc0. lia. }
    destruct (Z_le_dec 4 sc0) as [L4|L4]; [destruct (Z_le_dec sc0 31) as [L31|L31]|].
    3:{ right. destruct (mb1_pb1b regs m rom n sc0 u P1) as (R & Hms & A8 & A9 & A10 & A11 & _ & A18 & _ & A20 & K).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb1.RES_pb1b fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z33.
          - rewrite br_ltu_z. apply Z.ltb_lt. rewrite (Z.mod_small 27) by lia.
            replace (sc0 + -4) with ((sc0 - 4 + 2^64) + (-1) * 2^64) by ring. rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
          - rewrite br_eq_z. apply Z.eqb_neq. rewrite !Z.mod_small by lia. exact N6. }
        exists R. split; [exact Hms|]. apply NC; try assumption.
        - apply (keep_sub R _ K). kb_in.
        - apply Msc0. lia. }
    2:{ right. destruct (mb1_pb1b regs m rom n sc0 u P1) as (R & Hms & A8 & A9 & A10 & A11 & _ & A18 & _ & A20 & K).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb1.RES_pb1b fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z33.
          - rewrite br_ltu_z. apply Z.ltb_lt. rewrite !Z.mod_small by lia. lia.
          - rewrite br_eq_z. apply Z.eqb_neq. rewrite !Z.mod_small by lia. exact N6. }
        exists R. split; [exact Hms|]. apply NC; try assumption.
        - apply (keep_sub R _ K). kb_in.
        - apply Msc0. lia. }
    assert (SC4 : branch_taken BC_LTU (wa (zeval (Ez regs (VALS_mb1 n sc0 u)) (ELit 27))) (wa (zeval (Ez regs (VALS_mb1 n sc0 u)) (EAlu ALU_ADD (EVar 33) (ELit (-4))))) = false).
    { cbn [zeval edenot]. rewrite Z33. rewrite br_ltu_z. apply Z.ltb_ge. rewrite !Z.mod_small by lia. lia. }
    assert (SC6 : branch_taken BC_EQ (wa (zeval (Ez regs (VALS_mb1 n sc0 u)) (EVar 33))) (wa (zeval (Ez regs (VALS_mb1 n sc0 u)) (ELit 6))) = false).
    { cbn [zeval edenot]. rewrite Z33. rewrite br_eq_z. apply Z.eqb_neq. rewrite !Z.mod_small by lia. exact N6. }
    destruct (Z.even sc0) eqn:Ev.
    2:{ right. destruct (mb1_pb1c regs m rom n sc0 u P1) as (R & Hms & A8 & A9 & A10 & A11 & _ & A18 & _ & A20 & K).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb1.RES_pb1c fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
          - cbn [zeval edenot]. rewrite Z33. rewrite br_ne_z. apply negb_true_iff, Z.eqb_neq.
            rewrite (Z.mod_small sc0) by lia. rewrite (Z.mod_small 1) by lia.
            assert (E1 : Z.land sc0 1 = sc0 mod 2^1) by (rewrite <- (Z.land_ones sc0 1) by lia; reflexivity). rewrite E1.
            change (2^1) with 2. pose proof (Z.mod_pos_bound sc0 2 ltac:(lia)) as B2.
            rewrite (Z.mod_small (sc0 mod 2)) by lia. change (0 mod 2^64) with 0.
            rewrite Zeven_mod in Ev. apply Bool.not_true_iff_false in Ev. intros E. apply Ev. apply Z.eqb_eq. exact E.
          - exact SC4.
          - exact SC6. }
        exists R. split; [exact Hms|]. apply NC; try assumption.
        - apply (keep_sub R _ K). kb_in.
        - apply Msc0. intros (_ & _ & E & _). congruence. }
    assert (SCo : branch_taken BC_NE (wa (zeval (Ez regs (VALS_mb1 n sc0 u)) (EAlu ALU_AND (EVar 33) (ELit 1)))) (wa (zeval (Ez regs (VALS_mb1 n sc0 u)) (ELit 0))) = false).
    { cbn [zeval edenot]. rewrite Z33. rewrite br_ne_z. apply negb_false_iff, Z.eqb_eq.
      rewrite (Z.mod_small sc0) by lia. rewrite (Z.mod_small 1) by lia.
      assert (E1 : Z.land sc0 1 = sc0 mod 2^1) by (rewrite <- (Z.land_ones sc0 1) by lia; reflexivity). rewrite E1.
      change (2^1) with 2. pose proof (Z.mod_pos_bound sc0 2 ltac:(lia)) as B2.
      rewrite (Z.mod_small (sc0 mod 2)) by lia. change (0 mod 2^64) with 0.
      rewrite Zeven_mod in Ev. apply Z.eqb_eq in Ev. exact Ev. }
    destruct (Z.eq_dec u 0) as [U0|U1].
    2:{ right. destruct (mb1_pb1d regs m rom n sc0 u P1) as (R & Hms & A8 & A9 & A10 & A11 & _ & A18 & _ & A20 & K).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb1.RES_pb1d fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
          - cbn [zeval edenot]. rewrite Z34. rewrite br_eq_z. apply Z.eqb_neq. rewrite !Z.mod_small by lia. exact U1.
          - exact SCo.
          - exact SC4.
          - exact SC6. }
        exists R. split; [exact Hms|]. apply NC; try assumption.
        - apply (keep_sub R _ K). kb_in.
        - apply Msc0. lia. }
    (* [comment removed for export] *)
    destruct (mb1_pb1e regs m rom n sc0 u P1) as (R1 & Hms1 & A8 & A9 & A10 & A11 & A12 & A18 & A19 & A20 & K1).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb1.RES_pb1e fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
      - cbn [zeval edenot]. rewrite Z34. rewrite br_eq_z. apply Z.eqb_eq. rewrite U0. reflexivity.
      - exact SCo.
      - exact SC4.
      - exact SC6. }
    assert (L30 : sc0 <= 30) by (rewrite Zeven_mod in Ev; apply Z.eqb_eq in Ev; destruct (Z.eq_dec sc0 31) as [E31|]; [rewrite E31 in Ev; discriminate | lia]).
    assert (Ka3 : sc0 mod 2 = 0) by (rewrite Zeven_mod in Ev; apply Z.eqb_eq in Ev; exact Ev).
    set (u1 := usage_of s (sc0 + 1)).
    assert (Ru1 : 0 <= u1 <= 2^40) by (pose proof (HU (sc0 + 1) ltac:(lia)); pose proof (usage_of_nonneg s (sc0 + 1) (inv_ctx HW)); unfold u1; lia).
    pose proof (bd_usage (sc0 + 1) ltac:(lia)) as MUSG1. fold u1 in MUSG1. replace (8 * (sc0 + 1) + 622184) with (8 * sc0 + 622192) in MUSG1 by ring.
    pose proof (bd_act (sc0 + 1) ltac:(lia)) as MACT1. replace (8 * (sc0 + 1) + 621800) with (8 * sc0 + 621808) in MACT1 by ring.
    assert (Msc : mw_sc s n = (if (if match active_hd s (sc0 + 1) with
                                       | None => true
                                       | Some h => match mlookup (st_metas s) h with
                                                   | Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0)
                                                   | _ => true
                                                   end
                                       end then u1 + 3 else u1) <=? 12 then sc0 + 1 else sc0)).
    { unfold mw_sc. fold sc0. unfold active_hd in Eg0. rewrite Eg0. cbn [osptr_eqb andb].
      replace ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage_of s sc0 =? 0)) with true.
      2:{ symmetry. rewrite Ev. fold u. rewrite U0. replace (4 <=? sc0) with true by (symmetry; apply Z.leb_le; lia).
          replace (sc0 <? 32) with true by (symmetry; apply Z.ltb_lt; lia). replace (sc0 =? 6) with false by (symmetry; apply Z.eqb_neq; exact N6).
          reflexivity. }
      fold u1. unfold active_hd. reflexivity. }
    assert (K1' : forall k, In k kb_keep -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) by (apply (keep_sub R1 _ K1); kb_in).
    destruct (active_hd s (sc0 + 1)) as [h0|] eqn:Eh0.
    2:{ (* [comment removed for export] *)
        cbn [oaddr] in MACT1.
        assert (P2 : mb2a_pre R1 m n sc0 u1) by (constructor; try assumption; lia).
        assert (Y34 : bv_unsigned (ev (Ez R1 (VALS_mb2a n sc0 u1)) 34) = u1) by (apply zatom; [reflexivity | reflexivity | lia]).
        right. destruct (Z_lt_le_dec (u1 + 3) 13) as [Lt|Ge].
        - destruct (mb2a_pb2at R1 m rom n sc0 u1 P2) as (R & Hms & B8 & B9 & B10 & B11 & _ & B18 & _ & B20 & K).
          { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2a.RES_pb2at fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Y34.
            rewrite br_ltu_z. apply Z.ltb_lt. rewrite !Z.mod_small by lia. lia. }
          exists R. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms)|].
          assert (E : mw_sc s n = sc0 + 1) by (rewrite Msc; replace (u1 + 3 <=? 12) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
          unfold b_slow. rewrite E. split; [intros g Hg; rewrite Eh0 in Hg; discriminate|].
          split; [exact B8|]. split; [exact B9|]. split; [exact B10|]. split; [exact B11|]. split; [exact B18|]. split; [exact B20|].
          apply (keep_trans R R1 kb_keep _ K1' K). kb_in2.
        - destruct (mb2a_pb2af R1 m rom n sc0 u1 P2) as (R & Hms & B8 & B9 & B10 & B11 & _ & B18 & _ & B20 & K).
          { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2a.RES_pb2af fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Y34.
            rewrite br_ltu_z. apply Z.ltb_ge. rewrite !Z.mod_small by lia. lia. }
          exists R. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms)|].
          assert (E : mw_sc s n = sc0) by (rewrite Msc; replace (u1 + 3 <=? 12) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
          unfold b_slow. rewrite E. split; [exact Hnone|].
          split; [exact B8|]. split; [exact B9|]. split; [exact B10|]. split; [exact B11|]. split; [exact B18|]. split; [exact B20|].
          apply (keep_trans R R1 kb_keep _ K1' K). kb_in2. }
    (* [comment removed for export] *)
    destruct (Eact (sc0 + 1) ltac:(lia) ltac:(rewrite Eh0; discriminate)) as (h & ah & Eh & HMTh & Hsch & H1 & HAL).
    rewrite Eh0 in Eh. injection Eh as <-. cbn [oaddr] in MACT1.
    destruct (bd_meta h0 ah HMTh) as (MAVh & MFRh & MWh & Ravh & Rfrh).
    set (Hv := loc_addr L (LMem h0)) in *.
    unfold MT in HMTh. rewrite HMTh in Msc.
    assert (P2 : mb2b_pre R1 m n sc0 u1 Hv (am_avail ah) (am_freed ah)) by (constructor; try assumption; lia).
    assert (Y34 : bv_unsigned (ev (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) 34) = u1) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Y36 : bv_unsigned (ev (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) 36) = am_avail ah) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Y37 : bv_unsigned (ev (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) 37) = am_freed ah) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (SAV : forall t, (negb (am_avail ah =? 0)) = t ->
              branch_taken BC_NE (wa (zeval (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) (EExt true 0 4 (EVar 36))))
                                 (wa (zeval (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) (ELit 0))) = t).
    { intros t Et. cbn [zeval edenot]. rewrite Y36. rewrite br_ne_z. rewrite ext4_swrap. rewrite (Z.mod_small (am_avail ah)) by lia.
      rewrite swrap32_nz by lia. exact Et. }
    assert (SFR : forall t, (negb (am_freed ah =? 0)) = t ->
              branch_taken BC_NE (wa (zeval (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) (EExt true 0 4 (EVar 37))))
                                 (wa (zeval (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) (ELit 0))) = t).
    { intros t Et. cbn [zeval edenot]. rewrite Y37. rewrite br_ne_z. rewrite ext4_swrap. rewrite (Z.mod_small (am_freed ah)) by lia.
      rewrite swrap32_nz by lia. exact Et. }
    assert (SU : forall t, (u1 <? 13) = t ->
              branch_taken BC_LTU (wa (zeval (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) (EVar 34)))
                                  (wa (zeval (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) (ELit 13))) = t).
    { intros t Et. cbn [zeval edenot]. rewrite Y34. rewrite br_ltu_z. rewrite !Z.mod_small by lia. exact Et. }
    assert (SU3 : forall t, (u1 + 3 <? 13) = t ->
              branch_taken BC_LTU (wa (zeval (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) (EAlu ALU_ADD (EVar 34) (ELit 3))))
                                  (wa (zeval (Ez R1 (VALS_mb2b n sc0 u1 Hv (am_avail ah) (am_freed ah))) (ELit 13))) = t).
    { intros t Et. cbn [zeval edenot]. rewrite Y34. rewrite br_ltu_z. rewrite !Z.mod_small by lia. exact Et. }
    (* [comment removed for export] *)
    assert (TAILH : forall R2, msteps SEGS (mkst R1 (wa 0x53fa0) m rom) (mkst R2 (wa 0x53ff0) m rom) ->
              getr R2 8 = wa n -> getr R2 9 = wa 621712 -> getr R2 18 = wa Hv -> getr R2 19 = wa 98952 -> getr R2 20 = wa (sc0 + 1) ->
              (forall k, In k kb_keep -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
              mw_sc s n = sc0 + 1 ->
              (exists R g am, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x5405c) (mb0_mem m (loc_addr L (LMem g)) (am_avail am)) rom) /\ b_fast R g am)
              \/ (exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x54044) m rom) /\ b_slow R)).
    { intros R2 Hms2 C8 C9 C18 C19 C20 K2 E.
      destruct (Z.eq_dec (am_avail ah) 0) as [A0|A1].
      - right.
        assert (P3 : mbt_pre R2 m n (sc0 + 1) Hv (am_avail ah) (znth 0 debruijn)).
        { constructor.
          all: first [ assumption | lia | (replace (znth 0 debruijn) with 0 by reflexivity; lia)
                     | (rewrite A0; replace (db_mach (wa 0)) with 0 by (vm_compute; reflexivity); lia)
                     | (rewrite A0; replace (db_mach (wa 0) + 98952) with (98952 + 0) by (vm_compute; reflexivity); exact (Mdb 0 ltac:(lia))) ]. }
        destruct (mbt_slow R2 m rom n (sc0 + 1) Hv (am_avail ah) _ P3 A0) as (R & Hms & B8 & B9 & B10 & B11 & B18 & B19 & B20 & K).
        exists R. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms))|].
        unfold b_slow. rewrite E. split.
        + intros g Hg. rewrite Eh0 in Hg. injection Hg as <-. exists ah. split; [exact HMTh | exact A0].
        + split; [exact B8|]. split; [exact B9|]. split; [exact B10|]. split; [exact B11|]. split; [exact B18|]. split; [exact B20|].
          apply (keep_trans R R2 kb_keep _ K2 K). kb_in2.
      - left. destruct (bd_idx (am_avail ah) ltac:(lia)) as (Rdb & Mdb' & Ridx).
        assert (P3 : mbt_pre R2 m n (sc0 + 1) Hv (am_avail ah) (ctz32 (lowbit (am_avail ah)))) by (constructor; first [assumption | lia]).
        destruct (mbt_fast R2 m rom n (sc0 + 1) Hv (am_avail ah) _ P3 A1) as (R & Hms & B8 & B9 & B18 & B19 & B20 & K).
        exists R, h0, ah. split.
        + change (mb0_mem m Hv (am_avail ah)) with (mbt_mem m Hv (am_avail ah)). exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms)).
        + unfold b_fast. rewrite E. split; [exact Eh0|]. split; [exact HMTh|]. split; [exact A1|]. split; [exact B8|]. split; [exact B9|].
          split; [exact B18|]. split; [exact B19|]. split; [exact B20|]. apply (keep_trans R R2 kb_keep _ K2 K). kb_in2. }
    assert (TAILZ : forall R2, msteps SEGS (mkst R1 (wa 0x53fa0) m rom) (mkst R2 (wa 0x53ff0) m rom) ->
              getr R2 8 = wa n -> getr R2 9 = wa 621712 -> getr R2 18 = wa 0 -> getr R2 19 = wa 98952 -> getr R2 20 = wa sc0 ->
              (forall k, In k kb_keep -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
              mw_sc s n = sc0 ->
              (exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x54044) m rom) /\ b_slow R)).
    { intros R2 Hms2 C8 C9 C18 C19 C20 K2 E.
      assert (P3 : mbz_pre R2 m n sc0) by (constructor; first [assumption | lia]).
      destruct (mbz_pbz R2 m rom n sc0 P3) as (R & Hms & B8 & B9 & B10 & B11 & B18 & B19 & B20 & K).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mbz.RES_pbz fst snd]. apply Forall_nil. }
      exists R. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms))|].
      unfold b_slow. rewrite E. split; [exact Hnone|].
      split; [exact B8|]. split; [exact B9|]. split; [exact B10|]. split; [exact B11|]. split; [exact B18|]. split; [exact B20|].
      apply (keep_trans R R2 kb_keep _ K2 K). kb_in2. }
    assert (K1K : forall R2, (forall k, In k [1; 2; 3; 4; 5; 6; 7; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
               getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr R1 (Z_to_bv 5 (Z.of_nat k))) ->
               forall k, In k kb_keep -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
    { intros R2 K. apply (keep_trans R2 R1 kb_keep _ K1' K). kb_in2. }
    destruct (Z.eq_dec (am_avail ah) 0) as [A0|A1]; [destruct (Z.eq_dec (am_freed ah) 0) as [F0|F1]|].
    * (* [comment removed for export] *)
      assert (Ehf : (am_avail ah =? 0) && (am_freed ah =? 0) = true) by (rewrite A0, F0; reflexivity).
      rewrite Ehf in Msc.
      destruct (Z_lt_le_dec (u1 + 3) 13) as [Lt|Ge].
      + destruct (mb2b_pb2b5 R1 m rom n sc0 u1 Hv (am_avail ah) (am_freed ah) P2) as (R2 & Hms2 & C8 & C9 & C10 & _ & _ & _ & C18 & C19 & C20 & K2).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2b.RES_pb2b5 fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
          - apply SU3. apply Z.ltb_lt. lia.
          - apply SFR. rewrite F0. reflexivity.
          - apply SAV. rewrite A0. reflexivity. }
        apply (TAILH R2 Hms2 C8 C9 C18 C19 C20 (K1K R2 K2)). rewrite Msc. replace (u1 + 3 <=? 12) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + destruct (mb2b_pb2b6 R1 m rom n sc0 u1 Hv (am_avail ah) (am_freed ah) P2) as (R2 & Hms2 & C8 & C9 & C10 & _ & _ & _ & C18 & C19 & C20 & K2).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2b.RES_pb2b6 fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
          - apply SU3. apply Z.ltb_ge. lia.
          - apply SFR. rewrite F0. reflexivity.
          - apply SAV. rewrite A0. reflexivity. }
        right. apply (TAILZ R2 Hms2 C8 C9 C18 C19 C20 (K1K R2 K2)). rewrite Msc. replace (u1 + 3 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    * (* [comment removed for export] *)
      assert (Ehf : (am_avail ah =? 0) && (am_freed ah =? 0) = false) by (rewrite A0; cbn; apply Z.eqb_neq; exact F1).
      rewrite Ehf in Msc.
      destruct (Z_lt_le_dec u1 13) as [Lt|Ge].
      + destruct (mb2b_pb2b3 R1 m rom n sc0 u1 Hv (am_avail ah) (am_freed ah) P2) as (R2 & Hms2 & C8 & C9 & C10 & _ & _ & _ & C18 & C19 & C20 & K2).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2b.RES_pb2b3 fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
          - apply SU. apply Z.ltb_lt. lia.
          - apply SFR. apply negb_true_iff, Z.eqb_neq. exact F1.
          - apply SAV. rewrite A0. reflexivity. }
        apply (TAILH R2 Hms2 C8 C9 C18 C19 C20 (K1K R2 K2)). rewrite Msc. replace (u1 <=? 12) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + destruct (mb2b_pb2b4 R1 m rom n sc0 u1 Hv (am_avail ah) (am_freed ah) P2) as (R2 & Hms2 & C8 & C9 & C10 & _ & _ & _ & C18 & C19 & C20 & K2).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2b.RES_pb2b4 fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
          - apply SU. apply Z.ltb_ge. lia.
          - apply SFR. apply negb_true_iff, Z.eqb_neq. exact F1.
          - apply SAV. rewrite A0. reflexivity. }
        right. apply (TAILZ R2 Hms2 C8 C9 C18 C19 C20 (K1K R2 K2)). rewrite Msc. replace (u1 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    * (* [comment removed for export] *)
      assert (Ehf : (am_avail ah =? 0) && (am_freed ah =? 0) = false) by (replace (am_avail ah =? 0) with false by (symmetry; apply Z.eqb_neq; exact A1); reflexivity).
      rewrite Ehf in Msc.
      destruct (Z_lt_le_dec u1 13) as [Lt|Ge].
      + destruct (mb2b_pb2b1 R1 m rom n sc0 u1 Hv (am_avail ah) (am_freed ah) P2) as (R2 & Hms2 & C8 & C9 & C10 & _ & _ & _ & C18 & C19 & C20 & K2).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2b.RES_pb2b1 fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
          - apply SU. apply Z.ltb_lt. lia.
          - apply SAV. apply negb_true_iff, Z.eqb_neq. exact A1. }
        apply (TAILH R2 Hms2 C8 C9 C18 C19 C20 (K1K R2 K2)). rewrite Msc. replace (u1 <=? 12) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + destruct (mb2b_pb2b2 R1 m rom n sc0 u1 Hv (am_avail ah) (am_freed ah) P2) as (R2 & Hms2 & C8 & C9 & C10 & _ & _ & _ & C18 & C19 & C20 & K2).
        { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb2bz.AXF_mb2b.RES_pb2b2 fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z.
          - apply SU. apply Z.ltb_ge. lia.
          - apply SAV. apply negb_true_iff, Z.eqb_neq. exact A1. }
        right. apply (TAILZ R2 Hms2 C8 C9 C18 C19 C20 (K1K R2 K2)). rewrite Msc. replace (u1 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

End BD.
