(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_depot_find.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Inductive linked (d : depot_st) : Z -> Z -> Prop :=
| linked_refl : forall s, s <> 0 -> linked d s s
| linked_step : forall s id, s <> 0 -> linked d (dn_link (dnode d s)) id -> linked d s id.

Lemma linked_snoc : forall d s id' id, linked d s id' -> dn_link (dnode d id') = id -> id <> 0 -> linked d s id.
Proof.
  intros d s id' id L. induction L as [s0 Hs| s0 id0 Hs L IH]; intros E Hid.
  - apply linked_step; [exact Hs|]. rewrite E. apply linked_refl. exact Hid.
  - apply linked_step; [exact Hs|]. apply IH; assumption.
Qed.
Lemma dreach_linked : forall d b id, dreach d b id -> linked d (d_tab d b) id.
Proof.
  intros d b id R. induction R as [id E Hid| id id' R IH E Hid].
  - rewrite E. apply linked_refl. exact Hid.
  - eapply linked_snoc; eauto.
Qed.
Lemma linked_nz : forall d s id, linked d s id -> s <> 0.
Proof. intros d s id L. destruct L; assumption. Qed.

Section FIND.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (st : rtstate) (h b : Z).
  Let d := st_depot st.
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis Hh : 0 <= h < 2^64.
  Hypothesis Hb : b = dbucket h.

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Notation ST_ pc x10 x11 x12 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 h) s4 s5 (Z_to_bv 64 0xffff) s7 (Z_to_bv 64 A_DEPOT_MAP1) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  Lemma U_bound : 1 <= d_U d <= DEPOT_KMAX + 1.
  Proof.
    pose proof (wf_depot_ok st WF) as WD. pose proof (wd_U_le st WD). pose proof (wd_trs0 st WD). pose proof (wd_trs_max st WD). pose proof (wd_U_pos st WD).
    subst d. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma node_cells : forall id, 1 <= id <= d_U d ->
    exists blk, rw_cells asegs m (A_DEPOT_MAP1 + 8 * (id / DEPOT_L2_NODES)) [C8 (Z_to_bv 64 blk)]
      /\ AIMG_HI <= blk /\ blk + NODEBLOCK_SIZE <= alloc_ceiling   (* [comment removed for export] *)
      /\ dnode_addr d id = blk + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)
      /\ rw_cells asegs m (dnode_addr d id) [C8 (Z_to_bv 64 (dn_hash (dnode d id))); C4 (Z_to_bv 64 (dn_link (dnode d id))); C4 (Z_to_bv 64 (dn_store (dnode d id)))]
      /\ 0 <= dn_link (dnode d id) < id /\ 0 <= dn_hash (dnode d id) < 2^64.
  Proof.
    intros id Hid. pose proof (wf_depot_ok st WF) as WD. pose proof (rr_depot st m HR) as RD.
    destruct RD as (_ & _ & MAP1 & _ & NODES & _).
    set (q := id / DEPOT_L2_NODES).
    assert (Hq : 0 <= q < d_nnb d).
    { pose proof (wd_nnb st WD) as E. subst d. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    pose proof (wd_nnb_max st WD) as NM. unfold DEPOT_NNB_MAX in NM. subst d. unfold d_nnb in *.
    exists (nthz (d_nblocks (st_depot st)) q 0).
    split; [apply MAP1; lia|].
    assert (Hin : In (nthz (d_nblocks (st_depot st)) q 0) (d_nblocks (st_depot st))) by (apply nthz_In; exact Hq).
    destruct (nb_range st WF _ Hin) as (R1 & R2 & R3).
    split; [exact (ablk_img _ _ R1)|]. split; [exact R2|]. split; [reflexivity|].
    split; [apply NODES; exact Hid|].
    destruct (wd_node st WD id Hid) as (L1 & L2 & L3). split; [exact L1| exact L2].
  Qed.

  Lemma find_loop : forall (n : nat) (s : Z) x10 x12 (Q : machine_state -> Prop),
    Z.to_nat s = n -> (s = 0 \/ 1 <= s <= d_U d) ->
    (* [comment removed for export] *)
    (forall s' x11 x12, 1 <= s' <= d_U d -> linked d s s' -> dn_hash (dnode d s') = h ->
       evt asegs Q (ST_ 0x745bc (Z_to_bv 64 s') x11 x12)) ->
    (* [comment removed for export] *)
    ((forall id, linked d s id -> 1 <= id <= d_U d -> dn_hash (dnode d id) <> h) ->
       forall x10 x12, evt asegs Q (ST_ 0x74510 x10 (Z_to_bv 64 0) x12)) ->
    evt asegs Q (ST_ 0x744b8 x10 (Z_to_bv 64 s) x12).
  Proof.
    induction n as [n IH] using lt_wf_ind; intros s x10 x12 Q Hn Hs KF KN.
    pose proof U_bound as UB. unfold DEPOT_KMAX in UB.
    zstep. (if_cases K0; zify_cond K0).
    - (* [comment removed for export] *)
      subst s. apply KN. intros id L. exfalso. pose proof (linked_nz _ _ _ L). lia.
    - destruct Hs as [Hs|Hs]; [exfalso; lia|].
      destruct (node_cells s Hs) as (blk & MAPC & B1 & B2 & ADDR & NODE & LNK & HSH).
      unfold A_DEPOT_MAP1, DEPOT_L2_NODES, DEPOT_NODE_SZ, NODEBLOCK_SIZE, KHIGHMEM_BEG, AIMG_HI in *.
      zstep. zstep.
      setreg 11 (Z_to_bv 64 (s / 65536))
        ltac:(f_equal; unfold bv_wrap; change (bv_modulus 32) with 4294967296; rewrite (Z.mod_small s) by lia;
              rewrite Z.shiftr_div_pow2 by lia; change (2^16) with 65536; symmetry; apply swrap32_small; Z.div_mod_to_equations; lia).
      zstep. zstep.
      remember (5816680 + 8 * (s / 65536)) as mp eqn:Hmp.
      setreg 12 (Z_to_bv 64 mp) ltac:(f_equal; subst mp; rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. (* [comment removed for export] *)
      zstep. if_lia. (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      destruct (ex_intro (fun nd => nd = dnode_addr d s) _ eq_refl) as [nd Hnd]. rewrite <- Hnd in NODE.
      setreg 11 (Z_to_bv 64 nd)
        ltac:(f_equal; rewrite Hnd; etransitivity; [exact ADDR|]; change 65535 with (Z.ones 16); rewrite Z.land_ones by lia;
              rewrite Z.shiftl_mul_pow2 by lia; change (2^16) with 65536; change (2^4) with 16; Z.div_mod_to_equations; lia).
      zstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      setreg 11 (Z_to_bv 64 (dn_link (dnode d s))) ltac:(symmetry; apply sx32_small; lia).
      zstep. (if_cases K1; zify_cond K1).
      + (* [comment removed for export] *)
        eapply (IH (Z.to_nat (dn_link (dnode d s)))); [lia| reflexivity| lia| |].
        * intros s' x11' x12' Hs' L E. eapply KF; [exact Hs'| | exact E]. apply linked_step; [lia| exact L].
        * intros NF. apply KN. intros id L Hid. inversion L; subst; [lia|]. apply NF; [assumption| lia].
      + (* [comment removed for export] *)
        zstep. eapply KF; [exact Hs| apply linked_refl; lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma find_entry : forall (p : Z) (x10 x11 x12 x20 x24 x25 : word) (Q : machine_state -> Prop),
    p = A_DEPOT + 4 * b ->
    (forall x10 x12,
       evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A_DEPOT) x10 (Z_to_bv 64 (d_tab d b)) x12 (Z_to_bv 64 0x400008) a4 a5 a6 a7
                         (Z_to_bv 64 p) (Z_to_bv 64 h) (Z_to_bv 64 (A_DEPOT_NIDS + 8)) s5 (Z_to_bv 64 0xffff) (Z_to_bv 64 0x7fffffff)
                         (Z_to_bv 64 A_DEPOT_MAP1) (Z_to_bv 64 (d_tab d b)) s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x744b8) fc None m (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A_DEPOT) x10 x11 x12 (Z_to_bv 64 0x400000) a4 a5 a6 a7
                     (Z_to_bv 64 p) (Z_to_bv 64 h) x20 s5 (Z_to_bv 64 0xffff) (Z_to_bv 64 0x7fffffff) x24 x25 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x74498) fc None m (seg_rom asegs)).
  Proof.
    intros p x10 x11 x12 x20 x24 x25 Q Hp K.
    pose proof (wf_depot_ok st WF) as WD. pose proof (rr_depot st m HR) as RD. destruct RD as (TAB & _).
    assert (HB : 0 <= b < 2^20) by (subst b; unfold dbucket, DEPOT_TAB_LOG; apply Z.mod_pos_bound; lia).
    pose proof (TAB b ltac:(unfold DEPOT_TAB_LOG; exact HB)) as TB. rewrite <- Hp in TB. cbv delta [wz] in TB.
    pose proof (wd_tab st WD b ltac:(unfold DEPOT_TAB_LOG; exact HB)) as TV. pose proof U_bound as UB. unfold DEPOT_KMAX in UB. subst d.
    unfold A_DEPOT, A_DEPOT_MAP1, A_DEPOT_NIDS in *.
    zstep. setreg 10 (Z_to_bv 64 (d_tab (st_depot st) b)) ltac:(symmetry; apply sx32_small; lia).
    zstep. zstep. fl. zstep. zstep.
    setreg 25 (Z_to_bv 64 (d_tab (st_depot st) b)) ltac:(f_equal; change 2147483647 with (Z.ones 31); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    zstep. zstep. fl. zstep.
    apply K.
  Qed.
End FIND.


End CeilWrap.
End RTW_depot_find.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
Module RTW_depot_abs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface RTW_depot_find OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_hash OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nthz_app_l : forall {A} (l1 l2 : list A) i d, 0 <= i < zlen l1 -> nthz (l1 ++ l2) i d = nthz l1 i d.
Proof. intros A l1 l2 i d Hi. unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [lia|]. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma nthz_app_r1 : forall {A} (l1 : list A) x d, nthz (l1 ++ [x]) (zlen l1) d = x.
Proof. intros A l1 x d. unfold nthz, zlen. destruct (Z.ltb_spec0 (Z.of_nat (length l1)) 0); [lia|]. rewrite Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma nthz_over : forall {A} (l : list A) i d, zlen l <= i -> nthz l i d = d.
Proof. intros A l i d Hi. unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [reflexivity|]. apply nth_overflow. lia. Qed.
Lemma zlen_app1 : forall {A} (l : list A) x, zlen (l ++ [x]) = zlen l + 1.
Proof. intros. unfold zlen. rewrite length_app. cbn [length]. lia. Qed.

Section INS.
  Variables (d : depot_st) (h v sid b T' : Z) (nbl' sbl' : list Z).
  Definition d_ins : depot_st :=
    mkDepot (d_nodes d ++ [(h, v, sid)]) (fun i => if i =? b then d_U d + 1 else d_tab d i) nbl' T' sbl'.

  Lemma dU_ins : d_U d_ins = d_U d + 1.
  Proof. unfold d_U, d_ins. cbn [d_nodes]. rewrite length_app. cbn [length]. lia. Qed.
  Lemma dnode_ins_old : forall id, 1 <= id <= d_U d -> dnode d_ins id = dnode d id.
  Proof. intros id Hid. unfold dnode, d_ins. cbn [d_nodes]. apply nthz_app_l. unfold d_U, zlen in *. lia. Qed.
  Lemma dnode_ins_new : dnode d_ins (d_U d + 1) = (h, v, sid).
  Proof. unfold dnode, d_ins. cbn [d_nodes]. replace (d_U d + 1 - 1) with (zlen (d_nodes d)) by (unfold d_U, zlen; lia). apply nthz_app_r1. Qed.
  Lemma dtab_ins_b : d_tab d_ins b = d_U d + 1.
  Proof. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma dtab_ins_other : forall i, i <> b -> d_tab d_ins i = d_tab d i.
  Proof. intros i Hi. cbn. destruct (Z.eqb_spec i b); [lia| reflexivity]. Qed.

  Hypothesis Hv : v = d_tab d b.
  Hypothesis SOUND : forall b0 id, dreach d b0 id -> 1 <= id <= d_U d.
  Hypothesis U0 : 0 <= d_U d.

  Lemma dreach_ins_inv : forall b0 id, dreach d_ins b0 id -> (id = d_U d + 1 /\ b0 = b) \/ dreach d b0 id.
  Proof.
    intros b0 id R. induction R as [id E Hid| id id' R IH E Hid].
    - destruct (Z.eqb_spec b0 b) as [->|NE].
      + rewrite dtab_ins_b in E. left. split; [lia| reflexivity].
      + rewrite dtab_ins_other in E by exact NE. right. apply dreach_head; assumption.
    - destruct IH as [[-> ->]|IH].
      + rewrite dnode_ins_new in E. cbn in E. right. apply dreach_head; [| exact Hid]. rewrite <- Hv. exact E.
      + pose proof (SOUND _ _ IH) as B. rewrite dnode_ins_old in E by exact B. right. eapply dreach_link; eauto.
  Qed.
  Lemma dreach_ins_old : forall b0 id, dreach d b0 id -> dreach d_ins b0 id.
  Proof.
    intros b0 id R. induction R as [id E Hid| id id' R IH E Hid].
    - destruct (Z.eqb_spec b0 b) as [->|NE].
      + eapply dreach_link; [apply dreach_head; [apply dtab_ins_b| lia]| rewrite dnode_ins_new; cbn; rewrite Hv; exact E| exact Hid].
      + apply dreach_head; [rewrite dtab_ins_other by exact NE; exact E| exact Hid].
    - pose proof (SOUND _ _ R) as B. eapply dreach_link; [exact IH| rewrite dnode_ins_old by exact B; exact E| exact Hid].
  Qed.
  Lemma dreach_ins_new : dreach d_ins b (d_U d + 1).
  Proof. apply dreach_head; [apply dtab_ins_b| lia]. Qed.
End INS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pwdj_comm_inv : forall r L1 L2, pwdj (r :: L1 ++ L2) -> pwdj (L1 ++ r :: L2).
Proof.
  intros r L1 L2. revert r L2. induction L1 as [|x L1 IH]; intros r L2 H; [exact H|].
  cbn in H. destruct H as [HF [HF2 HP2]]. inversion HF; subst.
  cbn. split.
  - apply Forall_app in HF2 as [HA HB]. apply Forall_app. split; [exact HA|]. constructor; [lia| exact HB].
  - apply IH. cbn. split; [assumption| exact HP2].
Qed.
Lemma pwdj_snoc : forall L r, pwdj L -> Forall (fun r' => snd r <= fst r' \/ snd r' <= fst r) L -> pwdj (L ++ [r]).
Proof.
  intros L r HP HF. replace (L ++ [r]) with (L ++ r :: []) by reflexivity. apply pwdj_comm_inv. rewrite app_nil_r. cbn. split; [exact HF| exact HP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DEP.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Variables (d' : depot_st) (trs' : list (list Z)) (nnew snew : list Z).
Let st  := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Let st' := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 d' trs' a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Hypothesis WF : RTWF st.
Hypothesis WD' : wf_depot st'.
Hypothesis HNB' : d_nblocks d' = d_nblocks a12 ++ nnew.
Hypothesis HSB' : d_sblocks d' = d_sblocks a12 ++ snew.
Hypothesis LN : (length nnew <= 1)%nat.
Hypothesis LS : (length snew <= 1)%nat.
Hypothesis NEWR : forall b, In b nnew -> ablk b (b + NODEBLOCK_SIZE) /\ b + NODEBLOCK_SIZE <= CEIL /\ b mod 4096 = 0
                      /\ forall r, In r (rt_ranges st) -> b + NODEBLOCK_SIZE <= fst r \/ snd r <= b.
Hypothesis SEWR : forall b, In b snew -> ablk b (b + STOREBLOCK_SIZE) /\ b + STOREBLOCK_SIZE <= CEIL /\ b mod 4096 = 0
                      /\ forall r, In r (rt_ranges st) -> b + STOREBLOCK_SIZE <= fst r \/ snd r <= b.
Hypothesis NSD : forall b b', In b nnew -> In b' snew -> b + NODEBLOCK_SIZE <= b' \/ b' + STOREBLOCK_SIZE <= b.

Lemma rt_ranges_dep : rt_ranges st' = rt_nd st ++ (NBR st ++ map (fun b => (b, b + NODEBLOCK_SIZE)) nnew) ++ (SBR st ++ map (fun b => (b, b + STOREBLOCK_SIZE)) snew).
Proof.
  rewrite rt_ranges_nd. unfold rt_nd, NBR, SBR. cbn [st_pbase st_pa st_loose0 st_sec st_depot st st']. rewrite HNB', HSB', !map_app. reflexivity.
Qed.

Lemma rt_ranges_dep_In : forall r, In r (rt_ranges st') ->
  In r (rt_ranges st) \/ (exists b, In b nnew /\ r = (b, b + NODEBLOCK_SIZE)) \/ (exists b, In b snew /\ r = (b, b + STOREBLOCK_SIZE)).
Proof.
  intros r H. rewrite rt_ranges_dep in H. rewrite (rt_ranges_nd st).
  apply in_app_iff in H. destruct H as [H|H]; [left; apply in_or_app; left; exact H|].
  apply in_app_iff in H. destruct H as [H|H]; apply in_app_iff in H; destruct H as [H|H].
  - left. apply in_or_app; right; apply in_or_app; left; exact H.
  - apply in_map_iff in H as (b & <- & Hb). right; left. exists b. auto.
  - left. apply in_or_app; right; apply in_or_app; right; exact H.
  - apply in_map_iff in H as (b & <- & Hb). right; right. exists b. auto.
Qed.

Lemma pwdj_app_iff : forall L1 L2, pwdj (L1 ++ L2) <-> pwdj L1 /\ pwdj L2 /\ (forall r1 r2, In r1 L1 -> In r2 L2 -> snd r1 <= fst r2 \/ snd r2 <= fst r1).
Proof.
  induction L1 as [|r L1 IH]; intros L2.
  - cbn. split; [intros H; split; [exact I| split; [exact H| intros r1 r2 []]]| intros (_ & H & _); exact H].
  - cbn. rewrite IH, Forall_app, !Forall_forall. split.
    + intros ((F1 & F2) & P1 & P2 & C). split; [split; [exact F1| exact P1]|]. split; [exact P2|].
      intros r1 r2 [<-|H1] H2; [apply F2; exact H2| apply C; assumption].
    + intros ((F1 & P1) & P2 & C). split; [split; [exact F1| intros x Hx; apply C; [left; reflexivity| exact Hx]]|].
      split; [exact P1|]. split; [exact P2|]. intros r1 r2 H1 H2. apply C; [right; exact H1| exact H2].
Qed.

Lemma pwdj_le1 : forall (l : list Z) (f : Z -> Z * Z), (length l <= 1)%nat -> pwdj (map f l).
Proof. intros l f H. destruct l as [|x [|y l]]; cbn in *; [exact I| split; [constructor| exact I]| lia]. Qed.

Lemma pwdj_dep : pwdj (rt_ranges st').
Proof.
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_dep. rewrite (rt_ranges_nd st) in PW.
  assert (OLDIN : forall r, In r (rt_nd st) \/ In r (NBR st) \/ In r (SBR st) -> In r (rt_ranges st)).
  { intros r H. rewrite (rt_ranges_nd st), !in_app_iff. tauto. }
  apply pwdj_app_iff in PW as (P1 & P23 & C1). apply pwdj_app_iff in P23 as (P2 & P3 & C23).
  apply pwdj_app_iff. split; [exact P1|]. split.
  - apply pwdj_app_iff. split; [| split].
    + apply pwdj_app_iff. split; [exact P2|]. split; [apply pwdj_le1; exact LN|].
      intros r1 r2 H1 H2. apply in_map_iff in H2 as (b & <- & Hb). cbn [fst snd]. destruct (NEWR b Hb) as (_ & _ & _ & D).
      destruct (D r1 (OLDIN r1 ltac:(tauto))); lia.
    + apply pwdj_app_iff. split; [exact P3|]. split; [apply pwdj_le1; exact LS|].
      intros r1 r2 H1 H2. apply in_map_iff in H2 as (b & <- & Hb). cbn [fst snd]. destruct (SEWR b Hb) as (_ & _ & _ & D).
      destruct (D r1 (OLDIN r1 ltac:(tauto))); lia.
    + intros r1 r2 H1 H2. apply in_app_iff in H1. apply in_app_iff in H2. destruct H1 as [H1|H1], H2 as [H2|H2].
      * apply C23; assumption.
      * apply in_map_iff in H2 as (b & <- & Hb). cbn [fst snd]. destruct (SEWR b Hb) as (_ & _ & _ & D). destruct (D r1 (OLDIN r1 ltac:(tauto))); lia.
      * apply in_map_iff in H1 as (b & <- & Hb). cbn [fst snd]. destruct (NEWR b Hb) as (_ & _ & _ & D). destruct (D r2 (OLDIN r2 ltac:(tauto))); lia.
      * apply in_map_iff in H1 as (b & <- & Hb). apply in_map_iff in H2 as (b' & <- & Hb'). cbn [fst snd]. destruct (NSD b b' Hb Hb'); lia.
  - intros r1 r2 H1 H2. rewrite !in_app_iff in H2. destruct H2 as [[H2|H2]|[H2|H2]].
    + apply C1; [exact H1| apply in_or_app; left; exact H2].
    + apply in_map_iff in H2 as (b & <- & Hb). cbn [fst snd]. destruct (NEWR b Hb) as (_ & _ & _ & D). destruct (D r1 (OLDIN r1 ltac:(tauto))); lia.
    + apply C1; [exact H1| apply in_or_app; right; exact H2].
    + apply in_map_iff in H2 as (b & <- & Hb). cbn [fst snd]. destruct (SEWR b Hb) as (_ & _ & _ & D). destruct (D r1 (OLDIN r1 ltac:(tauto))); lia.
Qed.

Lemma RTWF_dep : RTWF st'.
Proof.
  constructor.
  - pose proof (wf_base_ok st WF) as WB. destruct WB; constructor; try assumption.
    + intros r Hr. destruct (rt_ranges_dep_In r Hr) as [H|[(b & Hb & ->)|(b & Hb & ->)]]; [apply wb_ranges; exact H| |]; cbn [fst snd].
      * destruct (NEWR b Hb) as (R1 & R2 & R3 & _). unfold NODEBLOCK_SIZE, CEIL in *. blia.
      * destruct (SEWR b Hb) as (R1 & R2 & R3 & _). unfold STOREBLOCK_SIZE, CEIL in *. blia.
    + exact pwdj_dep.
  - intros c Hc. destruct (wf_class_ok st WF c Hc); constructor; assumption.
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; assumption.
  - exact WD'.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.

Lemma rt_prov_dep : rt_prov st' = rt_prov st - prov_depot st + prov_depot st'.
Proof.
  assert (E1 : prov_classes st' = prov_classes st) by reflexivity.
  assert (E2 : prov_nb st' = prov_nb st) by reflexivity.
  assert (E3 : prov_q st' = prov_q st) by reflexivity.
  assert (E4 : prov_ptr st' = prov_ptr st) by reflexivity.
  assert (E5 : prov_live st' = prov_live st) by reflexivity.
  assert (E6 : prov_quar st' = prov_quar st) by reflexivity.
  assert (E7 : prov_slots st' = prov_slots st) by reflexivity.   (* [comment removed for export] *)
  assert (E8 : prov_l24 st' = prov_l24 st) by reflexivity.       (* [comment removed for export] *)
  assert (E10 : prov_emb st' = prov_emb st) by reflexivity.      (* [comment removed for export] *)
  unfold rt_prov. rewrite E1, E2, E3, E4, E5, E6, E7, E8. lia.
Qed.
Lemma prov_depot_dep : prov_depot st' = prov_depot st - NODEBLOCK_SIZE * zlen nnew - STOREBLOCK_SIZE * zlen snew.
Proof.
  unfold prov_depot. cbn [st_depot st st']. unfold d_nnb, d_nsb. rewrite HNB', HSB', !zlen_app. lia.
Qed.

(* [comment removed for export] *)
Lemma RTMODEL_dep : forall mo mo', RTMODEL st mo ->
  (forall e, In e (vm_maps (m_vmmaps mo')) <->
     In e (map (fun b => (wz b, wz NODEBLOCK_SIZE)) nnew ++ map (fun b => (wz b, wz STOREBLOCK_SIZE)) snew) \/ In e (vm_maps (m_vmmaps mo))) ->
  (forall x, lzf mo x = true -> lzf mo' x = true) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  (forall e, In e (st_sec st) -> sec_plain mo (fst e) (smapsize (snd e)) -> sec_plain mo' (fst e) (smapsize (snd e))) ->  (* [comment removed for export] *)
  RTMODEL st' mo'.
Proof.
  intros mo mo' (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9) MAPS LZ LIM PLN.
  assert (OLDZ : forall lo sz, zin lo sz (vm_maps (m_vmmaps mo)) -> zin lo sz (vm_maps (m_vmmaps mo'))).
  { intros lo sz H. unfold zin in *. apply MAPS. right. exact H. }
  assert (LOOSE : forall e, In e (rt_loose st') <-> In e (rt_loose st) \/ In e (map (fun b => (b, NODEBLOCK_SIZE)) nnew ++ map (fun b => (b, STOREBLOCK_SIZE)) snew)).
  { intros e. unfold rt_loose. cbn [st_loose0 st_sec st_depot st st']. rewrite HNB', HSB', !map_app, !in_app_iff. tauto. }
  unfold RTMODEL. cbn [st_pbase st_pa st st'] in *.
  split; [apply OLDZ; exact M1|]. split; [apply OLDZ; exact M2|]. split; [apply OLDZ; exact M3|]. split; [apply OLDZ; exact M4|].
  split.
  { intros e He. apply LOOSE in He. destruct He as [He|He]; [apply OLDZ; exact (M5 e He)|].
    unfold zin. apply MAPS. left. rewrite in_app_iff in He |- *. rewrite !in_map_iff in He |- *.
    destruct He as [(b & <- & Hb)|(b & <- & Hb)]; [left| right]; exists b; auto. }
  split; [apply OLDZ; exact M6|].   (* [comment removed for export] *)
  split; [intros x Hx; apply LZ; exact (M7 x Hx)|].
  split; [rewrite LIM; exact M8|].
  intros e He. apply (PLN e He). exact (M9 e He).
Qed.

(* [comment removed for export] *)
Lemma GWIN_dep : forall m m' mo mo' G G' R R',
  GWIN st m mo (mkG G R) -> LOK asegs mo -> wmono asegs m m' ->
  (forall x, in_winb G' x = true -> (exists b, In b snew /\ b <= bv_unsigned x < b + STOREBLOCK_SIZE) \/ in_winb G x = true) ->
  (forall x, lzf mo' x = true -> (exists b, In b snew /\ b <= bv_unsigned x < b + STOREBLOCK_SIZE) \/ lzf mo x = true) ->
  (forall b, In b snew -> stk asegs m' b (b + STOREBLOCK_SIZE)) ->
  GWIN st' m' mo' (mkG G' R').
Proof.
  intros m m' mo mo' G G' R R' HG HO WM WIN LZ VIS x Hw Hz Hr. cbn [g_win] in *.
  assert (NEWV : forall b, In b snew -> b <= bv_unsigned x < b + STOREBLOCK_SIZE -> m' x <> None).
  { intros b Hb Hx. destruct (VIS b Hb) as (_ & _ & V). destruct (V (bv_unsigned x) Hx) as [W _].
    unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. destruct (SEWR b Hb) as (R1 & R2 & _). pose proof (ablk_img _ _ R1) as R0.
    apply (wview_noseg_some m' x); [| exact W]. apply noseg_high. unfold KHIGHMEM_BEG, AIMG_HI in *. lia. }
  assert (Hw' : (exists b, In b snew /\ b <= bv_unsigned x < b + STOREBLOCK_SIZE) \/ gwin_in (mkG G R) x).   (* [comment removed for export] *)
  { unfold gwin_in in Hw. cbn [g_win] in Hw. destruct Hw as [Hw|Hv]; [destruct (WIN x Hw) as [X|Hw0]; [left; exact X| right; left; exact Hw0]| right; right; exact Hv]. }
  destruct Hw' as [(b & Hb & Hx)|Hw0]; [exact (NEWV b Hb Hx)|].
  destruct (LZ x Hz) as [(b & Hb & Hx)|Hz0]; [exact (NEWV b Hb Hx)|].
  assert (OLD : RTSH st (bv_unsigned x) -> m' x <> None).
  { intros Hr0. pose proof (HG x Hw0 Hz0 Hr0) as V. pose proof (lok_lazy_noseg asegs mo HO x (lzf_lazy mo x Hz0)) as NS.
    apply (wview_noseg_some m' x NS). apply WM. unfold wview. destruct (m x); [discriminate| exfalso; exact (V eq_refl)]. }
  destruct Hr as [Hr|[Hr|(b & Hb & Hx)]]; [apply OLD; left; exact Hr| apply OLD; right; left; exact Hr|].
  cbn [st_depot st'] in Hb. rewrite HSB' in Hb. apply in_app_iff in Hb as [Hb|Hb].
  - apply OLD. right; right. exists b. split; [exact Hb| exact Hx].
  - exact (NEWV b Hb Hx).
Qed.
End DEP.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section WD.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st  := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Hypothesis WF : RTWF st.
Variables (tr : list Z) (h b v sid T' : Z) (nbl' sbl' : list Z) (c : Z).
Local Abbreviation d := a12.
Local Abbreviation U := (d_U a12).
Hypothesis Hh : h = trace_hash tr.
Hypothesis Hb : b = dbucket h.
Hypothesis Hv : v = d_tab d b.
Hypothesis ROOM : trs_room tr a13.
Hypothesis TRL : 1 <= zlen tr <= TRACE_MAX_LEN.

Lemma trace_hash_range : forall t, 0 <= trace_hash t < 2^64.
Proof. intros t. unfold trace_hash, murmur64. apply mm_fin_range. apply mm_add_range. Qed.
Lemma h_range : 0 <= h < 2^64.
Proof. rewrite Hh. apply trace_hash_range. Qed.
Lemma b_range : 0 <= b < 2^DEPOT_TAB_LOG.
Proof. rewrite Hb. unfold dbucket. apply Z.mod_pos_bound. unfold DEPOT_TAB_LOG. lia. Qed.

(* [comment removed for export] *)
Definition trs_hit : list (list Z) := if in_dec (list_eq_dec Z.eq_dec) tr a13 then a13 else tr :: a13.
Lemma trs_put_hit : trs_put tr a13 trs_hit.
Proof. unfold trs_put, trs_hit. destruct (in_dec _ tr a13); [left| right]; auto. Qed.

Let st_hit := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 trs_hit a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Lemma wf_depot_hit : forall id, 1 <= id <= U -> dn_hash (dnode d id) = h -> wf_depot st_hit.
Proof.
  intros id Hid Hhash. pose proof (wf_depot_ok st WF) as WD.
  assert (LEN : zlen trs_hit <= zlen a13 + 1 /\ zlen a13 <= zlen trs_hit /\ zlen trs_hit <= DEPOT_KMAX).
  { unfold trs_hit. pose proof (wd_trs_max st WD) as M. cbn [st_trs st] in M. unfold trs_room in ROOM.
    destruct (in_dec _ tr a13) as [I|NI]; [lia|]. rewrite zlen_cons. destruct ROOM as [R|R]; [exfalso; exact (NI R)|]. unfold zlen in *. lia. }
  destruct WD; constructor; cbn [st_depot st_trs st_trs0 st st_hit] in *; try assumption; try lia.
  intros tr' Htr'. apply in_app_iff in Htr'. destruct Htr' as [Htr'|Htr'].
  - unfold trs_hit in Htr'. destruct (in_dec _ tr a13) as [I|NI].
    + apply wd_traces. apply in_or_app. left. exact Htr'.
    + destruct Htr' as [<-|Htr']; [exists id; split; [exact Hid| rewrite Hhash, Hh; reflexivity]|].
      apply wd_traces. apply in_or_app. left. exact Htr'.
  - apply wd_traces. apply in_or_app. right. exact Htr'.
Qed.

(* [comment removed for export] *)
Hypothesis NOTFOUND : forall id, linked d v id -> 1 <= id <= U -> dn_hash (dnode d id) <> h.
Hypothesis SID : 0 <= sid < 2^32.
Hypothesis Hc : c = zlen tr + 1.
Hypothesis HT' : T' = d_T d + c \/ (T' = d_T d + 2 * c /\ d_T d mod 1048576 + c > 1048576).
Hypothesis LSB' : zlen sbl' = (T' - 1) / SSTORE_BLOCK_FRAMES + 1.
Hypothesis LNB' : zlen nbl' = (U + 1) / DEPOT_L2_NODES + 1.
Hypothesis ANB' : forall x, In x nbl' -> x mod 4096 = 0.
Hypothesis ASB' : forall x, In x sbl' -> x mod 4096 = 0.

Let d' := d_ins d h v sid b T' nbl' sbl'.
Let st_ins := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 d' (tr :: a13) a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.

Lemma tr_fresh : ~ In tr (a13 ++ a14).
Proof.
  intros IN. pose proof (wf_depot_ok st WF) as WD.
  destruct (wd_traces st WD tr IN) as (id & Hid & Hhash). cbn [st_depot st] in *.
  apply (NOTFOUND id); [| exact Hid| rewrite Hhash, Hh; reflexivity].
  rewrite Hv. replace b with (dbucket (dn_hash (dnode d id))) by (rewrite Hhash, <- Hh, Hb; reflexivity).
  apply dreach_linked. apply (wd_reach_complete st WD). exact Hid.
Qed.

Lemma trs_put_ins : trs_put tr a13 (tr :: a13).
Proof. right. split; [| reflexivity]. intros I. apply tr_fresh. apply in_or_app. left. exact I. Qed.

Lemma wf_depot_ins : wf_depot st_ins.
Proof.
  pose proof (wf_depot_ok st WF) as WD. pose proof h_range as HR. pose proof b_range as BR. pose proof tr_fresh as FR.
  pose proof (wd_U_pos st WD) as UP. pose proof (wd_U_le st WD) as ULE. pose proof (wd_trs0 st WD) as T0. pose proof (wd_trs_max st WD) as TM.
  pose proof (wd_T_pos st WD) as TP. pose proof (wd_T_le st WD) as TLE. pose proof (wd_nsb st WD) as NSB. pose proof (wd_nsb_max st WD) as NSBM.
  pose proof (wd_nnb st WD) as NNB. pose proof (wd_nnb_max st WD) as NNBM.
  pose proof (wd_node st WD) as WN. pose proof (wd_tab st WD) as WT. pose proof (wd_tab_out st WD) as WTO.
  pose proof (wd_reach_sound st WD) as WRS. pose proof (wd_reach_complete st WD) as WRC. pose proof (wd_traces st WD) as WTR.
  cbn [st_depot st_trs st_trs0 st] in *.
  assert (ROOM' : zlen a13 < DEPOT_KMAX).
  { unfold trs_room in ROOM. destruct ROOM as [R|R]; [exfalso; apply FR; apply in_or_app; left; exact R| exact R]. }
  assert (SOUND : forall b0 id, dreach d b0 id -> 1 <= id <= U) by (intros b0 id R; exact (proj1 (WRS b0 id R))).
  assert (TABV : v = 0 \/ 1 <= v <= U) by (rewrite Hv; apply WT; exact BR).
  assert (DU : d_U d' = U + 1) by apply dU_ins.
  unfold TRACE_MAX_LEN, DEPOT_KMAX, DEPOT_NNB_MAX, DEPOT_NSB_MAX, DEPOT_L2_NODES, SSTORE_BLOCK_FRAMES in *.
  constructor; cbn [st_depot st_trs st_trs0 st_ins]; rewrite ?DU; unfold TRACE_MAX_LEN, DEPOT_KMAX, DEPOT_NNB_MAX, DEPOT_NSB_MAX, DEPOT_L2_NODES, SSTORE_BLOCK_FRAMES.
  - (* [comment removed for export] *) intros id Hid. destruct (Z.eq_dec id (U + 1)) as [->|NE].
    + unfold d'. rewrite dnode_ins_new. cbn. lia.
    + unfold d'. rewrite dnode_ins_old by lia. apply WN. lia.
  - (* [comment removed for export] *) intros b0 Hb0. unfold d'. destruct (Z.eq_dec b0 b) as [->|NE]; [rewrite dtab_ins_b; right; lia| rewrite dtab_ins_other by exact NE].
    destruct (WT b0 Hb0); [left; assumption| right; lia].
  - (* [comment removed for export] *) intros b0 Hb0. unfold d'. rewrite dtab_ins_other by (intros ->; exact (Hb0 BR)). apply WTO. exact Hb0.
  - (* [comment removed for export] *) intros b0 id R. unfold d' in R. apply dreach_ins_inv in R; [| first [exact Hv| exact SOUND| lia] ..].
    destruct R as [[-> ->]|R].
    + split; [lia|]. unfold d'. rewrite dnode_ins_new. cbn. rewrite Hb. reflexivity.
    + pose proof (WRS b0 id R) as [S1 S2]. split; [lia|]. unfold d'. rewrite dnode_ins_old by exact S1. exact S2.
  - (* [comment removed for export] *) intros id Hid. destruct (Z.eq_dec id (U + 1)) as [->|NE].
    + unfold d'. rewrite dnode_ins_new. cbn [dn_hash fst snd]. rewrite <- Hb. apply dreach_ins_new. lia.
    + unfold d'. rewrite dnode_ins_old by lia. apply dreach_ins_old; [exact Hv| exact SOUND| lia|]. apply WRC. lia.
  - (* [comment removed for export] *) intros tr' Htr'. cbn [app] in Htr'. destruct Htr' as [<-|Htr'].
    + exists (U + 1). split; [lia|]. unfold d'. rewrite dnode_ins_new. cbn [dn_hash fst snd]. rewrite Hh. reflexivity.
    + destruct (WTR tr' Htr') as (id & Hid & E). exists id. split; [lia|]. unfold d'. rewrite dnode_ins_old by exact Hid. exact E.
  - rewrite zlen_cons. lia.
  - exact T0.
  - rewrite zlen_cons. lia.
  - lia.
  - (* [comment removed for export] *) unfold d_nnb, d'. cbn [d_nblocks d_ins]. exact LNB'.
  - unfold d_nnb, d'. cbn [d_nblocks d_ins]. rewrite LNB'. Z.div_mod_to_equations. nia.
  - (* [comment removed for export] *) unfold d'. cbn [d_T d_ins]. lia.
  - (* [comment removed for export] *) unfold d', d_nsb. cbn [d_T d_sblocks d_ins]. rewrite zlen_cons, LSB'. unfold d_nsb in NSB, TLE. rewrite NSB in TLE.
    destruct HT' as [E|[E STR]]; rewrite E; Z.div_mod_to_equations; nia.
  - unfold d_nsb, d'. cbn [d_T d_sblocks d_ins]. exact LSB'.
  - unfold d_nsb, d'. cbn [d_T d_sblocks d_ins]. rewrite LSB'. unfold d_nsb in NSB, NSBM, TLE. rewrite NSB in TLE, NSBM.
    destruct HT' as [E|[E STR]]; rewrite E; Z.div_mod_to_equations; nia.
  - intros x Hx. apply ANB'. exact Hx.
  - intros x Hx. apply ASB'. exact Hx.
Qed.
End WD.


End CeilWrap.
End RTW_depot_abs.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_nstore.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_depot_put.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.InitMem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_nstore.RTW_depot_create OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_nstore.RTW_depot_alloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_hash OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_nstore.RTW_depot_store OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_nstore OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma amoadd_w_val : forall (U c : Z), 0 <= U -> 0 <= c -> U + c < 2^32 ->
  bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 U)))) (Z_to_bv 32 c)) = U + c.
Proof.
  intros U c HU Hc HUc. cbn [amo_val].
  rewrite bv_add_unsigned, bv_extract_unsigned, le_bytes_to_word_le4, !unsigned_lit by lia.
  rewrite Z_to_bv_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fresh_vs_mapped_n : forall mo (ua bm km : word) n X kk,
  mmap_grant mo ua n -> 0 < n -> bv_unsigned ua + n < 2^64 -> In (bm, km) (vm_maps (m_vmmaps mo)) ->
  bv_unsigned bm <= X -> X + kk <= bv_unsigned bm + bv_unsigned km -> 0 < kk ->
  X + kk <= bv_unsigned ua \/ bv_unsigned ua + n <= X.
Proof.
  intros mo ua bm km n X kk (_ & _ & GC & GF) Hn Hn2 HIN HB1 HB2 Hk.
  rewrite region_free_app in GF. apply andb_true_iff in GF as [_ GF].
  pose proof (bv_unsigned_in_range 64 ua) as RA. change (bv_modulus 64) with (2^64) in RA.
  pose proof (bv_unsigned_in_range 64 bm) as RB. change (bv_modulus 64) with (2^64) in RB.
  destruct (Z_lt_le_dec X (bv_unsigned ua + n)); [| right; lia].
  destruct (Z_lt_le_dec (bv_unsigned ua) (X + kk)); [| left; lia]. exfalso.
  set (x := Z.max X (bv_unsigned ua)).
  eapply (region_free_false_of _ ua (Z_to_bv 64 n) bm km (Z_to_bv 64 x) GF HIN); rewrite ?unsigned_lit by lia; lia.
Qed.

Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[l h] W1 IH]; intros; cbn; [tauto|]. rewrite IH. tauto. Qed.

Section PUTINS.
  (* [comment removed for export] *)
  Variables (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 vra : word) (fj : list byte).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z).
  Variables (T n P p v h U k lo : Z) (sbl nbl : list Z) (tr : list Z) (nj : list byte).
  Hypothesis HC : mmap_consts mv.
  Hypothesis CF240 : ro_cells asegs mv 0x13be98 [C4 (Z_to_bv 64 0)].
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 496 <= bv_unsigned sp /\ bv_unsigned sp + 112 < 2^64.
  Hypothesis FRP : rw_cells asegs mv (bv_unsigned sp)
    [CB 8 fj; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 n); C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra].
  (* [comment removed for export] *)
  Hypothesis SSR : ssrep mv T sbl.
  Hypothesis SSW : sswf T sbl.
  Hypothesis HT : T + 64 < 2^31.
  Hypothesis HSB : zlen sbl < 4095.
  (* [comment removed for export] *)
  Hypothesis Hn : n = zlen tr /\ 1 <= n <= 30.
  Hypothesis HP : alloc_ceiling <= P /\ P + 8 * n <= 2^64 /\ (P + 8 * n <= lo \/ bv_unsigned sp + 112 <= P).
  Hypothesis TRC : cells_at asegs mv P (trace_cells tr).
  Hypothesis Hh : 0 <= h < 2^64.
  (* [comment removed for export] *)
  Hypothesis Hp : 0x18c158 <= p /\ p + 4 <= 0x58c158 /\ p mod 4 = 0.
  Hypothesis Hv : 0 <= v < 2^31.
  Hypothesis TB : rw_cells asegs mv p [C4 (Z_to_bv 64 v)].
  Hypothesis HU : 1 <= U /\ U + 1 < 2^21.
  Hypothesis NIDS : rw_cells asegs mv 0x58c158 [C4 (Z_to_bv 64 U); CB 4 nj; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis Hk : k = (U + 1) / 65536.
  Hypothesis MAP1 : rw_cells asegs mv (0x58c168 + 8 * k) [C8 (Z_to_bv 64 (nthz nbl k 0))].
  Hypothesis HNB : zlen nbl = U / 65536 + 1 /\ (forall b, In b nbl -> 0x5ff000 <= b /\ b + 1048576 <= alloc_ceiling /\ b mod 4096 = 0).
  Hypothesis NVIS : forall b, In b nbl -> stk asegs mv b (b + 1048576).
  (* [comment removed for export] *)
  Hypothesis NBSB : forall b b', In b nbl -> In b' sbl -> b + 1048576 <= b' \/ b' + 8388608 <= b.
  Hypothesis NBM : forall b, In b nbl -> exists (bm km : word), In (bm, km) (vm_maps (m_vmmaps mo)) /\ bv_unsigned bm <= b /\ b + 1048576 <= bv_unsigned bm + bv_unsigned km.
  Hypothesis SBM : forall b, In b sbl -> exists (bm km : word), In (bm, km) (vm_maps (m_vmmaps mo)) /\ bv_unsigned bm <= b /\ b + 8388608 <= bv_unsigned bm + bv_unsigned km.
  (* [comment removed for export] *)
  Hypothesis HFS1 : forall a : word, mmap_grant mo a 1048576 -> 0x5ff000 <= bv_unsigned a.
  Hypothesis HFS8 : forall mo1 (a : word),
    (mo1 = mo \/ exists a1 : word, mmap_grant mo a1 1048576 /\ mo1 = mm_add_map a1 (Z_to_bv 64 1048576) mo) ->
    mmap_grant mo1 a 8388608 -> 0x5ff000 <= bv_unsigned a.

  Definition new_id : Z := U + 1.
  Definition node_of (nbl' : list Z) : Z := nthz nbl' k 0 + 16 * (new_id mod 65536).

  Lemma put_insert_spec : forall (Pp : machine_state -> Model -> lghost -> Prop),
    1048576 + 8388608 <= R -> mmap_placeable mo 1048576 ->
    (forall mo1, (mo1 = mo \/ exists a1 : word, mmap_grant mo a1 1048576 /\ mo1 = mm_add_map a1 (Z_to_bv 64 1048576) mo) ->
       mmap_placeable mo1 8388608) ->
    (forall (nbl' : list Z) (nb1 : list (Z * Z)) (mo1 : Model) (R1 : Z)
            (start : Z) (sbl' : list Z) (nb2 : list (Z * Z)) (m' : word -> option byte) (mo' : Model) (G' : list (Z * Z)) (R' : Z) (lj : list byte)
            (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
       (* [comment removed for export] *)
       ((nbl' = nbl /\ nb1 = [] /\ mo1 = mo /\ R1 = R /\ k < zlen nbl)
        \/ (exists a : word, nbl' = nbl ++ [bv_unsigned a] /\ nb1 = [(bv_unsigned a, bv_unsigned a + 1048576)] /\ k = zlen nbl
                             /\ mmap_grant mo a 1048576
                             /\ mo1 = mm_add_map a (Z_to_bv 64 1048576) mo /\ R1 = R - 1048576
                             /\ 0x5ff000 <= bv_unsigned a /\ bv_unsigned a + 1048576 <= alloc_ceiling /\ bv_unsigned a mod 4096 = 0)) ->
       (* [comment removed for export] *)
       (start = T \/ (start = T + (n + 1) /\ T mod 1048576 + (n + 1) > 1048576)) -> start mod 1048576 + (n + 1) <= 1048576 ->
       ssrep m' (start + (n + 1)) sbl' -> sswf (start + (n + 1)) sbl' -> start / 1048576 < zlen sbl' ->
       ((sbl' = sbl /\ nb2 = [] /\ mo' = mo1 /\ G' = G /\ R' = R1)
        \/ (exists a : word, sbl' = sbl ++ [bv_unsigned a] /\ nb2 = [(bv_unsigned a, bv_unsigned a + 8388608)]
                             /\ mmap_grant mo1 a 8388608
                             /\ mo' = mm_add_lazy a (Z_to_bv 64 8388608) mo1 /\ G' = (bv_unsigned a, bv_unsigned a + 8388608) :: G /\ R' = R1 - 8388608)) ->
       (* [comment removed for export] *)
       (forall b, In b nbl' -> stk asegs m' b (b + 1048576)) ->
       rw_cells asegs m' (node_of nbl') [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 (start + 1))] ->
       rw_cells asegs m' p [C4 (Z_to_bv 64 new_id)] ->
       (exists nj', rw_cells asegs m' 0x58c158 [C4 (Z_to_bv 64 new_id); CB 4 nj'; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) ->
       rw_cells asegs m' (0x58c168 + 8 * k) [C8 (Z_to_bv 64 (nthz nbl' k 0))] ->
       mem_inv asegs m' ->
       munch ((lo, bv_unsigned sp + 112) :: (p, p + 4) :: (0x58c158, 0x58c164) :: (0x58c168 + 8 * k, 0x58c168 + 8 * k + 8)
              :: (node_of nbl', node_of nbl' + 16)
              :: (nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576), nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576) + 8 * (n + 1))
              :: ssfp T nb2 ++ nb1) mv m' ->
       wmono asegs mv m' -> stk asegs m' lo (bv_unsigned sp + 112) ->
       LSCPS asegs Pp (MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp x5 x6 x7 v0 v1 (Z_to_bv 64 new_id) x11 x12 x13 x14 x15 x16 x17
                              v2 v3 v4 v5 v6 v7 v8 v9 s10 s11 x28 x29 x30 x31)
                         F (ret_pc vra) fc None m' (seg_rom asegs)) mo' (mkG G' R')) ->
    forall (x10 x12 : word),
    LSCPS asegs Pp (MS (mkR vra sp gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 0x18c158) x10 (Z_to_bv 64 0) x12 a3 a4 a5 a6 a7
                         (Z_to_bv 64 p) (Z_to_bv 64 h) (Z_to_bv 64 0x58c160) s5 (Z_to_bv 64 0xffff) (Z_to_bv 64 0x7fffffff)
                         (Z_to_bv 64 0x58c168) (Z_to_bv 64 v) s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x74510) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros Pp HRR HPL1 HPL8 K x10 x12.
    pose proof HC as HC0.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0. pose proof TB as TBW. pose proof NIDS as NIDW. pose proof MAP1 as MAPW. pose proof FRP as FR.
    clear TB NIDS MAP1 FRP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    assert (HK : 0 <= k <= zlen nbl /\ k < 33) by (rewrite Hk; destruct HNB as [E _]; rewrite E; Z.div_mod_to_equations; nia).
    destruct (ex_intro (fun q => q = 0x58c168 + 8 * k) _ eq_refl) as [qm Hqm]. rewrite <- Hqm in MAPW.
    pose proof (munch_refl [(lo, bv_unsigned sp + 112); (p, p + 4); (0x58c158, 0x58c164); (qm, qm + 8)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    change (cells_at asegs mv P (trace_cells tr)) with (ro_cells asegs mv P (trace_cells tr)) in TRC. hide TRC. hide CF240.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    eapply lock_spec; [exact MI| idtac; lia| exact Hv| exact TBW| exact ST| idtac; lia|].
    intros x5 x6 x7 x11' x12' x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 TB1 MI1 MU1 WM1 ST1.
    replace (ret_pc (Z_to_bv 64 476440)) with (Z_to_bv 64 476440 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rw_cells_transport in FR; [| exact MU1| exact WM1| cbn; lia].
    eapply rw_cells_transport in NIDW; [| exact MU1| exact WM1| cbn; lia].
    eapply rw_cells_transport in MAPW; [| exact MU1| exact WM1| cbn; lia].
    apply (munch_weaken _ [(lo, bv_unsigned sp + 112); (p, p + 4); (0x58c158, 0x58c164); (qm, qm + 8)]) in MU1. 2:{ unfold sub_fp; cbn; intros; lia. }
    pose proof (munch_trans _ _ _ _ MU MU1) as MU2. clear MU MU1. rename MU2 into MU.
    pose proof (wmono_trans asegs _ _ _ WM WM1) as WM2. clear WM WM1 MI ST. rename WM2 into WM. rename MI1 into MI. rename ST1 into ST.
    lstep. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 (bv_unsigned ?jv))) _) =>
        rewrite (le4_of_u32 jv); replace (Z_to_bv 64 (bv_unsigned jv) : word) with (Z_to_bv 64 (U + 1) : word) by (f_equal; symmetry; apply amoadd_w_val; lia);
        mem_after_store
    end.
    fl. rewrite (sx32_small U) by lia.
    lstep. (* [comment removed for export] *)
    rewrite (swrap32_small (U + 1)) by lia.
    lstep. lstep. (* [comment removed for export] *)
    rewrite (Z.mod_small (U + 1) 4294967296) by lia.
    lstep. if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 k) ltac:(f_equal; rewrite Hk, Z.shiftr_div_pow2 by lia; reflexivity).
    setreg 10 (Z_to_bv 64 qm) ltac:(f_equal; rewrite Hqm, Hk, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2^16) with 65536; change (2^3) with 8; lia).
    lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (JOIN : forall (nbl' : list Z) (nb1 : list (Z * Z)) (mo1 : Model) (R1 : Z) (m2 : word -> option byte) (ndj : list byte)
                          (ya y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      ya = Z_to_bv 64 (nthz nbl' k 0) ->
      ((nbl' = nbl /\ nb1 = [] /\ mo1 = mo /\ R1 = R /\ k < zlen nbl)
        \/ (exists a : word, nbl' = nbl ++ [bv_unsigned a] /\ nb1 = [(bv_unsigned a, bv_unsigned a + 1048576)] /\ k = zlen nbl
                             /\ mmap_grant mo a 1048576
                             /\ mo1 = mm_add_map a (Z_to_bv 64 1048576) mo /\ R1 = R - 1048576
                             /\ 0x5ff000 <= bv_unsigned a /\ bv_unsigned a + 1048576 <= alloc_ceiling /\ bv_unsigned a mod 4096 = 0)) ->
      (forall b, In b nbl' -> stk asegs m2 b (b + 1048576)) ->
      (forall b, In b nbl' -> 0x5ff000 <= b /\ b + 1048576 <= alloc_ceiling /\ b mod 4096 = 0) ->
      k < zlen nbl' ->
      rw_cells asegs m2 (node_of nbl') [CB 16 ndj] ->
      rw_cells asegs m2 (bv_unsigned sp) [CB 8 fj; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 n); C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
      rw_cells asegs m2 0x58c158 [C4 (Z_to_bv 64 (U + 1)); CB 4 nj; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m2 qm [C8 (Z_to_bv 64 (nthz nbl' k 0))] ->
      rw_cells asegs m2 p [C4 (Z_to_bv 64 (Z.lor v 18446744071562067968))] ->
      ro_cells asegs m2 P (trace_cells tr) -> ro_cells asegs m2 0x13be98 [C4 (Z_to_bv 64 0)] -> mmap_consts m2 ->
      ssrep m2 T sbl -> mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp) ->
      munch ((lo, bv_unsigned sp + 112) :: (p, p + 4) :: (0x58c158, 0x58c164) :: (qm, qm + 8) :: nb1) mv m2 -> wmono asegs mv m2 ->
      LSCPS asegs Pp (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 0) (Z_to_bv 64 (U + 1)) ya y11 y12 y13 y14 y15 y16 y17
                           (Z_to_bv 64 p) (Z_to_bv 64 h) (Z_to_bv 64 0x58c160) (Z_to_bv 64 v) (Z_to_bv 64 0xffff) (Z_to_bv 64 (U + 1))
                           (Z_to_bv 64 0x58c168) (Z_to_bv 64 v) s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x74580) fc None m2 (seg_rom asegs)) mo1 (mkG G R1)).
    { intros nbl' nb1 mo1 R1 m2 ndj ya y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 -> HNB1 NVIS' HNB' HK' NDC FR2 NIDW2 MAPW2 TB2 TRC2 CF2 HC2 SSR2 MI2 ST2 MUj WMj.
      clear MI ST FR NIDW MAPW TBW MU WM. (nelimp SSW 3%nat; intros T1 LENS BR).
      assert (INB : In (nthz nbl' k 0) nbl') by (apply nthz_In; lia).
      (nelim (HNB' _ INB) 3%nat; intros Rn1 Rn2 Rn3).
      destruct (ex_intro (fun ndv => ndv = node_of nbl') _ eq_refl) as [ndv Hndv].
      assert (HND : nthz nbl' k 0 <= ndv /\ ndv + 16 <= nthz nbl' k 0 + 1048576) by (rewrite Hndv; unfold node_of, new_id; Z.div_mod_to_equations; nia).
      rewrite <- Hndv in NDC.
      (* [comment removed for export] *)
      assert (HMO1 : mo1 = mo \/ exists a1 : word, mmap_grant mo a1 1048576 /\ mo1 = mm_add_map a1 (Z_to_bv 64 1048576) mo).
      { destruct HNB1 as [(_ & _ & -> & _)|(a1 & _ & _ & _ & G1 & -> & _)]; [left; reflexivity| right; exists a1; split; [exact G1| reflexivity]]. }
      assert (HR1 : 8388608 <= R1) by (destruct HNB1 as [(_ & _ & _ & -> & _)|(a1 & _ & _ & _ & _ & _ & -> & _)]; lia).
      assert (MAPS1 : forall e, In e (vm_maps (m_vmmaps mo)) -> In e (vm_maps (m_vmmaps mo1))).
      { intros e He. destruct HMO1 as [->|(a1 & _ & ->)]; [exact He|]. rewrite mm_add_map_vmmaps. cbn [vm_maps]. right. exact He. }
      apply lscps_step_evt.
      lstep. lstep. lstep. (* [comment removed for export] *)
      setreg 9 (Z_to_bv 64 ndv) ltac:(f_equal; rewrite Hndv; unfold node_of, new_id; change 65535 with (Z.ones 16); rewrite Z.land_ones, Z.shiftl_mul_pow2 by lia; change (2^16) with 65536; change (2^4) with 16; lia).
      lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      (* [comment removed for export] *)
      apply (rw_cells_app _ _ [_] [_; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. destruct FR2 as [FRJ FR2].
      apply (rw_cells_app _ _ [_; _] [_; _; _; _; _; _; _; _; _; _; _]) in FR2. destruct FR2 as [ARGSC FR2].
      fixaddrH ARGSC (bv_unsigned sp + 8). fixaddrH FR2 (bv_unsigned sp + 24).
      apply (rw_cells_app _ _ [_] [_]) in ARGSC. destruct ARGSC as [ARG1 ARG2]. fixaddrH ARG2 (bv_unsigned sp + 16).
      apply (C8_as_C4s _ _ n) in ARG2; [| lia].
      assert (ARGSC : rw_cells asegs m2 (bv_unsigned sp + 8) [C8 (Z_to_bv 64 P); C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)]).
      { apply (rw_cells_app _ _ [_] [_; _]). split; [exact ARG1|]. fixaddr (bv_unsigned sp + 16). exact ARG2. }
      clear ARG1 ARG2.
      apply evt_done. eapply nstore_spec with (lo := lo) (tr := tr) (sbl := sbl) (T := T).
      { exact HC2. } { exact CF2. } { exact MI2. } { exact ST2. } { idtac. lia. } { exact SSR2. } { exact SSW. } { exact Hn. } { exact HT. } { exact HSB. }
      { lia. }
      { exact ARGSC. }
      { idtac. lia. }
      { exact TRC2. }
      { lia. }
      { exact NDC. }
      { intros a GRa. apply (HFS8 mo1 a); [exact HMO1| exact GRa]. }
      { (* [comment removed for export] *)
        intros b' Hb'. destruct HNB1 as [(-> & _)|(a1 & -> & _ & KE & G1 & _)].
        - destruct (NBSB _ b' INB Hb'); lia.
        - apply in_app_iff in INB. destruct INB as [INB|[E|[]]].
          + destruct (NBSB _ b' INB Hb'); lia.
          + (nelim (SBM b' Hb') 5%nat; intros bm km HIN B1 B2).
            pose proof (fresh_vs_mapped_n mo a1 bm km 1048576 b' 8388608 G1 ltac:(lia) ltac:((nelim G1 4%nat; intros _ _ GC _); idtac; pose proof (bv_unsigned_in_range 64 a1); lia) HIN B1 B2 ltac:(lia)).
            rewrite <- E in *. lia. }
      { (* [comment removed for export] *)
        destruct HNB1 as [(-> & _ & -> & _)|(a1 & -> & _ & KE & G1 & -> & _)].
        - (nelim (NBM _ INB) 5%nat; intros bm km HIN B1 B2). exists bm, km. split; [exact HIN| lia].
        - apply in_app_iff in INB. destruct INB as [INB|[E|[]]].
          + (nelim (NBM _ INB) 5%nat; intros bm km HIN B1 B2). exists bm, km. split; [rewrite mm_add_map_vmmaps; cbn [vm_maps]; right; exact HIN| lia].
          + exists a1, (Z_to_bv 64 1048576). split; [rewrite mm_add_map_vmmaps; cbn [vm_maps]; left; reflexivity|].
            rewrite unsigned_lit by lia. rewrite <- E in *. lia. }
      { exact HR1. }
      { apply HPL8. exact HMO1. }
      intros start sbl' nb2 m3 mo' G' R' lj z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HS1 HS2 SSR' SSW' HBF HALT ARGSC' NODE MI3 MU3 WM3 ST3.
      assert (NB2F : forall iv, In iv nb2 -> 0x5ff000 <= fst iv /\ snd iv <= alloc_ceiling).
      { intros iv Hiv. destruct HALT as [(_ & -> & _)|(ua & _ & -> & GRa & _)]; [destruct Hiv|].
        destruct Hiv as [<-|[]]. cbn [fst snd].
        assert (0x5ff000 <= bv_unsigned ua) by (apply (HFS8 mo1 ua); [exact HMO1| exact GRa]).
        (nelim GRa 4%nat; intros _ _ GC _). idtac. lia. }
      assert (DJ3 : forall a sz, 0x18c158 <= a -> 0 <= sz -> (a + sz <= 0x5ff000 \/ bv_unsigned sp <= a) ->   (* [comment removed for export] *)
                     disjoint_from ((lo, bv_unsigned sp) :: (ndv, ndv + 16)
                        :: (nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576), nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576) + 8 * (n + 1))
                        :: ssfp T nb2) a sz).
      { intros a sz A1 A2 A3. (nelimp SSW' 3%nat; intros _ _ BR'). assert (INS : In (nthz sbl' (start / 1048576) 0) sbl') by (apply nthz_In; split; [Z.div_mod_to_equations; lia| exact HBF]).
        (nelim (BR' _ INS) 3%nat; intros Q1 Q2 Q3).
        cbn [disjoint_from ssfp].
        split; [lia|]. split; [lia|]. split. { clear - Q1 Q2 HS2 A1 A2 A3 Hn LO RSP. Z.div_mod_to_equations. lia. } split; [lia|]. split; [lia|].
        clear - NB2F A1 A2 A3 LO RSP. induction nb2 as [|[l' h'] nb2 IH]; [exact I|]. cbn. split.
        - destruct (NB2F (l', h') ltac:(left; reflexivity)) as (X1 & X2). cbn [fst snd] in X1, X2. lia.
        - apply IH. intros iv Hiv. apply NB2F. right. exact Hiv. }
      eapply rw_cells_transport in FRJ; [| exact MU3| exact WM3| apply DJ3; cbn; lia].
      eapply rw_cells_transport in FR2; [| exact MU3| exact WM3| apply DJ3; cbn; lia].
      eapply rw_cells_transport in TB2; [| exact MU3| exact WM3| apply DJ3; cbn; lia].
      eapply rw_cells_transport in NIDW2; [| exact MU3| exact WM3| apply DJ3; cbn; lia].
      eapply rw_cells_transport in MAPW2; [| exact MU3| exact WM3| apply DJ3; cbn; lia].
      pose proof (wmono_trans asegs _ _ _ WMj WM3) as WM03.
      hide MUj. hide MU3. clear MI2 ST2 WMj.
      pose proof (munch_refl [(p, p + 4); (ndv, ndv + 16)] m3) as MU4. pose proof (wmono_refl asegs m3) as WM4.
      apply lscps_step_evt.
      replace (ret_pc (Z_to_bv 64 476576)) with (Z_to_bv 64 476576 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      lstep. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. if_lia. (* [comment removed for export] *)
      do 11 lstep. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with H1 : rw_cells _ mm (bv_unsigned sp) [CB 8 ?j1], H2 : rw_cells _ mm (bv_unsigned sp + 8) ?cs2, H3 : rw_cells _ mm (bv_unsigned sp + 24) ?cs3 |- _ =>
          assert (FRM : rw_cells asegs mm (bv_unsigned sp) ([CB 8 j1] ++ cs2 ++ cs3));
          [ apply rw_cells_app; split; [exact H1|]; fixaddr (bv_unsigned sp + 8); apply rw_cells_app; split; [exact H2|]; fixaddr (bv_unsigned sp + 24); exact H3
          | cbn [app] in FRM; clear H1 H2 H3 ] end end.
      release_frame FRM ST3 (bv_unsigned sp + 112).
      apply evt_done.
      lazymatch goal with |- LSCPS _ _ (MS _ _ _ _ _ ?mm _) _ _ =>
      eapply (K nbl' nb1 mo1 R1 start sbl' nb2 mm mo' G' R' lj);
        [ exact HNB1 | exact HS1 | exact HS2
        | eapply (ssrep_munch _ m3 mm); [exact SSR'| exact SSW'| exact MU4| exact WM4| intros a' sz' A1 A2; cbn; lia]
        | exact SSW' | exact HBF | exact HALT
        | intros b Hb; (nelim (HNB' b Hb) 3%nat; intros Q1 Q2 Q3); eapply stk_wmono_noseg; [exact (NVIS' b Hb)| first [exact WM3 | eapply wmono_trans; [exact WM3| exact WM4]]| unfold AIMG_HI; lia]
        | rewrite <- Hndv; lazymatch goal with H : rw_cells _ mm ndv _ |- _ => exact H end
        | unfold new_id; lazymatch goal with H : rw_cells _ mm p _ |- _ => exact H end
        | exists nj; exact NIDW2
        | rewrite <- Hqm; exact MAPW2
        | assumption
        | | first [exact WM03 | exact (wmono_trans asegs _ _ _ WM03 WM4)] | assumption ]
      end.
      (* [comment removed for export] *)
      unhide MUj. unhide MU3. rewrite <- Hqm, <- Hndv.
      set (TG := (lo, bv_unsigned sp + 112) :: (p, p + 4) :: (5816664, 5816676) :: (qm, qm + 8) :: (ndv, ndv + 16)
                 :: (nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576), nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576) + 8 * (n + 1))
                 :: ssfp T nb2 ++ nb1).
      assert (X1 : munch TG mv m2).
      { clear - MUj. eapply munch_weaken; [| exact MUj]. unfold sub_fp, TG; intros x Hx. cbn [outside ssfp app] in Hx |- *.
        (nelim Hx 9%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Hx). apply (proj1 (outside_app nb2 nb1 x)) in Hx. destruct Hx as [Y9 Y10].
        repeat (split; [assumption|]). exact Y10. }
      assert (X2 : munch TG m2 m3).
      { clear - MU3 LO RSP. eapply munch_weaken; [| exact MU3]. unfold sub_fp, TG; intros x Hx. cbn [outside ssfp app] in Hx |- *.
        (nelim Hx 9%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Hx). apply (proj1 (outside_app nb2 nb1 x)) in Hx. destruct Hx as [Y9 Y10].
        split; [lia|]. split; [exact Y5|]. split; [exact Y6|]. split; [exact Y7|]. split; [exact Y8|]. exact Y9. }
      lazymatch goal with |- munch _ _ ?mf =>
      assert (X3 : munch TG m3 mf)
        by (clear - MU4; eapply munch_weaken; [| exact MU4]; unfold sub_fp, TG; intros x Hx; cbn [outside ssfp app] in Hx |- *;
            (nelim Hx 6%nat; intros Y1 Y2 Y3 Y4 Y5 Hx); split; [exact Y2| split; [exact Y5| exact I]])
      end.
      subst TG. exact (munch_trans _ _ _ _ X1 (munch_trans _ _ _ _ X2 X3)). }
    destruct (Z_lt_le_dec k (zlen nbl)) as [KLT|KGE].
    - (* [comment removed for export] *)
      assert (INB : In (nthz nbl k 0) nbl) by (apply nthz_In; lia).
      (nelim (proj2 HNB _ INB) 3%nat; intros Rn1 Rn2 Rn3).
      lstep. if_lia. (* [comment removed for export] *)
      apply evt_done.
      (* [comment removed for export] *)
      unhide TRC. unhide CF240.
      pose proof (NVIS _ INB) as VB. eapply stk_wmono_noseg in VB; [| exact WM| unfold AIMG_HI; lia].
      assert (HND : nthz nbl k 0 <= node_of nbl /\ node_of nbl + 16 <= nthz nbl k 0 + 1048576).
      { unfold node_of, new_id. Z.div_mod_to_equations. nia. }
      destruct (stk_split asegs _ (nthz nbl k 0) (node_of nbl + 16) (nthz nbl k 0 + 1048576) VB ltac:(lia)) as [S1 _].
      destruct (stk_carve asegs _ (nthz nbl k 0) (node_of nbl + 16) 16 S1 ltac:(cbn; lia)) as [_ (ndj & NDC)].
      replace (node_of nbl + 16 - Z.of_nat 16) with (node_of nbl) in NDC by (cbn; lia).
      eapply (JOIN nbl [] mo R); [reflexivity| left; repeat (split; [reflexivity|]); exact KLT| | exact (proj2 HNB)| exact KLT| exact NDC| exact FR| exact NIDW| exact MAPW| exact TB1
        | eapply ro_cells_transport; [exact TRC| exact MU| rewrite trace_cells_size; cbn; lia]
        | eapply ro_cells_transport; [exact CF240| exact MU| cbn; lia]
        | eapply (mmap_consts_munch _ mv _ HC0 MU); cbn; lia
        | eapply (ssrep_munch _ mv); [exact SSR| exact SSW| exact MU| exact WM| intros a' sz' A1 A2; cbn; lia]
        | exact MI| exact ST| exact MU| exact WM].
      intros b Hb. (nelim (proj2 HNB b Hb) 3%nat; intros Q1 Q2 Q3). eapply stk_wmono_noseg; [exact (NVIS b Hb)| exact WM| unfold AIMG_HI; lia].
    - (* [comment removed for export] *)
      assert (KEQ : k = zlen nbl) by lia.
      rewrite (nthz_over nbl k 0) in MAPW |- * by lia.
      lstep. if_lia. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      unhide TRC. unhide CF240.
      apply evt_done. eapply tlm_create_spec with (lo := lo).
      { eapply (mmap_consts_munch _ mv _ HC0 MU); cbn; lia. }
      { exact MI. }
      { exact ST. }
      { idtac. lia. }
      { lia. }
      { replace 5816672 with (5816664 + Z.of_nat (cells_size [C4 (Z_to_bv 64 (U + 1)); CB 4 nj])) by (cbn; lia).
        eapply (rw_cells_drop _ _ [_; _] [_; _; _; _]). exact NIDW. }
      { rewrite <- Hqm. exact MAPW. }
      { lia. } { exact HPL1. }
      intros a y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 GR MI2 MU2 WM2 ST2 ZNEW MUB MAP2 GI GC GA.
      rewrite <- Hqm in MU2, MAP2. idtac. unfold AIMG_HI in GI.
      pose proof (HFS1 a GR) as GK.
      pose proof (bv_unsigned_in_range 64 a) as RA. change (bv_modulus 64) with (2^64) in RA.
      apply lscps_step_evt.
      replace (ret_pc (Z_to_bv 64 476696)) with (Z_to_bv 64 476696 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      lstep. (* [comment removed for export] *)
      apply evt_done.
      (* [comment removed for export] *)
      pose proof (stk_of_rw_cells asegs m2 _ _ ZNEW) as VB.
      match type of VB with stk _ _ _ ?hi => replace hi with (bv_unsigned a + 1048576) in VB by (cbn -[Z.add Z.of_nat Z.to_nat]; rewrite ?Z2Nat.id by lia; cbn; lia) end.
      assert (EN : nthz (nbl ++ [bv_unsigned a]) k 0 = bv_unsigned a) by (rewrite KEQ; apply nthz_app_r1).
      assert (END : node_of (nbl ++ [bv_unsigned a]) = bv_unsigned a).
      { unfold node_of, new_id. rewrite EN. replace ((U + 1) mod 65536) with 0; [lia|]. destruct HNB as [E _]. rewrite Hk in KEQ. rewrite E in KEQ. Z.div_mod_to_equations. nia. }
      destruct (stk_split asegs _ (bv_unsigned a) (bv_unsigned a + 16) (bv_unsigned a + 1048576) VB ltac:(lia)) as [S1 _].
      destruct (stk_carve asegs _ (bv_unsigned a) (bv_unsigned a + 16) 16 S1 ltac:(cbn; lia)) as [_ (ndj & NDC)].
      replace (bv_unsigned a + 16 - Z.of_nat 16) with (bv_unsigned a) in NDC by (cbn; lia).
      eapply (JOIN (nbl ++ [bv_unsigned a]) [(bv_unsigned a, bv_unsigned a + 1048576)] (mm_add_map a (Z_to_bv 64 1048576) mo) (R - 1048576) m2 ndj).
      { rewrite EN. symmetry. apply Z_to_bv_bv_unsigned. }
      { right. exists a. repeat (split; [first [reflexivity| assumption| lia]|]). exact GA. }
      { intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]]; [| exact VB].
        (nelim (proj2 HNB b Hb) 3%nat; intros Q1 Q2 Q3). eapply stk_wmono_noseg; [exact (NVIS b Hb)| eapply wmono_trans; [exact WM| exact WM2]| unfold AIMG_HI; lia]. }
      { intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|[]]]; [exact (proj2 HNB b Hb)| lia]. }
      { rewrite zlen_app1. lia. }
      { rewrite END. exact NDC. }
      { eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn; lia]. }
      { apply (rw_cells_app _ _ [_; _] [_; _; _; _]). split; [| replace (5816664 + Z.of_nat (cells_size [C4 (Z_to_bv 64 (U + 1)); CB 4 nj])) with 5816672 by (cbn; lia); exact MUB].
        eapply rw_cells_transport; [eapply (rw_cells_take _ _ [_; _] [_; _; _; _]); exact NIDW| exact MU2| exact WM2| cbn; lia]. }
      { rewrite EN, Z_to_bv_bv_unsigned. exact MAP2. }
      { eapply rw_cells_transport; [exact TB1| exact MU2| exact WM2| cbn; lia]. }
      { eapply ro_cells_transport; [| exact MU2| rewrite trace_cells_size; cbn; lia]. eapply ro_cells_transport; [exact TRC| exact MU| rewrite trace_cells_size; cbn; lia]. }
      { eapply ro_cells_transport; [| exact MU2| cbn; lia]. eapply ro_cells_transport; [exact CF240| exact MU| cbn; lia]. }
      { eapply (mmap_consts_munch _ m); [eapply (mmap_consts_munch _ mv _ HC0 MU); cbn; lia| exact MU2| ..]; cbn; lia. }
      { eapply (ssrep_munch _ m); [eapply (ssrep_munch _ mv); [exact SSR| exact SSW| exact MU| exact WM| intros a' sz' A1 A2; cbn; lia]| exact SSW| exact MU2| exact WM2| intros a' sz' A1 A2; cbn; lia]. }
      { exact MI2. } { exact ST2. }
      { apply (munch_weaken _ [(lo, bv_unsigned sp + 112); (p, p + 4); (5816664, 5816676); (qm, qm + 8); (bv_unsigned a, bv_unsigned a + 1048576)]) in MU. 2:{ unfold sub_fp; cbn; intros; lia. }
        apply (munch_weaken _ [(lo, bv_unsigned sp + 112); (p, p + 4); (5816664, 5816676); (qm, qm + 8); (bv_unsigned a, bv_unsigned a + 1048576)]) in MU2. 2:{ unfold sub_fp; cbn; intros; lia. }
        exact (munch_trans _ _ _ _ MU MU2). }
      { exact (wmono_trans asegs _ _ _ WM WM2). }
  Qed.
End PUTINS.


End CeilWrap.
End RTW_depot_put.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_nstore.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_nstore.RTW_depot_create.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_nstore.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_nstore.RTW_depot_alloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_hash.
Import RTW_depot_find.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_nstore.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_nstore.RTW_depot_store.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_depot_nstore.
Import RTW_depot_put.
Import RTW_depot_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_grant RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition depot_put_spec' : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (P : Z) (tr : list Z) (lo : Z),
  RTS st m mo g ->
  a0 = wz P -> a1 = wz (zlen tr) -> 1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  cells_at asegs m P (trace_cells tr) -> (P + 8 * zlen tr <= lo \/ bv_unsigned sp <= P) -> alloc_ceiling <= P -> P + 8 * zlen tr < 2^64 ->
  tp = wz ATP ->
  trs_room tr (st_trs st) ->
  rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ADEPOT_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (depot_put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st tr lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ADEPOT_PUT) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_of_bytes : forall j : list byte, length j = 4%nat -> le4 (Z_to_bv 64 (bytes_le_to_Z j)) = j.
Proof.
  intros j L. unfold le4.
  pose proof (le_val_range (map bv_unsigned j) (bytes_ok_map j)) as R. rewrite length_map, L in R. change (256 ^ Z.of_nat 4) with 4294967296 in R.
  rewrite <- bytes_le_to_Z_le_val in R. rewrite unsigned_lit by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.
Lemma CB4_as_C4 : forall m A (x : word) j rest, rw_cells asegs m A (C8 x :: CB 4 j :: rest) -> exists w : word, rw_cells asegs m A (C8 x :: C4 w :: rest).
Proof.
  intros m A x j rest H. assert (L : length j = 4%nat) by (destruct H as [[W _] _]; cbn in W; tauto).
  exists (Z_to_bv 64 (bytes_le_to_Z j)). eapply rw_cells_recast; [exact H| | | reflexivity].
  - destruct H as [[W _] _]. cbn in W |- *. tauto.
  - cbn [cells_bytes cbytes app]. rewrite (le4_of_bytes j L). reflexivity.
Qed.
Lemma C4_as_CB4 : forall m A (x w : word) rest, rw_cells asegs m A (C8 x :: C4 w :: rest) -> rw_cells asegs m A (C8 x :: CB 4 (le4 w) :: rest).
Proof.
  intros m A x w rest H. eapply rw_cells_recast; [exact H| | reflexivity| reflexivity].
  destruct H as [[W _] _]. cbn -[le4] in W |- *. rewrite length_le4. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nb_range_i : forall st, RTWF st -> forall b, In b (d_nblocks (st_depot st)) -> 0x5ff000 <= b /\ b + NODEBLOCK_SIZE <= alloc_ceiling /\ b mod 4096 = 0.
Proof. intros st WF b Hb. (nelim (nb_range st WF b Hb) 3%nat; intros R1 R2 R3). pose proof (ablk_img _ _ R1) as R0. unfold AIMG_HI in R0. tauto. Qed.
Lemma sb_range_i : forall st, RTWF st -> forall b, In b (d_sblocks (st_depot st)) -> 0x5ff000 <= b /\ b + STOREBLOCK_SIZE <= alloc_ceiling /\ b mod 4096 = 0.
Proof. intros st WF b Hb. (nelim (sb_range st WF b Hb) 3%nat; intros R1 R2 R3). pose proof (ablk_img _ _ R1) as R0. unfold AIMG_HI in R0. tauto. Qed.

Section ENTRY.
  Variables (st : rtstate) (m : word -> option byte) (mo : Model).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HM : RTMODEL st mo.
  Let d := st_depot st.

  Lemma entry_ss : ssrep m (d_T d) (d_sblocks d) /\ sswf (d_T d) (d_sblocks d).
  Proof.
    (nelimp (rr_depot st m HR) 8%nat; intros _ _ _ _ _ SS SBLK SBVIS). pose proof (wf_depot_ok st WF) as WD.
    unfold A_STACKSTORE, STOREBLOCK_SIZE, SSTORE_NBLOCKS in *. cbv delta [wz zb] in SS, SBLK.
    split; [split; [| split]| split; [| split]].
    - unfold d_nsb, zlen in SS. exact SS.
    - intros bb Hb. destruct (SBLK bb Hb) as (j1 & H). replace (1556808 + 16 + 16 * bb) with (1556824 + 16 * bb) in H by lia.
      exact (CB4_as_C4 m _ _ j1 _ H).
    - exact SBVIS.
    - exact (wd_T_pos st WD).
    - pose proof (wd_nsb st WD) as E. unfold d_nsb, SSTORE_BLOCK_FRAMES in E. exact E.
    - intros bb Hb. exact (sb_range_i st WF bb Hb).
  Qed.

  Lemma entry_nb : zlen (d_nblocks d) = d_U d / 65536 + 1
    /\ (forall b, In b (d_nblocks d) -> 0x5ff000 <= b /\ b + 1048576 <= alloc_ceiling /\ b mod 4096 = 0)
    /\ (forall b, In b (d_nblocks d) -> stk asegs m b (b + 1048576)).
  Proof.
    pose proof (wf_depot_ok st WF) as WD. (nelimp (rr_depot st m HR) 5%nat; intros _ _ _ NBVIS _).
    split; [pose proof (wd_nnb st WD) as E; unfold d_nnb, DEPOT_L2_NODES in E; exact E|].
    split; [intros bb Hb; exact (nb_range_i st WF bb Hb)| exact NBVIS].
  Qed.

  (* [comment removed for export] *)
  Lemma entry_nbsb : forall b b', In b (d_nblocks d) -> In b' (d_sblocks d) -> b + 1048576 <= b' \/ b' + 8388608 <= b.
  Proof.
    intros bb b' Hb Hb'. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW.
    destruct (pwdj_In _ (bb, bb + NODEBLOCK_SIZE) (b', b' + STOREBLOCK_SIZE) PW) as [E|[E|E]]; cbn [fst snd] in *.
    - unfold rt_ranges. do 2 right. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists bb. auto.
    - unfold rt_ranges. do 2 right. rewrite !in_app_iff. right; right; right. apply in_map_iff. exists b'. auto.
    - injection E. unfold NODEBLOCK_SIZE, STOREBLOCK_SIZE. lia.
    - unfold NODEBLOCK_SIZE in E. lia.
    - unfold STOREBLOCK_SIZE in E. lia.
  Qed.

  Lemma entry_mapped : forall lo sz, In (lo, sz) (rt_loose st) ->
    exists (bm km : word), In (bm, km) (vm_maps (m_vmmaps mo)) /\ bv_unsigned bm <= lo /\ lo + sz <= bv_unsigned bm + bv_unsigned km.
  Proof.
    intros lo sz Hin. (nelimp HM 6%nat; intros _ _ _ _ M5 _).
    pose proof (M5 _ Hin) as Z1. unfold zin in Z1. cbn [fst snd] in Z1.
    assert (R : 4096 <= lo /\ lo < lo + sz /\ lo + sz <= alloc_ceiling).
    { pose proof (wb_ranges st (wf_base_ok st WF) (lo, lo + sz)) as X. cbn [fst snd] in X.
      assert (In (lo, lo + sz) (rt_ranges st)).
      { unfold rt_ranges. do 2 right. unfold rt_loose in Hin. rewrite !in_app_iff in Hin |- *. rewrite !in_map_iff in Hin.
        destruct Hin as [H|[(e & E & H)|[(bb & E & H)|(bb & E & H)]]].
        - left. apply in_map_iff. exists (lo, sz). auto.
        - right; left. apply in_map_iff. exists e. injection E; intros <- <-. auto.
        - right; right; left. apply in_map_iff. exists bb. injection E; intros <- <-. auto.
        - right; right; right. apply in_map_iff. exists bb. injection E; intros <- <-. auto. }
      specialize (X H). blia. }
    exists (wz lo), (wz sz). split; [exact Z1|]. unfold wz, KHIGHMEM_BEG, AIMG_HI in *. rewrite !unsigned_lit by lia. lia.
  Qed.
  Lemma entry_nbm : forall b, In b (d_nblocks d) -> exists (bm km : word), In (bm, km) (vm_maps (m_vmmaps mo)) /\ bv_unsigned bm <= b /\ b + 1048576 <= bv_unsigned bm + bv_unsigned km.
  Proof. intros bb Hb. apply (entry_mapped bb 1048576). unfold rt_loose. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists bb. auto. Qed.
  Lemma entry_sbm : forall b, In b (d_sblocks d) -> exists (bm km : word), In (bm, km) (vm_maps (m_vmmaps mo)) /\ bv_unsigned bm <= b /\ b + 8388608 <= bv_unsigned bm + bv_unsigned km.
  Proof. intros bb Hb. apply (entry_mapped bb 8388608). unfold rt_loose. rewrite !in_app_iff. right; right; right. apply in_map_iff. exists bb. auto. Qed.

  (* [comment removed for export] *)
  Lemma entry_ranges_mapped : forall r, In r (rt_ranges st) ->
    exists (bm km : word), In (bm, km) (vm_maps (m_vmmaps mo)) /\ bv_unsigned bm <= fst r /\ snd r <= bv_unsigned bm + bv_unsigned km.
  Proof.
    intros r Hr. (nelimp HM 6%nat; intros M1 M2 _ _ M5 _).
    pose proof (wb_ranges st (wf_base_ok st WF) r Hr) as X.
    unfold rt_ranges in Hr. cbn [In] in Hr. rewrite !in_app_iff, !in_map_iff in Hr.
    unfold zin, wz, KHIGHMEM_BEG, AIMG_HI, PRIM_RES_SIZE, PTRARR_RES_SIZE in *.
    destruct Hr as [<-|[<-|[(e & <- & H)|[(e & <- & H)|[(bb & <- & H)|(bb & <- & H)]]]]]; cbn [fst snd] in *.
    - exists (Z_to_bv 64 (st_pbase st)), (Z_to_bv 64 PRIM_RES_SIZE). split; [exact M1|]. unfold PRIM_RES_SIZE in *. rewrite !unsigned_lit by blia. lia.
    - exists (Z_to_bv 64 (st_pa st)), (Z_to_bv 64 PTRARR_RES_SIZE). split; [exact M2|]. unfold PTRARR_RES_SIZE in *. rewrite !unsigned_lit by blia. lia.
    - destruct e as [lo sz]. cbn [fst snd] in *. apply (entry_mapped lo sz). unfold rt_loose. rewrite !in_app_iff. left. exact H.
    - destruct e as [mb n]. cbn [fst snd] in *. apply (entry_mapped mb (smapsize n)). unfold rt_loose. rewrite !in_app_iff. right; left. apply in_map_iff. exists (mb, n). auto.
    - apply (entry_mapped bb NODEBLOCK_SIZE). unfold rt_loose. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists bb. auto.
    - apply (entry_mapped bb STOREBLOCK_SIZE). unfold rt_loose. rewrite !in_app_iff. right; right; right. apply in_map_iff. exists bb. auto.
  Qed.
End ENTRY.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pwdj_nth : forall L (i j : nat) r1 r2, pwdj L -> nth_error L i = Some r1 -> nth_error L j = Some r2 -> i <> j ->
  snd r1 <= fst r2 \/ snd r2 <= fst r1.
Proof.
  induction L as [|r L IH]; intros i j r1 r2 HP H1 H2 NE; [destruct i; discriminate|].
  cbn in HP. destruct HP as [HF HP]. rewrite Forall_forall in HF.
  destruct i as [|i], j as [|j]; cbn in H1, H2; [lia| | |].
  - injection H1; intros <-. apply nth_error_In in H2. pose proof (HF _ H2). lia.
  - injection H2; intros <-. apply nth_error_In in H1. pose proof (HF _ H1). lia.
  - eapply IH; eauto.
Qed.
Lemma nthz_blocks_disj : forall (l : list Z) (sz : Z) i j, pwdj (map (fun b => (b, b + sz)) l) ->
  0 <= i < zlen l -> 0 <= j < zlen l -> i <> j ->
  nthz l i 0 + sz <= nthz l j 0 \/ nthz l j 0 + sz <= nthz l i 0.
Proof.
  intros l sz i j PW Hi Hj NE. unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [lia|]. destruct (Z.ltb_spec0 j 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) as [x|] eqn:E1; [| apply nth_error_None in E1; lia].
  destruct (nth_error l (Z.to_nat j)) as [y|] eqn:E2; [| apply nth_error_None in E2; lia].
  rewrite (nth_error_nth _ _ _ E1), (nth_error_nth _ _ _ E2).
  pose proof (pwdj_nth _ (Z.to_nat i) (Z.to_nat j) (x, x + sz) (y, y + sz) PW) as D.
  rewrite !nth_error_map, E1, E2 in D. cbn [option_map fst snd] in D. destruct (D eq_refl eq_refl ltac:(lia)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FINAL.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (c1 c2 c3 : list (Z * Z)) (c4 : list qbatch) (c5 : list (qbatch * Z)).
Let st  := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5.
Variables (m m' : word -> option byte) (mo mo1 mo' : Model) (G G' : list (Z * Z)) (R R1 R' : Z) (SP lo : Z).
Variables (tr : list Z) (start : Z) (nbl' sbl' : list Z) (nb1 nb2 : list (Z * Z)) (lj : list byte).
Local Abbreviation d := a12.
Let h := trace_hash tr.
Let b := dbucket h.
Let v := d_tab d b.
Let U := d_U d.
Let k := (U + 1) / 65536.
Let n := zlen tr.
Hypothesis HR : RTREP st m.
Hypothesis WF : RTWF st.
Hypothesis HM : RTMODEL st mo.
Hypothesis HG : GWIN st m mo (mkG G R).
Hypothesis HFR : FRONTR mo R.
Hypothesis HSW : SWIN st (mkG G R).   (* [comment removed for export] *)
Hypothesis HOK : LOK asegs mo.
Hypothesis NWX : no_wx asegs.
Hypothesis TRL : 1 <= n <= TRACE_MAX_LEN.
Hypothesis ROOM : trs_room tr a13.
Hypothesis LO : CEIL <= lo /\ lo <= SP /\ SP <= 2^64.
Hypothesis HRR : 1048576 + 8388608 <= R.
Hypothesis NOTFOUND : forall id, linked d v id -> 1 <= id <= U -> dn_hash (dnode d id) <> h.
Hypothesis HNB1 : (nbl' = d_nblocks d /\ nb1 = [] /\ mo1 = mo /\ R1 = R /\ k < zlen (d_nblocks d))
        \/ (exists a : word, nbl' = d_nblocks d ++ [bv_unsigned a] /\ nb1 = [(bv_unsigned a, bv_unsigned a + 1048576)] /\ k = zlen (d_nblocks d)
                             /\ mmap_grant mo a 1048576
                             /\ mo1 = mm_add_map a (Z_to_bv 64 1048576) mo /\ R1 = R - 1048576
                             /\ 0x5ff000 <= bv_unsigned a /\ bv_unsigned a + 1048576 <= alloc_ceiling /\ bv_unsigned a mod 4096 = 0).
Hypothesis HS1 : start = d_T d \/ (start = d_T d + (n + 1) /\ d_T d mod 1048576 + (n + 1) > 1048576).
Hypothesis HS2 : start mod 1048576 + (n + 1) <= 1048576.
Hypothesis SSR' : ssrep m' (start + (n + 1)) sbl'.
Hypothesis SSW' : sswf (start + (n + 1)) sbl'.
Hypothesis HBF : start / 1048576 < zlen sbl'.
Hypothesis HALT : (sbl' = d_sblocks d /\ nb2 = [] /\ mo' = mo1 /\ G' = G /\ R' = R1)
        \/ (exists a : word, sbl' = d_sblocks d ++ [bv_unsigned a] /\ nb2 = [(bv_unsigned a, bv_unsigned a + 8388608)]
                             /\ mmap_grant mo1 a 8388608
                             /\ mo' = mm_add_lazy a (Z_to_bv 64 8388608) mo1 /\ G' = (bv_unsigned a, bv_unsigned a + 8388608) :: G /\ R' = R1 - 8388608).
Hypothesis NVIS' : forall bb, In bb nbl' -> stk asegs m' bb (bb + 1048576).
Hypothesis NODE' : rw_cells asegs m' (nthz nbl' k 0 + 16 * ((U + 1) mod 65536)) [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 (start + 1))].
Hypothesis TAB' : rw_cells asegs m' (A_DEPOT + 4 * b) [C4 (Z_to_bv 64 (U + 1))].
Hypothesis NIDS' : exists nj', rw_cells asegs m' 0x58c158 [C4 (Z_to_bv 64 (U + 1)); CB 4 nj'; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Hypothesis MAP1' : rw_cells asegs m' (0x58c168 + 8 * k) [C8 (Z_to_bv 64 (nthz nbl' k 0))].
Hypothesis MI' : mem_inv asegs m'.
Definition WTOT : list (Z * Z) :=
  (lo, SP) :: (A_DEPOT + 4 * b, A_DEPOT + 4 * b + 4) :: (0x58c158, 0x58c164) :: (0x58c168 + 8 * k, 0x58c168 + 8 * k + 8)
  :: (nthz nbl' k 0 + 16 * ((U + 1) mod 65536), nthz nbl' k 0 + 16 * ((U + 1) mod 65536) + 16)
  :: (nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576), nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576) + 8 * (n + 1))
  :: ssfp (d_T d) nb2 ++ nb1.
Hypothesis MU : munch WTOT m m'.
Hypothesis WM : wmono asegs m m'.

Definition d' : depot_st := d_ins d h v (start + 1) b (start + (n + 1)) nbl' sbl'.
Definition st' : rtstate := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 d' (tr :: a13) a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5.
Definition nnew : list Z := match nb1 with [] => [] | (x, _) :: _ => [x] end.
Definition snew : list Z := match nb2 with [] => [] | (x, _) :: _ => [x] end.

(* [comment removed for export] *)
Lemma WD : wf_depot st. Proof. exact (wf_depot_ok st WF). Qed.
Lemma U_facts : 1 <= U /\ U + 1 <= DEPOT_KMAX + 2 /\ zlen a13 < DEPOT_KMAX.
Proof.
  pose proof WD as W. pose proof (wd_U_pos st W). pose proof (wd_U_le st W) as L. pose proof (wd_trs0 st W). pose proof (wd_trs_max st W) as M.
  cbn [st_depot st_trs st_trs0 st] in *.
  assert (FR : ~ In tr (a13 ++ a14)) by (exact (tr_fresh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 WF tr h b v eq_refl eq_refl eq_refl NOTFOUND)).
  unfold trs_room in ROOM. destruct ROOM as [RM|RM]; [exfalso; apply FR; apply in_or_app; left; exact RM|]. unfold U, DEPOT_KMAX, zlen in *. lia.
Qed.
Lemma T_facts : 1 <= d_T d /\ d_T d + 64 < 2^31 /\ zlen (d_sblocks d) = (d_T d - 1) / 1048576 + 1 /\ zlen (d_sblocks d) <= 32.
Proof.
  pose proof WD as W. pose proof (wd_T_pos st W). pose proof (wd_T_le st W) as L. pose proof (wd_nsb st W) as NS. pose proof (wd_nsb_max st W). pose proof (wd_trs_max st W).
  cbn [st_depot st_trs st] in *. unfold d_nsb, DEPOT_NSB_MAX, DEPOT_KMAX, SSTORE_BLOCK_FRAMES in *.
  rewrite NS in L. split; [lia|]. split; [Z.div_mod_to_equations; nia|]. split; [exact NS|]. Z.div_mod_to_equations; nia.
Qed.
Lemma NB_facts : zlen (d_nblocks d) = U / 65536 + 1 /\ zlen (d_nblocks d) <= 17 /\ 0 <= k <= zlen (d_nblocks d).
Proof.
  pose proof WD as W. pose proof (wd_nnb st W) as E. cbn [st_depot st] in E. unfold d_nnb, DEPOT_L2_NODES in E.
  (nelimp U_facts 3%nat; intros U1 U2 _). unfold DEPOT_KMAX in U2. unfold k. split; [exact E|]. rewrite E. Z.div_mod_to_equations. nia.
Qed.
Lemma nbl'_eq : d_nblocks d' = d_nblocks d ++ nnew /\ zlen nbl' = (U + 1) / 65536 + 1 /\ k < zlen nbl'.
Proof.
  (nelimp NB_facts 3%nat; intros E _ K1). unfold d'. cbn [d_nblocks d_ins]. unfold nnew.
  pose proof HNB1 as HNB1c. destruct HNB1c as [(E1 & E2 & _ & _ & KL)|(a & E1 & E2 & KE & _)]; rewrite E1, E2.
  - rewrite app_nil_r. split; [reflexivity|]. fold k in KL. unfold k in *. rewrite E in KL |- *. split; [Z.div_mod_to_equations; nia| lia].
  - split; [reflexivity|]. rewrite zlen_app1. fold k in KE. unfold k in *. rewrite E in KE |- *. split; [Z.div_mod_to_equations; nia| lia].
Qed.
Lemma sbl'_eq : d_sblocks d' = d_sblocks d ++ snew.
Proof. unfold d'. cbn [d_sblocks d_ins]. unfold snew. pose proof HALT as HALTc. destruct HALTc as [(E1 & E2 & _)|(a & E1 & E2 & _)]; rewrite E1, E2; [rewrite app_nil_r|]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma maps_mo1 : forall e, In e (vm_maps (m_vmmaps mo)) -> In e (vm_maps (m_vmmaps mo1)).
Proof.
  intros e He. pose proof HNB1 as X. destruct X as [(_ & _ & E & _)|(a & _ & _ & _ & _ & E & _)]; rewrite E; [exact He|].
  rewrite mm_add_map_vmmaps. cbn [vm_maps]. right. exact He.
Qed.

Lemma nb1_fresh : forall f, In f nb1 -> 0x5ff000 <= fst f /\ snd f = fst f + 1048576 /\ snd f <= alloc_ceiling /\ fst f mod 4096 = 0
   /\ (forall r, In r (rt_ranges st) -> snd f <= fst r \/ snd r <= fst f)
   /\ exists a : word, fst f = bv_unsigned a /\ mmap_grant mo a 1048576.
Proof.
  intros f Hf. pose proof HNB1 as X. destruct X as [(_ & E & _)|(a & _ & E & _ & GR & _ & _ & K1 & K2 & K3)]; rewrite E in Hf; [destruct Hf|].
  destruct Hf as [<-|[]]. cbn [fst snd]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact K3|]. split.
  - intros r Hr. (nelim (entry_ranges_mapped st mo WF HM r Hr) 5%nat; intros bm km HIN B1 B2).
    (nelimp (wb_ranges st (wf_base_ok st WF) r Hr) 3%nat; intros _ RR _).
    destruct (fresh_vs_mapped_n mo a bm km 1048576 (fst r) (snd r - fst r) GR ltac:(lia) ltac:(lia) HIN B1 ltac:(lia) ltac:(lia)); lia.
  - exists a. auto.
Qed.
Lemma nb2_fresh : forall f, In f nb2 -> 0x5ff000 <= fst f /\ snd f = fst f + 8388608 /\ snd f <= alloc_ceiling /\ fst f mod 4096 = 0
   /\ (forall r, In r (rt_ranges st) -> snd f <= fst r \/ snd r <= fst f)
   /\ (forall f1, In f1 nb1 -> snd f <= fst f1 \/ snd f1 <= fst f)
   /\ exists a : word, fst f = bv_unsigned a /\ mmap_grant mo1 a 8388608.
Proof.
  intros f Hf. pose proof HALT as X. destruct X as [(_ & E & _)|(a & E1 & E & GR & _)]; rewrite E in Hf; [destruct Hf|].
  destruct Hf as [<-|[]]. cbn [fst snd].
  assert (RG : 0x5ff000 <= bv_unsigned a /\ bv_unsigned a + 8388608 <= alloc_ceiling /\ bv_unsigned a mod 4096 = 0).
  { (nelimp SSW' 3%nat; intros _ _ BR). apply BR. rewrite E1. apply in_or_app. right. left. reflexivity. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [tauto|]. split; [| split].
  - intros r Hr. (nelim (entry_ranges_mapped st mo WF HM r Hr) 5%nat; intros bm km HIN B1 B2).
    (nelimp (wb_ranges st (wf_base_ok st WF) r Hr) 3%nat; intros _ RR _).
    destruct (fresh_vs_mapped_n mo1 a bm km 8388608 (fst r) (snd r - fst r) GR ltac:(lia) ltac:(lia) (maps_mo1 _ HIN) B1 ltac:(lia) ltac:(lia)); lia.
  - intros f1 Hf1. pose proof HNB1 as Y. destruct Y as [(_ & E2 & _)|(a1' & _ & E2 & _ & GR1 & EM & _)]; rewrite E2 in Hf1; [destruct Hf1|]. destruct Hf1 as [<-|[]]. cbn [fst snd].
    assert (HIN : In (a1', Z_to_bv 64 1048576) (vm_maps (m_vmmaps mo1))) by (rewrite EM, mm_add_map_vmmaps; cbn [vm_maps]; left; reflexivity).
    destruct (fresh_vs_mapped_n mo1 a a1' (Z_to_bv 64 1048576) 8388608 (bv_unsigned a1') 1048576 GR ltac:(lia) ltac:((lia_on RG)) HIN ltac:(lia) ltac:(rewrite unsigned_lit by lia; lia) ltac:(lia)); lia.
  - exists a. auto.
Qed.
Lemma LOK_mo1 : LOK asegs mo1.
Proof.
  pose proof HNB1 as X. destruct X as [(_ & _ & E & _)|(a & _ & _ & _ & (GA & GP & GC & GF) & E & _)]; rewrite E; [exact HOK|].
  apply mm_add_map_LOK; [exact HOK| rewrite unsigned_lit by lia; exact GC|].
  rewrite region_free_app in GF. apply andb_true_iff in GF as [_ GF]. exact GF.
Qed.
Lemma SHBAND_mo1 : SHBAND mo1.
Proof. apply (shband_mono mo mo1 maps_mo1). exact (shband_of_model st mo HM). Qed.
Lemma nb1_ablk : forall f, In f nb1 -> ablk (fst f) (snd f).
Proof.
  intros f Hf. (nelim (nb1_fresh f Hf) 8%nat; intros _ X2 _ _ _ a X6 GR). rewrite X2, X6.
  exact (grant_ablk_b mo a 1048576 HOK (shband_of_model st mo HM) ltac:(lia) GR).
Qed.
Lemma nb2_ablk : forall f, In f nb2 -> ablk (fst f) (snd f).
Proof.
  intros f Hf. (nelim (nb2_fresh f Hf) 9%nat; intros _ X2 _ _ _ _ a X6 GR). rewrite X2, X6.
  exact (grant_ablk_b mo1 a 8388608 LOK_mo1 SHBAND_mo1 ltac:(lia) GR).
Qed.

Lemma nnew_spec : forall x, In x nnew <-> exists f, In f nb1 /\ x = fst f.
Proof.
  intros x. unfold nnew. pose proof HNB1 as X. destruct X as [(_ & E & _)|(a & _ & E & _)]; rewrite E; cbn.
  - split; [intros []| intros nelH_; (nelim nelH_ 3%nat; intros f [] _)].
  - split; [intros [<-|[]]; eexists; split; [left; reflexivity| reflexivity]| intros (f & [<-|[]] & ->); left; reflexivity].
Qed.
Lemma snew_spec : forall x, In x snew <-> exists f, In f nb2 /\ x = fst f.
Proof.
  intros x. unfold snew. pose proof HALT as X. destruct X as [(_ & E & _)|(a & _ & E & _)]; rewrite E; cbn.
  - split; [intros []| intros nelH_; (nelim nelH_ 3%nat; intros f [] _)].
  - split; [intros [<-|[]]; eexists; split; [left; reflexivity| reflexivity]| intros (f & [<-|[]] & ->); left; reflexivity].
Qed.
Lemma nbl'_app : nbl' = d_nblocks d ++ nnew.
Proof. unfold nnew. pose proof HNB1 as X. destruct X as [(E1 & E2 & _)|(a & E1 & E2 & _)]; rewrite E1, E2; [rewrite app_nil_r|]; reflexivity. Qed.
Lemma sbl'_app : sbl' = d_sblocks d ++ snew.
Proof. unfold snew. pose proof HALT as X. destruct X as [(E1 & E2 & _)|(a & E1 & E2 & _)]; rewrite E1, E2; [rewrite app_nil_r|]; reflexivity. Qed.

(* [comment removed for export] *)
Local Abbreviation NS := (nthz nbl' k 0 + 16 * ((U + 1) mod 65536)).
Local Abbreviation DD := (nthz sbl' (start / 1048576) 0 + 8 * (start mod 1048576)).

Lemma b_facts : 0 <= b < 1048576 /\ 0 <= h < 2^64.
Proof. pose proof (trace_hash_range tr) as HR0. unfold b, dbucket, DEPOT_TAB_LOG, h in *. split; [apply Z.mod_pos_bound; lia| exact HR0]. Qed.

Lemma blkN_facts : In (nthz nbl' k 0) nbl' /\ 0x5ff000 <= nthz nbl' k 0 /\ nthz nbl' k 0 + 1048576 <= alloc_ceiling
  /\ nthz nbl' k 0 <= NS /\ NS + 16 <= nthz nbl' k 0 + 1048576.
Proof.
  (nelimp nbl'_eq 3%nat; intros _ L KL). (nelimp NB_facts 3%nat; intros E _ K0).
  assert (IN : In (nthz nbl' k 0) nbl') by (apply nthz_In; lia).
  assert (R0 : 0x5ff000 <= nthz nbl' k 0 /\ nthz nbl' k 0 + 1048576 <= alloc_ceiling).
  { assert (IN2 : In (nthz nbl' k 0) (d_nblocks d ++ nnew)) by (rewrite <- nbl'_app; exact IN).
    apply in_app_iff in IN2. destruct IN2 as [IN2|IN2].
    - pose proof (nb_range_i st WF _ IN2). unfold KHIGHMEM_BEG, AIMG_HI, NODEBLOCK_SIZE in *. blia.
    - apply nnew_spec in IN2 as (f & Hf & Ef). (nelim (nb1_fresh f Hf) 4%nat; intros X1 X2 X3 _). lia. }
  split; [exact IN|]. split; [lia|]. split; [lia|]. unfold k. Z.div_mod_to_equations. nia.
Qed.
Lemma blkS_facts : In (nthz sbl' (start / 1048576) 0) sbl' /\ 0x5ff000 <= nthz sbl' (start / 1048576) 0
  /\ nthz sbl' (start / 1048576) 0 + 8388608 <= alloc_ceiling
  /\ nthz sbl' (start / 1048576) 0 <= DD /\ DD + 8 * (n + 1) <= nthz sbl' (start / 1048576) 0 + 8388608.
Proof.
  pose proof T_facts as (T1 & _). (nelimp SSW' 3%nat; intros _ _ BR).
  assert (IN : In (nthz sbl' (start / 1048576) 0) sbl') by (apply nthz_In; split; [Z.div_mod_to_equations; lia| exact HBF]).
  (nelim (BR _ IN) 3%nat; intros Q1 Q2 Q3). split; [exact IN|]. split; [lia|]. split; [lia|]. unfold TRACE_MAX_LEN in TRL. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma dj_new : forall a sz, 0 <= sz ->
  (a + sz <= 0x5ff000 \/ CEIL <= a \/ exists r, In r (rt_ranges st) /\ fst r <= a /\ a + sz <= snd r) ->
  disjoint_from (nb2 ++ nb1) a sz.
Proof.
  intros a sz Hsz H.
  assert (G1 : forall f, In f (nb2 ++ nb1) -> a + sz <= fst f \/ snd f <= a).
  { intros f Hf. apply in_app_iff in Hf. destruct Hf as [Hf|Hf].
    - (nelim (nb2_fresh f Hf) 6%nat; intros X1 X2 X3 _ X5 _). unfold CEIL in *. destruct H as [H|[H|(r & Hr & C1 & C2)]]; [blia| lia|].
      destruct (X5 r Hr); lia.
    - (nelim (nb1_fresh f Hf) 6%nat; intros X1 X2 X3 _ X5 _). unfold CEIL in *. destruct H as [H|[H|(r & Hr & C1 & C2)]]; [lia| lia|].
      destruct (X5 r Hr); lia. }
  clear H. induction (nb2 ++ nb1) as [|[l' h'] L IH]; [exact I|]. cbn. split.
  - pose proof (G1 (l', h') ltac:(left; reflexivity)). cbn [fst snd] in *. lia.
  - apply IH. intros f Hf. apply G1. right. exact Hf.
Qed.

Lemma NBR_In : forall bb, In bb (d_nblocks d) -> In (bb, bb + NODEBLOCK_SIZE) (rt_ranges st).
Proof. intros bb H. unfold rt_ranges. do 2 right. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists bb. auto. Qed.
Lemma SBR_In : forall bb, In bb (d_sblocks d) -> In (bb, bb + STOREBLOCK_SIZE) (rt_ranges st).
Proof. intros bb H. unfold rt_ranges. do 2 right. rewrite !in_app_iff. right; right; right. apply in_map_iff. exists bb. auto. Qed.

Ltac djW := match goal with |- disjoint_from ?W ?a ?sz => let sz' := eval cbn in sz in change (disjoint_from W a sz') end;
  unfold WTOT; cbn [disjoint_from ssfp app]; unfold A_DEPOT.

Lemma NBR_pwdj : pwdj (NBR st).
Proof. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_nd in PW. apply pwdj_app_iff in PW as (_ & PW & _). apply pwdj_app_iff in PW as (PW & _). exact PW. Qed.

(* [comment removed for export] *)
Lemma R_depot_final : R_depot st' m'.
Proof.
  (nelimp (rr_depot st m HR) 8%nat; intros TAB NIDSx MAP1s NBVIS NODES SS SBLK SBVIS). cbn [st_depot st] in TAB, NIDSx, MAP1s, NBVIS, NODES, SS, SBLK, SBVIS.
  pose proof b_facts as (BF & HF). (nelimp NB_facts 3%nat; intros NBE NB17 KR). (nelimp nbl'_eq 3%nat; intros NBL1 NBL2 NBL3).
  (nelimp T_facts 4%nat; intros T1 T2 T3 T4). (nelimp blkN_facts 5%nat; intros QN0 QN1 QN2 QN3 QN4). (nelimp blkS_facts 5%nat; intros QS0 QS1 QS2 QS3 QS4).
  (nelimp LO 3%nat; intros L1 L2 L3). unfold CEIL in L1. unfold TRACE_MAX_LEN in TRL.
  (nelimp U_facts 3%nat; intros U1 U2 U3). unfold DEPOT_KMAX in U2, U3.
  assert (TB0 : 0 <= d_T d / 1048576 <= 33) by (Z.div_mod_to_equations; nia).
  assert (DU : d_U d' = U + 1) by (unfold d'; apply dU_ins).
  unfold R_depot. cbn [st_depot st']. rewrite DU.
  assert (EU : U = d_U d) by reflexivity. assert (EK : k = (U + 1) / 65536) by reflexivity. assert (En : n = zlen tr) by reflexivity.
  cbv delta [wz zb] in *. unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, NODEBLOCK_SIZE, STOREBLOCK_SIZE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - (* [comment removed for export] *) intros i Hi. destruct (Z.eq_dec i b) as [->|NE].
    + unfold d'. rewrite dtab_ins_b. exact TAB'.
    + unfold d'. rewrite dtab_ins_other by exact NE. eapply rw_cells_transport; [exact (TAB i Hi)| exact MU| exact WM|].
      djW. repeat (split; [(lia_on T1 L1 U1 Hi HS1 NE TRL QN1 QN3 QS1 QS3 TB0)|]). apply dj_new; [lia|]. left. lia.
  - (* [comment removed for export] *) exact NIDS'.
  - (* [comment removed for export] *) intros k0 Hk0. unfold d'. cbn [d_nblocks d_ins]. destruct (Z.eq_dec k0 k) as [->|NE]; [exact MAP1'|].
    assert (EQ : nthz nbl' k0 0 = nthz (d_nblocks d) k0 0).
    { rewrite nbl'_app. destruct (Z_lt_le_dec k0 (zlen (d_nblocks d))); [apply nthz_app_l; lia|].
      rewrite !nthz_over; [reflexivity| lia|]. rewrite <- nbl'_app. lia. }
    rewrite EQ. eapply rw_cells_transport; [exact (MAP1s k0 Hk0)| exact MU| exact WM|].
    djW. repeat (split; [(lia_on T1 L1 U1 Hk0 BF TRL HS1 NE QN1 QN3 QS1 QS3 TB0)|]). apply dj_new; [lia|]. left. lia.
  - (* [comment removed for export] *) intros bb Hbb. unfold d' in Hbb. cbn [d_nblocks d_ins] in Hbb. exact (NVIS' bb Hbb).
  - (* [comment removed for export] *) intros id Hid. unfold dnode_addr. unfold d' at 1. cbn [d_nblocks d_ins]. unfold DEPOT_L2_NODES, DEPOT_NODE_SZ.
    destruct (Z.eq_dec id (U + 1)) as [->|NE].
    + unfold d'. rewrite dnode_ins_new. cbn [dn_hash dn_link dn_store fst snd]. exact NODE'.
    + unfold d'. rewrite dnode_ins_old by lia.
      assert (QI : 0 <= id / 65536 < zlen (d_nblocks d)) by (rewrite NBE; Z.div_mod_to_equations; nia).
      assert (EQ : nthz nbl' (id / 65536) 0 = nthz (d_nblocks d) (id / 65536) 0) by (rewrite nbl'_app; apply nthz_app_l; exact QI).
      rewrite EQ. pose proof (NODES id ltac:(lia)) as ND. unfold dnode_addr, DEPOT_L2_NODES, DEPOT_NODE_SZ in ND.
      assert (INB : In (nthz (d_nblocks d) (id / 65536) 0) (d_nblocks d)) by (apply nthz_In; exact QI).
      (nelimp (nb_range_i st WF _ INB) 3%nat; intros Y1 Y2 Y3). unfold KHIGHMEM_BEG, AIMG_HI, NODEBLOCK_SIZE in Y1, Y2.
      assert (OFF : 0 <= 16 * (id mod 65536) /\ 16 * (id mod 65536) + 16 <= 1048576) by (Z.div_mod_to_equations; lia).
      eapply rw_cells_transport; [exact ND| exact MU| exact WM|].
      djW. repeat match goal with |- _ /\ _ => split end; try (cut_to TRL T1 L1 U1 Hid Y1 Y2 OFF BF NB17 KR TB0; lia).
      * (* [comment removed for export] *)
        pose proof HNB1 as X. destruct X as [(E1 & _ & _ & _ & KL)|(a & E1 & E5 & KE & _ & _ & _ & K1 & K2 & K3)].
        -- rewrite E1. destruct (Z.eq_dec (id / 65536) k) as [EQK|NEK].
           ++ rewrite EQK. assert (id mod 65536 <> (U + 1) mod 65536) by (intros EM; apply NE; rewrite EK in EQK; Z.div_mod_to_equations; nia). 
              Z.div_mod_to_equations. nia.
           ++ pose proof (nthz_blocks_disj (d_nblocks d) 1048576 (id / 65536) k NBR_pwdj QI ltac:(lia) NEK). Z.div_mod_to_equations. nia.
        -- rewrite E1, KE, nthz_app_r1. (nelim (nb1_fresh (bv_unsigned a, bv_unsigned a + 1048576) ltac:(rewrite E5; left; reflexivity)) 6%nat; intros _ _ _ _ X5 _).
           cbn [fst snd] in X5. pose proof (X5 _ (NBR_In _ INB)) as X6. cbn [fst snd] in X6. unfold NODEBLOCK_SIZE in X6.
           assert (MZ : (U + 1) mod 65536 = 0) by (rewrite EK, NBE in KE; clear - KE U1; Z.div_mod_to_equations; nia).
           rewrite MZ. clear - X6 OFF. lia.
      * (* [comment removed for export] *)
        assert (INS2 : In (nthz sbl' (start / 1048576) 0) (d_sblocks d ++ snew)) by (rewrite <- sbl'_app; exact QS0).
        apply in_app_iff in INS2. destruct INS2 as [INS|INS].
        -- destruct (entry_nbsb st WF _ _ INB INS); lia.
        -- apply snew_spec in INS as (f & Hf & Ef). (nelim (nb2_fresh f Hf) 6%nat; intros _ X2 _ _ X5 _). rewrite <- Ef in *.
           destruct (X5 _ (NBR_In _ INB)); cbn [fst snd] in *; unfold NODEBLOCK_SIZE in *; lia.
      * apply dj_new; [lia|]. right; right. exists (nthz (d_nblocks d) (id / 65536) 0, nthz (d_nblocks d) (id / 65536) 0 + 1048576).
        split; [exact (NBR_In _ INB)|]. cbn [fst snd]. lia.
  - (* [comment removed for export] *) destruct SSR' as (TOT & _). unfold d'. cbn [d_T d_sblocks d_ins]. unfold d_nsb. cbn [d_sblocks]. exact TOT.
  - (* [comment removed for export] *) intros bb Hbb. (nelimp SSR' 3%nat; intros _ BL _). destruct (BL bb Hbb) as (sj & H). exists (le4 sj).
    unfold d'. cbn [d_sblocks d_ins]. replace (1556808 + 16 + 16 * bb) with (1556824 + 16 * bb) by lia. apply C4_as_CB4. exact H.
  - (* [comment removed for export] *) intros bb Hbb. (nelimp SSR' 3%nat; intros _ _ VIS). unfold d' in Hbb. cbn [d_sblocks d_ins] in Hbb. exact (VIS bb Hbb).
Qed.

(* [comment removed for export] *)
Lemma fresh_ok_final : fresh_ok st (nb1 ++ nb2).
Proof.
  intros f Hf. apply in_app_iff in Hf. destruct Hf as [Hf|Hf].
  - (nelim (nb1_fresh f Hf) 6%nat; intros X1 _ _ _ X5 _). split; [exact (nb1_ablk f Hf)| exact X5].
  - (nelim (nb2_fresh f Hf) 6%nat; intros X1 _ _ _ X5 _). split; [exact (nb2_ablk f Hf)| exact X5].
Qed.

Lemma dz_ok_final : Forall (dz_ok st (nb1 ++ nb2)) WTOT.
Proof.
  pose proof b_facts as (BF & _). (nelimp NB_facts 3%nat; intros NBE NB17 KR). (nelimp T_facts 4%nat; intros T1 T2 T3 T4).
  (nelimp blkN_facts 5%nat; intros QN0 QN1 QN2 QN3 QN4). (nelimp blkS_facts 5%nat; intros QS0 QS1 QS2 QS3 QS4). (nelimp LO 3%nat; intros L1 L2 L3).
  assert (TB0 : 0 <= d_T d / 1048576 <= 33) by (Z.div_mod_to_equations; nia).
  unfold WTOT. cbn [ssfp app]. unfold A_DEPOT.
  assert (STAT : forall lo' hi', 0x17c148 <= lo' -> hi' <= 0x5cc168 -> dz_ok st (nb1 ++ nb2) (lo', hi')).
  { intros lo' hi' A B. apply dz_ok_static; [rewrite A_STACKSTORE_val| rewrite A_DEPOT_END_val]; cbn; lia. }
  constructor; [apply dz_ok_stack; cbn; lia|].
  constructor; [apply STAT; lia|]. constructor; [apply STAT; lia|]. constructor; [apply STAT; lia|].
  constructor.
  { (* [comment removed for export] *)
    assert (IN2 : In (nthz nbl' k 0) (d_nblocks d ++ nnew)) by (rewrite <- nbl'_app; exact QN0).
    apply in_app_iff in IN2. destruct IN2 as [IN2|IN2].
    - eapply dz_ok_nb; [exact IN2| cbn; lia| cbn; unfold NODEBLOCK_SIZE; lia].
    - apply nnew_spec in IN2 as (f & Hf & Ef). (nelim (nb1_fresh f Hf) 3%nat; intros X1 X2 _).
      eapply dz_ok_fresh; [apply in_or_app; left; exact Hf| cbn; lia| cbn; lia]. }
  constructor.
  { (* [comment removed for export] *)
    assert (IN2 : In (nthz sbl' (start / 1048576) 0) (d_sblocks d ++ snew)) by (rewrite <- sbl'_app; exact QS0).
    apply in_app_iff in IN2. destruct IN2 as [IN2|IN2].
    - eapply dz_ok_sb; [exact IN2| cbn; lia| cbn; unfold STOREBLOCK_SIZE; lia].
    - apply snew_spec in IN2 as (f & Hf & Ef). (nelim (nb2_fresh f Hf) 3%nat; intros X1 X2 _).
      eapply dz_ok_fresh; [apply in_or_app; right; exact Hf| cbn; lia| cbn; lia]. }
  constructor; [apply STAT; lia|]. constructor; [apply STAT; lia|].
  apply Forall_forall. intros f Hf. destruct f as [l' h']. apply (dz_ok_fresh st _ (l', h')); [| cbn; lia| cbn; lia].
  apply in_app_iff in Hf. apply in_or_app. tauto.
Qed.

Theorem RTREP_final : RTREP st' m'.
Proof.
  apply RTREP_of_nd; [| exact R_depot_final].
  exact (RTREP_nd_set_depot st d' (tr :: a13) m' (dz_others st WF WTOT (nb1 ++ nb2) dz_ok_final fresh_ok_final m m' MU WM HR)).
Qed.

(* [comment removed for export] *)
Lemma nnew_len : (length nnew <= 1)%nat. Proof. unfold nnew. destruct nb1 as [|[? ?] ?]; cbn; lia. Qed.
Lemma snew_len : (length snew <= 1)%nat. Proof. unfold snew. destruct nb2 as [|[? ?] ?]; cbn; lia. Qed.
Lemma NEWR : forall bb, In bb nnew -> ablk bb (bb + NODEBLOCK_SIZE) /\ bb + NODEBLOCK_SIZE <= CEIL /\ bb mod 4096 = 0
                      /\ forall r, In r (rt_ranges st) -> bb + NODEBLOCK_SIZE <= fst r \/ snd r <= bb.
Proof.
  intros bb Hb. apply nnew_spec in Hb as (f & Hf & ->). (nelim (nb1_fresh f Hf) 8%nat; intros X1 X2 X3 X4 X5 a X6 GR).
  split; [pose proof (nb1_ablk f Hf) as AB; rewrite X2 in AB; exact AB|].
  unfold KHIGHMEM_BEG, AIMG_HI, NODEBLOCK_SIZE, CEIL. split; [lia|]. split; [exact X4|]. intros r Hr. destruct (X5 r Hr); lia.
Qed.
Lemma SEWR : forall bb, In bb snew -> ablk bb (bb + STOREBLOCK_SIZE) /\ bb + STOREBLOCK_SIZE <= CEIL /\ bb mod 4096 = 0
                      /\ forall r, In r (rt_ranges st) -> bb + STOREBLOCK_SIZE <= fst r \/ snd r <= bb.
Proof.
  intros bb Hb. apply snew_spec in Hb as (f & Hf & ->). (nelim (nb2_fresh f Hf) 9%nat; intros X1 X2 X3 X4 X5 _ a X6 GR).
  split; [pose proof (nb2_ablk f Hf) as AB; rewrite X2 in AB; exact AB|].
  unfold KHIGHMEM_BEG, AIMG_HI, STOREBLOCK_SIZE, CEIL. split; [lia|]. split; [exact X4|]. intros r Hr. destruct (X5 r Hr); lia.
Qed.
Lemma NSD : forall bb b', In bb nnew -> In b' snew -> bb + NODEBLOCK_SIZE <= b' \/ b' + STOREBLOCK_SIZE <= bb.
Proof.
  intros bb b' Hb Hb'. apply nnew_spec in Hb as (f & Hf & ->). apply snew_spec in Hb' as (f' & Hf' & ->).
  (nelim (nb1_fresh f Hf) 3%nat; intros _ X2 _). (nelim (nb2_fresh f' Hf') 7%nat; intros _ Y2 _ _ _ Y6 _).
  destruct (Y6 f Hf); unfold NODEBLOCK_SIZE, STOREBLOCK_SIZE; lia.
Qed.

Lemma wf_depot_final : wf_depot st'.
Proof.
  (nelimp T_facts 4%nat; intros T1 T2 T3 T4). (nelimp nbl'_eq 3%nat; intros NBL1 NBL2 NBL3). (nelimp SSW' 3%nat; intros ST1 ST2 SBR').
  pose proof blkN_facts as (QN0 & _).
  unfold st', d'.
  eapply (wf_depot_ins a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 WF tr h b v (start + 1) (start + (n + 1)) nbl' sbl' (n + 1));
    try reflexivity.
  - exact ROOM.
  - exact TRL.
  - exact NOTFOUND.
  - unfold TRACE_MAX_LEN in TRL. lia.
  - unfold TRACE_MAX_LEN in TRL. destruct HS1 as [E|[E STR]]; [left| right]; lia.
  - unfold SSTORE_BLOCK_FRAMES. replace (start + (n + 1) - 1) with (start + (n + 1) - 1) by lia. rewrite ST2. reflexivity.
  - unfold DEPOT_L2_NODES. exact NBL2.
  - intros x Hx. assert (IN2 : In x (d_nblocks d ++ nnew)) by (rewrite <- nbl'_app; exact Hx). apply in_app_iff in IN2. destruct IN2 as [I|I].
    + exact (proj2 (proj2 (nb_range st WF x I))).
    + exact (proj1 (proj2 (proj2 (NEWR x I)))).
  - intros x Hx. exact (proj2 (proj2 (SBR' x Hx))).
Qed.

Theorem RTWF_final : RTWF st'.
Proof.
  unfold st'. eapply (RTWF_dep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 d' (tr :: a13) nnew snew WF).
  - exact wf_depot_final.
  - exact (proj1 nbl'_eq).
  - exact sbl'_eq.
  - exact nnew_len.
  - exact snew_len.
  - exact NEWR.
  - exact SEWR.
  - exact NSD.
Qed.

(* [comment removed for export] *)

Lemma lzf_mo' : forall x, lzf mo' x = true <-> (exists bb, In bb snew /\ bb <= bv_unsigned x < bb + 8388608) \/ lzf mo x = true.
Proof.
  intros x.
  assert (L1 : lzf mo1 x = lzf mo x).
  { pose proof HNB1 as X. destruct X as [(_ & _ & E & _)|(a & _ & _ & _ & _ & E & _)]; rewrite E; [reflexivity| apply (f_equal (fun f => f x) (mm_add_map_lzf _ _ _))]. }
  unfold snew. pose proof HALT as X. destruct X as [(_ & E2 & E & _)|(a & _ & E2 & GR & E & _)]; rewrite E, E2.
  - rewrite L1. cbn. split; [intros H; right; exact H| intros [(bb & [] & _)|H]; exact H].
  - (nelimp GR 4%nat; intros _ _ GC GF). rewrite (lzf_add_lazy mo1 a 8388608 x LOK_mo1 GF ltac:(lia)), L1. unfold in_range.
    split.
    + intros H. apply orb_true_iff in H as [H|H]; [left| right; exact H]. apply andb_true_iff in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B.
      exists (bv_unsigned a). split; [left; reflexivity| lia].
    + intros [(bb & [<-|[]] & Hx)|H]; apply orb_true_iff; [left| right; exact H]. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Theorem RTMODEL_final : RTMODEL st' mo'.
Proof.
  unfold st'. eapply (RTMODEL_dep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 d' (tr :: a13) nnew snew
            (proj1 nbl'_eq) sbl'_eq mo mo' HM).
  - (* [comment removed for export] *)
    intros e. unfold nnew, snew, wz, NODEBLOCK_SIZE, STOREBLOCK_SIZE.
    pose proof HALT as X. destruct X as [(_ & E2 & E & _)|(a2' & _ & E2 & _ & E & _)]; rewrite E, E2;
    pose proof HNB1 as Y; destruct Y as [(_ & E1 & E0 & _)|(a1' & _ & E1 & _ & _ & E0 & _)]; rewrite E0, E1;
    rewrite ?mm_add_lazy_vmmaps, ?mm_add_map_vmmaps; cbn [vm_maps map app In]; rewrite ?Z_to_bv_bv_unsigned; (cut_on [TRL LO HNB1 HS1 HALT] tauto).
  - intros x Hx. apply lzf_mo'. right. exact Hx.
  - pose proof HALT as X. destruct X as [(_ & _ & E & _)|(a2' & _ & _ & _ & E & _)]; rewrite E;
    pose proof HNB1 as Y; destruct Y as [(_ & _ & E0 & _)|(a1' & _ & _ & _ & _ & E0 & _)]; rewrite E0; reflexivity.
  - (* [comment removed for export] *)
    intros e He PL.
    assert (INmo : In (wz (fst e), wz (smapsize (snd e))) (vm_maps (m_vmmaps mo))).
    { (nelimp HM 6%nat; intros _ _ _ _ M5 _). apply (M5 (fst e, smapsize (snd e))). unfold rt_loose.
      apply in_or_app; right; apply in_or_app; left. apply in_map_iff. exists e. auto. }
    (nelimp (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e)) ltac:(rewrite rt_ranges_tail; apply in_or_app; right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)) 4%nat; intros Q1 Q2 Q3 _)
.
    cbn [fst snd] in Q1, Q2, Q3.
    assert (U1 : bv_unsigned (wz (fst e)) = fst e) by (unfold wz; apply unsigned_lit; unfold KHIGHMEM_BEG, AIMG_HI in *; blia).
    assert (U2 : bv_unsigned (wz (smapsize (snd e))) = smapsize (snd e)) by (unfold wz; apply unsigned_lit; unfold KHIGHMEM_BEG, AIMG_HI in *; blia).
    assert (PL1 : sec_plain mo1 (fst e) (smapsize (snd e)) /\ In (wz (fst e), wz (smapsize (snd e))) (vm_maps (m_vmmaps mo1))).
    { pose proof HNB1 as Y. destruct Y as [(_ & _ & E0 & _)|(a1' & _ & _ & _ & _ & E0 & _)]; rewrite E0.
      - split; [exact PL| exact INmo].
      - split; [apply sec_plain_add_map; exact PL| rewrite mm_add_map_vmmaps; cbn [vm_maps]; right; exact INmo]. }
    destruct PL1 as [PL1 IN1].
    pose proof HALT as X. destruct X as [(_ & _ & E & _)|(a2' & _ & _ & GR & E & _)]; rewrite E; [exact PL1|].
    apply sec_plain_add_lazy; [exact PL1| lia|].
    (nelim GR 4%nat; intros _ _ _ RF). rewrite region_free_app in RF. apply andb_true_iff in RF as [_ RF].
    pose proof (region_free_elim _ a2' (Z_to_bv 64 8388608) _ _ RF IN1 ltac:(rewrite unsigned_lit by lia; lia) ltac:(rewrite U2; lia)) as D.
    rewrite unsigned_lit in D by lia. rewrite U1, U2 in D. lia.
Qed.

(* [comment removed for export] *)
Theorem GWIN_final : GWIN st' m' mo' (mkG G' R').
Proof.
  unfold st'. eapply (GWIN_dep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 d' (tr :: a13) nnew snew
            sbl'_eq nnew_len snew_len SEWR m m' mo mo' G G' R R' HG HOK WM).
  - intros x Hw. unfold snew. pose proof HALT as X. destruct X as [(_ & E2 & _ & E & _)|(a2' & _ & E2 & _ & _ & E & _)]; rewrite E2; rewrite E in Hw; [right; exact Hw|].
    rewrite in_winb_cons in Hw. apply orb_true_iff in Hw as [Hw|Hw]; [left| right; exact Hw]. cbn [fst snd] in Hw.
    apply andb_true_iff in Hw as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. exists (bv_unsigned a2'). split; [cbn; left; reflexivity| unfold STOREBLOCK_SIZE; lia].
  - intros x Hz. apply lzf_mo' in Hz. exact Hz.
  - intros bb Hb. (nelimp SSR' 3%nat; intros _ _ VIS). unfold STOREBLOCK_SIZE. apply VIS. rewrite sbl'_app. apply in_or_app. right. exact Hb.
Qed.

(* [comment removed for export] *)
Theorem FRONTR_final : FRONTR mo' R'.
Proof.
  assert (F1 : FRONTR mo1 R1 /\ 8388608 <= R1).
  { pose proof HNB1 as X. destruct X as [(_ & _ & E & ER & _)|(a & _ & _ & _ & GR & E & ER & _)]; rewrite E, ER; [split; [exact HFR| lia]|].
    split; [| lia]. apply (FRONTR_grant mo R a 1048576 HFR ltac:(unfold FR_MINGRANT; lia) ltac:(reflexivity) ltac:(lia)). }
  destruct F1 as [F1 R8].
  pose proof HALT as X. destruct X as [(_ & _ & E & _ & ER)|(a & _ & _ & GR & E & _ & ER)]; rewrite E, ER; [exact F1|].
  apply (FRONTR_grant_lazy mo1 R1 a 8388608 F1 ltac:(unfold FR_MINGRANT; lia) ltac:(reflexivity) R8).
Qed.

Lemma R_final : R' = R - 1048576 * zlen nnew - 8388608 * zlen snew /\ gmono (mkG G R) (mkG G' R').
Proof.
  unfold nnew, snew, gmono. cbn [g_win].
  pose proof HALT as X. destruct X as [(_ & E2 & _ & EG & ER)|(a & _ & E2 & _ & _ & EG & ER)]; rewrite E2, EG, ER;
  pose proof HNB1 as Y; destruct Y as [(_ & E1 & _ & ER1 & _)|(a1' & _ & E1 & _ & _ & _ & ER1 & _)]; rewrite E1, ER1; unfold zlen; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; (split; [lia| intros w Hw; first [exact Hw| right; exact Hw]]).
Qed.

Theorem budget_final : budget_ok st (mkG G R) st' (mkG G' R') 0.
Proof.
  unfold budget_ok. cbn [g_res]. destruct R_final as [ER _].
  unfold st'. rewrite (rt_prov_dep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 d' (tr :: a13) nnew snew).
  rewrite (prov_depot_dep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 d' (tr :: a13) nnew snew (proj1 nbl'_eq) sbl'_eq).
  unfold NODEBLOCK_SIZE, STOREBLOCK_SIZE. fold st. lia.
  all: first [exact nnew_len | exact snew_len].
Qed.

(* [comment removed for export] *)
Lemma WTOT_cover : forall iv, In iv WTOT ->
  (iv = (lo, SP))
  \/ (0x17c148 <= fst iv /\ snd iv <= 0x5cc168)
  \/ (exists bb, In bb (d_nblocks d') /\ bb <= fst iv /\ snd iv <= bb + 1048576)
  \/ (exists bb, In bb (d_sblocks d') /\ bb <= fst iv /\ snd iv <= bb + 8388608).
Proof.
  pose proof b_facts as (BF & _). (nelimp NB_facts 3%nat; intros NBE NB17 KR). (nelimp T_facts 4%nat; intros T1 T2 T3 T4).
  (nelimp blkN_facts 5%nat; intros QN0 QN1 QN2 QN3 QN4). (nelimp blkS_facts 5%nat; intros QS0 QS1 QS2 QS3 QS4).
  assert (TB0 : 0 <= d_T d / 1048576 <= 33) by (Z.div_mod_to_equations; nia).
  assert (ND' : d_nblocks d' = nbl') by reflexivity. assert (SD' : d_sblocks d' = sbl') by reflexivity. rewrite ND', SD'.
  intros iv Hiv. unfold WTOT in Hiv. cbn [ssfp app In] in Hiv. unfold A_DEPOT in Hiv.
  destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hiv]]]]]]]]; cbn [fst snd].
  - left. reflexivity.
  - right; left. lia.
  - right; left. lia.
  - right; left. lia.
  - right; right; left. exists (nthz nbl' k 0). split; [exact QN0| lia].
  - right; right; right. exists (nthz sbl' (start / 1048576) 0). split; [exact QS0| lia].
  - right; left. lia.
  - right; left. lia.
  - apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
    + right; right; right. (nelim (nb2_fresh iv Hiv) 3%nat; intros _ X2 _). exists (fst iv). split; [| lia].
      rewrite sbl'_app. apply in_or_app. right. apply snew_spec. exists iv. auto.
    + right; right; left. (nelim (nb1_fresh iv Hiv) 3%nat; intros _ X2 _). exists (fst iv). split; [| lia].
      rewrite nbl'_app. apply in_or_app. right. apply nnew_spec. exists iv. auto.
Qed.

Lemma outside_intro : forall W a, (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof. intros W a H. induction W as [|[l' h'] W IH]; [exact I|]. cbn. split; [exact (H (l', h') ltac:(left; reflexivity))| apply IH; intros iv Hiv; apply H; right; exact Hiv]. Qed.

Theorem rt_frame_final : rt_frame (depot_fp st') lo SP m m'.
Proof.
  intros a Ha HS HN. apply MU. rewrite wa_unsigned by lia. apply outside_intro. intros iv Hiv Hin.
  destruct (WTOT_cover iv Hiv) as [->|[X|[(bb & Hb & X1 & X2)|(bb & Hb & X1 & X2)]]]; cbn [fst snd] in *.
  - exact (HS Hin).
  - apply HN. exists A_STACKSTORE, (A_DEPOT_MAP1 + 8 * 2 ^ 15). split; [left; reflexivity|]. unfold A_STACKSTORE, A_DEPOT_MAP1. lia.
  - apply HN. exists bb, (bb + NODEBLOCK_SIZE). split; [| unfold NODEBLOCK_SIZE; lia]. right. unfold fp_depot_blocks. apply in_or_app. left. apply in_map_iff. exists bb. auto.
  - apply HN. exists bb, (bb + STOREBLOCK_SIZE). split; [| unfold STOREBLOCK_SIZE; lia]. right. unfold fp_depot_blocks. apply in_or_app. right. apply in_map_iff. exists bb. auto.
Qed.

(* [comment removed for export] *)
Lemma nblock'_not_client : forall bb a, In bb (d_nblocks d') -> bb <= a < bb + 1048576 -> ~ cj_client_addr a1 a23 a17 SP a.
Proof.
  intros bb a Hb Ha HC. (nelimp LO 3%nat; intros L1 L2 L3). unfold CEIL in L1.
  assert (ND' : d_nblocks d' = nbl') by reflexivity. rewrite ND', nbl'_app in Hb. apply in_app_iff in Hb.
  assert (RG : ablk bb (bb + 1048576) /\ bb + 1048576 <= alloc_ceiling
          /\ (forall A n0, In (A, n0) a23 -> bb + 1048576 <= A \/ A + n0 <= bb)
          /\ (bb + 1048576 <= a15 \/ a15 + FS_TOTAL <= bb)).
  { destruct Hb as [Hb|Hb].
    - (nelimp (nb_range st WF bb Hb) 3%nat; intros Y1 Y2 _). destruct (nb_blockfree st WF bb Hb) as [B1 B2].
      unfold NODEBLOCK_SIZE in *. split; [exact Y1|]. split; [lia|]. split; [exact (blockfree_lb st WF _ _ B1)| exact B2].
    - apply nnew_spec in Hb as (f & Hf & ->). (nelim (nb1_fresh f Hf) 6%nat; intros X1 X2 X3 _ X5 _). split; [pose proof (nb1_ablk f Hf) as AB; rewrite X2 in AB; exact AB|]. split; [lia|]. split.
      + intros A n0 Hin. (nelimp (block_geom st WF A n0 ltac:(unfold all_blocks; apply in_or_app; left; exact Hin)) 11%nat; intros G0 _ G2 G3 G4 G5 _ _ _ GP GS).
        pose proof (usz_le_rounded8 n0) as (UZ & _).
        destruct (bprim n0) eqn:EP.
        * (nelim (GP eq_refl) 6%nat; intros _ _ _ P1 P2 _). destruct (X5 (st_pbase st, st_pbase st + PRIM_RES_SIZE) ltac:(left; reflexivity)); cbn [fst snd st_pbase st] in *; unfold usz in *; lia.
        * (nelim (GS eq_refl) 3%nat; intros S1 S2 _). destruct (X5 (b_lo A n0, b_lo A n0 + smapsize n0)); cbn [fst snd] in *; [| unfold usz in *; lia| unfold usz in *; lia].
          unfold rt_ranges. do 2 right. rewrite !in_app_iff. right; left. apply in_map_iff. exists (b_lo A n0, n0). auto.
      + destruct (X5 (a15, a15 + FS_TOTAL)); cbn [fst snd] in *; [| lia| lia].
        unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (a15, FS_TOTAL). split; [reflexivity|]. exact (wb_fs_loose st (wf_base_ok st WF)). }
  (nelim RG 4%nat; intros Y1 Y2 RB RF).
  pose proof (ablk_img _ _ Y1) as Y1i. unfold AIMG_HI in Y1i. pose proof (ablk_disj_band _ _ Y1) as Y1b. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in Y1b.
  destruct HC as [H|[H|[(A & n0 & Hin & Hr)|[(F & kk & Hin & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. (lia_on Ha H Y1i).
  - destruct (RB A n0 Hin); lia.
  - (nelimp (frame_range st WF F kk Hin) 4%nat; intros Hk X Y AL). cbn [st_fs st] in X, Y. unfold FS_FRAMES_OFF in *.
    destruct Hr as [Hr|Hr]; [(lia_on Ha Hr RF Y1i X Y AL)|].
    (nelimp (fs_range st WF) 3%nat; intros F1 F2 _). cbn [st_fs st] in F1, F2. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, FS_TOTAL in *.
    assert (FZ : 0 < fsz kk) by (destruct Hk as [-> | ->]; cbn; (lia_on Hr)).
    pose proof (rt_SH_bounds F ltac:(blia)) as B0. pose proof (rt_SH_bounds (F + fsz kk) ltac:((cut_on [X Y F1 FZ] blia))) as B. rewrite (rt_SH_aligned_add F (fsz kk) AL) in B. blia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. (lia_on Ha H Y1b).
Qed.

Lemma sblock'_not_client : forall bb a, In bb (d_sblocks d') -> bb <= a < bb + 8388608 -> ~ cj_client_addr a1 a23 a17 SP a.
Proof.
  intros bb a Hb Ha HC. (nelimp LO 3%nat; intros L1 L2 L3). unfold CEIL in L1.
  assert (SD' : d_sblocks d' = sbl') by reflexivity. rewrite SD', sbl'_app in Hb. apply in_app_iff in Hb.
  assert (RG : ablk bb (bb + 8388608) /\ bb + 8388608 <= alloc_ceiling
          /\ (forall A n0, In (A, n0) a23 -> bb + 8388608 <= A \/ A + n0 <= bb)
          /\ (bb + 8388608 <= a15 \/ a15 + FS_TOTAL <= bb)).
  { destruct Hb as [Hb|Hb].
    - (nelimp (sb_range st WF bb Hb) 3%nat; intros Y1 Y2 _). destruct (sb_blockfree st WF bb Hb) as [B1 B2].
      unfold STOREBLOCK_SIZE in *. split; [exact Y1|]. split; [lia|]. split; [exact (blockfree_lb st WF _ _ B1)| exact B2].
    - apply snew_spec in Hb as (f & Hf & ->). (nelim (nb2_fresh f Hf) 6%nat; intros X1 X2 X3 _ X5 _). split; [pose proof (nb2_ablk f Hf) as AB; rewrite X2 in AB; exact AB|]. split; [lia|]. split.
      + intros A n0 Hin. (nelimp (block_geom st WF A n0 ltac:(unfold all_blocks; apply in_or_app; left; exact Hin)) 11%nat; intros G0 _ G2 G3 G4 G5 _ _ _ GP GS).
        pose proof (usz_le_rounded8 n0) as (UZ & _).
        destruct (bprim n0) eqn:EP.
        * (nelim (GP eq_refl) 6%nat; intros _ _ _ P1 P2 _). destruct (X5 (st_pbase st, st_pbase st + PRIM_RES_SIZE) ltac:(left; reflexivity)); cbn [fst snd st_pbase st] in *; unfold usz in *; (lia_on X2 G3 P1 H G4 P2).
        * (nelim (GS eq_refl) 3%nat; intros S1 S2 _). destruct (X5 (b_lo A n0, b_lo A n0 + smapsize n0)); cbn [fst snd] in *; [| unfold usz in *; lia| unfold usz in *; lia].
          unfold rt_ranges. do 2 right. rewrite !in_app_iff. right; left. apply in_map_iff. exists (b_lo A n0, n0). auto.
      + destruct (X5 (a15, a15 + FS_TOTAL)); cbn [fst snd] in *; [| lia| lia].
        unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (a15, FS_TOTAL). split; [reflexivity|]. exact (wb_fs_loose st (wf_base_ok st WF)). }
  (nelim RG 4%nat; intros Y1 Y2 RB RF).
  pose proof (ablk_img _ _ Y1) as Y1i. unfold AIMG_HI in Y1i. pose proof (ablk_disj_band _ _ Y1) as Y1b. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in Y1b.
  destruct HC as [H|[H|[(A & n0 & Hin & Hr)|[(F & kk & Hin & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. (lia_on Ha H Y1i).
  - destruct (RB A n0 Hin); lia.
  - (nelimp (frame_range st WF F kk Hin) 4%nat; intros Hk X Y AL). cbn [st_fs st] in X, Y. unfold FS_FRAMES_OFF in *.
    destruct Hr as [Hr|Hr]; [(lia_on Ha Hr RF Y1i X Y AL)|].
    (nelimp (fs_range st WF) 3%nat; intros F1 F2 _). cbn [st_fs st] in F1, F2. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, FS_TOTAL in *.
    assert (FZ : 0 < fsz kk) by (destruct Hk as [-> | ->]; cbn; (lia_on Hr)).
    pose proof (rt_SH_bounds F ltac:(blia)) as B0. pose proof (rt_SH_bounds (F + fsz kk) ltac:((cut_on [X Y F1 FZ] blia))) as B. rewrite (rt_SH_aligned_add F (fsz kk) AL) in B. blia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. (lia_on Ha H Y1b).
Qed.

Lemma static_not_client : forall a, 0x17c148 <= a < 0x5cc168 -> ~ cj_client_addr a1 a23 a17 SP a.
Proof.
  intros a Ha HC. (nelimp LO 3%nat; intros L1 L2 L3). unfold CEIL in L1.
  destruct HC as [H|[H|[(A & n0 & Hin & Hr)|[(F & kk & Hin & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. destruct H as [H|[H|(H1 & H2 & H3)]]; [lia| lia|].
    apply H2. exists 0xa6c18, 0x5cc8d0. split; [cbn; right; left; reflexivity| lia].
  - pose proof (ablk_img _ _ (blk_band st WF A n0 Hin)) as BI. unfold KHIGHMEM_BEG, AIMG_HI in *. lia.
  - (nelimp (frame_range st WF F kk Hin) 4%nat; intros Hk X Y AL). cbn [st_fs st] in X, Y. (nelimp (fs_range st WF) 3%nat; intros F1 F2 _). cbn [st_fs st] in F1, F2.
    pose proof (ablk_img _ _ F1) as F1i.
    unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI, CEIL, FS_TOTAL in *. destruct Hr as [Hr|Hr]; [lia|].
    assert (FZ : 0 < fsz kk) by (destruct Hk as [-> | ->]; cbn; (lia_on Hr X AL F1i)).
    pose proof (rt_SH_bounds F ltac:(lia)) as B0. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. lia.
Qed.

Theorem cli_pres_final : cli_pres st SP m m'.
Proof.
  unfold cli_pres, cj_pres. cbn [st_sp0 st_lb st_lf st]. intros a Ha HC. split; [| apply WM].
  apply MU. rewrite wa_unsigned by lia. apply outside_intro. intros iv Hiv Hin. (nelimp LO 3%nat; intros L1 L2 L3). unfold CEIL in L1.
  destruct (WTOT_cover iv Hiv) as [->|[X|[(bb & Hb & X1 & X2)|(bb & Hb & X1 & X2)]]]; cbn [fst snd] in *.
  - destruct HC as [H|[H|[(A & n0 & Hin' & Hr)|[(F & kk & Hin' & Hr)|H]]]].
    + lia.
    + unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. (lia_on H Hin L1).
    + (nelimp (block_geom st WF A n0 ltac:(unfold all_blocks; apply in_or_app; left; exact Hin')) 7%nat; intros _ _ _ G3 G4 G5 _). unfold usz in G4. lia.
    + (nelimp (frame_range st WF F kk Hin') 4%nat; intros Hk X Y AL). cbn [st_fs st] in X, Y. (nelimp (fs_range st WF) 3%nat; intros F1 F2 _). cbn [st_fs st] in F1, F2.
      unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI, CEIL, FS_TOTAL in *. destruct Hr as [Hr|Hr]; [lia|].
      assert (FZ : 0 < fsz kk) by (destruct Hk as [-> | ->]; cbn; (lia_on Hr)).
      pose proof (rt_SH_bounds (F + fsz kk) ltac:(blia)) as B. rewrite (rt_SH_aligned_add F (fsz kk) AL) in B. lia.
    + unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. lia.
  - exact (static_not_client a ltac:(lia) HC).
  - exact (nblock'_not_client bb a Hb ltac:(lia) HC).
  - exact (sblock'_not_client bb a Hb ltac:(lia) HC).
Qed.

Lemma same_but_depot_final : same_but_depot st st'.
Proof. unfold same_but_depot. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.
Lemma trs_put_final : trs_put tr (st_trs st) (st_trs st').
Proof. cbn [st_trs st st']. exact (trs_put_ins a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 WF tr h b v eq_refl eq_refl eq_refl NOTFOUND). Qed.

Theorem post_final :
  RTS st' m' mo' (mkG G' R') /\ cli_pres st SP m m' /\ rt_frame (depot_fp st') lo SP m m' /\ gmono (mkG G R) (mkG G' R')
  /\ budget_ok st (mkG G R) st' (mkG G' R') 0 /\ same_but_depot st st' /\ trs_put tr (st_trs st) (st_trs st').
Proof.
  split; [apply RTS_intro; [exact RTREP_final| exact RTWF_final| exact RTMODEL_final| exact GWIN_final| cbn [g_res]; exact FRONTR_final
                          | apply (SWIN_st st st'); [eapply SWIN_mono; [exact HSW| exact (proj2 R_final)]| reflexivity]]|].
  split; [exact cli_pres_final|]. split; [exact rt_frame_final|]. split; [exact (proj2 R_final)|].
  split; [exact budget_final|]. split; [exact same_but_depot_final| exact trs_put_final].
Qed.
End FINAL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HITF.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (c1 c2 c3 : list (Z * Z)) (c4 : list qbatch) (c5 : list (qbatch * Z)).
Let st  := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5.
Variables (m m' : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (SP lo : Z) (tr : list Z) (id : Z).
Let st' := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 (trs_hit a13 tr) a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5.
Hypothesis HR : RTREP st m.
Hypothesis WF : RTWF st.
Hypothesis HM : RTMODEL st mo.
Hypothesis HG : GWIN st m mo (mkG G R).
Hypothesis HFR : FRONTR mo R.
Hypothesis HSW : SWIN st (mkG G R).   (* [comment removed for export] *)
Hypothesis HOK : LOK asegs mo.
Hypothesis TRL : 1 <= zlen tr <= TRACE_MAX_LEN.
Hypothesis ROOM : trs_room tr a13.
Hypothesis LO : CEIL <= lo /\ lo <= SP /\ SP <= 2^64.
Hypothesis HID : 1 <= id <= d_U a12 /\ dn_hash (dnode a12 id) = trace_hash tr.
Hypothesis MU : munch [(lo, SP)] m m'.
Hypothesis WM : wmono asegs m m'.

Theorem post_hit :
  RTS st' m' mo (mkG G R) /\ cli_pres st SP m m' /\ rt_frame (depot_fp st') lo SP m m' /\ gmono (mkG G R) (mkG G R)
  /\ budget_ok st (mkG G R) st' (mkG G R) 0 /\ same_but_depot st st' /\ trs_put tr (st_trs st) (st_trs st').
Proof.
  destruct HID as [HID1 HID2]. (nelimp LO 3%nat; intros L1 L2 L3).
  assert (HR' : RTREP st m').
  { eapply (RTREP_stack_frame st WF [(lo, SP)]); [constructor; [cbn; exact L1| constructor]| exact MU| exact WM| exact HR]. }
  assert (WD' : wf_depot st').
  { exact (wf_depot_hit a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 WF tr (trace_hash tr) eq_refl ROOM id HID1 HID2). }
  assert (NR : forall bb : Z, In bb [] -> ablk bb (bb + NODEBLOCK_SIZE) /\ bb + NODEBLOCK_SIZE <= CEIL /\ bb mod 4096 = 0 /\ (forall r, In r (rt_ranges st) -> bb + NODEBLOCK_SIZE <= fst r \/ snd r <= bb)) by (intros bb []).
  assert (SR : forall bb : Z, In bb [] -> ablk bb (bb + STOREBLOCK_SIZE) /\ bb + STOREBLOCK_SIZE <= CEIL /\ bb mod 4096 = 0 /\ (forall r, In r (rt_ranges st) -> bb + STOREBLOCK_SIZE <= fst r \/ snd r <= bb)) by (intros bb []).
  split.
  { apply RTS_intro.
    - apply RTREP_of_nd; [| exact (rr_depot st m' HR')]. exact (RTREP_nd_set_depot st a12 (trs_hit a13 tr) m' (RTREP_to_nd st m' HR')).
    - unfold st'. eapply (RTWF_dep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 a12 (trs_hit a13 tr) [] [] WF WD');
        [symmetry; apply app_nil_r| symmetry; apply app_nil_r| cbn; lia| cbn; lia| exact NR| exact SR| intros bb b' [] _].
    - exact HM.
    - apply (GWIN_st st). 2:{ intros bb Hb. exact Hb. } eapply GWIN_mem; [exact HG| exact HOK| exact WM].
    - cbn [g_res]. exact HFR.
    - apply (SWIN_st st st'); [exact HSW| reflexivity]. }
  split.
  { unfold cli_pres, cj_pres. cbn [st_sp0 st_lb st_lf st]. intros a Ha HC. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. cbn. split; [| exact I].
    intros Hin. unfold CEIL in L1.
    destruct HC as [H|[H|[(A & n0 & Hin' & Hr)|[(F & kk & Hin' & Hr)|H]]]].
    - lia.
    - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. lia.
    - (nelimp (block_geom st WF A n0 ltac:(unfold all_blocks; apply in_or_app; left; exact Hin')) 7%nat; intros _ _ _ G3 G4 G5 _). unfold usz in G4. lia.
    - (nelimp (frame_range st WF F kk Hin') 4%nat; intros Hk X Y AL). cbn [st_fs st] in X, Y. (nelimp (fs_range st WF) 3%nat; intros F1 F2 _). cbn [st_fs st] in F1, F2.
      unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI, CEIL, FS_TOTAL in *. destruct Hr as [Hr|Hr]; [lia|].
      assert (FZ : 0 < fsz kk) by (destruct Hk as [-> | ->]; cbn; lia).
      pose proof (rt_SH_bounds (F + fsz kk) ltac:(blia)) as B. rewrite (rt_SH_aligned_add F (fsz kk) AL) in B. lia.
    - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. lia. }
  split. { intros a Ha HS HN. apply MU. rewrite wa_unsigned by lia. cbn. split; [exact HS| exact I]. }
  split. { intros w Hw. exact Hw. }
  split. { unfold budget_ok. cbn [g_res]. unfold st'.
           rewrite (rt_prov_dep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 a12 (trs_hit a13 tr) [] []); [| cbn; lia| cbn; lia].
           rewrite (prov_depot_dep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 c1 c2 c3 c4 c5 a12 (trs_hit a13 tr) [] []);
             [| symmetry; apply app_nil_r| symmetry; apply app_nil_r| cbn; lia| cbn; lia]. unfold zlen. cbn [length Z.of_nat]. fold st.
           unfold NODEBLOCK_SIZE, STOREBLOCK_SIZE. lia. }
  split. { unfold same_but_depot. cbn. repeat (split; [reflexivity|]). reflexivity. }
  cbn [st_trs st st']. apply trs_put_hit.
Qed.
End HITF.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma prov_depot_big : forall st, RTWF st -> NODEBLOCK_SIZE + STOREBLOCK_SIZE <= rt_prov st.
Proof.
  intros st WF. unfold rt_prov.
  pose proof (prov_classes_nonneg st).
  assert (0 <= prov_nb st) by (unfold prov_nb; destruct (st_qthread st); unfold NB; lia).
  pose proof (prov_q_nonneg st (qc_bytes_nonneg _)).
  assert (0 <= prov_ptr st) by (unfold prov_ptr; lia).
  assert (0 <= prov_live st).
  { apply prov_live_nonneg. apply Forall_forall. intros b Hb.
    destruct (wk_block st (wf_blocks_ok st WF) b ltac:(unfold all_blocks; apply in_or_app; left; exact Hb)) as [Hn _]. lia. }
  pose proof (prov_quar_nonneg st).
  assert (NODEBLOCK_SIZE + STOREBLOCK_SIZE <= prov_depot st).
  { unfold prov_depot. pose proof (wf_depot_ok st WF) as WD.
    pose proof (wd_nnb st WD) as NN. pose proof (wd_nsb st WD) as NS. pose proof (wd_U_le st WD) as UL. pose proof (wd_trs0 st WD) as T0.
    pose proof (wd_trs_max st WD) as TM. pose proof (wd_T_le st WD) as TL. pose proof (wd_nsb_max st WD) as NSM. pose proof (wd_T_pos st WD). pose proof (wd_U_pos st WD).
    unfold DEPOT_KMAX, DEPOT_L2_NODES, SSTORE_BLOCK_FRAMES, DEPOT_NNB_MAX, DEPOT_NSB_MAX, NODEBLOCK_SIZE, STOREBLOCK_SIZE in *.
    rewrite NN, NS. rewrite NS in TL, NSM. Z.div_mod_to_equations. nia. }
  pose proof (prov_slots_nonneg st).   (* [comment removed for export] *)
  pose proof (prov_l24_nonneg st).     (* [comment removed for export] *)
  pose proof (prov_emb_nonneg st).     (* [comment removed for export] *)
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem depot_put_proof' : depot_put_spec'.
Proof.
  unfold depot_put_spec'.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo g st P tr lo.
  intros HRTS A0 A1 TRL TRR TRC PSEP PCEIL PHI TP ROOM PROV ST HCEIL LO MI.
  destruct g as [G R]. cbn [g_res g_win] in *.
  destruct st as [a1_ a2_ a3_ a4_ a5_ a6_ a7_ a8_ a9_ a10_ a11_ dd trs trs0 a15_ a16_ a17_ a18_ a19_ a20_ a21_ a22_ a23_ c1_ c2_ c3_ c4_ c5_].
  set (st := mkRT a1_ a2_ a3_ a4_ a5_ a6_ a7_ a8_ a9_ a10_ a11_ dd trs trs0 a15_ a16_ a17_ a18_ a19_ a20_ a21_ a22_ a23_ c1_ c2_ c3_ c4_ c5_) in *.
  (nelim HRTS 6%nat; intros HR WF HM HG HFR HSW). cbn [st_trs] in ROOM.
  subst a0 a1 tp. cbv delta [wz]. unfold ADEPOT_PUT, ADEPOT_STACK, TRACE_MAX_LEN in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  (* [comment removed for export] *)
  pose proof (entry_ss st m HR WF) as [SSR SSW]. (nelimp (entry_nb st m HR WF) 3%nat; intros NBL NBR0 NVIS).
  pose proof (wf_depot_ok st WF) as WD.
  set (h := trace_hash tr). set (b := dbucket h). set (v := d_tab dd b). set (U := d_U dd).
  assert (HH : 0 <= h < 2^64) by (apply trace_hash_range).
  assert (HB : 0 <= b < 2^20) by (unfold b, dbucket, DEPOT_TAB_LOG; apply Z.mod_pos_bound; lia).
  assert (HV : v = 0 \/ 1 <= v <= U) by (unfold v, U; apply (wd_tab st WD); unfold DEPOT_TAB_LOG; exact HB).
  assert (HU : 1 <= U /\ U <= 2^20 + 1 /\ zlen trs <= 2^20).
  { pose proof (wd_U_pos st WD). pose proof (wd_U_le st WD). pose proof (wd_trs0 st WD). pose proof (wd_trs_max st WD). cbn [st_depot st_trs st_trs0 st] in *. unfold U, DEPOT_KMAX in *. lia. }
  change (cells_at asegs m P (trace_cells tr)) with (ro_cells asegs m P (trace_cells tr)) in TRC.
  apply lscps_assume. intros NWX HOK HBINV.
  apply lscps_step_evt.
  do 8 lstep.
  eapply put_A; [exact MI| exact TRR| lia| lia| exact TRC| lia| exact ST| lia|].
  intros x10 x11 x12 x14 x15 x16 m1 junk FR1 MI1 MU1 WM1 ST1.
  assert (HR1 : RTREP st m1).
  { eapply (RTREP_stack_frame st WF [(bv_unsigned sp - 112, bv_unsigned sp)]); [constructor; [cbn; unfold RT_artF.CEIL; lia| constructor]| exact MU1| exact WM1| exact HR]. }
  eapply find_entry with (m := m1) (st := st) (h := h) (b := b) (p := A_DEPOT + 4 * b); [exact HR1| exact WF| reflexivity| reflexivity|].
  intros y10 y12.
  eapply find_loop with (m := m1) (st := st) (h := h) (n := Z.to_nat v) (s := v); [exact HR1| exact WF| exact HH| reflexivity| exact HV| |].
  - (* [comment removed for export] *)
    intros s' z11 z12 Hs' L E.
    do 11 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR1 ST1 (bv_unsigned sp).
    apply evt_done. apply lscps_done.
    lazymatch goal with |- depot_put_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mf _) _ _ =>
    (nelim (post_hit a1_ a2_ a3_ a4_ a5_ a6_ a7_ a8_ a9_ a10_ a11_ dd trs trs0 a15_ a16_ a17_ a18_ a19_ a20_ a21_ a22_ a23_ c1_ c2_ c3_ c4_ c5_ m mf mo G R (bv_unsigned sp) lo tr s' HR WF HM HG HFR HSW HOK ROOM ltac:(unfold RT_artF.CEIL; lia) (conj Hs' E) ltac:(eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn; intros; lia) WM1) 7%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7)

 end.
    unfold depot_put_post, rt_post_std. nexists 17%nat. split; [reflexivity|]. split; [exact MI1|].
    exists s'. split; [reflexivity|]. split; [clear - Hs' HU; cbn [st_depot st] in Hs'; unfold U in HU; lia|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q1|]. split; [exact ST1|].
    split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4| exact Q5].
  - (* [comment removed for export] *)
    intros NF y10' y12'. apply evt_done.
    pose proof (mmap_cells st m1 HR1) as HC1. pose proof (cf240_cell st m1 HR1) as CF1.
    (nelimp (rr_depot st m1 HR1) 8%nat; intros TAB NIDSx MAP1s _ _ _ _ _). cbn [st_depot st] in TAB, NIDSx, MAP1s.
    destruct NIDSx as (nj & NIDS1). cbv delta [wz zb] in TAB, NIDS1, MAP1s. unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, DEPOT_TAB_LOG in TAB, NIDS1, MAP1s.
    pose proof (entry_ss st m1 HR1 WF) as [SSR1 SSW1]. (nelimp (entry_nb st m1 HR1 WF) 3%nat; intros NBL1 NBR1 NVIS1). cbn [st_depot st] in SSR1, SSW1, NBL1, NBR1, NVIS1.
    cbn [st_depot st] in NF.
    assert (TF : 1 <= d_T dd /\ d_T dd + 64 < 2^31 /\ zlen (d_sblocks dd) <= 32).
    { pose proof (wd_T_pos st WD). pose proof (wd_T_le st WD) as L. pose proof (wd_nsb st WD) as NS. pose proof (wd_nsb_max st WD). pose proof (wd_trs_max st WD).
      cbn [st_depot st_trs st] in *. unfold d_nsb, DEPOT_NSB_MAX, DEPOT_KMAX, SSTORE_BLOCK_FRAMES in *. rewrite NS in L. split; [lia|]. split; Z.div_mod_to_equations; nia. }
    assert (KR : 0 <= (U + 1) / 65536 < 2^15) by (Z.div_mod_to_equations; nia).
    pose proof (prov_depot_big st WF) as BIG. unfold NODEBLOCK_SIZE, STOREBLOCK_SIZE in BIG.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (rewrite unsigned_lit by lia; reflexivity).
    assert (F1M : forall a1 : word, mmap_grant mo a1 1048576 ->
                  FRONTR (mm_add_map a1 (Z_to_bv 64 1048576) mo) (R - 1048576) /\ 0x5ff000 <= bv_unsigned a1 /\ LOK asegs (mm_add_map a1 (Z_to_bv 64 1048576) mo)).
    { intros a1 GR. pose proof (FRONTR_grant mo R a1 1048576 HFR ltac:(unfold FR_MINGRANT; lia) ltac:(reflexivity) ltac:(lia)) as F1.
      pose proof (ablk_img _ _ (grant_ablk_b mo a1 1048576 HOK (shband_of_model st mo HM) ltac:(lia) GR)) as F2. unfold KHIGHMEM_BEG, AIMG_HI in F2.
      split; [exact F1|]. split; [lia|]. (nelim GR 4%nat; intros _ _ GC GF). apply mm_add_map_LOK; [exact HOK| rewrite unsigned_lit by lia; exact GC|].
      rewrite region_free_app in GF. apply andb_true_iff in GF as [_ GF]. exact GF. }
    eapply put_insert_spec with (T := d_T dd) (n := zlen tr) (P := P) (p := A_DEPOT + 4 * b) (v := v) (h := h) (U := U) (k := (U + 1) / 65536) (lo := lo)
                                (sbl := d_sblocks dd) (nbl := d_nblocks dd) (tr := tr) (nj := nj) (mo := mo) (R := R).
    all: lazymatch goal with
         | |- mmap_consts _ => exact HC1
         | |- ro_cells _ _ 0x13be98 _ => exact CF1
         | |- mem_inv _ _ => exact MI1
         | |- stk _ _ _ _ => rewrite ESP; exact ST1
         | |- ssrep _ _ _ => exact SSR1
         | |- sswf _ _ => exact SSW1
         | |- ro_cells _ _ _ (trace_cells _) => eapply ro_cells_transport; [exact TRC| exact MU1| rewrite trace_cells_size; cbn; lia]
         | |- rw_cells _ _ (bv_unsigned _) _ => rewrite ESP; exact FR1
         | |- rw_cells _ _ (A_DEPOT + 4 * _) _ => unfold A_DEPOT; apply TAB; lia
         | |- rw_cells _ _ 5816664 _ => exact NIDS1
         | |- rw_cells _ _ (5816680 + _) _ => apply MAP1s; lia
         | |- mmap_placeable _ 1048576 => apply (FRONTR_placeable mo R); [exact HOK| exact HFR| lia| unfold FR_NMAX; lia]
         | |- _ => idtac
         end.
    { rewrite ESP. lia. }
    { lia. } { lia. } { lia. }
    { rewrite ESP. lia. }
    { change (cells_at asegs m1 P (trace_cells tr)) with (ro_cells asegs m1 P (trace_cells tr)). eapply ro_cells_transport; [exact TRC| exact MU1| rewrite trace_cells_size; cbn; lia]. }
    { unfold A_DEPOT. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
    { lia. } { lia. } { reflexivity. }
    { split; [exact NBL1| exact NBR1]. }
    { exact NVIS1. }
    { exact (entry_nbsb st WF). }
    { exact (entry_nbm st mo WF HM). }
    { exact (entry_sbm st mo WF HM). }
    { intros a GR. exact (proj1 (proj2 (F1M a GR))). }
    { intros mo1 a HMO GR. destruct HMO as [->|(a1 & G1 & ->)].
      - pose proof (ablk_img _ _ (grant_ablk_b mo a 8388608 HOK (shband_of_model st mo HM) ltac:(lia) GR)) as X. unfold AIMG_HI in X. lia.
      - (nelim (F1M a1 G1) 3%nat; intros _ _ L1).
        pose proof (ablk_img _ _ (grant_ablk_b _ a 8388608 L1 (shband_add_map mo a1 _ (shband_of_model st mo HM)) ltac:(lia) GR)) as X. unfold AIMG_HI in X. lia. }
    { lia. }
    { intros mo1 HMO. destruct HMO as [->|(a1 & G1 & ->)].
      - apply (FRONTR_placeable mo R); [exact HOK| exact HFR| lia| unfold FR_NMAX; lia].
      - (nelim (F1M a1 G1) 3%nat; intros F1 _ L1). apply (FRONTR_placeable _ (R - 1048576)); [exact L1| exact F1| lia| unfold FR_NMAX; lia]. }
    (* [comment removed for export] *)
    intros nbl' nb1 mo1 R1 start sbl' nb2 m' mo' G' R' lj x5 x6 x7 x11' x12' x13 x14' x15' x16' x17 x28 x29 x30 x31.
    intros HNB1 HS1 HS2 SSR' SSW' HBF HALT NVIS' NODE' TAB' NIDS' MAP1' MI' MUp WMp STp.
    rewrite ESP in MUp, STp |- *.
    replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) in MUp, STp |- * by lia.
    rewrite (Z_to_bv_bv_unsigned sp).
    assert (MUtot : munch (WTOT dd (bv_unsigned sp) lo tr start nbl' sbl' nb1 nb2) m m').
    { eapply munch_trans; [| exact MUp]. eapply munch_weaken; [| exact MU1]. unfold sub_fp, WTOT. intros x Hx. cbn [outside] in Hx |- *. split; [(lia_on HCEIL LO HU TF Hx)| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM1 WMp) as WMtot.
    unshelve epose proof (post_final a1_ a2_ a3_ a4_ a5_ a6_ a7_ a8_ a9_ a10_ a11_ dd trs trs0 a15_ a16_ a17_ a18_ a19_ a20_ a21_ a22_ a23_ c1_ c2_ c3_ c4_ c5_
                            m m' mo mo1 mo' G G' R R1 R' (bv_unsigned sp) lo tr start nbl' sbl' nb1 nb2
                            HR WF HM HG HFR HSW HOK ltac:(exact TRL) ROOM _ _ NF HNB1 HS1 HS2 SSR' SSW' HBF HALT NVIS' NODE' TAB' NIDS' MAP1' MUtot WMtot)
      as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7); [unfold RT_artF.CEIL; lia| lia|].
    apply lscps_done. unfold depot_put_post, rt_post_std. nexists 17%nat. split; [reflexivity|]. split; [exact MI'|].
    exists (U + 1). split; [reflexivity|]. split; [lia|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q1|]. split; [exact STp|].
    split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4| exact Q5].
Qed.


End CeilWrap.
