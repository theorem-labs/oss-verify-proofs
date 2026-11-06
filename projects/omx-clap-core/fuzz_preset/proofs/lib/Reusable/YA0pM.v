(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane, the B2 walk prover, for
   another Theorem Labs lane: the CODE WALK of knock's FIRST StackDepotPut (StackDepotPut 0x70ef0, which tail-jumps to
   StackDepotBase<StackDepotNode,1,20>::Put 0x70f10; fuzz_knock.asan sha256 61768cf4739b...) around its two first-use
   callees, as segment lemmas in continuation-passing form. lib/A/AD3j.v (the statement tfib_depot_first_put_spec)
   composes K1-K3 with S7 (lib/A/AD3g.v tfib_tlm_create_nb_ok, TwoLevelMap::Create 0x71714) and S1 (lib/A/AD3a.v
   tfib_store_ok, StackStore::Store 0x6e8f4):
     K1 put_to_create        0x70ef0 -> 0x71714 (Create's entry; ra 0x71190)
     K2 create_ret_to_store  0x71190 -> 0x6e8f4 (Store's entry, inside StackDepotNode::store 0x70c08; ra 0x70c34)
     K3 store_ret_to_exit    0x70c34 -> Put's return to its caller
   and K0 put_size0 is the size-0 early return (0x70ef0 -> Put's return, a0 = 0).
   Each lemma: for any postcondition Q, if Q's run holds from every state that meets the boundary facts at the end PC,
   it holds from the start PC. The boundary facts of K1-K3 are the named Definitions at_create_call, at_store_call,
   put_exit. K1 reads the hash constants at 0x102d8 / 0x102f8 / 0x10388 through as_const (AD3j's premise).

   THE CODE (A image; DP = as_depot B = 0x180418, SS = as_store B = 0x170408; disassembly of the packed base's
   Asan_seg_001.hex, (internal path))
     0x70ef0 StackDepotPut: a2 := a1 (n); a1 := DP; a3 := a0 (buf); a0 := DP; a1 := buf; a3 := 0; j Put.
     0x70f10 Put: frame 0x70 at P = sp - 112: ra, s0-s9 at P + 0x68 .. P + 0x18; s0 := 0; s1 := DP; buf at P + 8, n at
       P + 16; n = 0 or buf = 0 -> return 0 (not taken: tr <> []).
     0x70f68-0x71000 the hash loop over the n trace words (constants DH_M / DH_M8 / DH_SEED from 0x102d8 / 0x102f8 /
       0x10388): s3 := h = tfib_dhash tr; s6 := 0xffff; s7 := 0x7fffffff.
     0x71004 s2 := DP + 4 * (h mod 2^20); lw tab[b1] = 0; s8 := DP + 0x400010 (map1_); s9 := 0; s4 := DP + 0x400008
       (mu_ = DP + tlm_mu); beqz -> 0x71088.
     0x7108c jal lock 0x71684 (frame 48 at P - 48): lr.w / sc.w tab[b1] := 0x80000000; returns the old word 0.
     0x71090 s5 := 0; beq 0, s9 -> 0x710c0: amoadd.w n_uniq_ids (DP + d_nuniq) 0 -> 1; s1 := 1; s7 := 1; a1 := 1 >> 16 = 0;
       ld map1_[0] = 0 -> 0x71188: a0 := s4; jal Create 0x71714 (ra 0x71190).                                   [K1]
     0x71190 j 0x710f8: s1 := x + 16 (x = Create's result, node 1); a2 := P + 8; a0 := s1; a1 := 0; a3 := h;
       jal StackDepotNode::store 0x70c08 (ra 0x71118): frame 32 at N = P - 32 (ra at N + 0x18, s0 at N + 0x10);
       s0 := x + 16; node.hash := h (sd at x + 16); pack := 0 at N + 8; a0 := SS; a1 := P + 8; a2 := N + 8;
       jal Store 0x6e8f4 (ra 0x70c34).                                                                        [K2]
     0x70c34 ld pack (0); node.store_id := a0 (sw at x + 28); pack = 0 -> restore ra, s0; ret to 0x71118:
       node.link := s5 = 0 (sw at x + 24); fence; a0 := 1; tab[b1] := 1 (the unlock); s0 = 0 -> restore ra, s0-s9;
       ret (a0 = 1).                                                                                           [K3]
   Stack below Put's entry sp: Put 112, the lock 48 more (160); the callees' bands are S7's and S1's.

   The walk uses the symbolic runner of AFem.v (the mapped-case Put) with first-use seeds: AFem's Section s lemmas
   assume layout_ok and AFek's sstates carry DF_fixed (NB, SB >= 4096, n_uniq_ids >= 1), false at the first Put, so
   the seeds, the loop state and the frame invariant are rebuilt here; AFem's hash_loop is ported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/AD3k.v, with its module paths changed; 178 of its 205 lines of code are new or changed and 846 lines of the source are left out. *)
(* The runners a secondary recycle walk calls (SRr_run_sh_gen,
   SRr_run_to_sh_gen, SRr_ret_at and the tactics srr_run_sh / srr_run_to_sh), each twinned so the continuation keeps
   the materialized-page fact instead of `forall mat'`:
   - run_postM adds mat_in_win E (ss_mem ss) model model': every page materialized after the run was materialized
     before it or is the page of an address in the run's read window (the first symbolic memory's region extents,
     YP09R.in_rrange);
   - SRr_ret_atM: a jalr x0 touches no memory, so the model after the return is the model before it.
   The window is from the per-step soundness with windows (YP0kR / YP0iR), the chain from YA0nM.SRr_mstepsM. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK18 YK0j YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0x YP09R YA0nM YP0kM YP0iM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

(* Every page materialized in md' was materialized in md or is the page of an address in the read window. *)
Definition mat_in_win (E : env) (rs : smem) (md md' : Model) : Prop :=
  forall p, In p (m_vm_materialized md') ->
    In p (m_vm_materialized md) \/ exists a, in_rrange E rs a /\ p = page_base_of a.

Lemma mat_in_win_of : forall E rs md md' accs,
  mat_in md md' accs -> accs_in_rrange E rs accs -> mat_in_win E rs md md'.
Proof.
  intros E rs md md' accs HM HW p Hp. destruct (HM p Hp) as [H | (a & n & k & Hin & Hk & ->)]; [left; exact H | right].
  exists (bv_unsigned a + Z.of_nat k). split; [exact (HW a n k Hin Hk) | reflexivity].
Qed.

Lemma mat_in_win_refl : forall E rs md, mat_in_win E rs md md.
Proof. intros E rs md p Hp. left. exact Hp. Qed.

(* The bridge to a page-allowance base B (review 05:5xZ check 6): the page of an address that lies in a page-aligned
   extent of B is allowed by B. Page alignment is needed (page_allowedb asks the whole page inside one extent), and
   a < 2^64 because page_base_of wraps. *)
Lemma page_allowedb_of_extent : forall B lo hi a,
  In (lo, hi) B -> lo mod page_size = 0 -> hi mod page_size = 0 -> lo <= a < hi -> 0 <= a < 2 ^ 64 ->
  page_allowedb B (page_base_of a) = true.
Proof.
  intros B lo hi a Hin Hlo Hhi Ha Ha64. unfold page_allowedb. apply existsb_exists. exists (lo, hi).
  split; [exact Hin|]. cbn [fst snd].
  assert (U : bv_unsigned (page_base_of a) = a / page_size * page_size).
  { unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64).
    unfold page_size in *. pose proof (Z.div_mod a 4096 ltac:(lia)). pose proof (Z.mod_pos_bound a 4096 ltac:(lia)). lia. }
  rewrite U. unfold page_size in *.
  pose proof (Z.div_mod a 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound a 4096 ltac:(lia)) as M.
  pose proof (Z.div_mod lo 4096 ltac:(lia)) as Dl. pose proof (Z.div_mod hi 4096 ltac:(lia)) as Dh.
  rewrite Hlo in Dl. rewrite Hhi in Dh.
  assert (L1 : lo / 4096 <= a / 4096) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 4096 < hi / 4096) by (apply Z.div_lt_upper_bound; lia).
  apply andb_true_iff. split; apply Z.leb_le; nia.
Qed.

(* mat_in_win into a base B: when every window address lies in a page-aligned extent of B, every page materialized
   by the run was materialized before or is allowed by B (the first clause of YGcfLazyResid.step_mat_in_cf with P = []). *)
Lemma mat_in_win_base : forall E rs md md' B,
  (forall a, in_rrange E rs a -> 0 <= a < 2 ^ 64 /\
     exists lo hi, In (lo, hi) B /\ lo mod page_size = 0 /\ hi mod page_size = 0 /\ lo <= a < hi) ->
  mat_in_win E rs md md' ->
  forall p, In p (m_vm_materialized md') -> In p (m_vm_materialized md) \/ page_allowedb B p = true.
Proof.
  intros E rs md md' B HB HW p Hp. destruct (HW p Hp) as [H | (a & Ha & ->)]; [left; exact H | right].
  destruct (HB a Ha) as (Ha64 & lo & hi & Hin & Hlo & Hhi & Hr).
  exact (page_allowedb_of_extent B lo hi a Hin Hlo Hhi Hr Ha64).
Qed.

(* A jalr reports no memory access. *)
Lemma step_accesses_jalr_nil {fx : FPState} : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  exists ms', step_accesses segs (mkst regs pc mem rom) = MachineOk (@mkAccessReport _ ms' []).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst]. rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota. rewrite Hdecode.
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1 Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst].
  rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota; destruct (is_x0 rd); cbv beta iota; eexists; reflexivity.
Qed.

Section d.
Variable segs : list Segment.
Context {fx : FPState}.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.

Definition run_postM (W : world segs) (E : env) (ss ss' : sstate) (st : run_status)
    (ms : machine_state) (model : Model) (Q : world segs -> config -> Prop) : Prop :=
  forall ms' mat',
    match st with RS_ecall => st_ok_ecall segs E ss' (restrict (w_H W) ms')
    | _ => st_ok segs E ss' (restrict (w_H W) ms') end ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mat_in_win E (ss_mem ss) model (with_vm_backing (m_vm_lazy model) mat' model) ->
    SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q.

Lemma SRr_of_restricted_chainM : forall W E ss ss' st ms msr' accs model Q,
  msteps_acc segs (restrict (w_H W) ms) msr' accs ->
  match st with RS_ecall => st_ok_ecall segs E ss' msr' | _ => st_ok segs E ss' msr' end ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  accs_in_rrange E (ss_mem ss) accs ->
  run_postM W E ss ss' st ms model Q ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros W E ss ss' st ms msr' accs model Q Hms HS' Hfr Hw Hk.
  apply (SRr_mstepsM segs Hwx W _ msr' accs Hms ms model Q eq_refl).
  intros model' Hsame Hcl Hmi.
  pose proof (mat_in_win_of E (ss_mem ss) model model' accs Hmi Hw) as MW.
  rewrite (same_but_materialized_wvb model model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
  - rewrite Hrr. exact HS'.
  - cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
  - change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
      with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
    rewrite Hrr. exact Hfr.
  - intros p Hp. rewrite m_vm_materialized_wvb in Hp. exact (MW p Hp).
Qed.

Lemma SRr_run_sh_genM : forall W n E ss ss' st ms model Q,
  st_ok segs E ss (restrict (w_H W) ms) ->
  sym_runN_sh segs tbl n ss = (ss', st) ->
  run_postM W E ss ss' st ms model Q ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros W n E ss ss' st ms model Q HS Hrun Hk.
  destruct (msteps_run_shM segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & accs & Hms & HS' & Hfr & Hw).
  exact (SRr_of_restricted_chainM W E ss ss' st ms msr' accs model Q Hms HS' Hfr Hw Hk).
Qed.

Lemma SRr_run_to_sh_genM : forall W n stop E ss ss' st ms model Q,
  st_ok segs E ss (restrict (w_H W) ms) ->
  sym_run_toN_sh segs tbl n stop ss = (ss', st) ->
  run_postM W E ss ss' st ms model Q ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros W n stop E ss ss' st ms model Q HS Hrun Hk.
  destruct (msteps_run_to_shM segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & accs & Hms & HS' & Hfr & Hw).
  exact (SRr_of_restricted_chainM W E ss ss' st ms msr' accs model Q Hms HS' Hfr Hw Hk).
Qed.

(* SRr_ret_at with the model kept: the return's continuation sees md itself, not any same_but_materialized md'. *)
Lemma SRr_ret_atM : forall W E ss ms md Q,
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  clookup tbl (ss_pc ss) = Some RET_WORD_r ->
  Q W (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom segs)) md) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
  intros W E ss ms md Q HS Hrv Hpc HQ.
  pose proof (st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hshape.
  assert (HF : fetch_word segs (Z_to_bv 64 (ss_pc ss)) = Some (0x00008067%bv : bv 32)).
  { rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply tbl_ok. exact Hpc. }
  eapply (SRr_stepM segs Hwx W); [reflexivity | |].
  - rewrite restrict_mkst_fx. change 0 with (bv_signed (0%bv : bv 12)).
    eapply (step_jalr_x0 segs _ _ _ _ (0x00008067%bv : bv 32) 1 (0%bv : bv 12)); [exact HF | reflexivity | exact decode_ret_r | reflexivity].
  - intros model' Hsame Hcl Hmat.
    rewrite restrict_mkst_fx in Hmat.
    destruct (step_accesses_jalr_nil segs (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (mrestrict (w_H W) (ms_mem ms))
                (seg_rom segs) (0x00008067%bv : bv 32) 0 1 (0%bv : bv 12) HF eq_refl decode_ret_r) as (msj & Hj).
    pose proof (report_step segs _ _ _ Hj) as Hsj.
    rewrite (step_jalr_x0 segs (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom segs)
               (0x00008067%bv : bv 32) 1 (0%bv : bv 12) _ HF eq_refl decode_ret_r eq_refl) in Hsj.
    injection Hsj as Hsj. rewrite <- Hsj in Hj.
    change (bv_signed (0%bv : bv 12)) with 0 in Hj.
    pose proof (Hmat [] Hj) as Hm. rewrite materialize_model_accesses_nil in Hm. injection Hm as <-.
    cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. apply SRr_ret. exact HQ.
Qed.
End d.

Ltac srr_after_runM HS :=
  let ms' := fresh "ms" in let mat' := fresh "mat" in
  let HF := fresh "HF" in let HFr := fresh "HFr" in let HMW := fresh "HMW" in
  intros ms' mat' HS HF HFr HMW;
  cbn [ms_mem mkst pend_at] in HF, HFr;
  try match type of HS with context [restrict _ ?msn] =>
    repeat match goal with
    | old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
    end
  end;
  srr_norm_model.

Ltac srr_run_shM tblok HS :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of tblok with
    | table_ok _ ?tbl =>
      let r := eval vm_compute in (sym_runN_sh segs tbl FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_sh segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
          | _ => fail "srr_run_shM: no hypothesis  wx_segs_nowrap segs" end in
        eapply (SRr_run_sh_genM segs tbl tblok HWX W FUEL E ss ss' st ms _ _ HS Hrun);
        clear Hrun HS;
        try match type of ms with machine_state => clear ms | _ => idtac end;
        srr_after_runM HS
      end
    end
  | _ => fail "srr_run_shM: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
  end.

Ltac srr_run_to_shM tblok HS stop :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of tblok with
    | table_ok _ ?tbl =>
      let r := eval vm_compute in (sym_run_toN_sh segs tbl FUEL stop ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN_sh segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
        let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
          | _ => fail "srr_run_to_shM: no hypothesis  wx_segs_nowrap segs" end in
        eapply (SRr_run_to_sh_genM segs tbl tblok HWX W FUEL stop E ss ss' st ms _ _ HS Hrun);
        clear Hrun HS;
        try match type of ms with machine_state => clear ms | _ => idtac end;
        cbv beta iota;
        srr_after_runM HS
      end
    end
  | _ => fail "srr_run_to_shM: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
  end.
