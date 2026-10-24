(* SPDX-License-Identifier: MIT *)
(** Boundary cases of the fixed checksum fuzzer's actual RISC-V code.
    The continuation certificate includes both checksum initializers and
    restoration of every saved register.  This is not the full target. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YK0i YP0m YP0e YP09 YP0l YP0k YP02 YP03 YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import ZImage.
Import ListNotations.
Section Bounds.
Context {fx : FPState}.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition zbound_return : Z := 0x140ec.
Definition zbound_regs (large : bool) : list sv :=
  map (fun n => if Nat.eqb n 0 then SLit 0
    else if Nat.eqb n 1 then SLit zbound_return
    else if Nat.eqb n 11 then if large then SOff 11 0 else SLit 0
    else SOff n 0) (seq 0 32).
Definition zbound_mem : smem :=
  [mkRegion (Some 2%nat) (-112) 0 (-112) 0 []].
Definition zbound_facts (large : bool) : facts :=
  mkFacts ([(2%nat, mkAF 65536 (2^63-1) 4)] ++
    if large then [(11%nat, mkAF 1048577 (2^64-1) 0)] else []) [] [].
Definition zbound_entry (large : bool) : sstate :=
  mkSS 0x141f0 (zbound_regs large) zbound_mem None (zbound_facts large).
Definition zzero_result := Eval vm_compute in
  sym_run_toN zsegs ztbl 200 zbound_return (zbound_entry false).
Definition zlarge_result := Eval vm_compute in
  sym_run_toN zsegs ztbl 200 zbound_return (zbound_entry true).
Definition zbound_result (large : bool) := if large then zlarge_result else zzero_result.
Definition zbound_final (large : bool) := fst (zbound_result large).
Lemma zbound_run_zero : sym_run_toN zsegs ztbl 200 zbound_return (zbound_entry false)
  = (zbound_final false, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma zbound_run_large : sym_run_toN zsegs ztbl 200 zbound_return (zbound_entry true)
  = (zbound_final true, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma zbound_reaches_return : forall large,
  ss_pc (zbound_final large) = zbound_return /\
  sr_get (ss_regs (zbound_final large)) (Z_to_bv 5 10) = SLit 0 /\
  sr_get (ss_regs (zbound_final large)) (Z_to_bv 5 2) = SOff 2 0.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.
Theorem zbound_machine_certificate : forall large E ms,
  st_ok zsegs E (zbound_entry large) ms ->
  exists final, msteps zsegs ms final /\
    st_ok zsegs E (zbound_final large) final /\
    frame_of E zbound_mem (ms_mem ms) (ms_mem final).
Proof.
  intros large E ms HS. destruct large.
  - exact (msteps_run_to_gen zsegs ztbl ztbl_ok 200 zbound_return E
      (zbound_entry true) (zbound_final true) RS_running ms HS zbound_run_large).
  - exact (msteps_run_to_gen zsegs ztbl ztbl_ok 200 zbound_return E
      (zbound_entry false) (zbound_final false) RS_running ms HS zbound_run_zero).
Qed.

Lemma zdenot_offset_zero : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Definition zbound_env (regs : bvmap 5 word) : env :=
  mkEnv (fun n => getr regs (Z_to_bv 5 (Z.of_nat n))) (fun _ => []).
Lemma zbound_regs_ok : forall (large : bool) regs,
  getr regs (Z_to_bv 5 1) = Z_to_bv 64 zbound_return ->
  (if large then True else getr regs (Z_to_bv 5 11) = Z_to_bv 64 0) ->
  regs_ok (zbound_env regs) (zbound_regs large) regs.
Proof.
  intros large regs Hra Hn r.
  pose proof (u5_range r) as Hr.
  remember (Z.to_nat (bv_unsigned r)) as n eqn:Hidx.
  assert (Hlt : (n < 32)%nat) by lia.
  assert (R : r = Z_to_bv 5 (Z.of_nat n)).
  { apply bv_eq. rewrite Z_to_bv_unsigned.
    change (bv_wrap 5 (Z.of_nat n)) with (Z.of_nat n mod 32).
    rewrite Z.mod_small by lia. lia. }
  subst r.
  do 32 (destruct n as [|n]; [
    lazymatch goal with |- getr ?rr ?r = _ =>
      let v := eval vm_compute in (sr_get (zbound_regs large) r) in
      change (getr rr r = sv_denot (zbound_env rr) v)
    end;
    destruct large; cbn in Hn;
    first [exact Hra | exact Hn | reflexivity |
      rewrite zdenot_offset_zero; reflexivity] |]).
  lia.

Qed.
Lemma zbound_entry_st_ok : forall (large : bool) regs mem,
  getr regs (Z_to_bv 5 1) = Z_to_bv 64 zbound_return ->
  65536 <= bv_unsigned (getr regs (Z_to_bv 5 2)) < 2^63 ->
  bv_unsigned (getr regs (Z_to_bv 5 2)) mod 16 = 0 ->
  (if large then 1048577 <= bv_unsigned (getr regs (Z_to_bv 5 11))
   else getr regs (Z_to_bv 5 11) = Z_to_bv 64 0) ->
  (forall a, bv_unsigned (getr regs (Z_to_bv 5 2)) - 112 <= a <
      bv_unsigned (getr regs (Z_to_bv 5 2)) -> writable_at zsegs mem a) ->
  st_ok zsegs (zbound_env regs) (zbound_entry large)
    (mkst regs (Z_to_bv 64 0x141f0) mem (seg_rom zsegs)).
Proof.
  intros large regs mem Hra Hsp Hal Hn Hw.
  unfold st_ok. cbn [mkst zbound_entry ss_fregs ss_pc ss_resv ss_regs ss_mem ss_facts].
  repeat (split; [reflexivity|]).
  split.
  - apply zbound_regs_ok; [exact Hra|]. destruct large; [exact I|exact Hn].
  - split.
    + unfold mem_ok, zbound_mem. split; [reflexivity|]. split.
      * constructor; [|constructor]. unfold region_ok, base_val.
        cbn [r_base r_lo r_hi r_wlo r_whi r_chunks zbound_env ew].
        split.
        { change (0 <= bv_unsigned (getr regs (Z_to_bv 5 2)) + -112). lia. }
        split.
        { change (bv_unsigned (getr regs (Z_to_bv 5 2)) + 0 <= 2^64). lia. }
        split; [|constructor].
        intros o Ho. cbn [r_wlo r_whi] in Ho.
        change (writable_at zsegs mem (bv_unsigned (getr regs (Z_to_bv 5 2)) + o)).
        apply Hw. lia.
      * cbn [pairwise_disjoint all_disjoint]. auto.
    + unfold facts_ok, zbound_facts. cbn [f_atoms f_conds f_alias].
      split; [|split; exact I]. split.
      * change ((65536 <= bv_unsigned (getr regs (Z_to_bv 5 2)) <= 2^63-1) /\
          bv_unsigned (getr regs (Z_to_bv 5 2)) mod 16 = 0 /\ 0 <= 4 <= 64).
        split; [lia|]. split; [exact Hal|lia].
      * destruct large; [|exact I].
        change (((1048577 <= bv_unsigned (getr regs (Z_to_bv 5 11)) <= 2^64-1) /\
          bv_unsigned (getr regs (Z_to_bv 5 11)) mod 1 = 0 /\ 0 <= 0 <= 64) /\ True).
        pose proof (u64_range (getr regs (Z_to_bv 5 11))).
        repeat split; try lia; try apply Z.mod_1_r.
Qed.
Lemma zbound_saved_symbolic : forall large r,
  In r [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] ->
  sr_get (ss_regs (zbound_final large)) (Z_to_bv 5 r) =
  sr_get (zbound_regs large) (Z_to_bv 5 r).
Proof.
  intros [] r H; repeat (destruct H as [<-|H]; [vm_compute; reflexivity|]); contradiction.
Qed.
Theorem zbound_returns_normally : forall (large : bool) regs mem,
  getr regs (Z_to_bv 5 1) = Z_to_bv 64 zbound_return ->
  65536 <= bv_unsigned (getr regs (Z_to_bv 5 2)) < 2^63 ->
  bv_unsigned (getr regs (Z_to_bv 5 2)) mod 16 = 0 ->
  (if large then 1048577 <= bv_unsigned (getr regs (Z_to_bv 5 11))
   else getr regs (Z_to_bv 5 11) = Z_to_bv 64 0) ->
  (forall a, bv_unsigned (getr regs (Z_to_bv 5 2)) - 112 <= a <
      bv_unsigned (getr regs (Z_to_bv 5 2)) -> writable_at zsegs mem a) ->
  exists final,
    msteps zsegs (mkst regs (Z_to_bv 64 0x141f0) mem (seg_rom zsegs)) final /\
    ms_pc_val final = Z_to_bv 64 zbound_return /\
    getr (ms_regs final) (Z_to_bv 5 10) = Z_to_bv 64 0 /\
    (forall r, In r [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] ->
      getr (ms_regs final) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
    frame_of (zbound_env regs) zbound_mem mem (ms_mem final).
Proof.
  intros large regs mem Hra Hsp Hal Hn Hw.
  pose proof (zbound_entry_st_ok large regs mem Hra Hsp Hal Hn Hw) as HS.
  destruct (zbound_machine_certificate large (zbound_env regs) _ HS)
    as [final [Hsteps [HF Hframe]]].
  destruct (zbound_reaches_return large) as [Hpc [Ha0 Hsp0]].
  pose proof HF as (_ & HP & _ & _ & _ & _ & HR & _).
  exists final. split; [exact Hsteps|]. split.
  - rewrite HP, Hpc. reflexivity.
  - split.
    + rewrite HR, Ha0. reflexivity.
    + split; [|exact Hframe]. intros r Hin.
      rewrite HR, zbound_saved_symbolic by exact Hin.
      symmetry. apply (zbound_regs_ok large regs Hra).
      destruct large; [exact I|exact Hn].
Qed.
End Bounds.
