(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module RLF.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 head_may_be_arith (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h _ =>
        (match Constr.Unsafe.kind h with
         | Constr.Unsafe.Constant _ _ =>
             List.exist (fun r => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h r)
               [reference:(not); reference:(iff); reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt);
                reference:(lt); reference:(ge); reference:(gt); reference:(N.le); reference:(N.lt); reference:(Z.divide)]
         | Constr.Unsafe.Ind _ _ =>
             List.exist (fun r => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h r) [reference:(and); reference:(or); reference:(eq); reference:(le)]
         | _ => true
         end)
    | _ => true
    end.
  Ltac2 is_local (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
  (* [comment removed for export] *)
  Ltac2 meets_s (xs : ident list) (vs : ident FSet.t) : bool := List.exist (fun x => FSet.mem x vs) xs.
  Ltac2 add_all (s : ident FSet.t) (xs : ident list) : ident FSet.t := List.fold_left (fun s x => FSet.add x s) s xs.
  Ltac2 rec close_s (cand : (ident * ident list) list) (vs : ident FSet.t) (n : int) : ident FSet.t :=
    if Int.le n 0 then vs else
    let vs' := List.fold_left (fun acc c => let (_, hv) := c in if meets_s hv vs then add_all acc hv else acc) vs cand in
    if Int.equal (FSet.cardinal vs') (FSet.cardinal vs) then vs else close_s cand vs' (Int.sub n 1).
  Ltac2 drop_list (n : int) : ident list :=
    let cand := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if head_may_be_arith ty then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.arith ty then Some (id, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.vars ty) else None) else None) else None
                  end) (Control.hyps ()) in
    let vs := close_s cand (add_all (FSet.empty FSet.Tags.ident_tag) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.vars (Control.goal ()))) n in
    List.map_filter (fun c => let (id, hv) := c in if meets_s hv vs then None else Some id) cand.
  Ltac2 prune (nd : bool) (n : int) : unit :=
    let drop := drop_list n in
    match drop with [] => () | _ :: _ => Std.clear drop end;
    if Bool.neg nd then () else
    let disj := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.has_or ty then Some id else None) else None
                  end) (Control.hyps ()) in
    match disj with [] => () | _ :: _ => Std.clear disj end.
  Ltac2 prune2 () : unit := Control.enter (fun () => prune true 2).
  Ltac2 prune2d () : unit := Control.enter (fun () => prune false 2).
End RLF.
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.rl_prune ::= ltac2:(RLF.prune2 ()).
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.rl_prune_d ::= ltac2:(RLF.prune2d ()).
(* [comment removed for export] *)
Local Ltac solve_acc1 ::= solve_acc1_rl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma asan_inited_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m 0xaf2d8 [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5c6f8) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros INI RIMG RTLS.
  do 6 step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma get_current_thread_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] ->
  rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 ->
  evtF asegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fe08) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> TI TK T88 TSD CT C0 C1 RIMG RTLS RSTK RCTX.
  unfold ATP, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  do 3 step.            (* [comment removed for export] *)
  do 4 step. if_false.  (* [comment removed for export] *)
  lstep. step.          (* [comment removed for export] *)
  do 7 lstep.           (* [comment removed for export] *)
  step. if_cases K; zify_cond K; [exfalso; lia|]. step.   (* [comment removed for export] *)
  do 3 step.            (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stack_top_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t top bot : Z),
  mem_inv asegs m ->
  a0 = Z_to_bv 64 t ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> 0 <= t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng RNG t 4096 ->
  evtF asegs RNG (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 top) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5ffcc) fc None m (seg_rom asegs)).
Proof.
  intros until bot. intros MI -> TB SW B0 BT TT T0 TC RT. atop_facts.
  lstep. step. step. if_lit.  (* [comment removed for export] *)
  do 2 step.                  (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  rewrite (sel_mask_true (bot <? top) top) by (first [apply Z.ltb_lt; lia | lia]).
  step. apply evtF_done. eexists. reflexivity.
Qed.

#[using="Type"] Lemma stack_bottom_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t top bot : Z),
  mem_inv asegs m ->
  a0 = Z_to_bv 64 t ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> 0 <= t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng RNG t 4096 ->
  evtF asegs RNG (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 bot) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x60024) fc None m (seg_rom asegs)).
Proof.
  intros until bot. intros MI -> TB SW B0 BT TT T0 TC RT. atop_facts.
  lstep. step. step. if_lit.  (* [comment removed for export] *)
  do 2 step.                  (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  rewrite (sel_mask_true (bot <? top) bot) by (first [apply Z.ltb_lt; lia | lia]).
  step. apply evtF_done. eexists. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma uchain_invalid_nil : forall m top pc p f k tr,
  uchain m top pc p f k tr -> ~ (p < f /\ f < top - 16 /\ f mod 8 = 0 /\ (0 < k)%nat) -> tr = [].
Proof. intros m top pc p f k tr H Hn. destruct H; [reflexivity| exfalso; apply Hn; auto | exfalso; apply Hn; auto]. Qed.

(* [comment removed for export] *)
Definition uwf_post (S pc top spf : Z) (raf s0f s1f s2f s3f s4f s5f s6f : word)
    (gp tp t0 t1 t2 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (size : nat) (tb : list word) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a2' a5' a6' a7' m' tb',
    ms' = MS (mkR raf (Z_to_bv 64 (spf + 64)) gp tp t0 t1 t2 s0f s1f
                  (Z_to_bv 64 S) (Z_to_bv 64 pc) a2' (Z_to_bv 64 4096) (Z_to_bv 64 (S + 16)) a5' a6' a7'
                  s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc raf) fc None m' (seg_rom asegs)
    /\ munch [(S + 8, S + 12); (S + 16, S + 2056)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (Z.of_nat size + Z.of_nat (length tr)))]
    /\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ (forall i, (i < size)%nat -> nth_error tb' i = nth_error tb i)
    /\ map bv_unsigned (firstn (length tr) (skipn size tb')) = tr.

End CANSEC1.
Local Ltac uwf_epilogue := do 10 step.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac uwf_tail IH HC size tb :=
  let K3 := fresh "K3" in let K4 := fresh "K4" in let K5 := fresh "K5" in let Etr := fresh "Etr" in
  let AL2 := fresh "AL2" in let NA2 := fresh "NA2" in
  step; if_cases K3; zify_cond K3;
  [ pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue
  | step; if_cases K4; zify_cond K4;
    [ pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue
    | do 2 zstep; step; if_cases K5; zify_cond K5;
      [ (* [comment removed for export] *)
        assert (AL2 : _ mod 8 = 0) by (change 7 with (Z.ones 3) in K5; rewrite Z.land_ones in K5 by lia; exact K5)
      | assert (NA2 : _ mod 8 <> 0) by (change 7 with (Z.ones 3) in K5; rewrite Z.land_ones in K5 by lia; exact K5);
        pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue ] ] ].

Local Ltac all_exits_post MU WM SZC TB LTB :=
  apply evtF_done; unfold uwf_post; do 6 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|]; split; [assumption|];
  split; [cbn [length app]; rewrite ?Z.add_0_r; exact SZC|]; split; [exact TB|]; split; [exact LTB|];
  split; [intros; reflexivity| reflexivity].

Local Ltac push_exits_post MU WM SZC TB LTB size :=
  apply evtF_done; unfold uwf_post; do 6 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|]; split; [assumption|];
  split; [cbn [length app]; replace (Z.of_nat size + Z.of_nat 1) with (Z.of_nat (Datatypes.S size)) by lia; exact SZC |];
  split; [exact TB|]; split; [rewrite upd_length; exact LTB|];
  split; [let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply nth_error_upd_other; lia|];
  cbn [length app]; rewrite skipn_upd_here by lia; cbn [firstn map]; rewrite unsigned_lit by lia; reflexivity.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition uwf_loop__stmt : Prop := forall m0 top pc prev frame k tr,
  uchain m0 top pc prev frame k tr ->
  forall RNG (gp tp t0 t1 t2 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : amem)
         (S spf lo : Z) (raf s0f s1f s2f s3f s4f s5f s6f : word) (size : nat) (tb : list word),
  (forall i, frame - 16 <= i < top -> m (wa i) = m0 (wa i)) ->
  mem_inv asegs m ->
  prev < frame -> frame < top - 16 -> frame mod 8 = 0 ->
  Z.of_nat size + Z.of_nat k = 30 -> length tb = 255%nat ->
  rw_cells asegs m (S + 8) [C4 (Z_to_bv 64 (Z.of_nat size))] ->
  u64arr asegs m (S + 16) tb ->
  rw_cells asegs m spf [C8 s6f; C8 s5f; C8 s4f; C8 s3f; C8 s2f; C8 s1f; C8 s0f; C8 raf] ->
  ATOP <= lo -> lo <= spf -> spf + 64 <= S -> S + 2072 <= frame -> top <= 2^47 -> 0 <= pc < 2^64 ->
  rng RNG lo (top - lo) ->
  evtF asegs RNG (uwf_post S pc top spf raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc size tb tr m)
    (MS (mkR raf (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 30) (Z_to_bv 64 (top - 16))
             (Z_to_bv 64 S) (Z_to_bv 64 pc) (Z_to_bv 64 frame) (Z_to_bv 64 4096) (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (Z.of_nat size)) a6 a7
             (Z_to_bv 64 APGSZ) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7702c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable m0 : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 0).
Variable top : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 1).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 2).
Variable prev : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 3).
Variable frame : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 4).
Variable k : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 5).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 6).
#[using="Type"] Lemma uwf_loop__body : ltac:(let T := type of (fun (h : uwf_loop__stmt) => h m0 top pc prev frame k tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (m0, (top, (pc, (prev, (frame, (k, tr))))))) as _.
  intros H.
  induction H as [prev frame k Hn | prev frame k fp rav H1 H2 H3 H4 B1 B2 Hra
                | prev frame k fp rav tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH];
    intros until tb; intros AG MI PF FT AL SK LTB SZC TB FR CEIL LOS SPS SPV TOP PC RR; unfold APGSZ in *.
  - (* [comment removed for export] *)
    assert (K0 : k = 0%nat) by (destruct k; [reflexivity| exfalso; apply Hn; repeat split; auto; lia]). subst k.
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K; zify_cond K; [| exfalso; lia].
    uwf_epilogue.
    apply evtF_done. unfold uwf_post. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [cbn [length]; rewrite Z.add_0_r; exact SZC|]. split; [exact TB|]. split; [exact LTB|].
    split; [intros; reflexivity| reflexivity].
  - (* [comment removed for export] *)
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; lia|].
    assert (B2' : bytes_at asegs m (frame + -8) (le8 (Z_to_bv 64 rav))).
    { eapply bytes_at_agree; [replace (frame + -8) with (frame - 8) by lia; exact B2|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    pose proof (bytes_at_read8 _ _ _ B2') as R2.
    step. clear R2 B2'.
    step. if_cases K1; zify_cond K1; [| exfalso; lia].
    uwf_epilogue.
    apply evtF_done. unfold uwf_post. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [cbn [length]; rewrite Z.add_0_r; exact SZC|]. split; [exact TB|]. split; [exact LTB|].
    split; [intros; reflexivity| reflexivity].
  - (* [comment removed for export] *)
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; lia|].
    assert (B2' : bytes_at asegs m (frame + -8) (le8 (Z_to_bv 64 rav))).
    { eapply bytes_at_agree; [replace (frame + -8) with (frame - 8) by lia; exact B2|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    assert (B1' : bytes_at asegs m (frame + -16) (le8 (Z_to_bv 64 fp))).
    { eapply bytes_at_agree; [replace (frame + -16) with (frame - 16) by lia; exact B1|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    pose proof (bytes_at_read8 _ _ _ B2') as R2.
    step. clear R2 B2'.
    step. if_cases K1; zify_cond K1; [exfalso; lia|].
    step. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (rav =? pc) with true in * by (symmetry; apply Z.eqb_eq; lia).
      pose proof (bytes_at_read8 _ _ _ B1') as R1.
      step. clear R1 B1'.
      uwf_tail IH HC size tb.
      * (* [comment removed for export] *)
        all_exits_post MU WM SZC TB LTB.
      * all_exits_post MU WM SZC TB LTB.
      * (* [comment removed for export] *)
        eapply evtF_mono.
        { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
            eapply (IH RNG gp tp t0 t1 t2 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm S spf lo raf s0f s1f s2f s3f s4f s5f s6f
                       size tb) end.
          all: try eassumption; try lia.
          intros i Hi. transitivity (m (wa i)); [apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia | apply AG; lia]. }
        intros ms' PO. cbn [app] in *. exact PO.
      * all_exits_post MU WM SZC TB LTB.
    + (* [comment removed for export] *)
      replace (rav =? pc) with false in * by (symmetry; apply Z.eqb_neq; lia).
      do 3 zstep.                                         (* [comment removed for export] *)
      step.                                               (* [comment removed for export] *)
      rewrite (Z.shiftl_mul_pow2 (Z.of_nat size) 3) by lia. change (2^3) with 8.
      replace (S + 16 + Z.of_nat size * 8) with (S + 16 + 8 * Z.of_nat size) by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u64arr_store_ok asegs mm (S + 16) tb (Z.of_nat size) (wa (S + 16 + 8 * Z.of_nat size)) TB ltac:(lia) eq_refl) as SOK end.
      step.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (u64arr_write asegs mm (S + 16) tb (Z.of_nat size) (Z_to_bv 64 rav) TB ltac:(lia)) as TB2 end.
      clear TB. store_done. rename TB2 into TB.
      pose proof (bytes_at_read8 _ _ _ B1') as R1.
      step. clear R1 B1'.
      replace (Z.of_nat size + 1) with (Z.of_nat (Datatypes.S size)) in * by lia.
      replace (Z.to_nat (Z.of_nat size)) with size in TB by lia.
      uwf_tail IH HC (Datatypes.S size) (upd tb size (Z_to_bv 64 rav)).
      * push_exits_post MU WM SZC TB LTB size.
      * push_exits_post MU WM SZC TB LTB size.
      * eapply evtF_mono.
        { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
            eapply (IH RNG gp tp t0 t1 t2 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm S spf lo raf s0f s1f s2f s3f s4f s5f s6f
                       (Datatypes.S size) (upd tb size (Z_to_bv 64 rav))) end.
          all: try eassumption; try lia.
          - intros i Hi. transitivity (m (wa i)); [apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia | apply AG; lia].
          - rewrite upd_length. exact LTB. }
        intros ms' PO. unfold uwf_post in PO |- *.
        (nd_pre PO 7%nat; intros a2' a5' a6' a7' m' tb' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MU' WM' MI' SZ' TB' LTB' OLD NEW; nd_post).
        exists a2', a5', a6', a7', m', tb'. split; [reflexivity|].
        split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
        split; [cbn [length app]; replace (Z.of_nat size + Z.of_nat (Datatypes.S (length tr))) with (Z.of_nat (Datatypes.S size) + Z.of_nat (length tr)) by lia; exact SZ'|].
        split; [exact TB'|]. split; [exact LTB'|]. split.
        { intros i Hi. rewrite (OLD i) by lia. apply nth_error_upd_other. lia. }
        cbn [length app]. rewrite (skipn_S_nth tb' size (Z_to_bv 64 rav)).
        2:{ rewrite (OLD size) by lia. apply nth_error_upd_here. lia. }
        cbn [firstn map]. rewrite unsigned_lit by lia. f_equal. exact NEW.
      * push_exits_post MU WM SZC TB LTB size.
Qed.
End Zd1.
#[using="Type"] Lemma uwf_loop : ltac:(let t := eval cbv delta [uwf_loop__stmt] in uwf_loop__stmt in exact t).
Proof. exact uwf_loop__body. Qed.

(* [comment removed for export] *)
Definition unwind_fast_post (S pc top : Z) (sp : word) (raf s0f s1f s2f s3f s4f s5f s6f : word)
    (gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
    (tb : list word) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a2' a3' a4' a5' a6' a7' m' tb',
    ms' = MS (mkR raf sp gp tp t0 t1 t2 s0f s1f
                  (Z_to_bv 64 S) (Z_to_bv 64 pc) a2' a3' a4' a5' a6' a7'
                  s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc raf) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (1 + Z.of_nat (length tr)))]
    /\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length tr)) tb') = pc :: tr.

Definition unwind_fast_spec__stmt : Prop := forall RNG (raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp top bot lo : Z) (tb : list word) (tr : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= S ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 top -> a4 = Z_to_bv 64 bot -> a5 = Z_to_bv 64 30 ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  uchain m top pc bot bp 29%nat tr ->
  0 <= bot -> bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> top <= 2^47 -> S + 2072 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (top - lo) ->
  evtF asegs RNG (unwind_fast_post S pc top sp raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo tb tr m)
    (MS (mkR raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x76f6c) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 0).
Variable raf : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 7).
Variable s0f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 8).
Variable s1f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 17).
Variable s2f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 18).
Variable s3f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 19).
Variable s4f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 20).
Variable s5f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 21).
Variable s6f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 34).
Variable S : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 36).
Variable bp : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 37).
Variable top : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 38).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 40).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 42).
#[using="Type"] Lemma unwind_fast_spec__body : ltac:(let T := type of (fun (h : unwind_fast_spec__stmt) => h RNG raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S pc bp top bot lo tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (raf, (sp, (gp, (tp, (t0, (t1, (t2, (s0f, (s1f, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2f, (s3f, (s4f, (s5f, (s6f, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (S, (pc, (bp, (top, (bot, (lo, (tb, tr))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SPS MI -> -> -> -> -> -> GPG PG [szj SZC] TB LTB UC B0 BB BT BA TOP SB PC RIMG RTLS RR.
  unfold GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. do 3 zstep.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 3 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_store_ok asegs mm (S + 16) tb 0 (wa (S + 16)) TB ltac:(lia) ltac:(f_equal; lia)) as SOK end.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u64arr_write asegs mm (S + 16) tb 0 (Z_to_bv 64 pc) TB ltac:(lia)) as TB2;
    rewrite Z.mul_0_r, Z.add_0_r in TB2 end.
  clear TB. store_done. rename TB2 into TB. cbn [Z.to_nat upd] in TB.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in K0 by lia. Z.div_mod_to_equations. lia. }
  step. if_cases K1; zify_cond K1. { exfalso. lia. }     (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  zstep. step. if_cases K4; zify_cond K4.                (* [comment removed for export] *)
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact BA. }
  zstep. step.                                 (* [comment removed for export] *)
  replace (top + -16) with (top - 16) by lia.
  change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)).
  eapply evtF_mono.
  { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (uwf_loop m top pc bot bp 29 tr UC RNG gp tp t0 t1 t2 _ _ _ _ _ _ s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm
                S (bv_unsigned sp + -64) lo raf s0f s1f s2f s3f s4f s5f s6f 1%nat (upd tb 0 (Z_to_bv 64 pc))) end.
    all: try eassumption; try lia.
    - intros i Hi. apply MU. unfold wa. rewrite unsigned_lit by lia. cbn. lia.
    - rewrite upd_length. exact LTB. }
  intros ms' PO. unfold uwf_post in PO. unfold unwind_fast_post.
  (nd_pre PO 7%nat; intros a2' a5' a6' a7' m' tb' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MU' WM' MI' SZ' TB' LTB' OLD NEW; nd_post).
  exists a2', (Z_to_bv 64 4096), (Z_to_bv 64 (S + 16)), a5', a6', a7', m', tb'.
  split. { replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. intros x Hx. cbn in Hx |- *. tauto. }
  split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
  split. { (* [comment removed for export] *)
    match goal with FRH : rw_cells asegs ?mx (bv_unsigned sp + -64) ?cs, STH : stk asegs ?mx' lo _ |- _ =>
      constr_eq mx mx';
      pose proof (rw_cells_transport asegs _ _ _ _ cs FRH MU' WM' ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
      pose proof (stk_transport_disjoint asegs _ _ _ _ _ STH MU' WM' ltac:(cbn [disjoint_from]; lia)) as ST'
    end.
    eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
    replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in FR' by lia. exact FR'. }
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|].
  destruct tb' as [|w tb'']; [cbn in LTB'; lia|].
  specialize (OLD 0%nat ltac:(lia)). cbn [nth_error] in OLD.
  destruct tb as [|w0 tb0]; [cbn in LTB; lia|]. cbn in OLD. injection OLD as ->.
  cbn [firstn map skipn] in NEW |- *. rewrite unsigned_lit by lia. f_equal. exact NEW.
Qed.
End Zd2.
#[using="Type"] Lemma unwind_fast_spec : ltac:(let t := eval cbv delta [unwind_fast_spec__stmt] in unwind_fast_spec__stmt in exact t).
Proof. exact unwind_fast_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC2.
Notation unwind_impl_W sp S t :=
  ([(bv_unsigned sp - 160, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056); (S + 2056, S + 2064); (t + 3168, t + 3169)]%Z) (only parsing).

Section CANSEC3. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition unwind_impl_post (S pc bp t : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' tb',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (unwind_impl_W sp S t) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (1 + Z.of_nat (length tr)))]
    /\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length tr)) tb') = pc :: tr
    /\ rw_cells asegs m' (S + 2056) [C8 (Z_to_bv 64 bp)]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Definition unwind_impl_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp ctx t top bot lo : Z) (tb : list word) (tr : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp <= S ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 30 ->
  (* [comment removed for export] *)
  rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  (exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  (exists bpj, rw_cells asegs m (S + 2056) [C8 bpj]) ->
  (* [comment removed for export] *)
  uchain m top pc bot bp 29%nat tr ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  0 <= bot -> bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> top <= 2^47 -> S + 2080 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (top - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (unwind_impl_post S pc bp t ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo tr m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e3a0) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 34).
Variable S : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 36).
Variable bp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 37).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 39).
Variable top : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 40).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 42).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 43).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 44).
#[using="Type"] Lemma unwind_impl_spec__body : ltac:(let T := type of (fun (h : unwind_impl_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S pc bp ctx t top bot lo tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (S, (pc, (bp, (ctx, (t, (top, (bot, (lo, (tb, tr))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SPS MI TP -> -> -> -> -> -> INI TI TK T88 TSD CT GPG PG TT SW UW [szj SZC] TB LTB [bpj BPJ] UC
         C0 C1 T0 T1 CT2 B0 BB BT BA TOP SB PC RIMG RTLS RR RCTX RT. unfold sclr, iclr, KLS, AIMG_LO in *.   (* [comment removed for export] *)
  unfold AIMG_HI, AINITED, ATSDI, ATSDK, ATP88, ATSD, GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl (unwind_impl_W sp S t) m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.        (* [comment removed for export] *)
  box RT.   (* [comment removed for export] *)
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. rename POST into ST. try rename MI0 into MI.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI end.
  step. if_cases K; zify_cond K; [exfalso; lia|].     (* [comment removed for export] *)
  zstep. lstep. step. step.                           (* [comment removed for export] *)
  step. if_lit.                                       (* [comment removed for export] *)
  step. step. callp stack_top_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  do 3 step. callp stack_bottom_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  step. step. if_lit.                                 (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 8 step.                                          (* [comment removed for export] *)
  do 6 zstep.                                         (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615.
  rewrite (land_ones_l bp) by lia.
  step.                                               (* [comment removed for export] *)
  step. if_lit. step. if_lit. step. if_lit.           (* [comment removed for export] *)
  do 5 step.                                          (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -80).
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (UC' : uchain mm top pc bot bp 29 tr)
      by (eapply uchain_frame; [exact UC|]; intros a Ha; apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia) end.
  name_sp sp (-80). rewrite <- Hsp in ST.
  eapply evtF_cut.
  { eapply unwind_fast_spec;
    [ exact ST | exact CEIL | | | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | exact GPG | exact PG | eexists; exact SZC | exact TB | exact LTB | exact UC' | | | | exact BA | | | exact PC
    | exact RIMG | exact RTLS | exact RR ].
    all: lia. }
  cbv beta. unfold unwind_fast_post.
  lazymatch goal with |- forall ms', _ -> evtF _ _ _ _ => idtac end.
  lazymatch type of MU with munch _ _ ?mcur => post_call asegs mcur end.
  unname_sp.
  clear UC'. rename PC0 into ST. rename PC1 into SZ'. rename PC2 into TB'. rename PC3 into LTB'. rename POST into TR'.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
  (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  do 12 step.                                         (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_impl_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|]. split; [exact TR'|].
  split; assumption.
Qed.
End Zd3.
#[using="Type"] Lemma unwind_impl_spec : ltac:(let t := eval cbv delta [unwind_impl_spec__stmt] in unwind_impl_spec__stmt in exact t).
Proof. exact unwind_impl_spec__body. Qed.
End CANSEC3.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module RLF.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 head_may_be_arith (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h _ =>
        (match Constr.Unsafe.kind h with
         | Constr.Unsafe.Constant _ _ =>
             List.exist (fun r => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h r)
               [reference:(not); reference:(iff); reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt);
                reference:(lt); reference:(ge); reference:(gt); reference:(N.le); reference:(N.lt); reference:(Z.divide)]
         | Constr.Unsafe.Ind _ _ =>
             List.exist (fun r => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h r) [reference:(and); reference:(or); reference:(eq); reference:(le)]
         | _ => true
         end)
    | _ => true
    end.
  Ltac2 is_local (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
  (* [comment removed for export] *)
  Ltac2 meets_s (xs : ident list) (vs : ident FSet.t) : bool := List.exist (fun x => FSet.mem x vs) xs.
  Ltac2 add_all (s : ident FSet.t) (xs : ident list) : ident FSet.t := List.fold_left (fun s x => FSet.add x s) s xs.
  Ltac2 rec close_s (cand : (ident * ident list) list) (vs : ident FSet.t) (n : int) : ident FSet.t :=
    if Int.le n 0 then vs else
    let vs' := List.fold_left (fun acc c => let (_, hv) := c in if meets_s hv vs then add_all acc hv else acc) vs cand in
    if Int.equal (FSet.cardinal vs') (FSet.cardinal vs) then vs else close_s cand vs' (Int.sub n 1).
  Ltac2 drop_list (n : int) : ident list :=
    let cand := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if head_may_be_arith ty then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.arith ty then Some (id, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.vars ty) else None) else None) else None
                  end) (Control.hyps ()) in
    let vs := close_s cand (add_all (FSet.empty FSet.Tags.ident_tag) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.vars (Control.goal ()))) n in
    List.map_filter (fun c => let (id, hv) := c in if meets_s hv vs then None else Some id) cand.
  Ltac2 prune (nd : bool) (n : int) : unit :=
    let drop := drop_list n in
    match drop with [] => () | _ :: _ => Std.clear drop end;
    if Bool.neg nd then () else
    let disj := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.RL.has_or ty then Some id else None) else None
                  end) (Control.hyps ()) in
    match disj with [] => () | _ :: _ => Std.clear disj end.
  Ltac2 prune2 () : unit := Control.enter (fun () => prune true 2).
  Ltac2 prune2d () : unit := Control.enter (fun () => prune false 2).
End RLF.
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.rl_prune ::= ltac2:(RLF.prune2 ()).
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.rl_prune_d ::= ltac2:(RLF.prune2d ()).
(* [comment removed for export] *)
Local Ltac solve_acc1 ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.AFastTac.solve_acc1_rl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma asan_inited_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m 0xaf6d8 [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5c760) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros INI RIMG RTLS.
  do 6 step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma get_current_thread_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (ctx t lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] ->
  rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 ->
  evtF asegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fe70) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> TI TK T88 TSD CT C0 C1 RIMG RTLS RSTK RCTX.
  unfold ATP, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  do 3 step.            (* [comment removed for export] *)
  do 4 step. if_false.  (* [comment removed for export] *)
  lstep. step.          (* [comment removed for export] *)
  do 7 lstep.           (* [comment removed for export] *)
  step. if_cases K; zify_cond K; [exfalso; lia|]. step.   (* [comment removed for export] *)
  do 3 step.            (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stack_top_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t top bot : Z),
  mem_inv asegs m ->
  a0 = Z_to_bv 64 t ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> 0 <= t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng RNG t 4096 ->
  evtF asegs RNG (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 top) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x60034) fc None m (seg_rom asegs)).
Proof.
  intros until bot. intros MI -> TB SW B0 BT TT T0 TC RT. atop_facts.
  lstep. step. step. if_lit.  (* [comment removed for export] *)
  do 2 step.                  (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  rewrite (sel_mask_true (bot <? top) top) by (first [apply Z.ltb_lt; lia | lia]).
  step. apply evtF_done. eexists. reflexivity.
Qed.

#[using="Type"] Lemma stack_bottom_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t top bot : Z),
  mem_inv asegs m ->
  a0 = Z_to_bv 64 t ->
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  0 <= bot -> bot < top -> top <= 2^47 -> 0 <= t -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng RNG t 4096 ->
  evtF asegs RNG (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 bot) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6008c) fc None m (seg_rom asegs)).
Proof.
  intros until bot. intros MI -> TB SW B0 BT TT T0 TC RT. atop_facts.
  lstep. step. step. if_lit.  (* [comment removed for export] *)
  do 2 step.                  (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  rewrite (sel_mask_true (bot <? top) bot) by (first [apply Z.ltb_lt; lia | lia]).
  step. apply evtF_done. eexists. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma uchain_invalid_nil : forall m top pc p f k tr,
  uchain m top pc p f k tr -> ~ (p < f /\ f < top - 16 /\ f mod 8 = 0 /\ (0 < k)%nat) -> tr = [].
Proof. intros m top pc p f k tr H Hn. destruct H; [reflexivity| exfalso; apply Hn; auto | exfalso; apply Hn; auto]. Qed.

(* [comment removed for export] *)
Definition uwf_post (S pc top spf : Z) (raf s0f s1f s2f s3f s4f s5f s6f : word)
    (gp tp t0 t1 t2 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (size : nat) (tb : list word) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a2' a5' a6' a7' m' tb',
    ms' = MS (mkR raf (Z_to_bv 64 (spf + 64)) gp tp t0 t1 t2 s0f s1f
                  (Z_to_bv 64 S) (Z_to_bv 64 pc) a2' (Z_to_bv 64 4096) (Z_to_bv 64 (S + 16)) a5' a6' a7'
                  s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc raf) fc None m' (seg_rom asegs)
    /\ munch [(S + 8, S + 12); (S + 16, S + 2056)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (Z.of_nat size + Z.of_nat (length tr)))]
    /\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ (forall i, (i < size)%nat -> nth_error tb' i = nth_error tb i)
    /\ map bv_unsigned (firstn (length tr) (skipn size tb')) = tr.

End CANSEC1.
Local Ltac uwf_epilogue := do 10 step.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac uwf_tail IH HC size tb :=
  let K3 := fresh "K3" in let K4 := fresh "K4" in let K5 := fresh "K5" in let Etr := fresh "Etr" in
  let AL2 := fresh "AL2" in let NA2 := fresh "NA2" in
  step; if_cases K3; zify_cond K3;
  [ pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue
  | step; if_cases K4; zify_cond K4;
    [ pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue
    | do 2 zstep; step; if_cases K5; zify_cond K5;
      [ (* [comment removed for export] *)
        assert (AL2 : _ mod 8 = 0) by (change 7 with (Z.ones 3) in K5; rewrite Z.land_ones in K5 by lia; exact K5)
      | assert (NA2 : _ mod 8 <> 0) by (change 7 with (Z.ones 3) in K5; rewrite Z.land_ones in K5 by lia; exact K5);
        pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue ] ] ].

Local Ltac all_exits_post MU WM SZC TB LTB :=
  apply evtF_done; unfold uwf_post; do 6 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|]; split; [assumption|];
  split; [cbn [length app]; rewrite ?Z.add_0_r; exact SZC|]; split; [exact TB|]; split; [exact LTB|];
  split; [intros; reflexivity| reflexivity].

Local Ltac push_exits_post MU WM SZC TB LTB size :=
  apply evtF_done; unfold uwf_post; do 6 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|]; split; [assumption|];
  split; [cbn [length app]; replace (Z.of_nat size + Z.of_nat 1) with (Z.of_nat (Datatypes.S size)) by lia; exact SZC |];
  split; [exact TB|]; split; [rewrite upd_length; exact LTB|];
  split; [let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply nth_error_upd_other; lia|];
  cbn [length app]; rewrite skipn_upd_here by lia; cbn [firstn map]; rewrite unsigned_lit by lia; reflexivity.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition uwf_loop__stmt : Prop := forall m0 top pc prev frame k tr,
  uchain m0 top pc prev frame k tr ->
  forall RNG (gp tp t0 t1 t2 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : amem)
         (S spf lo : Z) (raf s0f s1f s2f s3f s4f s5f s6f : word) (size : nat) (tb : list word),
  (forall i, frame - 16 <= i < top -> m (wa i) = m0 (wa i)) ->
  mem_inv asegs m ->
  prev < frame -> frame < top - 16 -> frame mod 8 = 0 ->
  Z.of_nat size + Z.of_nat k = 30 -> length tb = 255%nat ->
  rw_cells asegs m (S + 8) [C4 (Z_to_bv 64 (Z.of_nat size))] ->
  u64arr asegs m (S + 16) tb ->
  rw_cells asegs m spf [C8 s6f; C8 s5f; C8 s4f; C8 s3f; C8 s2f; C8 s1f; C8 s0f; C8 raf] ->
  ATOP <= lo -> lo <= spf -> spf + 64 <= S -> S + 2072 <= frame -> top <= 2^47 -> 0 <= pc < 2^64 ->
  rng RNG lo (top - lo) ->
  evtF asegs RNG (uwf_post S pc top spf raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc size tb tr m)
    (MS (mkR raf (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 30) (Z_to_bv 64 (top - 16))
             (Z_to_bv 64 S) (Z_to_bv 64 pc) (Z_to_bv 64 frame) (Z_to_bv 64 4096) (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (Z.of_nat size)) a6 a7
             (Z_to_bv 64 APGSZ) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x77094) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable m0 : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 0).
Variable top : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 1).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 2).
Variable prev : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 3).
Variable frame : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 4).
Variable k : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 5).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'uwf_loop__stmt 6).
#[using="Type"] Lemma uwf_loop__body : ltac:(let T := type of (fun (h : uwf_loop__stmt) => h m0 top pc prev frame k tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (m0, (top, (pc, (prev, (frame, (k, tr))))))) as _.
  intros H.
  induction H as [prev frame k Hn | prev frame k fp rav H1 H2 H3 H4 B1 B2 Hra
                | prev frame k fp rav tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH];
    intros until tb; intros AG MI PF FT AL SK LTB SZC TB FR CEIL LOS SPS SPV TOP PC RR; unfold APGSZ in *.
  - (* [comment removed for export] *)
    assert (K0 : k = 0%nat) by (destruct k; [reflexivity| exfalso; apply Hn; repeat split; auto; lia]). subst k.
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K; zify_cond K; [| exfalso; lia].
    uwf_epilogue.
    apply evtF_done. unfold uwf_post. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [cbn [length]; rewrite Z.add_0_r; exact SZC|]. split; [exact TB|]. split; [exact LTB|].
    split; [intros; reflexivity| reflexivity].
  - (* [comment removed for export] *)
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; lia|].
    assert (B2' : bytes_at asegs m (frame + -8) (le8 (Z_to_bv 64 rav))).
    { eapply bytes_at_agree; [replace (frame + -8) with (frame - 8) by lia; exact B2|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    pose proof (bytes_at_read8 _ _ _ B2') as R2.
    step. clear R2 B2'.
    step. if_cases K1; zify_cond K1; [| exfalso; lia].
    uwf_epilogue.
    apply evtF_done. unfold uwf_post. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [cbn [length]; rewrite Z.add_0_r; exact SZC|]. split; [exact TB|]. split; [exact LTB|].
    split; [intros; reflexivity| reflexivity].
  - (* [comment removed for export] *)
    pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; lia|].
    assert (B2' : bytes_at asegs m (frame + -8) (le8 (Z_to_bv 64 rav))).
    { eapply bytes_at_agree; [replace (frame + -8) with (frame - 8) by lia; exact B2|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    assert (B1' : bytes_at asegs m (frame + -16) (le8 (Z_to_bv 64 fp))).
    { eapply bytes_at_agree; [replace (frame + -16) with (frame - 16) by lia; exact B1|].
      intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
    pose proof (bytes_at_read8 _ _ _ B2') as R2.
    step. clear R2 B2'.
    step. if_cases K1; zify_cond K1; [exfalso; lia|].
    step. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      replace (rav =? pc) with true in * by (symmetry; apply Z.eqb_eq; lia).
      pose proof (bytes_at_read8 _ _ _ B1') as R1.
      step. clear R1 B1'.
      uwf_tail IH HC size tb.
      * (* [comment removed for export] *)
        all_exits_post MU WM SZC TB LTB.
      * all_exits_post MU WM SZC TB LTB.
      * (* [comment removed for export] *)
        eapply evtF_mono.
        { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
            eapply (IH RNG gp tp t0 t1 t2 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm S spf lo raf s0f s1f s2f s3f s4f s5f s6f
                       size tb) end.
          all: try eassumption; try lia.
          intros i Hi. transitivity (m (wa i)); [apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia | apply AG; lia]. }
        intros ms' PO. cbn [app] in *. exact PO.
      * all_exits_post MU WM SZC TB LTB.
    + (* [comment removed for export] *)
      replace (rav =? pc) with false in * by (symmetry; apply Z.eqb_neq; lia).
      do 3 zstep.                                         (* [comment removed for export] *)
      step.                                               (* [comment removed for export] *)
      rewrite (Z.shiftl_mul_pow2 (Z.of_nat size) 3) by lia. change (2^3) with 8.
      replace (S + 16 + Z.of_nat size * 8) with (S + 16 + 8 * Z.of_nat size) by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u64arr_store_ok asegs mm (S + 16) tb (Z.of_nat size) (wa (S + 16 + 8 * Z.of_nat size)) TB ltac:(lia) eq_refl) as SOK end.
      step.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (u64arr_write asegs mm (S + 16) tb (Z.of_nat size) (Z_to_bv 64 rav) TB ltac:(lia)) as TB2 end.
      clear TB. store_done. rename TB2 into TB.
      pose proof (bytes_at_read8 _ _ _ B1') as R1.
      step. clear R1 B1'.
      replace (Z.of_nat size + 1) with (Z.of_nat (Datatypes.S size)) in * by lia.
      replace (Z.to_nat (Z.of_nat size)) with size in TB by lia.
      uwf_tail IH HC (Datatypes.S size) (upd tb size (Z_to_bv 64 rav)).
      * push_exits_post MU WM SZC TB LTB size.
      * push_exits_post MU WM SZC TB LTB size.
      * eapply evtF_mono.
        { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
            eapply (IH RNG gp tp t0 t1 t2 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm S spf lo raf s0f s1f s2f s3f s4f s5f s6f
                       (Datatypes.S size) (upd tb size (Z_to_bv 64 rav))) end.
          all: try eassumption; try lia.
          - intros i Hi. transitivity (m (wa i)); [apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia | apply AG; lia].
          - rewrite upd_length. exact LTB. }
        intros ms' PO. unfold uwf_post in PO |- *.
        (nd_pre PO 7%nat; intros a2' a5' a6' a7' m' tb' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MU' WM' MI' SZ' TB' LTB' OLD NEW; nd_post).
        exists a2', a5', a6', a7', m', tb'. split; [reflexivity|].
        split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
        split; [cbn [length app]; replace (Z.of_nat size + Z.of_nat (Datatypes.S (length tr))) with (Z.of_nat (Datatypes.S size) + Z.of_nat (length tr)) by lia; exact SZ'|].
        split; [exact TB'|]. split; [exact LTB'|]. split.
        { intros i Hi. rewrite (OLD i) by lia. apply nth_error_upd_other. lia. }
        cbn [length app]. rewrite (skipn_S_nth tb' size (Z_to_bv 64 rav)).
        2:{ rewrite (OLD size) by lia. apply nth_error_upd_here. lia. }
        cbn [firstn map]. rewrite unsigned_lit by lia. f_equal. exact NEW.
      * push_exits_post MU WM SZC TB LTB size.
Qed.
End Zd1.
#[using="Type"] Lemma uwf_loop : ltac:(let t := eval cbv delta [uwf_loop__stmt] in uwf_loop__stmt in exact t).
Proof. exact uwf_loop__body. Qed.

(* [comment removed for export] *)
Definition unwind_fast_post (S pc top : Z) (sp : word) (raf s0f s1f s2f s3f s4f s5f s6f : word)
    (gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
    (tb : list word) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a2' a3' a4' a5' a6' a7' m' tb',
    ms' = MS (mkR raf sp gp tp t0 t1 t2 s0f s1f
                  (Z_to_bv 64 S) (Z_to_bv 64 pc) a2' a3' a4' a5' a6' a7'
                  s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc raf) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (1 + Z.of_nat (length tr)))]
    /\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length tr)) tb') = pc :: tr.

Definition unwind_fast_spec__stmt : Prop := forall RNG (raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp top bot lo : Z) (tb : list word) (tr : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= S ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 top -> a4 = Z_to_bv 64 bot -> a5 = Z_to_bv 64 30 ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  uchain m top pc bot bp 29%nat tr ->
  0 <= bot -> bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> top <= 2^47 -> S + 2072 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (top - lo) ->
  evtF asegs RNG (unwind_fast_post S pc top sp raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo tb tr m)
    (MS (mkR raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x76fd4) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 0).
Variable raf : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 7).
Variable s0f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 8).
Variable s1f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 17).
Variable s2f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 18).
Variable s3f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 19).
Variable s4f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 20).
Variable s5f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 21).
Variable s6f : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 34).
Variable S : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 36).
Variable bp : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 37).
Variable top : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 38).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 39).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 40).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'unwind_fast_spec__stmt 42).
#[using="Type"] Lemma unwind_fast_spec__body : ltac:(let T := type of (fun (h : unwind_fast_spec__stmt) => h RNG raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S pc bp top bot lo tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (raf, (sp, (gp, (tp, (t0, (t1, (t2, (s0f, (s1f, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2f, (s3f, (s4f, (s5f, (s6f, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (S, (pc, (bp, (top, (bot, (lo, (tb, tr))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SPS MI -> -> -> -> -> -> GPG PG [szj SZC] TB LTB UC B0 BB BT BA TOP SB PC RIMG RTLS RR.
  unfold GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  do 9 step.                                   (* [comment removed for export] *)
  step. do 3 zstep.                            (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  do 3 step.                                   (* [comment removed for export] *)
  step. if_lit.                                (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_store_ok asegs mm (S + 16) tb 0 (wa (S + 16)) TB ltac:(lia) ltac:(f_equal; lia)) as SOK end.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u64arr_write asegs mm (S + 16) tb 0 (Z_to_bv 64 pc) TB ltac:(lia)) as TB2;
    rewrite Z.mul_0_r, Z.add_0_r in TB2 end.
  clear TB. store_done. rename TB2 into TB. cbn [Z.to_nat upd] in TB.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in K0 by lia. Z.div_mod_to_equations. lia. }
  step. if_cases K1; zify_cond K1. { exfalso. lia. }     (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  zstep. step. if_cases K4; zify_cond K4.                (* [comment removed for export] *)
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact BA. }
  zstep. step.                                 (* [comment removed for export] *)
  replace (top + -16) with (top - 16) by lia.
  change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)).
  eapply evtF_mono.
  { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (uwf_loop m top pc bot bp 29 tr UC RNG gp tp t0 t1 t2 _ _ _ _ _ _ s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm
                S (bv_unsigned sp + -64) lo raf s0f s1f s2f s3f s4f s5f s6f 1%nat (upd tb 0 (Z_to_bv 64 pc))) end.
    all: try eassumption; try lia.
    - intros i Hi. apply MU. unfold wa. rewrite unsigned_lit by lia. cbn. lia.
    - rewrite upd_length. exact LTB. }
  intros ms' PO. unfold uwf_post in PO. unfold unwind_fast_post.
  (nd_pre PO 7%nat; intros a2' a5' a6' a7' m' tb' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MU' WM' MI' SZ' TB' LTB' OLD NEW; nd_post).
  exists a2', (Z_to_bv 64 4096), (Z_to_bv 64 (S + 16)), a5', a6', a7', m', tb'.
  split. { replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. intros x Hx. cbn in Hx |- *. tauto. }
  split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
  split. { (* [comment removed for export] *)
    match goal with FRH : rw_cells asegs ?mx (bv_unsigned sp + -64) ?cs, STH : stk asegs ?mx' lo _ |- _ =>
      constr_eq mx mx';
      pose proof (rw_cells_transport asegs _ _ _ _ cs FRH MU' WM' ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
      pose proof (stk_transport_disjoint asegs _ _ _ _ _ STH MU' WM' ltac:(cbn [disjoint_from]; lia)) as ST'
    end.
    eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
    replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in FR' by lia. exact FR'. }
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|].
  destruct tb' as [|w tb'']; [cbn in LTB'; lia|].
  specialize (OLD 0%nat ltac:(lia)). cbn [nth_error] in OLD.
  destruct tb as [|w0 tb0]; [cbn in LTB; lia|]. cbn in OLD. injection OLD as ->.
  cbn [firstn map skipn] in NEW |- *. rewrite unsigned_lit by lia. f_equal. exact NEW.
Qed.
End Zd2.
#[using="Type"] Lemma unwind_fast_spec : ltac:(let t := eval cbv delta [unwind_fast_spec__stmt] in unwind_fast_spec__stmt in exact t).
Proof. exact unwind_fast_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC2.
Notation unwind_impl_W sp S t :=
  ([(bv_unsigned sp - 160, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056); (S + 2056, S + 2064); (t + 3168, t + 3169)]%Z) (only parsing).

Section CANSEC3. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition unwind_impl_post (S pc bp t : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (tr : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' tb',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (unwind_impl_W sp S t) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (1 + Z.of_nat (length tr)))]
    /\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
    /\ map bv_unsigned (firstn (Datatypes.S (length tr)) tb') = pc :: tr
    /\ rw_cells asegs m' (S + 2056) [C8 (Z_to_bv 64 bp)]
    /\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].

Definition unwind_impl_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (S pc bp ctx t top bot lo : Z) (tb : list word) (tr : list Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp <= S ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 30 ->
  (* [comment removed for export] *)
  rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  (exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  (exists bpj, rw_cells asegs m (S + 2056) [C8 bpj]) ->
  (* [comment removed for export] *)
  uchain m top pc bot bp 29%nat tr ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  0 <= bot -> bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> top <= 2^47 -> S + 2080 <= bp -> 0 <= pc < 2^64 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (top - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (unwind_impl_post S pc bp t ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo tr m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e408) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 34).
Variable S : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 36).
Variable bp : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 37).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 38).
Variable t : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 39).
Variable top : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 40).
Variable bot : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 42).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 43).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'unwind_impl_spec__stmt 44).
#[using="Type"] Lemma unwind_impl_spec__body : ltac:(let T := type of (fun (h : unwind_impl_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S pc bp ctx t top bot lo tb tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (S, (pc, (bp, (ctx, (t, (top, (bot, (lo, (tb, tr))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SPS MI TP -> -> -> -> -> -> INI TI TK T88 TSD CT GPG PG TT SW UW [szj SZC] TB LTB [bpj BPJ] UC
         C0 C1 T0 T1 CT2 B0 BB BT BA TOP SB PC RIMG RTLS RR RCTX RT. unfold sclr, iclr, KLS, AIMG_LO in *.   (* [comment removed for export] *)
  unfold AIMG_HI, AINITED, ATSDI, ATSDK, ATP88, ATSD, GOT_PGSZ, APGSZ in *.
  pose proof (munch_refl (unwind_impl_W sp S t) m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.        (* [comment removed for export] *)
  box RT.   (* [comment removed for export] *)
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. rename POST into ST. try rename MI0 into MI.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI end.
  step. if_cases K; zify_cond K; [exfalso; lia|].     (* [comment removed for export] *)
  zstep. lstep. step. step.                           (* [comment removed for export] *)
  step. if_lit.                                       (* [comment removed for export] *)
  step. step. callp stack_top_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  do 3 step. callp stack_bottom_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
  step. step. if_lit.                                 (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 8 step.                                          (* [comment removed for export] *)
  do 6 zstep.                                         (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615.
  rewrite (land_ones_l bp) by lia.
  step.                                               (* [comment removed for export] *)
  step. if_lit. step. if_lit. step. if_lit.           (* [comment removed for export] *)
  do 5 step.                                          (* [comment removed for export] *)
  do 8 step.                                          (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -80).
  step.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (UC' : uchain mm top pc bot bp 29 tr)
      by (eapply uchain_frame; [exact UC|]; intros a Ha; apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia) end.
  name_sp sp (-80). rewrite <- Hsp in ST.
  eapply evtF_cut.
  { eapply unwind_fast_spec;
    [ exact ST | exact CEIL | | | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | exact GPG | exact PG | eexists; exact SZC | exact TB | exact LTB | exact UC' | | | | exact BA | | | exact PC
    | exact RIMG | exact RTLS | exact RR ].
    all: lia. }
  cbv beta. unfold unwind_fast_post.
  lazymatch goal with |- forall ms', _ -> evtF _ _ _ _ => idtac end.
  lazymatch type of MU with munch _ _ ?mcur => post_call asegs mcur end.
  unname_sp.
  clear UC'. rename PC0 into ST. rename PC1 into SZ'. rename PC2 into TB'. rename PC3 into LTB'. rename POST into TR'.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
  (* [comment removed for export] *)
  step.                                               (* [comment removed for export] *)
  do 12 step.                                         (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold unwind_impl_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|]. split; [exact TR'|].
  split; assumption.
Qed.
End Zd3.
#[using="Type"] Lemma unwind_impl_spec : ltac:(let t := eval cbv delta [unwind_impl_spec__stmt] in unwind_impl_spec__stmt in exact t).
Proof. exact unwind_impl_spec__body. Qed.
End CANSEC3.
End TwB.
