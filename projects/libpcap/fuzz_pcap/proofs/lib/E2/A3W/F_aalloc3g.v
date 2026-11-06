(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memsetZ F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3 F_acache3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memsetZ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aclass2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 yl_is_copy (id : ident) : bool :=
  let s := Ident.to_string id in
  let n := String.length s in
  if Int.ge n 1 then
    (if Char.equal (String.get s 0) (Char.of_int 89) then true
     else if Int.ge n 2 then (if Char.equal (String.get s 0) (Char.of_int 68) then Char.equal (String.get s 1) (Char.of_int 88) else false)
     else false)
  else false.
Local Ltac2 yl_prune () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then (if yl_is_copy id then None else zt_is_prop_some ty id) else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac yl_prune := ltac2:(Control.enter yl_prune).
Set Default Proof Mode "Classic".
Local Ltac ylia := first [ yl_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ]
                   | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_base8 := lazymatch goal with |- (?a <= ?b /\ _)%Z => let X := leftmost a in let Y := leftmost b in first [ constr_eq X Y | is_Zlit X; is_Zlit Y ] end.
Local Ltac fp_find8s := first [ apply Exists_cons_hd; cbn [fst snd]; fp_base8; split; lia | apply Exists_cons_tl; fp_find8s ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8s | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma cb_take : forall m A n k bs,
  rw_cells asegs m A [CB (Z.to_nat n) bs] -> 0 <= k <= n ->
  rw_cells asegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)] /\ rw_cells asegs m (A + k) [CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)].
Proof.
  intros m A n k bs H HK.
  assert (L : length bs = Z.to_nat n) by (destruct H as [[[WF _] _] _]; cbn in WF; exact WF).
  assert (H2 : rw_cells asegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs); CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)]).
  { eapply rw_cells_recast; [exact H | | |].
    - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
    - cbn [cells_size csize]. lia. }
  lazymatch type of H2 with rw_cells _ _ _ [?x; ?y] => change [x; y] with ([x] ++ [y]) in H2 end.
  apply rw_cells_app in H2. destruct H2 as [HA HR]. cbn [cells_size csize] in HR. rewrite Nat.add_0_r, Z2Nat.id in HR by lia.
  split; [exact HA | exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_app2 : forall m A n1 bs1 n2 bs2,
  rw_cells asegs m A [CB n1 bs1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells asegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros m A n1 bs1 n2 bs2 H1 H2.
  assert (H : rw_cells asegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  cbn [app] in H. eapply rw_cells_recast; [exact H | | |].
  - destruct H1 as [[[W1 _] _] _]. destruct H2 as [[[W2 _] _] _]. cbn in W1, W2 |- *. rewrite length_app. repeat split; lia.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn [cells_size csize]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stats_class_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (X size : Z),
  a0 = Z_to_bv 64 X -> 0 <= X -> X + 112 < 2^64 ->
  24 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 112)) (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34298) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x341a4) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros -> X0 X1 SZ M8 RIMG RTLS.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. (nd_pre CF 6%nat; intros C1 CS1 CS2 CS3 CSM CBG; nd_post).
  step. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
  - eapply evtF_mono; [eapply (classblock2_spec RNG); [lia | exact M8 | exact RIMG | exact RTLS] |].
    cbv beta. intros ms' P. (nd_pre P 6%nat; intros a2' a3' a4' a5' a6' ndR1__; nd_post; revert ndR1__; intros ->). do 5 eexists. reflexivity.
  - zstep. zstep. rewrite <- (CSM ltac:(lia)). step.            (* [comment removed for export] *)
    apply evtF_done. do 5 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma fill_len_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min n 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x342d0) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x342c4) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros N RIMG RTLS.
  step. step. if_cases K; zify_cond K.                           (* [comment removed for export] *)
  - replace (Z.min n 4096) with n by lia. apply evtF_done. reflexivity.
  - step. replace (Z.min n 4096) with 4096 by lia. apply evtF_done. reflexivity.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition allocD_postG (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).

Definition allocD_gen__stmt : Prop := forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
    (n t c AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
    (fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6 : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + n <= ATOP -> AB mod 16 = 0 ->
  class_id (needed_size n) = c ->
  (t + 4096 <= AB \/ AB + 65536 <= t) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
  rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
  0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  tclr AB (UB + n - AB) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0xa54d0 [C8 (Z_to_bv 64 0xa7360)] ->
  rw_cells asegs m 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)] ->
  rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x1400c0 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 <= b1m < 256 -> 0 < id < 2^31 ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
  evtF asegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x34154) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 4).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 5).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 7).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 8).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 9).
Variable c : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 10).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 11).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 12).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 13).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 14).
Variable b1m : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 15).
Variable id : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 16).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 17).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 18).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 19).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 20).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 21).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 22).
Variable raX : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 23).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 24).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 25).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 26).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 27).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 28).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 29).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 30).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 31).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 32).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 33).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 34).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 35).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 36).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 37).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 38).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 39).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 40).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 41).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 42).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 43).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 44).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 45).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 46).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 47).
Variable s6x : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 48).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 49).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 50).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 51).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 52).
Let fl := Z.min n 4096.
#[using="fl"] Lemma allocD_gen__body : ltac:(let T := type of (fun (h : allocD_gen__stmt) => h L RNG sp gp tp F fc m n t c AB UB lo b0 b1m id S sj uj j1 j2 fr0 raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (sp, (gp, (tp, (F, (fc, (m, (n, (t, (c, (AB, (UB, (lo, (b0, (b1m, (id, (S, (sj, (uj, (j1, (j2, (fr0, (raX, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, (s11v, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s6x, (t3, (t4, (t5, t6))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1 TCB
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RTLS RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  tclr_int TCB.
  unfold AIMG_HI, ATP88, ATSD in *.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N PRIM HC) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ2 SM16 SMALL MC2; nd_post).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  step. call_sp (thread_stats_spec RNG (al_ctx L) t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  rename POST into ST.
  aload STATS 2 (t + 2800 + 16).                                 (* [comment removed for export] *)
  aload STATS 0 (t + 2800 + 0).                                  (* [comment removed for export] *)
  aload STATS 1 (t + 2800 + 8).                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep. zstep. zstep.                       (* [comment removed for export] *)
  astore STATS 0.                                                (* [comment removed for export] *)
  astore STATS 1.                                                (* [comment removed for export] *)
  astore STATS 2.                                                (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2: { exfalso. lia. }          (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evtF_cut; [eapply (stats_class_spec RNG); [reflexivity | lia | lia | lia | clear -NS RSM RZM; rewrite NS; Z.div_mod_to_equations; lia | exact RIMG | exact RTLS] |].
  cbv beta. intros msS PS. (nd_pre PS 6%nat; intros a2s a3s a4s a5s a6s ndR1__; nd_post; revert ndR1__; intros ->). rewrite HC.
  zstep. zstep.                                                  (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 c 3) by lia. change (2^3) with 8.
  aload STATS (14 + c) (t + 2912 + c * 8).                       (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  astore STATS (14 + c).                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  carry UJ MUs WMs ltac:(with_box DJT ylia). carry HDR MUs WMs ltac:(with_box DJT ylia).
  unbox LH.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH' : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH RZ). box LH. carry LH MUs WMs ltac:(with_box DJT ylia). exact LH. }
  clear LH MUs WMs. box LH'. box STATS.
  snapshot [(UB - 16, UB + n); (AB, AB + 16); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUc WMc.
  snapshot [(UB - 16, UB + n); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUl WMl.
  (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. lstep. step. if_lit.                               (* [comment removed for export] *)
  eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG | exact RTLS] |]. cbv beta. intros msF ->.   (* [comment removed for export] *)
  chg (Z.min n 4096) fl.
  destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
  step. step. step. lstep. step.                                 (* [comment removed for export] *)
  box UJ1.   (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear UJ1
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => unboxed UJ1
       | |- rng _ _ _ => eapply rng_sub'; [exact RU|]; subst fl; lia
       | |- _ => subst fl; atop_facts; lia
       end.
  rename POST into UF1.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (UF : rw_cells asegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
  { replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
    apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
  clear UF1 UJ2.
  (* [comment removed for export] *)
  step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
  lstep. zstep. zstep. zstep. zstep. step.                       (* [comment removed for export] *)
  sstep. step. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  unbox LH'.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH' RZ). box LH'. carry LH' MUl WMl ltac:(lia). exact LH'. }
  clear LH' MUl WMl.
  pose proof (rz_size_cases n) as RZC. box RZC.
  step. if_cases K3; zify_cond K3.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    clear LH.
    match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => unboxed STK__
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ _ _ => exact HK
         | |- rng _ _ _ => solve_rng
         | |- _ => atop_facts; lia
         end.
    rename POST into ST.
    do 16 step.                                                  (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    carry STATS MUc WMc ltac:(with_box DJT ylia).
    apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
    intros RZ. exfalso. lia.
  - (* [comment removed for export] *)
    specialize (LH ltac:(with_box RZC ylia)).
    zstep. step. if_cases K4; zify_cond K4. { exfalso. with_box RZC ylia. }   (* [comment removed for export] *)
    step. step.                                                  (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => unboxed STK__
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ _ _ => exact HK
         | |- rng _ _ _ => solve_rng
         | |- _ => atop_facts; lia
         end.
    rename POST into ST.
    do 16 step.
    release_frame FR ST (bv_unsigned sp).
    carry STATS MUc WMc ltac:(with_box DJT ylia).
    apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
    intros _. exact LH.
Qed.
End Zd1.
#[using="Type"] Lemma allocD_gen : ltac:(let t := eval cbv delta [allocD_gen__stmt] in allocD_gen__stmt in exact t).
Proof. exact allocD_gen__body. Qed.
End CANSEC2.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memsetZ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aclass2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 yl_is_copy (id : ident) : bool :=
  let s := Ident.to_string id in
  let n := String.length s in
  if Int.ge n 1 then
    (if Char.equal (String.get s 0) (Char.of_int 89) then true
     else if Int.ge n 2 then (if Char.equal (String.get s 0) (Char.of_int 68) then Char.equal (String.get s 1) (Char.of_int 88) else false)
     else false)
  else false.
Local Ltac2 yl_prune () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then (if yl_is_copy id then None else zt_is_prop_some ty id) else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac yl_prune := ltac2:(Control.enter yl_prune).
Set Default Proof Mode "Classic".
Local Ltac ylia := first [ yl_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ]
                   | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_base8 := lazymatch goal with |- (?a <= ?b /\ _)%Z => let X := leftmost a in let Y := leftmost b in first [ constr_eq X Y | is_Zlit X; is_Zlit Y ] end.
Local Ltac fp_find8s := first [ apply Exists_cons_hd; cbn [fst snd]; fp_base8; split; lia | apply Exists_cons_tl; fp_find8s ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8s | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma cb_take : forall m A n k bs,
  rw_cells asegs m A [CB (Z.to_nat n) bs] -> 0 <= k <= n ->
  rw_cells asegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)] /\ rw_cells asegs m (A + k) [CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)].
Proof.
  intros m A n k bs H HK.
  assert (L : length bs = Z.to_nat n) by (destruct H as [[[WF _] _] _]; cbn in WF; exact WF).
  assert (H2 : rw_cells asegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs); CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)]).
  { eapply rw_cells_recast; [exact H | | |].
    - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
    - cbn [cells_size csize]. lia. }
  lazymatch type of H2 with rw_cells _ _ _ [?x; ?y] => change [x; y] with ([x] ++ [y]) in H2 end.
  apply rw_cells_app in H2. destruct H2 as [HA HR]. cbn [cells_size csize] in HR. rewrite Nat.add_0_r, Z2Nat.id in HR by lia.
  split; [exact HA | exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_app2 : forall m A n1 bs1 n2 bs2,
  rw_cells asegs m A [CB n1 bs1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells asegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros m A n1 bs1 n2 bs2 H1 H2.
  assert (H : rw_cells asegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  cbn [app] in H. eapply rw_cells_recast; [exact H | | |].
  - destruct H1 as [[[W1 _] _] _]. destruct H2 as [[[W2 _] _] _]. cbn in W1, W2 |- *. rewrite length_app. repeat split; lia.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn [cells_size csize]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stats_class_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (X size : Z),
  a0 = Z_to_bv 64 X -> 0 <= X -> X + 112 < 2^64 ->
  24 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 112)) (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34300) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3420c) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros -> X0 X1 SZ M8 RIMG RTLS.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. (nd_pre CF 6%nat; intros C1 CS1 CS2 CS3 CSM CBG; nd_post).
  step. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
  - eapply evtF_mono; [eapply (classblock2_spec RNG); [lia | exact M8 | exact RIMG | exact RTLS] |].
    cbv beta. intros ms' P. (nd_pre P 6%nat; intros a2' a3' a4' a5' a6' ndR1__; nd_post; revert ndR1__; intros ->). do 5 eexists. reflexivity.
  - zstep. zstep. rewrite <- (CSM ltac:(lia)). step.            (* [comment removed for export] *)
    apply evtF_done. do 5 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma fill_len_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min n 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34338) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3432c) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros N RIMG RTLS.
  step. step. if_cases K; zify_cond K.                           (* [comment removed for export] *)
  - replace (Z.min n 4096) with n by lia. apply evtF_done. reflexivity.
  - step. replace (Z.min n 4096) with 4096 by lia. apply evtF_done. reflexivity.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition allocD_postG (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).

Definition allocD_gen__stmt : Prop := forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
    (n t c AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
    (fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6 : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + n <= ATOP -> AB mod 16 = 0 ->
  class_id (needed_size n) = c ->
  (t + 4096 <= AB \/ AB + 65536 <= t) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
  rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
  0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  tclr AB (UB + n - AB) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0xa58b0 [C8 (Z_to_bv 64 0xa7740)] ->
  rw_cells asegs m 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)] ->
  rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x1404c0 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 <= b1m < 256 -> 0 < id < 2^31 ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
  evtF asegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x341bc) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 4).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 5).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 7).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 8).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 9).
Variable c : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 10).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 11).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 12).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 13).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 14).
Variable b1m : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 15).
Variable id : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 16).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 17).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 18).
Variable uj : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 19).
Variable j1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 20).
Variable j2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 21).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 22).
Variable raX : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 23).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 24).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 25).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 26).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 27).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 28).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 29).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 30).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 31).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 32).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 33).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 34).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 35).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 36).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 37).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 38).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 39).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 40).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 41).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 42).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 43).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 44).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 45).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 46).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 47).
Variable s6x : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 48).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 49).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 50).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 51).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocD_gen__stmt 52).
Let fl := Z.min n 4096.
#[using="fl"] Lemma allocD_gen__body : ltac:(let T := type of (fun (h : allocD_gen__stmt) => h L RNG sp gp tp F fc m n t c AB UB lo b0 b1m id S sj uj j1 j2 fr0 raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (sp, (gp, (tp, (F, (fc, (m, (n, (t, (c, (AB, (UB, (lo, (b0, (b1m, (id, (S, (sj, (uj, (j1, (j2, (fr0, (raX, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, (s11v, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s6x, (t3, (t4, (t5, t6))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1 TCB
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RTLS RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  tclr_int TCB.
  unfold AIMG_HI, ATP88, ATSD in *.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N PRIM HC) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ2 SM16 SMALL MC2; nd_post).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  step. call_sp (thread_stats_spec RNG (al_ctx L) t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  rename POST into ST.
  aload STATS 2 (t + 2800 + 16).                                 (* [comment removed for export] *)
  aload STATS 0 (t + 2800 + 0).                                  (* [comment removed for export] *)
  aload STATS 1 (t + 2800 + 8).                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep. zstep. zstep.                       (* [comment removed for export] *)
  astore STATS 0.                                                (* [comment removed for export] *)
  astore STATS 1.                                                (* [comment removed for export] *)
  astore STATS 2.                                                (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2: { exfalso. lia. }          (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evtF_cut; [eapply (stats_class_spec RNG); [reflexivity | lia | lia | lia | clear -NS RSM RZM; rewrite NS; Z.div_mod_to_equations; lia | exact RIMG | exact RTLS] |].
  cbv beta. intros msS PS. (nd_pre PS 6%nat; intros a2s a3s a4s a5s a6s ndR1__; nd_post; revert ndR1__; intros ->). rewrite HC.
  zstep. zstep.                                                  (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 c 3) by lia. change (2^3) with 8.
  aload STATS (14 + c) (t + 2912 + c * 8).                       (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  astore STATS (14 + c).                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  carry UJ MUs WMs ltac:(with_box DJT ylia). carry HDR MUs WMs ltac:(with_box DJT ylia).
  unbox LH.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH' : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH RZ). box LH. carry LH MUs WMs ltac:(with_box DJT ylia). exact LH. }
  clear LH MUs WMs. box LH'. box STATS.
  snapshot [(UB - 16, UB + n); (AB, AB + 16); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUc WMc.
  snapshot [(UB - 16, UB + n); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUl WMl.
  (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. lstep. step. if_lit.                               (* [comment removed for export] *)
  eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG | exact RTLS] |]. cbv beta. intros msF ->.   (* [comment removed for export] *)
  chg (Z.min n 4096) fl.
  destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
  step. step. step. lstep. step.                                 (* [comment removed for export] *)
  box UJ1.   (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear UJ1
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => unboxed UJ1
       | |- rng _ _ _ => eapply rng_sub'; [exact RU|]; subst fl; lia
       | |- _ => subst fl; atop_facts; lia
       end.
  rename POST into UF1.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (UF : rw_cells asegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
  { replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
    apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
  clear UF1 UJ2.
  (* [comment removed for export] *)
  step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
  lstep. zstep. zstep. zstep. zstep. step.                       (* [comment removed for export] *)
  sstep. step. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  unbox LH'.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH' RZ). box LH'. carry LH' MUl WMl ltac:(lia). exact LH'. }
  clear LH' MUl WMl.
  pose proof (rz_size_cases n) as RZC. box RZC.
  step. if_cases K3; zify_cond K3.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    clear LH.
    match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => unboxed STK__
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ _ _ => exact HK
         | |- rng _ _ _ => solve_rng
         | |- _ => atop_facts; lia
         end.
    rename POST into ST.
    do 16 step.                                                  (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    carry STATS MUc WMc ltac:(with_box DJT ylia).
    apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
    intros RZ. exfalso. lia.
  - (* [comment removed for export] *)
    specialize (LH ltac:(with_box RZC ylia)).
    zstep. step. if_cases K4; zify_cond K4. { exfalso. with_box RZC ylia. }   (* [comment removed for export] *)
    step. step.                                                  (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => unboxed STK__
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ _ _ => exact HK
         | |- rng _ _ _ => solve_rng
         | |- _ => atop_facts; lia
         end.
    rename POST into ST.
    do 16 step.
    release_frame FR ST (bv_unsigned sp).
    carry STATS MUc WMc ltac:(with_box DJT ylia).
    apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
    intros _. exact LH.
Qed.
End Zd1.
#[using="Type"] Lemma allocD_gen : ltac:(let t := eval cbv delta [allocD_gen__stmt] in allocD_gen__stmt in exact t).
Proof. exact allocD_gen__body. Qed.
End CANSEC2.
(* [comment removed for export] *)
End TwB.
